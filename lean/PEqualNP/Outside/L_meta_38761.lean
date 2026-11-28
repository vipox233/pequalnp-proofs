import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38761

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0400000854085615#64 ++ 0xfb804e78fd18fe3f#64 : BitVec 128),
   (0x284194ab306b32cc#64 ++ 0xf7c3b5af32ef33cc#64 : BitVec 128),
   (0xb09c294dc30dc370#64 ++ 0xeefc39cfc30fc3f0#64 : BitVec 128),
   (0xc02ec1f003b001aa#64 ++ 0xdf3fc1f003f003ff#64 : BitVec 128),
   (0x00377e0003d6a800#64 ++ 0xbfbffe0003fffc00#64 : BitVec 128),
   (0x003bfff6a8000000#64 ++ 0x7e7ffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0004000003d6a800 0x8180000003fffc00

def z1 : W := mkw 0x003bfff6a8000000 0x7e7ffffffc000000

def z2 : W := mkw 0x0400000854085615 0xfb804e78fd18fe3f

def z3 : W := mkw 0x284194ab306b32cc 0xf7c3b5af32ef33cc

def z4 : W := mkw 0xb09c294dc30dc370 0xeefc39cfc30fc3f0

def z5 : W := mkw 0xc00881f0002001aa 0x400001f0000003ff

def z6 : W := mkw 0xc02ec1f003b001aa 0xdf3fc1f003f003ff

def z7 : W := mkw 0x00377e0003d6a800 0xbfbffe0003fffc00

def z8 : W := mkw 0xb09c294dc30dc370 0x447c31cfc20703f0

def z9 : W := mkw 0x0000000000000000 0x7a004e78fc000000

def z10 : W := mkw 0x284194a3206320c8 0x0443b18702e701c0

def z11 : W := mkw 0x084000001062308c 0x0100000000e0300c

def z12 : W := mkw 0xc004000003b001aa 0x8100000003f003ff

def z13 : W := mkw 0xc02ec1f003b001aa 0x043f818002e001c0

def z14 : W := mkw 0xb09c294583058160 0x047c3187020701c0

def z15 : W := mkw 0xb8ddbdefb36fb3ec 0xf7ffb5af32ef33cc

def z16 : W := mkw 0x800c014003000120 0x043c0180020001c0

def z17 : W := mkw 0xb09c294dc30dc370 0xfffc79ffc31fc3ff

def z18 : W := mkw 0xc03ffff6abb001aa 0xff7ffffffff003ff

def z19 : W := mkw 0xb088014580010160 0x00400187000001c0

def z20 : W := mkw 0x0026400003900000 0x9f3fc00003f00000

def z21 : W := mkw 0xc03ffff003f6a9aa 0xffbffff003ffffff

def z22 : W := mkw 0xc42ec1f857b857bf 0xffbfcff8fff8ffff

def z23 : W := mkw 0x287bffffb86b32cc 0xfffffffffeef33cc

def z24 : W := mkw 0x0400000054005415 0x19004e70fd10fc3f

def z25 : W := mkw 0x2000000900090240 0xe6c0318f020f03c0

def z26 : W := mkw 0x0008015488000000 0x00000050cc000000

def z27 : W := mkw 0x04377e0857defe15 0xffbffe78fffffe3f

def z28 : W := mkw 0x04366a004794cc11 0x083c4a50cd10cc33

def z29 : W := mkw 0x00377e0003d6a800 0x043fb00002e70000

def z30 : W := mkw 0x00113e000046a800 0x20803e00000ffc00

def z31 : W := mkw 0xb09c294583058160 0x6e7c39cfc20701c0

def z32 : W := mkw 0x000194a220200088 0xf743b5af32e003cc

def z33 : W := mkw 0x2c4194ab746b76dd 0xffc3ffffffffffff

def z34 : W := mkw 0xb8ddbdeff36ff3fc 0xffffbdeff3eff3fc

def z35 : W := mkw 0x2877feab33ffbacc 0xffffffaf33ffffcc

def z36 : W := mkw 0x000080a000200088 0x400001a0000003cc

def z37 : W := mkw 0x0001160228000000 0x000006003c000000

def z38 : W := mkw 0x0023560000d22800 0x1103c60000f03c00

def z39 : W := mkw 0x0018294480000000 0x6e7c39cfc0000000

def z40 : W := mkw 0x0400000854085615 0x818000000118fe3f

def z41 : W := mkw 0x909c2944c304c130 0x083c0840c100c030

def z42 : W := mkw 0x002ac1f6a8000000 0x5e7fc1fffc000000

def z43 : W := mkw 0x00193f46a8000000 0x6e7c3fcffc000000

def z44 : W := mkw 0x003ffff6abd6a800 0xfffffffffffffc00

def z45 : W := mkw 0x043bfffefc085615 0xfffffffffd18fe3f

def z46 : W := mkw 0x084080a23020108c 0x000000203000000c

def z47 : W := mkw 0x0863d6b23862308c 0x1103c6303ce0300c

def z48 : W := mkw 0xec6fd5fb77fb77ff 0xffffffffffffffff

def z49 : W := mkw 0x284194ab206b22c8 0xe6c3b18f02ef03c0

def z50 : W := mkw 0x4422c0b014b0148f 0x1103c6303cf03c0f

def z51 : W := mkw 0x00377e0003d6a800 0x193fce0001f0fc00

def z52 : W := mkw 0xb098294dc0094370 0x6e7c39cfc00003f0

def z53 : W := mkw 0xb084000943dfeb70 0x8180000003fffff0

def z54 : W := mkw 0xb8dc294dd36ff3fc 0xeffc39cfc3eff3fc

def z55 : W := mkw 0x0400000014001405 0x110046303c103c0f

def z56 : W := mkw 0x0400000044004411 0x08004a50cd10cc33

def z57 : W := mkw 0xe84881fb302913ee 0x404001ff300003ff

def z58 : W := mkw 0x0001140000422000 0xb783b40002ef3000

def z59 : W := mkw 0x0418294cd4085615 0xfffc7ffffd18fe3f

def z60 : W := mkw 0x949c2944c704c531 0x083c4a50cd10cc33

def z61 : W := mkw 0xb49c294dd70dd775 0xfffc7fffff1fffff

def z62 : W := mkw 0x3090280dc00dc250 0x20c0380fc00fc000

def z63 : W := mkw 0x0000000000000000 0xdb0040700110023f

def z64 : W := mkw 0x10902804c004c010 0x00000800c000c000

def z65 : W := mkw 0xc0000000002001aa 0x00000000000003ff

def z66 : W := mkw 0x000194a220000000 0x7e43fffffc000000

def z67 : W := mkw 0x287bfff7a86320c8 0x7e7ffffffee701c0

def z68 : W := mkw 0xc03ffff6abb001aa 0x7e7ffffffee001c0

def z69 : W := mkw 0x040881fefc085615 0xfbc04ffffd18fe3f

def z70 : W := mkw 0xb088014dc0094370 0x404001cfc00003f0

def z71 : W := mkw 0x0400000004000401 0x000042100c100c03

def z72 : W := mkw 0x04377e0017d6bc05 0xbfbffe303ffffc0f

def z73 : W := mkw 0x043bfffefc085615 0x7efffffffc08fc00

def z74 : W := mkw 0x3090280dc00dc250 0xeac0384fc10fc230

def z75 : W := mkw 0x287bffffb82912cc 0x7e7ffffffc0003cc

def z76 : W := mkw 0x003bfff6a8000000 0x047fb18700000000

def z77 : W := mkw 0x000080a000200088 0xd70381a002e003cc

def z78 : W := mkw 0xb09ca9edc32dc3f8 0xffffb9efc3efc3fc

def z79 : W := mkw 0xc40881f8542857bf 0xfb804ff8fd18ffff

def z80 : W := mkw 0x286bd5fb306b32cc 0xfffff5ff32ef33cc

def z81 : W := mkw 0x00377e0843deea10 0xffbffe48c3fffe30

def z82 : W := mkw 0x002bd5f220000000 0x7e7ff5ff30000000

def z83 : W := mkw 0x000194a220000000 0x7643b5af30000000

def z84 : W := mkw 0x800c014003000120 0xdf3c41f0031003ff

def z85 : W := mkw 0x00377e0003d6a800 0xffbffe7003fffe3f

def z86 : W := mkw 0x30bbffffe80dc250 0x7efffffffc0fc000

def z87 : W := mkw 0x0404000857defe15 0xfb804e78fffffe3f

def z88 : W := mkw 0x0026400003900000 0x083c400001100000

def z89 : W := mkw 0x0010280480000000 0x2040380fc0000000

def z90 : W := mkw 0xe86fd5f323f321ea 0xdf7ff1f703f703ff

def z91 : W := mkw 0x800c014003000120 0xce3c01c0030003f0

def z92 : W := mkw 0xd0be6954c394c132 0x083c4850c110c033

def z93 : W := mkw 0xf0bee9fdc3bdc3fa 0xfffff9ffc3ffc3ff

def z94 : W := mkw 0x000080b228000000 0x000000303c000000

def z95 : W := mkw 0x0033feb228000000 0x3e3ffe303c000000

def z96 : W := mkw 0x287bfff7a86320c8 0x047fb18702e701c0

def z97 : W := mkw 0x284194ab304b3244 0x76c3b5af300f3000

def z98 : W := mkw 0x0023d6b228000000 0x1003c6303c000000

def z99 : W := mkw 0x00113e06a8000000 0x20403e0ffc000000

def z100 : W := mkw 0xb488014dd4095775 0x404001fffc0003ff

def z101 : W := mkw 0x2841140b304b3244 0xf3c0342f300f320c

def z102 : W := mkw 0x909c2944c304c130 0xaebc3840c30fc030

def z103 : W := mkw 0x003b7f56a8000000 0x287c7e5ffc000000

def z104 : W := mkw 0x284194ab306b32cc 0x4443b1af32e703cc

def z105 : W := mkw 0x2c7bfffffc6b76dd 0xffffffffffffffff

def z106 : W := mkw 0xc404000857b857bf 0xfb804e78fff8ffff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000

def z108 : W := mkw 0x0000000000000000 0x400000700000023f

def z109 : W := mkw 0x00366a0003948800 0x083c4a000110cc00

def z110 : W := mkw 0x04142808570cd615 0xffbc7e78ff1ffe3f

def z111 : W := mkw 0x0014280003048000 0xaebc3800030fc000

def z112 : W := mkw 0x002ac1f000000000 0x5e3fc1f000000000

def z113 : W := mkw 0xb4bf7f4dd7dfff75 0xffffffffffffffff

def z114 : W := mkw 0x0400000844084611 0xea804a58cd18ce33

def z115 : W := mkw 0x0000000000000000 0xbb804e000118fc00

def z116 : W := mkw 0x003bfff6a8000000 0x447fb1fffc000000

def z117 : W := mkw 0x084194a23062308c 0x7743b5af30e0300c

def z118 : W := mkw 0x0400000854085615 0xa1800e08fd18fe3f

def z119 : W := mkw 0x04113e0efc085615 0xfbc07e7ffd18fe3f

def z120 : W := mkw 0xe02ec1f903b903ea 0xfffff1ff03ff03ff

def z121 : W := mkw 0x0000000000000000 0xa6803000020f0000

def z122 : W := mkw 0x000194aa30081204 0xf7c3b5af3008320c

def z123 : W := mkw 0x00366a0003948800 0xbbbc4e000118fc00

def z124 : W := mkw 0x003bfffee8084210 0xfefffffffd08c230

def z125 : W := mkw 0x084194aa306a328c 0xf383842830e8320c

def z126 : W := mkw 0xf8fffdfff3fff3fe 0xfffffdfff3fff3ff

def z127 : W := mkw 0xb0bffff7ab058160 0x047fb187020701c0

def z128 : W := mkw 0x084194a23062308c 0x1103842030e0300c

def z129 : W := mkw 0xb0840009430dc370 0x80800000030fc3f0

def z130 : W := mkw 0x00377e0003d6a800 0x24bfbe0002effc00

def z131 : W := mkw 0x0014280003048000 0x043c300002070000

def z132 : W := mkw 0xb09d3d4dc34fe370 0xffffbdcfc3eff3f0

def z133 : W := mkw 0x20011409004b2240 0xf7c3b58f02ef33c0

def z134 : W := mkw 0xb0bf7f4dc3dfeb70 0xffffffcfc3fffff0

def z135 : W := mkw 0x909c294cc30cc330 0xeabc0848c108c230

def z136 : W := mkw 0xb4840009570dd775 0x81800000031fffff

def z137 : W := mkw 0x0400000814081605 0xf38046383c183e0f

def z138 : W := mkw 0x0037fea003f6a888 0xffbfffa003ffffcc

def z139 : W := mkw 0x003bfff6a8000000 0x0c7ffbd7cc000000

def z140 : W := mkw 0xc02ec1f6abb001aa 0xdf7fc1fffff003ff

def z141 : W := mkw 0xc00c81f0032001aa 0xce3c01f0030003ff

def z142 : W := mkw 0xc02fd7f22bb001aa 0xdf3fc7f03ff003ff

def z143 : W := mkw 0x2c4080ab742956dd 0x404001fffc0003ff

def z144 : W := mkw 0x0400000854085615 0xdb004078fd10023f

def z145 : W := mkw 0x0023d6b228000000 0x7643f7bf3c000000

def z146 : W := mkw 0x284194ab302912cc 0x7643b5af300003cc

def z147 : W := mkw 0x000881f6a8000000 0x7a404ffffc000000

def z148 : W := mkw 0x2841140b304b3244 0xb7c3b40f32ef3000

def z149 : W := mkw 0xf09c294dc3bdc3fa 0xeffc39cfc3ffc3ff

def z150 : W := mkw 0x0423560854da7e15 0xfb83ce78fdf8fe3f

def z151 : W := mkw 0x0863d6a230f2388c 0x1103c62030f03c0c

def z152 : W := mkw 0x284194a3206320c8 0x7643b5af32e701c0

def z153 : W := mkw 0x284194a3206320c8 0xd743b1a702e703cc

def z154 : W := mkw 0xb0bf7f4dc3dfeb70 0xeeffb9cfc3efc3f0

def z155 : W := mkw 0xc43ffff857feffbf 0xffbffff8ffffffff

def z156 : W := mkw 0x003aebf6a8000000 0x487c4bfffc000000

def z157 : W := mkw 0x0400000854085615 0x7a804e78fc08fc00

def z158 : W := mkw 0x003a6b5488000000 0x6e7c7bdfcc000000

def z159 : W := mkw 0x00337e0000000000 0x3e3ffe0000000000

def z160 : W := mkw 0x0026c0a003b00088 0xdf3fc1a003f003cc

def z161 : W := mkw 0x00377e0003d6a800 0x3e3ffe0002e70000

def z162 : W := mkw 0xb09c2945c305c170 0x0c7c39c7c307c1f0

def z163 : W := mkw 0x2877fea323f7a8c8 0xbfffff8703fffdc0

def z164 : W := mkw 0x003bfff6a8000000 0x147ff7b73c000000

def z165 : W := mkw 0x90bf7f44c3d6e930 0xbfbffe40c3fffc30

def z166 : W := mkw 0x0404000857defe15 0x8180000003fffe3f

def z167 : W := mkw 0x0400000044004411 0xbb804e50cd18fc33

def z168 : W := mkw 0xb0bffff7ab058160 0x7e7ffffffe0701c0

def z169 : W := mkw 0x003bfff6a8000000 0xff7ffffffd10023f

def z170 : W := mkw 0x04337e0854085615 0xffbffe78fd18fe3f

def z171 : W := mkw 0x000881f6a8000000 0x404001fffc000000

def z172 : W := mkw 0x003bfff6a8422000 0xfffffffffeef3000

def z173 : W := mkw 0x000080a000000000 0x560381a000000000

def z174 : W := mkw 0x003ffff6ab948800 0x7e7ffffffd10cc00

def z175 : W := mkw 0x000080a000200088 0x0403818002e001c0

def z176 : W := mkw 0x3090280580058040 0x0040300700070000

def z177 : W := mkw 0x3090280dc00dc250 0xe6c0398fc20fc3c0

def z178 : W := mkw 0x0000000000000000 0x20800e000008fc00

def z179 : W := mkw 0x2018294d80090240 0xeefc39cfc20f03c0

def z180 : W := mkw 0x0423d6ba7c085615 0xfb83ce78fd18fe3f

def z181 : W := mkw 0x30b77e0dc3dfea50 0xbffffe0fc3fffc00

def z182 : W := mkw 0x284881ffb82912cc 0x404001fffc0003cc

def z183 : W := mkw 0xb49c294dd70dd775 0xeefc3fcfff0ffff0

def z184 : W := mkw 0xb09c294dc30dc370 0x487c09cfc100c3f0

def z185 : W := mkw 0x2c4080ab742956dd 0xfbc04ffffd18ffff

def z186 : W := mkw 0x04377e0047d6ec11 0xbfbffe50cffffc33

def z187 : W := mkw 0x284194a3306330cc 0x1543b5a732e731cc

def z188 : W := mkw 0x0400000854085615 0x40000078fc00023f

def z189 : W := mkw 0x0400000854085615 0x00000008fc000000

def z190 : W := mkw 0xe87ffffb33ffbbee 0xffffffff33ffffff

def z191 : W := mkw 0x2c4194ab746b76dd 0xf7c3b5af33ffffff

def z192 : W := mkw 0x0000000000200088 0x8100000002e003cc

def z193 : W := mkw 0x284194ab306b32cc 0x9183842032ef33cc

def z194 : W := mkw 0x3490280dd40dd655 0xfbc07e7ffd1ffe3f

def z195 : W := mkw 0x003ffff6abd6a800 0x047fb18702e70000

def z196 : W := mkw 0x0426400857985615 0xffbfce78fff8fe3f

def z197 : W := mkw 0x00337e0000422000 0xbfbffe0002ef3000

def z198 : W := mkw 0x084194a220622088 0x0003800000e00000

def z199 : W := mkw 0xb09c294583058160 0xce7c31c7030703f0

def z200 : W := mkw 0x0000000810081204 0x2080040830083000

def z201 : W := mkw 0x2c41140b744b7655 0x20c03e0ffc0ffc00

def z202 : W := mkw 0xe86fd5fb33fb33ee 0xfffff5ff33ff33ff

def z203 : W := mkw 0xb09c294d830d8360 0xe6fc318f020f03c0

def z204 : W := mkw 0x04113e08544efe15 0x20803e08fc0ffc00

def z205 : W := mkw 0x284080ab302912cc 0x404001af300003cc

def z206 : W := mkw 0xc02fd5f223b001aa 0xff7ff5ff33f003ff

def z207 : W := mkw 0x28400009106b32cc 0x8180000002ef33cc

def z208 : W := mkw 0x2000000940094250 0xeec039cfc30fc3f0

def z209 : W := mkw 0xc02e415003900122 0x083c405001100033

def z210 : W := mkw 0x200080a9002902c8 0xf7c3b1af02ef03cc

def z211 : W := mkw 0x00366a0003948800 0x003c000000000000

def z212 : W := mkw 0x0000000810081204 0xfb804e283118fe0c

def z213 : W := mkw 0x0400000014001405 0x0100000000103c0f

def z214 : W := mkw 0x284594ab33ffbacc 0xf7c3b5af33ffffcc

def z215 : W := mkw 0x2000000910091244 0xf7c035af320f33cc

def z216 : W := mkw 0x0019bde6a0000000 0x7e7fbdeff0000000

def z217 : W := mkw 0x002ec1f003900000 0xdf3fc1f003f00000

def z218 : W := mkw 0x003bfff6a8000000 0x247fbf8ffc000000

def z219 : W := mkw 0x003aebf488000000 0x5e3fcbf0cc000000

def z220 : W := mkw 0xc02ec1f003b001aa 0x443f81f002e003ff

def z221 : W := mkw 0x0000000000000000 0xca00004001000230

def z222 : W := mkw 0xf08881fdc02943fa 0x404001ffc00003ff

def z223 : W := mkw 0x0026400003900000 0xdf3fc07003f0023f

def z224 : W := mkw 0xb488014dd4095775 0xfbc04ffffd18ffff

def z225 : W := mkw 0x003a6b5488000000 0x083c4a50cc000000

def z226 : W := mkw 0x002a415000000000 0x083c405000000000

def z227 : W := mkw 0x909c294483048120 0x003c000000000000

def z228 : W := mkw 0xd0bee9f4c3b4c1ba 0xdf3fc9f0c3f0c3ff

def z229 : W := mkw 0x0018294480000000 0x047c318700000000

def z230 : W := mkw 0x003bfff6a8000000 0x183fce70fc000000

def z231 : W := mkw 0x0000000000000000 0xc6000180020003c0

def z232 : W := mkw 0xf0be695dc39dc372 0xeefc79dfc31fc3f3

def z233 : W := mkw 0x0004000003948800 0x000000000110cc00

def z234 : W := mkw 0x00377e0003948800 0x3e3ffe000110cc00

def z235 : W := mkw 0x4022c0b000b0008a 0x1103c03000f0000f

def z236 : W := mkw 0x2400000954095655 0xffc07fffff1fffff

def z237 : W := mkw 0x043a6b54cc004411 0x083c4a50cd10cc33

def z238 : W := mkw 0xc43ffffeffb857bf 0xfffffffffff8ffff

def z239 : W := mkw 0x0000000840084210 0xea800848c108c230

def z240 : W := mkw 0x4022c0b000b0008a 0xdb03c07001f0023f

def z241 : W := mkw 0x0000000850085214 0xfb800c68f108f23c

def z242 : W := mkw 0x949c294cd70cd735 0xfbbc4e78fd18fe3f

def z243 : W := mkw 0x203bffffa8090240 0xfefffffffe0f03c0

def z244 : W := mkw 0x0400000854085615 0x20800e08fc08fc00

def z245 : W := mkw 0xb8ffffeff3fffbfc 0xffffffeff3fffffc

def z246 : W := mkw 0x2840000b30091244 0x0040000f30000000

def z247 : W := mkw 0x0001160000422800 0x0000060000003c00

def z248 : W := mkw 0x8004000003000120 0x80000000030003f0

def z249 : W := mkw 0x0000000840084210 0xfb804878c118c23f

def z250 : W := mkw 0x003a6b5488000000 0x7a3c4e78fc000000

def z251 : W := mkw 0x0000000000000000 0x818000000118fc00

def z252 : W := mkw 0x00337e0000000000 0xbfbffe000118fc00

def z253 : W := mkw 0x0000000810081204 0x818000000008320c

def z254 : W := mkw 0x0000000810081204 0xf38004283008320c

def z255 : W := mkw 0xb09c294dd30dd374 0xfffc3deff30ff3fc

def z256 : W := mkw 0xb08c014dc30dc370 0xc0c001cfc30fc3f0

def z257 : W := mkw 0x284194ab306b32cc 0x24c3b58f32ef31c0

def z258 : W := mkw 0xf0bee9f583b581ea 0x047fb18702e701c0

def z259 : W := mkw 0x0001140000422000 0x20803400000f3000

def z260 : W := mkw 0x0400000854085615 0xea800878fd08c23f

def z261 : W := mkw 0x000080a81028128c 0xf78385a832e833cc

def z262 : W := mkw 0x0011bea6a8000000 0x7643bfaffc000000

def z263 : W := mkw 0x0014280003048000 0x083c08000100c000

def z264 : W := mkw 0x0000000840084210 0xfb804e48c118fe30

def z265 : W := mkw 0x0423d6b23c001405 0x1103c6303c103c0f

def z266 : W := mkw 0x28400001006320c8 0x0000000002e701c0

def z267 : W := mkw 0x2841140b304b3244 0x20c0340f300f3000

def z268 : W := mkw 0xc02ec1f843b843ba 0xffbfc9f8c3f8c3ff

def z269 : W := mkw 0xb0bf7f4583d7a960 0xbfffff8703fffdc0

def z270 : W := mkw 0xc03ffff003b001aa 0xff3ffff003f003ff

def z271 : W := mkw 0x4026c0b003b0008a 0x9f3fc03003f0000f

def z272 : W := mkw 0x000194a220000000 0x0443b18700000000

def z273 : W := mkw 0x0022421008000000 0x000042100c000000

def z274 : W := mkw 0x2000000100010040 0x04403187020701c0

def z275 : W := mkw 0xa00c014903090360 0xeefc31cf030f03f0

def z276 : W := mkw 0xb09c294dc30dc370 0x24fc398fc20fc1c0

def z277 : W := mkw 0xc02e415003900122 0xdb3c40700110023f

def z278 : W := mkw 0x0000000000000000 0xfb804e78fd18fc00

def z279 : W := mkw 0xc03eebf003b489aa 0xdf3fcbf003f0cfff

def z280 : W := mkw 0x2863d6ab30fb3acc 0xf7c3f7af32ff3fcc

def z281 : W := mkw 0x0023560000d22800 0xbb83ce0001f8fc00

def z282 : W := mkw 0x0400000044004411 0x000000000110cc33

def z283 : W := mkw 0xb0840009430dc370 0xe6c0318f030fc3f0

def z284 : W := mkw 0x0001140000422000 0x0403b00002e70000

def z285 : W := mkw 0x284080a3202100c8 0x00400187000001c0

def z286 : W := mkw 0x002ac1f000000000 0xdf3fc1f00110023f

def z287 : W := mkw 0xb09ca9ffeb0dc370 0xeefc39ffff0fc3f0

def z288 : W := mkw 0xc026400003b001aa 0x9f3fc00003f003ff

def z289 : W := mkw 0xb09c294dc30dc370 0xfffc7fcfc31ffff0

def z290 : W := mkw 0xb09c294dc30dc370 0x84fc3187030fc3f0

def z291 : W := mkw 0x043bfff6ec004411 0x7e7ffffffd10cc33

def z292 : W := mkw 0x000000000046a800 0x00800000000ffc00

def z293 : W := mkw 0xc008015000000122 0x0000005000000033

def z294 : W := mkw 0x0018294cc0084210 0xeefc39cfc108c230

def z295 : W := mkw 0xb0bfffffeb0dc370 0xeeffb9cfc30fc3f0

def z296 : W := mkw 0xb0bfffffeb0dc370 0xfeffffffff0fc3f0

def z297 : W := mkw 0x003bfff6a8000000 0x6e7fb9cfc0000000

def z298 : W := mkw 0x908400004304c130 0x000000000100c030

def z299 : W := mkw 0x0c4194aa746a769d 0xfb83ce78fdf8fe3f

def z300 : W := mkw 0xc02ac1f0002001aa 0x5e3fc1f0000003ff

def z301 : W := mkw 0xe86ec1f913fb33ee 0xdfbfc1f003ff33ff

def z302 : W := mkw 0x0000000000000000 0x6a000848c0000000

def z303 : W := mkw 0x2863d6bb386b32cc 0xf7c3f7bf3eef33cc

def z304 : W := mkw 0xf0aec1f943bdc3fa 0xdfbfc1f003ffc3ff

def z305 : W := mkw 0xb49c294dc70dc771 0xeefc7bdfcf1fcff3

def z306 : W := mkw 0x4863d4b230f2308e 0x1103c43030f0300f

def z307 : W := mkw 0x00113e000046a800 0xb783be0002effc00

def z308 : W := mkw 0x28400009106b32cc 0xe7c0318f02ef33cc

def z309 : W := mkw 0xf0bffffdc3ffebfa 0xffffffffc3ffffff

def z310 : W := mkw 0xc004000003900122 0x0000000001100033

def z311 : W := mkw 0x00377e0003d6a800 0xffbffe78fffffc00

def z312 : W := mkw 0x403bfff6a8b0008a 0x7f7ffffffcf0000f

def z313 : W := mkw 0x284194ab306b32cc 0x514385af30e033cc

def z314 : W := mkw 0x801c294483000120 0xee7c39cfc30003f0

def z315 : W := mkw 0xb09c294dc30dc370 0x28fc384fc10fc030

def z316 : W := mkw 0x284194ab306b32cc 0x31c3b42f30ef300c

def z317 : W := mkw 0xc03ee9f003b481aa 0xffbff9f003ffc3ff

def z318 : W := mkw 0x287bffffb86b32cc 0xf7ffb5af32ef33cc

def z319 : W := mkw 0x0400000854085615 0xf38004283118fe3f

def z320 : W := mkw 0x0018294480000000 0x083c0840c0000000

def z321 : W := mkw 0xc02ec1f003b001aa 0xff3fcff8fff003ff

def z322 : W := mkw 0x4000000000b0008a 0x0100000000f0000f

def z323 : W := mkw 0x0000000840084210 0x40000048c0000230

def z324 : W := mkw 0x2877fea323f7a8c8 0x047fb18702e701c0

def z325 : W := mkw 0x30913e0dc04fea50 0x20c03e0fc00ffc00

def z326 : W := mkw 0x00153e000346a800 0xaebc3e00030ffc00

def z327 : W := mkw 0xc02ec1f003b001aa 0x9f3fc18003f001c0

def z328 : W := mkw 0x003b7f4480000000 0x7e7fffcfc0000000

def z329 : W := mkw 0xb8ddbdefe36fe3f8 0xeeffb9cfc3efc3f0

def z330 : W := mkw 0x2c4194ab346b36cd 0xf7c3f7bf3eff3fcf

def z331 : W := mkw 0x0877fea233f6b88c 0xbfbffe2033fffc0c

def z332 : W := mkw 0x0027560003d22800 0x9f3fc60003f03c00

def z333 : W := mkw 0x0000000000000000 0x08004a000110cc00

def z334 : W := mkw 0x2c77feab77fffedd 0xffffffffffffffff

def z335 : W := mkw 0x000080a000200088 0x1103802000e0000c

def z336 : W := mkw 0xc026c0b003b001aa 0x9103c03003f003ff

def z337 : W := mkw 0x0000000000000000 0x40000078fc000000

def z338 : W := mkw 0xb09c294dc30dc370 0xfefc7fffff0fc3f0

def z339 : W := mkw 0x0023560000d22800 0x0003800000e00000

def z340 : W := mkw 0x043bfff6bc001405 0x7f7ffffffc103c0f

def z341 : W := mkw 0xb0bf7f4dc30dc370 0xfeffffcfc30fc3f0

def z342 : W := mkw 0x0000000000000000 0x20000e08fc000000

def z343 : W := mkw 0x0018a9f6a8000000 0x6e7c39fffc000000

def z344 : W := mkw 0x0000000000d22800 0x0100000000f03c00

def z345 : W := mkw 0xc03ffff003f6a9aa 0xdf3ff1f003f703ff

def z346 : W := mkw 0x0400000854085615 0x51004678fc103e3f

def z347 : W := mkw 0x00337e0000d22800 0x3f3ffe0000f03c00

def z348 : W := mkw 0x0008014480000000 0x404001cfc0000000

def z349 : W := mkw 0x20142809030d8240 0xeefc398f030fc3c0

def z350 : W := mkw 0xc02ec1f003b001aa 0x853f818003f003ff

def z351 : W := mkw 0x0000000040004010 0x08000840c100c030

def z352 : W := mkw 0xc03ffff6ab900122 0x7e7ffffffd100033

def z353 : W := mkw 0x002bd7f228000000 0x5e3fc7f03c000000

def z354 : W := mkw 0x00377e06abd6a800 0xbffffe0ffffffc00

def z355 : W := mkw 0xb4bfffffff0dd775 0xffffffffff1fffff

def z356 : W := mkw 0x00102a0488000000 0x00000a00cc000000

def z357 : W := mkw 0x287bffffb84b3244 0x7efffffffc0f3000

def z358 : W := mkw 0x0400000854085615 0x000000000000023f

def z359 : W := mkw 0x287fffffbbffbacc 0xffffffffffffffcc

def z360 : W := mkw 0x00113e06a846a800 0x20c03e0ffc0ffc00

def z361 : W := mkw 0x30913e0fe80dc250 0x20c03e0ffc0fc000

def z362 : W := mkw 0x003a6b5488000000 0x003c000000000000

def z363 : W := mkw 0x2841140320432040 0x0040300700070000

def z364 : W := mkw 0x38d1bcaff06ff2dc 0xf7c3bdaff2eff3cc

def z365 : W := mkw 0xb0be6b4dc39dcb70 0xeefc7bcfc31fcff0

def z366 : W := mkw 0x000194a220000000 0x1003842030000000

def z367 : W := mkw 0x0c4194a23462348d 0x1103c6303cf03c0f

def z368 : W := mkw 0x003e6b548b948800 0x083c4a50cd10cc00

def z369 : W := mkw 0x0037fea223d6a800 0xffffffaf33fffc00

def z370 : W := mkw 0xe84594ab33fb33ee 0xf7c3b5af33ff33ff

def z371 : W := mkw 0xb4840009570dd775 0xfb804e78ff1fffff

def z372 : W := mkw 0x38d13c0ff04ff254 0x20c03c0ff00ff000

def z373 : W := mkw 0x003f7f548bd6a800 0xbfbffe50cffffc00

def z374 : W := mkw 0x0018294480000000 0x7e7c7ffffc000000

def z375 : W := mkw 0x040080a85428569d 0xff83cff8fff8ffff

def z376 : W := mkw 0x0400000854085615 0xf3800e28fc08fe0c

def z377 : W := mkw 0x0400000854085615 0xbb804e08fd18fc00

def z378 : W := mkw 0x28777e0913ffbacc 0xbfbffe0003ffffcc

def z379 : W := mkw 0xb084000103058160 0x00000000020701c0

def z380 : W := mkw 0xc03bfff6a82001aa 0x7e7ffffffc0003ff

def z381 : W := mkw 0xc02ec1f813b813ae 0xffbfc5f833f833ff

def z382 : W := mkw 0x000080a220000000 0x404001af30000000

def z383 : W := mkw 0x0033fea220000000 0x7e7fffaf30000000

def z384 : W := mkw 0x28777e0b33dfba44 0xbffffe0f33fffc00

def z385 : W := mkw 0x2c400009546b76dd 0xfb804e78ffffffff

def z386 : W := mkw 0x30800009400dc250 0x00800000000fc000

def z387 : W := mkw 0xc02ec1f003b001aa 0x0c3fc1d003f001f3

def z388 : W := mkw 0xbcddbdeff76ff7fd 0xffffffffffffffff

def z389 : W := mkw 0x0001140000422000 0x1103840000e03000

def z390 : W := mkw 0x284194ab306b32cc 0xffc3fffffeef33cc

def z391 : W := mkw 0x4037feb003f6a88a 0xbfbffe3003fffc0f

def z392 : W := mkw 0xc03ffff6abf6a9aa 0xffffffffffffffff

def z393 : W := mkw 0x284194a3206320c8 0xb7c3b58702ef31c0

def z394 : W := mkw 0x400080b00020008a 0x000000300000000f

def z395 : W := mkw 0x284194ab306b32cc 0x60c035af300f33cc

def z396 : W := mkw 0x0000000800080200 0xe280000800080200

def z397 : W := mkw 0x04377e0857defe15 0xbfbffe0003fffe3f

def z398 : W := mkw 0x003ffff003d6a800 0xffbffff003fffc00

def z399 : W := mkw 0x0400000014001405 0x000000303c00000f

def z400 : W := mkw 0xc03ffff6abb001aa 0xdf7ff1f703f003ff

def z401 : W := mkw 0x2c400009546b76dd 0x8180000003ffffff

def z402 : W := mkw 0x00366a0003d6a800 0x89bc4a0003fffc00

def z403 : W := mkw 0x284080ab302912cc 0xd74381af32e003cc

def z404 : W := mkw 0x00377e0003d6a800 0x85bfb00003fffc00

def z405 : W := mkw 0x040881fefc085615 0x404001fffc00023f

def z406 : W := mkw 0x00113e000046a800 0xbb807e00011ffc00

def z407 : W := mkw 0xc42ec1f857b857bf 0xdf3fc1f8fff003ff

def z408 : W := mkw 0x04113e0efc085615 0x20c03e0ffc08fc00

def z409 : W := mkw 0x90be6b44c394c930 0x083c4a40c110cc30

def z410 : W := mkw 0x802e414003900120 0xdf3fc1c003f003f0

def z411 : W := mkw 0x0014280003d6a800 0xafbc380003fffc00

def z412 : W := mkw 0x0400000014001405 0x7b004e78fc103c0f

def z413 : W := mkw 0x2c4194ab746b76dd 0xf7c3bfaffeefffcc

def z414 : W := mkw 0x001c294483048000 0xeefc39cfc30fc000

def z415 : W := mkw 0x003bfff6a846a800 0x7efffffffc0ffc00

def z416 : W := mkw 0x0027560003d6a800 0x9183c60003fffc00

def z417 : W := mkw 0x0000000000000000 0xaa8008000108c000

def z418 : W := mkw 0x0033feb6a8000000 0x3043fe3ffc000000

def z419 : W := mkw 0x0400000854085615 0x89804a50cd18fe3f

def z420 : W := mkw 0x0000000000000000 0xb380040000083000

def z421 : W := mkw 0x2841140b306b32cc 0xa1c0340f32ef33cc

def z422 : W := mkw 0xc02ec1f003b001aa 0x153fc1b002f001cf

def z423 : W := mkw 0xf4bee9fdd7bdd7ff 0xffffffffffffffff

def z424 : W := mkw 0xc02ec1f003b001aa 0x483c41f0011003ff

def z425 : W := mkw 0x4023d6b000f2288a 0x1103c63000f03c0f

def z426 : W := mkw 0x0005140003d6a800 0xb783b40003fffc00

def z427 : W := mkw 0x284194ab306b32cc 0xffc3f5ff33ff33ff

def z428 : W := mkw 0xc03e6b548b900122 0x083c4a50cd100033

def z429 : W := mkw 0x0000000840084210 0x808000000108c230

def z430 : W := mkw 0x90be6b54cb04c130 0x083c4a50cd00c030

def z431 : W := mkw 0x0026400003900000 0xbfbfce0003f8fc00

def z432 : W := mkw 0xe86fd5f323f321ea 0x047fb18702e701c0

def z433 : W := mkw 0x00337e0000d6a800 0x3183fe0000fffc00

def z434 : W := mkw 0x0000000810081204 0x400000283000020c

def z435 : W := mkw 0x0000000810081204 0xfb804e78fc08320c

def z436 : W := mkw 0xb0840009430dc370 0xea800848c30fc3f0

def z437 : W := mkw 0x002ac1f000200088 0xdf3fc1f002e003cc

def z438 : W := mkw 0x04011408544a7615 0xff83fe78fffffe3f

def z439 : W := mkw 0xc00881f0002001aa 0xd70381f002e003ff

def z440 : W := mkw 0x2000000900090240 0x80800000020f03c0

def z441 : W := mkw 0x0022420000900800 0x0000420000100c00

def z442 : W := mkw 0x0000000000000000 0x7200042830000000

def z443 : W := mkw 0xc42e415047904533 0x083c4a50cd10cc33

def z444 : W := mkw 0xc00881f0002001aa 0x00000180000001c0

def z445 : W := mkw 0x0000000000000000 0x9703800002e00000

def z446 : W := mkw 0x0023d6b228000000 0x7a03ce78fc000000

def z447 : W := mkw 0xe844000913fb33ee 0x8180000003ff33ff

def z448 : W := mkw 0x284194ab306b32cc 0xffc3ffaf33ffffcc

def z449 : W := mkw 0xb09c294dc30dc370 0x88bc0840c30fc3f0

def z450 : W := mkw 0xf084000943bdc3fa 0x8180000003ffc3ff

def z451 : W := mkw 0x2867d4ab33fb32cc 0xfffff5af33ff33cc

def z452 : W := mkw 0x00337e000046a800 0x3ebffe00000ffc00

def z453 : W := mkw 0xc00480a003b001aa 0xd70381a003f003ff

def z454 : W := mkw 0x0000000840084210 0xfa804e78fd08c230

def z455 : W := mkw 0x284194ab306b32cc 0x85c3b18702ef33cc

def z456 : W := mkw 0x6863d4bb30fb32ce 0xf7c3f5bf32ff33cf

def z457 : W := mkw 0x00153e0003d6a800 0xa1803e0003fffc00

def z458 : W := mkw 0x803ffff6ab000120 0xfe7fffffff0003f0

def z459 : W := mkw 0x0004000003000000 0x8e3c000003000000

def z460 : W := mkw 0x284194ab706b72dc 0xffc3bdeff3eff3fc

def z461 : W := mkw 0x040194aa74085615 0xffc3fffffd18fe3f

def z462 : W := mkw 0x4023d6b228b0008a 0x1103c6303cf0000f

def z463 : W := mkw 0x4022c0b000b0008a 0xd703c1b002f003cf

def z464 : W := mkw 0x0400000044004411 0xdb004a70cd10ce3f

def z465 : W := mkw 0x000194a000622088 0xf783b5a002ef33cc

def z466 : W := mkw 0x00326a0000000000 0x083c4a0000000000

def z467 : W := mkw 0x0000000010001004 0x110004203000300c

def z468 : W := mkw 0x00337e0000000000 0x043fb00000000000

def z469 : W := mkw 0xb0942809430dc370 0xaebc3800030fc3f0

def z470 : W := mkw 0xc02e415003900122 0x003c000000000000

def z471 : W := mkw 0xc02ec1f003b001aa 0xffbfcff003f8ffff

def z472 : W := mkw 0x043a6b5cdc085615 0xfbbc4e78fd18fe3f

def z473 : W := mkw 0x00377e0003d6a800 0x0c3ffa0003f7cc00

def z474 : W := mkw 0x4022401000900002 0x0000401000100003

def z475 : W := mkw 0xb0bfffffebdfeb70 0xfffffffffffffff0

def z476 : W := mkw 0xc02ec1f003900122 0x5e3fc1f001100033

def z477 : W := mkw 0x003bfff6a8000000 0x767fb5af30000000

def z478 : W := mkw 0x0400000014001405 0xdb0046703d103e3f

def z479 : W := mkw 0x284080ab302912cc 0xe6c031af320f03cc

def z480 : W := mkw 0x0000000000000000 0x110040300010000f

def z481 : W := mkw 0xa84d95eb336b33ec 0xffffb5ef33ef33fc

def z482 : W := mkw 0x0010280000000000 0x2e3c380000000000

def z483 : W := mkw 0x0023560000000000 0x1003c60000000000

def z484 : W := mkw 0x003bfff6a8000000 0xfffffffffd18fc00

def z485 : W := mkw 0xc004000003b001aa 0x0000000002e001c0

def z486 : W := mkw 0x003f7f4483d6a800 0xffffffcfc3fffc00

def z487 : W := mkw 0xb08c014dc3094370 0xce7c01cfc30003f0

def z488 : W := mkw 0x800c81e0032001a8 0xdf3f81e003e003fc

def z489 : W := mkw 0x2877feab33ffbacc 0xf7ffb5af32ef33cc

def z490 : W := mkw 0x0000000000000000 0x1100460000103c00

def z491 : W := mkw 0x0026400003900000 0x043f800002e00000

def z492 : W := mkw 0x0400000854085615 0x918046303d18fe3f

def z493 : W := mkw 0x00337e0000000000 0x7e3ffe78fc000000

def z494 : W := mkw 0x0027540003d22000 0xbfbff40003ff3000

def z495 : W := mkw 0x0001140000000000 0x3603b40000000000

def z496 : W := mkw 0x0400000044004411 0x00000a00cc00cc00

def z497 : W := mkw 0x800c014843084330 0xeebc09c8c308c3f0

def z498 : W := mkw 0xc02ec1f003b001aa 0x193fc07001f0003f

def z499 : W := mkw 0x800c014003000120 0x083c004001000030

def z500 : W := mkw 0x00000006a8000000 0x0040000ffc000000

def z501 : W := mkw 0x00337e06a8000000 0x3e7ffe0ffc000000

def z502 : W := mkw 0xb08881ffe8094370 0x404001fffc0003f0

def z503 : W := mkw 0xb0bf7f4583d7a960 0x047fb18702e701c0

def z504 : W := mkw 0xc0377e0003f6a9aa 0xbfbffe0003ffffff

def z505 : W := mkw 0x00377e0813deba04 0xffbffe2833fffe0c

def z506 : W := mkw 0xb49c294dd70dd775 0xeefc39ffff0fc3ff

def z507 : W := mkw 0x04366a08579cde15 0xfbbc4e78fd18fe3f

def z508 : W := mkw 0xb098294dc00dc370 0x60c039cfc00fc3f0

def z509 : W := mkw 0xc42ec1f047b045bb 0xdf3fcbf0cff0cfff

def z510 : W := mkw 0x0400000014001405 0x000006003c003c00

def z511 : W := mkw 0x28411409106b32cc 0xb783b40002ef33cc

def z512 : W := mkw 0x003ffff6ab048000 0xfeffffffff0fc000

def z513 : W := mkw 0x0000000840084210 0x20800808c008c000

def z514 : W := mkw 0x0841140230423004 0x0000040030003000

def z515 : W := mkw 0x0400000854085615 0xf3800478fc08323f

def z516 : W := mkw 0xb8dca9eff32dd3fc 0xeefc39eff30fc3fc

def z517 : W := mkw 0x0000000000000000 0x6640318f00000000

def z518 : W := mkw 0x0022c0b000000000 0x1003c03000000000

def z519 : W := mkw 0x00366a0003948800 0xaebc7a00031fcc00

def z520 : W := mkw 0xb080000940094370 0x00000000000003f0

def z521 : W := mkw 0xb49c294dd70dd775 0xeffc39cfc31fffff

def z522 : W := mkw 0xb0be694dc39dc370 0xfffff9cfc3ffc3f0

def z523 : W := mkw 0x0001140220000000 0x2040340f30000000

def z524 : W := mkw 0xb094280dc30dc370 0xa0c0380fc30fc3f0

def z525 : W := mkw 0x0001140000422000 0xbf83fe0003fffc00

def z526 : W := mkw 0xc86fd5f233f231ae 0xdf3fc5f033f033ff

def z527 : W := mkw 0x909c2944c304c130 0x6e7c39cfc100c030

def z528 : W := mkw 0x04377e0857defe15 0xbfbffe08fffffc00

def z529 : W := mkw 0x087bfff6b862308c 0x7f7ffffffce0300c

def z530 : W := mkw 0x003bfff6a8200088 0xff7ffffffee003cc

def z531 : W := mkw 0x0026400003d6a800 0x9fbfc00003fffc00

def z532 : W := mkw 0x00113e0000000000 0x20003e0000000000

def z533 : W := mkw 0xc004000003f6a9aa 0x8180000003ffffff

def z534 : W := mkw 0x00113e06a8000000 0x0040300700000000

def z535 : W := mkw 0x0400000854085615 0xea800e48fd08fe30

def z536 : W := mkw 0x003ffff6abd6a800 0xbfffff8703fffc00

def z537 : W := mkw 0xc02ac1f000b001aa 0x5103c1f000f003ff

def z538 : W := mkw 0xb09c294583058160 0xaefc3987030fc1c0

def z539 : W := mkw 0xc03ee9f483b001aa 0xff7ff9ffc3f003ff

def z540 : W := mkw 0xc02fd5f003f221aa 0xffbff5f003ff33ff

def z541 : W := mkw 0x0000000000000000 0x08004a50cc000000

def z542 : W := mkw 0xb8dd3d4ff34ff374 0xeefc3dcff30ff3f0

def z543 : W := mkw 0x003ae9f480000000 0x7e7ff9ffc0000000

def z544 : W := mkw 0x2000000900090240 0x4040018f000003c0

def z545 : W := mkw 0x28400009104b3244 0x00800000000f3000

def z546 : W := mkw 0x2000000900090240 0x20c0300f000f0000

def z547 : W := mkw 0x0000000000000000 0x9b00400001100000

def z548 : W := mkw 0x00142808430cc210 0xeebc3848c30fc230

def z549 : W := mkw 0x002ac1f000000000 0x043f818000000000

def z550 : W := mkw 0xc00881f6a82001aa 0x404001fffc0003ff

def z551 : W := mkw 0x0000000000000000 0xfb804e700118fe3f

def z552 : W := mkw 0x003bfffeb8081204 0xfffffffffc08320c

def z553 : W := mkw 0x0004000003048000 0x80800000030fc000

def z554 : W := mkw 0xb09dbdefe30dc370 0xfeffbdeff30fc3f0

def z555 : W := mkw 0x00113e06a8000000 0x7a407e7ffc000000

def z556 : W := mkw 0xc02e415003900122 0xce3c41d0031003f3

def z557 : W := mkw 0x0023d6b228000000 0x0003800000000000

def z558 : W := mkw 0x2859bdefb06b32cc 0xffffbdeff2ef33cc

def z559 : W := mkw 0x000080a000200088 0xdf03c1f003f003ff

def z560 : W := mkw 0xc40881f8542857bf 0x400001f8fc0003ff

def z561 : W := mkw 0x0400000014001405 0xbb804e303d18fc0f

def z562 : W := mkw 0xf09ca9fdc32dc3fa 0xeefc39ffc30fc3ff

def z563 : W := mkw 0x2851beafb86b32cc 0xf7c3bfaffeef33cc

def z564 : W := mkw 0x0014280003048000 0xbfbc7e00031ffc00

def z565 : W := mkw 0xb8c40009536ff3fc 0x8180000003eff3fc

def z566 : W := mkw 0x003ffff6abd6a800 0x7e7ffffffee70000

def z567 : W := mkw 0x00102a0000048800 0x00000a000000cc00

def z568 : W := mkw 0x0000000810081204 0xfb8044783118323f

def z569 : W := mkw 0x2c4194ab746b76dd 0xf7c3b5fffeef33ff

def z570 : W := mkw 0xb8c995eff06b73fc 0xf7c3b5eff2ef33fc

def z571 : W := mkw 0xc42ec1f857b857bf 0xdfbfc1f003f8ffff

def z572 : W := mkw 0x00377e0003d6a800 0xaebfb80003efc000

def z573 : W := mkw 0xc00c81f003b001aa 0xc10001f003f003ff

def z574 : W := mkw 0x000194a220422000 0xf7c3b5af32ef3000

def z575 : W := mkw 0x28513e0fb84b3244 0x20c03e0ffc0f3000

def z576 : W := mkw 0x00377e0003d6a800 0xb7bfb40002ef3000

def z577 : W := mkw 0x002ac1f000000000 0x7e3fcff8fc000000

def z578 : W := mkw 0x840c014857085735 0xffbc4ff8ff18ffff

def z579 : W := mkw 0x0010280000048000 0x20803800000fc000

def z580 : W := mkw 0xc02e415003b001aa 0x893c405003f003ff

def z581 : W := mkw 0xb8fffffffb6ff3fc 0xffffffffffeff3fc

def z582 : W := mkw 0x0400000854085615 0xdb8040700118fe3f

def z583 : W := mkw 0x0022400000900000 0x1103c00000f00000

def z584 : W := mkw 0xf0bee9f583b581ea 0xdf7ff1f703f703ff

def z585 : W := mkw 0x28400009102912cc 0x00000000000003cc

def z586 : W := mkw 0x04113e08544efe15 0xfb807e78fd1ffe3f

def z587 : W := mkw 0xc02ec1f003b001aa 0xce3f81c003e003f0

def z588 : W := mkw 0x0004000003d6a800 0xbb804e0003fffc00

def z589 : W := mkw 0xe86ec1fb33b913ee 0xdf7fc1ff33f003ff

def z590 : W := mkw 0x0400000854085615 0x60800e78fc08fe3f

def z591 : W := mkw 0xe87fffffbbfb33ee 0xffffffffffff33ff

def z592 : W := mkw 0x20377e0903dfaa40 0xffffff8f03ffffc0

def z593 : W := mkw 0x0400000854085615 0x31804e38fc18fc0f

def z594 : W := mkw 0xf0bfffffebbdc3fa 0xffffffffffffc3ff

def z595 : W := mkw 0x0400000854085615 0x28804e58fd18fc33

def z596 : W := mkw 0xf0bee9fdc3bdc3fa 0xeeffb9cfc3efc3f0

def z597 : W := mkw 0x284995ffb86b32cc 0xf7c3b5fffeef33cc

def z598 : W := mkw 0x0022400000000000 0x1e3fc00000000000

def z599 : W := mkw 0x2844000913ffbacc 0x8180000003ffffcc

def z600 : W := mkw 0x000881f000000000 0x400001f000000000

def z601 : W := mkw 0x0004000003900000 0x8100000003f00000

def z602 : W := mkw 0xb0bee9fdc30dc370 0xfefff9ffc30fc3f0

def z603 : W := mkw 0x00377e0003900000 0xbf3ffe0003f00000

def z604 : W := mkw 0x3098294dc00dc250 0x6efc39cfc00fc000

def z605 : W := mkw 0x043ffffeffdefe15 0xfffffffffffffe3f

def z606 : W := mkw 0x043bfffefc085615 0x7e7ffffffc00023f

def z607 : W := mkw 0x0400000854085615 0x008000000008fc00

def z608 : W := mkw 0x000881f6a8000000 0x0040018700000000

def z609 : W := mkw 0x00377e0003d6a800 0x28bc7e00011ffc00

def z610 : W := mkw 0x284080ab306b32cc 0xc1c001af32ef33cc

def z611 : W := mkw 0x003bfff000000000 0x7e3ffff000000000

def z612 : W := mkw 0x3094280dc30dc250 0xaefc380fc30fc000

def z613 : W := mkw 0x00153c000346a000 0xbfbfbc0003eff000

def z614 : W := mkw 0x003bfff6a8d22800 0x7f7ffffffcf03c00

def z615 : W := mkw 0x0023d6b228d22800 0x1103c6303cf03c00

def z616 : W := mkw 0xe84995fb306b33ee 0xf7c3b5ff32ef33ff

def z617 : W := mkw 0xc42ec1f017b015af 0xdf3fc7f03ff03fff

def z618 : W := mkw 0x002bd7f6a8000000 0x5043c7fffc000000

def z619 : W := mkw 0xb09d3f4dc34feb70 0xeefc3fcfc30ffff0

def z620 : W := mkw 0xb8c594ab736ff3fc 0xf7c3b5af33eff3fc

def z621 : W := mkw 0x042ac1f854085615 0xffbfcff8fd18fe3f

def z622 : W := mkw 0xc02ec1f003b001aa 0xd73f81a002e003cc

def z623 : W := mkw 0x00113e000046a800 0x0000300000070000

def z624 : W := mkw 0xc02e415003900122 0x9f3fc05003f00033

def z625 : W := mkw 0x2c41140b744b7655 0xfbc07e7ffd1ffe3f

def z626 : W := mkw 0x00011408104a3204 0xf783b42832ef320c

def z627 : W := mkw 0x003b7f5488000000 0x3e3ffe50cc000000

def z628 : W := mkw 0x3490280dd40dd655 0x20c03e0ffc0ffc00

def z629 : W := mkw 0xb088014dc0094370 0xe6c031cfc20f03f0

def z630 : W := mkw 0x000995f6a8000000 0x7643b5fffc000000

def z631 : W := mkw 0xc03ffff003f6a9aa 0x043fb18002e701c0

def z632 : W := mkw 0x0400000044004411 0x7a004e78fd10cc33

def z633 : W := mkw 0x0023560000d22800 0xb783f60002ff3c00

def z634 : W := mkw 0xb09d3f4feb0dc370 0xeefc3fcfff0fc3f0

def z635 : W := mkw 0x00366a0003948800 0x9f3fca0003f0cc00

def z636 : W := mkw 0xb09c294dc3dfeb70 0xeffc39cfc3fffff0

def z637 : W := mkw 0x0400000044004411 0x00000050cc000033

def z638 : W := mkw 0x00377e0003d6a800 0x153ff60002f73c00

def z639 : W := mkw 0x0004000003d6a800 0x0000000002e70000

def z640 : W := mkw 0xc00881f0002001aa 0xdb0041f0011003ff

def z641 : W := mkw 0x802ec1f003000120 0xde3fc1f0030003f0

def z642 : W := mkw 0xb8ddbde7a367a1e8 0x047fb18702e701c0

def z643 : W := mkw 0x90880144c0004130 0x00000040c0000030

def z644 : W := mkw 0x2851beab306fbacc 0xf7c3bfaf32efffcc

def z645 : W := mkw 0x0000000000000000 0xd30000200000020c

def z646 : W := mkw 0x0036680003948000 0xbfbff80003ffc000

def z647 : W := mkw 0x801c294003048120 0xeebc39c0030fc3f0

def z648 : W := mkw 0x0000000000000000 0x5a00407000000000

def z649 : W := mkw 0x200194ab20090240 0xf6c3b5af320f03c0

def z650 : W := mkw 0xe86fd5fb33fb33ee 0xf7ffb5af32ef33cc

def z651 : W := mkw 0x0000000000000000 0x3a004e0000000000

def z652 : W := mkw 0xc02ec1f003b001aa 0x5e3fc1f002e001c0

def z653 : W := mkw 0x003bfff6a8000000 0x3e7fff8700000000

def z654 : W := mkw 0x28513e0b304fba44 0x20c03e0f300ffc00

def z655 : W := mkw 0x3080000dc0094250 0x0040000fc0000000

def z656 : W := mkw 0xc03eebf48bb001aa 0xdf3fcbf0cff003ff

def z657 : W := mkw 0x909c2944c304c130 0xce3c09c0c300c3f0

def z658 : W := mkw 0xb088014dc0094370 0xeac009cfc108c3f0

def z659 : W := mkw 0x2855bcab336fb2cc 0xffffbdaf33eff3cc

def z660 : W := mkw 0x0000000000422000 0x8180000002ef3000

def z661 : W := mkw 0x4022c0b000b0008a 0x0003800000e00000

def z662 : W := mkw 0xc42e415857985737 0xfbbc4e78fd18fe3f

def z663 : W := mkw 0x0400000854085615 0xc1800078fd18fe3f

def z664 : W := mkw 0xc02fd7f003f229aa 0xdf3fc7f003f03fff

def z665 : W := mkw 0xc03e6b5003948922 0x083c4a500110cc33

def z666 : W := mkw 0xb08c0149430dc370 0xcebc01c0030fc3f0

def z667 : W := mkw 0x084194a23062308c 0xb783b42032ef300c

def z668 : W := mkw 0x0019bff6a8000000 0x60403ffffc000000

def z669 : W := mkw 0x28400009106b32cc 0xf380042832ef33cc

def z670 : W := mkw 0x0037feb22bd6a800 0xbfbffe303ffffc00

def z671 : W := mkw 0xc03ffff003f6a9aa 0xbfbfff8003fffdc0

def z672 : W := mkw 0x084194a23062308c 0xd70385a032e033cc

def z673 : W := mkw 0x0000000000000000 0x810000000110023f

def z674 : W := mkw 0x90bffff6eb04c130 0x7e7ffffffd00c030

def z675 : W := mkw 0xb0b77e0943dfeb70 0xbfbffe0003fffff0

def z676 : W := mkw 0x0000000000000000 0x0800405001100033

def z677 : W := mkw 0x4422c0b854b8569f 0xfb83ce78fdf8fe3f

def z678 : W := mkw 0xc004000003b001aa 0xdb00407003f003ff

def z679 : W := mkw 0x0400000854085615 0xbb804e000118fe3f

def z680 : W := mkw 0x0000000000000000 0x100046303c000000

def z681 : W := mkw 0x0008014000000000 0x4e3c01c000000000

def z682 : W := mkw 0xb0bbffffe8094370 0x7e7ffffffc0003f0

def z683 : W := mkw 0xf0aec1fdc3b943fa 0xdf7fc1ffc3f003ff

def z684 : W := mkw 0xb0be6b5dcb0dc370 0xeefc7bdfcf0fc3f0

def z685 : W := mkw 0xc03ffff6abb001aa 0x047fb18702e001c0

def z686 : W := mkw 0x803f7f4003d6a920 0xffbfffc003fffff0

def z687 : W := mkw 0x284080ab302912cc 0xf3c005af300833cc

def z688 : W := mkw 0x0000000000000000 0xfb004e78fd10023f

def z689 : W := mkw 0x8008014000000120 0x400001c0000003f0

def z690 : W := mkw 0x0423560014d23c05 0x1103c6303cf03c0f

def z691 : W := mkw 0x0400000854085615 0xeb800848c118fe3f

def z692 : W := mkw 0xc00c014003b001aa 0xcf3c01c003f003ff

def z693 : W := mkw 0x00377e0003d6a800 0x9f3ff00003f70000

def z694 : W := mkw 0x0400000854085615 0x48004a78fd10ce3f

def z695 : W := mkw 0x284080a9106b32cc 0xd78381a002ef33cc

def z696 : W := mkw 0x003bfff6a8000000 0x5e7ff1f700000000

def z697 : W := mkw 0xb8c881eff02953fc 0x404001eff00003fc

def z698 : W := mkw 0xc03f7f5003d6a922 0xbfbffe5003fffc33

def z699 : W := mkw 0x003ffff6ab900000 0xff7ffffffff00000

def z700 : W := mkw 0x2841140b304b3244 0xe6c0358f320f33c0

def z701 : W := mkw 0x0400000854085615 0x7a004e78fc00023f

def z702 : W := mkw 0xc02ec1f003f6a9aa 0xdfbfc1f003ffffff

def z703 : W := mkw 0x402ac1f000b0008a 0x5f3fc1f000f0000f

def z704 : W := mkw 0xc404000857b857bf 0x8180000003f8ffff

def z705 : W := mkw 0x00377e0003048000 0xbebffe00030fc000

def z706 : W := mkw 0x2873feab306b32cc 0xffffffaf32ef33cc

def z707 : W := mkw 0x284194a3206320c8 0xa6c3b18702ef01c0

def z708 : W := mkw 0xc019bff00066a9aa 0x60803ff0000fffff

def z709 : W := mkw 0xc02ec1f003b001aa 0x8d3fc1d003f003ff

def z710 : W := mkw 0xb09c294dc30dc370 0xfffc7fffff1fc3ff

def z711 : W := mkw 0x2001140100432040 0xb7c3b58702ef31c0

def z712 : W := mkw 0xb49c294dd70dd775 0x24fc3f8ffe0ffdc0

def z713 : W := mkw 0xf48881fdd42957ff 0x404001fffc0003ff

def z714 : W := mkw 0xb08c014dc3094370 0xeefc31cfc30f03f0

def z715 : W := mkw 0xc02ec1f223b001aa 0xdf7fc1ff33f003ff

def z716 : W := mkw 0xd0be695483948122 0x003c000000000000

def z717 : W := mkw 0xa00c014103010160 0xce7c31c7030703f0

def z718 : W := mkw 0x04377e0857defe15 0x443fb078fee7023f

def z719 : W := mkw 0x087bfff6a8622088 0x7e7ffffffce00000

def z720 : W := mkw 0xb09c294583058160 0x847c3187030703f0

def z721 : W := mkw 0x284194a3206320c8 0xf7c3b5a702ef33cc

def z722 : W := mkw 0x00377e0003d6a800 0xb7bfbe0002effc00

def z723 : W := mkw 0xb49c294dd70dd775 0xfffc3deff31fffff

def z724 : W := mkw 0x003aebf6a8000000 0x7a7c4ffffc000000

def z725 : W := mkw 0xb49c294dd70dd775 0xfffc79ffc31fffff

def z726 : W := mkw 0x043bfffefc085615 0x85ffb1870118fe3f

def z727 : W := mkw 0x2008014900090240 0xeefc31cf020f03c0

def z728 : W := mkw 0x003bfff6a8d22800 0xfffffffffeff3c00

def z729 : W := mkw 0x24142809570dd655 0xfffc7fffff1fffff

def z730 : W := mkw 0x00377e0003d6a800 0xa5bfbe0003fffc00

def z731 : W := mkw 0x003b7f56a8000000 0x6e7c7fdffc000000

def z732 : W := mkw 0x284194ab306b32cc 0x0443b18702e703cc

def z733 : W := mkw 0xd0be6954c394c132 0x083c0840c100c030

def z734 : W := mkw 0xc02ac1f000b001aa 0x5f3fc1f000f003ff

def z735 : W := mkw 0x800c81e0032001a8 0xdf3fc1f003f003ff

def z736 : W := mkw 0x00377e048bd6a800 0xbfbffe00cffffc00

def z737 : W := mkw 0x28411409106b32cc 0xf7c3b58f02ef33cc

def z738 : W := mkw 0xb09c294dc30dc370 0xfefc3deff30fc3f0

def z739 : W := mkw 0x284194ab306b32cc 0xf7c3bfaffeef33cc

def z740 : W := mkw 0xb09c294583058160 0x84fc3187030fc1c0

def z741 : W := mkw 0xb49c294597059565 0x157c77b73e173dcf

def z742 : W := mkw 0x003bfff6a8000000 0x387ffe7ffc000000

def z743 : W := mkw 0x284194ab306b32cc 0xe7c3b18f02ef33cc

def z744 : W := mkw 0x2c4194ab346b36cd 0xf7c3b7af3eef3fcc

def z745 : W := mkw 0x00182946a8000000 0x6e7c39cffc000000

def z746 : W := mkw 0x003bfff6a8048800 0x7e7ffffffc00cc00

def z747 : W := mkw 0x403bfff6a8f2288a 0x7f7ffffffcf03c0f

def z748 : W := mkw 0x000c81f6abd6a800 0xc1c001fffffffc00

def z749 : W := mkw 0xb09c294d830d8360 0xeefc39cfc20f03c0

def z750 : W := mkw 0xc0153e06abb001aa 0xa1403e0ffff003ff

def z751 : W := mkw 0x2841140b304b3244 0xf7c3b58f32ef33c0

def z752 : W := mkw 0x2c4881fffc2956dd 0x404001fffc0003ff

def z753 : W := mkw 0x2c4194ab746b76dd 0xf7c3f7fffeff3fff

def z754 : W := mkw 0x2004000903090240 0xeefc318f030f03c0

def z755 : W := mkw 0x284194a3206320c8 0x6643b18f02e701c0

def z756 : W := mkw 0x0c63d6a234f23c8d 0x1103c6303cf03c0f

def z757 : W := mkw 0x90be6b54cb94c930 0x083c4a50cd10cc30

def z758 : W := mkw 0x003bfff6a8000000 0x7efffffffc08fc00

def z759 : W := mkw 0x2876eaab33bd9acc 0x487c4baf3110cfcc

def z760 : W := mkw 0x284194a3306330cc 0x0443b58732e731c0

def z761 : W := mkw 0x003b7f46a8000000 0x7e7fffcffc000000

def z762 : W := mkw 0xf09c294dc39dc372 0xeefc39cfc31fc3f3

def z763 : W := mkw 0x4863d4ba30fa328e 0xfb83c47831f8323f

def z764 : W := mkw 0x20142809030d8240 0xe6fc318f020f03c0

def z765 : W := mkw 0x00377e0003d6a800 0xbfbffe50cffffc00

def z766 : W := mkw 0x284194ab306b32cc 0xf7c3f7bf3eef33cc

def z767 : W := mkw 0x003a6b5488000000 0x7e7c7ffffc000000

def z768 : W := mkw 0x00193f46a8000000 0x7e7c7ffffc000000

def z769 : W := mkw 0xb09c294dc30dc370 0xeefc3fcfc30ffff0

def z770 : W := mkw 0x003bfff6a8622088 0xfffffffffeef33cc

def z771 : W := mkw 0x00377e0483d6a800 0xbffffe0fc3fffc00

def z772 : W := mkw 0x0036680003948000 0xbfbffe0003fffc00

def z773 : W := mkw 0x003ae9f480000000 0x7e7ffffffc000000

def z774 : W := mkw 0x4863d4b220f2208a 0x0003800000e00000

def z775 : W := mkw 0xb49c294dd70dd775 0xfffc3fefff0ffffc

def z776 : W := mkw 0xc02ec1f483b001aa 0xdf7fc1ffc3f003ff

def z777 : W := mkw 0x284194ab306b32cc 0xf7c3b5af33ff33ff

def z778 : W := mkw 0x284194ab306b32cc 0xffc3b5ef33ef33fc

def z779 : W := mkw 0xb09c294dc30dc370 0xfffc7fffff1ffff0

def z780 : W := mkw 0x284194ab306b32cc 0xf7c3b5ff32ef33ff

def z781 : W := mkw 0xc00c81e003b001aa 0xdf3f81e003f003ff

def z782 : W := mkw 0xc02ec1f6abb001aa 0xdf7fc1f703f003ff

def z783 : W := mkw 0x284194ab306b32cc 0xd743b1af32e703cc

def z784 : W := mkw 0x284194a3206320c8 0x9743b18702e701c0

def z785 : W := mkw 0x003aebf6a8000000 0x6e7c7bfffc000000

def z786 : W := mkw 0x0c63d6b23c62348d 0x1103c6303cf03c0f

def z787 : W := mkw 0x284194ab306b32cc 0xf7c3bfaf32efffcc

def z788 : W := mkw 0x0018a9f6a8000000 0x447c31fffc000000

def z789 : W := mkw 0x003bfff6a8000000 0x767fb5fffc000000

def z790 : W := mkw 0x2000000900090240 0xf7c3b18f02ef03c0

def z791 : W := mkw 0x284194ab306b32cc 0x04c3b18702ef31c0

def z792 : W := mkw 0xb09c2b4dc30dcb70 0xeefc3bcfc30fcff0

def z793 : W := mkw 0x200080a1002100c8 0x0443b18702e701c0

def z794 : W := mkw 0x284194ab706b72dc 0xffc3ffeff3fffffc

def z795 : W := mkw 0xb09c2945c305c170 0x6e7c39cfc307c1f0

def z796 : W := mkw 0xc02ec1f003b001aa 0x5e3fc1f002e003ff

def z797 : W := mkw 0x94be6b44c794cd31 0x083c4a50cd10cc33

def z798 : W := mkw 0x00377e0003d6a800 0x8dbffa0003fffc00

def z799 : W := mkw 0x284194ab306b32cc 0xe6c3b1af32ef03cc

def z800 : W := mkw 0xb4840009570dd775 0x80800000030fc3ff

def z801 : W := mkw 0x20011409104b3244 0xf7c3b5af32ef33cc

def z802 : W := mkw 0x003bfff6a8000000 0xfefffffffe0f0000

def z803 : W := mkw 0x000881f6a8000000 0x4e7c01fffc000000

def z804 : W := mkw 0x98ddbde6f366f1bc 0x193f8c60f1e0f03c

def z805 : W := mkw 0x003bfff6a8422000 0x7f7ffffffce03000

def z806 : W := mkw 0x00377e0003d6a800 0xffbfff8003ffffc0

def z807 : W := mkw 0x003aebf6a8000000 0x407c01fffc000000

def z808 : W := mkw 0x003bfff6a846a800 0xfffffffffd1ffc00

def z809 : W := mkw 0x0400000854085615 0x68804e78fd18fe3f

def z810 : W := mkw 0x00377e0003d6a800 0xffbffe2833fffc00

def z811 : W := mkw 0xc42ec1f857b857bf 0x24bf8f88fee8fdc0

def z812 : W := mkw 0xd4be695cd79cd737 0xfbbc4e78fd18fe3f

def z813 : W := mkw 0xc02ec1f003b001aa 0xdfbfc1f003f8ffff

def z814 : W := mkw 0x284194ab706b72dc 0xf7c3b5af33eff3fc

def z815 : W := mkw 0xc02ec1f003b001aa 0xdf3fc7f003f03fff

def z816 : W := mkw 0xb0ab574dc0db6b70 0x5143c7cfc0f03ff0

def z817 : W := mkw 0x2c4194ab746b76dd 0xffc3fffffeef33ff

def z818 : W := mkw 0xc00c81f6abb001aa 0xc14001fffff003ff

def z819 : W := mkw 0x284194ab306b32cc 0xffc3ffffffffffcc

def z820 : W := mkw 0x003bfff6a8900000 0x7f7ffffffcf00000

def z821 : W := mkw 0x0018294480000000 0x6e7c3fcffc000000

def z822 : W := mkw 0x003bfff6a8000000 0x587fcffffc000000

def z823 : W := mkw 0x00113e06a8000000 0x2e7c3e0ffc000000

def z824 : W := mkw 0x003bfff6a8d22800 0xfffffffffdf8fc00

def z825 : W := mkw 0x284194a3306330cc 0x7743b5af32e731cc

def z826 : W := mkw 0xc03ffff6abf6a9aa 0x047fb18702e701c0

def z827 : W := mkw 0xb09c294dc39dc370 0xeffc39cfc3ffc3f0

def z828 : W := mkw 0x2400000954095655 0xfb804e78ff1fffff

def z829 : W := mkw 0x403bfff6a8b0008a 0x7e7ffffffce00000

def z830 : W := mkw 0x287a6b5d986b32cc 0x89bc4a50ceef33cc

def z831 : W := mkw 0x2c4194ab746b76dd 0xf7c3b5ffffffffff

def z832 : W := mkw 0xb09c294dd30dd374 0xfffc7feff31ffffc

def z833 : W := mkw 0xb09c294583058160 0x667c318f020701c0

def z834 : W := mkw 0xb49c294dc70dc771 0xfffc7fdfcf1ffff3

def z835 : W := mkw 0x00153c000346a000 0xbfbffe0003fffc00

def z836 : W := mkw 0x00337e06a8000000 0x7e7ffe7ffc000000

def z837 : W := mkw 0xec4881fb742957ff 0x404001fffc0003ff

def z838 : W := mkw 0xb49c294dd70dd775 0xeefc39cfff0fc3f0

def z839 : W := mkw 0xa01c2949030d8360 0xeefc39cf030fc3f0

def z840 : W := mkw 0x003bfff6a8000000 0x7e7ffffffd100033

def z841 : W := mkw 0x2c513e0b744ffe55 0x20c03e0ffc0ffc00

def z842 : W := mkw 0xb09c294dc30dc370 0xfefc79ffc30fc3f0

def z843 : W := mkw 0x003bfff6a8200088 0x7e7ffffffee001c0

def z844 : W := mkw 0xb49c294dd70dd775 0xfffc3dffff0ff3ff

def z845 : W := mkw 0x802e414003900120 0xdf3fc1f003f003ff

def z846 : W := mkw 0xb09c2945c305c170 0xaefc39c7c30fc1f0

def z847 : W := mkw 0x4863d6b238f2308e 0x1103c6303cf0300f

def z848 : W := mkw 0xb09c294583058160 0x247c398fc20701c0

def z849 : W := mkw 0x00377e0003d6a800 0xbfbffe5003fffc33

def z850 : W := mkw 0x2c4194ab746b76dd 0xffc3ffaf33ffffff

def z851 : W := mkw 0xc02ec1f003b001aa 0xffbfc5f003f833ff

def z852 : W := mkw 0x003b7f56a8000000 0x7a7c7e7ffc000000

def z853 : W := mkw 0x284194a3306330cc 0xb7c3b5a732ef31cc

def z854 : W := mkw 0x2c4194a3646364d9 0x0c43fbd7cff7cdf3

def z855 : W := mkw 0x284194bb386b32cc 0xf7c3b5bf3eef33cc

def z856 : W := mkw 0x90be6b4483948920 0x083c4a000110cc00

def z857 : W := mkw 0xb09c294583058160 0x24fc3987020fc1c0

def z858 : W := mkw 0xbcc40009576ff7fd 0x8180000003ffffff

def z859 : W := mkw 0x40377e1003d6a802 0xbfbffe1003fffc03

def z860 : W := mkw 0x00377e0003d6a800 0xffffff8f03fffc00

def z861 : W := mkw 0xb49c294dd70dd775 0xeffc39ffff1fffff

def z862 : W := mkw 0x90be6b44c394c930 0x083c0840c100c030

def z863 : W := mkw 0x284194a3206320c8 0x24c3b58702ef31c0

def z864 : W := mkw 0x2c4194ab346b36cd 0xffc3ffbf3fffffcf

def z865 : W := mkw 0xe86f555b33db3366 0x28fc745f311f3033

def z866 : W := mkw 0x0c63d6aa74fa7e9d 0xfb83ce78fdf8fe3f

def z867 : W := mkw 0xb09c294dc30dc370 0xc4fc31cfc30fc3f0

def z868 : W := mkw 0x284196ab306b3acc 0xf7c3b7af32ef3fcc

def z869 : W := mkw 0x284194ab206b22c8 0x4443b18f02e703c0

def z870 : W := mkw 0x003bfff6a8000000 0x2c7fffdffc000000

def z871 : W := mkw 0x2c4194ab746b76dd 0xffc3bdffffeff3ff

def z872 : W := mkw 0x00337e000046a800 0xbfbffe0002effc00

def z873 : W := mkw 0xb09c294583058160 0xa6fc3187020f01c0

def z874 : W := mkw 0xc02e415003b001aa 0x9f3fc05003f003ff

def z875 : W := mkw 0x20142809430dc250 0xeefc39cfc30fc3f0

def z876 : W := mkw 0x403bfff6a8900002 0x7e7ffffffc100003

def z877 : W := mkw 0x3098294dc00dc250 0xeefc39cfc20fc3c0

def z878 : W := mkw 0xb49c294dd70dd775 0xfefc7fffff0fc3ff

def z879 : W := mkw 0x3cd13c0ff44ff655 0x20c03e0ffc0ffc00

def z880 : W := mkw 0x801c294483048120 0xeefc39cfc30fc3f0

def z881 : W := mkw 0xb49c294dd70dd775 0xfffc7fcfc31fffff

def z882 : W := mkw 0xbcc881eff42957fd 0x404001fffc0003ff

def z883 : W := mkw 0x00377e0003d6a800 0x99bfce0003fffc00

def z884 : W := mkw 0x00193f46a8000000 0x247c3f8ffc000000

def z885 : W := mkw 0x34913e0dd44ffe55 0x20c03e0ffc0ffc00

def z886 : W := mkw 0x0018a9f6a8000000 0x7e7c7ffffc000000

def z887 : W := mkw 0x003bfff6a846a800 0x7e7ffffffc070000

def z888 : W := mkw 0x003bfff6a8000000 0x5e7ff1fffc000000

def z889 : W := mkw 0x2018294d80090240 0xe6fc318f020f03c0

def z890 : W := mkw 0x00377e06abd6a800 0xbffffe0703fffc00

def z891 : W := mkw 0x0c63d6ba7c6a769d 0xfb83ce78fdf8fe3f

def z892 : W := mkw 0xb484000957dfff75 0x8180000003ffffff

def z893 : W := mkw 0x00377e0003d6a800 0x35bffe0002fffc00

def z894 : W := mkw 0xb09c294dd30dd374 0xfffc7dfff31ff3ff

def z895 : W := mkw 0xb09c2945c305c170 0x047c31c7c20701f0

def z896 : W := mkw 0x003bfff6a8000000 0x6e7fbfcffc000000

def z897 : W := mkw 0xb09c294583058160 0x0c7c31c7030701f0

def z898 : W := mkw 0x0400000854085615 0xff807e78ff1ffe3f

def z899 : W := mkw 0x003bfff6a8422000 0x7efffffffc0f3000

def z900 : W := mkw 0xa40c014957095775 0xfffc7fffff1fffff

def z901 : W := mkw 0xc02ac1f0002001aa 0xdf3fc1f002e003ff

def z902 : W := mkw 0x003bfff6a8000000 0x7f7ffffffc10000f

def z903 : W := mkw 0x284194ab606b62d8 0xeec3b9cfc3efc3f0

def z904 : W := mkw 0xc02ec1f003b001aa 0xdf3fcbf003f0cfff

def z905 : W := mkw 0x003bfff6a8422000 0x7e7ffffffee70000

def z906 : W := mkw 0xb49c294dd70dd775 0xeefc7bffff1fcfff

def z907 : W := mkw 0xb09c294dc30dc370 0xeffc39cfc31fc3ff

def z908 : W := mkw 0x284194ab206b22c8 0x84c3b18702ef03c0

def z909 : W := mkw 0xb09c294d830d8360 0x24fc318f020f01c0

def z910 : W := mkw 0x0863d4a230f2308c 0x1103c42030f0300c

def z911 : W := mkw 0x003bfff6a8000000 0xfe7ffffffe0003c0

def z912 : W := mkw 0x0019bfe6a8000000 0x7e7fbfeffc000000

def z913 : W := mkw 0x200080a9102912cc 0xf7c3b5af32ef33cc

def z914 : W := mkw 0x00193f46a8000000 0x287c3e4ffc000000

def z915 : W := mkw 0xb49c294dc70dc771 0xeefc39cfc31fcff3

def z916 : W := mkw 0x0400000054005415 0x7b004e78fd10fc3f

def z917 : W := mkw 0x002ac1f6a8000000 0x447f81fffc000000

def z918 : W := mkw 0x0863d6a220f22888 0x1103c60000f03c00

def z919 : W := mkw 0x003bfff6a8000000 0x547ff7fffc000000

def z920 : W := mkw 0xb09c294583058160 0x447c31c7020703f0

def z921 : W := mkw 0x003bfff6a8000000 0xfffffffffc083000

def z922 : W := mkw 0x284080ab302912cc 0xf7c3b1af32ef03cc

def z923 : W := mkw 0xc02ec1f003b001aa 0xd73f81a003f003ff

def z924 : W := mkw 0xb4840009570dd775 0x80800000030ffff0

def z925 : W := mkw 0xc02ec1f003b001aa 0xffbff1f003ff03ff

def z926 : W := mkw 0x284194a3206320c8 0x7e43fffffee701c0

def z927 : W := mkw 0xb09c294dd30dd374 0xfffc7fffff0ff3fc

def z928 : W := mkw 0x284194a3206320c8 0x1543b58702e731c0

def z929 : W := mkw 0x2c513e0ffc4b7655 0x20c03e0ffc0ffc00

def z930 : W := mkw 0xb0a7d6bb6b0dc370 0x9083c6303f0fc3f0

def z931 : W := mkw 0xb09c294583058160 0xee7c39cfc30703f0

def z932 : W := mkw 0x94be6b4cd79cdf35 0xfbbc4e78fd18fe3f

def z933 : W := mkw 0xc02ec1f003b001aa 0x043f818002e003ff

def z934 : W := mkw 0x80377e0003d6a920 0xbfbffe0003fffff0

def z935 : W := mkw 0xb09c294dc30dc370 0xfffc3dcfc30ff3f0

def z936 : W := mkw 0x00377e100bd6a800 0xbfbffe100ffffc00

def z937 : W := mkw 0xb49c294dd70dd775 0xfefc7fffff0ffff0

def z938 : W := mkw 0x284194a3206320c8 0xf743b5af32e703cc

def z939 : W := mkw 0xc02ec1f003b001aa 0xc53f81f003f003ff

def z940 : W := mkw 0xc02ec1f003b001aa 0xffbfc9f003f8c3ff

def z941 : W := mkw 0x284196ab386b32cc 0xf7c3b7af3eef33cc

def z942 : W := mkw 0x003bfff6a846a800 0xfffffffffeeffc00

def z943 : W := mkw 0xc02ec1f003b001aa 0xff3fcff003f003ff

def z944 : W := mkw 0x284194ab306b32cc 0xffc3bdeff2ef33cc

def z945 : W := mkw 0x003bfff6a8000000 0xfefffffffd08c000

def z946 : W := mkw 0x2001140100432040 0x0443b18702e701c0

def z947 : W := mkw 0x003bfff6a8000000 0x3e7fff8ffc000000

def z948 : W := mkw 0x2c4194ab746b76dd 0xf7c3b5affeef33cc

def z949 : W := mkw 0x2c4194ab346b36cd 0xf7c3b5af32ff3fcf

def z950 : W := mkw 0x2418294dd4095655 0xfffc7fffff1fffff

def z951 : W := mkw 0x284194ab306b32cc 0x64c3b5af32ef33cc

def z952 : W := mkw 0xa00c014913091364 0xfffc75ff331f33ff

def z953 : W := mkw 0xb49c294dc70dc771 0xeefc3bcfcf0fcff0

def z954 : W := mkw 0x003b7f4480000000 0x7e7ffffffc000000

def z955 : W := mkw 0x003bfff6a8000000 0x6e7fb9fffc000000

def z956 : W := mkw 0x284194a3206320c8 0xbfc3ff8703fffdc0

def z957 : W := mkw 0xb09c294583058160 0xeefc39c7030fc3f0

def z958 : W := mkw 0xc02ec1f003b001aa 0x593fc1f001f003ff

def z959 : W := mkw 0x0027540003d22000 0xbfbffe0003fffc00

def z960 : W := mkw 0xec44000957fb77ff 0x8180000003ffffff

def z961 : W := mkw 0xc0377e0003d6a922 0xbfbffe0003fffc33

def z962 : W := mkw 0xb09c294dc30dc370 0x2cfc39cfc30fc1f0

def z963 : W := mkw 0xb09c294583058160 0xeefc39cfc30fc1c0

def z964 : W := mkw 0x0033fea220000000 0x7e7ffffffc000000

def z965 : W := mkw 0x4863d6b230f2388e 0x1103c63030f03c0f

def z966 : W := mkw 0x90be6b4cc39ccb30 0xfbbc4e48c118fe30

def z967 : W := mkw 0x284194ab306b32cc 0xffc3f5af33ff33cc

def z968 : W := mkw 0x403bfff6a8b0008a 0xff7ffffffdf0023f

def z969 : W := mkw 0x284194ab306b32cc 0xffc3f5ff32ef33cc

def z970 : W := mkw 0xb09c294dc30dc370 0xeefc39ffff0fc3f0

def z971 : W := mkw 0x0026400003d6a800 0x85bf800003fffc00

def z972 : W := mkw 0x003b7f56a8000000 0x3e7ffe5ffc000000

def z973 : W := mkw 0x00377e0003d6a800 0xbfbffe303ffffc00

def z974 : W := mkw 0xf484000957bdd7ff 0x8180000003ffffff

def z975 : W := mkw 0x284194ab206b22c8 0xf7c3b1af02ef03cc

def z976 : W := mkw 0x284194ab306b32cc 0x95c3b5a732ef33cc

def z977 : W := mkw 0xb09c294dc30dc370 0xeffc39cfc31ffff0

def z978 : W := mkw 0x00377e06abd6a800 0xfffffe7ffffffc00

def z979 : W := mkw 0xb09c294dc30dc370 0xaefc3987030fc3f0

def z980 : W := mkw 0x003b7f56a8000000 0x207c3e0ffc000000

def z981 : W := mkw 0x003bfff6a8d6a800 0x7ffffffffcfffc00

def z982 : W := mkw 0x003bfff6a8d22800 0x7e7ffffffce00000

def z983 : W := mkw 0xc02ec1f003b481aa 0xdfbfc1f003ffc3ff

def z984 : W := mkw 0x284194a3206320c8 0x1443b5a732e701c0

def z985 : W := mkw 0x2400000954095655 0xfbc07e7ffd1ffe3f

def z986 : W := mkw 0xd0be695483948122 0x083c405001100033

def z987 : W := mkw 0x0018a9f6a8000000 0x487c09fffc000000

def z988 : W := mkw 0xb09c294dc30dc370 0xfefc7fcfc30fc3f0

def z989 : W := mkw 0x00377e0003d6a800 0xbfbffe3003fffc0f

def z990 : W := mkw 0x0026400003d6a800 0xbfbfce0003fffc00

def z991 : W := mkw 0xb09c2945c305c170 0x047c3987c207c1c0

def z992 : W := mkw 0xc02ec1f003b489aa 0xdf3fc1f003f0cfff

def z993 : W := mkw 0xb09c294dc30dc370 0x64fc39cfc20fc3f0

def z994 : W := mkw 0xc03bfff6a8000122 0x7e7ffffffc000033

def z995 : W := mkw 0x284194a3206320c8 0xf7c3b5af32ef31c0

def z996 : W := mkw 0xb098294dc00dc370 0x6efc39cfc00fc3f0

def z997 : W := mkw 0x284194ab306b32cc 0xffc3ffffffff33ff

def z998 : W := mkw 0x003bfff6a8000000 0x647fbffffc000000

def z999 : W := mkw 0x403bfff6a8b0008a 0xff7ffffffef003cf

def z1000 : W := mkw 0x2c4194ab346b36cd 0xffc3f7ff3fff3fff

def z1001 : W := mkw 0xc02ec3f00bb001aa 0xdf3fc3f00ff003ff

def z1002 : W := mkw 0xc02ec3f003b009aa 0xdf3fc3f003f00fff

def z1003 : W := mkw 0xb09c294d930d9364 0xf7fc35af320f33cc

def z1004 : W := mkw 0x70b2e8bdc0bdc2da 0x31c3f83fc0ffc00f

def z1005 : W := mkw 0x284194ab306b32cc 0x0443b18f32e701c0

def z1006 : W := mkw 0xb09c294dc30dc370 0xe6fc31cfc20f03f0

def z1007 : W := mkw 0xb09c294d830d8360 0xeefc31cf030f03f0

def z1008 : W := mkw 0xc00c81f0032001aa 0xdf3f81f003e003ff

def z1009 : W := mkw 0xc026c0a003b001aa 0xdf3fc1a003f003ff

def z1010 : W := mkw 0x2c4194ab746b76dd 0xf7c3bfafffffffff

def z1011 : W := mkw 0x002ac1f6a8000000 0x487c41fffc000000

def z1012 : W := mkw 0x2c4194ab746b76dd 0xffc3bfefffeffffc

def z1013 : W := mkw 0xb09c294dc30dc370 0xeefc7bcfc31fcff0

def z1014 : W := mkw 0xb08c0149430dc370 0xeefc31cf030fc3f0

def z1015 : W := mkw 0xd0be6b54cb94c132 0x083c4a50cd10c033

def z1016 : W := mkw 0x00377e0003d6a800 0xaebfbe0003effc00

def z1017 : W := mkw 0xd0be6b54c394c932 0x083c4a50c110cc33

def z1018 : W := mkw 0xb49c294dd70dd775 0xeffc3fcfff1fffff

def z1019 : W := mkw 0xb09c294583058160 0x447c31cfc20701c0

def z1020 : W := mkw 0x0036680003d6a800 0xbfbff80003fffc00

def z1021 : W := mkw 0xd4be6954c794c533 0x083c4a50cd10cc33

def z1022 : W := mkw 0xb09c294dc30dc370 0xfffc7fffc31fffff

def z1023 : W := mkw 0xb49c294dd70dd775 0xeffc7bdfcf1fffff

def z1024 : W := mkw 0x284194ab306b32cc 0x5543b5af32e733cc

def z1025 : W := mkw 0xb09c294dd30dd374 0xeefc39eff30fc3fc

def z1026 : W := mkw 0x003bfff6a8000000 0xfe7ffffffd000230

def z1027 : W := mkw 0x0400000854085615 0x99804e70fd18fe3f

def z1028 : W := mkw 0xb49c294dc70dc771 0xeefc39dfcf0fc3f3

def z1029 : W := mkw 0x00377e0003d6a800 0xbfbffe0003fffe3f

def z1030 : W := mkw 0x284194ab306b32cc 0xffc3ffff33ffffff

def z1031 : W := mkw 0x284194ab706b72dc 0xffc3ffffffeff3fc

def z1032 : W := mkw 0x00337e06a8000000 0x247fbe0ffc000000

def z1033 : W := mkw 0xa00c014943094370 0xeefc39cfc30fc3f0

def z1034 : W := mkw 0x0018294480000000 0x6e7c39fffc000000

def z1035 : W := mkw 0xb09c294dc30dc370 0x047c3187020703f0

def z1036 : W := mkw 0x002ac1f6a8000000 0x7e7fcffffc000000

def z1037 : W := mkw 0xc02ec1f003b001aa 0xcf3f81c003f003ff

def z1038 : W := mkw 0x00153e06abd6a800 0xa1c03e0ffffffc00

def z1039 : W := mkw 0x003bfff6a8048000 0x7efffffffc0fc000

def z1040 : W := mkw 0xc02ec1f003b001aa 0xdf3fcbf0cff003ff

def z1041 : W := mkw 0xd0be695cc39cc332 0xfbbc4878c118c23f

def z1042 : W := mkw 0xb09c294583058160 0xbffc7f87031ffdc0

def z1043 : W := mkw 0x201c294d830d8240 0xeefc39cfc30fc3c0

def z1044 : W := mkw 0xc02ec1f003b001aa 0xff3fc9f8c3f003ff

def z1045 : W := mkw 0xc02ec1f003b001aa 0xdf3fc7f03ff003ff

def z1046 : W := mkw 0x4c63d4b234f2348f 0x1103c6303cf03c0f

def z1047 : W := mkw 0x284194a3206320c8 0xdf43f1f703f703ff

def z1048 : W := mkw 0x003bfff6a8000000 0x347fffbffc000000

def z1049 : W := mkw 0xa00c014103010160 0x047c3187020701c0

def z1050 : W := mkw 0xc02ec1f003b001aa 0xff3fc5f833f003ff

def z1051 : W := mkw 0xb49c294dd70dd775 0x85fc3187031fffff

def z1052 : W := mkw 0x284194a3306330cc 0x0543b18702e731cc

def z1053 : W := mkw 0x284194a3206320c8 0x4443b1a702e703cc

def z1054 : W := mkw 0xc02ec1f003b001aa 0xdf3fc1f8fff003ff

def z1055 : W := mkw 0x284194ab306b32cc 0xf7c3f5bf32ff33cf

def z1056 : W := mkw 0xc02ec1f22bb001aa 0xdf3fc1f03ff003ff

def z1057 : W := mkw 0x0019bde6a0000000 0x7e7ffffffc000000

def z1058 : W := mkw 0x803bfff6a8000120 0x7e7ffffffc0003f0

def z1059 : W := mkw 0xb09c294dc30dc370 0x04fc3187020fc1c0

def z1060 : W := mkw 0xb09c294dc39dcb70 0xeefc39cfc31fcff0

def z1061 : W := mkw 0x2014280103058040 0x047c3187020701c0

def z1062 : W := mkw 0xc02ec1f003b001aa 0x993fc07003f003ff

def z1063 : W := mkw 0x00153e000346a800 0xbfbfbe0003effc00

def z1064 : W := mkw 0xb09c294dc30dc370 0xaefc398fc30fc1c0

def z1065 : W := mkw 0x284080a9106b32cc 0xf7c3b1af02ef33cc

def z1066 : W := mkw 0x002ac1f000200088 0xdf3fc1f003f003ff

def z1067 : W := mkw 0x00153c0003d6a800 0xbfbfbc0003fffc00

def z1068 : W := mkw 0xb09c294583058160 0xdf7c71f7031703ff

def z1069 : W := mkw 0x00377e0003d6a800 0x39bffe0001fffc00

def z1070 : W := mkw 0x003bfff6a8000000 0x767fbfaffc000000

def z1071 : W := mkw 0x284194ab706b72dc 0xf7c3bdaff2eff3cc

def z1072 : W := mkw 0x0400000854085615 0xff804ff8ff18ffff

def z1073 : W := mkw 0x284194ab306b32cc 0xb7c3b58702ef33cc

def z1074 : W := mkw 0xc02ec1f003b001aa 0x4c3fc1f003f003ff

def z1075 : W := mkw 0x2c4194ab746b76dd 0xf7c3b5af32efffcc

def z1076 : W := mkw 0xb09c294583058160 0x0c7c39870307c1c0

def z1077 : W := mkw 0x20142809130d9244 0xfffc7faf331fffcc

def z1078 : W := mkw 0xb49c294dd70dd775 0xeefc39cfc30fc3ff

def z1079 : W := mkw 0x003ae9f6a8000000 0x7e7ff9fffc000000

def z1080 : W := mkw 0x284194a3206320c8 0x3643b58702e701c0

def z1081 : W := mkw 0xb09c2945c305c170 0xce7c39c7c307c3f0

def z1082 : W := mkw 0xb09c294dc30dc370 0xeefc79dfc31fc3f3

def z1083 : W := mkw 0x000194a220622088 0xf7c3b5af32ef33cc

def z1084 : W := mkw 0xf09c295dc30dc372 0xeefc39dfc30fc3f3

def z1085 : W := mkw 0xb49c294dd70dd775 0xfffc79ffff1fc3ff

def z1086 : W := mkw 0xb09c294583058160 0x8e7c3187030701c0

def z1087 : W := mkw 0x284194a3306330cc 0x0443b1a732e701cc

def z1088 : W := mkw 0xb0942809430dc370 0xeefc398f030fc3f0

def z1089 : W := mkw 0x2018294dc0094250 0xeefc39cfc30fc3f0

def z1090 : W := mkw 0xb09c294dc30dc370 0xe6fc398fc20fc3c0

def z1091 : W := mkw 0x0863d4b23062308c 0x1103c43030e0300c

def z1092 : W := mkw 0x003bfff6a8000000 0x4c7ffbfffc000000

def z1093 : W := mkw 0x2c4194ab746b76dd 0xf7c3bffffeefffff

def z1094 : W := mkw 0xc02ec1f003b001aa 0xce3f81f003e003ff

def z1095 : W := mkw 0x00377e0003d6a800 0xffbffe78fffffe3f

def z1096 : W := mkw 0x003bfff6a8200088 0x7f7ffffffce0000c

def z1097 : W := mkw 0x4863d4b220f2208a 0x1103c03000f0000f

def z1098 : W := mkw 0x284194ab206b22c8 0x24c3b18f02ef01c0

def z1099 : W := mkw 0x003bfff6a8000000 0x7f7ffffffc103c00

def z1100 : W := mkw 0x0019bdf6a8000000 0x7e7fbdfffc000000

def z1101 : W := mkw 0x0033fea6a8000000 0x7e7fffaffc000000

def z1102 : W := mkw 0x00377e0003d6a800 0xffbffe7003fffc00

def z1103 : W := mkw 0x00377e0003d6a800 0xbfbffe08fffffc00

def z1104 : W := mkw 0x00337e06a8000000 0x287c7e0ffc000000

def z1105 : W := mkw 0xc03bfff6a8b001aa 0x7f7ffffffcf003ff

def z1106 : W := mkw 0xb09c294dc30dc370 0xeefc3fcfff0fc3f0

def z1107 : W := mkw 0x2c4194ab746b76dd 0xf7c3f7bf3fffffff

def z1108 : W := mkw 0xb09c294583058160 0x2e7c3987020701c0

def z1109 : W := mkw 0xb09c294dc30dc370 0xeefc7bdfcf0fc3f0

def z1110 : W := mkw 0xb09c294583058160 0xc67c3187020703c0

def z1111 : W := mkw 0xb09c294dc30dc370 0x047c318fc20701c0

def z1112 : W := mkw 0x284194ab306b32cc 0xe6c3b58f32ef33c0

def z1113 : W := mkw 0x240080a9542956dd 0xffc3ffffffffffff

def z1114 : W := mkw 0x003bfff6a8000000 0x7e7ffffffd10cc00

def z1115 : W := mkw 0xb09c294dd30dd374 0xeffc39cfc30ff3fc

def z1116 : W := mkw 0x284194ab306b32cc 0x76c3b5af32ef31c0

def z1117 : W := mkw 0x284194a3206320c8 0xc643b18702e703c0

def z1118 : W := mkw 0x2c44000957fffedd 0x8180000003ffffff

def z1119 : W := mkw 0xb49c294dd70dd775 0xeefc39cfc30ffff0

def z1120 : W := mkw 0xb49c2945c705c571 0x0c7c7bd7cf17cdf3

def z1121 : W := mkw 0xb098294dc0094370 0xeefc39cfc20f03f0

def z1122 : W := mkw 0x200080a1002100c8 0xd743b1a702e703cc

def z1123 : W := mkw 0x284194ab306b32cc 0xffc3ffaf32ef33cc

def z1124 : W := mkw 0xb09c294d830d8360 0x447c318f020703c0

def z1125 : W := mkw 0x00377e0003d6a800 0x04bfb00002effc00

def z1126 : W := mkw 0x003bfff6a8422000 0xfffffffffffffc00

def z1127 : W := mkw 0x00377e0003d6a800 0xffbffe4003fffe30

def z1128 : W := mkw 0xa00c014903090360 0xe6fc318f020f03c0

def z1129 : W := mkw 0x200080a9002902c8 0xe6c3b18f02ef03c0

def z1130 : W := mkw 0xc03bfff6a82001aa 0x7e7ffffffc0001c0

def z1131 : W := mkw 0x003a6b56a8000000 0x087c4a5ffc000000

def z1132 : W := mkw 0x00377e022bd6a800 0xbfbffe003ffffc00

def z1133 : W := mkw 0x284194ab306b32cc 0xa5c3b58f32ef33cc

def z1134 : W := mkw 0x003aebf6a8000000 0x5e7fcbfffc000000

def z1135 : W := mkw 0xb09c294dc30dc370 0x8cfc39c7c30fc3f0

def z1136 : W := mkw 0x284194ab306b32cc 0x7643b5af32e703cc

def z1137 : W := mkw 0x2c4194ab346b36cd 0xffc3fffffeff3fcf

def z1138 : W := mkw 0x284194a3206320c8 0x2443b58f32e701c0

def z1139 : W := mkw 0x2c4194ab746b76dd 0x24c3bf8ffeeffdc0

def z1140 : W := mkw 0x003bfff6a8000000 0x687c7ffffc000000

def z1141 : W := mkw 0x00377e0223d6a800 0xbffffe0f33fffc00

def z1142 : W := mkw 0x90be6944c394c130 0x083c4840c110c030

def z1143 : W := mkw 0x003bfff6a8000000 0xff7ffffffc00020c

def z1144 : W := mkw 0xb09c294d830d8360 0xeefc398f030fc3c0

def z1145 : W := mkw 0x00377e0003d6a800 0x2cbffe0003fffc00

def z1146 : W := mkw 0x0027540003d6a800 0xbfbff40003fffc00

def z1147 : W := mkw 0x3094280dc30dc250 0xeefc398fc30fc3c0

def z1148 : W := mkw 0x003bfff6a8200088 0xff7ffffffff003ff

def z1149 : W := mkw 0x0863d6a23062308c 0x1103c62030e0300c

def z1150 : W := mkw 0x284194ab306b32cc 0xf7c3f7af32ff3fcc

def z1151 : W := mkw 0xc026c0b003b001aa 0x9f3fc03003f003ff

def z1152 : W := mkw 0xb09c294dc30dc370 0xfffc79cfc31fc3f0

def z1153 : W := mkw 0xb49c294dd70dd775 0xeefc7fdfff1ffff3

def z1154 : W := mkw 0xa01c294d83090360 0xeefc39cfc30f03f0

def z1155 : W := mkw 0xc026400003b001aa 0xdf3fc07003f003ff

def z1156 : W := mkw 0xc02ec1f48bb001aa 0xdf3fc1f0cff003ff

def z1157 : W := mkw 0x284194ab706b72dc 0xf7c3b5eff2ef33fc

def z1158 : W := mkw 0x2c4194ab746b76dd 0xffc3f5ffffff33ff

def z1159 : W := mkw 0x00366a0003d6a800 0x9fbfca0003fffc00

def z1160 : W := mkw 0x0000000000000000 0xfb804e78fd18fe3f

def z1161 : W := mkw 0x0863d6a220f22888 0x0003800000e00000

def z1162 : W := mkw 0x200194ab202902c8 0xf7c3b5af32ef03cc

def z1163 : W := mkw 0x002bd5f220000000 0x7e7ffffffc000000

def z1164 : W := mkw 0x0863d6ba386a328c 0xfb83ce78fce8320c

def z1165 : W := mkw 0xb09c294dc30dc370 0x4c7c39cfc307c3f0

def z1166 : W := mkw 0xb09c294d830d8360 0x84fc3187020f03c0

def z1167 : W := mkw 0xb09c294dc30dc370 0xffffb9cfc3efc3f0

def z1168 : W := mkw 0x2c4194ab746b76dd 0xffc3ffafffffffcc

def z1169 : W := mkw 0xb49c294dc70dc771 0xfffc7bffcf1fcfff

def z1170 : W := mkw 0x284194ab206b22c8 0xf7c3b58f02ef33c0

def z1171 : W := mkw 0x0033feb6a8000000 0x3e7ffe3ffc000000

def z1172 : W := mkw 0xb09c294dc30dc370 0xeefc39ffc30fc3ff

def z1173 : W := mkw 0x2c4194ab746b76dd 0xffc3bdeff3ffffff

def z1174 : W := mkw 0x0863d6aa30fa3a8c 0xfb83ce2831f8fe0c

def z1175 : W := mkw 0x284194ab306b32cc 0xffc3bdaf33eff3cc

def z1176 : W := mkw 0xb09c294dc30dc370 0xce7c31cfc30703f0

def z1177 : W := mkw 0x284194ab306b32cc 0xd7c3b1a702ef33cc

def z1178 : W := mkw 0x284194a3206320c8 0x85c3b18702ef31c0

def z1179 : W := mkw 0x284194ab306b32cc 0xf7c3b5fffeef33cc

def z1180 : W := mkw 0x0863d6b228622088 0x0003800000e00000

def z1181 : W := mkw 0x002bd5f6a8000000 0x7e7ff5fffc000000

def z1182 : W := mkw 0x0019bff6a8000000 0x6e7c3ffffc000000

def z1183 : W := mkw 0x284194a3206320c8 0x5643b1a702e701c0

def z1184 : W := mkw 0xc03bfff6a82001aa 0xff7ffffffd1003ff

def z1185 : W := mkw 0x0863d6b228622088 0x1003c6303ce00000

def z1186 : W := mkw 0xc03e6b548b948922 0x083c4a50cd10cc33

def z1187 : W := mkw 0x2400000954095655 0xfbc04ffffd18ffff

def z1188 : W := mkw 0xb09c294dc30dc370 0xcefc31c7030fc3f0

def z1189 : W := mkw 0xb09c2945c305c170 0x047c31870307c1f0

def z1190 : W := mkw 0x0863d6b238f2388c 0x1103c6303cf03c0c

def z1191 : W := mkw 0x4863d4b230f2308e 0x1103842030e0300c

def z1192 : W := mkw 0xb09c2b4dcb0dc370 0xeefc3bcfcf0fc3f0

def z1193 : W := mkw 0xb09c294dc30dc370 0x6e7c39cfc20703f0

def z1194 : W := mkw 0x00377e0003d6a800 0xb7bfb40003fffc00

def z1195 : W := mkw 0x2018294580010040 0x6e7c39cfc20701c0

def z1196 : W := mkw 0x2c4194ab746b76dd 0xf7c3b5af32ef33ff

def z1197 : W := mkw 0x200194a9006b22c8 0xf7c3b5af02ef33cc

def z1198 : W := mkw 0x0400000854085615 0x39804e78fd18fc3f

def z1199 : W := mkw 0x284194ab306b32cc 0xf7c3b5af33ffffcc

def z1200 : W := mkw 0x284194ab206b22c8 0xf6c3b5af32ef03c0

def z1201 : W := mkw 0x284194ab306b32cc 0x35c3b5af32ef31cc

def z1202 : W := mkw 0x00337e0000422000 0xbfbffe0003fffc00

def z1203 : W := mkw 0x0863d6a230f2388c 0x1103842030e0300c

def z1204 : W := mkw 0x284194a3206320c8 0x8543b18702e703cc

def z1205 : W := mkw 0x2018294d90091244 0xfffc7ffffe0f33cc

def z1206 : W := mkw 0x2014280103058040 0xaefc3987030fc1c0

def z1207 : W := mkw 0x00377e0003d6a800 0x3ebffe0002effc00

def z1208 : W := mkw 0x00377e0003d6a800 0xffbffe48c3fffc00

def z1209 : W := mkw 0x200194ab204b2240 0xf7c3b5af32ef33c0

def z1210 : W := mkw 0x90be6b4483948920 0x003c000000000000

def z1211 : W := mkw 0xc02ec1f003b001aa 0xff7ff1ff03f003ff

def z1212 : W := mkw 0x284194a3206320c8 0x1543b1a702e701cc

def z1213 : W := mkw 0xc02ec1f003b001aa 0x953fc1b003f003ff

def z1214 : W := mkw 0x2c4194ab346b36cd 0xf7c3b5bf3eef33cf

def z1215 : W := mkw 0x003bfff6a8422800 0x7e7ffffffc003c00

def z1216 : W := mkw 0x0026c0a003b00088 0xdf3fc1f003f003ff

def z1217 : W := mkw 0x4023d6b228f2288a 0x1103c6303cf03c0f

def z1218 : W := mkw 0x2018294580010040 0x047c3187020701c0

def z1219 : W := mkw 0x0400000054005415 0xbb804e70fd18fc3f

def z1220 : W := mkw 0xc03bfff6a82001aa 0xff7ffffffee003ff

def z1221 : W := mkw 0x284194a3306330cc 0xd743b5a732e733cc

def z1222 : W := mkw 0x003bfff6a8000000 0xfffffffffd18fe3f

def z1223 : W := mkw 0x2c4194ab746b76dd 0x85c3b18703ffffff

def z1224 : W := mkw 0x24011409544b7655 0xffc3ffffffffffff

def z1225 : W := mkw 0x4c63d4ba74fa769f 0xfb83ce78fdf8fe3f

def z1226 : W := mkw 0x003bfff6a8000000 0x7e7ffffffc00023f

def z1227 : W := mkw 0x2010280900090240 0xeefc398f020f03c0

def z1228 : W := mkw 0x003bfff6a8900800 0x7e7ffffffc100c00

def z1229 : W := mkw 0xc02ec1f003b001aa 0x553fc1f002f003ff

def z1230 : W := mkw 0xb49c294dc70dc771 0xfefc7fffff1fcff3

def z1231 : W := mkw 0xb09c294583058160 0x4e7c31c7020701c0

def z1232 : W := mkw 0x2c4194ab746b76dd 0xffc3fffffeefffcc

def z1233 : W := mkw 0x2c4194ab746b76dd 0xf7c3ffbffeffffcf

def z1234 : W := mkw 0x00377e0003d6a800 0xffbffe2003fffe0c

def z1235 : W := mkw 0xb49c294dd70dd775 0xfffc7fcfff1ffff0

def z1236 : W := mkw 0x003bfff6a8000000 0xff7ffffffd100000

def z1237 : W := mkw 0x684194bb306b32ce 0xf7c3b5bf32ef33cf

def z1238 : W := mkw 0xb09c294dd30dd374 0xeefc3dcff30ff3f0

def z1239 : W := mkw 0x284194ab306b32cc 0xc5c3b1af32ef33cc

def z1240 : W := mkw 0x00377e0003d6a800 0x9fbff00003fffc00

def z1241 : W := mkw 0xb09c294583058160 0x7e7c7ffffe0701c0

def z1242 : W := mkw 0x20011409404b6250 0xffc3ffcfc3fffff0

def z1243 : W := mkw 0xb09c294583058160 0x0c7c39c7c20701c0

def z1244 : W := mkw 0x2c4194a3346334cd 0x1543f7b73ef73dcf

def z1245 : W := mkw 0x20011409004b2240 0xe6c3b18f02ef03c0

def z1246 : W := mkw 0xc02ec1f003b001aa 0xffbfcff8fff8ffff

def z1247 : W := mkw 0xb49c294dd70dd775 0x447c31fffe0703ff

def z1248 : W := mkw 0x0400000854085615 0xffc07ffffd18fe3f

def z1249 : W := mkw 0x284194ab706b72dc 0xffc3fdfff3fff3ff

def z1250 : W := mkw 0x284194a3206320c8 0x4443b1af32e701c0

def z1251 : W := mkw 0x003bfff6a8200088 0x7e7ffffffc0003cc

def z1252 : W := mkw 0x2c4194ab746b76dd 0xffc3f5ff33ffffff

def z1253 : W := mkw 0x002bd7f6a8000000 0x5e7fc7fffc000000

def z1254 : W := mkw 0xb49c294dd70dd775 0xeefc3fffff0fffff

def z1255 : W := mkw 0xb09c294dc30dc370 0xfffc39efc30fc3fc

def z1256 : W := mkw 0xc02ec1f003b001aa 0xd73f81f002e003ff

def z1257 : W := mkw 0x00337e0000d6a800 0x3fbffe0000fffc00

def z1258 : W := mkw 0xb09c295dcb0dc370 0xeefc39dfcf0fc3f0

def z1259 : W := mkw 0x0400000854085615 0x59004e78fd10fe3f

def z1260 : W := mkw 0x0400000854085615 0xff83ce78fff8fe3f

def z1261 : W := mkw 0x284194ab306b32cc 0xb7c3b58f32ef31c0

def z1262 : W := mkw 0xc026400003b001aa 0x853f800003f003ff

def z1263 : W := mkw 0x200080a9402942d8 0xffc3f9ffc3ffc3ff

def z1264 : W := mkw 0xb09c294dc30dc370 0xe6fc318f030fc3f0

def z1265 : W := mkw 0x2c4194ab746b76dd 0x4443b1fffee703ff

def z1266 : W := mkw 0x003bfff6a8000000 0x047fb18ffc000000

def z1267 : W := mkw 0x00377e0003d6a800 0x95bff60003fffc00

def z1268 : W := mkw 0x0400000054005415 0xdb004e70fd10fe3f

def z1269 : W := mkw 0xc02ec1f003b001aa 0x9f3fc18003f003ff

def z1270 : W := mkw 0xb09c294dc30dc370 0x68fc39cfc10fc3f0

def z1271 : W := mkw 0x00377e0003d6a800 0xafbfb80003fffc00

def z1272 : W := mkw 0xb09c294dc30dc370 0x6efc39cfc20fc1c0

def z1273 : W := mkw 0x003bfff6a8000000 0xff7ffffffee00000

def z1274 : W := mkw 0xc02e414003b001aa 0xdf3fc1c003f003ff

def z1275 : W := mkw 0xb09c294dc30dc370 0xa4fc398fc30fc3f0

def z1276 : W := mkw 0x403bfff6a820008a 0x7e7ffffffc00000f

def z1277 : W := mkw 0x0027560003d6a800 0x9fbfc60003fffc00

def z1278 : W := mkw 0x0863d6b23862308c 0x1103842030e0300c

def z1279 : W := mkw 0xc02ec1f6abb001aa 0xff7fcffffff003ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z3,z8,z6]),(0,[z9,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z11,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z12,z13]),(0,[z7,z1,z2,z3,z14,z15,z6]),(0,[z7,z1,z2,z3,z16,z4,z6]),(0,[z7,z1,z2,z3,z4,z17,z6])],[(0,[z0,z7,z2,z3,z4,z6,z18]),(0,[z7,z1,z2,z3,z19,z4,z6]),(0,[z20,z7,z1,z2,z3,z4,z21]),(0,[z7,z1,z2,z3,z4,z21,z22]),(0,[z7,z1,z2,z3,z23,z4,z6]),(0,[z7,z1,z24,z25,z3,z4,z6])],[(0,[z26,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z27,z3,z14,z6]),(0,[z7,z1,z2,z28,z3,z4,z6]),(0,[z29,z7,z1,z2,z3,z14,z6]),(0,[z30,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z31,z4,z6]),(0,[z32,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z12,z22]),(0,[z7,z1,z2,z33,z4,z34,z6])],[(0,[z7,z1,z2,z10,z35,z4,z6]),(0,[z36,z7,z1,z2,z3,z4,z6]),(0,[z37,z7,z1,z2,z3,z4,z6])],[(0,[z38,z7,z1,z2,z3,z4,z6]),(0,[z39,z7,z40,z2,z3,z4,z6]),(0,[z39,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z41,z4,z34,z6])],[(0,[z42,z7,z1,z2,z3,z4,z6]),(1,[z43,z7,z2,z3,z4,z6])],[(0,[z7,z44,z2,z45,z3,z4,z6]),(0,[z7,z1,z2,z46,z3,z4,z6]),(1,[z7,z1,z2,z47,z3,z6]),(0,[z7,z1,z2,z33,z4,z6,z48]),(0,[z7,z1,z2,z49,z3,z4,z6]),(0,[z7,z1,z2,z3,z50,z4,z6]),(0,[z51,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z52,z4,z6]),(0,[z7,z1,z2,z3,z53,z4,z6]),(0,[z7,z1,z2,z3,z4,z54,z6]),(0,[z7,z1,z55,z56,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z57])]],
   [[(0,[z58,z7,z1,z2,z41,z4,z6]),(0,[z7,z1,z2,z59,z3,z4,z6]),(0,[z7,z1,z2,z3,z60,z61,z6]),(0,[z7,z1,z2,z3,z62,z14,z6]),(0,[z63,z7,z1,z2,z3,z4,z13]),(0,[z7,z1,z2,z64,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z65,z6]),(0,[z9,z7,z1,z45,z3,z4,z6]),(0,[z66,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z67,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z68])],[(0,[z7,z1,z2,z69,z3,z4,z6]),(0,[z7,z1,z2,z3,z70,z4,z6]),(0,[z7,z1,z71,z2,z3,z4,z6]),(0,[z7,z1,z2,z72,z3,z4,z6]),(0,[z7,z1,z2,z73,z3,z4,z6]),(0,[z7,z1,z2,z3,z74,z4,z6])],[(0,[z7,z1,z2,z3,z75,z4,z6]),(0,[z7,z76,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z33,z14,z6]),(0,[z77,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z4,z78,z6])],[(0,[z7,z1,z2,z3,z4,z6,z79]),(0,[z7,z1,z2,z3,z80,z4,z6]),(0,[z7,z81,z1,z2,z3,z4,z6]),(0,[z82,z7,z1,z2,z3,z4,z6])],[(0,[z83,z7,z1,z2,z23,z4,z6]),(0,[z7,z1,z2,z3,z84,z4,z6]),(1,[z85,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z86,z4,z6])],[(0,[z7,z1,z2,z87,z3,z4,z6]),(0,[z88,z7,z1,z2,z3,z4,z6]),(0,[z89,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z90]),(0,[z7,z1,z2,z3,z91,z14,z6]),(0,[z7,z1,z2,z4,z6,z92,z93])],[(0,[z94,z7,z1,z2,z3,z4,z6]),(0,[z95,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z96,z4,z6]),(0,[z7,z1,z2,z97,z3,z4,z6]),(0,[z77,z7,z1,z2,z33,z4,z6])]],
   [[(0,[z38,z7,z1,z2,z3,z70,z6]),(0,[z98,z7,z1,z2,z25,z3,z6]),(0,[z99,z7,z1,z2,z3,z4,z12]),(0,[z7,z1,z2,z3,z100,z61,z6]),(0,[z7,z1,z2,z3,z4,z61,z6])],[(0,[z7,z1,z2,z101,z3,z4,z6])],[(0,[z7,z1,z2,z3,z102,z4,z6]),(1,[z7,z103,z2,z3,z4,z6])],[(1,[z7,z1,z2,z104,z4,z6]),(0,[z7,z1,z2,z3,z105,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z106]),(0,[z7,z1,z2,z3,z14,z4,z6]),(0,[z107,z7,z1,z2,z3,z61,z6])],[(0,[z7,z44,z2,z3,z4,z12,z6]),(0,[z108,z7,z1,z2,z3,z4,z6]),(0,[z109,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z110,z3,z4,z6]),(0,[z111,z7,z1,z2,z10,z4,z6]),(1,[z112,z7,z2,z3,z4,z18]),(0,[z7,z1,z2,z3,z61,z113,z6]),(0,[z7,z1,z114,z2,z3,z4,z6])],[(0,[z115,z7,z116,z2,z3,z4,z6]),(0,[z7,z1,z2,z117,z3,z4,z6]),(0,[z7,z1,z118,z2,z3,z4,z6]),(0,[z112,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z119,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z120])],[(0,[z121,z7,z1,z2,z3,z4,z6]),(0,[z20,z7,z1,z2,z10,z4,z6]),(0,[z122,z7,z1,z2,z3,z4,z6]),(0,[z99,z7,z1,z2,z3,z4,z6]),(0,[z123,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z124,z2,z3,z4,z6]),(0,[z7,z1,z2,z125,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z126])],[(1,[z7,z1,z2,z3,z4,z6]),(0,[z7,z76,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z127,z6]),(0,[z98,z7,z1,z2,z128,z3,z6]),(0,[z7,z1,z2,z33,z129,z4,z6]),(0,[z7,z1,z2,z3,z41,z61,z6]),(0,[z7,z85,z1,z2,z3,z4,z6]),(0,[z63,z130,z1,z2,z3,z4,z6])]],
   [[(0,[z131,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z132,z6]),(0,[z7,z1,z2,z133,z4,z134,z6]),(0,[z7,z1,z2,z3,z135,z4,z6]),(0,[z7,z2,z3,z4,z136,z61,z6]),(0,[z7,z1,z137,z2,z3,z4,z6]),(0,[z7,z138,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z23,z61,z6]),(0,[z112,z7,z1,z2,z33,z4,z6]),(0,[z7,z139,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z4,z13,z6])],[(1,[z7,z1,z2,z3,z4,z140]),(1,[z111,z1,z2,z3,z134,z6]),(0,[z7,z1,z2,z3,z4,z141,z6])],[(0,[z7,z2,z3,z23,z4,z6,z18]),(0,[z7,z1,z2,z3,z4,z6,z142]),(0,[z7,z1,z2,z3,z143,z4,z6])],[(0,[z7,z1,z144,z2,z3,z4,z6]),(0,[z145,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z146,z3,z4,z6]),(0,[z147,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z148,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z149])],[(0,[z7,z1,z2,z150,z3,z4,z6])],[(0,[z7,z1,z2,z151,z3,z35,z6]),(0,[z7,z1,z2,z3,z4,z13,z21]),(1,[z7,z1,z2,z152,z4,z6]),(0,[z7,z1,z2,z10,z10,z4,z6]),(1,[z7,z1,z2,z153,z4,z6])]],
   [[(0,[z7,z1,z2,z3,z4,z154,z6]),(0,[z7,z1,z2,z3,z134,z61,z6]),(0,[z38,z7,z1,z2,z25,z3,z6]),(0,[z39,z7,z1,z2,z25,z3,z6])],[(0,[z7,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z155]),(0,[z58,z7,z156,z2,z3,z4,z6]),(0,[z7,z1,z157,z2,z3,z4,z6]),(0,[z7,z158,z1,z2,z3,z4,z6])],[(0,[z7,z1,z1,z2,z3,z4,z6]),(1,[z159,z44,z2,z3,z4,z6]),(0,[z160,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z70,z61,z6]),(0,[z7,z1,z40,z2,z3,z4,z6]),(0,[z161,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z162,z4,z6]),(0,[z7,z1,z2,z3,z163,z4,z6]),(0,[z7,z164,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z165,z4,z6])],[(0,[z7,z1,z2,z166,z3,z4,z6]),(0,[z7,z1,z167,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z168,z6]),(0,[z63,z7,z169,z2,z3,z4,z6])],[(0,[z7,z1,z2,z170,z3,z4,z6]),(0,[z0,z171,z1,z2,z3,z4,z6]),(0,[z58,z7,z172,z2,z3,z4,z6]),(0,[z173,z7,z1,z2,z3,z4,z6]),(0,[z98,z7,z1,z2,z3,z129,z6]),(1,[z7,z1,z2,z4,z6,z92])],[(0,[z7,z1,z174,z2,z3,z4,z6]),(1,[z38,z1,z2,z3,z70,z6]),(0,[z112,z7,z1,z2,z3,z14,z6]),(0,[z175,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z84,z61,z6]),(0,[z7,z1,z2,z3,z176,z4,z6]),(0,[z7,z103,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z177,z4,z6])],[(0,[z178,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z179,z3,z6]),(0,[z7,z1,z2,z180,z3,z4,z6]),(0,[z7,z1,z55,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z181,z4,z6])],[(0,[z7,z1,z2,z3,z182,z4,z6]),(0,[z39,z7,z2,z3,z4,z6,z18]),(1,[z7,z1,z2,z3,z183,z6])]],
   [[(0,[z7,z1,z2,z3,z184,z4,z6]),(0,[z7,z1,z2,z3,z185,z4,z6]),(0,[z7,z1,z2,z186,z3,z4,z6]),(0,[z7,z1,z2,z187,z3,z4,z6])],[(0,[z7,z44,z2,z3,z129,z4,z6]),(1,[z29,z1,z188,z3,z4,z6]),(0,[z7,z1,z189,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z190]),(1,[z7,z1,z2,z191,z4,z6]),(0,[z192,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z193,z3,z4,z6]),(0,[z7,z1,z2,z3,z194,z4,z6])],[(0,[z7,z1,z195,z2,z3,z4,z6]),(0,[z7,z1,z2,z196,z3,z4,z6]),(0,[z7,z1,z40,z2,z152,z4,z6]),(0,[z197,z7,z1,z2,z3,z4,z6]),(0,[z98,z7,z2,z3,z129,z4,z6]),(0,[z7,z1,z2,z198,z10,z4,z6]),(1,[z7,z1,z2,z3,z199,z6]),(0,[z7,z1,z2,z25,z3,z4,z6])],[(0,[z58,z7,z1,z2,z35,z4,z6]),(0,[z109,z7,z1,z2,z35,z4,z6]),(0,[z98,z7,z1,z2,z33,z4,z6]),(0,[z200,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z56,z10,z4,z6]),(0,[z7,z1,z2,z3,z14,z61,z6]),(0,[z7,z1,z2,z25,z4,z34,z6])],[(0,[z7,z1,z2,z201,z33,z4,z6]),(0,[z7,z1,z2,z33,z4,z6,z202]),(0,[z7,z1,z2,z3,z203,z4,z6])],[(0,[z7,z1,z2,z204,z3,z4,z6]),(0,[z58,z7,z1,z2,z205,z4,z6]),(0,[z109,z7,z1,z2,z205,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z206]),(0,[z7,z1,z2,z207,z33,z4,z6]),(0,[z7,z1,z2,z208,z33,z4,z6]),(0,[z7,z1,z2,z10,z4,z209,z6]),(1,[z63,z7,z1,z3,z4,z22]),(1,[z7,z1,z2,z210,z4,z6])],[(0,[z7,z1,z188,z2,z3,z4,z6]),(0,[z211,z7,z1,z2,z3,z4,z6]),(0,[z212,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z213,z2,z3,z4,z6]),(0,[z99,z7,z1,z2,z3,z61,z6])],[(0,[z7,z1,z2,z3,z214,z4,z6]),(0,[z7,z1,z2,z128,z10,z4,z6]),(1,[z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z61,z61,z6]),(0,[z7,z1,z2,z215,z3,z4,z6]),(0,[z216,z7,z1,z2,z3,z4,z6])]],
   [[(0,[z217,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z2,z33,z4,z6]),(0,[z63,z7,z218,z2,z3,z4,z6]),(0,[z7,z219,z1,z2,z3,z4,z6])],[(0,[z7,z1,z44,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z4,z220,z6]),(0,[z7,z1,z2,z45,z10,z4,z6]),(0,[z221,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z222])],[(0,[z7,z1,z55,z2,z3,z14,z6])],[(0,[z1,z2,z27,z3,z4,z6,z21]),(0,[z223,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z224,z6]),(0,[z7,z225,z1,z2,z3,z4,z6]),(0,[z226,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z227,z4,z6]),(0,[z7,z1,z2,z128,z25,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z228])],[(0,[z171,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z40,z2,z191,z4,z6]),(0,[z7,z2,z3,z129,z4,z6,z18]),(0,[z229,z7,z1,z2,z3,z14,z6]),(0,[z7,z230,z1,z2,z3,z4,z6]),(0,[z231,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z232])],[(0,[z7,z1,z44,z2,z33,z4,z6]),(0,[z233,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z27,z10,z4,z6]),(0,[z7,z1,z2,z45,z33,z4,z6]),(0,[z234,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z235,z14,z6]),(0,[z77,z7,z1,z2,z3,z4,z202])],[(0,[z7,z1,z25,z236,z3,z4,z6]),(0,[z7,z1,z2,z25,z3,z235,z6])],[(1,[z115,z1,z27,z3,z4,z6]),(0,[z30,z7,z1,z2,z3,z4,z18]),(0,[z7,z1,z2,z237,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z238]),(0,[z98,z7,z1,z2,z3,z14,z6]),(1,[z239,z7,z1,z3,z61,z6]),(0,[z7,z1,z2,z3,z240,z4,z6]),(0,[z241,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z242,z4,z6])]],
   [[(0,[z7,z1,z2,z3,z4,z113,z6]),(0,[z239,z7,z1,z3,z4,z61,z6]),(0,[z7,z1,z2,z243,z3,z4,z6])],[(0,[z0,z1,z2,z27,z3,z4,z6]),(0,[z29,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z27,z33,z4,z6]),(0,[z1,z2,z205,z3,z35,z4,z6]),(0,[z7,z1,z2,z207,z3,z14,z6]),(0,[z39,z98,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z129,z4,z6]),(0,[z7,z1,z244,z2,z10,z4,z6])],[(0,[z7,z1,z2,z3,z4,z245,z6]),(0,[z7,z1,z2,z246,z3,z4,z6]),(0,[z7,z1,z40,z2,z3,z61,z6]),(0,[z77,z7,z1,z2,z4,z6,z202])],[(0,[z247,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z248,z4,z6]),(0,[z7,z1,z55,z2,z49,z4,z6]),(0,[z249,z7,z1,z2,z3,z4,z6])],[(0,[z7,z250,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z2,z3,z14,z6]),(0,[z7,z1,z2,z25,z3,z91,z6])],[(0,[z251,z7,z1,z2,z3,z4,z6]),(0,[z252,z7,z1,z2,z3,z4,z6]),(0,[z253,z7,z1,z2,z3,z4,z6]),(1,[z7,z225,z2,z207,z4,z6]),(0,[z254,z7,z1,z2,z3,z255,z6]),(0,[z7,z1,z244,z2,z33,z4,z6])],[(0,[z159,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z256,z4,z6]),(0,[z115,z1,z2,z27,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z168,z6]),(0,[z7,z1,z2,z257,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z258])],[(0,[z259,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z260,z2,z3,z4,z6]),(0,[z63,z7,z1,z2,z257,z4,z6]),(0,[z7,z1,z244,z2,z3,z4,z22]),(0,[z261,z7,z1,z2,z3,z4,z6]),(0,[z262,z7,z1,z2,z3,z4,z6])]],
   [[(0,[z115,z29,z1,z2,z3,z4,z6]),(0,[z263,z7,z1,z2,z3,z4,z6]),(0,[z264,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z265,z3,z4,z6]),(0,[z7,z1,z2,z266,z10,z4,z6]),(0,[z7,z1,z2,z267,z10,z4,z6])],[(0,[z7,z1,z44,z2,z3,z14,z6]),(0,[z30,z7,z1,z2,z3,z4,z5]),(0,[z7,z40,z2,z45,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z268]),(0,[z7,z1,z2,z3,z14,z269,z6])],[(0,[z7,z1,z2,z3,z4,z6,z270]),(0,[z29,z7,z1,z27,z3,z4,z6]),(1,[z9,z7,z45,z3,z4,z6]),(0,[z7,z1,z2,z25,z3,z61,z6])],[(0,[z7,z1,z2,z3,z271,z4,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z272,z7,z1,z2,z3,z4,z6]),(0,[z273,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z274,z10,z4,z6]),(1,[z7,z1,z2,z3,z275,z6])],[(0,[z7,z1,z2,z267,z33,z4,z6]),(0,[z63,z7,z1,z2,z3,z276,z6])],[(0,[z0,z171,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z151,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z18]),(0,[z7,z1,z56,z3,z4,z61,z6]),(0,[z7,z1,z2,z10,z4,z277,z6]),(0,[z7,z1,z2,z128,z3,z91,z6])],[(0,[z278,z7,z1,z2,z3,z4,z6]),(0,[z29,z1,z188,z2,z3,z4,z6]),(0,[z7,z1,z188,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z4,z6,z279])],[(0,[z58,z7,z1,z2,z10,z4,z6]),(0,[z109,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z280,z4,z6]),(0,[z9,z7,z1,z2,z3,z4,z6]),(0,[z63,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z215,z3,z61,z6]),(0,[z281,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z128,z3,z34,z6])]],
   [[(0,[z7,z1,z282,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z283,z4,z6])],[(1,[z7,z116,z2,z3,z4,z6]),(0,[z284,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z33,z4,z61,z6]),(0,[z7,z1,z244,z2,z3,z14,z6])],[(0,[z7,z76,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z285,z10,z4,z6]),(0,[z7,z1,z24,z2,z3,z4,z6])],[(0,[z58,z7,z1,z2,z33,z4,z6]),(0,[z109,z7,z1,z2,z33,z4,z6]),(0,[z286,z7,z1,z2,z3,z4,z6]),(0,[z7,z225,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z4,z18,z22]),(0,[z63,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z4,z183,z6])],[(0,[z7,z1,z2,z3,z4,z287,z6]),(1,[z7,z1,z2,z3,z4,z288]),(0,[z171,z7,z1,z2,z3,z61,z6]),(0,[z115,z7,z1,z2,z3,z289,z6]),(0,[z7,z1,z2,z3,z290,z4,z6]),(0,[z7,z1,z2,z33,z105,z4,z6]),(0,[z7,z1,z2,z291,z3,z4,z6]),(0,[z7,z1,z55,z3,z14,z4,z6])],[(0,[z292,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z293,z6]),(0,[z7,z1,z2,z3,z61,z6,z21]),(0,[z7,z1,z2,z10,z235,z4,z6]),(0,[z63,z7,z1,z2,z3,z4,z22]),(0,[z77,z7,z103,z2,z3,z4,z6])],[(0,[z294,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z295,z6]),(0,[z7,z1,z2,z3,z296,z61,z6]),(0,[z7,z1,z2,z10,z4,z6,z202]),(0,[z7,z297,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z267,z4,z209,z6])],[(0,[z7,z1,z2,z3,z298,z4,z6]),(0,[z7,z1,z2,z299,z3,z4,z6])]],
   [[(0,[z7,z1,z2,z3,z4,z300,z6]),(0,[z7,z1,z2,z3,z4,z6,z301]),(0,[z7,z1,z2,z267,z3,z14,z6])],[(0,[z29,z7,z1,z2,z3,z61,z6]),(0,[z302,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z303,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z304]),(0,[z7,z1,z56,z2,z3,z305,z6]),(0,[z7,z1,z2,z3,z306,z6,z202]),(0,[z307,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z62,z91,z6])],[(0,[z109,z1,z2,z205,z3,z4,z6]),(0,[z38,z7,z1,z2,z3,z134,z6]),(0,[z7,z1,z2,z10,z4,z296,z6]),(0,[z7,z1,z2,z308,z3,z4,z6]),(0,[z77,z7,z1,z2,z25,z4,z6]),(0,[z77,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z6,z309]),(0,[z7,z76,z1,z45,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z310,z6]),(0,[z7,z1,z2,z274,z3,z14,z6]),(0,[z7,z1,z2,z3,z275,z6,z202])],[(1,[z311,z1,z2,z3,z4,z6]),(0,[z239,z7,z1,z2,z10,z4,z6]),(0,[z7,z2,z3,z235,z312,z4,z6])],[(0,[z115,z7,z1,z188,z3,z4,z6]),(0,[z7,z1,z2,z313,z3,z4,z6]),(1,[z39,z7,z2,z3,z296,z6]),(0,[z7,z1,z2,z3,z314,z4,z6]),(1,[z7,z2,z3,z4,z136,z6]),(0,[z7,z1,z2,z3,z315,z4,z6]),(0,[z7,z1,z2,z316,z3,z4,z6])],[(0,[z159,z7,z1,z2,z3,z61,z6]),(0,[z171,z7,z2,z3,z23,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z317]),(0,[z7,z1,z2,z3,z318,z4,z6]),(0,[z7,z1,z319,z2,z3,z4,z6]),(0,[z320,z7,z1,z2,z3,z4,z6]),(0,[z7,z225,z2,z3,z4,z6,z18]),(1,[z7,z1,z2,z10,z14,z6]),(0,[z77,z7,z1,z2,z267,z4,z6])],[(0,[z58,z7,z1,z2,z3,z14,z6]),(0,[z20,z7,z1,z2,z3,z4,z12]),(0,[z7,z1,z2,z3,z4,z6,z321]),(0,[z7,z1,z2,z3,z322,z4,z6]),(0,[z7,z1,z2,z3,z61,z6,z93]),(0,[z63,z7,z1,z2,z3,z14,z6])]],
   [[(0,[z323,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z324,z4,z6]),(0,[z7,z1,z2,z3,z325,z4,z6]),(0,[z239,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z56,z10,z3,z4,z6]),(0,[z326,z7,z1,z2,z3,z4,z6])],[],[(0,[z39,z7,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z327,z6]),(0,[z7,z328,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z33,z14,z6]),(0,[z7,z1,z2,z3,z4,z329,z6]),(0,[z7,z1,z55,z2,z330,z4,z6]),(0,[z7,z1,z2,z331,z3,z4,z6]),(0,[z332,z7,z1,z2,z3,z4,z6])],[(0,[z333,z7,z1,z2,z3,z4,z6]),(0,[z111,z7,z1,z2,z3,z4,z6]),(0,[z99,z7,z225,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z334,z4,z6]),(0,[z9,z7,z1,z40,z3,z4,z6]),(0,[z83,z7,z225,z2,z3,z4,z6]),(0,[z112,z7,z1,z2,z3,z4,z6]),(0,[z335,z7,z1,z2,z3,z4,z6])],[(0,[z30,z1,z2,z27,z3,z4,z6]),(0,[z111,z38,z1,z2,z3,z4,z6]),(0,[z20,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z336,z6]),(0,[z7,z1,z2,z3,z91,z61,z6]),(1,[z130,z1,z2,z3,z4,z6])],[(0,[z337,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z5,z6]),(0,[z7,z311,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z338,z6]),(0,[z9,z7,z1,z2,z3,z290,z6])],[(0,[z7,z1,z2,z3,z8,z4,z6]),(0,[z339,z7,z1,z2,z3,z4,z6]),(0,[z30,z29,z1,z2,z3,z4,z6]),(0,[z9,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z340,z3,z4,z6])]],
   [[(0,[z7,z1,z2,z3,z4,z341,z6]),(0,[z1,z44,z2,z27,z3,z4,z6]),(0,[z342,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z6,z18]),(0,[z7,z1,z2,z3,z4,z136,z6]),(0,[z7,z1,z3,z4,z13,z6,z22])],[(0,[z159,z7,z2,z3,z4,z6,z18]),(0,[z7,z1,z2,z3,z4,z289,z6]),(1,[z343,z7,z2,z3,z4,z6]),(0,[z7,z1,z56,z2,z10,z4,z6])],[(0,[z344,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z345]),(0,[z7,z1,z346,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z61,z5,z6]),(0,[z347,z7,z1,z2,z3,z4,z6])],[(0,[z348,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z349,z3,z35,z6]),(0,[z30,z7,z1,z2,z3,z4,z21])],[(0,[z7,z1,z2,z3,z4,z350,z6]),(0,[z7,z1,z2,z3,z129,z14,z6]),(0,[z7,z1,z2,z3,z61,z6,z18]),(0,[z351,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z67,z4,z6]),(0,[z239,z7,z1,z2,z3,z14,z6]),(0,[z130,z7,z1,z2,z3,z4,z6]),(0,[z63,z7,z1,z3,z4,z6,z22]),(0,[z7,z1,z2,z3,z4,z6,z352]),(0,[z353,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z35,z4,z6]),(1,[z109,z1,z2,z205,z4,z6]),(0,[z99,z354,z1,z2,z3,z4,z6]),(0,[z7,z1,z56,z2,z33,z4,z6]),(0,[z7,z1,z55,z2,z10,z4,z6])],[(0,[z7,z1,z2,z3,z4,z355,z6]),(0,[z356,z7,z1,z2,z3,z4,z6]),(1,[z354,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z3,z4,z6]),(0,[z7,z1,z2,z3,z357,z4,z6])],[(1,[z7,z156,z2,z3,z4,z6]),(0,[z111,z7,z1,z2,z3,z70,z6]),(0,[z7,z1,z2,z3,z4,z255,z6]),(0,[z7,z1,z2,z10,z4,z34,z6])]],
   [[(0,[z7,z1,z358,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z359,z4,z6]),(0,[z360,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z361,z4,z6]),(0,[z7,z362,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z363,z10,z4,z6]),(0,[z7,z1,z2,z3,z61,z6,z22]),(0,[z7,z1,z2,z236,z3,z4,z6]),(0,[z7,z1,z2,z210,z4,z6,z93]),(0,[z7,z1,z2,z3,z364,z4,z6])],[(0,[z115,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z365,z6]),(0,[z366,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z367,z3,z4,z6]),(1,[z7,z169,z2,z3,z4,z6])],[(0,[z7,z1,z368,z2,z3,z4,z6]),(1,[z7,z172,z2,z3,z4,z6]),(0,[z38,z7,z1,z2,z128,z3,z6]),(0,[z20,z1,z2,z3,z4,z6,z21]),(0,[z9,z7,z1,z2,z3,z338,z6]),(0,[z7,z369,z1,z2,z3,z4,z6]),(0,[z39,z7,z1,z2,z128,z3,z6]),(0,[z98,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z370]),(0,[z77,z7,z1,z2,z3,z61,z6])],[],[(0,[z99,z7,z2,z45,z3,z4,z6]),(0,[z7,z225,z1,z2,z23,z4,z6]),(0,[z7,z1,z2,z207,z10,z4,z6]),(0,[z7,z1,z2,z3,z4,z371,z6]),(0,[z254,z7,z1,z56,z3,z4,z6]),(0,[z175,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z372,z4,z6]),(0,[z7,z1,z2,z267,z3,z4,z209])],[(0,[z7,z1,z373,z2,z3,z4,z6]),(0,[z98,z7,z1,z2,z3,z296,z6]),(1,[z374,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z375,z3,z4,z6]),(0,[z7,z1,z376,z2,z3,z4,z6])],[(0,[z7,z1,z377,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z378,z4,z6]),(0,[z7,z1,z2,z3,z379,z14,z6])],[(0,[z7,z2,z3,z4,z5,z6,z380]),(0,[z7,z1,z2,z3,z4,z6,z381]),(0,[z7,z1,z2,z2,z10,z4,z6])]],
   [[(0,[z382,z7,z1,z2,z3,z4,z6]),(0,[z383,z7,z1,z2,z3,z4,z6]),(0,[z7,z354,z1,z2,z3,z4,z6]),(0,[z7,z1,z3,z33,z4,z61,z6]),(0,[z7,z1,z2,z3,z276,z4,z6]),(0,[z7,z1,z2,z3,z384,z4,z6])],[(0,[z7,z1,z2,z3,z4,z6,z21]),(1,[z7,z1,z2,z3,z290,z6]),(0,[z7,z1,z56,z2,z3,z14,z6]),(0,[z7,z1,z2,z198,z3,z4,z6])],[(0,[z7,z1,z2,z3,z385,z4,z6]),(0,[z7,z1,z2,z3,z386,z4,z6]),(0,[z7,z1,z2,z3,z4,z387,z6]),(0,[z7,z1,z2,z3,z4,z388,z6])],[(0,[z389,z7,z1,z2,z3,z4,z6]),(0,[z111,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z390,z4,z6]),(0,[z7,z1,z2,z3,z391,z4,z6])],[(0,[z7,z1,z2,z3,z4,z6,z392]),(0,[z7,z1,z2,z393,z3,z4,z6]),(0,[z112,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z169,z2,z3,z4,z6])],[(0,[z7,z1,z172,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z394,z4,z6]),(0,[z7,z1,z2,z395,z3,z4,z6]),(0,[z20,z7,z1,z2,z3,z61,z6]),(0,[z396,z7,z1,z2,z3,z4,z6])],[(1,[z7,z218,z2,z3,z4,z6]),(0,[z7,z1,z2,z128,z3,z4,z6])],[(0,[z0,z7,z44,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z21]),(0,[z7,z1,z2,z397,z3,z4,z6]),(0,[z39,z7,z1,z2,z3,z129,z6]),(0,[z7,z1,z398,z2,z3,z4,z6]),(1,[z254,z7,z1,z33,z4,z6]),(0,[z339,z7,z1,z2,z3,z61,z6]),(1,[z7,z1,z24,z3,z4,z6])]],
   [[(0,[z7,z1,z44,z2,z3,z4,z6]),(0,[z7,z1,z399,z2,z3,z4,z6]),(0,[z30,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z45,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z400]),(0,[z7,z1,z2,z3,z401,z4,z6])],[(1,[z58,z1,z2,z35,z4,z6])],[(0,[z171,z7,z1,z2,z3,z4,z140]),(0,[z38,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z4,z5,z13]),(0,[z402,z7,z1,z2,z3,z4,z6]),(0,[z39,z7,z1,z2,z10,z4,z6]),(0,[z99,z7,z2,z3,z4,z12,z6])],[(0,[z7,z1,z2,z403,z3,z4,z6]),(0,[z404,z7,z1,z2,z3,z4,z6]),(0,[z254,z7,z1,z2,z3,z162,z6]),(0,[z7,z1,z55,z3,z33,z4,z6]),(0,[z7,z1,z2,z33,z41,z4,z6]),(0,[z7,z1,z2,z3,z4,z13,z6]),(0,[z7,z1,z2,z3,z4,z6,z93]),(1,[z7,z1,z2,z3,z62,z235])],[(0,[z7,z1,z2,z27,z3,z4,z6]),(0,[z7,z156,z1,z2,z3,z4,z6]),(0,[z30,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z33,z4,z5,z6]),(0,[z7,z1,z2,z405,z3,z4,z6]),(0,[z406,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z6,z407]),(0,[z7,z1,z2,z3,z35,z61,z6]),(1,[z7,z1,z2,z3,z338,z6]),(0,[z7,z1,z2,z408,z3,z4,z6])],[(0,[z0,z29,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z409,z4,z6]),(0,[z38,z7,z1,z2,z33,z4,z6]),(0,[z39,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z33,z4,z6,z18]),(0,[z7,z1,z2,z10,z3,z61,z6])],[(0,[z7,z1,z2,z3,z410,z4,z6]),(0,[z411,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z412,z2,z3,z4,z6]),(0,[z112,z7,z2,z3,z4,z6,z18]),(0,[z7,z1,z244,z2,z413,z4,z6])]],
   [[(0,[z414,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z3,z289,z6]),(0,[z58,z109,z1,z2,z3,z4,z6]),(0,[z30,z7,z415,z2,z3,z4,z6]),(0,[z416,z7,z1,z2,z3,z4,z6])],[(0,[z417,z7,z1,z2,z3,z4,z6]),(0,[z418,z7,z1,z2,z3,z4,z6])],[(0,[z99,z7,z76,z2,z3,z4,z6]),(0,[z7,z1,z419,z2,z3,z4,z6]),(0,[z7,z1,z2,z128,z3,z235,z6]),(0,[z7,z1,z2,z3,z62,z4,z6])],[(0,[z420,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z421,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z422,z6]),(0,[z7,z1,z2,z3,z4,z6,z423])],[(0,[z9,z311,z1,z2,z3,z4,z6]),(1,[z7,z1,z10,z33,z4,z6])],[(0,[z7,z1,z2,z3,z4,z424,z6]),(0,[z7,z1,z2,z3,z425,z4,z6]),(0,[z426,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z33,z4,z6]),(1,[z374,z7,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z61,z355,z6]),(1,[z7,z1,z2,z257,z4,z6])],[(0,[z7,z1,z2,z33,z70,z4,z6]),(1,[z7,z1,z2,z3,z31,z6]),(0,[z7,z1,z2,z3,z4,z12,z6]),(1,[z7,z1,z2,z3,z255,z6]),(0,[z7,z1,z2,z3,z16,z14,z6]),(0,[z7,z1,z2,z3,z427,z4,z6])],[(0,[z7,z1,z2,z266,z3,z4,z6]),(0,[z7,z1,z2,z3,z23,z14,z6]),(0,[z7,z1,z2,z3,z4,z6,z428]),(0,[z254,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z19,z14,z6]),(0,[z7,z1,z2,z267,z3,z4,z6])]],
   [[(0,[z30,z7,z1,z2,z3,z14,z6]),(0,[z429,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z430,z4,z6]),(0,[z431,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z244,z3,z4,z13,z6]),(0,[z7,z1,z2,z3,z4,z6,z432]),(0,[z433,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z91,z4,z6])],[(0,[z7,z225,z44,z2,z3,z4,z6]),(0,[z1,z188,z2,z27,z3,z4,z6]),(0,[z29,z1,z2,z3,z4,z6,z21]),(0,[z434,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z349,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z134,z6]),(0,[z435,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z198,z3,z61,z6]),(0,[z77,z7,z1,z2,z41,z4,z6])],[(0,[z38,z7,z1,z2,z3,z14,z6]),(1,[z7,z1,z2,z3,z4,z350]),(0,[z7,z1,z2,z3,z436,z4,z6]),(0,[z437,z7,z1,z2,z3,z4,z6]),(0,[z39,z7,z1,z2,z3,z14,z6]),(1,[z7,z1,z56,z3,z61,z6]),(0,[z7,z1,z2,z274,z3,z4,z6])],[(0,[z7,z1,z2,z438,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z439,z6]),(0,[z7,z1,z2,z440,z3,z4,z6]),(0,[z254,z7,z1,z2,z33,z4,z6])],[(0,[z441,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z6,z21]),(0,[z442,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z22]),(0,[z7,z1,z2,z3,z4,z6,z443])],[(0,[z7,z1,z2,z3,z4,z444,z6]),(0,[z445,z7,z1,z2,z3,z4,z6]),(1,[z20,z1,z2,z3,z4,z21]),(0,[z83,z7,z1,z2,z10,z4,z6]),(0,[z446,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z6,z447])],[(0,[z7,z1,z2,z3,z448,z4,z6]),(0,[z58,z7,z1,z2,z3,z4,z6]),(0,[z109,z7,z1,z2,z3,z4,z6]),(0,[z58,z7,z1,z2,z25,z4,z6]),(0,[z109,z7,z1,z2,z25,z4,z6]),(0,[z7,z1,z2,z3,z449,z4,z6]),(0,[z7,z1,z2,z47,z3,z4,z6]),(0,[z99,z7,z1,z2,z3,z4,z18]),(0,[z7,z1,z2,z128,z3,z61,z6]),(0,[z63,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z450]),(0,[z7,z1,z2,z3,z62,z235,z6])],[(0,[z7,z44,z2,z3,z23,z4,z6]),(0,[z7,z1,z2,z3,z451,z4,z6]),(0,[z7,z1,z2,z33,z14,z4,z6]),(0,[z66,z7,z1,z2,z3,z4,z6]),(0,[z63,z7,z1,z2,z427,z4,z6]),(0,[z7,z1,z2,z3,z4,z209,z6])]],
   [[(0,[z7,z1,z44,z2,z3,z61,z6]),(0,[z7,z1,z2,z45,z3,z61,z6]),(0,[z99,z7,z1,z2,z33,z4,z6]),(0,[z452,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z285,z3,z4,z6]),(0,[z7,z76,z1,z2,z3,z4,z6]),(0,[z7,z76,z40,z2,z3,z4,z6]),(0,[z7,z1,z40,z2,z3,z31,z6]),(0,[z83,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z4,z453,z6]),(0,[z454,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z61,z388,z6])],[(0,[z7,z1,z2,z455,z3,z4,z6]),(0,[z7,z1,z2,z3,z456,z4,z6])],[(0,[z0,z159,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z288,z6]),(0,[z30,z42,z7,z2,z3,z4,z6]),(0,[z457,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z244,z2,z3,z199,z6]),(0,[z7,z1,z2,z3,z458,z4,z6])],[(0,[z159,z7,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z27,z3,z61,z6]),(1,[z7,z1,z2,z349,z3,z6]),(0,[z459,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z460,z4,z6]),(1,[z7,z1,z2,z3,z91,z93])],[(0,[z159,z1,z44,z2,z3,z4,z6]),(1,[z7,z415,z2,z3,z4,z6]),(0,[z7,z1,z2,z461,z3,z4,z6]),(0,[z7,z1,z2,z3,z462,z4,z6]),(0,[z7,z1,z2,z33,z334,z4,z6]),(0,[z7,z1,z2,z3,z463,z4,z6]),(0,[z7,z1,z464,z2,z3,z4,z6])],[(0,[z0,z99,z7,z2,z3,z4,z6]),(0,[z465,z7,z1,z2,z3,z4,z6]),(0,[z39,z7,z2,z3,z4,z296,z6]),(0,[z7,z1,z2,z3,z14,z13,z6]),(0,[z7,z1,z2,z3,z14,z6,z93]),(0,[z63,z7,z1,z2,z3,z17,z6])],[(0,[z466,z7,z1,z2,z3,z4,z6]),(0,[z0,z7,z1,z2,z10,z4,z6]),(0,[z467,z7,z1,z2,z3,z4,z6]),(0,[z254,z7,z1,z2,z3,z14,z6])]],
   [[(0,[z468,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z469,z4,z6]),(0,[z171,z7,z2,z3,z4,z12,z6]),(0,[z99,z39,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z470,z6])],[(0,[z7,z1,z2,z3,z4,z6,z471]),(0,[z7,z1,z2,z472,z3,z4,z6]),(0,[z112,z7,z1,z2,z3,z4,z12]),(0,[z473,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z474,z4,z6]),(0,[z7,z1,z2,z3,z306,z4,z6]),(0,[z43,z7,z2,z3,z235,z4,z6])],[(0,[z7,z1,z2,z3,z4,z475,z6]),(0,[z7,z1,z2,z133,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z476,z6]),(0,[z7,z477,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z61,z13,z6]),(0,[z7,z1,z2,z3,z62,z61,z6]),(0,[z7,z1,z478,z2,z3,z4,z6])],[(0,[z0,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z479,z3,z4,z6]),(0,[z99,z112,z7,z2,z3,z4,z6]),(0,[z239,z7,z1,z2,z3,z4,z6]),(0,[z480,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z199,z4,z6]),(0,[z7,z1,z2,z3,z275,z4,z6]),(0,[z7,z1,z2,z3,z481,z4,z6])],[(0,[z482,z7,z1,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z10,z4,z6]),(0,[z20,z7,z1,z2,z3,z4,z5]),(0,[z7,z1,z2,z152,z3,z4,z6]),(0,[z7,z1,z40,z2,z33,z4,z6]),(0,[z99,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z125,z3,z14,z6])],[(0,[z483,z7,z1,z2,z3,z4,z6]),(0,[z115,z7,z484,z2,z3,z4,z6]),(0,[z9,z7,z2,z45,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z485,z6]),(0,[z83,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z486,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z33,z61,z6]),(0,[z7,z1,z2,z10,z41,z4,z6]),(1,[z7,z1,z2,z3,z14,z6])],[(0,[z7,z1,z2,z205,z10,z4,z6]),(0,[z7,z1,z2,z3,z487,z4,z6]),(0,[z7,z1,z2,z10,z4,z5,z6]),(0,[z7,z1,z2,z143,z33,z4,z6]),(0,[z7,z1,z10,z3,z33,z4,z6]),(0,[z131,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z488,z4,z6])],[(0,[z7,z1,z2,z3,z489,z4,z6]),(0,[z7,z1,z2,z10,z23,z4,z6]),(0,[z7,z1,z2,z267,z3,z61,z6])]],
   [[(0,[z490,z7,z1,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z33,z4,z6]),(0,[z491,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z415,z2,z3,z4,z6]),(0,[z7,z1,z492,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z4,z6,z18])],[(0,[z493,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z3,z4,z321]),(0,[z7,z1,z2,z3,z14,z12,z6]),(0,[z7,z1,z2,z3,z4,z305,z6]),(0,[z494,z7,z1,z2,z3,z4,z6])],[(0,[z495,z7,z1,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z3,z4,z220]),(0,[z7,z1,z2,z205,z33,z4,z6]),(0,[z7,z1,z496,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z61,z6,z423]),(0,[z7,z1,z2,z3,z497,z4,z6]),(0,[z7,z1,z2,z3,z4,z498,z6]),(0,[z7,z1,z2,z3,z499,z4,z6])],[],[(0,[z500,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z134,z6]),(0,[z501,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z502,z4,z6])],[(0,[z7,z1,z2,z3,z379,z4,z6]),(0,[z7,z1,z2,z3,z61,z12,z6])],[(0,[z58,z7,z1,z2,z3,z61,z6]),(0,[z109,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z4,z503,z6]),(0,[z7,z76,z1,z40,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z504]),(0,[z7,z505,z1,z2,z3,z4,z6]),(0,[z63,z7,z1,z2,z3,z61,z6]),(1,[z7,z1,z2,z49,z4,z6])],[(0,[z0,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z506,z6]),(0,[z7,z1,z2,z507,z3,z4,z6]),(0,[z7,z1,z2,z3,z508,z4,z6]),(0,[z7,z40,z2,z3,z129,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z509]),(0,[z7,z1,z2,z3,z4,z277,z6]),(0,[z7,z1,z510,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z6,z22]),(0,[z7,z1,z2,z3,z62,z235,z4])]],
   [[(0,[z7,z1,z2,z511,z3,z4,z6]),(0,[z7,z1,z188,z2,z33,z4,z6]),(0,[z7,z1,z512,z2,z3,z4,z6]),(1,[z7,z1,z2,z133,z4,z6]),(0,[z7,z1,z2,z10,z70,z4,z6]),(0,[z7,z1,z40,z2,z3,z14,z6]),(0,[z7,z1,z56,z2,z3,z4,z6]),(0,[z513,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z514,z3,z4,z6])],[(0,[z99,z159,z7,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z448,z4,z6]),(0,[z115,z7,z1,z27,z3,z4,z6]),(0,[z7,z1,z515,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z516,z6]),(0,[z111,z7,z1,z2,z3,z134,z6]),(0,[z7,z76,z1,z2,z3,z61,z6]),(0,[z517,z7,z1,z2,z3,z4,z6]),(0,[z518,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z33,z61,z6]),(0,[z519,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z520,z4,z6]),(0,[z7,z1,z2,z33,z4,z6,z21]),(0,[z7,z1,z2,z3,z4,z521,z6]),(0,[z7,z1,z2,z179,z3,z4,z6]),(0,[z239,z7,z1,z2,z460,z4,z6]),(0,[z7,z1,z2,z3,z14,z209,z6])],[(0,[z7,z1,z2,z3,z4,z522,z6]),(0,[z7,z362,z1,z2,z3,z4,z6]),(0,[z523,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z524,z4,z6]),(0,[z525,z7,z1,z2,z33,z4,z6]),(1,[z7,z1,z55,z33,z4,z6]),(0,[z7,z1,z2,z33,z4,z388,z6]),(0,[z7,z1,z2,z3,z176,z14,z6]),(0,[z7,z1,z2,z3,z4,z6,z526])],[(0,[z171,z7,z1,z2,z3,z4,z288]),(0,[z7,z1,z2,z3,z527,z4,z6]),(0,[z7,z1,z2,z10,z4,z6,z90]),(0,[z7,z1,z55,z2,z3,z4,z6]),(0,[z7,z1,z2,z528,z3,z4,z6])],[(0,[z7,z1,z2,z529,z3,z4,z6]),(0,[z7,z1,z2,z128,z41,z4,z6]),(0,[z7,z1,z2,z267,z3,z4,z202])],[(0,[z7,z1,z2,z205,z3,z14,z6]),(0,[z229,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z4,z61,z6]),(0,[z7,z1,z2,z3,z61,z209,z6]),(1,[z7,z530,z2,z3,z4,z6])],[(0,[z115,z7,z1,z2,z3,z4,z471]),(0,[z531,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z33,z227,z4,z6]),(0,[z7,z1,z2,z363,z3,z4,z6]),(0,[z7,z1,z2,z3,z235,z4,z6]),(0,[z7,z1,z2,z3,z312,z4,z6])]],
   [[(0,[z532,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z202])],[(0,[z7,z1,z2,z3,z4,z533,z6]),(0,[z534,z7,z1,z2,z3,z4,z6]),(0,[z98,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z14,z4,z6]),(0,[z7,z1,z2,z4,z209,z6,z202]),(0,[z7,z1,z535,z2,z3,z4,z6])],[(0,[z7,z1,z536,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z537,z6]),(0,[z9,z7,z76,z2,z3,z4,z6]),(0,[z7,z1,z2,z207,z3,z4,z6]),(0,[z7,z1,z2,z208,z3,z4,z6]),(0,[z239,z7,z1,z2,z3,z61,z6])],[(0,[z20,z1,z44,z2,z3,z4,z6]),(1,[z7,z1,z2,z3,z538,z6]),(0,[z7,z1,z188,z2,z3,z14,z6]),(1,[z7,z2,z3,z4,z6,z380]),(0,[z7,z76,z2,z3,z4,z6,z18]),(0,[z7,z1,z2,z3,z4,z6,z539]),(0,[z7,z1,z2,z3,z4,z296,z6]),(0,[z7,z1,z2,z33,z4,z6,z93]),(0,[z107,z7,z1,z2,z10,z4,z6])],[(0,[z7,z1,z2,z3,z4,z6,z540]),(0,[z83,z7,z1,z2,z207,z4,z6]),(0,[z239,z7,z1,z55,z3,z4,z6])],[(0,[z7,z1,z2,z2,z3,z4,z6]),(0,[z541,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z10,z135,z4,z6]),(1,[z7,z1,z244,z3,z4,z13]),(0,[z7,z1,z2,z3,z4,z542,z6]),(0,[z7,z543,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z544,z3,z4,z6]),(0,[z7,z1,z2,z545,z3,z4,z6]),(0,[z374,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z55,z3,z14,z6]),(0,[z7,z1,z2,z546,z3,z4,z6])]],
   [[(0,[z547,z7,z1,z2,z3,z4,z6]),(0,[z548,z7,z1,z2,z3,z4,z6]),(0,[z549,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z550,z6]),(0,[z107,z7,z1,z2,z33,z4,z6])],[(0,[z171,z112,z7,z2,z3,z4,z6]),(0,[z551,z7,z1,z2,z3,z4,z6]),(0,[z7,z225,z1,z2,z3,z14,z6]),(0,[z7,z1,z552,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z330,z4,z6]),(0,[z7,z1,z530,z2,z3,z4,z6])],[(0,[z553,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z104,z3,z4,z6]),(0,[z111,z7,z1,z2,z25,z3,z6]),(0,[z9,z7,z1,z2,z3,z4,z350]),(0,[z7,z1,z2,z3,z4,z554,z6]),(0,[z555,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z556,z6])],[(0,[z557,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z558,z4,z6]),(0,[z7,z1,z2,z33,z62,z4,z6]),(0,[z7,z218,z1,z2,z3,z4,z6]),(1,[z77,z7,z1,z2,z4,z202])],[(0,[z171,z7,z225,z2,z3,z4,z6]),(0,[z559,z7,z1,z2,z33,z4,z6]),(1,[z7,z2,z3,z136,z61,z6]),(0,[z7,z1,z2,z3,z4,z6,z560])],[(0,[z7,z1,z561,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z562]),(0,[z7,z1,z2,z3,z563,z4,z6]),(0,[z564,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z240,z14,z6]),(0,[z7,z1,z2,z3,z4,z565,z6]),(1,[z7,z1,z2,z267,z4,z209])],[(0,[z7,z1,z566,z2,z3,z4,z6]),(0,[z567,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z33,z33,z4,z6]),(0,[z568,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z569,z4,z6]),(0,[z7,z1,z2,z3,z4,z570,z6]),(0,[z7,z1,z2,z3,z4,z6,z380]),(0,[z7,z1,z2,z3,z4,z5,z22]),(0,[z7,z1,z2,z3,z4,z6,z571]),(0,[z7,z1,z2,z33,z4,z12,z6]),(0,[z284,z7,z1,z2,z10,z4,z6]),(0,[z572,z7,z1,z2,z3,z4,z6])]],
   [[(0,[z7,z1,z2,z3,z4,z573,z6]),(0,[z574,z7,z1,z2,z3,z4,z6]),(0,[z9,z7,z2,z3,z129,z4,z6]),(0,[z39,z7,z1,z2,z3,z296,z6]),(1,[z7,z1,z2,z3,z305,z6]),(0,[z7,z1,z56,z2,z3,z61,z6]),(0,[z7,z1,z2,z10,z163,z4,z6])],[(0,[z111,z7,z1,z2,z128,z3,z6]),(0,[z9,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z575,z4,z6]),(0,[z7,z1,z2,z33,z91,z4,z6]),(0,[z576,z7,z1,z2,z3,z4,z6]),(0,[z577,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z578,z4,z6])],[(0,[z579,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z33,z4,z134,z6]),(1,[z7,z1,z2,z390,z4,z6]),(0,[z7,z1,z2,z3,z4,z580,z6])],[(0,[z111,z1,z2,z3,z4,z134,z6]),(1,[z404,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z581,z6]),(0,[z7,z1,z582,z2,z3,z4,z6]),(0,[z7,z1,z244,z2,z3,z4,z6])],[(0,[z159,z7,z1,z2,z3,z14,z6]),(0,[z583,z7,z1,z2,z3,z4,z6]),(0,[z7,z225,z2,z207,z3,z4,z6]),(1,[z7,z1,z2,z3,z162,z6]),(0,[z7,z1,z56,z2,z3,z203,z6]),(0,[z7,z1,z55,z2,z3,z61,z6]),(0,[z107,z7,z1,z2,z3,z14,z6]),(0,[z446,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z584])],[(0,[z7,z1,z2,z585,z3,z4,z6]),(0,[z109,z7,z1,z2,z41,z4,z6]),(0,[z7,z1,z2,z586,z3,z4,z6]),(0,[z501,z7,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z33,z4,z6,z22]),(0,[z239,z7,z1,z2,z187,z4,z6]),(1,[z7,z1,z2,z330,z4,z6]),(0,[z7,z1,z2,z3,z4,z587,z6])],[(1,[z7,z1,z2,z3,z506,z6])],[(0,[z171,z159,z7,z2,z3,z4,z6]),(0,[z7,z2,z45,z3,z4,z6,z18]),(0,[z588,z7,z1,z2,z3,z4,z6]),(0,[z7,z2,z207,z3,z23,z4,z6]),(0,[z7,z1,z2,z3,z136,z61,z6]),(0,[z7,z1,z2,z3,z235,z61,z6]),(0,[z63,z85,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z413,z4,z6])]],
   [[(0,[z7,z1,z2,z3,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z589]),(0,[z7,z1,z590,z2,z3,z4,z6]),(1,[z7,z1,z2,z455,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z591]),(0,[z99,z531,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z33,z4,z209,z6]),(0,[z7,z1,z2,z3,z41,z14,z6]),(0,[z7,z1,z2,z592,z3,z4,z6]),(0,[z7,z1,z593,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z91,z6,z93])],[(0,[z9,z39,z7,z2,z3,z4,z6]),(1,[z7,z1,z2,z3,z521,z6]),(0,[z7,z1,z2,z3,z4,z6,z594]),(0,[z98,z7,z1,z2,z3,z61,z6]),(1,[z531,z1,z2,z3,z4,z6]),(1,[z99,z7,z2,z3,z4,z12]),(1,[z7,z1,z236,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z34,z6]),(0,[z7,z1,z595,z2,z3,z4,z6]),(0,[z43,z7,z1,z2,z3,z4,z6])],[(2,[z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z4,z6,z596]),(0,[z7,z1,z2,z41,z4,z209,z6])],[(0,[z7,z1,z2,z3,z597,z4,z6]),(1,[z7,z1,z2,z569,z4,z6]),(0,[z7,z1,z188,z2,z3,z538,z6]),(0,[z7,z1,z2,z207,z3,z61,z6]),(0,[z7,z1,z2,z3,z201,z4,z6]),(0,[z7,z1,z2,z3,z14,z6,z202]),(0,[z7,z1,z244,z2,z153,z4,z6])],[(0,[z598,z7,z1,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z3,z8,z6]),(0,[z7,z1,z2,z10,z4,z6,z21])],[(0,[z171,z7,z2,z45,z3,z4,z6]),(0,[z7,z1,z2,z3,z599,z4,z6]),(1,[z7,z1,z2,z409,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z6]),(0,[z9,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z6,z48]),(0,[z281,z7,z1,z2,z3,z14,z6]),(1,[z7,z1,z2,z3,z276,z6])],[(0,[z171,z1,z44,z2,z3,z4,z6]),(0,[z600,z7,z1,z2,z3,z4,z6]),(0,[z7,z116,z1,z2,z3,z4,z6]),(0,[z254,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z2,z3,z61,z6])],[(0,[z601,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z296,z6]),(0,[z7,z1,z2,z3,z4,z602,z6]),(0,[z603,z7,z1,z2,z3,z4,z6]),(0,[z99,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z604,z4,z6]),(0,[z123,z7,z1,z2,z10,z4,z6]),(0,[z374,z7,z1,z2,z3,z61,z6]),(1,[z7,z1,z3,z14,z61,z6]),(0,[z7,z1,z2,z3,z61,z6,z202])]],
   [[(0,[z7,z1,z2,z605,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z140]),(0,[z7,z1,z2,z606,z3,z4,z6]),(0,[z7,z1,z607,z2,z3,z4,z6]),(1,[z7,z1,z2,z10,z4,z6])],[(0,[z608,z7,z1,z2,z3,z4,z6]),(1,[z7,z484,z2,z3,z4,z6]),(0,[z9,z7,z1,z2,z3,z4,z321]),(0,[z7,z225,z1,z2,z207,z4,z6]),(0,[z7,z1,z2,z33,z4,z470,z6])],[(0,[z58,z1,z2,z3,z35,z4,z6]),(0,[z99,z7,z2,z3,z129,z4,z6]),(0,[z609,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z610,z3,z4,z6]),(0,[z29,z1,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z70,z14,z6]),(0,[z7,z611,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z612,z4,z6]),(0,[z557,z7,z1,z2,z3,z61,z6]),(1,[z7,z1,z2,z413,z4,z6]),(0,[z7,z1,z244,z2,z3,z183,z6]),(0,[z613,z7,z1,z2,z3,z4,z6])],[(1,[z7,z1,z2,z393,z4,z6]),(0,[z38,z7,z614,z2,z3,z4,z6]),(0,[z30,z20,z1,z2,z3,z4,z6]),(0,[z7,z1,z40,z2,z3,z521,z6]),(0,[z83,z7,z1,z2,z3,z4,z6]),(1,[z83,z7,z2,z23,z4,z6]),(0,[z112,z7,z1,z2,z3,z4,z18]),(1,[z7,z1,z2,z33,z4,z6])],[(0,[z615,z7,z1,z2,z3,z4,z6]),(1,[z0,z171,z2,z3,z4,z6]),(0,[z111,z7,z1,z2,z33,z4,z6]),(0,[z343,z7,z1,z2,z3,z4,z6]),(0,[z20,z7,z1,z2,z3,z4,z18]),(0,[z7,z1,z2,z3,z4,z6,z616]),(0,[z564,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z4,z6,z617]),(1,[z7,z1,z2,z427,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z92])],[(1,[z7,z1,z2,z3,z4,z220]),(0,[z618,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z409,z4,z134,z6]),(0,[z7,z1,z2,z3,z4,z619,z6]),(0,[z7,z1,z2,z3,z4,z620,z6]),(0,[z7,z1,z2,z621,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z622,z6]),(0,[z7,z1,z2,z10,z4,z6,z93])],[(0,[z623,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z624,z6]),(0,[z20,z7,z1,z2,z33,z4,z6]),(0,[z30,z7,z1,z2,z3,z61,z6])]],
   [[(0,[z1,z2,z3,z70,z4,z134,z6]),(0,[z77,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z625,z4,z6])],[(0,[z626,z7,z1,z2,z3,z4,z6]),(0,[z7,z627,z1,z2,z3,z4,z6]),(0,[z38,z7,z1,z2,z3,z61,z6]),(0,[z39,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z628,z4,z6]),(1,[z7,z1,z2,z128,z41,z6])],[(0,[z7,z1,z2,z3,z629,z4,z6]),(0,[z7,z1,z2,z3,z191,z4,z6]),(0,[z7,z1,z2,z23,z33,z4,z6]),(0,[z7,z1,z2,z47,z3,z23,z6]),(0,[z7,z1,z2,z3,z235,z91,z4])],[(0,[z630,z7,z1,z2,z3,z4,z6]),(1,[z7,z76,z40,z3,z4,z6]),(0,[z7,z1,z40,z2,z10,z4,z6]),(0,[z7,z2,z3,z4,z12,z6,z18]),(0,[z7,z1,z244,z2,z3,z61,z6])],[(0,[z7,z1,z484,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z631]),(0,[z7,z1,z632,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z14,z14,z6]),(1,[z7,z1,z2,z3,z17,z6]),(0,[z633,z7,z1,z2,z3,z4,z6])],[(1,[z7,z1,z2,z448,z4,z6]),(0,[z7,z1,z188,z2,z3,z506,z6]),(0,[z7,z1,z2,z3,z4,z634,z6]),(0,[z7,z1,z2,z10,z62,z4,z6]),(0,[z635,z7,z1,z2,z3,z4,z6])],[(0,[z0,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z636,z6]),(0,[z7,z1,z637,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z129,z4,z6]),(0,[z638,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z3,z14,z4,z61,z6])],[(0,[z639,z7,z1,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z104,z4,z6]),(0,[z7,z1,z2,z3,z4,z640,z6]),(0,[z7,z1,z2,z3,z14,z6,z584])]],
   [[(0,[z7,z1,z2,z3,z641,z4,z6]),(0,[z254,z7,z1,z3,z33,z4,z6]),(0,[z7,z1,z2,z10,z33,z4,z6]),(0,[z7,z1,z2,z3,z4,z642,z6])],[(0,[z7,z1,z2,z3,z643,z4,z6]),(0,[z111,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z644,z4,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z10,z4,z12,z6]),(0,[z645,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z3,z306,z6]),(0,[z646,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z188,z2,z569,z4,z6]),(0,[z7,z1,z2,z3,z647,z4,z6]),(0,[z648,z7,z1,z2,z3,z4,z6])],[(0,[z171,z7,z76,z2,z3,z4,z6]),(0,[z115,z7,z1,z2,z3,z4,z6]),(1,[z7,z1,z2,z3,z4,z471]),(0,[z20,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z649,z3,z4,z6]),(0,[z7,z1,z2,z367,z33,z4,z6]),(0,[z7,z1,z2,z10,z91,z4,z6]),(0,[z7,z1,z2,z25,z10,z4,z6]),(1,[z7,z1,z2,z460,z4,z6]),(0,[z7,z1,z2,z3,z4,z269,z6]),(0,[z7,z1,z2,z3,z4,z6,z650])],[(0,[z651,z7,z1,z2,z3,z4,z6]),(0,[z1,z44,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z10,z4,z134,z6]),(0,[z7,z1,z2,z3,z4,z652,z6]),(0,[z7,z1,z2,z3,z14,z34,z6])],[(0,[z7,z653,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z205,z3,z4,z6]),(0,[z7,z1,z2,z3,z654,z4,z6]),(0,[z7,z1,z2,z3,z655,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z656]),(0,[z7,z1,z2,z3,z4,z15,z6]),(0,[z7,z1,z2,z25,z3,z41,z6]),(0,[z7,z1,z2,z3,z657,z4,z6])],[(0,[z7,z1,z2,z3,z658,z4,z6]),(0,[z7,z1,z2,z3,z659,z4,z6]),(0,[z7,z2,z3,z129,z4,z296,z6]),(0,[z254,z7,z1,z2,z3,z61,z6])],[(0,[z7,z76,z44,z2,z3,z4,z6]),(0,[z660,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z188,z2,z10,z4,z6]),(1,[z7,z614,z2,z3,z4,z6]),(0,[z7,z1,z2,z25,z33,z4,z6]),(0,[z7,z1,z2,z10,z4,z6,z22]),(0,[z7,z1,z2,z3,z661,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z662]),(1,[z7,z2,z3,z312,z4,z6])]],
   [[(0,[z7,z1,z663,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z664]),(0,[z7,z1,z2,z3,z4,z6,z665]),(0,[z7,z1,z2,z3,z666,z4,z6]),(0,[z7,z1,z2,z33,z235,z4,z6]),(1,[z7,z1,z2,z10,z61,z6]),(0,[z374,z7,z2,z3,z4,z61,z6]),(0,[z7,z1,z2,z3,z61,z34,z6]),(1,[z7,z1,z2,z25,z34,z6])],[(0,[z7,z1,z2,z667,z3,z4,z6]),(0,[z668,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z669,z3,z4,z6]),(0,[z7,z670,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z671]),(0,[z77,z7,z530,z2,z3,z4,z6]),(0,[z7,z1,z2,z672,z3,z4,z6])],[(0,[z673,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z674,z4,z6])],[(0,[z7,z1,z188,z2,z393,z4,z6]),(0,[z7,z1,z2,z3,z35,z14,z6]),(1,[z42,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z675,z6]),(0,[z211,z7,z1,z2,z33,z4,z6]),(0,[z676,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z677,z4,z6])],[(0,[z83,z7,z1,z2,z3,z61,z6]),(0,[z7,z225,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z10,z3,z14,z6])],[(0,[z171,z7,z1,z2,z10,z4,z6]),(0,[z38,z1,z2,z3,z70,z4,z6]),(0,[z7,z1,z2,z33,z4,z296,z6]),(1,[z7,z1,z33,z4,z61,z6]),(0,[z7,z1,z2,z3,z62,z4,z93])],[(0,[z29,z7,z1,z188,z3,z4,z6]),(0,[z525,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z128,z3,z41,z6])],[(0,[z7,z1,z2,z3,z538,z4,z6]),(0,[z7,z1,z2,z3,z4,z678,z6]),(0,[z7,z1,z2,z3,z235,z6,z93])]],
   [[(0,[z7,z1,z679,z2,z3,z4,z6]),(0,[z171,z7,z2,z3,z129,z4,z6]),(0,[z7,z225,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z128,z33,z4,z6]),(1,[z7,z1,z2,z3,z203,z6]),(0,[z7,z1,z2,z3,z60,z4,z6]),(0,[z7,z1,z2,z153,z3,z4,z6])],[(0,[z171,z7,z1,z2,z33,z4,z6]),(0,[z680,z7,z1,z2,z3,z4,z6]),(0,[z681,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z628,z61,z6]),(0,[z7,z1,z2,z25,z4,z209,z6])],[(0,[z29,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z614,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z682,z6]),(0,[z7,z1,z2,z3,z4,z6,z683]),(0,[z9,z7,z1,z2,z390,z4,z6]),(0,[z7,z1,z2,z3,z4,z684,z6]),(0,[z7,z1,z2,z3,z4,z6,z685]),(0,[z7,z1,z2,z3,z686,z4,z6])],[(0,[z0,z20,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z687,z3,z4,z6]),(0,[z9,z404,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z13,z18]),(0,[z688,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z25,z3,z14,z6]),(0,[z7,z1,z2,z3,z91,z4,z93])],[(0,[z7,z1,z2,z3,z689,z4,z6]),(0,[z7,z1,z2,z401,z33,z4,z6]),(0,[z77,z7,z1,z2,z3,z4,z209])],[(0,[z112,z7,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z690,z3,z4,z6]),(0,[z99,z7,z2,z3,z23,z4,z6]),(0,[z7,z1,z691,z2,z3,z4,z6]),(0,[z7,z250,z1,z2,z10,z4,z6])],[(0,[z0,z7,z1,z2,z3,z61,z6]),(0,[z29,z7,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z35,z33,z4,z6]),(0,[z83,z7,z2,z3,z23,z4,z6]),(0,[z7,z1,z2,z179,z3,z23,z6]),(0,[z7,z1,z2,z3,z4,z692,z6]),(0,[z7,z1,z2,z3,z129,z61,z6]),(0,[z7,z1,z2,z3,z4,z100,z6]),(0,[z63,z7,z1,z244,z3,z4,z6]),(0,[z693,z7,z1,z2,z3,z4,z6])],[(0,[z159,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z33,z4,z13,z6])]],
   [[(0,[z7,z1,z694,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z4,z6]),(0,[z343,z38,z7,z2,z3,z4,z6]),(1,[z30,z1,z2,z3,z4,z5]),(0,[z9,z7,z1,z2,z455,z4,z6]),(0,[z7,z1,z2,z695,z3,z4,z6]),(0,[z7,z1,z2,z10,z4,z329,z6]),(0,[z7,z696,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z697,z6]),(0,[z7,z1,z2,z210,z3,z4,z6])],[(0,[z171,z39,z7,z2,z3,z4,z6]),(1,[z501,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z698])],[(0,[z7,z1,z699,z2,z3,z4,z6]),(0,[z7,z1,z244,z2,z3,z4,z13]),(0,[z7,z1,z2,z700,z3,z4,z6])],[(0,[z107,z7,z1,z2,z3,z4,z6]),(0,[z159,z7,z1,z2,z33,z4,z6]),(0,[z115,z7,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z25,z3,z34,z6])],[(0,[z7,z1,z701,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z6,z702]),(1,[z7,z1,z2,z151,z3,z6]),(0,[z30,z7,z1,z2,z3,z4,z12]),(0,[z7,z1,z2,z3,z703,z4,z6]),(0,[z272,z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z227,z14,z6]),(0,[z7,z1,z2,z128,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z6,z704])],[(0,[z171,z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z205,z3,z61,z6]),(0,[z705,z7,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z706,z4,z6]),(0,[z7,z1,z2,z45,z3,z14,z6]),(1,[z7,z1,z3,z33,z61,z6]),(1,[z7,z1,z2,z187,z4,z6])],[(0,[z559,z7,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z661,z61,z6]),(0,[z7,z1,z2,z3,z41,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z1,z2,z707,z4,z6]),(0,[z1,z2,z3,z4,z5,z708]),(0,[z7,z1,z2,z390,z290,z6])],[(0,[z311,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z4,z709])],[(0,[z343,z7,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z710,z6]),(0,[z7,z1,z2,z711,z4,z6]),(0,[z7,z1,z236,z3,z91,z6])],[(0,[z7,z1,z2,z152,z4,z6])],[(0,[z7,z1,z2,z3,z712,z6]),(0,[z7,z1,z2,z330,z61,z6]),(0,[z1,z2,z3,z4,z6,z713])],[(0,[z0,z7,z1,z33,z61,z6]),(0,[z7,z1,z694,z3,z61,z6]),(0,[z7,z1,z2,z3,z714,z6]),(0,[z311,z1,z2,z3,z4,z321]),(0,[z249,z7,z1,z3,z61,z6])],[(0,[z7,z1,z2,z3,z4,z715]),(0,[z7,z1,z2,z104,z4,z471]),(0,[z7,z1,z2,z4,z6,z716])],[(0,[z7,z1,z2,z455,z61,z6]),(0,[z7,z1,z157,z3,z4,z13]),(0,[z374,z7,z56,z3,z61,z6])],[(0,[z254,z7,z1,z33,z162,z6]),(0,[z7,z1,z2,z10,z717,z6]),(0,[z7,z1,z2,z4,z6,z92])],[(0,[z7,z1,z593,z33,z4,z6]),(0,[z374,z7,z3,z14,z61,z6])],[(0,[z7,z1,z2,z569,z61,z6]),(0,[z374,z7,z2,z10,z4,z6]),(0,[z7,z169,z2,z3,z4,z13])],[(0,[z1,z2,z718,z3,z4,z6]),(0,[z7,z172,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z290,z350]),(0,[z7,z2,z719,z3,z61,z6]),(0,[z7,z218,z2,z257,z4,z6])],[(0,[z42,z7,z2,z3,z4,z12]),(0,[z7,z1,z2,z390,z338,z6]),(0,[z7,z1,z2,z3,z720,z6]),(0,[z7,z169,z2,z3,z4,z22])],[(0,[z588,z171,z2,z3,z4,z6]),(0,[z29,z1,z188,z3,z4,z6]),(0,[z7,z1,z2,z721,z4,z6])],[(0,[z7,z614,z2,z3,z4,z6]),(0,[z343,z7,z2,z3,z14,z6]),(0,[z7,z1,z2,z10,z290,z6]),(0,[z7,z1,z2,z3,z199,z6]),(0,[z77,z7,z1,z2,z275,z202])],[(0,[z7,z1,z2,z104,z61,z6]),(0,[z7,z1,z33,z296,z61,z6])]],
   [[(0,[z112,z7,z2,z3,z61,z18]),(0,[z722,z1,z2,z3,z4,z6])],[],[(0,[z109,z1,z2,z205,z14,z6]),(0,[z7,z1,z2,z3,z723,z6]),(0,[z7,z724,z2,z10,z4,z6]),(0,[z7,z1,z2,z413,z61,z6])],[(0,[z83,z7,z2,z23,z61,z6])],[(0,[z7,z156,z2,z3,z14,z6]),(0,[z7,z2,z33,z4,z6,z380]),(0,[z7,z1,z2,z3,z725,z6]),(0,[z555,z7,z2,z3,z4,z12]),(0,[z211,z1,z2,z143,z4,z6]),(0,[z7,z1,z24,z10,z4,z6]),(0,[z7,z1,z2,z427,z61,z6])],[(0,[z42,z7,z2,z3,z4,z140]),(0,[z7,z1,z726,z3,z4,z6]),(0,[z7,z1,z2,z727,z3,z6]),(0,[z7,z1,z593,z3,z14,z6]),(0,[z7,z728,z2,z3,z4,z6])],[(0,[z7,z1,z2,z729,z3,z6]),(0,[z7,z1,z110,z33,z4,z6]),(0,[z730,z1,z2,z3,z4,z6]),(0,[z7,z731,z2,z3,z4,z6])],[(0,[z7,z1,z2,z732,z4,z6]),(0,[z7,z172,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z338,z350]),(0,[z98,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z203,z6]),(0,[z7,z1,z2,z4,z6,z733])],[(0,[z7,z1,z33,z61,z113,z6]),(0,[z7,z56,z3,z136,z61,z6])],[(0,[z29,z415,z2,z3,z4,z6]),(1,[z7,z1,z33,z255,z6]),(0,[z63,z7,z1,z3,z17,z22])],[(0,[z7,z1,z2,z3,z4,z734]),(0,[z7,z1,z2,z10,z338,z6]),(0,[z7,z1,z2,z3,z735,z61])],[(0,[z115,z1,z27,z3,z4,z6]),(0,[z736,z1,z2,z3,z4,z6]),(0,[z7,z1,z33,z4,z329,z6]),(0,[z7,z1,z33,z41,z61,z6])],[(0,[z7,z1,z2,z737,z4,z6]),(0,[z7,z2,z33,z136,z61,z6]),(0,[z7,z1,z2,z33,z62,z235])],[(0,[z7,z1,z2,z10,z289,z6]),(0,[z29,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z738,z6]),(0,[z7,z1,z2,z739,z4,z6])],[(0,[z159,z44,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z740,z6]),(0,[z7,z1,z3,z4,z741,z6]),(0,[z7,z742,z2,z3,z4,z6])],[]],
   [[(0,[z7,z1,z2,z743,z4,z6]),(0,[z7,z1,z2,z744,z4,z6])],[(0,[z745,z7,z2,z3,z4,z6]),(0,[z501,z354,z2,z3,z4,z6]),(0,[z7,z225,z2,z207,z4,z6]),(0,[z374,z7,z2,z215,z3,z6])],[(0,[z7,z1,z2,z3,z61,z471]),(0,[z7,z746,z2,z3,z4,z6]),(0,[z7,z1,z110,z3,z14,z6]),(0,[z30,z1,z2,z3,z4,z550]),(0,[z577,z7,z2,z3,z4,z18]),(0,[z7,z1,z2,z460,z61,z6])],[(0,[z7,z1,z2,z3,z289,z220]),(0,[z20,z7,z2,z3,z4,z380]),(0,[z7,z1,z33,z61,z5,z6]),(0,[z7,z1,z2,z10,z255,z6]),(0,[z7,z1,z2,z210,z91,z6])],[(0,[z7,z2,z3,z747,z4,z6]),(0,[z254,z7,z1,z33,z14,z6])],[(0,[z748,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z191,z61,z6]),(0,[z7,z1,z2,z3,z749,z6]),(0,[z531,z1,z2,z3,z4,z18]),(0,[z7,z1,z33,z61,z6,z18]),(0,[z99,z7,z2,z3,z4,z750]),(0,[z7,z1,z3,z33,z61,z6])],[(0,[z58,z1,z2,z35,z14,z6]),(0,[z7,z1,z2,z751,z4,z6]),(0,[z39,z7,z2,z3,z338,z6]),(0,[z1,z2,z33,z752,z4,z6]),(0,[z374,z7,z2,z33,z61,z6])],[(0,[z7,z1,z2,z3,z8,z6]),(0,[z7,z1,z2,z33,z31,z6]),(0,[z374,z7,z33,z4,z61,z6])],[(0,[z7,z1,z2,z753,z4,z6]),(0,[z7,z1,z2,z754,z3,z6]),(0,[z7,z1,z2,z47,z10,z6]),(0,[z7,z1,z2,z755,z4,z6]),(0,[z39,z7,z2,z3,z136,z6]),(0,[z7,z1,z2,z756,z33,z6]),(0,[z7,z1,z2,z128,z242,z6]),(0,[z7,z1,z2,z4,z209,z228])],[(0,[z7,z1,z2,z757,z4,z6]),(0,[z7,z116,z2,z10,z4,z6]),(0,[z7,z758,z2,z3,z4,z6]),(0,[z109,z1,z2,z759,z4,z6]),(0,[z63,z7,z1,z3,z61,z22]),(0,[z7,z1,z2,z760,z4,z6])],[(0,[z7,z1,z2,z448,z289,z6]),(0,[z7,z761,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z6,z762]),(0,[z99,z7,z2,z3,z4,z453]),(0,[z7,z1,z2,z3,z763,z6])],[(0,[z7,z1,z2,z764,z3,z6]),(0,[z564,z1,z2,z3,z134,z6]),(0,[z765,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z766,z4,z6]),(0,[z7,z1,z56,z33,z61,z6]),(0,[z7,z1,z56,z10,z203,z6]),(0,[z7,z767,z2,z3,z4,z6]),(0,[z768,z7,z2,z3,z4,z6])],[(0,[z7,z1,z2,z10,z4,z288]),(0,[z7,z1,z2,z3,z769,z6]),(0,[z7,z770,z2,z3,z4,z6]),(0,[z771,z1,z2,z3,z4,z6]),(0,[z772,z1,z2,z3,z4,z6]),(0,[z7,z773,z2,z3,z4,z6]),(0,[z7,z1,z24,z25,z34,z6])],[(0,[z111,z7,z1,z236,z3,z6]),(0,[z30,z42,z2,z3,z4,z5])],[(0,[z20,z1,z2,z33,z4,z21]),(0,[z7,z76,z40,z3,z31,z6]),(0,[z7,z1,z2,z3,z774,z6]),(0,[z7,z1,z2,z3,z775,z6])],[(0,[z7,z116,z2,z3,z4,z220])]],
   [[(0,[z7,z1,z2,z3,z4,z776]),(0,[z7,z1,z2,z777,z4,z6]),(0,[z7,z1,z2,z778,z4,z6])],[(0,[z7,z1,z2,z3,z779,z6]),(0,[z7,z1,z2,z780,z4,z6]),(0,[z58,z1,z2,z592,z4,z6]),(0,[z7,z1,z2,z3,z4,z781]),(0,[z7,z1,z10,z33,z14,z6])],[(0,[z7,z1,z2,z3,z4,z782]),(0,[z7,z1,z2,z257,z14,z6])],[(0,[z99,z7,z2,z3,z14,z12])],[(0,[z7,z1,z2,z783,z4,z6]),(0,[z85,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z784,z4,z6]),(0,[z7,z76,z2,z3,z4,z321])],[(0,[z112,z7,z2,z3,z4,z750]),(0,[z7,z1,z2,z33,z91,z93])],[(0,[z7,z116,z2,z448,z4,z6]),(0,[z7,z785,z2,z3,z4,z6]),(0,[z7,z415,z2,z33,z4,z6])],[(0,[z38,z7,z1,z236,z3,z6]),(0,[z30,z1,z2,z3,z61,z5]),(0,[z7,z1,z2,z3,z14,z350])],[(0,[z311,z1,z2,z3,z4,z6]),(0,[z501,z7,z2,z3,z61,z6]),(1,[z7,z726,z3,z4,z6]),(0,[z7,z1,z2,z786,z33,z6]),(0,[z7,z1,z2,z198,z60,z6])],[(0,[z7,z1,z2,z787,z4,z6]),(0,[z7,z103,z2,z3,z4,z6])],[(0,[z20,z1,z2,z3,z14,z21]),(0,[z99,z7,z2,z3,z4,z678]),(0,[z559,z7,z1,z2,z4,z202]),(0,[z788,z7,z2,z3,z4,z6])],[(0,[z7,z789,z2,z3,z4,z6]),(0,[z688,z7,z1,z3,z4,z22]),(0,[z7,z1,z464,z3,z61,z6])],[(0,[z7,z116,z2,z3,z4,z471]),(0,[z7,z1,z2,z790,z4,z6]),(0,[z7,z1,z2,z791,z4,z6])],[(0,[z7,z1,z2,z187,z61,z6])],[(0,[z7,z1,z2,z3,z792,z6]),(0,[z7,z1,z478,z33,z4,z6])],[(0,[z20,z1,z2,z3,z4,z702]),(0,[z7,z1,z2,z793,z4,z6])]],
   [[(0,[z7,z1,z2,z794,z4,z6]),(0,[z7,z1,z2,z3,z795,z6])],[(0,[z7,z1,z2,z3,z4,z796]),(0,[z286,z7,z2,z3,z4,z18]),(0,[z7,z1,z2,z797,z61,z6])],[(0,[z7,z415,z2,z3,z14,z6]),(0,[z798,z1,z2,z3,z4,z6]),(0,[z130,z1,z2,z427,z4,z6])],[(0,[z7,z1,z2,z799,z4,z6]),(0,[z7,z2,z3,z800,z506,z6]),(0,[z7,z3,z33,z136,z61,z6])],[(0,[z7,z1,z2,z274,z329,z6]),(0,[z43,z7,z2,z3,z61,z6])],[(0,[z343,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z801,z4,z6]),(0,[z7,z802,z2,z3,z4,z6]),(0,[z7,z1,z3,z242,z14,z6]),(0,[z803,z7,z2,z3,z4,z6])],[(0,[z354,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z153,z4,z6]),(0,[z7,z1,z33,z61,z355,z6]),(0,[z7,z1,z2,z804,z34,z6])],[(0,[z115,z1,z27,z3,z8,z6]),(0,[z7,z805,z2,z3,z4,z6]),(0,[z42,z7,z2,z3,z4,z18]),(0,[z7,z1,z2,z3,z176,z240]),(0,[z806,z1,z2,z3,z4,z6])],[(0,[z7,z807,z2,z33,z4,z6]),(0,[z7,z808,z2,z3,z4,z6])],[(0,[z7,z1,z809,z3,z4,z6]),(0,[z7,z1,z2,z455,z290,z6]),(0,[z7,z1,z33,z4,z6,z432]),(0,[z7,z1,z215,z33,z61,z6]),(0,[z7,z169,z2,z10,z4,z6]),(0,[z7,z1,z3,z61,z15,z6]),(0,[z130,z1,z2,z3,z17,z6])],[(0,[z360,z7,z2,z3,z4,z12]),(0,[z39,z7,z2,z3,z4,z321]),(0,[z7,z1,z478,z3,z14,z6])],[(0,[z7,z156,z2,z33,z4,z6]),(0,[z810,z1,z2,z3,z4,z6]),(0,[z7,z530,z2,z10,z4,z6]),(0,[z7,z1,z3,z4,z6,z811]),(0,[z7,z1,z2,z4,z6,z812])],[(0,[z7,z1,z2,z3,z4,z813]),(0,[z7,z1,z2,z814,z4,z6])],[(0,[z7,z1,z2,z3,z4,z815]),(0,[z111,z1,z2,z3,z816,z6]),(0,[z7,z1,z2,z25,z558,z6])],[(0,[z7,z76,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z183,z6]),(0,[z7,z169,z2,z427,z4,z6])],[(0,[z7,z1,z2,z817,z4,z6])]],
   [[],[(0,[z7,z2,z3,z4,z818,z6]),(0,[z7,z1,z2,z10,z538,z6]),(0,[z7,z1,z33,z61,z6,z21]),(1,[z374,z7,z33,z61,z6]),(0,[z7,z1,z10,z14,z61,z6]),(0,[z7,z2,z3,z312,z14,z6])],[(0,[z7,z1,z2,z819,z4,z6]),(0,[z0,z748,z2,z3,z4,z6]),(0,[z7,z820,z2,z3,z4,z6]),(0,[z7,z1,z56,z10,z4,z6]),(0,[z7,z1,z33,z61,z388,z6]),(0,[z821,z7,z2,z3,z4,z6])],[(0,[z7,z822,z2,z3,z4,z6]),(0,[z7,z1,z35,z33,z61,z6]),(0,[z823,z7,z2,z3,z4,z6])],[(0,[z551,z1,z27,z3,z4,z6]),(0,[z7,z824,z2,z3,z14,z6]),(0,[z7,z1,z2,z210,z4,z6]),(0,[z7,z1,z2,z128,z456,z6])],[(0,[z501,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z455,z338,z6]),(0,[z7,z1,z10,z385,z4,z6]),(0,[z7,z250,z2,z207,z4,z6]),(0,[z7,z169,z2,z3,z17,z6]),(0,[z7,z1,z2,z3,z91,z120])],[(0,[z7,z1,z2,z825,z4,z6]),(0,[z7,z218,z2,z10,z4,z6]),(0,[z7,z1,z2,z153,z183,z6])],[(0,[z7,z1,z244,z33,z4,z13]),(0,[z559,z7,z1,z2,z4,z48])],[(0,[z278,z1,z27,z3,z4,z6]),(0,[z7,z1,z3,z4,z6,z826]),(0,[z7,z1,z2,z3,z827,z6]),(0,[z7,z1,z828,z3,z4,z6]),(0,[z7,z1,z55,z33,z14,z6]),(0,[z7,z2,z3,z829,z4,z6])],[(0,[z7,z1,z2,z3,z61,z140]),(0,[z130,z1,z2,z3,z61,z6]),(0,[z63,z85,z1,z3,z4,z22]),(0,[z7,z1,z2,z153,z199,z6])],[(0,[z7,z225,z2,z830,z4,z6])],[(0,[z7,z1,z2,z831,z4,z6]),(0,[z254,z7,z1,z33,z4,z6]),(0,[z7,z218,z2,z427,z4,z6])],[(0,[z7,z1,z2,z3,z832,z6]),(0,[z7,z1,z2,z3,z833,z6])],[(0,[z58,z1,z2,z35,z4,z6]),(0,[z58,z1,z2,z163,z4,z6]),(0,[z404,z1,z2,z3,z4,z350]),(0,[z7,z1,z2,z10,z305,z6]),(0,[z7,z250,z2,z266,z4,z6])],[(0,[z7,z1,z2,z3,z834,z6]),(0,[z7,z1,z33,z33,z61,z6]),(0,[z239,z7,z1,z3,z61,z6]),(0,[z835,z1,z2,z3,z61,z6])],[(0,[z426,z171,z2,z3,z4,z6]),(0,[z836,z7,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z837]),(0,[z281,z1,z2,z3,z19,z6]),(0,[z7,z1,z2,z3,z62,z235])]],
   [[(0,[z7,z1,z2,z104,z289,z6]),(0,[z30,z1,z2,z3,z4,z640]),(0,[z7,z1,z2,z3,z838,z6]),(0,[z7,z1,z2,z3,z839,z6]),(0,[z404,z1,z2,z10,z4,z6]),(0,[z7,z840,z2,z3,z4,z6])],[(0,[z7,z1,z2,z10,z162,z6]),(0,[z7,z1,z2,z33,z841,z4]),(0,[z7,z1,z33,z91,z61,z6])],[(0,[z7,z1,z2,z3,z842,z6]),(0,[z7,z843,z2,z3,z4,z6]),(0,[z7,z218,z2,z3,z17,z6]),(0,[z7,z1,z2,z257,z276,z6]),(0,[z821,z7,z2,z3,z183,z6])],[(0,[z7,z1,z2,z10,z506,z6]),(0,[z7,z2,z207,z830,z4,z6]),(0,[z7,z1,z33,z61,z6,z423]),(0,[z7,z1,z244,z3,z14,z13])],[(0,[z7,z1,z2,z3,z844,z6]),(0,[z7,z1,z2,z25,z659,z6]),(0,[z39,z7,z1,z33,z61,z6])],[(0,[z1,z2,z27,z3,z4,z471]),(0,[z7,z1,z2,z275,z209,z6])],[(0,[z1,z718,z27,z3,z4,z6]),(0,[z7,z1,z2,z3,z845,z4]),(0,[z7,z1,z2,z10,z521,z6]),(0,[z83,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z128,z60,z6]),(0,[z7,z1,z2,z14,z6,z92]),(0,[z63,z130,z1,z3,z4,z22])],[(0,[z29,z1,z2,z3,z4,z471]),(0,[z7,z1,z2,z3,z846,z6])],[(0,[z7,z1,z2,z3,z847,z6]),(0,[z7,z1,z2,z3,z848,z6]),(0,[z7,z1,z10,z33,z4,z6]),(0,[z849,z1,z2,z3,z4,z6])],[(0,[z0,z20,z2,z3,z4,z18]),(0,[z9,z7,z45,z3,z4,z6]),(0,[z7,z2,z10,z312,z4,z6]),(0,[z374,z7,z2,z3,z61,z6]),(0,[z77,z7,z1,z2,z306,z202])],[(0,[z7,z1,z2,z850,z4,z6]),(0,[z7,z1,z2,z3,z31,z6]),(0,[z7,z2,z621,z3,z4,z18]),(0,[z531,z1,z2,z33,z4,z6]),(0,[z99,z7,z2,z33,z4,z12]),(0,[z7,z1,z2,z10,z276,z6]),(0,[z7,z1,z2,z267,z14,z209]),(0,[z7,z1,z2,z3,z275,z6])],[(0,[z7,z1,z2,z3,z4,z851]),(0,[z85,z1,z2,z3,z4,z13])],[(0,[z7,z116,z2,z104,z4,z6]),(0,[z7,z852,z2,z10,z4,z6])],[(0,[z7,z1,z55,z49,z14,z6])],[(0,[z360,z1,z2,z3,z4,z5]),(0,[z7,z484,z2,z10,z4,z6]),(0,[z7,z1,z2,z33,z4,z350]),(0,[z7,z1,z25,z236,z34,z6])],[(0,[z7,z1,z2,z390,z14,z6]),(0,[z7,z1,z33,z61,z209,z6]),(0,[z7,z1,z2,z427,z276,z6])]],
   [[],[(0,[z171,z7,z2,z179,z3,z6]),(0,[z7,z1,z2,z853,z4,z6]),(0,[z7,z1,z2,z854,z4,z6])],[(0,[z0,z171,z2,z10,z4,z6]),(0,[z39,z7,z2,z3,z521,z6]),(0,[z7,z1,z2,z152,z31,z6]),(0,[z7,z1,z2,z330,z14,z6])],[(0,[z7,z1,z2,z855,z4,z6]),(0,[z7,z1,z2,z3,z289,z471]),(0,[z7,z1,z2,z390,z4,z321]),(0,[z7,z1,z24,z3,z61,z6])],[],[(0,[z0,z1,z2,z3,z4,z288]),(0,[z171,z416,z2,z3,z4,z6]),(0,[z111,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z455,z14,z6]),(0,[z7,z1,z2,z25,z388,z6]),(0,[z7,z1,z2,z856,z4,z6]),(0,[z7,z1,z2,z804,z4,z6])],[(0,[z7,z1,z718,z3,z4,z6]),(0,[z531,z1,z2,z3,z14,z6])],[(0,[z7,z1,z2,z33,z4,z220]),(0,[z7,z1,z2,z3,z857,z6]),(0,[z107,z7,z1,z33,z61,z6]),(0,[z7,z2,z33,z4,z858,z6]),(0,[z7,z1,z2,z3,z62,z240])],[(0,[z7,z1,z2,z569,z14,z6]),(0,[z7,z76,z40,z10,z4,z6]),(0,[z7,z1,z33,z61,z470,z6]),(0,[z7,z1,z3,z625,z61,z6]),(0,[z1,z2,z3,z859,z4,z6])],[(0,[z7,z1,z2,z455,z4,z321]),(0,[z860,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z861,z6])],[(0,[z7,z1,z2,z862,z4,z6]),(0,[z7,z1,z2,z863,z4,z6])],[(0,[z7,z1,z2,z864,z4,z6]),(0,[z39,z7,z2,z3,z296,z6]),(0,[z7,z1,z3,z33,z255,z6]),(0,[z7,z1,z3,z14,z741,z6])],[(0,[z7,z2,z3,z136,z521,z6]),(0,[z7,z1,z2,z10,z14,z6]),(1,[z7,z1,z2,z4,z865])],[(0,[z7,z1,z419,z10,z4,z6]),(0,[z112,z7,z2,z3,z14,z18])],[(0,[z7,z1,z260,z3,z61,z6])]],
   [[(0,[z7,z1,z2,z866,z3,z6]),(0,[z111,z1,z2,z592,z3,z6]),(0,[z30,z1,z2,z3,z4,z708]),(0,[z525,z1,z2,z334,z4,z6]),(0,[z7,z1,z2,z413,z14,z6])],[(0,[z7,z1,z2,z3,z867,z6]),(0,[z7,z1,z2,z868,z4,z6]),(0,[z1,z2,z3,z70,z816,z6]),(0,[z7,z1,z2,z869,z4,z6]),(0,[z7,z1,z2,z10,z4,z321]),(0,[z83,z7,z2,z23,z14,z6]),(0,[z7,z870,z2,z3,z4,z6])],[(0,[z7,z1,z2,z871,z4,z6]),(0,[z872,z1,z2,z3,z4,z6]),(0,[z7,z225,z2,z695,z4,z6]),(0,[z7,z1,z236,z33,z61,z6]),(0,[z7,z1,z2,z33,z306,z6]),(0,[z7,z1,z2,z427,z14,z6])],[(0,[z112,z7,z2,z3,z4,z140]),(0,[z7,z1,z2,z3,z14,z220]),(0,[z7,z1,z2,z3,z873,z6])],[(0,[z7,z1,z2,z3,z4,z874]),(0,[z7,z614,z2,z10,z4,z6]),(0,[z7,z1,z2,z875,z33,z6]),(0,[z7,z2,z3,z876,z4,z6])],[(0,[z7,z1,z3,z185,z61,z6]),(0,[z1,z2,z3,z816,z134,z6]),(0,[z7,z1,z2,z3,z877,z6])],[(0,[z7,z1,z2,z3,z878,z6]),(0,[z7,z225,z2,z3,z4,z140]),(0,[z211,z7,z1,z33,z61,z6]),(0,[z77,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z879,z61])],[(0,[z0,z147,z2,z3,z4,z6]),(0,[z7,z1,z25,z33,z61,z6]),(0,[z7,z1,z3,z61,z642,z6]),(0,[z7,z1,z2,z25,z804,z6])],[(0,[z7,z116,z2,z3,z61,z6]),(0,[z7,z1,z632,z10,z4,z6])],[(0,[z7,z1,z2,z3,z880,z6]),(0,[z7,z1,z2,z3,z881,z6]),(0,[z7,z1,z438,z10,z4,z6]),(0,[z7,z2,z3,z4,z13,z380]),(0,[z1,z2,z3,z4,z882,z6])],[(0,[z7,z1,z2,z448,z14,z6]),(0,[z7,z1,z2,z4,z209,z865])],[(0,[z7,z1,z2,z3,z61,z288]),(0,[z883,z1,z2,z3,z4,z6]),(0,[z7,z1,z3,z677,z61,z6]),(0,[z7,z824,z2,z3,z4,z6])],[(0,[z159,z44,z2,z3,z14,z6]),(0,[z7,z225,z2,z511,z4,z6]),(0,[z109,z1,z2,z205,z4,z6]),(0,[z42,z7,z2,z33,z4,z6])],[(0,[z884,z7,z2,z3,z14,z6])],[(0,[z7,z156,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z885,z4]),(0,[z886,z7,z2,z3,z4,z6]),(0,[z7,z887,z2,z3,z4,z6]),(0,[z7,z1,z2,z128,z804,z6])],[(0,[z7,z888,z2,z3,z4,z6]),(0,[z7,z1,z2,z569,z538,z6]),(0,[z7,z1,z2,z889,z3,z6]),(0,[z890,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z198,z41,z6])]],
   [[(0,[z7,z1,z2,z3,z14,z471]),(0,[z7,z1,z2,z891,z3,z6]),(1,[z7,z2,z3,z4,z750]),(0,[z7,z1,z299,z10,z4,z6]),(0,[z7,z1,z2,z460,z14,z6])],[(0,[z7,z172,z2,z3,z4,z6])],[(0,[z7,z2,z3,z4,z892,z6]),(0,[z893,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z894,z6])],[(0,[z7,z1,z2,z3,z895,z6]),(0,[z7,z1,z2,z191,z14,z6]),(0,[z7,z1,z461,z10,z4,z6]),(0,[z7,z896,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z897,z6])],[],[(0,[z7,z1,z898,z3,z4,z6]),(0,[z7,z899,z2,z3,z4,z6]),(0,[z404,z1,z2,z390,z4,z6]),(0,[z66,z7,z2,z105,z4,z6])],[(0,[z7,z1,z27,z33,z61,z6])],[(0,[z7,z2,z45,z3,z4,z140]),(0,[z7,z1,z2,z3,z900,z6])],[(0,[z7,z1,z2,z3,z4,z901]),(0,[z7,z1,z2,z3,z816,z6]),(0,[z42,z7,z2,z3,z14,z6]),(0,[z7,z902,z2,z3,z4,z6])],[(0,[z30,z1,z2,z33,z4,z5]),(0,[z7,z1,z2,z903,z4,z6])],[(0,[z748,z159,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z904]),(0,[z38,z1,z2,z3,z816,z6]),(0,[z501,z7,z2,z33,z4,z6]),(0,[z7,z905,z2,z10,z4,z6]),(0,[z7,z1,z244,z3,z4,z13])],[(0,[z7,z1,z2,z756,z3,z6]),(0,[z404,z1,z2,z455,z4,z6]),(0,[z7,z1,z472,z33,z4,z6]),(0,[z7,z1,z55,z3,z14,z6])],[(0,[z7,z1,z2,z3,z906,z6]),(0,[z7,z1,z324,z33,z4,z6]),(0,[z111,z7,z1,z2,z133,z6]),(0,[z7,z1,z2,z3,z907,z6]),(0,[z7,z1,z2,z908,z4,z6]),(0,[z77,z7,z1,z236,z4,z6]),(0,[z7,z1,z2,z3,z909,z6])],[(0,[z7,z1,z2,z910,z3,z6]),(0,[z431,z1,z2,z3,z4,z21]),(0,[z7,z911,z2,z3,z4,z6]),(0,[z912,z7,z2,z3,z4,z6])],[(0,[z83,z7,z2,z47,z23,z6]),(0,[z7,z1,z2,z128,z303,z6]),(0,[z7,z1,z2,z913,z61,z6])],[]],
   [[(0,[z914,z7,z2,z3,z4,z6])],[(0,[z7,z1,z2,z569,z506,z6]),(0,[z7,z1,z854,z33,z4,z6])],[(0,[z85,z1,z2,z257,z4,z6])],[(0,[z20,z44,z2,z3,z4,z12]),(0,[z452,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z41,z365,z6]),(0,[z7,z1,z2,z3,z915,z6]),(0,[z7,z1,z2,z215,z388,z6])],[(0,[z7,z1,z2,z3,z841,z4]),(0,[z7,z1,z2,z133,z61,z6]),(0,[z343,z7,z2,z25,z3,z6])],[(0,[z7,z76,z679,z3,z4,z6]),(0,[z30,z1,z2,z3,z14,z5]),(0,[z7,z1,z916,z3,z4,z6]),(0,[z354,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z25,z15,z6])],[(0,[z38,z7,z1,z2,z133,z6]),(0,[z501,z7,z2,z3,z14,z6]),(0,[z7,z1,z2,z390,z4,z6]),(0,[z43,z7,z2,z33,z4,z6])],[(0,[z917,z7,z2,z3,z4,z6])],[(0,[z1,z2,z196,z3,z4,z21]),(0,[z39,z7,z2,z3,z168,z6]),(0,[z7,z1,z33,z4,z6,z662]),(0,[z7,z1,z2,z918,z10,z6]),(0,[z7,z169,z2,z3,z61,z6])],[(0,[z7,z2,z726,z3,z4,z6]),(0,[z7,z1,z33,z61,z34,z6]),(0,[z7,z1,z236,z10,z4,z6])],[(0,[z7,z919,z2,z3,z4,z6]),(0,[z223,z1,z2,z3,z4,z21]),(0,[z7,z1,z2,z3,z920,z6]),(0,[z7,z530,z2,z3,z61,z6])],[(0,[z0,z668,z2,z3,z4,z6]),(0,[z7,z921,z2,z3,z4,z6]),(0,[z7,z1,z2,z922,z4,z6]),(0,[z7,z1,z2,z3,z4,z923]),(0,[z7,z1,z2,z786,z3,z6]),(0,[z7,z1,z2,z187,z14,z6]),(0,[z7,z2,z3,z924,z183,z6])],[(0,[z7,z2,z3,z4,z800,z6]),(0,[z7,z1,z2,z257,z4,z6])],[(0,[z531,z1,z2,z3,z4,z6]),(0,[z7,z1,z590,z33,z4,z6]),(0,[z99,z7,z2,z3,z4,z12]),(0,[z7,z1,z2,z918,z3,z6]),(0,[z7,z1,z244,z3,z199,z13])],[(0,[z7,z1,z2,z3,z4,z925]),(0,[z7,z1,z2,z926,z4,z6]),(0,[z7,z1,z2,z3,z927,z6])],[(0,[z7,z1,z2,z928,z4,z6]),(0,[z7,z1,z2,z33,z929,z4])]],
   [[(0,[z7,z1,z2,z151,z33,z6]),(0,[z7,z1,z2,z3,z4,z750]),(0,[z85,z1,z2,z3,z4,z22])],[(0,[z7,z484,z2,z104,z4,z6]),(0,[z7,z1,z2,z3,z4,z350]),(0,[z7,z2,z3,z930,z296,z6]),(0,[z7,z1,z56,z3,z61,z6]),(0,[z7,z3,z14,z136,z61,z6])],[(0,[z468,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z931,z6]),(0,[z7,z1,z33,z628,z61,z6]),(0,[z7,z1,z2,z3,z628,z235]),(0,[z43,z7,z2,z3,z14,z6])],[(0,[z7,z1,z2,z932,z4,z6]),(0,[z7,z1,z3,z14,z61,z6])],[(0,[z7,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z4,z933]),(0,[z20,z1,z2,z3,z4,z21]),(0,[z1,z2,z3,z934,z4,z6]),(0,[z7,z2,z3,z62,z235,z312])],[(0,[z7,z1,z2,z3,z935,z6]),(0,[z936,z1,z2,z3,z4,z6]),(0,[z112,z7,z2,z33,z4,z18]),(0,[z7,z1,z2,z3,z937,z6]),(0,[z7,z218,z2,z3,z61,z6])],[(0,[z9,z7,z59,z3,z4,z6]),(0,[z7,z1,z2,z938,z4,z6]),(0,[z7,z1,z198,z33,z4,z6])],[(0,[z7,z1,z2,z3,z4,z939]),(0,[z7,z484,z2,z3,z4,z220]),(0,[z7,z2,z3,z61,z6,z380]),(0,[z374,z7,z2,z3,z338,z6]),(0,[z7,z1,z33,z129,z61,z6]),(0,[z77,z7,z1,z2,z61,z202]),(0,[z7,z1,z2,z236,z34,z6])],[(0,[z278,z7,z45,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z940]),(0,[z38,z1,z2,z3,z100,z6]),(0,[z7,z1,z2,z941,z4,z6]),(0,[z7,z942,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z943]),(0,[z7,z1,z2,z944,z4,z6]),(0,[z374,z7,z2,z3,z136,z6])],[(0,[z7,z1,z2,z3,z16,z584])],[(0,[z7,z1,z2,z33,z4,z140]),(0,[z7,z945,z2,z3,z4,z6]),(0,[z7,z1,z2,z946,z4,z6]),(0,[z7,z2,z3,z830,z4,z6]),(0,[z7,z1,z2,z3,z91,z93])],[(0,[z7,z415,z2,z3,z4,z6]),(0,[z7,z947,z2,z3,z4,z6]),(0,[z7,z1,z2,z948,z4,z6]),(0,[z7,z1,z2,z949,z4,z6])],[(0,[z7,z1,z2,z950,z3,z6]),(0,[z7,z1,z2,z128,z41,z6])],[(0,[z7,z484,z2,z448,z4,z6]),(0,[z7,z1,z2,z951,z4,z6]),(0,[z7,z1,z150,z3,z61,z6]),(0,[z7,z1,z2,z3,z952,z6]),(0,[z7,z1,z2,z41,z804,z6])],[(0,[z404,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z191,z521,z6]),(0,[z7,z1,z2,z3,z953,z6]),(0,[z7,z954,z2,z3,z61,z6]),(0,[z374,z7,z2,z3,z355,z6])]],
   [[(0,[z7,z1,z2,z104,z14,z6]),(0,[z7,z1,z2,z33,z17,z6]),(0,[z7,z1,z2,z4,z865,z202])],[(0,[z7,z955,z2,z3,z4,z6]),(0,[z7,z1,z2,z956,z4,z6]),(0,[z7,z1,z2,z3,z957,z6]),(0,[z7,z1,z2,z3,z4,z958]),(0,[z959,z1,z2,z33,z4,z6]),(0,[z7,z2,z3,z4,z6,z960])],[(0,[z38,z7,z1,z33,z61,z6]),(0,[z281,z1,z2,z3,z70,z6]),(0,[z99,z7,z2,z179,z3,z6]),(0,[z1,z2,z3,z4,z6,z961])],[(0,[z159,z44,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z962,z6]),(0,[z7,z1,z2,z3,z4,z865])],[(0,[z7,z1,z2,z3,z963,z6]),(0,[z7,z484,z2,z3,z4,z471]),(0,[z7,z76,z726,z3,z4,z6]),(0,[z112,z354,z2,z3,z4,z6]),(0,[z964,z7,z2,z33,z4,z6])],[(0,[z7,z1,z2,z3,z965,z6]),(0,[z7,z1,z2,z966,z4,z6]),(0,[z7,z1,z2,z3,z306,z6])],[(0,[z7,z1,z2,z967,z4,z6]),(0,[z38,z1,z2,z33,z70,z6]),(0,[z7,z1,z180,z3,z61,z6]),(0,[z7,z2,z3,z968,z14,z6])],[(0,[z7,z1,z2,z3,z14,z140]),(0,[z7,z1,z2,z33,z4,z471]),(0,[z7,z1,z2,z969,z4,z6]),(0,[z7,z1,z2,z10,z199,z6]),(0,[z63,z7,z1,z3,z276,z22])],[(0,[z7,z1,z2,z3,z970,z6]),(0,[z99,z7,z2,z3,z4,z336]),(0,[z971,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z4,z6,z865])],[(0,[z7,z972,z2,z3,z4,z6]),(0,[z7,z1,z2,z409,z61,z6]),(0,[z973,z1,z2,z3,z4,z6]),(0,[z7,z1,z33,z60,z61,z6]),(0,[z7,z2,z3,z61,z6,z974]),(0,[z7,z1,z2,z975,z4,z6])],[(0,[z1,z44,z2,z3,z4,z288]),(0,[z7,z1,z2,z976,z4,z6]),(0,[z7,z1,z2,z413,z199,z6])],[(0,[z7,z1,z2,z3,z977,z6]),(0,[z7,z2,z3,z312,z4,z6]),(0,[z7,z1,z2,z3,z84,z423])],[(0,[z978,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z25,z34,z6])],[(0,[z171,z457,z2,z3,z4,z6]),(0,[z7,z484,z2,z3,z61,z6]),(0,[z7,z1,z208,z33,z61,z6])],[(0,[z63,z7,z1,z33,z4,z22]),(0,[z7,z807,z2,z3,z4,z6])],[(0,[z42,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z979,z6]),(0,[z7,z980,z2,z33,z4,z6])]],
   [[(0,[z115,z1,z718,z3,z4,z6]),(0,[z7,z1,z2,z393,z61,z6]),(0,[z7,z2,z179,z3,z6,z18]),(0,[z7,z1,z2,z33,z61,z6]),(0,[z7,z1,z2,z10,z203,z6]),(0,[z7,z981,z2,z3,z4,z6])],[(0,[z0,z171,z2,z3,z61,z6]),(0,[z7,z982,z2,z3,z4,z6]),(0,[z7,z76,z40,z191,z4,z6]),(0,[z7,z1,z33,z4,z61,z6]),(1,[z7,z1,z460,z61,z6]),(0,[z7,z1,z2,z210,z91,z93])],[(0,[z159,z354,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z983]),(0,[z111,z1,z2,z133,z134,z6]),(0,[z7,z1,z2,z830,z4,z6]),(0,[z354,z225,z2,z3,z4,z6]),(0,[z7,z1,z2,z984,z4,z6]),(0,[z7,z1,z55,z33,z4,z6]),(0,[z7,z1,z985,z3,z4,z6])],[(0,[z7,z1,z2,z201,z4,z470]),(0,[z7,z1,z3,z227,z61,z6]),(0,[z7,z1,z2,z4,z6,z986])],[(0,[z159,z7,z2,z3,z4,z140]),(0,[z115,z1,z27,z10,z4,z6])],[(0,[z7,z1,z3,z503,z61,z6]),(0,[z987,z7,z2,z3,z4,z6])],[(0,[z130,z169,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z988,z6]),(0,[z7,z76,z40,z3,z61,z6]),(0,[z7,z2,z10,z4,z136,z6]),(0,[z989,z1,z2,z3,z4,z6])],[],[(0,[z7,z116,z2,z3,z289,z6]),(0,[z990,z1,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z750,z18]),(0,[z7,z1,z2,z128,z227,z6]),(0,[z7,z1,z2,z3,z991,z6])],[(0,[z7,z1,z2,z3,z4,z992]),(0,[z7,z1,z2,z3,z993,z6]),(0,[z115,z1,z27,z3,z4,z220]),(0,[z7,z2,z3,z4,z6,z994]),(0,[z7,z1,z2,z179,z33,z6]),(0,[z63,z7,z1,z3,z14,z22])],[(0,[z7,z1,z2,z995,z4,z6]),(0,[z7,z1,z2,z3,z996,z6]),(0,[z7,z1,z2,z997,z4,z6]),(0,[z1,z2,z33,z4,z6,z837]),(0,[z7,z2,z3,z4,z924,z6])],[(0,[z7,z998,z2,z3,z4,z6]),(0,[z9,z7,z45,z3,z4,z350]),(0,[z7,z1,z2,z3,z741,z6]),(0,[z7,z2,z3,z999,z4,z6])],[(0,[z7,z1,z419,z3,z61,z6])],[(0,[z111,z1,z2,z3,z269,z6]),(0,[z7,z1,z460,z4,z61,z6]),(0,[z7,z1,z2,z1000,z4,z6])],[]],
   [[(0,[z7,z1,z2,z10,z8,z6]),(1,[z1,z2,z3,z4,z708]),(0,[z7,z1,z2,z3,z61,z321]),(0,[z7,z1,z2,z3,z4,z1001]),(0,[z1,z2,z3,z61,z6,z713])],[(0,[z115,z1,z27,z448,z4,z6]),(0,[z7,z1,z2,z3,z4,z1002]),(0,[z7,z1,z56,z3,z1003,z6])],[(0,[z7,z1,z2,z198,z135,z6]),(0,[z7,z1,z2,z3,z235,z1004])],[(0,[z7,z614,z2,z3,z61,z6]),(0,[z311,z1,z2,z390,z4,z6]),(0,[z354,z2,z45,z3,z4,z6]),(0,[z435,z7,z1,z33,z4,z6]),(0,[z130,z218,z2,z3,z4,z6]),(0,[z7,z1,z2,z25,z642,z6])],[(0,[z7,z767,z2,z10,z4,z6]),(0,[z241,z7,z1,z3,z61,z6]),(0,[z7,z1,z2,z267,z4,z209])],[(0,[z7,z1,z2,z1005,z4,z6]),(0,[z7,z1,z2,z49,z61,z6]),(0,[z7,z1,z244,z153,z4,z13])],[(0,[z7,z1,z2,z3,z1006,z6]),(0,[z7,z1,z2,z3,z8,z220]),(0,[z7,z1,z2,z3,z1007,z6]),(0,[z284,z1,z2,z163,z4,z6]),(0,[z7,z1,z2,z3,z1004,z91])],[(0,[z311,z76,z2,z3,z4,z6]),(0,[z7,z1,z632,z3,z61,z6])],[(0,[z7,z1,z438,z3,z61,z6]),(0,[z175,z7,z1,z2,z4,z90]),(0,[z77,z7,z1,z2,z275,z6])],[(0,[z7,z1,z2,z3,z4,z1008])],[(0,[z7,z1,z2,z3,z4,z1009]),(0,[z7,z116,z2,z33,z4,z6])],[(0,[z30,z501,z2,z3,z4,z5]),(0,[z7,z1,z492,z33,z4,z6]),(0,[z229,z7,z2,z3,z168,z6])],[(0,[z7,z1,z2,z1010,z4,z6]),(0,[z7,z1,z2,z330,z4,z6]),(0,[z1011,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z1012,z4,z6])],[(0,[z7,z1,z2,z33,z4,z288]),(0,[z7,z1,z2,z448,z8,z6]),(0,[z7,z1,z2,z3,z1013,z6]),(0,[z7,z1,z2,z3,z1014,z6]),(0,[z7,z1,z2,z4,z6,z1015]),(0,[z85,z1,z2,z10,z4,z6]),(0,[z1016,z1,z2,z3,z4,z6]),(0,[z7,z1,z244,z3,z183,z13])],[(0,[z7,z1,z2,z4,z6,z1017]),(0,[z343,z7,z2,z128,z3,z6]),(0,[z311,z1,z2,z3,z4,z350]),(0,[z66,z7,z1,z33,z61,z6]),(0,[z7,z1,z55,z3,z203,z6]),(0,[z7,z1,z2,z14,z6,z986])],[(0,[z7,z1,z2,z455,z4,z6]),(0,[z454,z7,z1,z3,z61,z6]),(0,[z7,z1,z2,z3,z1018,z6]),(0,[z7,z1,z299,z3,z61,z6]),(1,[z7,z1,z2,z3,z1004])]],
   [[(0,[z748,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1019,z6]),(0,[z58,z156,z2,z35,z4,z6]),(0,[z1020,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z4,z6,z1021])],[(0,[z7,z1,z2,z3,z1022,z6]),(0,[z311,z1,z2,z10,z4,z6]),(0,[z7,z1,z2,z3,z1023,z6])],[(0,[z7,z1,z2,z569,z4,z6]),(0,[z7,z1,z2,z1024,z4,z6]),(0,[z7,z1,z2,z3,z929,z4]),(0,[z7,z1,z461,z3,z61,z6]),(0,[z7,z1,z114,z10,z4,z6]),(0,[z7,z103,z2,z10,z4,z6]),(0,[z85,z1,z2,z427,z4,z6])],[(0,[z29,z1,z701,z3,z4,z6]),(0,[z7,z1,z2,z3,z8,z471]),(0,[z7,z1,z2,z3,z1025,z6]),(0,[z58,z172,z2,z35,z4,z6]),(0,[z20,z1,z2,z3,z4,z708]),(0,[z7,z2,z719,z3,z4,z6]),(0,[z7,z1026,z2,z3,z4,z6])],[(0,[z7,z1,z1027,z3,z4,z6]),(0,[z525,z7,z1,z33,z61,z6])],[(0,[z7,z1,z2,z3,z1028,z6]),(0,[z1029,z1,z2,z3,z4,z6]),(1,[z7,z2,z830,z4,z6]),(0,[z374,z7,z1,z33,z61,z6]),(0,[z7,z1,z244,z33,z61,z6])],[(0,[z7,z116,z2,z3,z14,z6]),(0,[z568,z7,z1,z33,z4,z6])],[(0,[z7,z1,z2,z104,z4,z6]),(0,[z7,z1,z2,z875,z3,z6]),(0,[z111,z1,z2,z409,z134,z6]),(0,[z7,z1,z2,z1030,z4,z6]),(0,[z7,z1,z492,z3,z14,z6]),(0,[z7,z1,z2,z1031,z4,z6]),(0,[z130,z1,z2,z3,z276,z6])],[(0,[z1032,z7,z2,z3,z4,z6]),(0,[z112,z7,z2,z3,z4,z18]),(0,[z7,z1,z33,z242,z4,z6]),(0,[z7,z1,z2,z25,z481,z6])],[(0,[z7,z1,z2,z3,z14,z288]),(0,[z7,z1,z2,z33,z1033,z6]),(0,[z85,z1,z2,z3,z17,z6]),(0,[z7,z1,z3,z4,z13,z811])],[(0,[z1034,z7,z2,z3,z506,z6]),(0,[z551,z7,z1,z3,z4,z22]),(0,[z7,z2,z33,z4,z6,z960]),(0,[z7,z1,z2,z413,z4,z6]),(0,[z272,z7,z2,z67,z4,z6])],[(0,[z7,z1,z2,z3,z1035,z6]),(0,[z1036,z7,z2,z3,z4,z6]),(0,[z1,z2,z205,z759,z4,z6]),(0,[z7,z1,z2,z3,z4,z1037]),(0,[z83,z7,z2,z23,z4,z6]),(0,[z7,z1,z143,z33,z61,z6])],[(0,[z7,z1,z2,z427,z4,z6]),(0,[z7,z1,z236,z3,z235,z6])],[(0,[z7,z2,z3,z129,z4,z140]),(0,[z7,z1,z2,z3,z4,z220]),(0,[z77,z7,z1,z2,z4,z90])],[(0,[z1038,z7,z2,z3,z4,z6]),(0,[z111,z1,z2,z33,z134,z6]),(0,[z343,z7,z2,z10,z4,z6]),(0,[z130,z1,z2,z33,z4,z6]),(0,[z7,z1,z10,z625,z4,z6])],[(0,[z0,z171,z2,z3,z4,z140]),(0,[z7,z1,z205,z33,z61,z6])]],
   [[(0,[z7,z1039,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z1040]),(0,[z7,z1,z2,z4,z6,z1041])],[(0,[z7,z1,z2,z3,z1042,z6]),(0,[z7,z1,z346,z33,z4,z6]),(0,[z404,z1,z2,z3,z290,z6]),(0,[z772,z1,z2,z3,z61,z6]),(0,[z7,z1,z2,z3,z628,z661])],[(0,[z7,z1,z3,z4,z811,z22])],[(0,[z7,z1,z2,z1043,z3,z6]),(0,[z7,z1,z2,z3,z4,z1044]),(0,[z7,z1,z2,z3,z4,z1045]),(0,[z83,z7,z2,z67,z4,z6]),(0,[z835,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z33,z1046,z6]),(0,[z7,z1,z2,z3,z17,z6])],[(0,[z7,z1,z2,z448,z4,z6]),(0,[z29,z1,z188,z569,z4,z6]),(0,[z7,z1,z2,z1047,z4,z6]),(0,[z7,z2,z33,z312,z4,z6]),(0,[z959,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z91,z584]),(0,[z77,z7,z1,z2,z4,z120])],[(0,[z1,z2,z33,z4,z882,z6]),(0,[z7,z1048,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1049,z6])],[(0,[z159,z44,z2,z3,z4,z6]),(0,[z171,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z4,z1050])],[(0,[z7,z1,z2,z3,z1051,z6]),(0,[z7,z1,z2,z1052,z4,z6]),(0,[z374,z7,z2,z3,z129,z6]),(0,[z354,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z10,z183,z6]),(0,[z884,z7,z2,z3,z4,z6])],[(0,[z9,z7,z1,z33,z61,z6]),(0,[z7,z1,z56,z3,z255,z6]),(0,[z7,z1,z236,z3,z61,z6]),(0,[z7,z1,z49,z33,z4,z6])],[(0,[z7,z1,z2,z1053,z4,z6])],[(0,[z7,z1,z2,z3,z4,z1054]),(0,[z7,z1,z2,z3,z4,z471]),(0,[z437,z7,z2,z3,z4,z18]),(0,[z7,z1,z59,z33,z4,z6]),(0,[z7,z169,z2,z33,z4,z6]),(0,[z7,z1,z2,z460,z4,z6]),(0,[z7,z1,z2,z1055,z4,z6]),(0,[z130,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z413,z183,z6])],[(0,[z7,z1,z10,z185,z4,z6])],[(0,[z0,z501,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z1056]),(0,[z7,z1,z33,z227,z61,z6]),(0,[z1057,z7,z2,z3,z61,z6])],[(0,[z7,z1,z346,z3,z14,z6]),(0,[z7,z2,z3,z1058,z4,z6]),(0,[z404,z1,z2,z3,z338,z6]),(0,[z7,z1,z2,z191,z4,z6]),(0,[z32,z7,z2,z23,z4,z6]),(0,[z39,z7,z2,z243,z3,z6]),(0,[z374,z7,z2,z3,z296,z6]),(0,[z7,z1,z2,z3,z1059,z6]),(0,[z7,z1,z2,z3,z62,z1004])],[(0,[z374,z7,z2,z33,z4,z6]),(0,[z7,z1,z2,z25,z78,z6])],[(0,[z7,z1,z3,z14,z371,z6])]],
   [[(0,[z7,z1,z208,z3,z61,z6]),(0,[z7,z1,z2,z128,z135,z6])],[(0,[z63,z7,z1,z3,z4,z22])],[(0,[z7,z1,z2,z3,z1060,z6]),(0,[z7,z1,z2,z1061,z3,z6]),(0,[z7,z1,z2,z33,z290,z6]),(0,[z7,z1,z2,z3,z4,z1062]),(0,[z7,z980,z2,z3,z4,z6]),(0,[z7,z1,z3,z578,z14,z6])],[(0,[z7,z1,z2,z3,z61,z6]),(0,[z354,z1,z2,z3,z14,z6])],[(0,[z39,z7,z2,z3,z287,z6]),(0,[z9,z7,z45,z390,z4,z6]),(0,[z7,z2,z3,z4,z12,z750]),(0,[z99,z7,z1,z33,z61,z6]),(0,[z254,z7,z1,z854,z4,z6]),(0,[z1063,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z1064,z6]),(0,[z441,z7,z1,z2,z25,z6]),(0,[z7,z40,z726,z3,z4,z6]),(0,[z7,z1,z2,z1065,z4,z6]),(0,[z1066,z7,z1,z2,z33,z4])],[(0,[z1067,z1,z2,z3,z4,z6]),(0,[z7,z1,z59,z3,z14,z6]),(0,[z7,z1,z2,z3,z1068,z6]),(0,[z7,z169,z2,z3,z14,z6]),(0,[z1069,z1,z2,z3,z4,z6])],[(0,[z115,z1,z27,z104,z4,z6]),(0,[z7,z218,z2,z33,z4,z6]),(0,[z7,z1070,z2,z3,z4,z6]),(0,[z239,z7,z1,z10,z61,z6])],[(0,[z29,z1,z144,z3,z4,z6]),(0,[z7,z1,z24,z33,z4,z6]),(0,[z7,z1,z2,z10,z62,z235]),(0,[z7,z1,z2,z1071,z4,z6])],[(0,[z7,z1,z1072,z3,z4,z6])],[(0,[z115,z7,z1,z33,z61,z6]),(0,[z9,z7,z45,z455,z4,z6]),(0,[z7,z1,z2,z801,z61,z6]),(0,[z374,z7,z2,z3,z14,z6]),(0,[z7,z2,z3,z61,z858,z6])],[(0,[z7,z1,z2,z1073,z4,z6]),(0,[z7,z1,z2,z3,z4,z1074]),(0,[z7,z1,z2,z25,z132,z6]),(0,[z7,z1,z2,z152,z61,z6]),(0,[z7,z1,z2,z1075,z4,z6]),(0,[z7,z843,z2,z10,z4,z6])],[(0,[z7,z1,z2,z3,z1076,z6]),(0,[z38,z614,z2,z3,z70,z6]),(0,[z7,z33,z4,z136,z61,z6])],[(0,[z7,z2,z3,z129,z338,z6])],[(0,[z7,z1,z2,z33,z338,z6]),(0,[z7,z2,z45,z3,z4,z321]),(0,[z7,z1,z2,z33,z735,z4])],[(0,[z7,z1,z2,z1077,z3,z6]),(0,[z30,z1,z2,z3,z4,z5]),(0,[z7,z1,z2,z3,z845,z61])]],
   [[(0,[z501,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1078,z6]),(0,[z7,z2,z3,z23,z4,z140]),(0,[z58,z1,z2,z151,z35,z6]),(0,[z7,z1079,z2,z3,z4,z6]),(1,[z7,z1,z854,z4,z6]),(0,[z7,z1,z2,z25,z488,z6])],[(0,[z7,z1,z2,z33,z289,z6]),(0,[z559,z7,z1,z33,z61,z6]),(0,[z7,z1,z10,z854,z4,z6])],[(0,[z7,z1,z2,z3,z290,z321]),(0,[z9,z7,z45,z10,z4,z6]),(0,[z374,z7,z2,z10,z61,z6])],[(0,[z7,z1,z2,z1080,z4,z6]),(0,[z7,z1,z2,z104,z8,z6]),(0,[z7,z1,z2,z151,z3,z6]),(0,[z7,z1,z2,z10,z31,z6]),(0,[z7,z1,z2,z3,z1081,z6]),(0,[z7,z1,z2,z3,z1082,z6]),(0,[z7,z1,z2,z10,z275,z6]),(0,[z7,z218,z2,z3,z14,z6])],[(0,[z1083,z7,z1,z2,z4,z6]),(0,[z112,z7,z1,z33,z61,z6]),(0,[z7,z1,z24,z3,z14,z6])],[(0,[z29,z1,z188,z3,z61,z6]),(0,[z7,z1,z2,z3,z6,z1084]),(0,[z7,z1,z2,z3,z1085,z6]),(0,[z7,z1,z2,z187,z4,z6]),(0,[z131,z1,z2,z3,z269,z6])],[],[(0,[z7,z225,z1,z33,z61,z6]),(0,[z457,z7,z2,z3,z4,z18]),(0,[z7,z1,z2,z33,z255,z6]),(0,[z63,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z61,z6,z92])],[(0,[z44,z2,z3,z4,z573,z6]),(0,[z7,z1,z2,z3,z1086,z6]),(0,[z7,z726,z45,z3,z4,z6]),(0,[z7,z1,z33,z4,z255,z6]),(0,[z7,z1,z56,z49,z4,z6])],[(0,[z7,z1,z2,z210,z61,z6])],[(0,[z115,z1,z27,z3,z4,z471]),(0,[z7,z1,z2,z1087,z4,z6]),(0,[z7,z1,z595,z10,z4,z6]),(0,[z239,z7,z1,z460,z61,z6]),(0,[z7,z1,z535,z3,z61,z6])],[(0,[z7,z1,z2,z3,z1088,z6]),(0,[z7,z1,z2,z1089,z33,z6])],[(0,[z311,z1,z2,z455,z4,z6]),(0,[z7,z76,z582,z3,z4,z6]),(0,[z43,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1090,z6])],[(0,[z7,z1,z33,z4,z371,z6]),(0,[z7,z1,z2,z1091,z3,z6]),(0,[z7,z1,z24,z49,z4,z6])],[(0,[z7,z1,z2,z3,z338,z321])],[(0,[z9,z311,z45,z3,z4,z6]),(0,[z7,z1,z33,z14,z61,z6])]],
   [[(0,[z7,z1092,z2,z3,z4,z6]),(0,[z7,z1,z2,z1093,z4,z6]),(0,[z239,z374,z7,z3,z61,z6])],[(0,[z0,z171,z2,z3,z4,z288]),(0,[z7,z1,z215,z33,z4,z6])],[(0,[z159,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z4,z1094]),(0,[z1095,z1,z2,z3,z4,z6])],[(0,[z115,z1,z27,z3,z61,z6]),(0,[z7,z225,z2,z401,z4,z6]),(0,[z7,z1096,z2,z3,z4,z6])],[(0,[z7,z1,z3,z460,z61,z6]),(0,[z7,z1,z2,z3,z4,z811])],[(1,[z1,z718,z3,z4,z6]),(0,[z39,z7,z2,z10,z296,z6]),(0,[z7,z1,z33,z334,z61,z6])],[(0,[z415,z2,z27,z3,z4,z6]),(0,[z7,z2,z10,z4,z6,z380]),(0,[z7,z1,z2,z3,z1097,z6])],[(0,[z7,z1,z2,z759,z4,z6]),(0,[z7,z1,z3,z194,z14,z6]),(0,[z7,z1,z2,z1098,z4,z6])],[(0,[z7,z1099,z2,z3,z4,z6]),(0,[z1100,z7,z2,z3,z4,z6]),(0,[z7,z1,z691,z3,z61,z6]),(0,[z374,z7,z3,z33,z61,z6]),(0,[z7,z1,z2,z3,z1004,z6])],[(0,[z7,z225,z2,z207,z61,z6])],[(0,[z1101,z7,z2,z3,z4,z6]),(0,[z1102,z1,z2,z3,z4,z6])],[(0,[z7,z1,z137,z3,z14,z6])],[(0,[z1103,z1,z2,z3,z4,z6])],[(0,[z1104,z7,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z6,z1105]),(0,[z7,z1,z2,z3,z1106,z6]),(0,[z7,z1,z2,z1107,z4,z6]),(0,[z7,z1,z2,z215,z34,z6])],[(0,[z7,z1,z2,z3,z1108,z6]),(0,[z7,z1,z2,z33,z14,z6]),(0,[z7,z2,z10,z136,z61,z6])],[(0,[z7,z1,z2,z3,z1109,z6]),(0,[z7,z1,z2,z3,z1110,z6])]],
   [[(0,[z109,z1,z2,z143,z4,z6]),(0,[z7,z2,z3,z968,z4,z6])],[(0,[z7,z1,z2,z3,z4,z140]),(0,[z111,z1,z2,z3,z134,z6]),(0,[z7,z1,z2,z3,z1111,z6]),(0,[z7,z1,z2,z208,z388,z6]),(1,[z7,z1,z2,z804,z6])],[(0,[z7,z1,z188,z33,z61,z6]),(0,[z7,z1,z2,z1112,z4,z6])],[(0,[z493,z44,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z930,z6]),(0,[z557,z7,z1,z33,z61,z6]),(0,[z7,z767,z2,z3,z61,z6]),(0,[z768,z7,z2,z3,z61,z6]),(0,[z7,z1,z2,z1113,z4,z6])],[(0,[z7,z773,z2,z3,z61,z6])],[(0,[z239,z7,z1,z187,z61,z6])],[(0,[z7,z1,z561,z33,z4,z6]),(0,[z7,z1,z319,z33,z4,z6]),(0,[z241,z7,z1,z33,z4,z6]),(0,[z835,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1046,z6]),(0,[z7,z169,z2,z3,z276,z6])],[(0,[z7,z156,z2,z10,z4,z6]),(0,[z109,z1,z2,z165,z4,z6]),(0,[z7,z1,z2,z3,z885,z61])],[(0,[z7,z1114,z2,z3,z4,z6]),(0,[z7,z1,z2,z349,z33,z6]),(0,[z264,z7,z1,z3,z61,z6]),(0,[z7,z1,z2,z3,z1115,z6]),(0,[z7,z1,z2,z1116,z4,z6])],[(0,[z354,z2,z3,z129,z4,z6])],[(0,[z964,z7,z2,z3,z4,z6]),(0,[z7,z172,z2,z10,z4,z6]),(0,[z7,z1,z2,z1117,z4,z6])],[(0,[z1034,z7,z2,z3,z4,z6])],[(0,[z38,z1,z2,z3,z70,z6]),(0,[z85,z1,z2,z3,z61,z6])],[(0,[z7,z1,z2,z179,z3,z6]),(0,[z7,z2,z3,z703,z4,z18]),(0,[z43,z7,z2,z3,z62,z235])],[(0,[z7,z1,z2,z3,z14,z321])],[(0,[z7,z2,z3,z1118,z4,z6]),(0,[z7,z1,z2,z3,z1119,z6]),(0,[z7,z530,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z717,z6])]],
   [[(0,[z311,z1,z2,z3,z61,z6])],[(0,[z374,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1120,z6]),(0,[z7,z103,z2,z3,z61,z6]),(0,[z7,z1,z114,z3,z61,z6]),(0,[z7,z1,z2,z3,z1004,z4])],[(0,[z7,z1,z561,z3,z14,z6])],[(0,[z171,z748,z2,z3,z4,z6]),(0,[z7,z1,z244,z10,z4,z13]),(0,[z7,z1,z2,z49,z14,z6]),(0,[z7,z218,z2,z3,z276,z6])],[(0,[z7,z1,z55,z10,z14,z6])],[(0,[z252,z44,z2,z3,z4,z6]),(0,[z29,z484,z2,z3,z4,z6]),(0,[z7,z1,z2,z393,z538,z6]),(0,[z7,z1,z2,z33,z538,z6]),(0,[z7,z1,z2,z133,z14,z6]),(0,[z7,z1,z2,z3,z290,z6])],[],[(0,[z7,z1,z2,z3,z1121,z6]),(1,[z1,z2,z3,z816,z6]),(0,[z7,z1,z2,z1122,z14,z6])],[(0,[z7,z1,z2,z1123,z4,z6]),(0,[z7,z1,z2,z3,z1124,z6]),(0,[z1125,z1,z2,z3,z4,z6]),(0,[z7,z1126,z2,z33,z4,z6]),(0,[z1127,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1128,z6]),(0,[z7,z1,z2,z1129,z4,z6])],[(0,[z7,z116,z2,z3,z8,z6]),(0,[z7,z2,z3,z4,z6,z1130]),(0,[z7,z724,z2,z3,z4,z6]),(0,[z7,z1,z244,z3,z4,z811])],[(0,[z77,z7,z103,z2,z4,z202])],[(0,[z7,z1,z24,z3,z4,z6]),(0,[z7,z1,z33,z61,z13,z6]),(0,[z7,z1,z33,z61,z6,z93]),(0,[z7,z1,z33,z62,z61,z6]),(0,[z7,z530,z2,z3,z14,z6])],[(0,[z7,z1131,z2,z3,z4,z6]),(0,[z7,z1,z2,z390,z4,z350]),(0,[z1132,z1,z2,z3,z4,z6])],[(0,[z343,z7,z2,z3,z61,z6]),(0,[z7,z2,z830,z23,z4,z6]),(0,[z7,z1,z2,z25,z329,z6])],[(0,[z7,z1,z2,z153,z61,z6])],[(0,[z7,z1,z2,z1133,z4,z6])]],
   [[(0,[z7,z1,z167,z10,z4,z6]),(0,[z7,z1,z2,z210,z235,z6])],[(0,[z7,z484,z2,z3,z289,z6]),(0,[z7,z1134,z2,z3,z4,z6]),(0,[z7,z1,z2,z151,z10,z6]),(0,[z7,z1,z2,z3,z338,z6]),(0,[z7,z2,z3,z4,z750,z6]),(0,[z7,z1,z2,z33,z305,z6])],[(0,[z30,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z455,z4,z350])],[(0,[z7,z1,z2,z3,z1135,z6])],[(0,[z0,z7,z2,z3,z4,z140]),(0,[z7,z1,z2,z3,z289,z6]),(0,[z404,z1,z2,z33,z4,z6])],[(0,[z7,z1,z2,z33,z162,z6])],[(0,[z7,z1,z2,z1136,z4,z6]),(0,[z531,z1,z2,z10,z4,z6]),(0,[z99,z7,z2,z10,z4,z12]),(0,[z7,z1,z33,z61,z12,z6])],[(0,[z7,z1,z2,z33,z506,z6]),(0,[z7,z1,z2,z1137,z4,z6]),(0,[z7,z1,z2,z1138,z4,z6]),(0,[z7,z1,z376,z33,z4,z6])],[(0,[z7,z1,z412,z3,z14,z6]),(0,[z7,z1,z2,z1139,z4,z6]),(0,[z77,z7,z1,z2,z14,z202])],[(0,[z7,z2,z3,z129,z521,z6])],[(0,[z7,z1,z2,z10,z4,z350]),(0,[z7,z1,z2,z33,z521,z6]),(0,[z7,z1,z2,z3,z255,z6]),(0,[z7,z1,z236,z33,z4,z6]),(0,[z7,z1,z56,z10,z61,z6])],[(0,[z7,z1140,z2,z3,z4,z6]),(0,[z7,z1,z375,z10,z4,z6])],[(0,[z7,z1,z2,z797,z4,z6]),(0,[z354,z2,z3,z23,z4,z6]),(0,[z7,z1,z33,z61,z6,z22])],[(0,[z20,z1,z2,z10,z4,z21]),(0,[z1141,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z930,z6])],[(0,[z7,z1,z2,z1142,z4,z6]),(0,[z7,z1143,z2,z3,z4,z6]),(0,[z7,z1,z2,z33,z276,z6]),(0,[z7,z1,z2,z41,z6,z232])],[(0,[z7,z1,z2,z3,z1144,z6]),(0,[z1,z2,z3,z4,z816,z6]),(0,[z7,z1,z196,z33,z4,z6]),(0,[z1145,z1,z2,z3,z4,z6])]],
   [[(0,[z7,z116,z2,z3,z4,z6]),(0,[z404,z1,z2,z3,z14,z6]),(0,[z1146,z1,z2,z3,z4,z6]),(0,[z7,z2,z3,z829,z61,z6])],[(0,[z7,z1,z2,z3,z1147,z6]),(0,[z7,z76,z40,z3,z521,z6]),(0,[z7,z1148,z2,z33,z4,z6]),(0,[z7,z1,z2,z257,z17,z6])],[(0,[z7,z1,z2,z1149,z3,z6]),(0,[z7,z484,z2,z33,z4,z6]),(0,[z7,z1,z137,z33,z4,z6])],[(0,[z7,z1,z2,z3,z4,z288]),(0,[z7,z1,z2,z10,z4,z220]),(0,[z254,z7,z1,z33,z61,z6])],[(0,[z7,z1,z2,z1150,z4,z6]),(0,[z404,z1,z2,z3,z4,z321]),(0,[z7,z1,z2,z10,z91,z93])],[(0,[z7,z1,z2,z3,z4,z1151]),(0,[z58,z1,z2,z35,z61,z6]),(0,[z7,z415,z2,z10,z4,z6])],[(0,[z0,z171,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z1152,z6]),(0,[z7,z1,z236,z3,z14,z6]),(0,[z7,z1,z2,z3,z1153,z6])],[(0,[z7,z1,z24,z3,z203,z6])],[(0,[z99,z7,z2,z3,z4,z573]),(0,[z7,z1,z2,z349,z3,z6]),(0,[z7,z1,z2,z3,z1154,z6])],[(0,[z347,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z1155]),(0,[z7,z1,z2,z3,z4,z1156]),(0,[z1,z2,z3,z4,z708,z21])],[(0,[z7,z1,z2,z1157,z4,z6]),(0,[z7,z1,z2,z409,z14,z6]),(0,[z7,z1,z2,z1158,z4,z6]),(0,[z7,z1,z23,z33,z61,z6])],[(0,[z7,z1,z515,z33,z4,z6]),(0,[z1159,z1,z2,z3,z4,z6])],[(0,[z1160,z7,z1,z3,z4,z6]),(0,[z7,z1,z2,z1161,z3,z6]),(0,[z20,z1,z2,z3,z4,z533]),(0,[z7,z2,z3,z4,z136,z6]),(0,[z7,z76,z40,z33,z4,z6]),(0,[z7,z1,z2,z191,z31,z6])],[(0,[z7,z1,z2,z1162,z4,z6]),(0,[z1163,z7,z2,z33,z4,z6]),(0,[z123,z1,z2,z285,z4,z6])],[(0,[z7,z484,z2,z3,z14,z6]),(0,[z9,z7,z726,z3,z4,z6]),(0,[z7,z1,z2,z1164,z3,z6]),(0,[z7,z1,z2,z10,z306,z6])],[(0,[z7,z1,z2,z3,z1165,z6]),(0,[z7,z1,z2,z3,z1166,z6]),(1,[z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z3,z1033,z6]),(0,[z63,z7,z169,z3,z4,z22])]],
   [[(0,[z7,z1,z2,z3,z1167,z6]),(0,[z109,z7,z1,z2,z349,z6]),(0,[z7,z1,z10,z33,z61,z6]),(0,[z7,z1,z2,z3,z84,z93])],[(0,[z7,z1,z2,z393,z14,z6]),(0,[z9,z7,z45,z3,z61,z6])],[(0,[z0,z171,z2,z3,z14,z6]),(0,[z7,z1,z2,z1168,z4,z6]),(0,[z7,z1,z33,z578,z4,z6])],[(0,[z1,z188,z718,z3,z4,z6]),(0,[z66,z7,z2,z23,z4,z6]),(0,[z7,z1,z367,z33,z61,z6])],[(0,[z115,z1,z27,z3,z289,z6]),(0,[z130,z1,z2,z3,z4,z6]),(0,[z7,z2,z3,z129,z4,z321]),(0,[z7,z1,z236,z3,z227,z6]),(0,[z77,z7,z1,z2,z4,z865]),(0,[z7,z1,z2,z3,z1169,z6])],[(0,[z7,z1,z2,z1170,z4,z6]),(0,[z58,z7,z1,z33,z61,z6]),(0,[z7,z1,z2,z33,z4,z321])],[(0,[z39,z311,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1003,z6]),(0,[z7,z1,z2,z913,z4,z6]),(0,[z85,z169,z2,z3,z4,z6])],[(0,[z212,z7,z1,z33,z4,z6]),(0,[z1171,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z367,z227,z6]),(0,[z7,z1,z2,z3,z804,z6])],[(0,[z7,z1,z2,z3,z1172,z6]),(0,[z7,z614,z2,z33,z4,z6]),(0,[z42,z7,z2,z10,z4,z6]),(0,[z1066,z7,z1,z2,z3,z4]),(0,[z7,z76,z40,z3,z14,z6]),(0,[z7,z1,z2,z1173,z4,z6]),(0,[z7,z2,z33,z1118,z4,z6]),(0,[z7,z1,z33,z136,z61,z6]),(0,[z7,z1,z33,z235,z61,z6]),(0,[z239,z7,z3,z136,z61,z6]),(0,[z7,z1,z2,z711,z14,z6])],[(0,[z7,z1,z2,z1174,z3,z6]),(0,[z7,z1,z2,z152,z14,z6]),(0,[z374,z7,z2,z198,z3,z6]),(0,[z7,z1,z595,z3,z61,z6])],[(0,[z7,z1,z2,z33,z879,z4])],[(0,[z7,z1,z2,z1175,z4,z6]),(0,[z7,z1,z2,z3,z1176,z6]),(0,[z7,z1,z2,z1177,z4,z6]),(0,[z7,z1,z2,z179,z10,z6]),(1,[z7,z1,z3,z741,z6]),(0,[z63,z7,z1,z3,z4,z811]),(0,[z43,z7,z2,z25,z3,z6])],[(0,[z44,z2,z170,z3,z4,z6]),(0,[z7,z1,z2,z1178,z4,z6]),(0,[z7,z1,z2,z1179,z4,z6]),(0,[z7,z1,z2,z133,z4,z6]),(0,[z7,z1,z2,z1180,z3,z6]),(0,[z98,z7,z1,z236,z3,z6]),(0,[z7,z1,z55,z330,z14,z6])],[(0,[z354,z1,z2,z3,z4,z6])],[(0,[z7,z1,z96,z33,z4,z6])],[]],
   [[(0,[z115,z116,z27,z3,z4,z6]),(0,[z7,z169,z2,z3,z4,z6]),(0,[z7,z1,z33,z61,z6,z202]),(0,[z7,z1,z128,z33,z61,z6])],[(0,[z549,z7,z2,z3,z4,z18]),(0,[z7,z1,z903,z33,z4,z6]),(0,[z7,z1,z2,z91,z92,z93])],[(0,[z1181,z7,z2,z3,z4,z6]),(0,[z311,z1,z2,z3,z290,z6]),(0,[z7,z1,z45,z33,z61,z6]),(0,[z43,z7,z2,z128,z3,z6])],[(0,[z1182,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z1183,z4,z6]),(0,[z85,z218,z2,z3,z4,z6]),(0,[z7,z1,z2,z299,z41,z6])],[(0,[z7,z614,z2,z3,z14,z6]),(0,[z7,z1,z401,z33,z61,z6])],[(0,[z7,z2,z3,z4,z6,z1184])],[(0,[z58,z7,z1,z2,z349,z6])],[(0,[z7,z1,z2,z1185,z3,z6]),(0,[z7,z2,z3,z14,z136,z6])],[(0,[z7,z2,z3,z4,z6,z380]),(0,[z7,z1,z2,z3,z538,z6]),(0,[z7,z1,z2,z208,z34,z6])],[(0,[z7,z1,z2,z4,z6,z1186]),(0,[z7,z1,z1187,z3,z4,z6]),(0,[z83,z7,z2,z830,z4,z6]),(0,[z7,z1,z244,z413,z4,z13])],[(0,[z7,z1,z2,z3,z1188,z6]),(0,[z7,z1,z2,z3,z1189,z6])],[(0,[z7,z1,z2,z1190,z3,z6]),(0,[z9,z404,z45,z3,z4,z6]),(0,[z7,z1126,z2,z3,z4,z6]),(0,[z77,z7,z530,z2,z4,z202])],[],[(0,[z30,z415,z2,z3,z4,z5]),(0,[z7,z218,z2,z3,z4,z6]),(0,[z7,z1,z2,z267,z4,z277]),(0,[z7,z1,z2,z3,z1191,z6])],[(0,[z311,z1,z2,z3,z338,z6]),(0,[z7,z1,z2,z1089,z3,z6]),(0,[z7,z1,z2,z3,z1192,z6])],[(0,[z7,z1,z44,z33,z61,z6]),(0,[z7,z1,z412,z33,z4,z6])]],
   [[(0,[z7,z1,z2,z201,z4,z209])],[(0,[z7,z1,z2,z3,z1193,z6]),(0,[z7,z2,z3,z4,z300,z18])],[(0,[z564,z7,z1,z33,z61,z6])],[(0,[z7,z44,z2,z179,z3,z6]),(0,[z1194,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z1195,z10,z6]),(0,[z7,z1,z2,z3,z1004,z93])],[(0,[z7,z1,z2,z1196,z4,z6]),(0,[z109,z1,z2,z205,z61,z6]),(0,[z7,z1,z2,z1197,z4,z6]),(0,[z7,z1,z2,z3,z305,z6]),(0,[z7,z1,z2,z3,z735,z4])],[(0,[z0,z354,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z12,z140]),(0,[z484,z2,z27,z3,z4,z6]),(0,[z7,z1,z377,z3,z4,z13]),(0,[z39,z7,z2,z3,z634,z6]),(0,[z351,z7,z1,z3,z61,z6]),(0,[z7,z1,z2,z363,z4,z277])],[(0,[z574,z7,z2,z23,z4,z6]),(0,[z7,z156,z2,z3,z61,z6]),(0,[z7,z1,z694,z10,z4,z6]),(0,[z886,z7,z2,z3,z61,z6]),(0,[z7,z1,z128,z236,z4,z6]),(0,[z7,z1,z1198,z3,z4,z6])],[(0,[z7,z1,z2,z1199,z4,z6]),(0,[z7,z954,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z380,z22]),(0,[z7,z1,z55,z33,z61,z6]),(0,[z85,z1,z2,z3,z276,z6])],[(0,[z7,z1,z2,z1200,z4,z6]),(0,[z7,z1,z2,z3,z162,z6]),(0,[z7,z1,z2,z1195,z3,z6]),(0,[z7,z1,z2,z1201,z4,z6]),(0,[z1,z2,z3,z61,z882,z6])],[(0,[z7,z172,z2,z3,z61,z6]),(0,[z7,z1,z507,z33,z4,z6]),(0,[z1202,z1,z2,z33,z4,z6]),(1,[z7,z1,z236,z34,z6])],[(0,[z7,z1,z2,z3,z506,z6]),(0,[z7,z1,z2,z1203,z3,z6]),(0,[z29,z1,z188,z3,z538,z6]),(0,[z7,z1,z2,z393,z506,z6]),(0,[z1,z2,z3,z752,z4,z6]),(0,[z7,z1,z2,z1204,z4,z6]),(0,[z7,z2,z3,z4,z6,z974])],[(0,[z7,z1,z2,z1205,z3,z6]),(1,[z7,z33,z136,z61,z6]),(0,[z7,z1,z2,z1206,z3,z6]),(0,[z7,z1,z236,z3,z41,z6])],[(0,[z1207,z1,z2,z3,z4,z6]),(0,[z7,z2,z719,z10,z4,z6])],[(0,[z7,z76,z2,z3,z4,z140]),(0,[z1208,z1,z2,z3,z4,z6]),(0,[z7,z1,z33,z61,z6,z48])],[(0,[z7,z1,z2,z1209,z4,z6]),(0,[z85,z1,z2,z33,z4,z6]),(0,[z7,z1,z2,z367,z41,z6])],[(0,[z7,z1,z2,z1210,z4,z6]),(0,[z7,z1,z2,z3,z4,z1211]),(0,[z7,z1,z2,z125,z227,z6])]],
   [[(0,[z30,z2,z3,z4,z5,z380]),(0,[z30,z7,z2,z3,z4,z380]),(0,[z374,z7,z2,z25,z3,z6]),(0,[z7,z1,z2,z1212,z4,z6])],[(0,[z197,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z1213]),(0,[z112,z7,z2,z10,z4,z18]),(0,[z1057,z7,z2,z33,z4,z6]),(0,[z7,z1,z2,z3,z276,z6])],[(0,[z109,z7,z1,z33,z61,z6]),(0,[z688,z7,z45,z3,z4,z6]),(0,[z7,z1,z244,z3,z61,z13])],[(0,[z7,z1,z55,z903,z4,z6]),(0,[z7,z103,z2,z33,z4,z6]),(0,[z7,z1,z2,z274,z34,z6]),(0,[z7,z852,z2,z3,z4,z6]),(0,[z7,z1,z55,z3,z741,z6])],[],[(0,[z7,z1,z2,z152,z521,z6]),(0,[z7,z2,z33,z4,z136,z6])],[(0,[z7,z1,z2,z104,z4,z220]),(0,[z7,z1,z2,z1214,z4,z6]),(0,[z7,z1,z2,z349,z10,z6])],[(0,[z20,z1,z2,z3,z4,z392]),(0,[z7,z1215,z2,z3,z4,z6]),(0,[z1216,z7,z1,z2,z33,z4]),(0,[z7,z1,z236,z4,z209,z6])],[(0,[z7,z1,z2,z33,z4,z6]),(0,[z598,z44,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z1217,z6]),(0,[z58,z1,z2,z349,z35,z6])],[(0,[z0,z171,z2,z3,z4,z6]),(0,[z7,z1,z2,z1218,z3,z6])],[(0,[z7,z1,z1219,z3,z4,z6]),(0,[z415,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z47,z33,z6]),(0,[z85,z1,z2,z3,z14,z6])],[(0,[z7,z2,z3,z4,z6,z1220]),(0,[z99,z531,z2,z3,z4,z12]),(0,[z7,z1,z2,z1221,z4,z6])],[(0,[z29,z1,z188,z3,z506,z6]),(0,[z7,z1,z2,z10,z17,z6])],[],[(0,[z7,z1222,z2,z3,z4,z6]),(0,[z7,z1,z2,z390,z61,z6]),(0,[z7,z1,z2,z1223,z4,z6]),(0,[z83,z7,z2,z179,z23,z6])],[(0,[z159,z44,z2,z10,z4,z6]),(0,[z7,z1,z167,z3,z61,z6]),(0,[z7,z1,z2,z1224,z4,z6]),(0,[z7,z76,z40,z3,z4,z6]),(0,[z7,z103,z2,z3,z14,z6])]],
   [[(0,[z123,z1,z2,z205,z4,z6]),(0,[z7,z1,z33,z661,z61,z6]),(0,[z1163,z7,z2,z3,z4,z6]),(0,[z788,z7,z2,z3,z14,z6]),(0,[z7,z1,z2,z3,z1225,z6])],[(0,[z7,z1226,z2,z3,z4,z6]),(0,[z39,z354,z2,z3,z4,z6]),(0,[z7,z1,z2,z427,z17,z6]),(0,[z7,z1,z236,z3,z34,z6])],[(0,[z7,z1,z2,z1227,z3,z6]),(0,[z7,z1228,z2,z3,z4,z6]),(0,[z38,z1,z2,z10,z70,z6]),(0,[z63,z7,z1,z257,z4,z22])],[(0,[z39,z7,z2,z3,z4,z140]),(0,[z7,z1,z2,z448,z4,z220]),(0,[z7,z1,z2,z10,z4,z471]),(0,[z9,z7,z45,z3,z290,z6])],[(0,[z7,z1,z2,z3,z14,z6]),(0,[z7,z1,z2,z257,z61,z6])],[(0,[z531,z1,z2,z3,z61,z6]),(0,[z99,z7,z2,z3,z61,z12])],[(0,[z7,z1,z2,z3,z4,z1229]),(0,[z7,z1,z2,z3,z1230,z6]),(0,[z7,z1,z2,z3,z1231,z6]),(0,[z7,z1,z2,z1232,z4,z6]),(0,[z7,z1,z3,z854,z4,z6]),(0,[z7,z1,z2,z1233,z4,z6])],[(0,[z7,z76,z40,z152,z4,z6]),(0,[z1234,z1,z2,z3,z4,z6]),(0,[z7,z362,z1,z33,z61,z6]),(0,[z7,z1,z2,z267,z4,z865])],[(0,[z109,z7,z1,z236,z4,z6]),(0,[z7,z1,z2,z3,z4,z321]),(0,[z7,z1,z2,z33,z183,z6])],[(0,[z7,z1,z2,z3,z1235,z6]),(0,[z7,z1,z2,z3,z61,z350])],[(0,[z7,z1236,z2,z3,z4,z6]),(0,[z29,z1,z188,z393,z4,z6]),(0,[z29,z1,z188,z33,z4,z6]),(0,[z254,z7,z1,z33,z255,z6]),(0,[z63,z7,z1,z10,z4,z22]),(0,[z7,z1,z375,z3,z61,z6])],[(0,[z7,z1,z2,z33,z199,z6])],[(1,[z748,z2,z3,z4,z6]),(0,[z525,z1,z2,z35,z4,z6]),(0,[z7,z1,z2,z1237,z4,z6]),(0,[z20,z1,z2,z3,z61,z21]),(0,[z7,z1,z2,z10,z61,z6]),(0,[z7,z1,z201,z33,z61,z6]),(0,[z7,z1,z3,z203,z61,z6]),(0,[z7,z1,z56,z854,z4,z6]),(0,[z7,z1,z2,z61,z6,z1021]),(0,[z7,z1,z2,z153,z14,z6])],[(0,[z1,z2,z759,z35,z4,z6]),(0,[z7,z1,z207,z33,z61,z6]),(0,[z7,z1,z2,z49,z4,z6]),(0,[z7,z1,z2,z3,z1238,z6]),(0,[z7,z1,z2,z3,z879,z4])],[(0,[z7,z1,z198,z33,z61,z6]),(0,[z339,z1,z2,z3,z100,z6])],[(0,[z7,z1,z2,z1239,z4,z6]),(0,[z748,z1,z2,z3,z4,z6]),(0,[z9,z7,z45,z3,z338,z6]),(0,[z1240,z1,z2,z3,z4,z6]),(0,[z7,z1,z3,z385,z61,z6]),(0,[z7,z1,z2,z274,z15,z6]),(0,[z63,z7,z1,z427,z4,z22])]],
   [[(0,[z7,z1,z2,z448,z4,z471]),(0,[z38,z1,z2,z331,z3,z6]),(0,[z7,z1,z2,z3,z1241,z6])],[(0,[z7,z1,z2,z1242,z4,z6]),(0,[z20,z415,z2,z3,z4,z6]),(0,[z311,z2,z45,z3,z4,z6]),(0,[z7,z1,z33,z100,z61,z6]),(0,[z7,z1,z2,z1122,z4,z6])],[(0,[z7,z1,z2,z3,z61,z220]),(0,[z7,z1,z2,z128,z280,z6]),(0,[z7,z1,z2,z3,z1243,z6]),(0,[z7,z1,z3,z741,z61,z6])],[(0,[z29,z1,z718,z3,z4,z6]),(0,[z7,z362,z2,z401,z4,z6]),(0,[z7,z1,z2,z1244,z4,z6])],[(0,[z7,z1,z2,z1245,z4,z6]),(0,[z7,z415,z2,z3,z61,z6]),(0,[z7,z1,z2,z33,z203,z6])],[(0,[z115,z484,z27,z3,z4,z6]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z20,z7,z1,z33,z61,z6]),(0,[z7,z530,z2,z3,z4,z6]),(0,[z7,z1,z2,z1185,z10,z6]),(0,[z7,z2,z3,z892,z61,z6])],[(0,[z7,z1,z2,z3,z4,z1246]),(0,[z0,z2,z3,z4,z550,z6]),(0,[z7,z1,z2,z3,z1247,z6]),(0,[z29,z1,z188,z3,z14,z6]),(0,[z7,z1,z3,z14,z224,z6]),(0,[z7,z1,z1248,z3,z4,z6]),(0,[z7,z1,z2,z125,z41,z6]),(0,[z7,z1,z2,z1249,z4,z6])],[(0,[z7,z1,z2,z1250,z4,z6])],[(0,[z115,z1,z27,z33,z4,z6]),(0,[z30,z1,z2,z10,z4,z5]),(0,[z239,z7,z1,z33,z61,z6]),(0,[z339,z7,z1,z33,z61,z6]),(0,[z7,z1,z56,z10,z14,z6])],[(0,[z7,z1,z2,z448,z61,z6]),(0,[z7,z1251,z2,z3,z4,z6]),(0,[z501,z7,z2,z10,z4,z6]),(0,[z406,z1,z2,z3,z4,z5]),(0,[z39,z7,z1,z236,z3,z6]),(0,[z7,z1,z2,z1252,z4,z6])],[(0,[z1253,z7,z2,z3,z4,z6]),(0,[z564,z1,z2,z3,z113,z6]),(0,[z7,z1,z2,z210,z14,z6])],[(0,[z7,z1,z2,z3,z1254,z6]),(0,[z7,z1,z2,z3,z1255,z6])],[(0,[z7,z1,z464,z10,z4,z6])],[(0,[z7,z1,z2,z3,z4,z1256]),(0,[z1257,z1,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z1258,z6]),(0,[z1,z2,z3,z759,z4,z6]),(0,[z58,z7,z1,z236,z4,z6]),(0,[z343,z38,z2,z3,z70,z6]),(0,[z7,z1,z2,z3,z4,z708])],[(0,[z7,z1,z1259,z3,z4,z6]),(0,[z7,z1,z1260,z3,z4,z6])]],
   [[],[(0,[z7,z484,z2,z3,z8,z6]),(0,[z7,z905,z2,z3,z4,z6]),(0,[z7,z1,z33,z134,z61,z6]),(0,[z7,z1,z55,z460,z4,z6])],[(0,[z77,z7,z1,z2,z4,z202])],[(0,[z7,z1,z33,z70,z61,z6]),(0,[z9,z7,z45,z33,z4,z6]),(0,[z7,z2,z3,z136,z61,z6]),(0,[z7,z2,z3,z312,z61,z6]),(1,[z7,z1,z3,z4,z811])],[(0,[z7,z1,z2,z33,z8,z6]),(0,[z115,z1,z27,z3,z14,z6]),(0,[z7,z1,z33,z4,z642,z6]),(0,[z7,z1,z267,z33,z61,z6]),(0,[z7,z1,z2,z33,z275,z6]),(0,[z239,z7,z1,z3,z741,z6]),(0,[z7,z1,z198,z236,z4,z6])],[(0,[z7,z1,z40,z33,z61,z6]),(0,[z467,z7,z1,z33,z4,z6]),(0,[z43,z7,z2,z10,z4,z6]),(0,[z7,z1,z3,z61,z6,z258]),(0,[z7,z1,z2,z3,z235,z526])],[(0,[z7,z1,z3,z127,z61,z6]),(0,[z7,z1,z33,z84,z61,z6])],[(0,[z1216,z7,z1,z2,z3,z4]),(0,[z42,z7,z2,z3,z61,z6]),(0,[z63,z7,z218,z3,z4,z22])],[],[(0,[z7,z1,z2,z1261,z4,z6]),(0,[z20,z1,z2,z3,z4,z504]),(0,[z7,z1,z2,z1206,z10,z6]),(0,[z7,z982,z2,z3,z61,z6])],[(0,[z404,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z47,z3,z6]),(0,[z7,z225,z2,z207,z14,z6]),(0,[z531,z1,z2,z3,z4,z12]),(0,[z7,z1,z33,z194,z4,z6])],[],[(0,[z7,z1,z2,z3,z4,z1262]),(0,[z1202,z1,z2,z3,z4,z6]),(0,[z7,z1,z33,z105,z61,z6]),(0,[z7,z1,z2,z1263,z4,z6])],[(0,[z668,z7,z2,z3,z4,z12]),(0,[z7,z1,z2,z3,z1264,z6]),(0,[z613,z7,z1,z2,z25,z6])],[(0,[z7,z1,z2,z1265,z4,z6]),(0,[z7,z1266,z2,z3,z4,z6])],[(0,[z9,z7,z45,z3,z14,z6]),(0,[z39,z7,z2,z3,z930,z6]),(0,[z7,z1,z2,z10,z1097,z6])]],
   [[(0,[z7,z1,z2,z3,z521,z6]),(0,[z1267,z1,z2,z3,z4,z6]),(0,[z7,z1,z33,z61,z61,z6]),(0,[z7,z1,z236,z3,z4,z6])],[(0,[z354,z2,z3,z4,z12,z6]),(0,[z99,z354,z2,z3,z4,z12]),(0,[z7,z1,z236,z4,z34,z6])],[(0,[z130,z1,z2,z257,z4,z6])],[(0,[z9,z7,z45,z3,z4,z321]),(0,[z7,z1,z1268,z3,z4,z6])],[(0,[z7,z1,z2,z409,z4,z6]),(0,[z7,z1,z33,z4,z224,z6]),(0,[z311,z2,z3,z129,z4,z6]),(0,[z7,z40,z3,z4,z371,z6]),(0,[z1057,z7,z2,z3,z4,z6]),(0,[z7,z1,z2,z25,z474,z6])],[(0,[z7,z1,z2,z3,z4,z1269]),(0,[z7,z1,z2,z3,z1270,z6]),(0,[z311,z1,z2,z33,z4,z6]),(0,[z1271,z1,z2,z3,z4,z6])],[(1,[z1,z2,z759,z4,z6]),(0,[z7,z2,z3,z14,z6,z380]),(0,[z7,z1,z2,z3,z1272,z6]),(0,[z39,z7,z2,z33,z296,z6])],[(0,[z7,z1273,z2,z3,z4,z6]),(0,[z7,z1148,z2,z3,z4,z6])],[(0,[z7,z484,z2,z3,z4,z6])],[(0,[z7,z1,z2,z3,z4,z1274]),(0,[z7,z1,z2,z3,z1275,z6]),(0,[z354,z76,z2,z3,z4,z6])],[(0,[z7,z1,z2,z10,z4,z140]),(0,[z491,z1,z2,z3,z4,z21]),(0,[z111,z1,z2,z10,z134,z6]),(0,[z7,z1,z3,z1003,z61,z6]),(0,[z130,z1,z2,z10,z4,z6]),(0,[z374,z7,z2,z128,z3,z6])],[(0,[z7,z1,z2,z3,z4,z6]),(0,[z598,z7,z2,z3,z4,z18]),(0,[z7,z1,z2,z393,z4,z6]),(0,[z7,z2,z3,z1276,z4,z6]),(0,[z1277,z1,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z858,z6]),(0,[z7,z1,z56,z10,z305,z6]),(0,[z7,z1,z2,z856,z14,z6])],[(0,[z58,z1,z2,z759,z4,z6]),(0,[z7,z1,z2,z267,z61,z209])],[(0,[z7,z1,z2,z1278,z3,z6])],[(0,[z7,z169,z2,z257,z4,z6])],[(0,[z7,z1,z2,z3,z4,z1279])]]]

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
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1001).take 407) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1408)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [502, 499, 407] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 231).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 344).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 460).take 52).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 114, 113, 116, 52] = true :=
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

end PEqualNP.Outside.L_meta_38761

theorem PEqualNP.Outside.L_meta_38761 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38761.solve