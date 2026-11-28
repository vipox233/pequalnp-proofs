import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39819

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
  Nat.testBit (4008372970 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000004105030b0b5#64 ++ 0xff913cf1f471f1ff#64 : BitVec 128),
   (0x90465146c186565c#64 ++ 0xffeed34ecb8e7e7c#64 : BitVec 128),
   (0x2030a28b0c0b0b0a#64 ++ 0xebf0e38f0c0f8f8f#64 : BitVec 128),
   (0xc0bb03f00ed00de0#64 ++ 0xdcbf03f00ff00ff0#64 : BitVec 128),
   (0x013dfc000f6de000#64 ++ 0xbd3ffc000ffff000#64 : BitVec 128),
   (0x023ffbeda0000000#64 ++ 0x7a7ffffff0000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x000004105030b0b5 0xff913cf1f471f1ff

def z1 : W := mkw 0x013dfc000f6de000 0xbd3ffc000ffff000

def z2 : W := mkw 0x023ffbeda0000000 0x7a7ffffff0000000

def z3 : W := mkw 0x2030a28b0c0b0b0a 0xebf0e38f0c0f8f8f

def z4 : W := mkw 0x90465146c186565c 0xffeed34ecb8e7e7c

def z5 : W := mkw 0xc0bb03f00ed00de0 0xdcbf03f00ff00ff0

def z6 : W := mkw 0x000004105030b0b5 0x14011c70f0707070

def z7 : W := mkw 0x2030a28b0c0b0b0a 0x0060c30e080e0e00

def z8 : W := mkw 0x010d5c000364e000 0xbd1f3c0007f1f000

def z9 : W := mkw 0x904000024186565c 0x858000000b8e7e7c

def z10 : W := mkw 0x9046514681864648 0x006ec30e0b8e0e00

def z11 : W := mkw 0x0339aea92e69a000 0x00112cb134718000

def z12 : W := mkw 0xb070a28b4d8f5f5e 0xeff0e38f0f8fffff

def z13 : W := mkw 0xc08203e000800d40 0x0000030000000e00

def z14 : W := mkw 0x023ffbeda0000000 0x006ec30e00000000

def z15 : W := mkw 0x023ffffdf030b0b5 0xfffffffff471f1ff

def z16 : W := mkw 0x0000000040001014 0xff801040c000707c

def z17 : W := mkw 0x90465556d1b6f6fd 0xffffffffffffffff

def z18 : W := mkw 0x02045804a0000000 0x00001c00f0000000

def z19 : W := mkw 0xc2bffbedaec00d40 0x006ec30e0b800e00

def z20 : W := mkw 0x0000000000000000 0x6a10208100000000

def z21 : W := mkw 0x0030a0000c090000 0xa930e0000c0f8000

def z22 : W := mkw 0xc08b03f002d00de0 0x548f03f003f00ff0

def z23 : W := mkw 0x0006514680020208 0xfbeed34ec80e0e0c

def z24 : W := mkw 0x917ff946cfcf565c 0xffeed34ecb8e7e7c

def z25 : W := mkw 0x917dfc024feff65c 0xbdbffc000ffffe7c

def z26 : W := mkw 0x00000010001000a0 0xdc9100f0047001f0

def z27 : W := mkw 0xc0bb07f05ef0bdf5 0xffbf3ff1fff1ffff

def z28 : W := mkw 0x0000000000000000 0xa920c000080e0000

def z29 : W := mkw 0x907f5146cfc6565c 0xffffd34ecffe7e7c

def z30 : W := mkw 0xc0bb03f05ed01df5 0xdebf03f1fff00fff

def z31 : W := mkw 0x2030a28b0c0b0b0a 0xfbf1fffffc0f8f8f

def z32 : W := mkw 0x020f5beda0000000 0x524f1ffff0000000

def z33 : W := mkw 0x2000028b00020b0a 0x42c0038f00000f8f

def z34 : W := mkw 0xd0c203f6c0921ffc 0x42c003fec0000ffc

def z35 : W := mkw 0xd0ff53f6cfd65ffc 0xffffd3fecffe7ffc

def z36 : W := mkw 0x0030a28900000000 0xebf0e38f0401818f

def z37 : W := mkw 0x2030a00b0c0b020a 0xab70e00f0c0f800f

def z38 : W := mkw 0x0000000000000000 0xeb9020810401818f

def z39 : W := mkw 0xc0bb03f00ed00de0 0xffbf23f10ff18fff

def z40 : W := mkw 0xc08b017002d004e0 0x140f007003f00070

def z41 : W := mkw 0x003ba3e900000000 0x7a7fe3ff00000000

def z42 : W := mkw 0x223ffffffc3bbbbf 0xfffffffffc7fffff

def z43 : W := mkw 0x000004005020b015 0x010000000001f00f

def z44 : W := mkw 0x9046514481844440 0x000e000003800000

def z45 : W := mkw 0x000004005020b015 0x00001c00f0007000

def z46 : W := mkw 0xc0bb03e00ec00d40 0x9c3f03000ff00e00

def z47 : W := mkw 0x90465156c19656fc 0xffffd3fecffe7ffc

def z48 : W := mkw 0x010004000f6de000 0x850000000ffff000

def z49 : W := mkw 0x033fffedaf6de000 0xff7ffffffffff000

def z50 : W := mkw 0x003900000e400000 0x9c3f00000ff00000

def z51 : W := mkw 0x2000000200020b0a 0x0080000000000f8f

def z52 : W := mkw 0x0002014480000000 0x4240034ec0000000

def z53 : W := mkw 0x020203eda0000000 0x424003fff0000000

def z54 : W := mkw 0xc0b900100ed00de0 0x9cbf00000ff00ff0

def z55 : W := mkw 0x0030a4105c39b0b5 0xffb1fcf1fc7ff1ff

def z56 : W := mkw 0x10445006c106521c 0xbf6ed00ecb8e700c

def z57 : W := mkw 0x927ffbefe186565c 0xfffffffffb8e7e7c

def z58 : W := mkw 0x0000000000000000 0x7a113cf1f0000000

def z59 : W := mkw 0x013dfc000f6de000 0x852ec0000ffff000

def z60 : W := mkw 0x033fffedae69a000 0x7a7ffffff4718000

def z61 : W := mkw 0x0006514480000000 0x7a6ed34ec0000000

def z62 : W := mkw 0x223ffbefac0b0b0a 0xfbfffffffc0f8f8f

def z63 : W := mkw 0x0000000000000000 0x581100f000000000

def z64 : W := mkw 0x90465146c186565c 0x146ed34ecb8e7e70

def z65 : W := mkw 0x000004101030a0a1 0x00112cb134718183

def z66 : W := mkw 0x0004500001044000 0xbd2ed0000b8e7000

def z67 : W := mkw 0x023babeda0000000 0x42512ffff0000000

def z68 : W := mkw 0x90420556d0b2b6fd 0xffd13ffff471ffff

def z69 : W := mkw 0xc18f5d7003f4e4e0 0x140f1c7003f07070

def z70 : W := mkw 0x003002800c000900 0xc8b003800c000f80

def z71 : W := mkw 0x020ff96da0000000 0x324ffc7ff0000000

def z72 : W := mkw 0x0000000000000000 0x00112cb130000000

def z73 : W := mkw 0xc0bb03e00ec00d40 0x002e03000b800e00

def z74 : W := mkw 0x010d5c000364e000 0x140f1c0003f07000

def z75 : W := mkw 0xc0bb03f00ed00de0 0x409103f004700ff0

def z76 : W := mkw 0x013dfc105f7df0b5 0xffbffcf1fffff1ff

def z77 : W := mkw 0xc1bffbf00fdd4de0 0xdcbfc3f00ffe0ff0

def z78 : W := mkw 0x213dfe8b0f6feb0a 0xbd7fff0e0ffffe00

def z79 : W := mkw 0x2030a2890c090902 0x0000000000000000

def z80 : W := mkw 0x2000a00b000b020a 0x0040c00e000e0000

def z81 : W := mkw 0x0000000000000000 0x38113c0000000000

def z82 : W := mkw 0x0104f800010d4000 0x0000c000000e0000

def z83 : W := mkw 0x0006514480000000 0x7a7ffffff0000000

def z84 : W := mkw 0x927ffbefe082165c 0x7afffffff0000e7c

def z85 : W := mkw 0x000004005020b015 0xbf113c01f471f00f

def z86 : W := mkw 0x0204f80da0000000 0x2240fc0ff0000000

def z87 : W := mkw 0x90465144c1845454 0xbd2ed040cb8e7070

def z88 : W := mkw 0x0139ac000e69a000 0x00112c0004718000

def z89 : W := mkw 0x917ffd46cfeff65c 0xffffff4ecffffe7c

def z90 : W := mkw 0x000004005020b015 0xeb903c81f401f18f

def z91 : W := mkw 0x813ffd400fede440 0xfdbfff400ffffe70

def z92 : W := mkw 0x003d50000f444000 0xbd3fd0000ffe7000

def z93 : W := mkw 0x2000a00b000b020a 0xebe0e30f080f8e0f

def z94 : W := mkw 0x020f5d74f030b0b5 0x140f1c70f0707070

def z95 : W := mkw 0xc08b017002d004e0 0xdc9f00f007f001f0

def z96 : W := mkw 0xc08203f000900de0 0x408003f000000ff0

def z97 : W := mkw 0x000000000e400000 0x840000000ff00000

def z98 : W := mkw 0x213dfe8b0f6feb0a 0xffffff8f0fffff8f

def z99 : W := mkw 0xd1fffff6cffffffc 0xfffffffecffffffc

def z100 : W := mkw 0x000004101030a0a1 0xbd113cb13471f183

def z101 : W := mkw 0xe2bffbffaedb0fea 0xffffffffffff8fff

def z102 : W := mkw 0x8002014000800440 0xdcae03400b800e70

def z103 : W := mkw 0xe0bba3fb0edb0fea 0xffffe3ff0fff8fff

def z104 : W := mkw 0x0234fa8da0000000 0x6a70ff8ff0000000

def z105 : W := mkw 0x0139ac000e69a000 0xbd113c000471f000

def z106 : W := mkw 0xc1bffbe00fcd4d40 0x002ec3000b8e0e00

def z107 : W := mkw 0xe0bba3f90ed90de2 0xdcbf23f10ff18ff3

def z108 : W := mkw 0x10445006c106521c 0x2340d00ec00e700c

def z109 : W := mkw 0x00000010501010b5 0x428000f1f00001ff

def z110 : W := mkw 0x000004000020a000 0xbd113c000471f000

def z111 : W := mkw 0x2000a00b000b020a 0x2340e00f000f800f

def z112 : W := mkw 0x40b902b00e5009a0 0x001100b004700180

def z113 : W := mkw 0xc0bb03f00ed00de0 0x84ae03000ff00ff0

def z114 : W := mkw 0x90465146c082165c 0x7aeed34ec0000e7c

def z115 : W := mkw 0x3044f00fc10f521e 0x2340f00fc00ff00f

def z116 : W := mkw 0x0030a0000c090000 0xebb0e0810c0f818f

def z117 : W := mkw 0x0000000000000000 0x9c2e00000b800000

def z118 : W := mkw 0xc0bba3f90ed00de0 0xfeffe3ff0ff00ff0

def z119 : W := mkw 0x408000100e5009a0 0x0000000004700180

def z120 : W := mkw 0xb046f14fc18f565e 0xffeef34fcb8ffe7f

def z121 : W := mkw 0x0000000040001014 0x42800040c000007c

def z122 : W := mkw 0x000004105030b0b5 0x858000000471f1ff

def z123 : W := mkw 0x90465554d1b4f4f5 0x140f1c70f3f07070

def z124 : W := mkw 0x90465146c186565c 0x56ce134ec3807e7c

def z125 : W := mkw 0xe0b0a29b0edb0fea 0xeff0e38f0fff8fff

def z126 : W := mkw 0x90465144c1845454 0x140e1040c3807070

def z127 : W := mkw 0xb076f3cfcd8f5f5e 0xfffef3cfcf8fffff

def z128 : W := mkw 0x8002014200820648 0xffeec34e0b8e0e7c

def z129 : W := mkw 0x41bdfeb00f7de9a0 0xbd3ffcb00ffff180

def z130 : W := mkw 0x2000028b00020b0a 0xebd0238f04018f8f

def z131 : W := mkw 0x00000010001000a0 0x1401007000700070

def z132 : W := mkw 0xe0bba3eb0ecb0f4a 0x006ec30e0b8e0e00

def z133 : W := mkw 0x00000010001000a0 0x408000f0000001f0

def z134 : W := mkw 0x013dfc105f7df0b5 0xbdbffc000ffff1ff

def z135 : W := mkw 0x0000000200020208 0x0060c30e080e0e00

def z136 : W := mkw 0x000004105030b0b5 0xc78000f1f471f1ff

def z137 : W := mkw 0x200000000c090902 0x0000000004018183

def z138 : W := mkw 0xd2fffbffefd65ffc 0xfffffffffffe7ffc

def z139 : W := mkw 0x927ffbede1845454 0x7e7ffffff3807070

def z140 : W := mkw 0x9040000201864648 0x000000000b8e0e00

def z141 : W := mkw 0x033ffbedaf4d4000 0x7a7ffffffb8e0000

def z142 : W := mkw 0x010004000f6de000 0xbd113c000ffff000

def z143 : W := mkw 0x40b902b00e5009a0 0xdc9100f0047001f0

def z144 : W := mkw 0x0104fc00012de000 0x2100fc00000ff000

def z145 : W := mkw 0x10400006c002121c 0x0240000ec000000c

def z146 : W := mkw 0x000004105030b0b5 0xff801040c471f1ff

def z147 : W := mkw 0x2030a2890c090902 0x0010208104018183

def z148 : W := mkw 0x023ffbeda0000000 0x587fc3fe00000000

def z149 : W := mkw 0xc2bffbedaec00d40 0x7a7ffffffb800e00

def z150 : W := mkw 0x000004105030b0b5 0xa7803c01f471f1ff

def z151 : W := mkw 0x213dfe890f6de902 0xbd3ffc810ffff183

def z152 : W := mkw 0x0139ac000e69a000 0xa931ec000c7f8000

def z153 : W := mkw 0x013dfe800f6de900 0xfdbfff800fffff80

def z154 : W := mkw 0x90420144c0801454 0x00000040c0000070

def z155 : W := mkw 0x023ffbedae400000 0xfe7ffffffff00000

def z156 : W := mkw 0xe0b2a3fb0c9b0fea 0xebf0e3ff0c0f8fff

def z157 : W := mkw 0x023ffbeda0000000 0x426ec3fff0000000

def z158 : W := mkw 0xc08000100ed00de0 0x848000000ff00ff0

def z159 : W := mkw 0x90420146c082165c 0x42c0034ec0000e7c

def z160 : W := mkw 0x00000010001000a0 0xfe913cf1f47001f0

def z161 : W := mkw 0x033fffeda12de000 0x7b7ffffff00ff000

def z162 : W := mkw 0x0030a28900000000 0x6a70e38f00000000

def z163 : W := mkw 0xc2bffbfdaed00de0 0xfefffffffff00ff0

def z164 : W := mkw 0x823ffbeda0800440 0xfefffffffb800e70

def z165 : W := mkw 0x2034f28b0d0f4b0a 0xfffef38f0f8fff8f

def z166 : W := mkw 0xc1bffff00ffdede0 0xfdbffff00ffffff0

def z167 : W := mkw 0x000000000c000900 0x808000000c000f80

def z168 : W := mkw 0x023fffeda020a000 0xff7ffffff471f000

def z169 : W := mkw 0x0000000000000000 0x0000000000000000

def z170 : W := mkw 0x010d5c105374f0b5 0x140f1c70f3f07070

def z171 : W := mkw 0xc08b016002c00440 0x000e000003800000

def z172 : W := mkw 0x40b906b01e70a9a1 0x00112cb134718183

def z173 : W := mkw 0x0004f80000000000 0x2000fc0000000000

def z174 : W := mkw 0x0000000200020208 0xebf0e38f0c0f8f8f

def z175 : W := mkw 0x030f5d64a364e000 0x140f1c70f3f07000

def z176 : W := mkw 0xc0bba3f00ed90de0 0xfdbfe3f00fff8ff0

def z177 : W := mkw 0x41b9aeb00e79a9a0 0x00112cb004718180

def z178 : W := mkw 0x200000020c0b0b0a 0xebe0c30e0c0f8f8f

def z179 : W := mkw 0x8002014000800440 0x140e004003800070

def z180 : W := mkw 0x023ffbedac090000 0xfb7ffffffc0f8000

def z181 : W := mkw 0x023ff964a0000000 0x383ffc70f0000000

def z182 : W := mkw 0x000004105030b0b5 0x95811c70f471f1ff

def z183 : W := mkw 0x033dfea92f6de000 0xbd3ffcb13ffff000

def z184 : W := mkw 0x90465146c186565c 0xfffffffffb8e7e7c

def z185 : W := mkw 0x0034f0000d0d4000 0xbd3ef0000f8ff000

def z186 : W := mkw 0x213dfc0b0f6fe20a 0xbf7ffc0f0ffff00f

def z187 : W := mkw 0x0104fc00012de000 0xbd2efc000b8ff000

def z188 : W := mkw 0x020203eda0000000 0x0040030e00000000

def z189 : W := mkw 0x013dfc000f6de000 0x142fdc000bfe7000

def z190 : W := mkw 0x2000a28b000b0b0a 0x63c0e38f000f8f8f

def z191 : W := mkw 0x020f5964a0000000 0x100f1c70f0000000

def z192 : W := mkw 0x2039a28b0e4b0b0a 0xffffe38f0fff8f8f

def z193 : W := mkw 0x40890030025000a0 0x0001003000700000

def z194 : W := mkw 0x90465546d1a6f65d 0xffeeff4ffb8ffe7f

def z195 : W := mkw 0x2030a0020c0b0b0a 0xa9b0e0000c0f8f8f

def z196 : W := mkw 0x003006905c30b9b5 0xffb13ff1fc71ffff

def z197 : W := mkw 0x0000000000000000 0xbd00100000007000

def z198 : W := mkw 0x0030a00000000000 0x2830e00000000000

def z199 : W := mkw 0x2000028b0c0b0b0a 0xc3c0038f0c0f8f8f

def z200 : W := mkw 0x2139ae890e69a902 0x00112c8104718183

def z201 : W := mkw 0x003904105e70b0b5 0xffbf3cf1fff1f1ff

def z202 : W := mkw 0x0239aaa920000000 0x00112cb130000000

def z203 : W := mkw 0x2239aaab2c0b0b0a 0xebf1efbf3c0f8f8f

def z204 : W := mkw 0x803203c00c800d40 0xdcbe03c00f800ff0

def z205 : W := mkw 0x2030a69b5c3bbbbf 0xeff0e38f0c7fffff

def z206 : W := mkw 0xd0ff57f6dff6fffd 0xffffffffffffffff

def z207 : W := mkw 0x90465554d1b4f4f5 0xff9f3cf1f7f1f1ff

def z208 : W := mkw 0x000004000020a000 0x21003c000001f000

def z209 : W := mkw 0x013df8000f4d4000 0x002ec0000b8e0000

def z210 : W := mkw 0x020203eda0000000 0x7a513ffff0000000

def z211 : W := mkw 0x223ffbefac0b0b0a 0x7a7ffffff80e0e00

def z212 : W := mkw 0x90465146c186565c 0x374ed04ec38e707c

def z213 : W := mkw 0x223ffbedac090902 0x7a7ffffff4018183

def z214 : W := mkw 0x40b902b00e5009a0 0xc8b103b00c700f80

def z215 : W := mkw 0x010d580003444000 0x000e000003800000

def z216 : W := mkw 0x0200000da0000000 0x0240000ff0000000

def z217 : W := mkw 0x000004105030b0b5 0x56811cf1f07071ff

def z218 : W := mkw 0x924203efe082165c 0x42c003fff0000e7c

def z219 : W := mkw 0xb04000024d8f5f5e 0x858000000f8fffff

def z220 : W := mkw 0xc080001000900de0 0x0080000000000ff0

def z221 : W := mkw 0x0030a0000c090000 0x0010200004018000

def z222 : W := mkw 0x803b01400ec00440 0xdcbf03400ff00e70

def z223 : W := mkw 0x9040041251b6f6fd 0x858000000fffffff

def z224 : W := mkw 0x000004005020b015 0x23003c01f001f00f

def z225 : W := mkw 0x0204f80da0000000 0x7a51fcfff0000000

def z226 : W := mkw 0x00065554d030b0b5 0xfffffffff471f1ff

def z227 : W := mkw 0x013ffd448f6de000 0xff7fff4ecffff000

def z228 : W := mkw 0x904000024186565c 0xff801040cb8e7e7c

def z229 : W := mkw 0x000004000020a000 0xff113cf1f471f000

def z230 : W := mkw 0xc3bffffdaffdede0 0xfffffffffffffff0

def z231 : W := mkw 0x003b07f05030b0b5 0xffbf3ff1f471f1ff

def z232 : W := mkw 0x200004125c3bbbbf 0x858000000c7fffff

def z233 : W := mkw 0x2030a69b5c3bbbbf 0xfff1fffffc7fffff

def z234 : W := mkw 0x10445006c106521c 0xffc0d04ec00e707c

def z235 : W := mkw 0x013fffe00f6de000 0xfd3ffff00ffff000

def z236 : W := mkw 0x0030a2890c090000 0xeb70e38f0c0f8000

def z237 : W := mkw 0xc0bb03f000900de0 0x58bf03f000000ff0

def z238 : W := mkw 0x023ffbeda1044000 0xff7ffffffb8e7000

def z239 : W := mkw 0x200000020c0b0b0a 0x818000000c0f8f8f

def z240 : W := mkw 0x003002800c000900 0xebb023810c018f8f

def z241 : W := mkw 0x90465144c1845454 0xdcae1340cb807e70

def z242 : W := mkw 0x2030a28b0c0b0b0a 0xa970e30e0c0f8e00

def z243 : W := mkw 0x013dfc000f6de000 0xff3ffcf1fffff000

def z244 : W := mkw 0x0002014000000000 0x582e034000000000

def z245 : W := mkw 0x0039a0000e490000 0xbd3fe0000fff8000

def z246 : W := mkw 0xa032a3cb0c8b0f4a 0xfffee3cf0f8f8fff

def z247 : W := mkw 0x023ffffdb030a0a1 0x7a7ffffff4718183

def z248 : W := mkw 0xc08201500ed00de0 0xdcae03400ff00ff0

def z249 : W := mkw 0x013df8000f4d4000 0xbd2ed0000b8e7000

def z250 : W := mkw 0x8002014000800440 0x002e03000b800e00

def z251 : W := mkw 0x023dfaada0000000 0x2251fcbff0000000

def z252 : W := mkw 0x2000028900000902 0x0000008100000183

def z253 : W := mkw 0x9046514681864648 0xdceec34e0b8e0e70

def z254 : W := mkw 0x010004000e69a000 0x0000000004718000

def z255 : W := mkw 0xb17fffcfcfefff5e 0xffffffcfcfffffff

def z256 : W := mkw 0x010454000f6de000 0xbd2ed0000ffff000

def z257 : W := mkw 0x000454000124e000 0xbd3ffc000ffff000

def z258 : W := mkw 0xd0c653f6c1965ffc 0xffeed3fecb8e7ffc

def z259 : W := mkw 0x117dfc06cf6ff21c 0xbf7ffc0ecffff00c

def z260 : W := mkw 0x003b03e000000000 0x583f03f000000000

def z261 : W := mkw 0x90465156d19656fd 0xffeed3fffb8e7fff

def z262 : W := mkw 0x2030a28b00020b0a 0x6af0e38f00000f8f

def z263 : W := mkw 0x803b03e000800440 0xdcbf03f00b800e70

def z264 : W := mkw 0x023ffbeda0000000 0x6a7ee38f00000000

def z265 : W := mkw 0x0030a2800c090900 0xe9b0e3800c0f8f80

def z266 : W := mkw 0x220203efa0020b0a 0x42c003fff0000f8f

def z267 : W := mkw 0xc0bb03f00ed00de0 0x141f00f007f001f0

def z268 : W := mkw 0x0000028000000900 0x4080038000000f80

def z269 : W := mkw 0xc2bf5bf4aed00de0 0xdcbf1ff0fff00ff0

def z270 : W := mkw 0x020f5964a0000000 0x7a6fdf7ef0000000

def z271 : W := mkw 0x90465146c186565c 0x236ed30ecb8e7e0c

def z272 : W := mkw 0x0036f3cd80000000 0x7a7ef3cfc0000000

def z273 : W := mkw 0x0139a8000e490000 0x0000000000000000

def z274 : W := mkw 0x003dfa8900000000 0x7a7fff8f00000000

def z275 : W := mkw 0x0000000040001014 0xff913cf1f000707c

def z276 : W := mkw 0xc08b017002d004e0 0xdcaf03700bf00e70

def z277 : W := mkw 0xd0cf5174c3d454f4 0x140f1070c3f07070

def z278 : W := mkw 0x003000000c000000 0x883000000c000000

def z279 : W := mkw 0x2234fa8fac0b0b0a 0xebf0ff8ffc0f8f8f

def z280 : W := mkw 0x0030a28900000000 0x0010208100000000

def z281 : W := mkw 0x000004105030b0b5 0x23113cb1f471f18f

def z282 : W := mkw 0x000004101030a0a1 0x00010c3030700000

def z283 : W := mkw 0x0139ac000f6de000 0x85112c000ffff000

def z284 : W := mkw 0x0104fc10513df0b5 0xff91fcf1f47ff1ff

def z285 : W := mkw 0xe08000120edb0fea 0x858000000fff8fff

def z286 : W := mkw 0x2000a41b503bb2bf 0xffd1fcfff47ff1ff

def z287 : W := mkw 0x00000010501010b5 0x00000070f0000070

def z288 : W := mkw 0x927ffbefa1864648 0x7a7ffffffb8e0e00

def z289 : W := mkw 0x01045c000124e000 0x00001c0000007000

def z290 : W := mkw 0x0030a0020c0b0208 0xebf0e30e0c0f8e0c

def z291 : W := mkw 0x0004500480000000 0x2240d00ec0000000

def z292 : W := mkw 0x2030a28b0c0b0b0a 0x2360e30f080f8e0f

def z293 : W := mkw 0x924f5964e1845454 0x140f1c70f3807070

def z294 : W := mkw 0x917ffd44cfedf454 0xbd3ffc40cffff070

def z295 : W := mkw 0x010000000f4d4000 0x000000000b8e0000

def z296 : W := mkw 0x003df80000000000 0x383ffc0000000000

def z297 : W := mkw 0x013dfe890f6de000 0xff7fff8f0ffff000

def z298 : W := mkw 0x2030a2890c090902 0xeb9020810401818f

def z299 : W := mkw 0x2000a00b000b020a 0xebd0e08f040f818f

def z300 : W := mkw 0x90420146c082165c 0xebe0c34ec80e0e7c

def z301 : W := mkw 0x010d5c000364e000 0xbd2fdc000bfe7000

def z302 : W := mkw 0x0000000000000000 0x818000000401818f

def z303 : W := mkw 0x9046514681864648 0x7a6ed34ecb8e0e00

def z304 : W := mkw 0x023fffedf020b015 0x7b7ffffff001f00f

def z305 : W := mkw 0x0000000000000000 0x9c11000004700000

def z306 : W := mkw 0xd0ff53f68fd64fe8 0xdcffc3fe0ffe0ff0

def z307 : W := mkw 0x90420146c186565c 0xc7c0034ecb8e7e7c

def z308 : W := mkw 0x2030a2890c090902 0x6a70e38f04018183

def z309 : W := mkw 0x013dfc020f6fe208 0xffffff0e0ffffe0c

def z310 : W := mkw 0xd0c000124fd65ffc 0x858000000ffe7ffc

def z311 : W := mkw 0x2030a28b0c0b0b0a 0x42e0c38f080e0f8f

def z312 : W := mkw 0x0000000000000000 0xc890008004000180

def z313 : W := mkw 0x000000024002121c 0xffe0d34ec80e7e7c

def z314 : W := mkw 0x8002014040801454 0xffae1340cb807e7c

def z315 : W := mkw 0x00000010501010b5 0xeb9020f1f40181ff

def z316 : W := mkw 0x003900100e5000a0 0xdcbf00f00ff001f0

def z317 : W := mkw 0x8006514001844440 0xfdaed3400b8e7e70

def z318 : W := mkw 0x000004000020a000 0x00112c0004718000

def z319 : W := mkw 0x000004105030b0b5 0x0400000000707070

def z320 : W := mkw 0xe0bb03fb0ed20fea 0xdeff03ff0ff00fff

def z321 : W := mkw 0x010d5c000f6de000 0x950f1c000ffff000

def z322 : W := mkw 0x003f53e480000000 0x7a7fd3fec0000000

def z323 : W := mkw 0x2030a28b0c0b0b0a 0x81e0c30e0c0f8f8f

def z324 : W := mkw 0x90465556d1b6f6fd 0xffefdf7efbfe7e7c

def z325 : W := mkw 0x003900000e400000 0x0011000004700000

def z326 : W := mkw 0x003902a000000000 0x001100b000000000

def z327 : W := mkw 0x0000000000000000 0x428000810000018f

def z328 : W := mkw 0x003b03f0001000a0 0xdcbf03f0047001f0

def z329 : W := mkw 0x000004001020a001 0x00002c0130018003

def z330 : W := mkw 0xc0bb01700ed004e0 0x9c3f00700ff00070

def z331 : W := mkw 0x3074f28fcd0f5b1e 0xebf0f38fcc0fff8f

def z332 : W := mkw 0x80020150009004e0 0xdcbf03f00ff00ff0

def z333 : W := mkw 0x2030a28b0c0b0b0a 0xebe0c30e080e0e0c

def z334 : W := mkw 0x10445006c106521c 0xebe0d30ec80e7e0c

def z335 : W := mkw 0x023ffffdf030b0b5 0x7e7ffffff0707070

def z336 : W := mkw 0x033fffeda364e000 0x7e7ffffff3f07000

def z337 : W := mkw 0x2139ae8b0e6bab0a 0xebf1ef8f0c7f8f8f

def z338 : W := mkw 0x013904000f6de000 0x9d3f00000ffff000

def z339 : W := mkw 0x210004020f6feb0a 0x858000000fffff8f

def z340 : W := mkw 0x0030a28b00020208 0xebf0e38f080e0e0c

def z341 : W := mkw 0xc1bdfc100ffdede0 0xbdbffc000ffffff0

def z342 : W := mkw 0x000004105030b0b5 0xef9020810471f1ff

def z343 : W := mkw 0x0004500041045014 0xffaed040cb8e707c

def z344 : W := mkw 0x00000010001000a0 0x84800000047001f0

def z345 : W := mkw 0x0000000040001014 0x23001000c000700c

def z346 : W := mkw 0x10445406d126f21d 0x2340fc0ff00ff00f

def z347 : W := mkw 0x013dfc005f6df015 0xbf3ffc01fffff00f

def z348 : W := mkw 0x010004000364e000 0x0400000003f07000

def z349 : W := mkw 0x00000010001000a0 0xff9120f1047181ff

def z350 : W := mkw 0x917ffd468fefe648 0xbd7fff0e0ffffe00

def z351 : W := mkw 0x003b03e00e400000 0xdc3f03f00ff00000

def z352 : W := mkw 0x8002014000800440 0x4080034000000e70

def z353 : W := mkw 0x003df8000c090000 0xb93ffc000c0f8000

def z354 : W := mkw 0x203ba3eb0c0b0b0a 0xfbffe3ff0c0f8f8f

def z355 : W := mkw 0x023b03eda0000000 0x5a7f03fff0000000

def z356 : W := mkw 0xc0bb03f00ed00de0 0x142f03700bf00e70

def z357 : W := mkw 0x0000028900000000 0x4240038f00000000

def z358 : W := mkw 0x914004024feff65c 0x858000000ffffe7c

def z359 : W := mkw 0x42b9aab92e5009a0 0x00112cb134700180

def z360 : W := mkw 0x9246f94fe186565c 0xffeeff4ffb8e7e7c

def z361 : W := mkw 0x023ffbedac000900 0xfafffffffc000f80

def z362 : W := mkw 0xc0bb03f00ed00de0 0xfebf3ff1fff00ff0

def z363 : W := mkw 0x924f5966e186565c 0xffefdf7efb8e7e7c

def z364 : W := mkw 0xe0bb03f20edb0fea 0xddbf03f00fff8fff

def z365 : W := mkw 0x2030a2890c090902 0xc8b023810c018f83

def z366 : W := mkw 0x200004125c3bbbbf 0xff913cf1fc7fffff

def z367 : W := mkw 0x010dfc00036de000 0x350ffc0003fff000

def z368 : W := mkw 0x000004105030b0b5 0xdc911cf0f47071f0

def z369 : W := mkw 0x013dfc000f6de000 0xffbffc810ffff18f

def z370 : W := mkw 0x000000000c090000 0x810000000c0f8000

def z371 : W := mkw 0xc0b203f00c900de0 0xc8b003f00c000ff0

def z372 : W := mkw 0x408002b0001009a0 0x000000b000000180

def z373 : W := mkw 0x0000000000000000 0xeb8000000000000c

def z374 : W := mkw 0x000004105030b0b5 0xbd913c000471f1ff

def z375 : W := mkw 0x90465146c186565c 0x63c0d34ec00e7e7c

def z376 : W := mkw 0xc18004100ffdede0 0x858000000ffffff0

def z377 : W := mkw 0xc08b01700ed00de0 0x948f00700ff00ff0

def z378 : W := mkw 0x003b03e00c000900 0xd8bf03f00c000f80

def z379 : W := mkw 0x203002820c0b0b0a 0xc9b003800c0f8f8f

def z380 : W := mkw 0x200000020c0b0b0a 0x00000000080e0e00

def z381 : W := mkw 0x010d5c105374f0b5 0xff9f3cf1f7f1f1ff

def z382 : W := mkw 0xc1bf5ff00ff4ede0 0xdcbf1ff00ff07ff0

def z383 : W := mkw 0xd0fb03f6ced21ffc 0xdeff03fecff00ffc

def z384 : W := mkw 0x9040041251b6f6fd 0xff913cf1ffffffff

def z385 : W := mkw 0x033dfc0daf6de000 0xbf7ffc0ffffff000

def z386 : W := mkw 0x013dfc000f6de000 0x212efc000b8ff000

def z387 : W := mkw 0x013dfc00012de000 0x393ffc00000ff000

def z388 : W := mkw 0xc1bfffe00feded40 0xbd3fff000ffffe00

def z389 : W := mkw 0x90465146c186565c 0x958e1040cb8e7e7c

def z390 : W := mkw 0x0004500001044000 0x002ec0000b8e0000

def z391 : W := mkw 0xc08203f00ed00de0 0xc48003f00ff00ff0

def z392 : W := mkw 0xd0fb03f24fd65ffc 0xddbf03f00ffe7ffc

def z393 : W := mkw 0xd0c65156cfd65ffc 0xffeed34ecffe7ffc

def z394 : W := mkw 0xc08203f050901df5 0x428003f1f0000fff

def z395 : W := mkw 0xc0b902b00ed00de0 0x849100b00ff00ff0

def z396 : W := mkw 0x003df80000000000 0x7a3ffcf1f0000000

def z397 : W := mkw 0x0100ac000029a000 0x00002c0000018000

def z398 : W := mkw 0x003ffbe000000000 0x783ffff000000000

def z399 : W := mkw 0x023f5be4a0000000 0x583f1ff0f0000000

def z400 : W := mkw 0x000004000020a000 0x850000000471f000

def z401 : W := mkw 0x0000000000000000 0x7a001040c0000000

def z402 : W := mkw 0x023ffbeda0000000 0xfbfffffff401818f

def z403 : W := mkw 0x0000000000000000 0x22003c01f0000000

def z404 : W := mkw 0x003dfc000020a000 0xbd3ffc000471f000

def z405 : W := mkw 0x023ffbeda0000000 0x106fdf7ef0000000

def z406 : W := mkw 0x0204fc1df030b0b5 0xffd1fcfff471f1ff

def z407 : W := mkw 0xf0fff3ffcfdf5ffe 0xfffff3ffcfffffff

def z408 : W := mkw 0x2000a00900090002 0x0000200100018003

def z409 : W := mkw 0xc2bffbfda0900de0 0x7afffffff0000ff0

def z410 : W := mkw 0x023ffbeda0000000 0x387fff0e00000000

def z411 : W := mkw 0x0030a2890c000900 0xeaf0e38f0c000f80

def z412 : W := mkw 0x2030a28b4c0b1b1e 0xfff0f3cfcc0fffff

def z413 : W := mkw 0x0004500000000000 0x382ed00000000000

def z414 : W := mkw 0x0000000200020208 0xebe0c30e080e0e0c

def z415 : W := mkw 0x20000002000b020a 0x01000000000f800f

def z416 : W := mkw 0x0200a80920000000 0x00002c0130000000

def z417 : W := mkw 0x904201424186565c 0xddae03400b8e7e7c

def z418 : W := mkw 0x033fffedaf6de000 0xbd7fff0e0ffff000

def z419 : W := mkw 0x0030a28900000000 0x7a71fffff0000000

def z420 : W := mkw 0x023ffbfda01000a0 0xfefffffff47001f0

def z421 : W := mkw 0x003902800e400900 0xdcbf03800ff00f80

def z422 : W := mkw 0x033ffffdff7df0b5 0xfffffffffffff1ff

def z423 : W := mkw 0xe0bba3eb0ecb0f4a 0xebfee38f0f8f8f8f

def z424 : W := mkw 0x023df80da0000000 0x3a7ffc0ff0000000

def z425 : W := mkw 0x000004105030b0b5 0xff811c70f070707c

def z426 : W := mkw 0x003002800c000900 0x0010008004000180

def z427 : W := mkw 0x0206fbeda0000000 0x6240fffff0000000

def z428 : W := mkw 0x0209082020000000 0x00010c3030000000

def z429 : W := mkw 0x013dfc000e69a000 0x383ffc0004718000

def z430 : W := mkw 0x90465146c186565c 0x85eec30e0b8e7e7c

def z431 : W := mkw 0x90465146c186565c 0xfffef3cfcf8fffff

def z432 : W := mkw 0x023dfaa920000000 0x383ffcb130000000

def z433 : W := mkw 0x0206f94da0000000 0x7a6eff4ff0000000

def z434 : W := mkw 0x0000000040001014 0x858000000000707c

def z435 : W := mkw 0x013df8000f4d4000 0x9c3fc0000ffe0000

def z436 : W := mkw 0x033ffbedaf4d4000 0x006ec30e0b8e0000

def z437 : W := mkw 0xc0bb07f00ef0ade0 0xfdbf3ff00ff1fff0

def z438 : W := mkw 0x003df80001044000 0xbd3ffc000b8e7000

def z439 : W := mkw 0x90420146c082165c 0xffc0134ec0007e7c

def z440 : W := mkw 0x10465146c106521c 0x7b6ed34ec00e700c

def z441 : W := mkw 0x907653c6cd865f5c 0xfffed3cecf8e7ffc

def z442 : W := mkw 0x033ffd64af6de000 0xbd3ffc70fffff000

def z443 : W := mkw 0x127ffbefe106521c 0x7b7ffffff00e700c

def z444 : W := mkw 0x0239aeb93030a0a1 0x00112cb134718183

def z445 : W := mkw 0x010004105f7df0b5 0xff913cf1fffff1ff

def z446 : W := mkw 0xc1bb07f00ffdede0 0xddbf03f00ffffff0

def z447 : W := mkw 0x2030028b0c020b0a 0xcaf0038f0c000f8f

def z448 : W := mkw 0xe08203fb00920fea 0x42c003ff00000fff

def z449 : W := mkw 0x8002055050b0b4f5 0xffbf3ff1fff1ffff

def z450 : W := mkw 0x0000000050001015 0x02000001f000000f

def z451 : W := mkw 0xc2bffffdfef0bdf5 0xfffffffffff1ffff

def z452 : W := mkw 0x0000000040001014 0x14001040c0007070

def z453 : W := mkw 0x0304fc0da12de000 0x2340fc0ff00ff000

def z454 : W := mkw 0x213dfa8b0f4f4b0a 0xebfee38f0f8f8f8f

def z455 : W := mkw 0x0204fc0df020b015 0x2340fc0ff001f00f

def z456 : W := mkw 0xc0bb03f20ed20fe8 0xffffc3fe0ffe0ffc

def z457 : W := mkw 0x924653efe186565c 0xffeed3fffb8e7e7c

def z458 : W := mkw 0x000004004020b014 0xff913c40c471f07c

def z459 : W := mkw 0x003ff94480000000 0x7a7fff4ec0000000

def z460 : W := mkw 0x00000010101000a1 0x000000b130000183

def z461 : W := mkw 0xc2bb03fdaed00de0 0xdeff03fffff00ff0

def z462 : W := mkw 0x0004500001044000 0x2100d000000e7000

def z463 : W := mkw 0xd0cf5176c3d656fc 0xffefd37ecbfe7e7c

def z464 : W := mkw 0x0030a4000c29a000 0xbd31fc000c7ff000

def z465 : W := mkw 0x2030a29b0c1b0baa 0xfff1e3ff0c7f8fff

def z466 : W := mkw 0x0039a80000000000 0x00112c0000000000

def z467 : W := mkw 0x000004100030a0a0 0xfd913cf00471f1f0

def z468 : W := mkw 0x8000000000800440 0x848000000b800e70

def z469 : W := mkw 0x000004101030a0a1 0xeb912cb13471818f

def z470 : W := mkw 0x003002900c1009a0 0xdcb103f00c700ff0

def z471 : W := mkw 0x90420156d09216fd 0x42c003fff0000fff

def z472 : W := mkw 0xc08004105ef0bdf5 0xff913cf1fff1ffff

def z473 : W := mkw 0xc1bffd700ffde4e0 0xbd3ffc700ffff070

def z474 : W := mkw 0x013df8000f4d4000 0x383ffc000b8e0000

def z475 : W := mkw 0xc0820170009004e0 0x0000007000000070

def z476 : W := mkw 0x2030a6995c39b9b7 0xff913cf1f471f1ff

def z477 : W := mkw 0x000004005020b015 0xff803c41f001f07f

def z478 : W := mkw 0x213dfa8b0f4f4b0a 0x006ec30e0b8e0e00

def z479 : W := mkw 0x2030a68b5c2bbb1f 0xebf0ff8ffc0fff8f

def z480 : W := mkw 0x2030a28b0c0b0b0a 0x42d0238f04018f8f

def z481 : W := mkw 0x927ffffff1b6f6fd 0xffffffffffffffff

def z482 : W := mkw 0x023ffbede0001014 0xfffffffff000707c

def z483 : W := mkw 0x2000000b0002020a 0x0240000f0000000f

def z484 : W := mkw 0xd0ff53e68fc64f48 0x006ec30e0b8e0e00

def z485 : W := mkw 0x003002820c020b08 0xebf0c38e0c0e0f8c

def z486 : W := mkw 0x90465556d1b6f6fd 0xffeed34ecfffffff

def z487 : W := mkw 0x0239aeb97030b0b5 0xff913cf1f471f1ff

def z488 : W := mkw 0x000004101030a0a1 0x7a113cf1f4718183

def z489 : W := mkw 0x01090c000260a000 0x00010c0000700000

def z490 : W := mkw 0x90445006c186565c 0xa7c0d00ecb8e7e7c

def z491 : W := mkw 0x42bffbfdae5009a0 0x7a7ffffff4700180

def z492 : W := mkw 0x0000000000000000 0x0010208104018183

def z493 : W := mkw 0xb076f7dfddbfffff 0xffffffffffffffff

def z494 : W := mkw 0x1144fc06c12ff21c 0x2340fc0ec00ff00c

def z495 : W := mkw 0x2030a2890c090902 0xa930e0810c0f8183

def z496 : W := mkw 0x0000000000000000 0xc8a0030008000e00

def z497 : W := mkw 0xc1bffff05ffdfdf5 0xffbffff1ffffffff

def z498 : W := mkw 0x9046514681864648 0xbd6ed30e0b8e7e00

def z499 : W := mkw 0x0204f80da0000000 0x0040c00e00000000

def z500 : W := mkw 0x013dfc004f6df014 0xffbffc40cffff07c

def z501 : W := mkw 0xc0bb03f04ed01df4 0xffbf13f0cff07ffc

def z502 : W := mkw 0x2030a28b0c0b0b0a 0x819020810c0f8f8f

def z503 : W := mkw 0x223ffbefac0b0b0a 0xebfee38f0c0f8f8f

def z504 : W := mkw 0x013dfc105f7df0b5 0xbd3ffc70fffff070

def z505 : W := mkw 0xc2bbabf92ed00de0 0xdcbf2ff13ff00ff0

def z506 : W := mkw 0x223ffbefa00b020a 0x7b7ffffff00f800f

def z507 : W := mkw 0xc2bffbfda2d004e0 0x7e7ffffff3f00070

def z508 : W := mkw 0x2030a28b0c0b0b0a 0x6a70e38f080e0e00

def z509 : W := mkw 0xe0bba7fb5efbbfff 0xffffffffffffffff

def z510 : W := mkw 0x0000000000000000 0x6a60c30e00000000

def z511 : W := mkw 0x907f53e6c186565c 0xffffd3fecb8e7e7c

def z512 : W := mkw 0x0004500001044000 0x140e100003807000

def z513 : W := mkw 0x927ffbefa1864648 0x006ec30e0b8e0e00

def z514 : W := mkw 0x003df80000000000 0x002ec00000000000

def z515 : W := mkw 0x013dfc000364e000 0x3c3ffc0003f07000

def z516 : W := mkw 0xd0ff53f4cfd45df4 0xdcbf13f0cff07ff0

def z517 : W := mkw 0x9146fd46c1aff65c 0xffeeff4ecb8ffe7c

def z518 : W := mkw 0xc08207f050b0bdf5 0xff913ff1f471ffff

def z519 : W := mkw 0x013df8000f4d4000 0xa93ee0000f8f8000

def z520 : W := mkw 0x40b902b00e5009a0 0x9c3f00b00ff00180

def z521 : W := mkw 0x904000024186565c 0xefe0c30e0b8e7e7c

def z522 : W := mkw 0x000004105030b0b5 0xdd9100f00471f1ff

def z523 : W := mkw 0x00000010501010b5 0x7a913cf1f00001ff

def z524 : W := mkw 0x000004105030b0b5 0x85912cb13471f1ff

def z525 : W := mkw 0x203dfa8b0c0b0b0a 0xfbffff8f0c0f8f8f

def z526 : W := mkw 0x000454105134f0b5 0xffbffcf1fffff1ff

def z527 : W := mkw 0x013dfc101f7de0a1 0xbd3ffcb13ffff183

def z528 : W := mkw 0xb27ffbefed8f5f5e 0xffffffffff8fffff

def z529 : W := mkw 0x2239aaa92c090902 0x00112cb134018183

def z530 : W := mkw 0x2030a69b1c3babab 0xebf1efbf3c7f8f8f

def z531 : W := mkw 0x013dfc100f7de0a0 0xfdbffcf00ffff1f0

def z532 : W := mkw 0x003b03e000000000 0x002e030000000000

def z533 : W := mkw 0xd0ff53e6cfc65f5c 0xffeed34ecb8e7e7c

def z534 : W := mkw 0x9042014680820648 0x0040030e00000e00

def z535 : W := mkw 0xb0465146cd8f5f5e 0xffeed34ecf8fffff

def z536 : W := mkw 0x200000020c0b0b0a 0xeb9020810c0f8f8f

def z537 : W := mkw 0xc2bffbfdaed00de0 0xdcffc3fe0ff00ff0

def z538 : W := mkw 0x2000a40b502bb21f 0x2340fc0ff00ff00f

def z539 : W := mkw 0x0000000000000000 0x420000f1f0000000

def z540 : W := mkw 0x2030a28b000b020a 0x6b70e38f000f800f

def z541 : W := mkw 0x0030a28900000000 0x0060c30e00000000

def z542 : W := mkw 0x9076f146cd8f565c 0xfffef34ecf8ffe7c

def z543 : W := mkw 0x000004105030b0b5 0x14113cf1f471f1f3

def z544 : W := mkw 0x0000000000000000 0x230020010001800f

def z545 : W := mkw 0x003904000e60a000 0xbd3f3c000ff1f000

def z546 : W := mkw 0x0009000002400000 0x140f000003f00000

def z547 : W := mkw 0x020203fdf01010b5 0x42c003fff00001ff

def z548 : W := mkw 0x013dfc000f6de000 0x003fec000fff8000

def z549 : W := mkw 0x0000a00000090000 0x2100e000000f8000

def z550 : W := mkw 0x9040000041845454 0x0400000003807070

def z551 : W := mkw 0xc0b002900ed00de0 0xccb003800ff00ff0

def z552 : W := mkw 0xc0bb03f00ed00de0 0x40ae03f00b800ff0

def z553 : W := mkw 0x020f5964a0000000 0x7a1f3cf1f0000000

def z554 : W := mkw 0x003b03e000000000 0x7a3f3ff1f0000000

def z555 : W := mkw 0x020f5d74f030b0b5 0xff9f3cf1f471f1ff

def z556 : W := mkw 0x40bb03f00e5009a0 0x583f03f004700180

def z557 : W := mkw 0x2030a6991c39a9a3 0x00112cb134718183

def z558 : W := mkw 0x023ffbeda0000000 0x226eff0ff0000000

def z559 : W := mkw 0x213dfc020f6feb0a 0xbdbffc000fffff8f

def z560 : W := mkw 0x10445416d136f2bd 0xffd1fcfff47ff1ff

def z561 : W := mkw 0x927ffbefe186565c 0xffeed34ecb8e7e7c

def z562 : W := mkw 0x907ff946c186565c 0xffffff4ecb8e7e7c

def z563 : W := mkw 0x0004500201064208 0xffeed30e0b8e7e0c

def z564 : W := mkw 0x104000024106521c 0x01000000000e700c

def z565 : W := mkw 0x000004005020b015 0x7b113cf1f001f00f

def z566 : W := mkw 0x000004101030a0a1 0xdc912cf1347181f3

def z567 : W := mkw 0x010004105f7df0b5 0x858000000ffff1ff

def z568 : W := mkw 0x0000000000000000 0x10011c70f0000000

def z569 : W := mkw 0xc0bffbf00ed00de0 0xfcbffff00ff00ff0

def z570 : W := mkw 0x1044500681064208 0x0040c00e000e0000

def z571 : W := mkw 0x2036f3cf8c0b0b0a 0xfbfef3cfcc0f8f8f

def z572 : W := mkw 0x0139ac105e79b0b5 0xff913cf1f471f1ff

def z573 : W := mkw 0x013d5c000f64e000 0x9c3f1c000ff07000

def z574 : W := mkw 0xc1bbaff00ef9ade0 0xdcbf2ff00ff18ff0

def z575 : W := mkw 0x000004105030b0b5 0xbd113c70f471f070

def z576 : W := mkw 0x0000000200020208 0x42c0030e00000e0c

def z577 : W := mkw 0x000004125032b2bd 0xfff1fffffc7fffff

def z578 : W := mkw 0x10445004c1045014 0x00001000c0007000

def z579 : W := mkw 0x0134fc000d2de000 0xa930fc000c0ff000

def z580 : W := mkw 0x00000010401010b4 0xff9110f0c47071fc

def z581 : W := mkw 0x0030a0000c090000 0x0020c000080e0000

def z582 : W := mkw 0xb076f3cfcd8f5f5e 0xffeed34ecb8e7e7c

def z583 : W := mkw 0x023ffbeda0000000 0x007fefbf30000000

def z584 : W := mkw 0xb04203cfc0821f5e 0x42c003cfc0000fff

def z585 : W := mkw 0xc0bf53f48ed00de0 0xfeffd3fecff00ff0

def z586 : W := mkw 0xc28203fda0900de0 0x42c003fff0000ff0

def z587 : W := mkw 0x0239aaa920000000 0x0000000000000000

def z588 : W := mkw 0x904450024186565c 0xbdaed0000b8e7e7c

def z589 : W := mkw 0x023ffbefa0020208 0xfbfffffff80e0e0c

def z590 : W := mkw 0x2000069b5032bbbf 0xffd13ffff471ffff

def z591 : W := mkw 0xc0bf53f00fd44de0 0xfdbfd3f00ffe7ff0

def z592 : W := mkw 0x0000000000000000 0xfb913cf1f401818f

def z593 : W := mkw 0x8006514480800440 0xfeeed34ecb800e70

def z594 : W := mkw 0xe0bba3fb0edb0fea 0xdcffc3fe0ffe0ff0

def z595 : W := mkw 0x00000010501010b5 0xff8010f1f00071ff

def z596 : W := mkw 0x023ffbeda0000000 0x101f3cf1f0000000

def z597 : W := mkw 0x00000010001000a0 0x001100b004700180

def z598 : W := mkw 0x000004000020a000 0x14011c0000707000

def z599 : W := mkw 0x2000028b00020b0a 0x0040030e00000e00

def z600 : W := mkw 0x023ffbeda0000000 0x7a6ed34ec0000000

def z601 : W := mkw 0x2130a68b0f6feb0a 0xeff0e38f0fffff8f

def z602 : W := mkw 0x2000028b00020b0a 0xebe0c38f080e0f8f

def z603 : W := mkw 0x000004105030b0b5 0x37013c71f071f07f

def z604 : W := mkw 0x000004105030b0b5 0x63803cf1f001f1ff

def z605 : W := mkw 0xc08b057052f0b4f5 0xff9f3cf1f7f1f1ff

def z606 : W := mkw 0x60b9a2bb0e5b0baa 0xebf1e3bf0c7f8f8f

def z607 : W := mkw 0x02020164a0000000 0x00000070f0000000

def z608 : W := mkw 0x000004105030b0b5 0x7e113cf1f0707070

def z609 : W := mkw 0x2030a28b0c0b0b0a 0x2350e08f040f818f

def z610 : W := mkw 0xc08000100ed00de0 0xdc9100f00ff00ff0

def z611 : W := mkw 0x2000029b50121bbf 0x42c003fff0000fff

def z612 : W := mkw 0x0139ac101e79a0a1 0x00112cb134718183

def z613 : W := mkw 0x0104fc00012de000 0xbd11fc00047ff000

def z614 : W := mkw 0x0104fc000f6de000 0xa500fc000ffff000

def z615 : W := mkw 0x917ffd56dffff6fd 0xffffffffffffffff

def z616 : W := mkw 0x914f5d44c3e4f454 0x140f1c40c3f07070

def z617 : W := mkw 0x000004000020a000 0xff913c810471f18f

def z618 : W := mkw 0x0239aaa920000000 0x6a71efbf30000000

def z619 : W := mkw 0x90465146c186565c 0x42eec34ecb8e0e7c

def z620 : W := mkw 0x904000024082165c 0x0080000000000e7c

def z621 : W := mkw 0xc0bb07f05ef0bdf5 0xdcbf1ff0fff07ff0

def z622 : W := mkw 0x90465144c1845454 0xff8e1040c380707c

def z623 : W := mkw 0xc0bb03e00ec00d40 0xdcae03400b800e70

def z624 : W := mkw 0x0000000040001014 0xff9030c1c401f1ff

def z625 : W := mkw 0x0000000200020208 0x81800000080e0e0c

def z626 : W := mkw 0xc28f5974a2d004e0 0x140f1c70f3f00070

def z627 : W := mkw 0x0000000000000000 0xdc80004000000070

def z628 : W := mkw 0x013dfc000f6de000 0x2111fc00047ff000

def z629 : W := mkw 0x0130a4000f6de000 0xad30e0000ffff000

def z630 : W := mkw 0x000004101030a0a1 0x0000000004718183

def z631 : W := mkw 0x0239aaa920000000 0x7a113cf1f0000000

def z632 : W := mkw 0xc08203f000900de0 0xdcae03f00b800ff0

def z633 : W := mkw 0x60b9a2b90e5909a2 0x001120b104718183

def z634 : W := mkw 0xc08b057052f0b4f5 0x140f1c70f3f07070

def z635 : W := mkw 0x003df8000e400000 0xbc3ffc000ff00000

def z636 : W := mkw 0x0104fc00512df015 0x2300fc01f00ff00f

def z637 : W := mkw 0xb076f3cf8d8f4f4a 0xebfee38f0f8f8f8f

def z638 : W := mkw 0x01000400012de000 0x01000000000ff000

def z639 : W := mkw 0x0000000200020208 0x2340c00e000e000c

def z640 : W := mkw 0x00065144c0001014 0xffeed34ec000707c

def z641 : W := mkw 0xc0bb07f01ef0ade1 0xdcbf2ff13ff18ff3

def z642 : W := mkw 0x2104fc0b012fe20a 0x2340fc0f000ff00f

def z643 : W := mkw 0x0232a3eda0000000 0x6a70e3fff0000000

def z644 : W := mkw 0x223ffbefa0020b0a 0x7afffffff0000f8f

def z645 : W := mkw 0x0006514480000000 0x100e1040c0000000

def z646 : W := mkw 0x000d580000000000 0x100f1c0000000000

def z647 : W := mkw 0xb04653cfc1865f5e 0xffeed3cfcb8e7fff

def z648 : W := mkw 0x2000a00b0c0b0b0a 0xa3c0e00f0c0f8f8f

def z649 : W := mkw 0x937fffefefeff65c 0xfffffffffffffe7c

def z650 : W := mkw 0x917ff9468fcf4648 0x006ec30e0b8e0e00

def z651 : W := mkw 0xc08203f000900de0 0xdc9103f004700ff0

def z652 : W := mkw 0xc08000000ec00d40 0x000000000b800e00

def z653 : W := mkw 0xc0bb07f05ef0bdf5 0xddbf03f00ff1ffff

def z654 : W := mkw 0xc0bb03f00ed00de0 0x003f03b00ff00f80

def z655 : W := mkw 0x40b902a00e400900 0x0000000000000000

def z656 : W := mkw 0x003dfc105030b0b5 0xffbffcf1f471f1ff

def z657 : W := mkw 0x000203e000000000 0x400003f000000000

def z658 : W := mkw 0x000b016000000000 0x100f007000000000

def z659 : W := mkw 0xc080001002d004e0 0x0400000003f00070

def z660 : W := mkw 0x2030a28b0c0b0b0a 0x0070e38f0c0f8f83

def z661 : W := mkw 0x91465546cfeff65c 0xffeed34ecffffe7c

def z662 : W := mkw 0x9076f3cfc186565c 0xfffef3cfcb8e7e7c

def z663 : W := mkw 0x003002800c000900 0x0020030008000e00

def z664 : W := mkw 0x233fffefaf6feb0a 0xffffffffffffff8f

def z665 : W := mkw 0x2134fe8b0d2feb0a 0xebf0ff8f0c0fff8f

def z666 : W := mkw 0xc0bb03e00ec00d40 0x583f03f00b800e00

def z667 : W := mkw 0x020f5964a0000000 0x000e000000000000

def z668 : W := mkw 0x213dfe9b5f7ffbbf 0xffffffffffffffff

def z669 : W := mkw 0x003900000e400000 0x002e00000b800000

def z670 : W := mkw 0x0039000000000000 0x183f000000000000

def z671 : W := mkw 0x0030028000000000 0x4830038000000000

def z672 : W := mkw 0xc0bb03f002d004e0 0x5c3f03f003f00070

def z673 : W := mkw 0x2030a68b0c2bab0a 0xfff1ff8f0c7fff8f

def z674 : W := mkw 0x90465546c1a6f65c 0xffffff4ecffffe7c

def z675 : W := mkw 0x020002a920000000 0x000000b130000000

def z676 : W := mkw 0x0139ac000e69a000 0x9c3f2c000ff18000

def z677 : W := mkw 0x00000010501010b5 0x00800000000001ff

def z678 : W := mkw 0x223ffbefac0b0b0a 0x006ec30e080e0e00

def z679 : W := mkw 0x0000000000000000 0xa910200004018000

def z680 : W := mkw 0xb076f3cf8d8f4f4a 0x006ec30e0b8e0e00

def z681 : W := mkw 0x023ffbfdf01010b5 0x7afffffff00001ff

def z682 : W := mkw 0x0006514480000000 0x006ec30e00000000

def z683 : W := mkw 0x914f5d46c3e6f65c 0xffefdf4ecbfe7e7c

def z684 : W := mkw 0x90465144c1845454 0x7e6ed34ec3807070

def z685 : W := mkw 0x013dfc000f6de000 0x141f3c0007f1f000

def z686 : W := mkw 0x9046514681864648 0xebeec30e0b8e0e0c

def z687 : W := mkw 0xc08004105ef0bdf5 0x858000000ff1ffff

def z688 : W := mkw 0x020653eda0000000 0x7a6ed3fff0000000

def z689 : W := mkw 0x00000010501010b5 0xde9100f1f47001ff

def z690 : W := mkw 0x0030a6995030b0b5 0xfff1fffff471f1ff

def z691 : W := mkw 0x0000a00900000000 0x2240e00f00000000

def z692 : W := mkw 0x023babe920000000 0x583f2ff130000000

def z693 : W := mkw 0xc0bb03e00ec00d40 0xc8be03800f800f80

def z694 : W := mkw 0x90420146c082165c 0xdeee034ecb800e7c

def z695 : W := mkw 0xe1bffffb0fffefea 0xffffffff0fffffff

def z696 : W := mkw 0x0000000001044000 0x850000000b8e7000

def z697 : W := mkw 0x2232a3efac0b0b0a 0xebf0e3fffc0f8f8f

def z698 : W := mkw 0x000004105030b0b5 0x42912cf1f47181ff

def z699 : W := mkw 0x0006514481044000 0xff6ed34ecb8e7000

def z700 : W := mkw 0x020207fdf030b0b5 0xffd13ffff471f1ff

def z701 : W := mkw 0xb072a3cfcc8b1f5e 0xebf0e3cfcc0f8fff

def z702 : W := mkw 0x1244f80fe106521c 0x2340fc0ff00e700c

def z703 : W := mkw 0x40b906b05e70b9b5 0xff913cf1f471f1ff

def z704 : W := mkw 0x2030a29b5c1b1bbf 0xebf0e3fffc0f8fff

def z705 : W := mkw 0x2030a28b0c0b0b0a 0xc8f0c38e0c0e0f80

def z706 : W := mkw 0x2204f80fa00b020a 0x2340fc0ff00f800f

def z707 : W := mkw 0x2030a0020c0b0b0a 0xebf0e30e0c0f8f8f

def z708 : W := mkw 0x010d5c000f6de000 0x140f1c000bfe7000

def z709 : W := mkw 0x023ffffdf030b0b5 0x85eec30e0471f1ff

def z710 : W := mkw 0x800201424082165c 0xffeed34ecb8e7e7c

def z711 : W := mkw 0xc2bb03f4aed00de0 0xdcbf03f0fff00ff0

def z712 : W := mkw 0x023ffbeda0000000 0x325ffcfff0000000

def z713 : W := mkw 0x003df0000f4d4000 0xbd3ff0000ffff000

def z714 : W := mkw 0x023ffbeda0000000 0xfb7ffffff4018000

def z715 : W := mkw 0x000454000124e000 0xbd2fdc000bfe7000

def z716 : W := mkw 0x914004125ffff6fd 0x858000000fffffff

def z717 : W := mkw 0x0204faada0000000 0x2240fcbff0000000

def z718 : W := mkw 0x023babeda0000000 0x5a7f2ffff0000000

def z719 : W := mkw 0x233dfea92f6de902 0xbd3ffcb13ffff183

def z720 : W := mkw 0xd0c20176c09216fc 0x42c0037ec0000e7c

def z721 : W := mkw 0x924203fff09216fd 0x42c003fff0000fff

def z722 : W := mkw 0x023ffbeda0000000 0x7a7ffffff4018183

def z723 : W := mkw 0xc0bba3f90ed00de0 0xfefffffffff00ff0

def z724 : W := mkw 0x223ffbedac090902 0xfbfffffff401818f

def z725 : W := mkw 0xc284f81daed00de0 0xa6c0fc0ffff00ff0

def z726 : W := mkw 0x023ffbeda1044000 0x7a7ffffffb8e0000

def z727 : W := mkw 0xc08900100ed00de0 0x948f00000ff00ff0

def z728 : W := mkw 0x50fd52b6cf565bbc 0x2351d0bec47e718c

def z729 : W := mkw 0x013df8105f5d50b5 0x42aec0f1fb8e01ff

def z730 : W := mkw 0xc0bb03f00ed00de0 0xfebf23f10ff00ff0

def z731 : W := mkw 0xc0bb03e00ec00d40 0xdcbf03400ff00e70

def z732 : W := mkw 0x013dfc000f6de000 0xfd3ffcf00ffff000

def z733 : W := mkw 0x10445406d126f21d 0x2340d00ec00ff00f

def z734 : W := mkw 0x90465146c186565c 0xc7eec34ecb8e7e7c

def z735 : W := mkw 0x2030a28b0c0b0b0a 0x81f0e38f0c0f8f8f

def z736 : W := mkw 0xc0bba3f90ed90de0 0xffffe3ff0fff8ff0

def z737 : W := mkw 0xc2bb03f92ed00de0 0xdcbf03f13ff00ff0

def z738 : W := mkw 0x013dfc000f6de000 0xffbffcf1fffff18f

def z739 : W := mkw 0x020f5964a0000000 0x7a7ffffff0000000

def z740 : W := mkw 0x023ffbeda0000000 0xfe7ffffff4700000

def z741 : W := mkw 0x2239aaab2c0b0b0a 0xebf0e38f0c0f8f8f

def z742 : W := mkw 0x003f53e480000000 0x7a7ffffff0000000

def z743 : W := mkw 0x013dfe800f6de000 0xfd3fff800ffff000

def z744 : W := mkw 0xc0bba3f90ed00de0 0xffffe3ff0ff18fff

def z745 : W := mkw 0xc08201500ed00de0 0xdcbf03f00ff00ff0

def z746 : W := mkw 0x0204f80da0000000 0x3241fc7ff0000000

def z747 : W := mkw 0x210d5e8b0366eb0a 0x56cf1f8f03f07f8f

def z748 : W := mkw 0xc186fff001bdede0 0x6180fff0000ffff0

def z749 : W := mkw 0xc0bb03f00ed00de0 0x54af03f00bf00ff0

def z750 : W := mkw 0x90465146c186565c 0x7e6ed34ecb8e7e70

def z751 : W := mkw 0xc08b01700ed00de0 0xdc9f00f00ff00ff0

def z752 : W := mkw 0x030207edaf6de000 0xc74003fffffff000

def z753 : W := mkw 0x000004105030b0b5 0xffbf3cf1fff1f1ff

def z754 : W := mkw 0x210004125f7ffbbf 0x858000000fffffff

def z755 : W := mkw 0xc0bb03f00ed00de0 0x9c3f03700ff00e70

def z756 : W := mkw 0x9046555691b6e6e9 0x007fefbf3fff8f83

def z757 : W := mkw 0xc08b017002d00de0 0x148f007003f00ff0

def z758 : W := mkw 0xc08b03f002d00de0 0xdcaf03f00bf00ff0

def z759 : W := mkw 0xc0bb03f002d004e0 0xdcbf03f00bf00e70

def z760 : W := mkw 0x023ffbedaf444000 0xff7ffffffffe7000

def z761 : W := mkw 0x0206fbeda0000000 0x7a51fffff0000000

def z762 : W := mkw 0x0030a6995030b0b5 0xeff0e38f0471f1ff

def z763 : W := mkw 0x11445406c12ff21c 0x2340d00ec00ff00c

def z764 : W := mkw 0xc08b03f002d00de0 0x140f037003f00e70

def z765 : W := mkw 0x013904000f6de000 0xbd3f3c000ffff000

def z766 : W := mkw 0x003ba3e900000000 0x7a7ffffff0000000

def z767 : W := mkw 0xc2bb03fdaed00de0 0xdcff03fe0ff00ff0

def z768 : W := mkw 0xc0bba3f00ed90de0 0xdcbfc3f00ffe0ff0

def z769 : W := mkw 0x823ffbedaec00440 0xfefffffffff00e70

def z770 : W := mkw 0x823ffbeda0800440 0x7afffffff0000e70

def z771 : W := mkw 0x0200000da0000000 0x7a513cfff0000000

def z772 : W := mkw 0x0004500001044000 0xbd3fd0000ffe7000

def z773 : W := mkw 0x9279aaab6186565c 0x85912cb13b8e7e7c

def z774 : W := mkw 0x023ff96da0000000 0x3a7ffc7ff0000000

def z775 : W := mkw 0x90465146c186565c 0xffffffffff8fffff

def z776 : W := mkw 0x8006514481844440 0xffeed34ecb8e7e70

def z777 : W := mkw 0x0139ac000f6de000 0x9d3f2c000ffff000

def z778 : W := mkw 0x020f5beda0000000 0x7a5f3ffff0000000

def z779 : W := mkw 0x023ffbeda0000000 0x326fff7ff0000000

def z780 : W := mkw 0x013dfc000f6de000 0x213ffc000ffff000

def z781 : W := mkw 0xc08b017002d004e0 0x548f037003f00e70

def z782 : W := mkw 0x104004125136f2bd 0x85800000047ff1ff

def z783 : W := mkw 0x8002014000800440 0xdcbf03400ff00e70

def z784 : W := mkw 0xc2bb03fdaed00de0 0xfeff3ffffff00ff0

def z785 : W := mkw 0x90465146c186565c 0xefeec30e0b8e7e7c

def z786 : W := mkw 0x0232a3eda0000000 0x7a71fffff0000000

def z787 : W := mkw 0x020ff96da0000000 0x104fdc7ef0000000

def z788 : W := mkw 0x023ffbedac000900 0x7a7ffffff4000180

def z789 : W := mkw 0x023df80da0000000 0x7a7ffcfff0000000

def z790 : W := mkw 0xc2bbabf92ed00de0 0xfebf3ff1fff00ff0

def z791 : W := mkw 0xc0bb03f00ed00de0 0xfeffc3fe0ff00ff0

def z792 : W := mkw 0x0034f4000d2de000 0xbd3ffc000ffff000

def z793 : W := mkw 0x213dfe890f6de902 0xffbffc810ffff18f

def z794 : W := mkw 0xc08000100ed00de0 0x9cae00000ff00ff0

def z795 : W := mkw 0xe08ba17b02db06ea 0x374fe07f03ff807f

def z796 : W := mkw 0x013dfc000f6de000 0xbd2fdc000bfe7000

def z797 : W := mkw 0x0236fbeda0000000 0x6a70fffff0000000

def z798 : W := mkw 0x023b03eda0000000 0x7a7f3ffff0000000

def z799 : W := mkw 0x90465146c186565c 0x376ed34ecb8e7e7c

def z800 : W := mkw 0x2030a28b0c0b0b0a 0xfff0e3cf0c0f8fff

def z801 : W := mkw 0x010d5c000f6de000 0x850e00000ffff000

def z802 : W := mkw 0xc0bb03f00ed00de0 0xfcbf3ff00ff00ff0

def z803 : W := mkw 0x2030a28b0c0b0b0a 0xebf0e3fffc0f8f8f

def z804 : W := mkw 0xc0bb03f00ed00de0 0xffbf03f00ff00ffc

def z805 : W := mkw 0xc0bb03f00ed00de0 0xfebf13f0cff00ff0

def z806 : W := mkw 0x90465146c186565c 0xbd6ed34ecb8e7e70

def z807 : W := mkw 0x2030a28b0c0b0b0a 0xfbf0f3cfcc0f8f8f

def z808 : W := mkw 0x033dfeadaf6de000 0xbf7ffcbffffff000

def z809 : W := mkw 0x023ffbedac090000 0x7a7ffffff80e0000

def z810 : W := mkw 0x010454000f6de000 0x950e10000ffff000

def z811 : W := mkw 0xe0bba3f90ed90de2 0xfdbfe3f10fff8ff3

def z812 : W := mkw 0x020203eda0000000 0x42512ffff0000000

def z813 : W := mkw 0x2000028b0c0b0b0a 0xebe0c38f0c0f8f8f

def z814 : W := mkw 0x020f5964a0000000 0x524f1f7ef0000000

def z815 : W := mkw 0x90465146c186565c 0xfffed3cecf8e7ffc

def z816 : W := mkw 0x013dfc000f6de000 0xbf3ffc01fffff000

def z817 : W := mkw 0x023ffbedac000000 0xfa7ffffffc000000

def z818 : W := mkw 0x013dfc00036de000 0x3d3ffc0003fff000

def z819 : W := mkw 0xb076f3cdcd8d5d56 0x141e30c1c781f1f3

def z820 : W := mkw 0xc0bb03f00ed00de0 0x84bf03b00ff00ff0

def z821 : W := mkw 0x2030a28b0c0b0b0a 0xfff0f38f0c0fff8f

def z822 : W := mkw 0x023ffbeda2400000 0x7e7ffffff3f00000

def z823 : W := mkw 0xe0bba3f90ed90de2 0xfeffe3ff0ff18ff3

def z824 : W := mkw 0x90465146c186565c 0xfffef34ecf8ffe7c

def z825 : W := mkw 0x013dfe800f6de900 0xffbfff810fffff8f

def z826 : W := mkw 0xc0b203d00ed00de0 0xdcbe03c00ff00ff0

def z827 : W := mkw 0xd0c203f240921ffc 0x408003f000000ffc

def z828 : W := mkw 0xc0bba3f90ed00de0 0xdcffc3fe0ff00ff0

def z829 : W := mkw 0x013dfc000f6de000 0xfdbffc400ffff070

def z830 : W := mkw 0x0206fbeda0000000 0x7a6efffff0000000

def z831 : W := mkw 0xc2bba3fdaed00de0 0xfeffe3fffff00ff0

def z832 : W := mkw 0x033ffbeda3444000 0x7a7ffffff3800000

def z833 : W := mkw 0x0000000200020208 0xebe0c30e0c0f8f8f

def z834 : W := mkw 0x023ffbeda0000000 0x7a6fdf7ef0000000

def z835 : W := mkw 0x10445406d126f21d 0x2340dc0ef00e700c

def z836 : W := mkw 0x2000a00b000b020a 0xebf0e38f0c0f8f8f

def z837 : W := mkw 0x023ffbedac000900 0xfbfffffffc018f8f

def z838 : W := mkw 0xd0cf5574d3f4f4f5 0x140f1c70f3f07070

def z839 : W := mkw 0xe0bba3f90ed90de2 0xffbf23f10ff18fff

def z840 : W := mkw 0x010dfc000f6de000 0xb50ffc000ffff000

def z841 : W := mkw 0xc0bb03f00ed00de0 0x042e03000bf00e70

def z842 : W := mkw 0x0239aaada0000000 0x02512cbff0000000

def z843 : W := mkw 0xc0b902b00ed00de0 0x9cbf00b00ff00ff0

def z844 : W := mkw 0x0239aaa920000000 0x7a71fffff0000000

def z845 : W := mkw 0x803b01500ed004e0 0xdcbf03f00ff00ff0

def z846 : W := mkw 0x023ffbeda0000000 0x107ffffff0000000

def z847 : W := mkw 0x013df8000f4d4000 0xbd3fd0000ffe7000

def z848 : W := mkw 0x023dfaada0000000 0x6a71ffbff0000000

def z849 : W := mkw 0xc0bb03f00ed00de0 0xdcae03400ff00ff0

def z850 : W := mkw 0x803b03f0009004e0 0xdcbf03f00ff00ff0

def z851 : W := mkw 0x013d5c000f6de000 0x9d3f1c000ffff000

def z852 : W := mkw 0xc0bb03f00ed00de0 0x143f03f00ff00ff0

def z853 : W := mkw 0x020f5964a0000000 0x324fdc7ef0000000

def z854 : W := mkw 0x013dfc000f6de000 0xffbffc000ffff00c

def z855 : W := mkw 0x000004125032b2bd 0x858000000c7fffff

def z856 : W := mkw 0x823ffbedac800d40 0xfeffffffff800ff0

def z857 : W := mkw 0x9040041250b2b6fd 0x858000000471ffff

def z858 : W := mkw 0x220f5966ac0b0b0a 0x918f1c70fc0f8f8f

def z859 : W := mkw 0x917bad46ceebb65c 0x42d12f4ec4718e7c

def z860 : W := mkw 0xc0b900100ed00de0 0x84ae00000ff00ff0

def z861 : W := mkw 0x013dfc000f6de000 0xfdbffc800ffff180

def z862 : W := mkw 0xd0c20156c0921ffc 0x42c0034ec0000ffc

def z863 : W := mkw 0x033ffbeda10d4000 0x7a7ffffff00e0000

def z864 : W := mkw 0x90420156d09216fd 0x42c0037ef0000e7c

def z865 : W := mkw 0x904450024186565c 0xffeed30e0b8e7e7c

def z866 : W := mkw 0x803b03c00ec00d40 0xdcbf03c00ff00ff0

def z867 : W := mkw 0x023ffbeda0000000 0x6251fffff0000000

def z868 : W := mkw 0x2030a28b0c0b0b0a 0xebe0c30e0c0f8f8f

def z869 : W := mkw 0x823ffbeda1844440 0xfffffffffb8e7e70

def z870 : W := mkw 0x020f5beda0000000 0x104f1f7ef0000000

def z871 : W := mkw 0x914f5d54d3f4f4f5 0x140f1c70f3f07070

def z872 : W := mkw 0x003900000f444000 0x9d3f00000ffe7000

def z873 : W := mkw 0xc0bb01700ed00de0 0x9cbf00700ff00ff0

def z874 : W := mkw 0x010004000f6de000 0x9d2e00000ffff000

def z875 : W := mkw 0x000450024106521c 0xffeed34ecb8e7e7c

def z876 : W := mkw 0x2030a69b5c3bbbbf 0x1461df7ef87e7e70

def z877 : W := mkw 0xe08203fb50921fff 0x42c003fff0000fff

def z878 : W := mkw 0x11445c06c126f21c 0x2340dc0ec00e700c

def z879 : W := mkw 0xc0bb03f00ed00de0 0x949f00f00ff00ff0

def z880 : W := mkw 0x213dfc000f6de902 0xbd3ffc000ffff183

def z881 : W := mkw 0x013dfe890f6de900 0xffffff8f0fffff80

def z882 : W := mkw 0x90465146c186565c 0xffeeff4ffb8e7e7c

def z883 : W := mkw 0xc2bbabf92ed00de0 0xdcbf03f00ff00ff0

def z884 : W := mkw 0x90465146c186565c 0xffeef34fcb8ffe7f

def z885 : W := mkw 0xc0bb07e05ee0bd55 0x232e3f01fb81fe0f

def z886 : W := mkw 0x023ffbedae400000 0x7a7ffffffb800000

def z887 : W := mkw 0xc0bb03f00ed00de0 0xffbf3ff1fff18fff

def z888 : W := mkw 0x92465946e186565c 0xffeedf4efb8e7e7c

def z889 : W := mkw 0x223ffbeda0090002 0x7a7ffffff0018003

def z890 : W := mkw 0x023ffbeda0000000 0x587fdffef0000000

def z891 : W := mkw 0xc0bb01700ed004e0 0xdcbf03700ff00e70

def z892 : W := mkw 0xc0bba3f90ed00de0 0xdcbf23f10ff00ff0

def z893 : W := mkw 0xc08b01700ed00de0 0xdcaf03700ff00ff0

def z894 : W := mkw 0x023babeda0000000 0x7a513ffff0000000

def z895 : W := mkw 0xc08b03f00ed00de0 0xd48f03f00ff00ff0

def z896 : W := mkw 0x023f5beda0000000 0x5a7f1ffff0000000

def z897 : W := mkw 0x023ffbedae490000 0xff7fffffffff8000

def z898 : W := mkw 0xc0bb03f00ed00de0 0xdebf03f10ff00fff

def z899 : W := mkw 0x013dfc000f6de000 0xbd3ffc70fffff000

def z900 : W := mkw 0x1244fc0ff126f21d 0x2340fc0ff00ff00f

def z901 : W := mkw 0x80020150009004e0 0xdcaf03700bf00e70

def z902 : W := mkw 0x2030a28b0c0b0b0a 0x2370e38f0c0f8f8f

def z903 : W := mkw 0x000004105030b0b5 0xfff1fffff471f1ff

def z904 : W := mkw 0x013dfe890f6de000 0xffffff8f0ffff18f

def z905 : W := mkw 0xc0bb03f002d00de0 0x5cbf03f003f00ff0

def z906 : W := mkw 0x013dfe800f6de900 0xbd3ffc800ffff180

def z907 : W := mkw 0x033ffbedae490000 0x7a7ffffff0000000

def z908 : W := mkw 0x013dfc000f6de000 0xbf3ffc010ffff00f

def z909 : W := mkw 0x033ffbedaf4d4000 0xfb7fffffff8f8000

def z910 : W := mkw 0x023ffbeda0000000 0x227fffbff0000000

def z911 : W := mkw 0x9046514681864648 0xfdeed34e0b8e7e70

def z912 : W := mkw 0x2000a28b000b0b0a 0xebd0e38f040f8f8f

def z913 : W := mkw 0xc2bbabfdaed00de0 0xdeff2ffffff00ff0

def z914 : W := mkw 0x2030a28b0c0b0b0a 0xfbf1e3ff0c0f8f8f

def z915 : W := mkw 0xe0bba3f90ed90de2 0xdcbf03f00ff00ff0

def z916 : W := mkw 0xc0bb01500ed00de0 0xdcbf03400ff00ff0

def z917 : W := mkw 0x20000412503bb2bf 0x85800000047ff1ff

def z918 : W := mkw 0xb04203dfd0921fff 0x42c003fff0000fff

def z919 : W := mkw 0x033dfc0daf6de000 0xff7ffcfffffff000

def z920 : W := mkw 0x43b9aeb92e79a9a0 0x00112cb134718180

def z921 : W := mkw 0x033dfc092f6de000 0xbd3ffc013ffff000

def z922 : W := mkw 0x013dfc000f6de000 0xbd3ffc810ffff183

def z923 : W := mkw 0x010454000f6de000 0xbd3ffc000ffff000

def z924 : W := mkw 0x1344fc0fe12ff21c 0x2340fc0ff00ff00c

def z925 : W := mkw 0x020b0beda0000000 0x42410ffff0000000

def z926 : W := mkw 0x003dfc000124e000 0xbd3ffc000ffff000

def z927 : W := mkw 0x023ff964a0000000 0x7a7fff7ef0000000

def z928 : W := mkw 0x0139a4000f6de000 0xbd3fe0000ffff000

def z929 : W := mkw 0x2030a28b0c0b0b0a 0xebf1efbf3c0f8f8f

def z930 : W := mkw 0x2030a28b0c0b0b0a 0xfbf1ff8f0c0f8f8f

def z931 : W := mkw 0x90465146c186565c 0x63eed34ecb8e7e7c

def z932 : W := mkw 0x023ffbedac090000 0x7a7ffffff4018000

def z933 : W := mkw 0x023ffbeda0000000 0x626efffff0000000

def z934 : W := mkw 0x033ffbedaf4d4000 0xfe7ffffffffe0000

def z935 : W := mkw 0x2000a28b0c0b0b0a 0xe3c0e38f0c0f8f8f

def z936 : W := mkw 0x013dfc000f6de000 0xfdbfff000ffffe00

def z937 : W := mkw 0x90465146c186565c 0xdceed34ecb8e7e70

def z938 : W := mkw 0xc08b01700ed00de0 0x848e00000ff00ff0

def z939 : W := mkw 0x213dfe890f6de902 0xfdbfff810fffff83

def z940 : W := mkw 0xc2bffbedaec00d40 0xfe7ffffffff00e00

def z941 : W := mkw 0x2030a28b0c0b0b0a 0xebf0ff8ffc0f8f8f

def z942 : W := mkw 0xc0bb03f00ed00de0 0xfdbf23f00ff18ff0

def z943 : W := mkw 0x013dfc000f6de000 0x9c3fdc000ffe7000

def z944 : W := mkw 0x803b03e00ec00440 0xdcbf03f00ff00e70

def z945 : W := mkw 0x2030a28b0e4b0b0a 0xeff0e38f0fff8f8f

def z946 : W := mkw 0x2030a28b000b0b0a 0x6bf0e38f000f8f8f

def z947 : W := mkw 0xc0bba3f00ed90de0 0xdcbf23f00ff18ff0

def z948 : W := mkw 0x023ffbedac000900 0x7a7ffffff8000e00

def z949 : W := mkw 0x023ffbeda0000000 0xfbfffffff000000c

def z950 : W := mkw 0x203002820c0b0b0a 0xebf0c38e0c0f8f8f

def z951 : W := mkw 0xc08b01700ed00de0 0x140f00700bf00e70

def z952 : W := mkw 0x000004105030b0b5 0x37113cf1f471f1ff

def z953 : W := mkw 0x023ffbeda0000000 0xff7ffffff0007000

def z954 : W := mkw 0x013dfc000f6de000 0x952fdc000ffff000

def z955 : W := mkw 0x013dfc000f6de000 0x3c3ffc000bfe7000

def z956 : W := mkw 0xc0bba3f00ed00de0 0xfcbfe3f00ff00ff0

def z957 : W := mkw 0x013d5c000f64e000 0xbd3fdc000ffe7000

def z958 : W := mkw 0x000004105030b0b5 0x56913cf1f471f1ff

def z959 : W := mkw 0x013904000f6de000 0x852e00000ffff000

def z960 : W := mkw 0x023ffbeda0000900 0x7afffffff0000f80

def z961 : W := mkw 0x013dfc000f6de000 0xff3ffc40cffff000

def z962 : W := mkw 0x013dfe890f6de000 0xff7ffffffffff000

def z963 : W := mkw 0x0000028900000000 0x7a513ffff0000000

def z964 : W := mkw 0xf0c203ffc0921ffe 0x42c003ffc0000fff

def z965 : W := mkw 0x213dfc090f6de002 0xbd3ffc010ffff003

def z966 : W := mkw 0x013dfc000f6de000 0x352ffc000bfff000

def z967 : W := mkw 0xc08201500ed00de0 0x84ae03000ff00ff0

def z968 : W := mkw 0x000004105030b0b5 0xffb13ff1fc71ffff

def z969 : W := mkw 0x2030a28b0c0b0b0a 0x63e0e38f080f8f8f

def z970 : W := mkw 0xd0c203f6d0921ffd 0x42c003fff0000fff

def z971 : W := mkw 0x223ffbeda0000902 0x7a7ffffff0000183

def z972 : W := mkw 0x000004105030b0b5 0x95913cf1f471f1ff

def z973 : W := mkw 0xc0bb03f00ed00de0 0xfdbf13f00ff07ff0

def z974 : W := mkw 0x020f5964a0000000 0x106fdf7ef0000000

def z975 : W := mkw 0x023ffbeda0000000 0x7b7ffffff001800f

def z976 : W := mkw 0x010454000364e000 0xbd2ed0000bfe7000

def z977 : W := mkw 0x0202abeda0000000 0x42402ffff0000000

def z978 : W := mkw 0x90465146c186565c 0xffffd34ecffe7e7c

def z979 : W := mkw 0x013dfe800f6de900 0xbd3fff000ffffe00

def z980 : W := mkw 0x013dfc000364e000 0xbd3ffc000bfe7000

def z981 : W := mkw 0xc08b017002d004e0 0xdcbf03f00ff00ff0

def z982 : W := mkw 0x000004105030b0b5 0xffb1fcf1fc7ff1ff

def z983 : W := mkw 0x2139ae991e79a9a3 0x00112cb134718183

def z984 : W := mkw 0x003002820c020b08 0xebf0e38f0c0f8f8f

def z985 : W := mkw 0xe08004125efbbfff 0x858000000fffffff

def z986 : W := mkw 0x023ffbeda0000000 0x387fff7ef0000000

def z987 : W := mkw 0x90465146c186565c 0xffefdf7efb8e7e7c

def z988 : W := mkw 0x0234fa8da0000000 0x7a71fffff0000000

def z989 : W := mkw 0xc0b902900ed00de0 0xdcbf03800ff00ff0

def z990 : W := mkw 0xc08203f000900de0 0xdcbf03f00ff00ff0

def z991 : W := mkw 0x90465146c186565c 0xffeed34ecf8fffff

def z992 : W := mkw 0xc2bffbedaec00d40 0xfaffffffff800f80

def z993 : W := mkw 0x010d5c000f6de000 0xbd2fdc000ffff000

def z994 : W := mkw 0x023ffbeda0000000 0xfafffffff8000e00

def z995 : W := mkw 0x033dfea92f6de000 0xff7fffbf3ffff000

def z996 : W := mkw 0x013d54000f6de000 0xbd3fd0000ffff000

def z997 : W := mkw 0x013dfc000f6de000 0x853fec000ffff000

def z998 : W := mkw 0x927ffbeda1844440 0x7a7ffffff3800000

def z999 : W := mkw 0x023ffbedae400000 0x7a7ffffff4700000

def z1000 : W := mkw 0x033dfe8daf6de000 0xff7fff8ffffff000

def z1001 : W := mkw 0x90465146c186565c 0xffeed3cfcb8e7fff

def z1002 : W := mkw 0x2030a28b0c0b0b0a 0xc9f0c38e0c0f8f8f

def z1003 : W := mkw 0x2030a28b0c0b0b0a 0xfffee38f0f8f8f8f

def z1004 : W := mkw 0x2039a28b0e4b0b0a 0xebf1e38f0c7f8f8f

def z1005 : W := mkw 0x033dfc202f6de000 0xbd3ffc303ffff000

def z1006 : W := mkw 0x013dfc000f6de000 0x9d3fc0000ffff000

def z1007 : W := mkw 0x023dfaada0000000 0x7a51fcfff0000000

def z1008 : W := mkw 0x0204f80da0000000 0x2251fcbff0000000

def z1009 : W := mkw 0x033dfc04af6de000 0xbd3ffc00fffff000

def z1010 : W := mkw 0x020653eda0000000 0x7a7ffffff0000000

def z1011 : W := mkw 0x2030a28b0c0b0b0a 0xa9f0e30e0c0f8f8f

def z1012 : W := mkw 0xc2bb0bf02ed00de0 0xdcbf0ff03ff00ff0

def z1013 : W := mkw 0xe0bb03f90ed00de2 0xdcbf03f10ff00ff3

def z1014 : W := mkw 0x033dfea92f6de000 0xbd3ffc000ffff000

def z1015 : W := mkw 0x033dfc0daf6de000 0xbd7ffc0e0ffff000

def z1016 : W := mkw 0x0206f94da0000000 0x7a7ffffff0000000

def z1017 : W := mkw 0x0000000000000000 0x7a71fffff0000000

def z1018 : W := mkw 0x823ffbeda0800440 0x7a7ffffffb800e00

def z1019 : W := mkw 0x010dfc00036de000 0xbd2ffc000bfff000

def z1020 : W := mkw 0xc0bb03f00ed00de0 0xdcbf2ff13ff00ff0

def z1021 : W := mkw 0xc0bb03f00ed00de0 0x94af03700ff00ff0

def z1022 : W := mkw 0xc0bb03f00ed00de0 0xdebf03f1fff00ff0

def z1023 : W := mkw 0x2139aa8b0e4b0b0a 0xebf0e38f0c0f8f8f

def z1024 : W := mkw 0x80020150009004e0 0xdcae03400ff00ff0

def z1025 : W := mkw 0x0206f96da0000000 0x2240fc7ff0000000

def z1026 : W := mkw 0x003ff94480000000 0x7a7ffffff0000000

def z1027 : W := mkw 0x3044f40fd12ff21f 0x2340fc0ff00ff00f

def z1028 : W := mkw 0x020ff96da0000000 0x7a5ffcfff0000000

def z1029 : W := mkw 0x2230a2ab2c0b0b0a 0xebf0e3bf3c0f8f8f

def z1030 : W := mkw 0x0002014480000000 0x7a513ffff0000000

def z1031 : W := mkw 0x003df8000f444000 0xbd3ffc000ffe7000

def z1032 : W := mkw 0x90465146c186565c 0xffeed3fffb8e7e7c

def z1033 : W := mkw 0x60b9a2ab0e4b0b0a 0xebf0e38f0c0f8f8f

def z1034 : W := mkw 0x033dfea92f6de000 0xff3ffcf1fffff000

def z1035 : W := mkw 0x2239aaab2c0b0b0a 0xfbf1fffffc0f8f8f

def z1036 : W := mkw 0x020ffbeda0000000 0x724ffffff0000000

def z1037 : W := mkw 0xc08201500ed00de0 0x948e00400ff00ff0

def z1038 : W := mkw 0x0204f80da0000000 0x6240fcfff0000000

def z1039 : W := mkw 0xc082015002d004e0 0xdcae03400bf00e70

def z1040 : W := mkw 0x003dfa8900000000 0x7a7ffffff0000000

def z1041 : W := mkw 0x023dfaada0000000 0x3a7ffcbff0000000

def z1042 : W := mkw 0x023ffbedac090900 0xfbfffffffc0f8f80

def z1043 : W := mkw 0x010d5c000364e000 0x350fdc0003fe7000

def z1044 : W := mkw 0x2104fc0b512ff21f 0x2340fc0ff00ff00f

def z1045 : W := mkw 0xc0bb03f00ed00de0 0x549f03f007f00ff0

def z1046 : W := mkw 0x023babeda0000000 0x6a71effff0000000

def z1047 : W := mkw 0x1144fc02412ff21c 0x2100fc00000ff00c

def z1048 : W := mkw 0x823ffbeda0800440 0x7e7ffffff3800070

def z1049 : W := mkw 0x10445406c126f21c 0x2340fc0ec00ff00c

def z1050 : W := mkw 0xc0bba3f00ed90de0 0xffbfe3f10fff8fff

def z1051 : W := mkw 0xc08b03f002d00de0 0xdc9f03f007f00ff0

def z1052 : W := mkw 0x0104fc000f6de000 0xbd2efc000ffff000

def z1053 : W := mkw 0x2000a00b0c0b0b0a 0xebe0e30f0c0f8f8f

def z1054 : W := mkw 0xc0bb03f00ed00de0 0xc4ae03f00ff00ff0

def z1055 : W := mkw 0x000454000124e000 0xbd2ed0000ffff000

def z1056 : W := mkw 0x020203eda0000000 0x62403ffff0000000

def z1057 : W := mkw 0x023ffbeda1044000 0x7b7ffffff00e7000

def z1058 : W := mkw 0x0134f4000f6de000 0xbd3ef0000ffff000

def z1059 : W := mkw 0xc0bb03f00ed00de0 0xdcbf23f10ff18ff3

def z1060 : W := mkw 0xe2bbabf92ed90de2 0xdcbf2ff13ff18ff3

def z1061 : W := mkw 0xd2c203ffe0921ffc 0x42c003fff0000ffc

def z1062 : W := mkw 0xc0bb03f48ed00de0 0xdeff03fecff00ff0

def z1063 : W := mkw 0x010d5c00036de000 0x150f1c0003fff000

def z1064 : W := mkw 0x90465146c186565c 0x56eed34ecb8e7e7c

def z1065 : W := mkw 0xc2bffbeda0800d40 0x7a7ffffff0000e00

def z1066 : W := mkw 0x010d5c000364e000 0x142fdc000bfe7000

def z1067 : W := mkw 0x200004125032bbbf 0x858000000471ffff

def z1068 : W := mkw 0x013dfe890f6de000 0xbd7fff0e0ffff000

def z1069 : W := mkw 0xc08b017002d004e0 0x142f03700bf00e70

def z1070 : W := mkw 0x2039a28b0c0b0b0a 0xfbffe38f0c0f8f8f

def z1071 : W := mkw 0x010d5c000364e000 0xbd3ffc000ffff000

def z1072 : W := mkw 0x2030a28b0c0b0b0a 0xfff1e38f0c7f8f8f

def z1073 : W := mkw 0x2039a28b0e4b0b0a 0xebfee38f0f8f8f8f

def z1074 : W := mkw 0x60b9a6b91e79a9a3 0x00112cb134718183

def z1075 : W := mkw 0x023ffbeda0000000 0xfb7ffffff80e0000

def z1076 : W := mkw 0x013dfc000f6de000 0xbd3ffcb13ffff000

def z1077 : W := mkw 0xc2bffbeda2c00440 0x7a7ffffff3800000

def z1078 : W := mkw 0x90420156c09216fc 0x42c003fec0000ffc

def z1079 : W := mkw 0x010d5c000f6de000 0xbd1f3c000ffff000

def z1080 : W := mkw 0x013dfe890f6de000 0xbd3ffc810ffff000

def z1081 : W := mkw 0xc0bb03f90ed00de0 0xdeff03ff0ff00ff0

def z1082 : W := mkw 0x020df82da0000000 0x2241fc3ff0000000

def z1083 : W := mkw 0x904201424186565c 0xffeec34e0b8e7e7c

def z1084 : W := mkw 0x2030a28b0c0b0b0a 0x42f0e38f0c0f8f8f

def z1085 : W := mkw 0x2030a28b0c0b0b0a 0xc3e0c38f0c0f8f8f

def z1086 : W := mkw 0x023ffbeda0000000 0x7afffffff000018f

def z1087 : W := mkw 0x90465146d186565d 0xffeed34ffb8e7e7f

def z1088 : W := mkw 0xc1bbabf00ed90de0 0xdcbf03f00ff00ff0

def z1089 : W := mkw 0x020ff96da0000000 0x7a6fff7ff0000000

def z1090 : W := mkw 0x023f5be4a0000000 0x7a7fdffef0000000

def z1091 : W := mkw 0xc0bb03f00ed00de0 0xdcbf1ff0fff00ff0

def z1092 : W := mkw 0x013dfc090f6de000 0xbf7ffc0f0ffff000

def z1093 : W := mkw 0xc0bb03f00ed00de0 0x40bf03f00ff00ff0

def z1094 : W := mkw 0xc0bb03f00ed00de0 0x9cbf03000ff00ff0

def z1095 : W := mkw 0xd0c004125ff6fffd 0x858000000fffffff

def z1096 : W := mkw 0x013dfc000f6de900 0xbdbffc000fffff80

def z1097 : W := mkw 0x010d5c000364e000 0x950f1c000bfe7000

def z1098 : W := mkw 0x2030a28b0c0b0b0a 0xa3e0e30f0c0f8f8f

def z1099 : W := mkw 0x023ffbeda1044000 0x7e7ffffff3807000

def z1100 : W := mkw 0xc0bb03f00ed00de0 0x5c3f03f00bf00e70

def z1101 : W := mkw 0xc08b017002d004e0 0x948f00700bf00e70

def z1102 : W := mkw 0x90465146c186565c 0x95eed34ecb8e7e7c

def z1103 : W := mkw 0x90465554d1b4f4f5 0x140e1040c3f07070

def z1104 : W := mkw 0x8006514201864648 0xffeed34e0b8e7e7c

def z1105 : W := mkw 0xc3bffbedafcd4d40 0x7a7ffffffb8e0e00

def z1106 : W := mkw 0x003902900e5009a0 0xdcbf03f00ff00ff0

def z1107 : W := mkw 0x0030a28b00020208 0xebf0e38f0c0f8f8f

def z1108 : W := mkw 0x0006514480000000 0x7a6fdf7ef0000000

def z1109 : W := mkw 0x3144fc0fc12ff21e 0x2340fc0fc00ff00f

def z1110 : W := mkw 0x013dfc000f6de000 0x351ffc0007fff000

def z1111 : W := mkw 0x0004500480000000 0x7a51fcfff0000000

def z1112 : W := mkw 0x023ffbeda0000000 0xfefffffff0000070

def z1113 : W := mkw 0xc0bb03f00ed90de0 0xddbf03f00fff8ff0

def z1114 : W := mkw 0x800b014002c00440 0xdcaf03400bf00e70

def z1115 : W := mkw 0x013dfc000f6de000 0xbdbffc000ffff18f

def z1116 : W := mkw 0x013dfc000f6de000 0xa52efc000ffff000

def z1117 : W := mkw 0x2230aa8b2c0b0b0a 0xebf0ef8f3c0f8f8f

def z1118 : W := mkw 0xc0bb03f00ed00de0 0xccbe03800ff00ff0

def z1119 : W := mkw 0xc0bb03f00ed00de0 0xddbf03f00ff18fff

def z1120 : W := mkw 0x023ffbeda0000000 0xfe7ffffffb800000

def z1121 : W := mkw 0x013dfc000f6de000 0xff7fff0e0ffff000

def z1122 : W := mkw 0x213dfe890f6de902 0xbd3ffc000ffff000

def z1123 : W := mkw 0x013dfc000f6de000 0xbd2ed0000ffff000

def z1124 : W := mkw 0x010454000f6de000 0x852ec0000ffff000

def z1125 : W := mkw 0x0039a4000e69a000 0xbd3ffc000ffff000

def z1126 : W := mkw 0xc0bb03f00ed00de0 0xfdbfc3f00ffe0ff0

def z1127 : W := mkw 0x200000020c0b0b0a 0xebf0e38f0c0f8f8f

def z1128 : W := mkw 0x013dfc000f6de000 0x143ffc000ffff000

def z1129 : W := mkw 0xc2bffbedaec00d40 0xfefffffffb800e70

def z1130 : W := mkw 0xc2bbabf92ed00de0 0xfeffefff3ff00ff0

def z1131 : W := mkw 0x2039aa8b0c0b0b0a 0xebf1ef8f0c0f8f8f

def z1132 : W := mkw 0x000d500003444000 0xbd2fd0000bfe7000

def z1133 : W := mkw 0x800201400ec00440 0xdcae03400ff00e70

def z1134 : W := mkw 0x020f5beda0000000 0x7a6fdffff0000000

def z1135 : W := mkw 0x0000a00900000000 0x7a51fcfff0000000

def z1136 : W := mkw 0x803900000ec00440 0x9cbf00000ff00e70

def z1137 : W := mkw 0x013dfc048f6de000 0xbf7ffc0ecffff000

def z1138 : W := mkw 0x90465146c186565c 0xbdeed30e0b8e7e7c

def z1139 : W := mkw 0x013dfc000f6de000 0xff3ffc810ffff000

def z1140 : W := mkw 0x020f596da0000000 0x124f1c7ff0000000

def z1141 : W := mkw 0x013dfea00f6de000 0xbd3ffcb00ffff000

def z1142 : W := mkw 0xc0b900100ed00de0 0xdcbf00f00ff00ff0

def z1143 : W := mkw 0x42bffbedae400900 0x7a7ffffff0000000

def z1144 : W := mkw 0x803203d00c900de0 0xdcbf03f00ff00ff0

def z1145 : W := mkw 0x020203eda0000000 0x52411ffff0000000

def z1146 : W := mkw 0x223ffbedac090902 0xfb7ffffffc0f8183

def z1147 : W := mkw 0x1144fc06d12ff21d 0x2340fc0ff00ff00f

def z1148 : W := mkw 0x0104fc00012de000 0xbd3ffc000ffff000

def z1149 : W := mkw 0x92465166e186565c 0xffeed37efb8e7e7c

def z1150 : W := mkw 0x90465146c186565c 0xffffff4ecb8e7e7c

def z1151 : W := mkw 0xc0bb03f01ed00de1 0xdcbf03f13ff00ff3

def z1152 : W := mkw 0x033ffbedaf4d4000 0xff7ffffffb8e7000

def z1153 : W := mkw 0x61b9aeb90e79a9a2 0x00112cb104718183

def z1154 : W := mkw 0xc0bb03f00ed00de0 0xdcaf03700bf00e70

def z1155 : W := mkw 0x000450000f444000 0xbd2ed0000ffe7000

def z1156 : W := mkw 0x924f5d74f1b4f4f5 0x140f1c70f3f07070

def z1157 : W := mkw 0x010dfc00036de000 0x140fdc0003fe7000

def z1158 : W := mkw 0x013dfc000f6de000 0x042ec0000bfe7000

def z1159 : W := mkw 0x02065beda0000000 0x42401ffff0000000

def z1160 : W := mkw 0x023ffbedae400900 0xfefffffffff00f80

def z1161 : W := mkw 0x023ffbeda0000000 0x526fdffff0000000

def z1162 : W := mkw 0x0030a0020c0b0208 0xebf0e38f0c0f8f8f

def z1163 : W := mkw 0x2000028b00020b0a 0xebf0e38f0c0f8f8f

def z1164 : W := mkw 0x023ffbeda0000000 0x525f3ffff0000000

def z1165 : W := mkw 0x200000020c0b0b0a 0xfb913cf1fc0f8f8f

def z1166 : W := mkw 0x010dfc00036de000 0xbd1ffc0007fff000

def z1167 : W := mkw 0x023ffbedac090000 0xfbfffffffc0f818f

def z1168 : W := mkw 0x013dfc000f6de000 0xad3ee0000ffff000

def z1169 : W := mkw 0xc08203f00ed00de0 0xdcae03f00ff00ff0

def z1170 : W := mkw 0x013dfc000f6de000 0x951f3c000ffff000

def z1171 : W := mkw 0x010904000f6de000 0x950f00000ffff000

def z1172 : W := mkw 0xc0bbabf00ed00de0 0xdcbf2ff00ff00ff0

def z1173 : W := mkw 0x90465146c186565c 0xffffd3fecb8e7e7c

def z1174 : W := mkw 0x90465146c186565c 0xa7eed30ecb8e7e7c

def z1175 : W := mkw 0x000004105030b0b5 0x63913cf1f471f1ff

def z1176 : W := mkw 0x2039a2ab0c0b0b0a 0xebf1e3bf0c0f8f8f

def z1177 : W := mkw 0x223ffbedac090902 0x7a7ffffff0000000

def z1178 : W := mkw 0x200000020c0b0b0a 0x81e0c30e0c0f8f8f

def z1179 : W := mkw 0x2000a28b000b0b0a 0xebe0e38f080f8f8f

def z1180 : W := mkw 0x213dfe890f6de902 0xff7fff8f0ffff183

def z1181 : W := mkw 0x023ffbedad0d4000 0xff7fffffff8ff000

def z1182 : W := mkw 0x023ffbeda0000000 0x427feffff0000000

def z1183 : W := mkw 0x41bdfea00f6de900 0xbd3ffc000ffff000

def z1184 : W := mkw 0x013dfc001f6de001 0xbd3ffc013ffff003

def z1185 : W := mkw 0x223ffbedac090902 0xfafffffffc018f83

def z1186 : W := mkw 0x023ffbeda0000000 0xfafffffff4000180

def z1187 : W := mkw 0x90465146c186565c 0xfffef3cfcb8e7e7c

def z1188 : W := mkw 0xb04004125dbfffff 0x858000000fffffff

def z1189 : W := mkw 0x9040041251b6f6fd 0x858000000bfe7e7c

def z1190 : W := mkw 0x90420156d09216fd 0x42c0034ec0000fff

def z1191 : W := mkw 0x003d54000f64e000 0xbd3ffc000ffff000

def z1192 : W := mkw 0x023ffbeda0090000 0x7b7ffffff00f8000

def z1193 : W := mkw 0x90465146c186565c 0xddeec34e0b8e7e7c

def z1194 : W := mkw 0x0036f3cd80000000 0x7a7ffffff0000000

def z1195 : W := mkw 0x2030a28b0c0b0b0a 0x63d0e38f040f8f8f

def z1196 : W := mkw 0x90465146c186565c 0x046ec30e0b8e7e70

def z1197 : W := mkw 0xe0bb03f00ed90de2 0xdcbf03f00ff18ff3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(1,[z6,z1,z2,z7,z4,z5]),(0,[z0,z8,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z10,z5]),(0,[z0,z1,z2,z11,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z5])],[(0,[z0,z1,z2,z3,z4,z13,z5]),(0,[z1,z14,z2,z15,z3,z4,z5]),(0,[z16,z1,z2,z3,z4,z17,z5]),(0,[z0,z1,z18,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z19])],[(0,[z20,z0,z1,z2,z3,z4,z5]),(0,[z0,z21,z1,z2,z3,z4,z22]),(0,[z0,z23,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z24,z5]),(0,[z0,z1,z2,z3,z4,z25,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(1,[z26,z1,z2,z3,z4,z27]),(0,[z28,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z29,z5])],[(0,[z0,z1,z2,z3,z4,z5,z30]),(0,[z0,z1,z2,z3,z31,z4,z5]),(0,[z0,z21,z1,z32,z3,z4,z5]),(0,[z0,z1,z2,z33,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z34,z35])],[(0,[z0,z36,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z37,z3,z4,z5])],[(0,[z38,z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z3,z4,z40,z5]),(0,[z0,z41,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z42,z4,z5]),(0,[z43,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z44,z4,z5]),(0,[z45,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z46,z5]),(0,[z0,z1,z2,z3,z4,z47,z5]),(0,[z0,z48,z1,z49,z3,z4,z5]),(0,[z0,z50,z2,z49,z3,z4,z5]),(0,[z0,z1,z2,z51,z3,z4,z5]),(0,[z0,z52,z1,z2,z3,z4,z5])],[(0,[z0,z1,z53,z2,z3,z4,z54]),(0,[z0,z55,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z56,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z57,z5])],[(0,[z58,z0,z59,z2,z3,z4,z5]),(0,[z58,z0,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z60,z3,z4,z5]),(0,[z0,z61,z1,z3,z62,z4,z5])],[(0,[z63,z0,z1,z2,z3,z4,z5]),(0,[z38,z0,z1,z2,z3,z64,z5]),(0,[z65,z0,z1,z2,z3,z4,z5]),(0,[z0,z66,z1,z67,z3,z4,z5]),(0,[z0,z1,z2,z3,z68,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z69]),(0,[z0,z70,z1,z71,z3,z4,z5])],[(0,[z72,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z2,z3,z4,z40,z73]),(0,[z0,z48,z74,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z75,z5])],[(0,[z0,z48,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z77]),(0,[z58,z0,z1,z53,z3,z4,z5]),(0,[z0,z1,z2,z3,z78,z4,z5]),(0,[z0,z1,z2,z79,z3,z4,z5]),(0,[z0,z1,z2,z80,z3,z4,z5]),(0,[z0,z74,z2,z49,z3,z4,z5])],[(0,[z81,z0,z1,z2,z3,z4,z5]),(0,[z0,z82,z1,z2,z3,z4,z5]),(1,[z0,z83,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z84,z5])]],
   [[(0,[z85,z0,z1,z2,z3,z4,z5])],[(0,[z58,z0,z1,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z87,z4,z5]),(0,[z0,z88,z1,z2,z3,z4,z5]),(0,[z0,z66,z1,z2,z3,z89,z5]),(0,[z90,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z91,z4,z5]),(0,[z0,z92,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z3,z4,z5])],[(0,[z0,z1,z94,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z95,z5]),(0,[z0,z2,z49,z3,z4,z96,z5])],[(0,[z1,z2,z3,z10,z4,z17,z5]),(0,[z97,z0,z1,z2,z3,z4,z5]),(0,[z0,z66,z2,z3,z98,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z99]),(0,[z100,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z101]),(0,[z0,z1,z2,z3,z102,z4,z103]),(0,[z0,z1,z104,z2,z3,z4,z5])],[(0,[z0,z105,z1,z2,z3,z4,z5]),(0,[z0,z1,z86,z49,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z106]),(0,[z0,z61,z1,z3,z4,z57,z5]),(1,[z0,z1,z2,z3,z4,z107]),(0,[z0,z1,z2,z108,z3,z4,z35])],[(0,[z109,z110,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z111,z3,z4,z40]),(0,[z0,z1,z2,z3,z112,z4,z5])],[(0,[z58,z0,z1,z2,z3,z4,z113]),(0,[z0,z1,z2,z3,z114,z4,z5]),(0,[z0,z1,z2,z3,z4,z96,z5]),(0,[z0,z1,z2,z3,z115,z4,z5]),(0,[z0,z1,z2,z111,z4,z40,z5])],[(0,[z0,z116,z1,z2,z3,z4,z5]),(0,[z117,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z118]),(0,[z0,z1,z2,z3,z119,z4,z5]),(0,[z0,z1,z2,z3,z4,z120,z5])]],
   [[(0,[z121,z0,z1,z2,z3,z4,z5]),(0,[z122,z0,z1,z49,z3,z4,z5]),(1,[z0,z1,z2,z4,z123,z5]),(0,[z0,z53,z2,z49,z3,z4,z5]),(0,[z0,z1,z2,z3,z124,z4,z5]),(0,[z0,z50,z1,z2,z3,z102,z4]),(0,[z0,z1,z2,z3,z4,z5,z125]),(0,[z0,z1,z2,z126,z4,z127,z5]),(0,[z0,z70,z1,z2,z3,z4,z103])],[(0,[z0,z21,z74,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z128,z4,z5]),(0,[z0,z1,z2,z3,z129,z4,z5])],[(0,[z0,z1,z2,z130,z3,z4,z5]),(0,[z131,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z132])],[(0,[z109,z0,z76,z2,z3,z4,z5]),(0,[z133,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z98,z4,z5])],[(0,[z0,z1,z134,z2,z3,z4,z5]),(0,[z135,z0,z1,z2,z3,z4,z5]),(0,[z136,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z137,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z138]),(0,[z0,z1,z2,z3,z126,z4,z5]),(0,[z0,z1,z2,z3,z4,z139,z5])],[(0,[z0,z1,z2,z3,z140,z4,z5])],[(0,[z0,z1,z2,z141,z3,z4,z5]),(0,[z0,z142,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z143,z4,z5]),(1,[z0,z74,z2,z33,z4,z5]),(0,[z0,z144,z74,z2,z3,z4,z5]),(0,[z0,z1,z2,z145,z3,z4,z5]),(0,[z146,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z147,z3,z127,z5])],[(0,[z0,z59,z1,z2,z3,z4,z5]),(0,[z16,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z148,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z73,z5,z149]),(0,[z0,z144,z1,z2,z3,z102,z4]),(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z151,z4,z5]),(0,[z0,z152,z1,z2,z3,z4,z5]),(0,[z0,z70,z153,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z154,z4,z5]),(0,[z0,z1,z2,z155,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z156])],[],[(0,[z0,z1,z157,z2,z3,z4,z5]),(1,[z110,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z15,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z158])],[(0,[z109,z0,z2,z3,z159,z4,z5]),(0,[z38,z0,z1,z2,z126,z4,z5]),(0,[z160,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z161,z3,z4,z5]),(0,[z0,z162,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z163,z103]),(0,[z0,z1,z2,z3,z164,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z35])],[(0,[z26,z0,z1,z2,z3,z4,z27]),(0,[z0,z66,z48,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z165,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z166]),(0,[z167,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z168,z3,z4,z5]),(0,[z0,z1,z2,z7,z3,z4,z5]),(0,[z0,z1,z67,z2,z3,z4,z5])],[(0,[z169,z0,z1,z2,z3,z4,z5]),(0,[z0,z170,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z171,z5]),(0,[z0,z1,z2,z3,z172,z4,z5]),(0,[z0,z173,z1,z2,z3,z4,z5]),(0,[z0,z1,z49,z3,z62,z4,z5]),(1,[z0,z61,z1,z3,z57,z5]),(0,[z0,z1,z2,z3,z102,z4,z158])]],
   [[(1,[z174,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z175,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z176]),(0,[z0,z1,z2,z3,z177,z4,z5]),(1,[z0,z1,z2,z178,z4,z5]),(0,[z0,z1,z2,z3,z179,z4,z5])],[(1,[z0,z1,z180,z3,z4,z5]),(0,[z0,z1,z181,z2,z3,z4,z5]),(0,[z0,z144,z1,z2,z3,z4,z158]),(0,[z182,z0,z1,z2,z3,z4,z5]),(1,[z0,z2,z183,z3,z4,z5])],[(0,[z58,z0,z1,z2,z3,z184,z5]),(0,[z0,z1,z2,z111,z98,z4,z5]),(0,[z0,z185,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z186,z4,z5]),(0,[z0,z187,z1,z2,z3,z4,z5])],[(0,[z0,z1,z188,z2,z3,z4,z5]),(0,[z38,z0,z189,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z190,z4,z5]),(0,[z0,z1,z71,z2,z3,z4,z5])],[(0,[z0,z1,z53,z191,z3,z4,z5]),(1,[z0,z1,z2,z192,z4,z5]),(0,[z0,z144,z1,z2,z3,z4,z166]),(0,[z0,z1,z86,z2,z3,z4,z163]),(0,[z0,z1,z2,z3,z193,z4,z5]),(0,[z0,z1,z2,z3,z112,z5,z35])],[(0,[z0,z1,z2,z3,z4,z194,z5]),(0,[z0,z1,z2,z195,z3,z4,z5]),(0,[z0,z196,z1,z2,z3,z4,z5])],[(0,[z197,z0,z1,z2,z3,z4,z5]),(0,[z0,z198,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z199,z3,z4,z5]),(0,[z0,z1,z2,z3,z200,z4,z5])],[(0,[z16,z65,z1,z2,z3,z4,z5]),(0,[z0,z201,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z183,z3,z4,z5]),(0,[z0,z1,z202,z2,z203,z4,z5]),(0,[z0,z1,z2,z3,z204,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z205,z4,z5]),(0,[z38,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z202,z2,z3,z9,z5])],[(0,[z58,z0,z1,z49,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z206]),(0,[z0,z1,z2,z3,z4,z207,z5])],[(0,[z208,z0,z1,z2,z3,z4,z5]),(0,[z0,z209,z1,z210,z3,z4,z5]),(0,[z0,z1,z2,z3,z211,z4,z5]),(0,[z0,z1,z2,z3,z212,z4,z5])],[(0,[z0,z1,z2,z3,z10,z57,z5]),(1,[z0,z1,z3,z213,z4,z5]),(0,[z0,z1,z2,z3,z214,z4,z5])],[(0,[z0,z215,z1,z2,z3,z4,z5]),(0,[z0,z1,z216,z2,z3,z4,z5]),(0,[z217,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z218,z5]),(0,[z0,z1,z2,z3,z4,z219,z5])],[(0,[z0,z1,z2,z3,z4,z220,z5]),(0,[z0,z221,z1,z2,z3,z4,z5]),(0,[z0,z21,z1,z2,z98,z4,z5]),(0,[z0,z1,z2,z3,z222,z4,z89])],[(0,[z0,z1,z2,z3,z10,z4,z5]),(0,[z0,z1,z2,z3,z223,z4,z5]),(0,[z224,z0,z1,z2,z3,z4,z27]),(1,[z0,z1,z225,z3,z4,z5]),(0,[z0,z1,z191,z49,z3,z4,z5]),(0,[z0,z226,z1,z2,z3,z4,z5]),(0,[z0,z1,z227,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z228,z4,z5]),(0,[z65,z0,z1,z2,z3,z10,z5]),(0,[z229,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z230]),(0,[z0,z1,z32,z2,z3,z4,z5]),(0,[z0,z66,z50,z2,z3,z4,z5]),(0,[z0,z231,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z108,z3,z112,z5])]],
   [[(0,[z110,z0,z76,z2,z3,z4,z5]),(0,[z0,z1,z232,z3,z233,z4,z5]),(0,[z0,z1,z2,z234,z3,z4,z5]),(0,[z0,z74,z1,z2,z98,z4,z5]),(0,[z0,z50,z1,z2,z108,z3,z4]),(0,[z0,z1,z235,z2,z3,z4,z5]),(1,[z0,z92,z2,z3,z4,z5])],[(0,[z0,z236,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z237,z5]),(0,[z0,z1,z2,z238,z3,z4,z5])],[(0,[z0,z1,z2,z239,z7,z4,z5]),(1,[z0,z1,z3,z223,z4,z5]),(0,[z0,z240,z1,z2,z3,z4,z5]),(0,[z0,z66,z88,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z241,z4,z5])],[(0,[z0,z1,z2,z242,z3,z4,z5]),(1,[z0,z1,z210,z3,z4,z5]),(0,[z0,z48,z209,z2,z3,z4,z5]),(1,[z0,z243,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z31,z4,z5]),(1,[z65,z1,z2,z3,z10,z5]),(0,[z0,z244,z1,z2,z3,z4,z5]),(0,[z0,z245,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z246,z5])],[(0,[z0,z1,z2,z247,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z118]),(0,[z0,z1,z2,z3,z4,z248,z5])],[(0,[z0,z249,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z250,z4,z5]),(0,[z0,z50,z2,z3,z4,z5,z166]),(1,[z0,z1,z251,z3,z4,z5])],[(0,[z65,z1,z2,z3,z10,z4,z5]),(0,[z0,z1,z2,z252,z3,z4,z5])],[(0,[z0,z1,z2,z3,z253,z4,z5]),(0,[z0,z254,z1,z2,z3,z4,z5]),(0,[z0,z144,z1,z2,z108,z3,z4]),(0,[z0,z162,z1,z2,z62,z4,z5])]],
   [[(0,[z0,z66,z2,z49,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z255,z5]),(0,[z0,z61,z1,z2,z3,z9,z5]),(1,[z0,z256,z2,z3,z4,z5])],[(0,[z0,z257,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z108,z3,z4]),(0,[z0,z1,z2,z33,z4,z5,z103]),(0,[z0,z50,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z258]),(0,[z0,z1,z2,z259,z3,z4,z5])],[(0,[z0,z74,z2,z3,z4,z5,z166]),(1,[z0,z260,z1,z3,z4,z163])],[(0,[z0,z1,z2,z3,z4,z261,z5]),(0,[z0,z1,z2,z262,z3,z4,z5]),(0,[z0,z21,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z62,z4,z5]),(0,[z0,z1,z2,z3,z263,z4,z5]),(0,[z0,z70,z1,z2,z111,z4,z5])],[(0,[z0,z1,z15,z3,z62,z4,z5]),(0,[z0,z1,z264,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z27,z163]),(0,[z0,z265,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z266,z4,z5]),(0,[z0,z1,z3,z4,z57,z5,z163]),(0,[z0,z1,z2,z3,z4,z267,z5])],[(0,[z6,z0,z1,z2,z7,z4,z5]),(0,[z0,z74,z1,z2,z3,z4,z5]),(0,[z268,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z269]),(1,[z0,z1,z270,z3,z4,z5]),(0,[z0,z1,z2,z3,z102,z4,z5])],[(0,[z0,z1,z2,z3,z126,z10,z5]),(0,[z0,z1,z2,z3,z271,z4,z5]),(0,[z0,z1,z202,z2,z3,z4,z248]),(0,[z0,z272,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z273,z1,z2,z3,z4,z5]),(1,[z16,z1,z2,z3,z17,z5]),(0,[z0,z274,z1,z2,z3,z4,z5]),(0,[z0,z144,z1,z2,z3,z4,z5]),(0,[z0,z1,z239,z3,z62,z4,z5]),(0,[z275,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z147,z3,z4,z276]),(0,[z0,z1,z2,z111,z3,z4,z103]),(0,[z0,z1,z2,z3,z4,z5,z277])],[(0,[z0,z278,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z279,z4,z5])],[(0,[z0,z74,z209,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z5]),(0,[z16,z0,z1,z2,z3,z10,z5]),(0,[z0,z280,z1,z2,z3,z4,z5]),(0,[z281,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z86,z191,z3,z4,z5]),(0,[z0,z202,z2,z183,z3,z4,z5]),(0,[z0,z70,z1,z2,z3,z4,z5])],[(0,[z0,z189,z1,z2,z3,z4,z5]),(0,[z282,z0,z1,z2,z3,z4,z5]),(0,[z0,z283,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z176]),(0,[z0,z284,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z285]),(0,[z0,z1,z2,z286,z3,z4,z5])],[(0,[z287,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z288,z5]),(0,[z0,z289,z1,z2,z3,z4,z5]),(0,[z0,z66,z74,z2,z3,z4,z5]),(0,[z0,z290,z1,z2,z3,z4,z5]),(0,[z0,z291,z1,z2,z3,z4,z5])],[(0,[z0,z209,z2,z3,z98,z4,z5])]],
   [[(0,[z0,z1,z2,z292,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z293,z5]),(1,[z0,z1,z86,z3,z4,z158])],[(1,[z0,z1,z67,z3,z4,z5]),(1,[z0,z162,z1,z62,z4,z5]),(1,[z0,z1,z2,z3,z4,z248]),(0,[z0,z1,z2,z3,z4,z294,z5])],[(0,[z0,z295,z1,z2,z3,z4,z5]),(0,[z122,z0,z1,z3,z4,z5,z163]),(0,[z0,z296,z1,z2,z3,z4,z5])],[(0,[z0,z1,z297,z2,z3,z4,z5])],[(0,[z0,z1,z2,z298,z3,z4,z5]),(0,[z0,z1,z2,z299,z3,z4,z5]),(0,[z0,z1,z2,z3,z300,z4,z5]),(0,[z0,z301,z1,z2,z3,z4,z5])],[(0,[z302,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z303,z4,z5]),(0,[z0,z1,z2,z304,z3,z4,z5])],[(0,[z305,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z306]),(0,[z0,z1,z2,z3,z307,z4,z5]),(0,[z0,z1,z2,z308,z3,z4,z5]),(0,[z0,z1,z309,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z310])],[(0,[z0,z1,z2,z311,z3,z4,z5]),(0,[z0,z1,z76,z2,z3,z4,z5]),(0,[z312,z0,z1,z2,z3,z4,z5]),(0,[z313,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z314,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z149]),(0,[z315,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z166,z103])]],
   [[(0,[z0,z316,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z317,z4,z5])],[],[(0,[z318,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z49,z3,z98,z4,z5]),(0,[z0,z66,z1,z2,z3,z159,z5])],[(0,[z319,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z149]),(0,[z0,z2,z49,z3,z159,z4,z5]),(0,[z0,z1,z53,z202,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z320]),(0,[z0,z66,z2,z3,z4,z89,z5]),(0,[z0,z321,z1,z2,z3,z4,z5])],[(0,[z0,z209,z1,z141,z3,z4,z5]),(0,[z1,z2,z7,z3,z233,z4,z5]),(1,[z0,z2,z3,z151,z4,z5]),(0,[z0,z322,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z323,z4,z5]),(0,[z0,z1,z2,z3,z4,z324,z5]),(0,[z0,z1,z2,z3,z102,z5,z35])],[(1,[z0,z66,z2,z3,z89,z5])],[(0,[z0,z1,z2,z3,z159,z4,z5]),(0,[z0,z325,z1,z2,z3,z4,z5]),(0,[z0,z326,z1,z2,z3,z4,z5])]],
   [[(0,[z327,z0,z1,z2,z3,z4,z5]),(0,[z0,z328,z1,z2,z3,z4,z5]),(0,[z329,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z330,z5]),(1,[z0,z50,z2,z3,z4,z166]),(0,[z0,z162,z1,z2,z3,z4,z118]),(0,[z0,z1,z86,z3,z4,z158,z5]),(0,[z0,z1,z2,z3,z331,z4,z5])],[(1,[z122,z1,z14,z3,z4,z5]),(0,[z0,z1,z2,z3,z332,z4,z17]),(0,[z0,z1,z2,z333,z3,z4,z5]),(1,[z0,z88,z2,z3,z159,z5]),(0,[z0,z1,z2,z334,z3,z4,z5])],[(0,[z0,z1,z2,z335,z3,z4,z5]),(0,[z0,z1,z2,z336,z3,z4,z5]),(0,[z0,z1,z2,z3,z337,z4,z5]),(0,[z0,z338,z1,z2,z3,z4,z5])],[(0,[z0,z2,z33,z3,z98,z4,z5]),(0,[z0,z1,z2,z3,z339,z4,z5]),(0,[z0,z340,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z341])],[(0,[z0,z257,z2,z3,z4,z17,z5]),(0,[z26,z0,z1,z2,z3,z102,z4]),(0,[z342,z0,z1,z2,z3,z4,z5])],[(0,[z110,z0,z209,z2,z3,z4,z5]),(0,[z0,z343,z1,z2,z3,z4,z5]),(1,[z0,z1,z141,z3,z4,z5]),(0,[z344,z0,z1,z2,z3,z4,z5]),(0,[z345,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z346,z3,z4,z17]),(0,[z0,z1,z347,z2,z3,z4,z5]),(0,[z0,z1,z49,z3,z4,z5,z163]),(0,[z0,z348,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z108,z3,z4,z40])],[(0,[z0,z1,z53,z2,z3,z4,z5]),(0,[z0,z1,z86,z2,z3,z4,z158]),(0,[z349,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z350,z5]),(0,[z0,z351,z1,z2,z3,z4,z5]),(0,[z0,z88,z1,z2,z3,z89,z5]),(0,[z0,z1,z2,z3,z352,z4,z5]),(1,[z0,z1,z155,z3,z4,z5]),(0,[z0,z353,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z354,z4,z5]),(0,[z0,z301,z2,z147,z3,z4,z5])]],
   [[(0,[z174,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z355,z2,z3,z4,z5])],[(1,[z0,z59,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z73,z5,z27])],[(1,[z0,z1,z2,z3,z4,z356]),(1,[z38,z1,z2,z233,z4,z5]),(0,[z0,z88,z2,z3,z159,z4,z5]),(0,[z0,z1,z3,z62,z4,z5,z163])],[(0,[z58,z0,z1,z3,z4,z5,z163]),(0,[z0,z1,z2,z3,z4,z27,z103]),(0,[z357,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z358,z5]),(0,[z0,z1,z2,z3,z359,z4,z5]),(0,[z0,z1,z2,z3,z4,z360,z5]),(0,[z0,z1,z2,z361,z3,z4,z5]),(1,[z0,z1,z3,z164,z4,z5])],[(0,[z58,z0,z1,z2,z3,z4,z362]),(0,[z122,z1,z14,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z0,z21,z1,z180,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z363,z5]),(0,[z0,z1,z2,z3,z4,z5,z364]),(0,[z0,z1,z2,z365,z3,z4,z5])],[(0,[z0,z50,z1,z2,z192,z4,z5])],[(0,[z0,z1,z2,z366,z3,z4,z5]),(0,[z0,z1,z3,z9,z4,z57,z5]),(1,[z0,z367,z2,z3,z4,z5]),(0,[z368,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z369,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z332,z4,z5]),(0,[z0,z1,z2,z3,z4,z158,z27]),(0,[z370,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z371,z5]),(0,[z0,z1,z2,z3,z372,z4,z5]),(0,[z0,z2,z3,z159,z4,z96,z5]),(1,[z0,z1,z361,z3,z4,z5])]],
   [[(0,[z373,z0,z1,z2,z3,z4,z5]),(0,[z0,z162,z1,z2,z239,z4,z5]),(0,[z0,z1,z191,z3,z4,z5,z163])],[(0,[z374,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z375,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z376]),(1,[z0,z1,z2,z3,z4,z377]),(0,[z0,z378,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z379,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z158,z40])],[(0,[z0,z1,z2,z380,z3,z4,z5]),(0,[z0,z1,z14,z3,z62,z4,z5]),(0,[z0,z381,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z382]),(0,[z0,z1,z2,z3,z4,z5,z383]),(1,[z0,z1,z202,z3,z9,z5]),(0,[z0,z1,z2,z3,z384,z4,z5]),(0,[z0,z1,z2,z108,z3,z4,z163]),(0,[z0,z1,z2,z385,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z276]),(0,[z0,z92,z2,z3,z4,z5,z35])],[(0,[z0,z1,z2,z346,z3,z4,z5]),(0,[z0,z386,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z27]),(0,[z0,z387,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z113]),(0,[z0,z1,z2,z3,z4,z5,z388]),(0,[z0,z1,z2,z3,z389,z4,z5])],[(0,[z0,z390,z1,z2,z3,z4,z5]),(0,[z224,z0,z1,z2,z3,z102,z4]),(0,[z0,z1,z2,z3,z4,z391,z5]),(0,[z0,z1,z2,z3,z4,z5,z392]),(0,[z0,z1,z2,z3,z4,z5,z393])],[(0,[z0,z1,z2,z3,z4,z394,z5]),(0,[z0,z1,z2,z3,z4,z395,z5])],[(0,[z0,z396,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z397,z1,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z96]),(0,[z0,z398,z1,z2,z3,z4,z5]),(0,[z0,z1,z399,z2,z3,z4,z5])],[(0,[z400,z0,z1,z2,z3,z4,z5]),(0,[z401,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z402,z3,z4,z5])],[(0,[z109,z209,z1,z2,z3,z4,z5]),(0,[z403,z0,z1,z2,z3,z4,z5]),(0,[z0,z404,z1,z2,z3,z4,z5]),(1,[z0,z1,z405,z3,z4,z5]),(0,[z0,z1,z225,z2,z3,z4,z5]),(0,[z0,z48,z1,z2,z3,z4,z5]),(0,[z0,z1,z86,z202,z3,z4,z5])],[(0,[z38,z0,z1,z2,z7,z4,z5]),(0,[z0,z296,z1,z53,z3,z4,z5]),(0,[z0,z260,z1,z2,z3,z4,z163]),(0,[z0,z1,z406,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z407]),(0,[z0,z1,z2,z408,z3,z4,z5]),(0,[z0,z1,z2,z111,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z409]),(1,[z0,z1,z2,z203,z4,z5]),(0,[z0,z1,z202,z3,z4,z5,z163])],[(0,[z0,z86,z2,z385,z3,z4,z5])],[(0,[z0,z1,z410,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z10,z127,z5]),(1,[z0,z321,z2,z3,z4,z5]),(0,[z0,z411,z1,z2,z3,z4,z5])],[(0,[z0,z144,z1,z2,z3,z4,z96]),(0,[z0,z1,z191,z2,z62,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z412,z4,z5]),(0,[z0,z413,z1,z2,z3,z4,z5]),(1,[z0,z1,z238,z3,z4,z5]),(0,[z414,z0,z1,z2,z62,z4,z5]),(0,[z0,z1,z2,z415,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z22,z5]),(0,[z0,z1,z2,z3,z4,z5,z163])],[(0,[z0,z1,z416,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z417,z4,z5]),(0,[z0,z367,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z418,z3,z4,z5]),(0,[z0,z419,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z123,z5])],[(0,[z0,z1,z202,z49,z3,z4,z5]),(1,[z0,z144,z2,z3,z4,z96]),(0,[z0,z1,z86,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z40,z5,z103])],[(0,[z0,z1,z2,z420,z3,z4,z5]),(0,[z0,z421,z1,z2,z3,z4,z5]),(0,[z0,z260,z1,z86,z3,z4,z5]),(0,[z0,z1,z2,z147,z126,z4,z5])],[(0,[z109,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z422,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z423]),(0,[z0,z1,z424,z2,z3,z4,z5]),(0,[z425,z0,z1,z2,z3,z4,z5]),(0,[z0,z426,z1,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z3,z184,z5]),(0,[z0,z1,z2,z3,z17,z57,z5]),(0,[z0,z74,z2,z33,z3,z4,z5]),(1,[z0,z1,z427,z3,z4,z5]),(0,[z0,z1,z428,z2,z3,z4,z5]),(0,[z0,z429,z1,z2,z3,z4,z5])],[(0,[z122,z0,z1,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z430,z5]),(1,[z0,z1,z2,z3,z431,z5]),(0,[z0,z1,z432,z2,z3,z4,z5]),(0,[z0,z61,z1,z191,z3,z4,z5]),(0,[z0,z1,z433,z2,z3,z4,z5])],[(0,[z434,z0,z1,z2,z3,z4,z5]),(0,[z0,z435,z1,z2,z3,z4,z5]),(0,[z224,z1,z2,z3,z4,z73,z5]),(0,[z0,z48,z2,z3,z4,z96,z5])],[(0,[z109,z0,z209,z2,z3,z4,z5]),(0,[z0,z1,z2,z436,z3,z4,z5]),(0,[z0,z1,z2,z49,z3,z4,z5]),(0,[z0,z21,z1,z2,z33,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z437])],[(0,[z26,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z98,z159,z4,z5]),(0,[z0,z438,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z439,z4,z5]),(0,[z0,z1,z2,z440,z3,z4,z5]),(0,[z0,z1,z270,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z441,z5])],[(0,[z109,z0,z66,z2,z3,z4,z5]),(0,[z0,z1,z2,z239,z233,z4,z5]),(0,[z0,z50,z144,z2,z3,z4,z5]),(0,[z0,z1,z2,z442,z3,z4,z5]),(0,[z0,z1,z2,z3,z102,z4,z35]),(0,[z0,z1,z2,z443,z3,z4,z5])]],
   [[(0,[z0,z1,z444,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z332,z4]),(0,[z0,z445,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z446]),(0,[z0,z21,z1,z2,z3,z4,z176]),(0,[z0,z2,z3,z4,z96,z5,z166]),(0,[z0,z1,z2,z447,z3,z4,z5]),(1,[z0,z297,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z5,z448]),(0,[z0,z1,z2,z3,z449,z4,z5])],[(0,[z450,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z451]),(0,[z452,z0,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z3,z4,z73]),(0,[z0,z1,z2,z453,z3,z4,z5]),(1,[z0,z1,z2,z111,z4,z40])],[(0,[z0,z1,z2,z3,z454,z4,z5]),(0,[z0,z1,z455,z2,z3,z4,z5]),(0,[z0,z419,z1,z3,z233,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z456])],[(0,[z0,z1,z2,z3,z4,z184,z5]),(0,[z224,z0,z1,z2,z108,z3,z4]),(0,[z0,z1,z2,z3,z4,z457,z5]),(0,[z458,z0,z1,z2,z3,z4,z5]),(0,[z0,z459,z1,z2,z3,z4,z5]),(0,[z0,z162,z1,z2,z3,z4,z377])],[(0,[z460,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z461]),(0,[z0,z462,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z463])],[(0,[z0,z1,z2,z4,z123,z17,z5]),(0,[z0,z1,z2,z3,z4,z73,z163]),(0,[z0,z1,z153,z2,z3,z4,z5])]],
   [[(0,[z0,z464,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z232,z3,z4,z5]),(0,[z0,z1,z2,z3,z465,z4,z5]),(0,[z0,z466,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z192,z4,z5]),(0,[z467,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z468,z4,z5]),(0,[z0,z1,z2,z3,z4,z127,z5]),(0,[z469,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z108,z3,z4,z103])],[(1,[z0,z1,z2,z31,z4,z5]),(0,[z0,z470,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z108,z3,z112])],[(0,[z38,z0,z1,z2,z3,z4,z356]),(0,[z0,z1,z2,z3,z471,z4,z5]),(0,[z0,z50,z2,z3,z159,z4,z5]),(0,[z0,z1,z2,z3,z4,z472,z5]),(0,[z0,z1,z2,z3,z4,z5,z473])],[(0,[z0,z474,z1,z2,z3,z4,z5]),(0,[z6,z0,z1,z2,z233,z4,z5]),(0,[z0,z21,z2,z3,z98,z4,z5]),(0,[z0,z1,z2,z3,z4,z475,z5]),(0,[z0,z144,z2,z3,z4,z96,z5]),(0,[z0,z1,z2,z3,z476,z4,z5]),(0,[z477,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z478,z4,z5])],[(0,[z0,z1,z2,z3,z479,z4,z5]),(0,[z0,z1,z2,z480,z3,z4,z5]),(0,[z0,z260,z1,z3,z4,z5,z163]),(0,[z0,z1,z2,z3,z4,z276,z5])],[(0,[z0,z1,z2,z3,z4,z481,z5]),(0,[z0,z1,z405,z2,z3,z4,z5]),(0,[z224,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z482,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z40,z27]),(1,[z224,z1,z2,z3,z4,z73]),(0,[z0,z1,z2,z483,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z484])]],
   [[(0,[z0,z2,z3,z471,z4,z17,z5]),(0,[z0,z144,z2,z3,z98,z4,z5]),(0,[z0,z485,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z486,z5]),(0,[z0,z1,z487,z2,z3,z4,z5]),(0,[z488,z0,z1,z2,z3,z4,z5])],[(0,[z58,z0,z1,z2,z3,z4,z5]),(0,[z38,z414,z0,z1,z2,z4,z5]),(0,[z0,z489,z1,z2,z3,z4,z5]),(0,[z0,z162,z321,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z490,z4,z5])],[(0,[z0,z1,z2,z323,z3,z4,z5]),(0,[z0,z48,z1,z53,z3,z4,z5]),(1,[z0,z2,z3,z4,z5,z34]),(0,[z0,z1,z2,z3,z491,z4,z5])],[(0,[z110,z0,z1,z2,z3,z4,z5]),(0,[z492,z0,z1,z2,z3,z4,z5]),(0,[z224,z0,z1,z2,z3,z4,z73]),(1,[z0,z1,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z4,z158,z103])],[(0,[z0,z1,z2,z3,z4,z5,z362]),(0,[z122,z0,z1,z3,z9,z4,z5]),(0,[z0,z1,z2,z3,z4,z493,z5]),(0,[z0,z1,z2,z494,z3,z4,z5]),(0,[z0,z1,z2,z495,z3,z4,z5]),(0,[z496,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z497]),(0,[z0,z1,z2,z3,z4,z89,z5])],[(0,[z0,z1,z2,z98,z4,z5,z103]),(0,[z0,z1,z191,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z498,z4,z5]),(0,[z0,z1,z499,z2,z3,z4,z5]),(0,[z0,z50,z1,z155,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z40,z166]),(0,[z414,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z103])],[(0,[z0,z1,z500,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z501]),(0,[z0,z1,z2,z502,z3,z4,z5]),(1,[z0,z1,z2,z3,z102,z35]),(0,[z0,z1,z2,z3,z4,z5,z34])],[(0,[z38,z0,z1,z405,z3,z4,z5])],[(0,[z0,z1,z2,z3,z503,z4,z5]),(0,[z0,z1,z504,z2,z3,z4,z5]),(0,[z0,z1,z2,z494,z3,z4,z89]),(0,[z0,z1,z2,z62,z126,z4,z5]),(0,[z0,z1,z202,z2,z3,z4,z505]),(0,[z0,z1,z270,z147,z3,z4,z5]),(0,[z0,z1,z2,z3,z506,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z507])],[(0,[z110,z0,z66,z2,z3,z4,z5]),(0,[z209,z1,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z508,z3,z4,z5]),(1,[z0,z369,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z509]),(1,[z0,z296,z49,z3,z4,z5]),(0,[z510,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z511,z5]),(0,[z0,z1,z2,z108,z3,z4,z158])],[(0,[z0,z512,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z513,z5]),(0,[z0,z1,z147,z3,z213,z4,z5])],[(0,[z0,z514,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z17,z5]),(0,[z0,z1,z53,z3,z62,z4,z5]),(0,[z0,z515,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z40,z163]),(0,[z0,z1,z2,z3,z4,z5,z516]),(0,[z0,z1,z2,z108,z3,z112,z4])],[(0,[z122,z0,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z517,z5]),(0,[z0,z1,z2,z3,z4,z518,z5]),(0,[z0,z162,z1,z3,z62,z4,z5]),(1,[z0,z2,z385,z3,z4,z5]),(1,[z0,z338,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z96,z40]),(0,[z0,z1,z202,z2,z3,z57,z5])],[(0,[z0,z519,z1,z2,z3,z4,z5]),(0,[z0,z1,z225,z3,z4,z73,z5]),(0,[z0,z1,z2,z3,z520,z4,z5]),(0,[z0,z1,z2,z3,z521,z4,z5]),(0,[z522,z0,z1,z2,z3,z4,z5])],[(0,[z122,z0,z1,z53,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z39]),(0,[z523,z0,z1,z2,z3,z4,z5]),(0,[z524,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z178,z3,z4,z5])],[(0,[z122,z0,z1,z14,z3,z4,z5]),(0,[z122,z0,z61,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z525,z4,z5]),(0,[z0,z526,z1,z2,z3,z4,z5]),(0,[z0,z1,z202,z2,z3,z4,z5])],[(0,[z0,z1,z527,z2,z3,z4,z5]),(0,[z0,z162,z297,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z528,z5]),(0,[z0,z1,z2,z3,z529,z4,z5])],[(0,[z0,z1,z2,z3,z530,z4,z5]),(0,[z0,z1,z531,z2,z3,z4,z5]),(0,[z0,z260,z1,z2,z3,z4,z158]),(0,[z0,z1,z251,z2,z3,z4,z5])],[(0,[z0,z532,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z533])],[(0,[z0,z1,z2,z3,z534,z4,z5]),(0,[z0,z1,z53,z3,z4,z57,z5]),(0,[z0,z1,z427,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z535,z5]),(0,[z414,z0,z1,z2,z147,z4,z5])]],
   [[(0,[z0,z1,z2,z536,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z537]),(0,[z0,z61,z1,z202,z3,z4,z5]),(0,[z0,z1,z3,z102,z164,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z38,z0,z1,z2,z3,z431,z5]),(0,[z0,z1,z2,z538,z3,z4,z5]),(0,[z0,z70,z367,z2,z3,z4,z5])],[(0,[z539,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z540,z3,z4,z5]),(1,[z414,z0,z1,z2,z127,z5]),(0,[z0,z1,z2,z147,z3,z126,z5])],[(0,[z0,z541,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z461]),(0,[z0,z1,z2,z3,z4,z542,z5]),(0,[z0,z1,z2,z33,z111,z4,z5]),(0,[z0,z66,z1,z2,z3,z4,z5]),(0,[z543,z0,z1,z2,z3,z4,z5])],[(0,[z0,z296,z48,z2,z3,z4,z5])],[(0,[z544,z0,z1,z2,z3,z4,z5]),(0,[z0,z545,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z73,z103]),(0,[z0,z1,z3,z62,z9,z4,z5])],[(0,[z58,z0,z1,z3,z9,z4,z5]),(0,[z0,z546,z1,z2,z3,z4,z5])],[(0,[z0,z209,z2,z49,z3,z4,z5]),(0,[z0,z1,z547,z2,z3,z4,z5]),(0,[z122,z0,z162,z1,z3,z4,z5]),(0,[z122,z0,z1,z239,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z2,z3,z4,z5,z166])]],
   [[(0,[z58,z1,z2,z15,z3,z4,z5]),(1,[z0,z1,z402,z3,z4,z5]),(0,[z0,z548,z1,z2,z3,z4,z5]),(0,[z0,z549,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z550,z4,z5]),(0,[z0,z61,z1,z2,z3,z57,z5])],[(0,[z0,z83,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z551,z5]),(1,[z0,z1,z71,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z552,z5]),(0,[z0,z1,z553,z2,z3,z4,z5]),(0,[z0,z554,z1,z2,z3,z4,z5]),(1,[z0,z1,z32,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z1,z555,z2,z3,z4,z5]),(0,[z0,z1,z191,z3,z9,z4,z5]),(0,[z0,z61,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z556,z4,z5])],[(0,[z0,z1,z2,z3,z557,z4,z5]),(0,[z0,z1,z558,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z559,z4,z5]),(0,[z0,z1,z2,z560,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z561,z5]),(0,[z0,z1,z2,z3,z4,z562,z5])],[(1,[z0,z1,z2,z346,z3,z4]),(0,[z0,z563,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z564,z3,z4,z5]),(0,[z565,z0,z1,z2,z3,z4,z5]),(0,[z566,z0,z1,z2,z3,z4,z5])],[(0,[z0,z567,z1,z2,z3,z4,z5]),(0,[z568,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z569]),(1,[z0,z1,z2,z494,z3,z4])]],
   [[(0,[z0,z1,z2,z570,z3,z4,z5]),(0,[z0,z1,z2,z3,z571,z4,z5])],[(0,[z0,z1,z2,z3,z233,z4,z5]),(0,[z0,z572,z1,z2,z3,z4,z5]),(0,[z0,z50,z1,z427,z3,z4,z5]),(0,[z0,z573,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z362]),(0,[z0,z1,z2,z3,z4,z5,z574]),(0,[z0,z70,z1,z2,z4,z5,z103])],[(0,[z575,z0,z1,z2,z3,z4,z5]),(0,[z576,z0,z1,z2,z3,z4,z5]),(0,[z0,z66,z2,z3,z4,z96,z5]),(0,[z0,z577,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z578,z3,z4,z5]),(0,[z0,z579,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z108,z3,z4,z5]),(0,[z580,z0,z1,z2,z3,z4,z5])],[(0,[z0,z581,z1,z2,z3,z4,z5]),(0,[z58,z0,z1,z14,z3,z4,z5]),(0,[z58,z0,z61,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z582,z5]),(0,[z0,z1,z583,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z584,z5])],[(0,[z0,z1,z191,z15,z3,z4,z5]),(0,[z0,z1,z3,z223,z4,z17,z5]),(0,[z0,z1,z86,z3,z62,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z585]),(0,[z0,z1,z2,z3,z4,z5,z586])],[(0,[z0,z1,z587,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z222,z4])],[(0,[z0,z1,z2,z3,z588,z4,z5]),(0,[z0,z1,z202,z3,z9,z4,z5]),(0,[z0,z1,z2,z589,z3,z4,z5]),(0,[z414,z0,z1,z2,z3,z126,z5])]],
   [[(0,[z0,z76,z2,z3,z98,z4,z5]),(0,[z0,z1,z2,z3,z4,z356,z5]),(0,[z38,z0,z1,z2,z233,z4,z5]),(0,[z0,z1,z2,z590,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z591]),(0,[z592,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z158,z5,z163]),(0,[z0,z1,z2,z3,z593,z4,z5])],[(0,[z0,z1,z191,z14,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z594]),(0,[z0,z74,z1,z2,z33,z4,z5]),(0,[z595,z0,z1,z2,z3,z4,z5])],[(0,[z0,z48,z2,z3,z98,z4,z5]),(0,[z0,z1,z596,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z17,z127,z5]),(0,[z597,z0,z1,z2,z3,z4,z5]),(0,[z0,z48,z2,z3,z159,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z505])],[(0,[z598,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z599,z3,z4,z5]),(0,[z0,z1,z600,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z601,z4,z5]),(0,[z0,z1,z2,z602,z3,z4,z5]),(0,[z0,z260,z1,z2,z3,z4,z5]),(0,[z414,z0,z1,z2,z4,z127,z5]),(0,[z603,z0,z1,z2,z3,z4,z5]),(1,[z0,z153,z2,z3,z4,z5])],[(0,[z0,z1,z53,z86,z3,z4,z5]),(0,[z604,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z9,z4,z5]),(0,[z0,z1,z2,z3,z4,z605,z5]),(0,[z0,z1,z2,z3,z606,z4,z5])],[(1,[z0,z48,z53,z3,z4,z5]),(0,[z0,z1,z607,z2,z3,z4,z5]),(0,[z608,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z86,z3,z4,z57,z5]),(0,[z0,z1,z2,z147,z3,z4,z5]),(0,[z0,z1,z2,z609,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z610,z5]),(1,[z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z611,z3,z4,z5]),(1,[z0,z2,z3,z471,z4,z5]),(0,[z0,z296,z2,z49,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z158,z5])]],
   [[(0,[z58,z0,z162,z1,z3,z4,z5]),(0,[z58,z0,z1,z239,z3,z4,z5])],[(0,[z0,z612,z1,z2,z3,z4,z5]),(0,[z58,z122,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z431,z5]),(1,[z0,z257,z2,z3,z4,z5])],[(0,[z0,z74,z76,z2,z3,z4,z5]),(0,[z6,z1,z2,z7,z3,z4,z5]),(0,[z0,z48,z53,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z113,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z613,z1,z2,z3,z4,z5]),(0,[z0,z1,z202,z2,z178,z4,z5]),(0,[z0,z614,z1,z2,z3,z4,z5]),(1,[z0,z301,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z615,z5]),(0,[z38,z0,z369,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z64,z5]),(0,[z0,z1,z2,z3,z4,z616,z5])],[(0,[z58,z0,z243,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z158,z73]),(0,[z617,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z191,z239,z3,z4,z5]),(0,[z0,z1,z618,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z619,z4,z5]),(0,[z0,z1,z2,z3,z620,z4,z5]),(0,[z0,z1,z53,z2,z3,z4,z461])],[(1,[z0,z1,z232,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z621]),(0,[z0,z1,z2,z3,z622,z4,z5]),(0,[z0,z1,z2,z3,z4,z623,z5]),(0,[z624,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z625,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z626]),(0,[z0,z1,z2,z3,z102,z4,z40])],[(0,[z627,z0,z1,z2,z3,z4,z5]),(0,[z0,z296,z1,z49,z3,z4,z5]),(0,[z0,z1,z2,z190,z3,z4,z5]),(0,[z0,z256,z202,z2,z3,z4,z5]),(0,[z0,z338,z86,z2,z3,z4,z5]),(0,[z0,z628,z1,z2,z3,z4,z5])],[(0,[z174,z0,z1,z2,z4,z17,z5]),(0,[z0,z1,z2,z180,z3,z4,z5]),(0,[z0,z74,z2,z3,z159,z4,z5]),(0,[z0,z629,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z239,z126,z4,z5])],[(0,[z630,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z631,z2,z3,z4,z5]),(0,[z26,z224,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z96,z103])],[(0,[z0,z1,z2,z3,z4,z632,z5]),(0,[z0,z1,z2,z3,z633,z4,z5])],[(0,[z38,z6,z1,z2,z3,z4,z5]),(0,[z65,z0,z1,z2,z3,z17,z5]),(0,[z0,z1,z2,z3,z4,z634,z5]),(0,[z0,z635,z1,z2,z3,z4,z5]),(0,[z0,z70,z1,z2,z3,z4,z40])],[(0,[z0,z636,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z17,z5]),(1,[z0,z21,z2,z98,z4,z5])],[(0,[z0,z1,z14,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z430,z5]),(0,[z0,z1,z2,z3,z4,z637,z5]),(0,[z0,z638,z1,z2,z3,z4,z5]),(0,[z639,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z640,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z641]),(0,[z0,z1,z2,z3,z642,z4,z5]),(0,[z0,z1,z643,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z163]),(0,[z0,z1,z2,z3,z203,z4,z5]),(0,[z0,z1,z2,z108,z3,z102,z5])],[(0,[z0,z1,z2,z3,z644,z4,z5]),(0,[z0,z645,z1,z2,z3,z4,z5])],[(0,[z0,z646,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z647,z5]),(1,[z0,z1,z2,z190,z4,z5]),(0,[z0,z162,z1,z191,z3,z4,z5]),(0,[z0,z1,z2,z648,z3,z4,z5]),(0,[z0,z1,z2,z147,z3,z4,z107])],[(0,[z0,z1,z2,z3,z4,z649,z5]),(0,[z0,z1,z2,z3,z4,z650,z5])],[(0,[z0,z1,z2,z3,z4,z651,z5]),(0,[z0,z1,z2,z3,z4,z652,z5]),(0,[z0,z1,z2,z3,z4,z5,z653]),(0,[z0,z1,z2,z3,z4,z654,z5]),(0,[z0,z1,z2,z3,z655,z4,z5]),(0,[z0,z656,z1,z2,z3,z4,z5]),(0,[z0,z657,z1,z2,z3,z4,z5]),(0,[z0,z1,z53,z3,z4,z5,z163]),(0,[z0,z1,z2,z3,z222,z4,z5]),(0,[z0,z658,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z213,z4,z5]),(0,[z0,z1,z2,z3,z112,z102,z4])],[(1,[z0,z419,z1,z3,z4,z5]),(0,[z0,z1,z49,z3,z4,z57,z5]),(0,[z0,z2,z3,z98,z4,z5,z166]),(0,[z0,z1,z2,z3,z4,z659,z5]),(0,[z0,z1,z2,z3,z102,z4,z163])],[(0,[z0,z1,z2,z3,z430,z4,z5]),(0,[z6,z0,z1,z2,z126,z4,z5]),(0,[z0,z1,z2,z660,z3,z4,z5]),(0,[z0,z83,z1,z3,z4,z17,z5]),(0,[z0,z1,z2,z3,z4,z661,z5]),(0,[z0,z50,z48,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z662,z5])],[(0,[z0,z663,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z664,z4,z5]),(0,[z0,z1,z2,z3,z665,z4,z5]),(0,[z0,z144,z1,z2,z3,z4,z163]),(0,[z0,z1,z2,z239,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z107])]],
   [[(0,[z0,z1,z2,z3,z4,z666,z5]),(0,[z0,z1,z667,z2,z3,z4,z5]),(0,[z38,z0,z1,z402,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z73,z5]),(0,[z414,z0,z1,z2,z3,z127,z5])],[(0,[z0,z1,z2,z3,z668,z4,z5]),(0,[z0,z669,z1,z2,z3,z4,z5]),(0,[z0,z670,z1,z2,z3,z4,z5]),(0,[z0,z671,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z377,z5]),(0,[z0,z1,z2,z3,z4,z672,z5]),(0,[z0,z256,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z673,z4,z5]),(0,[z0,z1,z2,z3,z4,z674,z5]),(0,[z0,z1,z675,z2,z3,z4,z5]),(0,[z0,z88,z1,z2,z3,z159,z5]),(0,[z0,z1,z191,z2,z239,z4,z5]),(1,[z0,z1,z2,z147,z126,z5]),(0,[z0,z676,z1,z2,z3,z4,z5])],[(0,[z677,z0,z1,z2,z3,z4,z5]),(1,[z58,z1,z15,z3,z4,z5]),(0,[z414,z6,z0,z1,z2,z4,z5]),(0,[z414,z0,z1,z2,z239,z4,z5])],[(1,[z109,z209,z2,z3,z4,z5]),(0,[z38,z1,z2,z3,z233,z4,z5]),(0,[z0,z1,z2,z3,z126,z17,z5])],[(0,[z0,z1,z2,z3,z678,z4,z5])],[(0,[z0,z209,z1,z2,z3,z4,z5]),(0,[z679,z0,z1,z2,z3,z4,z5]),(0,[z110,z1,z76,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z680,z5]),(1,[z0,z70,z1,z2,z4,z103])]],
   [[(0,[z0,z1,z2,z681,z3,z4,z5]),(0,[z122,z0,z1,z86,z3,z4,z5]),(0,[z0,z682,z1,z2,z3,z4,z5]),(0,[z16,z0,z1,z2,z3,z17,z5]),(0,[z0,z1,z2,z3,z4,z683,z5]),(0,[z0,z66,z1,z238,z3,z4,z5]),(0,[z0,z1,z2,z3,z684,z4,z5]),(1,[z0,z1,z2,z3,z4,z505]),(0,[z0,z685,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z686,z4,z5]),(0,[z0,z1,z2,z3,z4,z687,z5]),(0,[z0,z1,z688,z2,z3,z4,z5]),(0,[z689,z0,z1,z2,z3,z4,z5]),(0,[z0,z690,z1,z2,z3,z4,z5]),(0,[z0,z691,z1,z2,z3,z4,z5]),(0,[z0,z2,z147,z3,z151,z4,z5])],[(0,[z0,z1,z2,z233,z62,z4,z5]),(0,[z0,z1,z2,z3,z4,z54,z5]),(0,[z0,z1,z692,z2,z3,z4,z5])],[(0,[z6,z0,z1,z2,z3,z4,z5]),(1,[z0,z189,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z693,z5]),(0,[z0,z1,z2,z3,z694,z4,z5])],[(0,[z26,z1,z2,z3,z4,z5,z27]),(0,[z0,z1,z2,z3,z4,z5,z695])],[(0,[z110,z0,z2,z3,z159,z4,z5]),(0,[z0,z76,z2,z49,z3,z4,z5]),(0,[z0,z1,z210,z2,z3,z4,z5]),(0,[z696,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z697,z4,z5]),(0,[z698,z0,z1,z2,z3,z4,z5]),(0,[z0,z70,z1,z361,z3,z4,z5])],[(0,[z0,z1,z243,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z62,z4,z5]),(0,[z0,z699,z1,z2,z3,z4,z5]),(0,[z0,z1,z700,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z701,z5]),(0,[z0,z1,z2,z702,z3,z4,z5]),(0,[z0,z1,z2,z3,z703,z4,z5])],[(0,[z0,z1,z2,z3,z704,z4,z5]),(0,[z58,z0,z1,z2,z323,z4,z5]),(0,[z0,z1,z2,z705,z3,z4,z5]),(0,[z0,z2,z3,z159,z4,z89,z5]),(0,[z0,z1,z2,z3,z706,z4,z5]),(0,[z0,z1,z251,z3,z102,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z4,z5]),(0,[z414,z0,z1,z2,z535,z5])],[(0,[z0,z708,z2,z3,z4,z5])],[(0,[z58,z1,z709,z3,z4,z5]),(0,[z0,z1,z2,z3,z710,z5]),(0,[z0,z1,z2,z3,z4,z711]),(0,[z0,z301,z2,z3,z4,z5]),(0,[z0,z50,z2,z145,z3,z4]),(0,[z0,z1,z251,z3,z4,z158]),(0,[z0,z1,z712,z3,z4,z5]),(0,[z0,z713,z2,z3,z4,z5])],[(0,[z0,z1,z714,z3,z4,z5]),(0,[z0,z715,z2,z3,z4,z5]),(0,[z0,z554,z1,z3,z4,z163]),(0,[z0,z2,z11,z3,z159,z5]),(0,[z0,z1,z213,z126,z4,z5])],[(0,[z0,z1,z2,z332,z4,z123]),(0,[z0,z1,z2,z178,z4,z505]),(0,[z0,z367,z361,z3,z4,z5])],[(0,[z0,z1,z3,z4,z716,z5]),(0,[z0,z1,z2,z31,z184,z5]),(0,[z0,z1,z3,z4,z666,z163]),(0,[z0,z1,z717,z3,z222,z4]),(0,[z0,z2,z183,z3,z4,z505])],[(0,[z110,z76,z2,z3,z4,z5]),(0,[z0,z243,z2,z3,z430,z5]),(0,[z0,z1,z718,z3,z4,z5]),(0,[z0,z2,z3,z719,z4,z5]),(0,[z0,z2,z3,z4,z5,z720])],[(0,[z0,z2,z3,z4,z721,z5]),(0,[z0,z1,z722,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z1,z3,z724,z4,z5]),(0,[z0,z74,z2,z3,z4,z176]),(0,[z0,z260,z1,z3,z4,z725])]],
   [[(0,[z0,z1,z726,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z727])],[(0,[z0,z240,z1,z2,z4,z103]),(0,[z0,z2,z3,z102,z34,z35]),(0,[z0,z1,z2,z108,z3,z728])],[(0,[z110,z729,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z1,z86,z3,z4,z113]),(0,[z0,z369,z405,z3,z4,z5])],[(0,[z0,z1,z2,z323,z4,z362]),(0,[z0,z61,z1,z3,z57,z5])],[(0,[z0,z1,z2,z178,z4,z5])],[(0,[z0,z1,z2,z3,z4,z731]),(0,[z0,z1,z180,z3,z4,z5]),(0,[z0,z411,z1,z62,z4,z5])],[(0,[z0,z396,z49,z3,z4,z5]),(0,[z58,z1,z406,z3,z4,z5]),(0,[z0,z474,z49,z3,z4,z5]),(0,[z122,z0,z297,z3,z4,z5]),(0,[z0,z1,z402,z3,z4,z356]),(0,[z38,z1,z402,z233,z4,z5]),(0,[z0,z646,z49,z3,z4,z5]),(0,[z0,z1,z3,z4,z248,z163])],[(0,[z0,z732,z2,z3,z4,z5]),(0,[z0,z1,z2,z733,z3,z4]),(0,[z16,z174,z1,z2,z17,z5])]],
   [[],[(0,[z0,z1,z2,z3,z734,z5]),(0,[z0,z1,z2,z735,z4,z5]),(0,[z0,z1,z2,z3,z4,z736]),(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z738,z2,z3,z4,z5])],[(0,[z0,z1,z739,z3,z4,z5]),(0,[z0,z1,z86,z203,z4,z5])],[(0,[z0,z1,z740,z3,z4,z5]),(0,[z58,z243,z15,z3,z4,z5]),(0,[z58,z1,z700,z3,z4,z5]),(0,[z0,z1,z2,z741,z4,z5]),(0,[z0,z742,z1,z3,z4,z5]),(0,[z0,z743,z2,z3,z4,z5]),(0,[z0,z367,z71,z3,z4,z5]),(0,[z0,z92,z2,z108,z3,z4])],[(0,[z109,z209,z210,z3,z4,z5]),(0,[z0,z419,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z744])],[(0,[z0,z1,z2,z3,z4,z745]),(0,[z0,z1,z746,z3,z4,z5]),(0,[z0,z270,z3,z151,z4,z5])],[(0,[z0,z321,z2,z3,z4,z377]),(0,[z0,z385,z3,z62,z4,z5]),(0,[z0,z1,z3,z263,z4,z163]),(0,[z0,z301,z2,z3,z4,z107])],[(0,[z0,z59,z2,z3,z4,z362]),(0,[z0,z21,z2,z98,z4,z176]),(0,[z0,z2,z747,z98,z4,z5]),(0,[z0,z2,z3,z4,z5,z748]),(0,[z0,z1,z3,z213,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z749]),(0,[z0,z1,z2,z3,z750,z5]),(0,[z0,z1,z2,z3,z4,z751]),(0,[z0,z257,z2,z4,z123,z5]),(0,[z0,z2,z752,z3,z4,z5]),(0,[z0,z421,z2,z3,z4,z166]),(0,[z753,z1,z2,z3,z4,z5]),(1,[z0,z2,z192,z4,z166])],[(0,[z0,z48,z427,z3,z4,z5])],[(0,[z0,z1,z3,z754,z4,z5]),(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z1,z53,z3,z4,z362]),(0,[z0,z1,z225,z3,z4,z5]),(0,[z0,z541,z1,z62,z4,z5]),(0,[z0,z1,z2,z3,z431,z356]),(0,[z38,z1,z2,z233,z431,z5]),(0,[z1,z2,z3,z10,z756,z5]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z2,z3,z4,z759]),(0,[z0,z1,z2,z147,z126,z5]),(0,[z0,z1,z760,z3,z4,z5])],[(0,[z0,z1,z761,z3,z4,z5]),(0,[z0,z762,z1,z3,z4,z5]),(0,[z174,z0,z83,z1,z4,z5]),(0,[z0,z1,z2,z763,z3,z4]),(0,[z0,z338,z427,z3,z4,z5])],[(0,[z109,z209,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z764]),(0,[z0,z256,z2,z3,z4,z505]),(0,[z0,z1,z3,z164,z4,z103])],[(0,[z0,z765,z2,z3,z4,z5]),(0,[z0,z766,z1,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z767]),(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z1,z86,z3,z184,z5]),(0,[z0,z1,z3,z769,z4,z5]),(0,[z0,z1,z3,z770,z4,z5]),(0,[z0,z1,z771,z3,z4,z5]),(0,[z0,z1,z86,z3,z4,z725]),(0,[z0,z70,z1,z2,z4,z103])],[(0,[z0,z1,z210,z3,z4,z5]),(0,[z0,z74,z141,z3,z4,z5]),(0,[z0,z2,z3,z332,z471,z4]),(0,[z0,z772,z2,z3,z4,z5]),(1,[z0,z1,z3,z773,z5])]],
   [[(0,[z729,z76,z2,z3,z4,z5]),(0,[z122,z1,z3,z4,z5,z19]),(0,[z0,z1,z774,z3,z4,z5]),(0,[z0,z1,z2,z3,z775,z5])],[(0,[z58,z0,z1,z3,z4,z461]),(0,[z0,z1,z239,z205,z4,z5]),(0,[z0,z1,z2,z3,z776,z5]),(0,[z0,z1,z251,z3,z4,z5]),(0,[z0,z777,z2,z3,z4,z5])],[(0,[z0,z189,z2,z3,z4,z5]),(0,[z0,z1,z778,z3,z4,z5]),(0,[z414,z0,z1,z2,z431,z5]),(0,[z0,z1,z779,z3,z4,z5]),(0,[z0,z780,z2,z3,z4,z5]),(0,[z90,z1,z2,z3,z4,z73]),(0,[z0,z1,z2,z3,z4,z781]),(0,[z0,z1,z155,z3,z102,z4]),(0,[z0,z1,z782,z3,z4,z5])],[(0,[z0,z1,z2,z3,z783,z4]),(0,[z0,z1,z210,z3,z4,z784]),(0,[z0,z1,z2,z3,z785,z5]),(0,[z0,z2,z346,z3,z471,z4]),(0,[z0,z1,z2,z98,z4,z176])],[(0,[z0,z1,z786,z3,z4,z5]),(0,[z0,z1,z787,z3,z4,z5]),(0,[z0,z256,z2,z3,z4,z5]),(0,[z0,z144,z2,z3,z4,z586])],[(0,[z38,z1,z2,z233,z4,z39]),(0,[z624,z1,z2,z3,z17,z5]),(0,[z0,z1,z788,z3,z4,z5])],[(0,[z0,z1,z789,z3,z4,z5]),(0,[z0,z66,z2,z3,z29,z5]),(0,[z0,z260,z1,z3,z4,z163]),(0,[z0,z338,z86,z3,z4,z158])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z126,z324,z5]),(0,[z0,z1,z2,z3,z4,z790]),(0,[z0,z180,z3,z98,z4,z5]),(0,[z0,z1,z2,z3,z4,z791])]],
   [[(0,[z0,z1,z2,z323,z430,z5]),(0,[z0,z792,z2,z3,z4,z5]),(0,[z0,z297,z2,z3,z4,z377]),(0,[z0,z1,z2,z540,z4,z40])],[(0,[z0,z2,z3,z793,z4,z5]),(0,[z0,z1,z67,z3,z4,z794]),(0,[z0,z1,z191,z3,z4,z118]),(0,[z0,z1,z2,z4,z40,z795])],[(0,[z0,z1,z405,z3,z431,z5]),(0,[z0,z796,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z356]),(0,[z38,z1,z2,z233,z64,z5]),(0,[z0,z1,z3,z62,z4,z461]),(0,[z0,z238,z3,z98,z4,z5]),(0,[z0,z1,z797,z3,z4,z5])],[(0,[z0,z1,z798,z3,z4,z5]),(0,[z0,z1,z2,z3,z799,z5]),(0,[z0,z1,z2,z800,z4,z5])],[(0,[z1,z2,z709,z3,z4,z5]),(0,[z0,z801,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z802]),(0,[z0,z1,z402,z3,z431,z5]),(0,[z488,z1,z2,z3,z10,z5]),(0,[z0,z245,z2,z98,z4,z5]),(1,[z0,z1,z3,z4,z725])],[(0,[z0,z1,z2,z803,z4,z5]),(0,[z122,z0,z385,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z804]),(0,[z0,z50,z2,z190,z4,z166]),(0,[z0,z1,z62,z389,z4,z5]),(0,[z0,z1,z2,z147,z126,z107])],[(0,[z0,z1,z86,z31,z4,z5]),(0,[z0,z1,z2,z3,z4,z805])]],
   [[(0,[z0,z1,z2,z3,z806,z5]),(0,[z0,z1,z2,z807,z4,z5]),(0,[z0,z155,z3,z159,z4,z5]),(0,[z0,z1,z361,z3,z4,z40]),(0,[z0,z251,z808,z3,z4,z5])],[(0,[z0,z1,z809,z3,z4,z5]),(0,[z0,z1,z2,z346,z4,z123]),(0,[z0,z2,z3,z200,z159,z5]),(0,[z0,z162,z297,z62,z4,z5]),(0,[z0,z810,z2,z3,z4,z5])],[(0,[z0,z1,z49,z203,z4,z5]),(0,[z0,z1,z2,z3,z4,z811])],[(0,[z0,z1,z812,z3,z4,z5]),(0,[z0,z1,z2,z813,z4,z5]),(0,[z0,z1,z2,z3,z728,z5])],[(0,[z0,z59,z2,z3,z430,z5]),(0,[z0,z1,z2,z31,z4,z113]),(0,[z0,z2,z192,z4,z5,z166]),(0,[z0,z1,z2,z192,z4,z158])],[(0,[z58,z1,z15,z323,z4,z5]),(0,[z0,z1,z405,z3,z4,z39]),(0,[z0,z48,z2,z3,z4,z54]),(0,[z0,z1,z814,z3,z4,z5]),(0,[z0,z1,z155,z190,z4,z5]),(0,[z0,z162,z1,z62,z4,z5])],[(0,[z0,z1,z2,z3,z184,z362]),(0,[z0,z1,z2,z3,z815,z5]),(0,[z0,z1,z32,z3,z4,z176])],[(0,[z0,z816,z2,z3,z4,z5]),(0,[z0,z1,z817,z3,z4,z5]),(0,[z0,z818,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z819,z5]),(0,[z0,z153,z2,z4,z5,z103])]],
   [[(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z549,z2,z98,z4,z5])],[(0,[z0,z1,z2,z821,z4,z5]),(0,[z0,z432,z49,z3,z4,z5]),(0,[z0,z50,z2,z3,z4,z376]),(0,[z0,z1,z3,z354,z4,z163])],[(0,[z0,z1,z405,z3,z64,z5]),(0,[z0,z257,z3,z223,z4,z5]),(0,[z0,z1,z86,z3,z4,z54]),(0,[z0,z74,z238,z3,z4,z5]),(0,[z0,z297,z191,z3,z4,z5]),(0,[z0,z338,z2,z3,z4,z163])],[(0,[z65,z1,z2,z3,z756,z5]),(0,[z0,z1,z822,z3,z4,z5]),(0,[z0,z144,z2,z259,z3,z4]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z3,z4,z107])],[(0,[z0,z1,z2,z3,z824,z5]),(0,[z0,z825,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z0,z2,z3,z4,z5,z827])],[(0,[z0,z1,z2,z3,z4,z828]),(0,[z38,z369,z2,z233,z4,z5]),(0,[z0,z829,z2,z3,z4,z5]),(0,[z0,z1,z223,z4,z123,z5]),(0,[z0,z1,z830,z3,z4,z5])],[(0,[z0,z421,z1,z2,z4,z103]),(0,[z0,z1,z2,z3,z4,z831])],[(0,[z0,z1,z832,z3,z4,z5]),(0,[z0,z1,z2,z3,z430,z113]),(0,[z833,z0,z1,z2,z4,z5]),(0,[z0,z1,z834,z3,z4,z5]),(0,[z0,z1,z2,z4,z123,z5]),(0,[z0,z1,z2,z835,z3,z4]),(0,[z0,z1,z2,z836,z4,z5]),(0,[z0,z1,z837,z3,z4,z5])]],
   [[(0,[z0,z419,z801,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z838])],[(0,[z0,z1,z2,z323,z4,z5]),(0,[z58,z59,z15,z3,z4,z5]),(1,[z1,z709,z3,z4,z5]),(0,[z174,z0,z1,z2,z346,z4])],[(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z1,z155,z108,z3,z4]),(0,[z0,z840,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z841])],[(0,[z0,z1,z842,z3,z4,z5])],[(0,[z0,z1,z402,z233,z4,z5]),(0,[z0,z1,z2,z3,z431,z39]),(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z50,z2,z3,z4,z166]),(0,[z0,z1,z2,z111,z4,z795])],[(0,[z122,z1,z14,z3,z4,z5]),(0,[z0,z1,z844,z3,z4,z5]),(0,[z0,z74,z2,z33,z4,z5])],[(1,[z729,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z845,z4]),(0,[z0,z1,z846,z3,z4,z5]),(0,[z16,z2,z3,z471,z17,z5]),(0,[z0,z847,z2,z3,z4,z5]),(1,[z0,z752,z3,z4,z5]),(0,[z0,z1,z2,z126,z819,z5]),(0,[z0,z1,z848,z3,z4,z5])],[(0,[z0,z1,z2,z31,z4,z362]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z2,z3,z850,z4]),(0,[z0,z1,z2,z108,z192,z4]),(0,[z0,z851,z2,z3,z4,z5]),(0,[z0,z1,z203,z9,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z852]),(0,[z16,z257,z2,z3,z17,z5]),(0,[z0,z1,z53,z3,z4,z505]),(0,[z0,z2,z98,z4,z5,z176]),(0,[z0,z301,z270,z3,z4,z5]),(0,[z0,z1,z853,z3,z4,z5])],[(0,[z0,z854,z2,z3,z4,z5]),(0,[z0,z855,z1,z3,z4,z5]),(0,[z0,z1,z3,z856,z4,z5])],[(0,[z0,z1,z3,z857,z4,z5])],[(0,[z0,z257,z83,z3,z4,z5]),(0,[z0,z1,z155,z3,z4,z5]),(0,[z0,z1,z2,z858,z4,z5])],[(0,[z58,z1,z15,z3,z4,z113]),(0,[z0,z2,z3,z859,z89,z5]),(0,[z0,z256,z2,z178,z4,z5]),(1,[z0,z1,z2,z3,z728])],[(0,[z0,z59,z2,z3,z4,z5]),(0,[z0,z144,z2,z3,z4,z748])],[(0,[z122,z0,z1,z3,z4,z118]),(0,[z0,z1,z2,z3,z4,z356]),(0,[z0,z83,z1,z4,z123,z5]),(0,[z0,z1,z202,z3,z9,z505])],[(0,[z0,z1,z210,z3,z4,z860]),(0,[z0,z1,z49,z31,z4,z5]),(0,[z174,z0,z1,z2,z4,z5]),(0,[z0,z861,z2,z3,z4,z5]),(0,[z268,z0,z1,z2,z4,z103]),(0,[z510,z0,z1,z62,z4,z5]),(0,[z0,z1,z3,z164,z4,z5])]],
   [[(0,[z0,z1,z31,z9,z4,z5]),(0,[z0,z369,z402,z3,z4,z5]),(0,[z0,z2,z49,z3,z4,z54]),(0,[z0,z2,z183,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z862])],[(0,[z0,z367,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z96,z748]),(0,[z0,z153,z2,z3,z4,z40]),(0,[z0,z92,z760,z3,z4,z5])],[(0,[z0,z1,z427,z3,z4,z54]),(0,[z0,z1,z2,z192,z4,z5]),(0,[z0,z66,z155,z3,z4,z5]),(0,[z0,z1,z202,z3,z773,z5]),(0,[z0,z1,z2,z3,z819,z5])],[(0,[z0,z1,z863,z3,z4,z5]),(0,[z0,z2,z3,z864,z4,z5]),(0,[z0,z1,z2,z3,z865,z5]),(0,[z0,z1,z153,z2,z4,z103])],[(0,[z0,z21,z2,z747,z4,z5]),(0,[z0,z50,z2,z3,z4,z591])],[(0,[z0,z1,z2,z3,z866,z4]),(0,[z0,z1,z867,z3,z4,z5]),(0,[z0,z1,z427,z3,z4,z163]),(0,[z0,z1,z427,z190,z4,z5]),(0,[z0,z1,z202,z3,z9,z5]),(0,[z0,z183,z3,z4,z5,z163]),(0,[z0,z1,z2,z3,z4,z276])],[(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z1,z2,z868,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z113]),(0,[z0,z50,z2,z3,z4,z446]),(0,[z0,z1,z3,z869,z4,z5]),(0,[z0,z1,z2,z203,z4,z505])],[(0,[z0,z1,z870,z3,z4,z5]),(0,[z0,z1,z2,z4,z871,z5]),(0,[z0,z872,z2,z3,z4,z5])],[(0,[z1,z14,z709,z3,z4,z5]),(0,[z0,z236,z2,z98,z4,z5]),(0,[z0,z1,z180,z3,z4,z176]),(0,[z0,z2,z3,z192,z4,z166])],[(0,[z0,z1,z2,z3,z4,z873]),(0,[z0,z74,z2,z447,z4,z5]),(0,[z0,z66,z2,z192,z4,z5]),(0,[z0,z874,z251,z3,z4,z5])],[(0,[z0,z875,z1,z2,z3,z5]),(0,[z0,z369,z2,z3,z431,z5]),(0,[z1,z2,z876,z233,z4,z5]),(0,[z0,z2,z3,z4,z5,z877]),(0,[z0,z1,z2,z878,z3,z4]),(0,[z0,z1,z2,z3,z4,z879]),(0,[z0,z1,z3,z529,z9,z5]),(0,[z0,z2,z3,z880,z4,z5]),(0,[z0,z881,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z882,z5]),(0,[z58,z690,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z883])],[(0,[z0,z1,z405,z3,z4,z5]),(0,[z0,z1,z2,z3,z884,z5]),(0,[z224,z1,z2,z3,z4,z885]),(0,[z0,z144,z2,z192,z4,z5]),(0,[z0,z1,z2,z3,z773,z5])],[(0,[z0,z1,z886,z3,z4,z5]),(0,[z0,z74,z2,z262,z4,z5]),(0,[z0,z92,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z859,z5]),(0,[z0,z1,z2,z3,z4,z887])]],
   [[(0,[z58,z1,z15,z3,z184,z5]),(0,[z0,z1,z2,z126,z431,z5]),(0,[z0,z419,z1,z239,z4,z5]),(0,[z0,z2,z33,z747,z4,z5]),(0,[z0,z1,z2,z3,z888,z5]),(0,[z0,z1,z270,z147,z126,z5]),(0,[z0,z1,z3,z889,z4,z5])],[(0,[z109,z2,z3,z68,z4,z5]),(0,[z0,z1,z3,z223,z4,z5]),(0,[z0,z1,z2,z747,z4,z5]),(0,[z0,z874,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z728,z102])],[(0,[z0,z243,z2,z3,z4,z5]),(0,[z58,z0,z297,z3,z4,z5]),(0,[z65,z1,z2,z3,z10,z5]),(0,[z0,z321,z2,z3,z4,z5]),(0,[z0,z1,z2,z147,z819,z5])],[(0,[z0,z1,z890,z3,z4,z5]),(0,[z0,z274,z49,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z891]),(0,[z0,z1,z2,z3,z4,z118]),(0,[z0,z1,z2,z3,z4,z892]),(0,[z0,z1,z2,z3,z4,z893]),(0,[z0,z1,z361,z3,z4,z103])],[(0,[z0,z1,z894,z3,z4,z5]),(0,[z0,z1,z2,z31,z430,z5]),(0,[z0,z1,z3,z4,z149,z103]),(0,[z0,z1,z2,z3,z4,z895]),(0,[z0,z1,z238,z3,z4,z5]),(0,[z0,z1,z896,z3,z4,z5]),(0,[z0,z1,z897,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z898]),(0,[z0,z899,z2,z3,z4,z5]),(0,[z0,z1,z2,z900,z3,z4]),(0,[z0,z1,z2,z3,z901,z4]),(0,[z0,z1,z2,z902,z4,z5]),(0,[z0,z338,z49,z3,z4,z5]),(0,[z0,z1,z191,z3,z4,z461]),(0,[z903,z1,z2,z3,z4,z5])],[(0,[z0,z904,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z2,z3,z222,z159,z4]),(1,[z0,z2,z3,z4,z748])],[(0,[z0,z369,z2,z3,z4,z39]),(0,[z0,z427,z49,z3,z4,z5]),(0,[z0,z66,z2,z3,z859,z5]),(0,[z0,z906,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z907,z3,z4,z5]),(0,[z0,z908,z2,z3,z4,z5]),(0,[z0,z1,z909,z3,z4,z5]),(0,[z0,z1,z910,z3,z4,z5])],[(0,[z0,z1,z2,z3,z911,z5]),(0,[z0,z144,z2,z3,z4,z96])],[(0,[z0,z1,z2,z912,z4,z5]),(0,[z0,z1,z2,z3,z4,z913]),(0,[z0,z153,z361,z3,z4,z5])],[(0,[z0,z1,z2,z914,z4,z5]),(0,[z0,z1,z2,z3,z4,z915]),(0,[z0,z1,z3,z4,z40,z149]),(0,[z0,z1,z49,z3,z4,z505]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z0,z1,z917,z3,z4,z5])],[(0,[z0,z1,z2,z3,z184,z5]),(0,[z0,z369,z2,z3,z64,z5]),(0,[z0,z2,z3,z4,z918,z5]),(0,[z0,z1,z2,z3,z102,z47]),(0,[z0,z225,z919,z3,z4,z5]),(0,[z0,z1,z2,z3,z920,z5]),(0,[z0,z2,z921,z3,z4,z5])],[(0,[z1,z2,z3,z756,z17,z5]),(0,[z275,z1,z2,z3,z17,z5]),(0,[z0,z1,z270,z3,z4,z5]),(0,[z0,z61,z1,z3,z363,z5]),(0,[z0,z70,z1,z71,z4,z103])],[(0,[z229,z76,z2,z3,z4,z5]),(0,[z0,z922,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z885,z27]),(0,[z0,z1,z3,z213,z4,z107])],[(0,[z209,z729,z2,z3,z4,z5]),(0,[z16,z1,z2,z3,z17,z5]),(0,[z0,z1,z355,z3,z4,z163])]],
   [[(0,[z38,z1,z232,z233,z4,z5]),(0,[z0,z83,z1,z3,z9,z5]),(0,[z0,z50,z2,z192,z4,z166])],[(0,[z58,z1,z15,z31,z4,z5]),(0,[z0,z923,z2,z3,z4,z5]),(0,[z0,z1,z2,z924,z3,z4])],[(0,[z0,z1,z251,z3,z4,z248]),(0,[z0,z1,z925,z3,z4,z5])],[(0,[z0,z926,z2,z3,z4,z5]),(0,[z0,z1,z927,z3,z4,z5]),(0,[z0,z928,z2,z3,z4,z5])],[(0,[z0,z1,z2,z929,z4,z5]),(0,[z0,z1,z2,z3,z4,z176]),(0,[z0,z338,z2,z3,z4,z158]),(0,[z0,z301,z2,z3,z4,z276]),(0,[z0,z70,z1,z361,z4,z103])],[(0,[z224,z1,z2,z560,z3,z4]),(0,[z0,z48,z53,z3,z4,z461]),(0,[z0,z1,z2,z108,z3,z359])],[(0,[z0,z1,z2,z930,z4,z5]),(0,[z0,z1,z2,z3,z931,z5]),(0,[z0,z116,z2,z98,z4,z5]),(0,[z174,z0,z1,z2,z126,z5]),(0,[z0,z1,z932,z3,z4,z5])],[(0,[z0,z1,z709,z3,z4,z5]),(0,[z0,z2,z98,z4,z166,z103]),(0,[z0,z1,z155,z192,z4,z5]),(0,[z0,z1,z86,z3,z4,z158]),(0,[z0,z1,z2,z111,z4,z40]),(0,[z0,z2,z808,z3,z4,z5])]],
   [[(0,[z0,z1,z933,z3,z4,z5]),(0,[z0,z1,z934,z3,z4,z5]),(0,[z0,z1,z67,z3,z4,z5]),(0,[z0,z1,z2,z935,z4,z5]),(0,[z0,z1,z2,z3,z4,z248]),(0,[z0,z2,z183,z178,z4,z5]),(0,[z0,z936,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z937,z5]),(0,[z0,z419,z1,z3,z4,z938]),(0,[z174,z0,z1,z223,z4,z5]),(0,[z0,z1,z202,z3,z588,z5]),(0,[z414,z0,z1,z213,z4,z5]),(0,[z0,z153,z71,z3,z4,z5]),(0,[z0,z2,z3,z939,z4,z5])],[(0,[z0,z1,z3,z4,z5,z940]),(0,[z0,z83,z3,z471,z4,z5]),(0,[z0,z424,z49,z3,z4,z5]),(0,[z0,z1,z717,z3,z4,z5]),(0,[z0,z1,z3,z9,z773,z5])],[(0,[z0,z83,z1,z3,z184,z5]),(0,[z0,z1,z402,z3,z4,z39]),(0,[z0,z353,z49,z3,z4,z5]),(0,[z0,z50,z2,z3,z4,z748])],[(0,[z0,z729,z2,z3,z4,z5]),(0,[z0,z243,z2,z323,z4,z5]),(0,[z0,z1,z2,z941,z4,z5]),(0,[z0,z1,z2,z3,z728,z35])],[(0,[z0,z1,z2,z3,z4,z942]),(0,[z0,z943,z2,z3,z4,z5]),(0,[z0,z1,z2,z299,z4,z40]),(0,[z0,z1,z2,z3,z944,z4]),(0,[z0,z1,z2,z945,z4,z5]),(0,[z0,z1,z2,z946,z4,z5]),(0,[z0,z1,z2,z3,z4,z947])],[(0,[z38,z419,z1,z233,z4,z5]),(0,[z16,z83,z1,z3,z17,z5]),(0,[z0,z438,z49,z3,z4,z5]),(0,[z0,z144,z1,z3,z164,z4]),(0,[z0,z1,z202,z178,z9,z5])],[(0,[z58,z226,z1,z3,z4,z5]),(0,[z0,z1,z948,z3,z4,z5]),(0,[z0,z629,z53,z3,z4,z5])]],
   [[(0,[z0,z1,z49,z3,z4,z362]),(0,[z0,z1,z402,z3,z64,z5])],[(0,[z109,z209,z141,z3,z4,z5]),(0,[z0,z1,z949,z3,z4,z5]),(0,[z0,z191,z385,z3,z4,z5]),(0,[z0,z1,z2,z950,z4,z5]),(0,[z0,z1,z270,z3,z4,z107])],[(0,[z58,z0,z385,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z951]),(0,[z0,z1,z3,z4,z5,z149]),(0,[z0,z53,z752,z3,z4,z5]),(0,[z952,z1,z2,z3,z4,z5])],[(0,[z0,z1,z953,z3,z4,z5]),(0,[z0,z954,z2,z3,z4,z5]),(0,[z0,z955,z2,z3,z4,z5]),(0,[z174,z0,z2,z471,z4,z5]),(0,[z224,z1,z2,z3,z4,z73]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z635,z49,z3,z4,z5]),(0,[z0,z2,z3,z151,z4,z5]),(1,[z0,z2,z3,z859,z5])],[(0,[z6,z1,z2,z876,z4,z5]),(0,[z0,z202,z183,z3,z9,z5]),(0,[z0,z957,z2,z3,z4,z5]),(0,[z0,z70,z153,z2,z4,z103])],[(0,[z958,z1,z2,z3,z4,z5]),(1,[z0,z2,z747,z4,z5]),(0,[z0,z66,z2,z3,z89,z5]),(0,[z0,z66,z2,z494,z3,z89]),(0,[z0,z153,z2,z3,z4,z103])],[(0,[z174,z0,z257,z2,z4,z5]),(0,[z0,z959,z2,z3,z4,z5]),(0,[z0,z1,z960,z3,z4,z5]),(0,[z0,z1,z692,z3,z4,z163])],[(0,[z0,z961,z2,z3,z4,z5]),(0,[z0,z419,z962,z3,z4,z5]),(0,[z963,z0,z1,z3,z4,z5]),(0,[z0,z2,z3,z4,z748,z166]),(0,[z0,z50,z2,z3,z317,z4])]],
   [[(0,[z0,z59,z210,z3,z4,z5]),(0,[z0,z1,z3,z9,z184,z5]),(0,[z0,z88,z2,z3,z159,z5]),(0,[z0,z61,z1,z3,z773,z5]),(0,[z0,z2,z3,z4,z5,z964]),(0,[z0,z2,z3,z965,z4,z5])],[(0,[z0,z966,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z967]),(0,[z0,z21,z2,z98,z4,z22]),(0,[z968,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z213,z4,z276])],[(1,[z0,z2,z98,z4,z176]),(0,[z0,z1,z2,z192,z4,z96]),(0,[z0,z61,z1,z203,z4,z5]),(0,[z0,z1,z3,z4,z158,z725])],[(0,[z0,z1,z2,z969,z4,z5]),(0,[z0,z2,z3,z4,z5,z970]),(0,[z0,z1,z3,z971,z4,z5]),(0,[z0,z2,z3,z4,z96,z383]),(0,[z972,z1,z2,z3,z4,z5])],[(0,[z0,z1,z141,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z973]),(0,[z729,z1,z2,z3,z4,z5]),(0,[z0,z189,z2,z3,z4,z356]),(0,[z38,z189,z2,z233,z4,z5]),(0,[z0,z1,z2,z3,z4,z938]),(0,[z0,z1,z974,z3,z4,z5]),(0,[z0,z48,z752,z3,z4,z5]),(0,[z0,z21,z32,z98,z4,z5]),(0,[z0,z66,z2,z3,z222,z89]),(0,[z0,z1,z2,z147,z126,z276])],[(0,[z0,z1,z975,z3,z4,z5]),(0,[z0,z202,z385,z3,z4,z5]),(0,[z0,z1,z2,z3,z102,z35])],[(0,[z0,z1,z225,z3,z4,z113]),(0,[z0,z976,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z725]),(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z977,z3,z4,z5])],[(0,[z0,z1,z2,z3,z978,z5]),(1,[z1,z2,z3,z4,z885])]],
   [[(0,[z608,z1,z2,z7,z4,z5]),(0,[z0,z979,z2,z3,z4,z5]),(0,[z0,z257,z2,z3,z332,z4]),(0,[z0,z256,z53,z3,z4,z5]),(0,[z0,z1,z427,z3,z4,z158])],[(0,[z38,z1,z2,z233,z4,z5]),(0,[z0,z980,z2,z3,z4,z5])],[],[(0,[z315,z209,z2,z3,z4,z5]),(0,[z0,z243,z2,z3,z4,z113]),(0,[z0,z1,z2,z3,z4,z981]),(0,[z160,z1,z2,z3,z4,z27]),(0,[z0,z338,z2,z3,z4,z5]),(0,[z0,z2,z385,z3,z4,z5]),(0,[z982,z1,z2,z3,z4,z5]),(0,[z0,z70,z367,z2,z4,z103])],[(0,[z0,z1,z2,z3,z983,z5]),(0,[z0,z1,z3,z9,z486,z5]),(0,[z0,z984,z1,z2,z4,z5]),(0,[z0,z1,z202,z3,z4,z461]),(0,[z0,z1,z3,z773,z57,z5])],[(0,[z0,z1,z2,z3,z430,z362]),(0,[z0,z1,z3,z4,z5,z985]),(0,[z0,z1,z2,z3,z4,z794])],[(0,[z0,z61,z1,z3,z184,z5]),(0,[z0,z1,z361,z3,z4,z5]),(0,[z0,z1,z2,z529,z126,z5]),(0,[z0,z256,z202,z3,z9,z5])],[(0,[z0,z1,z986,z3,z4,z5]),(0,[z0,z1,z2,z3,z987,z5]),(0,[z0,z1,z402,z126,z4,z5]),(0,[z0,z1,z2,z3,z64,z39]),(0,[z0,z1,z988,z3,z4,z5]),(0,[z174,z0,z1,z2,z127,z5]),(0,[z0,z1,z2,z3,z4,z989]),(0,[z0,z2,z3,z151,z4,z107])]],
   [[(0,[z0,z1,z2,z3,z4,z990]),(0,[z0,z1,z2,z3,z991,z5]),(0,[z0,z1,z3,z4,z5,z992]),(0,[z0,z1,z2,z3,z4,z377]),(0,[z0,z993,z2,z3,z4,z5]),(0,[z0,z658,z1,z3,z4,z163]),(0,[z0,z1,z994,z3,z4,z5]),(0,[z0,z2,z995,z3,z4,z5])],[(1,[z1,z2,z876,z4,z5]),(0,[z38,z1,z2,z876,z4,z5]),(0,[z0,z996,z2,z3,z4,z5])],[(0,[z0,z997,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z998,z5]),(0,[z16,z1,z2,z3,z756,z5]),(0,[z0,z1,z999,z3,z4,z5]),(0,[z0,z2,z1000,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1001,z5]),(0,[z0,z1,z2,z1002,z4,z5]),(0,[z0,z1,z2,z1003,z4,z5])],[(0,[z0,z189,z405,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z0,z1,z2,z1004,z4,z5]),(0,[z0,z1,z308,z62,z4,z5]),(0,[z0,z2,z1005,z3,z4,z5])],[(0,[z0,z1006,z2,z3,z4,z5]),(0,[z0,z1,z1007,z3,z4,z5])],[(0,[z0,z1,z1008,z3,z4,z5]),(0,[z0,z265,z2,z98,z4,z5]),(0,[z0,z1,z2,z3,z102,z29]),(0,[z0,z321,z2,z3,z4,z118]),(0,[z0,z2,z1009,z3,z4,z5]),(0,[z414,z0,z1,z2,z127,z5]),(0,[z0,z3,z151,z213,z4,z5])],[(0,[z0,z1,z1010,z3,z4,z5]),(0,[z0,z189,z402,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z461])]],
   [[(0,[z0,z1,z2,z1011,z4,z5]),(0,[z0,z1,z2,z3,z4,z1012]),(0,[z0,z256,z2,z203,z4,z5]),(0,[z0,z1,z2,z178,z4,z248])],[(0,[z6,z1,z2,z4,z207,z5]),(0,[z16,z1,z2,z3,z332,z17]),(0,[z565,z1,z2,z3,z4,z73]),(0,[z0,z48,z53,z3,z4,z54]),(0,[z0,z2,z183,z3,z4,z248])],[(0,[z58,z1,z15,z3,z4,z362]),(0,[z0,z3,z223,z471,z4,z5]),(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z411,z1,z2,z4,z103])],[(0,[z26,z1,z2,z3,z449,z4]),(0,[z0,z1,z2,z203,z4,z5]),(0,[z0,z1,z2,z609,z4,z40])],[(0,[z0,z1,z402,z3,z4,z5]),(0,[z0,z2,z1014,z3,z4,z5]),(0,[z0,z2,z1015,z3,z4,z5]),(0,[z0,z1,z1016,z3,z4,z5]),(0,[z1017,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z1018,z4,z5]),(0,[z0,z1,z2,z108,z3,z194]),(0,[z0,z1,z71,z3,z4,z5]),(0,[z0,z1019,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1020])],[(0,[z0,z243,z2,z3,z184,z5]),(0,[z0,z1,z2,z3,z4,z1021])]],
   [[(0,[z0,z1,z2,z3,z4,z1022]),(0,[z0,z1,z2,z1023,z4,z5]),(0,[z0,z1,z2,z3,z1024,z4]),(0,[z0,z1,z32,z3,z4,z22]),(0,[z0,z1,z1025,z3,z4,z5]),(0,[z0,z1,z147,z213,z126,z5])],[(0,[z0,z1026,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z1027,z4]),(0,[z16,z1,z3,z223,z17,z5]),(0,[z0,z2,z3,z4,z859,z5])],[(0,[z0,z74,z2,z130,z4,z5]),(0,[z0,z59,z2,z323,z4,z5]),(0,[z122,z1,z436,z3,z4,z5]),(0,[z0,z1,z1028,z3,z4,z5]),(0,[z0,z1,z2,z1029,z4,z5]),(0,[z0,z144,z2,z3,z4,z371]),(0,[z0,z1030,z1,z3,z4,z5]),(0,[z0,z1031,z2,z3,z4,z5]),(0,[z0,z41,z1,z3,z4,z163]),(0,[z0,z1,z2,z3,z728,z4])],[(0,[z0,z1,z2,z3,z1032,z5]),(0,[z0,z189,z2,z3,z431,z5]),(0,[z414,z0,z1,z402,z4,z5]),(0,[z16,z1,z2,z123,z17,z5]),(0,[z0,z1,z2,z1033,z4,z5]),(0,[z0,z2,z1034,z3,z4,z5]),(0,[z0,z2,z919,z3,z4,z5]),(0,[z0,z1,z2,z494,z3,z4]),(0,[z0,z50,z155,z3,z4,z166]),(0,[z0,z1,z3,z62,z4,z118])],[(0,[z0,z1,z2,z1035,z4,z5]),(0,[z0,z1,z1036,z3,z4,z5]),(0,[z0,z50,z1,z3,z164,z4])],[(0,[z0,z419,z1,z31,z4,z5]),(0,[z0,z1,z3,z4,z113,z163]),(0,[z0,z1,z2,z3,z4,z1037])],[(0,[z0,z1,z1038,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z362]),(0,[z122,z1,z709,z3,z4,z5]),(0,[z1,z2,z7,z876,z4,z5]),(0,[z0,z1,z2,z3,z4,z1039])],[(0,[z0,z1040,z1,z3,z4,z5]),(0,[z0,z1,z427,z3,z4,z5]),(0,[z0,z1,z1041,z3,z4,z5]),(0,[z0,z1,z1042,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z725]),(0,[z0,z1043,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z1044,z4]),(0,[z109,z729,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z431,z5]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z0,z1,z1046,z3,z4,z5]),(0,[z0,z1,z2,z1047,z3,z4]),(0,[z0,z1,z3,z1048,z4,z5])],[(0,[z0,z1,z2,z1049,z3,z4]),(0,[z1,z2,z3,z4,z73,z885]),(0,[z0,z153,z2,z111,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1050]),(0,[z0,z1,z2,z3,z4,z1051]),(1,[z1,z2,z3,z756,z5]),(0,[z0,z546,z2,z3,z4,z166]),(0,[z0,z1,z2,z3,z222,z4]),(0,[z0,z1,z3,z4,z773,z5]),(0,[z0,z1052,z2,z3,z4,z5]),(0,[z0,z1,z2,z1053,z4,z5]),(0,[z0,z2,z3,z151,z4,z276])],[(0,[z0,z1,z2,z3,z4,z1054]),(0,[z0,z1055,z2,z3,z4,z5]),(0,[z0,z1,z1056,z3,z4,z5]),(0,[z0,z1,z1057,z3,z4,z5]),(0,[z0,z1058,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1059]),(0,[z469,z1,z2,z3,z10,z5]),(0,[z0,z2,z3,z159,z5,z258]),(0,[z0,z162,z1,z62,z4,z118]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z2,z3,z4,z5,z1061]),(1,[z0,z1,z2,z819,z5])],[(0,[z0,z1,z2,z323,z4,z113]),(0,[z0,z1,z2,z3,z4,z1062]),(0,[z0,z1063,z2,z3,z4,z5])],[(0,[z0,z2,z3,z159,z261,z5]),(0,[z0,z699,z1,z3,z57,z5]),(0,[z0,z265,z1,z2,z4,z103]),(0,[z0,z1,z104,z3,z4,z158])],[(0,[z0,z1,z2,z3,z1064,z5]),(0,[z0,z1,z3,z4,z5,z1065]),(0,[z0,z1,z2,z3,z332,z4]),(0,[z0,z1066,z2,z3,z4,z5]),(0,[z0,z49,z3,z525,z4,z5]),(0,[z0,z297,z2,z3,z4,z5]),(0,[z0,z1,z618,z62,z4,z5])]],
   [[(0,[z38,z1,z2,z233,z4,z356]),(0,[z0,z2,z495,z98,z4,z5]),(0,[z0,z153,z2,z3,z4,z5]),(0,[z0,z1,z2,z111,z4,z330]),(0,[z0,z256,z67,z3,z4,z5]),(0,[z0,z2,z3,z159,z859,z5]),(0,[z0,z256,z2,z3,z4,z248]),(0,[z0,z70,z1,z2,z4,z795])],[(0,[z0,z59,z53,z3,z4,z5]),(0,[z224,z1,z225,z3,z4,z73]),(0,[z0,z1,z1067,z3,z4,z5])],[(0,[z0,z141,z3,z98,z4,z5]),(0,[z592,z1,z15,z3,z4,z5]),(0,[z0,z1068,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1069]),(0,[z0,z48,z53,z3,z4,z5]),(0,[z0,z1,z2,z1070,z4,z5]),(0,[z0,z66,z2,z3,z222,z4])],[(0,[z0,z2,z3,z471,z4,z5]),(0,[z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z3,z858,z4,z5]),(0,[z0,z378,z1,z3,z4,z163]),(1,[z0,z153,z2,z4,z103])],[(0,[z0,z1071,z2,z3,z4,z5]),(0,[z0,z959,z225,z3,z4,z5]),(0,[z0,z1,z2,z33,z4,z176])],[(0,[z0,z257,z2,z3,z4,z5]),(0,[z0,z1,z2,z1072,z4,z5]),(0,[z0,z1,z2,z1073,z4,z5]),(0,[z0,z1,z2,z3,z1074,z5]),(0,[z0,z48,z2,z192,z4,z5])],[(0,[z0,z1,z1075,z3,z4,z5])],[(0,[z0,z1076,z2,z3,z4,z5]),(0,[z58,z1,z15,z3,z430,z5])]],
   [[(0,[z523,z209,z2,z3,z4,z5]),(0,[z0,z1,z2,z31,z4,z5]),(0,[z0,z1,z2,z3,z64,z5]),(0,[z0,z1,z2,z108,z3,z112])],[(0,[z0,z59,z2,z3,z4,z113]),(0,[z0,z1,z3,z4,z5,z1077]),(0,[z0,z1,z225,z3,z4,z163])],[(0,[z0,z2,z3,z1078,z4,z5]),(0,[z0,z66,z238,z3,z89,z5])],[(0,[z0,z1,z232,z3,z4,z5]),(0,[z0,z1079,z2,z3,z4,z5]),(0,[z0,z1080,z2,z3,z4,z5]),(0,[z0,z1,z86,z3,z4,z551])],[(0,[z0,z1,z2,z3,z4,z1081]),(0,[z0,z162,z1,z858,z4,z5]),(0,[z0,z1,z858,z62,z4,z5]),(0,[z0,z1,z1082,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z74,z2,z480,z4,z5]),(0,[z414,z0,z1,z2,z819,z5]),(0,[z0,z92,z2,z3,z102,z35])],[(0,[z0,z257,z2,z346,z3,z4]),(0,[z0,z83,z1,z3,z332,z4]),(0,[z0,z1,z2,z3,z1083,z5]),(0,[z0,z92,z977,z3,z4,z5])],[(0,[z0,z1,z2,z1084,z4,z5]),(0,[z0,z2,z3,z747,z4,z5])]],
   [[(0,[z0,z1,z2,z1085,z4,z5]),(0,[z0,z1,z1086,z3,z4,z5]),(0,[z0,z1,z405,z3,z4,z356]),(0,[z38,z1,z405,z233,z4,z5]),(0,[z0,z1,z251,z3,z4,z163])],[(0,[z0,z1,z2,z3,z1087,z5]),(0,[z0,z1,z2,z323,z184,z5])],[(0,[z0,z1,z2,z3,z4,z1088]),(0,[z0,z1,z3,z184,z5,z163]),(0,[z0,z21,z2,z98,z4,z5]),(0,[z0,z2,z3,z4,z5,z34]),(0,[z0,z1,z2,z108,z3,z517]),(0,[z0,z1,z1089,z3,z4,z5]),(0,[z0,z1,z1090,z3,z4,z5]),(0,[z0,z1,z251,z3,z102,z35])],[(0,[z0,z1,z2,z3,z430,z5]),(0,[z0,z1,z2,z3,z4,z1091]),(0,[z0,z36,z1,z62,z4,z5]),(0,[z0,z1,z2,z3,z4,z54]),(0,[z0,z1092,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1093]),(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z48,z210,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1095]),(0,[z0,z1,z3,z4,z54,z163]),(0,[z0,z1,z53,z203,z4,z5]),(0,[z0,z1,z180,z3,z4,z22]),(0,[z0,z2,z3,z98,z4,z176]),(0,[z0,z50,z427,z3,z4,z166]),(0,[z0,z1096,z2,z3,z4,z5]),(0,[z0,z2,z183,z203,z4,z5]),(0,[z0,z1097,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1098,z4,z5]),(0,[z122,z0,z1,z3,z4,z461]),(0,[z0,z66,z2,z3,z661,z5]),(0,[z0,z1,z1099,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1100]),(0,[z0,z1,z2,z190,z4,z5]),(0,[z0,z1,z2,z3,z4,z1101])],[(0,[z0,z1,z2,z3,z1102,z5]),(0,[z0,z1,z2,z4,z1103,z5]),(0,[z0,z1,z2,z876,z4,z5]),(0,[z0,z1,z2,z3,z1104,z5]),(0,[z0,z1,z3,z4,z5,z1105])]],
   [[(0,[z122,z1,z366,z3,z4,z5]),(0,[z0,z1,z2,z37,z4,z40])],[(0,[z0,z1106,z1,z2,z3,z4]),(0,[z0,z243,z86,z3,z4,z5]),(0,[z0,z2,z147,z151,z126,z5])],[(0,[z0,z66,z2,z3,z674,z5]),(0,[z0,z1,z202,z203,z9,z5])],[(0,[z0,z369,z2,z3,z4,z5]),(0,[z0,z1107,z1,z2,z4,z5]),(0,[z0,z296,z49,z3,z4,z5])],[(0,[z122,z1,z3,z384,z4,z5]),(0,[z0,z1108,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z1109,z4]),(0,[z0,z2,z192,z159,z4,z5]),(0,[z0,z1110,z2,z3,z4,z5]),(0,[z0,z1,z2,z108,z3,z633]),(0,[z0,z1111,z1,z3,z4,z5])],[(0,[z0,z59,z2,z3,z184,z5]),(0,[z0,z1,z1112,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1113]),(0,[z0,z1,z2,z3,z1114,z4])],[(0,[z0,z1115,z2,z3,z4,z5]),(0,[z0,z67,z49,z3,z4,z5]),(0,[z0,z351,z1,z3,z4,z163]),(0,[z0,z66,z67,z3,z89,z5])],[(0,[z0,z1116,z2,z3,z4,z5]),(0,[z16,z1,z2,z346,z3,z17]),(0,[z349,z1,z2,z3,z4,z27]),(0,[z0,z66,z2,z3,z683,z5]),(0,[z0,z573,z2,z33,z4,z5]),(0,[z0,z1,z2,z1117,z4,z5]),(0,[z0,z1,z2,z819,z127,z5])]],
   [[(0,[z58,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1118]),(0,[z0,z1,z53,z3,z184,z5]),(0,[z0,z1,z2,z3,z4,z1119]),(0,[z174,z0,z1,z2,z431,z5]),(0,[z0,z2,z49,z192,z4,z5]),(0,[z0,z1,z1120,z3,z4,z5]),(0,[z0,z1121,z2,z3,z4,z5])],[(0,[z0,z2,z3,z1122,z4,z5]),(0,[z0,z50,z49,z3,z4,z163]),(0,[z0,z86,z183,z3,z4,z5])],[(0,[z617,z76,z2,z3,z4,z5]),(0,[z0,z1123,z2,z3,z4,z5]),(0,[z0,z1124,z2,z3,z4,z5])],[(0,[z0,z1125,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1126]),(0,[z0,z1,z427,z192,z4,z5])],[(0,[z0,z59,z49,z3,z4,z5]),(0,[z0,z1,z2,z1127,z4,z5]),(0,[z0,z1128,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1129]),(0,[z0,z245,z2,z3,z4,z166]),(0,[z0,z1,z2,z3,z4,z505]),(0,[z0,z385,z3,z4,z57,z5]),(0,[z0,z1,z2,z3,z4,z1130]),(0,[z0,z1,z2,z4,z795,z103])],[(0,[z0,z1,z2,z298,z126,z5]),(0,[z0,z1,z2,z1131,z4,z5]),(0,[z0,z236,z1,z62,z4,z5]),(0,[z0,z50,z2,z3,z91,z4]),(0,[z0,z1132,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1133,z4]),(0,[z0,z1,z1134,z3,z4,z5]),(0,[z0,z88,z2,z3,z859,z5]),(0,[z0,z1,z2,z3,z102,z393]),(0,[z0,z1,z2,z365,z4,z103]),(0,[z0,z1135,z1,z3,z4,z5])],[(0,[z110,z526,z2,z3,z4,z5]),(0,[z0,z1,z3,z332,z223,z4]),(0,[z174,z0,z1,z2,z332,z4]),(0,[z0,z1,z752,z3,z4,z5]),(0,[z0,z1,z2,z3,z1136,z4]),(0,[z0,z1,z270,z3,z4,z276])]],
   [[(0,[z0,z1,z2,z3,z184,z113]),(0,[z0,z1,z631,z3,z9,z5]),(0,[z0,z50,z238,z3,z4,z5]),(0,[z0,z1137,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1138,z5]),(0,[z0,z1139,z2,z3,z4,z5])],[(0,[z0,z48,z67,z3,z4,z5]),(0,[z0,z238,z3,z4,z96,z5]),(0,[z0,z1,z1140,z3,z4,z5]),(0,[z0,z1141,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z725,z163])],[(0,[z0,z1,z2,z3,z4,z1142]),(0,[z0,z1,z346,z3,z223,z4]),(0,[z0,z74,z180,z3,z4,z5])],[(0,[z6,z1,z2,z7,z4,z5]),(0,[z0,z1,z3,z1143,z4,z5])],[(0,[z58,z0,z1,z3,z4,z118])],[(0,[z0,z59,z2,z31,z4,z5]),(0,[z0,z1,z15,z31,z4,z5]),(0,[z0,z1,z2,z3,z1144,z4]),(0,[z0,z1,z1145,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z22]),(0,[z0,z1,z3,z1146,z4,z5])],[(0,[z0,z1,z2,z1147,z3,z4]),(0,[z0,z1148,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1149,z5]),(0,[z0,z1,z2,z192,z102,z4]),(0,[z0,z1,z86,z3,z4,z248])]],
   [[(0,[z0,z1,z2,z3,z1150,z5]),(0,[z0,z1,z2,z3,z4,z1151]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z243,z3,z4,z5,z163]),(0,[z0,z1,z2,z3,z756,z5]),(0,[z0,z1,z1152,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z27]),(0,[z0,z1,z2,z3,z1153,z5]),(0,[z0,z50,z2,z3,z4,z341])],[(0,[z0,z243,z2,z3,z4,z362]),(0,[z0,z1,z53,z31,z4,z5]),(0,[z0,z1,z32,z3,z4,z5]),(0,[z0,z1,z3,z222,z769,z4]),(0,[z0,z162,z1,z62,z4,z377]),(0,[z0,z1,z3,z164,z4,z40])],[(0,[z0,z1,z14,z31,z4,z5]),(0,[z0,z61,z1,z31,z4,z5]),(0,[z0,z1,z2,z3,z4,z1154]),(0,[z0,z1,z202,z3,z9,z248]),(0,[z0,z1155,z2,z3,z4,z5])],[(0,[z0,z1,z2,z4,z1156,z5]),(0,[z0,z1157,z2,z3,z4,z5]),(0,[z0,z2,z453,z3,z4,z96])],[(0,[z0,z419,z1,z62,z4,z5]),(0,[z0,z1158,z2,z3,z4,z5]),(0,[z0,z1,z1159,z3,z4,z5])],[(0,[z0,z1,z2,z346,z3,z4]),(0,[z0,z2,z471,z4,z123,z5]),(0,[z224,z1,z3,z4,z73,z149]),(0,[z0,z1,z1160,z3,z4,z5]),(0,[z0,z690,z1,z62,z4,z5])],[(0,[z0,z1,z1161,z3,z4,z5]),(0,[z1,z709,z15,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z885])],[(0,[z0,z1162,z1,z2,z4,z5]),(0,[z0,z1,z2,z1163,z4,z5]),(0,[z0,z1,z402,z7,z4,z5]),(0,[z0,z1,z1164,z3,z4,z5]),(1,[z0,z1,z2,z4,z795])]],
   [[(0,[z0,z210,z49,z3,z4,z5]),(0,[z0,z1,z1165,z3,z4,z5]),(0,[z0,z1166,z2,z3,z4,z5]),(0,[z0,z83,z1,z3,z57,z5]),(0,[z0,z1,z3,z4,z57,z461])],[(0,[z0,z1,z1167,z3,z4,z5]),(0,[z0,z1168,z2,z3,z4,z5]),(0,[z342,z1,z14,z3,z4,z5]),(0,[z592,z1,z2,z233,z4,z5]),(0,[z1,z2,z3,z4,z756,z5]),(0,[z0,z1,z2,z3,z4,z1169]),(0,[z0,z1170,z2,z3,z4,z5]),(0,[z0,z1171,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1172]),(0,[z0,z301,z3,z213,z4,z5]),(0,[z0,z1,z3,z102,z164,z35])],[(0,[z0,z83,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z1173,z5]),(0,[z0,z1,z2,z3,z1174,z5]),(0,[z0,z21,z180,z98,z4,z5]),(0,[z1175,z1,z2,z3,z4,z5]),(0,[z0,z297,z2,z3,z4,z118]),(0,[z0,z1,z2,z1176,z4,z5]),(0,[z0,z92,z2,z3,z102,z4])],[(0,[z1,z2,z3,z876,z4,z5]),(0,[z0,z419,z1,z3,z4,z723]),(0,[z0,z74,z2,z747,z4,z5]),(0,[z0,z1,z2,z192,z4,z166]),(0,[z0,z1,z203,z4,z5,z163]),(0,[z0,z1,z2,z203,z4,z248])],[(0,[z0,z962,z2,z3,z4,z5]),(0,[z0,z1,z3,z1177,z4,z5]),(0,[z0,z301,z2,z147,z126,z5]),(0,[z0,z1,z2,z3,z112,z728])],[(0,[z0,z1,z239,z31,z4,z5]),(0,[z0,z162,z1,z31,z4,z5]),(0,[z38,z577,z1,z2,z4,z5]),(0,[z0,z1,z2,z1178,z4,z5]),(0,[z0,z256,z49,z3,z4,z5]),(0,[z0,z1,z2,z1179,z4,z5]),(0,[z0,z2,z3,z1180,z4,z5]),(0,[z0,z1,z1181,z3,z4,z5])],[(0,[z0,z162,z321,z62,z4,z5])]],
   [[(0,[z0,z1,z1182,z3,z4,z5]),(0,[z0,z2,z3,z1183,z4,z5]),(0,[z0,z48,z643,z3,z4,z5]),(0,[z0,z1,z3,z593,z57,z5])],[(0,[z0,z189,z2,z3,z4,z39]),(0,[z0,z1184,z2,z3,z4,z5]),(0,[z0,z752,z49,z3,z4,z5]),(0,[z0,z1,z3,z1185,z4,z5])],[(0,[z0,z369,z2,z3,z4,z356]),(0,[z0,z1,z2,z192,z4,z163])],[(0,[z0,z243,z2,z31,z4,z5]),(0,[z0,z1,z49,z3,z184,z5]),(0,[z0,z1,z1186,z3,z4,z5]),(0,[z0,z1,z225,z3,z4,z158]),(0,[z0,z579,z2,z3,z4,z96])],[(0,[z0,z1,z2,z3,z1187,z5]),(0,[z0,z1,z3,z4,z1188,z5]),(0,[z0,z1,z3,z1189,z4,z5]),(0,[z0,z83,z1,z346,z3,z4]),(0,[z0,z296,z752,z3,z4,z5])],[(0,[z0,z1,z31,z4,z5,z163]),(0,[z0,z2,z3,z1190,z4,z5]),(0,[z0,z1191,z2,z3,z4,z5]),(0,[z0,z1,z1192,z3,z4,z5]),(0,[z0,z86,z385,z3,z4,z158]),(0,[z0,z1,z2,z4,z5,z795])],[(0,[z0,z189,z2,z3,z64,z5]),(0,[z0,z1,z67,z3,z4,z913]),(0,[z0,z1,z202,z3,z417,z5])],[(0,[z0,z1,z2,z3,z1193,z5]),(0,[z0,z1194,z1,z3,z4,z5]),(0,[z0,z50,z2,z3,z4,z230]),(0,[z0,z338,z53,z3,z4,z5]),(0,[z0,z1,z2,z1195,z4,z5]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z297,z3,z62,z4,z5]),(0,[z0,z1,z2,z3,z1196,z5]),(0,[z0,z1,z2,z3,z4,z1197]),(0,[z0,z1,z2,z3,z102,z463])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 540) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1073).take 64) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1137)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 540, 64] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 115).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 232).take 24).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 115, 24] = true :=
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

end PEqualNP.Outside.L_meta_39819

theorem PEqualNP.Outside.L_meta_39819 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008241312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39819.solve