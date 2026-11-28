import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38555

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
  Nat.testBit (4008373992 * 2 ^ 32 + 4008372392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x04000206140810a5#64 ++ 0xffc49e8e3d18f1ff#64 : BitVec 128),
   (0x23012830c8634652#64 ++ 0xfffb6971cee74e73#64 : BitVec 128),
   (0x8a0c518163058b18#64 ++ 0xb6cc7181f3078f9c#64 : BitVec 128),
   (0xcc1e81da03b80de0#64 ++ 0x6dff81fe03f80fe0#64 : BitVec 128),
   (0xf00ffc0003d6e000#64 ++ 0xe39ffe0003fff000#64 : BitVec 128),
   (0x002fffedbc000000#64 ++ 0x1faffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x002fffedbc000000 0x1faffffffc000000

def z1 : W := mkw 0x04000206140810a5 0xffc49e8e3d18f1ff

def z2 : W := mkw 0x23012830c8634652 0xfffb6971cee74e73

def z3 : W := mkw 0x23012a34dc634652 0xfffffffffee74e73

def z4 : W := mkw 0x8a0c518163058b18 0xb6cc7181f3078f9c

def z5 : W := mkw 0xcc1e81da03b80de0 0x6dff81fe03f80fe0

def z6 : W := mkw 0xf00ffc0003d6e000 0xe39ffe0003fff000

def z7 : W := mkw 0x002003edbc000000 0x1c2001fffc000000

def z8 : W := mkw 0xf02fffedbfd6e000 0xffbffffffffff000

def z9 : W := mkw 0xcc1e83de17b81de5 0xffff9ffe3ff8ffff

def z10 : W := mkw 0xf00ffc0003d6e000 0x001b600002e70000

def z11 : W := mkw 0xfa0ffd8163d7eb18 0xf7dfff81f3ffff9c

def z12 : W := mkw 0x0a00018160010b18 0x14400181f0000f9c

def z13 : W := mkw 0x2101283088624442 0x493308700ce04063

def z14 : W := mkw 0xf00ffc1003f6e440 0xefffff7003fffe60

def z15 : W := mkw 0xab0d79b1eb67cf5a 0x003b6171c2e70e00

def z16 : W := mkw 0x2b0129b1e8634f5a 0xfffb69f1fee74fff

def z17 : W := mkw 0x0c1001da00280de0 0x0c6001fe00000fe0

def z18 : W := mkw 0x30017c000046e000 0x82007e000007f000

def z19 : W := mkw 0xcc100002039809a0 0x0000000001180180

def z20 : W := mkw 0x002ed7cd34000000 0x0004968e30000000

def z21 : W := mkw 0x00217e25bc000000 0x12007e01fc000000

def z22 : W := mkw 0x0000000000000000 0xb6c410803100819c

def z23 : W := mkw 0x8a0c518163058b18 0x00086101c2070e00

def z24 : W := mkw 0x8a0c518163058b18 0x14486181f2070f9c

def z25 : W := mkw 0x002ffffdbc200440 0x7ffffffffee00e60

def z26 : W := mkw 0x04000206140810a5 0x9e401e8e3c00f1ff

def z27 : W := mkw 0xf02ffde9abd6e000 0x003b6171c2e70000

def z28 : W := mkw 0x0c1e81da00280de0 0x0def81fe00000fe0

def z29 : W := mkw 0x0000000000000000 0xffc008000c004073

def z30 : W := mkw 0x27012a36dc6b56f7 0xffffffffffffffff

def z31 : W := mkw 0xcc1e81ca039809a0 0x619f808e03f80180

def z32 : W := mkw 0xfc1ffc1203feede0 0xe3dffe0003ffffe0

def z33 : W := mkw 0x2001280000424000 0xe39b680002e74000

def z34 : W := mkw 0xd00ed4000394a000 0x0000000000000000

def z35 : W := mkw 0x040c5387340810a5 0xffccff8ffd18f1ff

def z36 : W := mkw 0x00212e249c000000 0x00000e000c000000

def z37 : W := mkw 0x000e81c800000000 0x0daf81fe00000000

def z38 : W := mkw 0x8a00000043058b18 0xa040000003078f9c

def z39 : W := mkw 0x2001282088424000 0xffbb6971cee74000

def z40 : W := mkw 0xdc1ed5da03bcade0 0x6dff97fe03f8bfe0

def z41 : W := mkw 0x8a2fffedff058b18 0xbfefffffff078f9c

def z42 : W := mkw 0xcc3fffffbfb80de0 0x7ffffffffff80fe0

def z43 : W := mkw 0xce1ed1db63bd8ff8 0xfffff1fff3ff8ffc

def z44 : W := mkw 0x000ffc0000000000 0x038ffe0000000000

def z45 : W := mkw 0xcc1e81da03b80de0 0xefff9ffe03f8ffe0

def z46 : W := mkw 0x880c518123048908 0x0000000000000000

def z47 : W := mkw 0x0200000040010210 0xb6cc7181f3078f9c

def z48 : W := mkw 0x27012a36dc6b56f7 0xfffbef7fceff7e73

def z49 : W := mkw 0x04000206140810a5 0x92049e8e3d18f19f

def z50 : W := mkw 0x202fffedbc424000 0xffbffffffee74000

def z51 : W := mkw 0xf300001043f7e652 0xe050000003fffe73

def z52 : W := mkw 0x2101283088624442 0x6dfb09700ee04e63

def z53 : W := mkw 0x0000000000000000 0xe3849e000118f000

def z54 : W := mkw 0x23012830c8634652 0xffffff71cffffe73

def z55 : W := mkw 0xf20ffc0043d7e210 0xf7dfff01c3fffe10

def z56 : W := mkw 0x0000000000000000 0xe040000000004073

def z57 : W := mkw 0xab0d79b1eb67cf5a 0xffff79f1ffe7cfff

def z58 : W := mkw 0x000c518120000000 0xb6cc7181f100819c

def z59 : W := mkw 0x0001282088000000 0x1fab6971cc000000

def z60 : W := mkw 0x0000020414000000 0xffc49e8e3c004073

def z61 : W := mkw 0x002fffedbc000000 0x002ff7fff0000000

def z62 : W := mkw 0x7003ac0000d26000 0x41138e0000f87000

def z63 : W := mkw 0x800c500003048000 0xa28c700003078000

def z64 : W := mkw 0x2101283088624442 0xebbb68700ee74063

def z65 : W := mkw 0xf00ffc0003d6e000 0x001ff60003ffb000

def z66 : W := mkw 0x23012830c8634652 0x1c7b6171cee70e73

def z67 : W := mkw 0x7003ac0000d26000 0xe39bee0002ff7000

def z68 : W := mkw 0x880c518123048908 0x000410803100818c

def z69 : W := mkw 0xca0ed18163958b18 0xf7dff181f3ff8f9c

def z70 : W := mkw 0x0000000000000000 0x1f8008000c000000

def z71 : W := mkw 0xcc1e81da03b80de0 0x607b017003f80fe0

def z72 : W := mkw 0x002fffedbc000000 0x092bef7fcc000000

def z73 : W := mkw 0x04000206140810a5 0x49008e0e0c187063

def z74 : W := mkw 0x8b0c51b1eb258f5a 0xbeec71f1ff078fff

def z75 : W := mkw 0x4412825e14b814e5 0xfff79efe3df8f1ff

def z76 : W := mkw 0xf81ffdd803f6ed40 0x003b617002e70e00

def z77 : W := mkw 0xcc10001203b80de0 0x6dd4808e03f80fe0

def z78 : W := mkw 0x8a2d7fa5ff058b18 0xb6cc7f81ff078f9c

def z79 : W := mkw 0x04000206140810a5 0x0004968e3118b18c

def z80 : W := mkw 0x23012830c8634652 0x003b6171c2e70e00

def z81 : W := mkw 0xeb1fa9f8cbf34f52 0x003b6171c2e70e00

def z82 : W := mkw 0x02012820c8010210 0xbfeb6971ce070e10

def z83 : W := mkw 0xf00ffc0003d6e000 0x411bee0002ff7000

def z84 : W := mkw 0x23012820c8434212 0x92006801cc074013

def z85 : W := mkw 0xf80ffd8003d6e900 0xe7dfff8003ffff80

def z86 : W := mkw 0xce1e81da43bd8ff8 0xedff81fe03ff8ffc

def z87 : W := mkw 0x0000020414000000 0x1c00008e3c000000

def z88 : W := mkw 0x8a0c518163058b18 0x000c7181f3078f8c

def z89 : W := mkw 0x0000001000200440 0x003b017002e00e00

def z90 : W := mkw 0x8e0c5387770d9bbd 0xffccff8fff1fffff

def z91 : W := mkw 0x0200000040010210 0xb6c86101c2070e10

def z92 : W := mkw 0xcc3fffefbf9809a0 0x1faffffffd180180

def z93 : W := mkw 0xba0d7d816347eb18 0xb6cc7f81f307ff9c

def z94 : W := mkw 0xcc1e81ca039809a0 0x0daf81fe01180180

def z95 : W := mkw 0x30217e25bc46e000 0x92007e01fc07f000

def z96 : W := mkw 0x0000001000200440 0x4933007000e00060

def z97 : W := mkw 0xf30ffc30cbf7e652 0xe3bfff71c3fffe00

def z98 : W := mkw 0xc00e800003900000 0x619f800003f80000

def z99 : W := mkw 0xfc10001203feede0 0xe050000003ffffe0

def z100 : W := mkw 0x04000002000800a0 0x0004808e01180180

def z101 : W := mkw 0x002fffedbc000000 0xffaffffffd18f000

def z102 : W := mkw 0xfc1ffdda03feede0 0xeffffffe03ffffe0

def z103 : W := mkw 0xf00ed40003d6e000 0xe014960003fff000

def z104 : W := mkw 0xab0d79b1eb67cf5a 0xb6ff71f1f3e78f9c

def z105 : W := mkw 0xcc10001203b81de5 0xe050000003f8ffff

def z106 : W := mkw 0x04000002000800a0 0x60400000011801e0

def z107 : W := mkw 0x0000000000000000 0x6dc0000000000060

def z108 : W := mkw 0x002ed7cd34000000 0x168cf78ff0000000

def z109 : W := mkw 0x042ed7cf340810a5 0xffc49e8e3d18f1ff

def z110 : W := mkw 0x0023ae6c9c000000 0x09238e7e0c000000

def z111 : W := mkw 0x0000020414001005 0x92001e003c00f01f

def z112 : W := mkw 0xc81e81d803b00d40 0x003b017002e00e00

def z113 : W := mkw 0x000e81d800200440 0x6dff81fe02e00e60

def z114 : W := mkw 0x002003cd34000000 0x0000008e30000000

def z115 : W := mkw 0x04000002000810a5 0x00400000000001ff

def z116 : W := mkw 0x04000206140810a5 0x0000008e3000018c

def z117 : W := mkw 0x802fffedbf048000 0xbfafffffff078000

def z118 : W := mkw 0x002c53edbc000000 0x1eac71fffc000000

def z119 : W := mkw 0x27012832c86b56f7 0xfffb6971cfffffff

def z120 : W := mkw 0xef10001243fb4ff2 0xe050000003ff4ff3

def z121 : W := mkw 0xef1fa9facbfb4ff2 0xffffe9ffcfff4ff3

def z122 : W := mkw 0xed1fa9fa8bfa4de2 0x6dff89fe0ff84fe3

def z123 : W := mkw 0xfa2fffedffd7eb18 0xffffffffffffff9c

def z124 : W := mkw 0x0023ae6c9c000000 0x1fabef7fcc000000

def z125 : W := mkw 0x23012830c8634652 0x9e606971cc074e73

def z126 : W := mkw 0xef1fa9facbfb4ff2 0x6dffe1ffc3ff0fe0

def z127 : W := mkw 0xf00ffc0003d6e000 0xa29f700003e78000

def z128 : W := mkw 0x03000030c8210652 0x1c600171cc000e73

def z129 : W := mkw 0x8c0c0386170819a5 0xffcc9f8e3f18ffff

def z130 : W := mkw 0x0000500000048000 0x8200700000078000

def z131 : W := mkw 0x2001280000424000 0xe39ffe0003fff000

def z132 : W := mkw 0x23012820c8434212 0xf39b6801cee74013

def z133 : W := mkw 0x042003efbc0810a5 0x1c6001fffc0001ff

def z134 : W := mkw 0x8a0c500043058b18 0xa2cc700003078f9c

def z135 : W := mkw 0x7003ac0000d26000 0x0013000000e00000

def z136 : W := mkw 0x0000001000200440 0x6dfb017002e00e60

def z137 : W := mkw 0x4412805a00b804e0 0x4933807e00f80060

def z138 : W := mkw 0x0000000000001005 0x800000000000f01f

def z139 : W := mkw 0xd00ffc000394a000 0x038ffe000118b000

def z140 : W := mkw 0x04000002000810a5 0xf6c410803118f1ff

def z141 : W := mkw 0x04000002000810a5 0xedc4808e0118f1ff

def z142 : W := mkw 0x00012a249c000000 0x1faffffffc000000

def z143 : W := mkw 0x23012820c8434212 0x00006001c0070000

def z144 : W := mkw 0xab0d79a1eb47cb1a 0xb6cc7981ff07cf9f

def z145 : W := mkw 0x0000020414001005 0x9f849e8e3c00f01f

def z146 : W := mkw 0xc00e800003900000 0x001b000002e00000

def z147 : W := mkw 0x0c3fffffbc280de0 0x1feffffffc000fe0

def z148 : W := mkw 0x0200000040058218 0x800000000007801c

def z149 : W := mkw 0x04000012002804e0 0x6dff81fe03f80fe0

def z150 : W := mkw 0xf30ffc30cbf7e652 0xfffb6971cee74e73

def z151 : W := mkw 0x000c518120000000 0x168c7181f0000000

def z152 : W := mkw 0xf003ac0003d6e000 0xe1138e0003fff000

def z153 : W := mkw 0x23012a24dc435217 0x92007e01fc07f01f

def z154 : W := mkw 0x002ffde9a8000000 0x1fab6971cc000000

def z155 : W := mkw 0x0000002088000000 0x1c200171cc000000

def z156 : W := mkw 0xff1ffdfacbffeff2 0xffffffffcffffff3

def z157 : W := mkw 0x0a00018160010b18 0xb6c86181f2070f9c

def z158 : W := mkw 0xd00ed4000394a000 0x000496000118b000

def z159 : W := mkw 0x04000002000800a0 0xffc4908e311881fc

def z160 : W := mkw 0xf000000003d6e000 0xe010000003fff000

def z161 : W := mkw 0x002fffedbc001005 0x9faffffffc00f01f

def z162 : W := mkw 0x002003edbc000000 0x1fa49ffffc000000

def z163 : W := mkw 0x23217e25fc434212 0x92007e01fc074013

def z164 : W := mkw 0x232ffffdfc634652 0xfffffffffee74e73

def z165 : W := mkw 0x04000206140810a5 0xfc40008e3d18f1ff

def z166 : W := mkw 0x000ffd8120000000 0x178fff81f0000000

def z167 : W := mkw 0x00212bedbc000000 0x1fab69fffc000000

def z168 : W := mkw 0xcc1ed1da03bc8de0 0xeffff1fe03ff8fe0

def z169 : W := mkw 0xc81e81d803b00d40 0x0dbf81fe02e00e00

def z170 : W := mkw 0x0000000000000000 0x490008000c004063

def z171 : W := mkw 0x000d79a1a8000000 0x1faf79f1fc000000

def z172 : W := mkw 0xcf1e81facbb90ff2 0x7dff81ffcff80ff3

def z173 : W := mkw 0x880e81c803000900 0x2def81fe03000f80

def z174 : W := mkw 0xcc1e801203b80de0 0x61df800003f80fe0

def z175 : W := mkw 0x0000001000200440 0x0c60017000000e60

def z176 : W := mkw 0xcc10001203b80de0 0x6dfb017003f80fe0

def z177 : W := mkw 0x0a00000040010b18 0x0040000000000f9c

def z178 : W := mkw 0x300ffc000046e000 0x838ffe000007f000

def z179 : W := mkw 0x04000206140810a5 0x1c40008e3c0001ff

def z180 : W := mkw 0xf00ffc0003d6e000 0x41179e0001f8f000

def z181 : W := mkw 0x4002800000900000 0x4113800000f80000

def z182 : W := mkw 0x2123ae7c9c624442 0x49338e7e0ce04063

def z183 : W := mkw 0x000fa9e888000000 0x1fafe9ffcc000000

def z184 : W := mkw 0x4412805a00b804e0 0x6dfb817e02f80e60

def z185 : W := mkw 0x04000206140810a5 0xdb009e0e3c18f07f

def z186 : W := mkw 0x4410001200b804e0 0x4010000000f80060

def z187 : W := mkw 0x0200000040010210 0x00086101c2070e00

def z188 : W := mkw 0x002e83edbc000000 0x1daf81fffc000000

def z189 : W := mkw 0xf00ffd8123d6e000 0xf79fff81f3fff000

def z190 : W := mkw 0xf00ffc0003d6e000 0x619fe00003ff0000

def z191 : W := mkw 0xcc1e81da03b81de5 0xedff81fe03f8ffff

def z192 : W := mkw 0xf00ffdc803d6e000 0xefbffffe03fff000

def z193 : W := mkw 0xcc3e83ffbfb80de0 0x7dff81fffff80fe0

def z194 : W := mkw 0x002fffedbc000000 0xffeffffffc004073

def z195 : W := mkw 0x8a0c518163058b18 0xffcc7981ff07cfff

def z196 : W := mkw 0xcc1e81ca039809a0 0x6dc4808e011801e0

def z197 : W := mkw 0x020052057405921d 0x92007e01fc07f01f

def z198 : W := mkw 0x8a0c518163058b18 0xf7ccff81f31fff9c

def z199 : W := mkw 0x2101282088424002 0x000008000c004003

def z200 : W := mkw 0x33017c30c867e652 0xfffb7f71cee7fe73

def z201 : W := mkw 0xcc10001203b80de0 0x6050000003f80fe0

def z202 : W := mkw 0x8a0c518163058b18 0xb6c86101c2070e10

def z203 : W := mkw 0xcc1ed1db23bc8de8 0x6dff91fe33f88fec

def z204 : W := mkw 0x0423ae6e9c0810a5 0x49238e7e0c187063

def z205 : W := mkw 0x2300001040634652 0xe050000002e74e73

def z206 : W := mkw 0x0000001000200440 0x6050000002e00e60

def z207 : W := mkw 0xd02fffedbf94a000 0x1faffffffd18b000

def z208 : W := mkw 0x7413ac5a00fa64e0 0x49338e7e00f87060

def z209 : W := mkw 0x2000000000424000 0xe010000002e74000

def z210 : W := mkw 0x2323ae7cdc634652 0xfffbef7fcee74e73

def z211 : W := mkw 0x880c018003000900 0x24cc018003000f80

def z212 : W := mkw 0x04000216142814e5 0xffff9ffe3ff8ffff

def z213 : W := mkw 0xce1ed1cb639d8bb8 0xb6ccf18ff31f8f9c

def z214 : W := mkw 0xc83ffdf9abb00d40 0x003b6171c2e00e00

def z215 : W := mkw 0xfc1ffdca03dee9a0 0xe39ffe8e03fff180

def z216 : W := mkw 0xcc1ed1db23b80de0 0x7ffff1fff3f80fe0

def z217 : W := mkw 0x0000018120000000 0x14000181f0000000

def z218 : W := mkw 0x8000000003048000 0xa000000003078000

def z219 : W := mkw 0x002ffde9a8000000 0x0dafe1ffc0000000

def z220 : W := mkw 0xef1ff9fbebffcffa 0xfffff9ffffffcfff

def z221 : W := mkw 0x002ffde9a8000000 0x002b6171c0000000

def z222 : W := mkw 0x23012830c8634652 0x1fbb6971cee70e00

def z223 : W := mkw 0x2300000040434212 0x8000000000074013

def z224 : W := mkw 0x23212bfdfc634652 0xfffb69fffee74e73

def z225 : W := mkw 0x0100003088200442 0x082000700c000063

def z226 : W := mkw 0x8a0c519163258f58 0xffff71f1f3e78ffc

def z227 : W := mkw 0x000ed1c920000000 0x1faff1fff0000000

def z228 : W := mkw 0x000ffc0000000000 0xe38ffe000118f000

def z229 : W := mkw 0xc81e81d803b00d40 0x61bf817003f80e00

def z230 : W := mkw 0xc02fffedbf900000 0x7fbffffffff80000

def z231 : W := mkw 0x042fffefbc0810a5 0xffeffffffd18f1ff

def z232 : W := mkw 0x04000002000800a0 0xffc4888e0d1841f3

def z233 : W := mkw 0x8e0c5183630d9bbd 0xf6cc7181f31fffff

def z234 : W := mkw 0x800c500003048000 0x0008600002070000

def z235 : W := mkw 0x002ed7edbc000000 0x1c2497fffc000000

def z236 : W := mkw 0x33017c20c847e212 0x92007e01cc07f013

def z237 : W := mkw 0x882ed7cd37048908 0x0004968e3100818c

def z238 : W := mkw 0x0423ae6e9c0810a5 0xffe79efe3d18f1ff

def z239 : W := mkw 0x8a0ed1c963058b18 0xbfeff1fff3078f9c

def z240 : W := mkw 0x04000002000800a0 0x6dc4808e011801e0

def z241 : W := mkw 0x03012830c8210652 0x1feb6971cc000e73

def z242 : W := mkw 0xf70ffe36dffff6f7 0xffffffffffffffff

def z243 : W := mkw 0x30017c000046e000 0x0000600000070000

def z244 : W := mkw 0x882fffedbf048908 0x1faffffffd00818c

def z245 : W := mkw 0xf30ffc30cbf7e652 0xffffff71cffffe73

def z246 : W := mkw 0x0c1001da00280de0 0x6dfb01fe02e00fe0

def z247 : W := mkw 0x0a00518160058b18 0x96407181f0078f9c

def z248 : W := mkw 0x23012830c8634652 0xf2506801cee74e73

def z249 : W := mkw 0x23012830c8634652 0x6dfb6171c2e70e60

def z250 : W := mkw 0x002fffedbc000000 0x1c2b61fffc000000

def z251 : W := mkw 0x002ffe6c9c000000 0x0baffe7e0c000000

def z252 : W := mkw 0x8a0c018043058b18 0xa4cc018003078f9c

def z253 : W := mkw 0x0000000000000000 0xa284100001008000

def z254 : W := mkw 0x04000206140810a5 0x1c44968e3d18b1ff

def z255 : W := mkw 0x0000000000000000 0xa04000000100819c

def z256 : W := mkw 0x8a00018163058b18 0xb4400181f3078f9c

def z257 : W := mkw 0x04000206140810a5 0xffc0088e3c0041ff

def z258 : W := mkw 0x2f1129fac86b4ff2 0xfffb69ffcee74ff3

def z259 : W := mkw 0x302fffedbc46e000 0x9faffffffc07f000

def z260 : W := mkw 0x0000020414000000 0xbfc49e8e3d00819c

def z261 : W := mkw 0x020c518160010210 0xb6cc7181f2070e10

def z262 : W := mkw 0xf40ffe0617def0a5 0xffdffe8e3ffff1ff

def z263 : W := mkw 0xf80ffd8123d6e908 0xe39ffe8033fff18c

def z264 : W := mkw 0xf00e800003d6e000 0xe19f800003fff000

def z265 : W := mkw 0xf32ffffdfff7e652 0xfffffffffffffe73

def z266 : W := mkw 0xcc12805a03b80de0 0x6973807e03f80fe0

def z267 : W := mkw 0xcc1e81da03b80de0 0x0c7b01fe02e00fe0

def z268 : W := mkw 0x0200500160058218 0x92007001f007801c

def z269 : W := mkw 0x0a2fffedfc010b18 0x1feffffffc000f9c

def z270 : W := mkw 0xcc1e81da03b80de0 0xffff91fe33f88ffc

def z271 : W := mkw 0x7403ae0614da70a5 0xffd79e8e3df8f1ff

def z272 : W := mkw 0xab2ffffdff67cf5a 0xffffffffffe7cfff

def z273 : W := mkw 0x0000000000000000 0x6184800001180000

def z274 : W := mkw 0x443fffffbcb804e0 0x5fbffffffcf80060

def z275 : W := mkw 0x0000000000000000 0xe00000000118f000

def z276 : W := mkw 0xf40ffc0203def0a5 0xe3dffe0003fff1ff

def z277 : W := mkw 0xaf0d7bb7ff6fdfff 0xffffffffffffffff

def z278 : W := mkw 0x0800018120000908 0x000000803000018c

def z279 : W := mkw 0xcc1e81ca039809a0 0x0004808e01180180

def z280 : W := mkw 0xda0ed5816395ab18 0xb6ccf781f31fbf9c

def z281 : W := mkw 0x0000020414000000 0xff849e8e3d18f000

def z282 : W := mkw 0x0022864c14000000 0x0000860e00000000

def z283 : W := mkw 0xf00ffc0003d6e000 0xf7dffe8033fff19c

def z284 : W := mkw 0x0000500120048008 0x000010003000800c

def z285 : W := mkw 0xaa0d79816347cb18 0xf7df7981f3e7cf9c

def z286 : W := mkw 0x0020026c9c000000 0x0820007e0c000000

def z287 : W := mkw 0x230fa9f8c8634652 0xffffe9ffcee74e73

def z288 : W := mkw 0xf40ffe0617def0a5 0xe39ffe8e33fff18c

def z289 : W := mkw 0x25012a369c6a54e7 0xfff79efe3df8f1ff

def z290 : W := mkw 0xfc3fffffbffeede0 0xffffffffffffffe0

def z291 : W := mkw 0x23012830c8634652 0x493b6971cee74e63

def z292 : W := mkw 0xf00ffe0417d6f005 0xf39ffe003ffff01f

def z293 : W := mkw 0x0000020414000000 0x1f849e8e3c000000

def z294 : W := mkw 0x000e81c800000000 0x0004808e00000000

def z295 : W := mkw 0x0c10001200280de0 0x0040000000000fe0

def z296 : W := mkw 0xf00ffc0003d6e000 0x821b7e0002e7f000

def z297 : W := mkw 0x880c018003000900 0xb6cc118033008f9c

def z298 : W := mkw 0x002fffcd34000000 0x038ffe8e30000000

def z299 : W := mkw 0x0000020414000000 0x0004968e30000000

def z300 : W := mkw 0x0000000000000000 0x920010003000801c

def z301 : W := mkw 0x0c1003de14281de5 0x1c6001fe3c000fff

def z302 : W := mkw 0xce10001243bd8ff8 0xe050000003ff8ffc

def z303 : W := mkw 0x04000206140810a5 0x6dc48e8e0d1871e3

def z304 : W := mkw 0xf3012830cbf7e652 0xfffb6971cffffe73

def z305 : W := mkw 0x04000002000800a0 0x0c40008e000001e0

def z306 : W := mkw 0xf02fffcd37d6e000 0xe39ffe8e33fff000

def z307 : W := mkw 0x2300001040634652 0xedfb017002e74e73

def z308 : W := mkw 0x04000206140800a0 0x7fc49e8e3d1801e0

def z309 : W := mkw 0x0000020414001005 0x100000003c00001f

def z310 : W := mkw 0xca1ed1d963b58f58 0x003b6171c2e70e00

def z311 : W := mkw 0x04000206140810a5 0xe044968e3118f1ff

def z312 : W := mkw 0x8a00500163058b18 0xb2407001f3078f9c

def z313 : W := mkw 0x23012830c8634652 0xffff79f1ffe7cfff

def z314 : W := mkw 0xf400000203def0a5 0xe050000003fff1ff

def z315 : W := mkw 0x6513a87a88fa44e2 0x4933887e0cf84063

def z316 : W := mkw 0xf000000003d6e000 0xe3949e0003fff000

def z317 : W := mkw 0x04000002000810a5 0xe04000000118f1ff

def z318 : W := mkw 0x000c518120000000 0x0004108030000000

def z319 : W := mkw 0x8e0c5183630d8bb8 0xffccf18ff31f8ffc

def z320 : W := mkw 0x8a2ffde9eb058b18 0xb6ef71f1f3078f9c

def z321 : W := mkw 0xa30d7830cb67c652 0xffff7971cfe7ce73

def z322 : W := mkw 0x8c0c5387370c99ad 0x0004968e3118b18c

def z323 : W := mkw 0x0003ac0000000000 0x01038e0000000000

def z324 : W := mkw 0x0000000000000000 0x24c8010002000e00

def z325 : W := mkw 0x03000020c8010212 0x10000001cc000013

def z326 : W := mkw 0x000ffc2088000000 0x1fafff71cc000000

def z327 : W := mkw 0x0300001040210652 0x0040000000000e73

def z328 : W := mkw 0x042003efbc0810a5 0xffe49ffffd18f1ff

def z329 : W := mkw 0x100054000004a000 0x000016000000b000

def z330 : W := mkw 0xf000000003d6e000 0x0010000002e70000

def z331 : W := mkw 0x0001282088000000 0x092308700c000000

def z332 : W := mkw 0x800c500003048000 0x0004100001008000

def z333 : W := mkw 0x800c518123048000 0xb68c7181f3078000

def z334 : W := mkw 0x06000206540912b5 0xffccff8fff1fffff

def z335 : W := mkw 0x04000206140810a5 0xb6c4968e3118b19c

def z336 : W := mkw 0xf00ffc0003d6e000 0x8204fe00011ff000

def z337 : W := mkw 0xc810001003b00d40 0x0010000002e00e00

def z338 : W := mkw 0x8a0c518163058b18 0x92047081f107819c

def z339 : W := mkw 0x03000030c8210652 0xbee86171ce070e73

def z340 : W := mkw 0xcc1ffdda03b80de0 0x6ffffffe03f80fe0

def z341 : W := mkw 0x0000000000000000 0x82001e000000f000

def z342 : W := mkw 0xf30ffc30cbf7e652 0x003b6171c2e70e00

def z343 : W := mkw 0x34017e06144ef0a5 0xffc4fe8e3d1ff1ff

def z344 : W := mkw 0x7003ac0000d26000 0xe3979e0001f8f000

def z345 : W := mkw 0xec1fa9da03fa4de0 0xefffe9fe03ff4fe0

def z346 : W := mkw 0x2101283088624442 0xfff308700ce04073

def z347 : W := mkw 0x23012830c8634652 0xdb336871cce74073

def z348 : W := mkw 0x8a2ed7cd77058b18 0xb6ccf78ff3078f9c

def z349 : W := mkw 0x4433ae7e9cb804e0 0x49338e7e0cf80060

def z350 : W := mkw 0xcc1e81da03b80de0 0xffff89fe0ff84ff3

def z351 : W := mkw 0xd00ed4000394a000 0xe3849e000118f000

def z352 : W := mkw 0x8a0c518163058b18 0x14441181f1008f9c

def z353 : W := mkw 0x0000000000000000 0x1684108030000000

def z354 : W := mkw 0x700ffc0000d26000 0x439ffe0000f87000

def z355 : W := mkw 0x07000236dc2916f7 0x1c6001fffc000fff

def z356 : W := mkw 0x300000000046e000 0x800000000007f000

def z357 : W := mkw 0xf400020617def0a5 0xffd49e8e3ffff1ff

def z358 : W := mkw 0x0000000000000000 0x144000803000019c

def z359 : W := mkw 0xab0d79b1eb67cf5a 0xfffb6971cee74e73

def z360 : W := mkw 0x0000000000000000 0xffc49e000d18f073

def z361 : W := mkw 0xcc1e83de17b80de0 0x7fff9ffe3ff80fe0

def z362 : W := mkw 0xf02ffde9abd6e000 0xe3bfff71c3fff000

def z363 : W := mkw 0xab012830cb67cf5a 0xfffb6971cfe7cfff

def z364 : W := mkw 0x232ffffdfc634652 0x1fbffffffee70e00

def z365 : W := mkw 0x8e000002430d9bbd 0xe0400000031fffff

def z366 : W := mkw 0x0000000000000000 0x41008e0000187000

def z367 : W := mkw 0xca1ed1d963b58f58 0xb6ff71f1f3e78f9c

def z368 : W := mkw 0xc40e8206179810a5 0xffdf9e8e3ff8f1ff

def z369 : W := mkw 0x00217e25bc000000 0x1fab7f71fc000000

def z370 : W := mkw 0x25012a369c6a54e7 0x49338e7e0cf87063

def z371 : W := mkw 0xc00ed00003948000 0xe39ff00003ff8000

def z372 : W := mkw 0x0e1001db60290ff8 0x1c6001fff0000ffc

def z373 : W := mkw 0x2001280000424000 0x8200680000074000

def z374 : W := mkw 0xcc3ffdfbabb80de0 0x6dffe1ffc3f80fe0

def z375 : W := mkw 0x040e83ce140810a5 0xffef9ffe3d18f1ff

def z376 : W := mkw 0x4c1281da00b80de0 0x4d7381fe00f80fe0

def z377 : W := mkw 0xfa0ffd8163d7eb18 0xb6df7181f3e78f9c

def z378 : W := mkw 0x2300001040634652 0x0010000002e70e00

def z379 : W := mkw 0x04000002000810a5 0x000000000118b18c

def z380 : W := mkw 0x0000000000000000 0xffc418803d00c1ff

def z381 : W := mkw 0x27012832c86b46f2 0xffffe9ffcfff4ff3

def z382 : W := mkw 0x7103ac3088f26442 0x49338e700cf87063

def z383 : W := mkw 0xf00ffc0003d6e000 0xffdffe000ffff073

def z384 : W := mkw 0x880c518123048908 0xb6c410803100819c

def z385 : W := mkw 0xf40ffc0203dee0a0 0xefdffe8e03fff1e0

def z386 : W := mkw 0xf001280003d6e000 0xe39b680003fff000

def z387 : W := mkw 0x0e00038774091bbd 0x1c40018ffc000fff

def z388 : W := mkw 0xab0d29b0cb634f52 0xffff69f1cfe74ff3

def z389 : W := mkw 0x000e81c800000000 0x002b017000000000

def z390 : W := mkw 0x8a0c518163058b18 0x168c7181f2070e00

def z391 : W := mkw 0x042fffefbc0810a5 0x1faffffffd18b18c

def z392 : W := mkw 0x04000002000810a5 0x4000000000187063

def z393 : W := mkw 0x232ffdf9e8634652 0x003b6171c2e70e00

def z394 : W := mkw 0x4412805a00b804e0 0x6df780fe01f801e0

def z395 : W := mkw 0x000e83cc14000000 0x1faf9ffe3c000000

def z396 : W := mkw 0xcc1e81ca039809a0 0x24cc818e03180f80

def z397 : W := mkw 0x032ffffdfc210652 0x1feffffffc000e73

def z398 : W := mkw 0x882fffedbf000900 0x3fefffffff000f80

def z399 : W := mkw 0xcc1ed1cb239c89a8 0x0004908e3118818c

def z400 : W := mkw 0xf00fac0003d26000 0x619f8e0003f87000

def z401 : W := mkw 0x04000206140810a5 0x7dc4808e3d1801ff

def z402 : W := mkw 0xf00ffc0003d6e000 0xe01b600003fff000

def z403 : W := mkw 0x27000012406b56f7 0xe050000003ffffff

def z404 : W := mkw 0x0200001040210650 0xfffb6171c2e70e70

def z405 : W := mkw 0x800c500003048000 0xe38cfe00031ff000

def z406 : W := mkw 0x30017c000046e000 0xe384fe00011ff000

def z407 : W := mkw 0xc00ffc0003900000 0x639ffe0003f80000

def z408 : W := mkw 0x0000000000000000 0x0000000000000000

def z409 : W := mkw 0x04000002000800a0 0x4900800e00180060

def z410 : W := mkw 0x880c019003200d40 0x6dff01f003e00fe0

def z411 : W := mkw 0x002ed7cd34000000 0x0daf97fe30000000

def z412 : W := mkw 0x8800000003000900 0x2040000003000f80

def z413 : W := mkw 0x002fffedbc000000 0x1204fe8ffc000000

def z414 : W := mkw 0x04000206140810a5 0x5d408e8e3c1871ff

def z415 : W := mkw 0xd40ed606179cb0a5 0xffc49e8e3d18f1ff

def z416 : W := mkw 0x020c518160058218 0x968c7181f007801c

def z417 : W := mkw 0xc81e81c803900900 0x0000000000000000

def z418 : W := mkw 0x0200500160058218 0x00006001c0070000

def z419 : W := mkw 0xc83ffffdbfb00d40 0x1fbffffffee00e00

def z420 : W := mkw 0xf02fffedbfd6e000 0x1fbffffffee70000

def z421 : W := mkw 0x0f1001fac8290ff2 0x1c6001ffcc000ff3

def z422 : W := mkw 0x6713a87ac8fb46f2 0xfffbe97fceff4e73

def z423 : W := mkw 0x0023afedbc000000 0x1d238ffffc000000

def z424 : W := mkw 0x8a2c53edff058b18 0xbeec71ffff078f9c

def z425 : W := mkw 0x04000206140810a5 0xe3849e8e3118f18c

def z426 : W := mkw 0x002fffedbc000000 0xbfeffffffd00819c

def z427 : W := mkw 0xd00ed4000394a000 0x619f960003f8b000

def z428 : W := mkw 0xf41ffc5a03fee4e0 0xebbffe7e03fff060

def z429 : W := mkw 0xce1ed1db63bd8ff8 0x6dffe1ffc3ff0fe0

def z430 : W := mkw 0x0000500120000000 0x12007001f0000000

def z431 : W := mkw 0x820c500043058210 0xb6cc7101c3078e10

def z432 : W := mkw 0x000ed40000000000 0x0004960000000000

def z433 : W := mkw 0x232fffedfc434212 0x9faffffffc074013

def z434 : W := mkw 0x2001281000624440 0xeffb697002e74e60

def z435 : W := mkw 0x8a2ffde9eb058b18 0x002b6171c2070e00

def z436 : W := mkw 0x8a0ffd8163058b18 0xb7cfff81f3078f9c

def z437 : W := mkw 0xf30ffc20cbd7e212 0xf39ffe01cffff013

def z438 : W := mkw 0xce1c519363bd8ff8 0xf6dc7181f3ff8ffc

def z439 : W := mkw 0x0c1003de14281de5 0xffe49ffe3d18ffff

def z440 : W := mkw 0x2101283088624442 0x5fbb6971cce04063

def z441 : W := mkw 0xfa00000043d7eb18 0xe050000003ffff9c

def z442 : W := mkw 0x23012820c8434212 0xffc06801cc074073

def z443 : W := mkw 0x8c0c0182030809a0 0x6dcc818e03180fe0

def z444 : W := mkw 0x0000001000200440 0xfffb09700ee04e73

def z445 : W := mkw 0xcc1e81da03b80de0 0x493780fe01f801e0

def z446 : W := mkw 0xf42fffefbfdef0a5 0xfffffffffffff1ff

def z447 : W := mkw 0xcc1e81da03b80de0 0x493b817e02f80e60

def z448 : W := mkw 0xcc1e81da03b80de0 0x003f81fe03f80f80

def z449 : W := mkw 0x022fffedfc010210 0xbfeffffffe070e10

def z450 : W := mkw 0x0000020414000000 0x12001e003c000000

def z451 : W := mkw 0x8a0c518163058b18 0xa0486101c3078f9c

def z452 : W := mkw 0x04217e27bc0810a5 0xffc4fe8ffd18f1ff

def z453 : W := mkw 0xcc1e83ce179819a5 0xffc49e8e3d18f1ff

def z454 : W := mkw 0x8a0c518163058b18 0x24cc6181c3070f80

def z455 : W := mkw 0xd80ed5812394a908 0x000496803118b18c

def z456 : W := mkw 0x8a00000043058b18 0x0000000002070e00

def z457 : W := mkw 0x00217e25bc001005 0x92007e01fc00f01f

def z458 : W := mkw 0x002ed5c920000000 0x0000000000000000

def z459 : W := mkw 0x04000002000810a5 0xffc008000d18f1ff

def z460 : W := mkw 0x0020560534000000 0x0000160030000000

def z461 : W := mkw 0x0a0c518160010b18 0x16cc7181f0000f9c

def z462 : W := mkw 0x002ed7cd34000000 0x1f849e8e3c000000

def z463 : W := mkw 0xfe1ffddb63ffeff8 0xfffffffff3fffffc

def z464 : W := mkw 0x23017831e867c65a 0xfffb7971fee7ce7f

def z465 : W := mkw 0xd02ed7cd3794a000 0x0004968e3118b000

def z466 : W := mkw 0x212ffffdbc624442 0x5fbffffffce04063

def z467 : W := mkw 0x04000206140810a5 0x1fc49e8e3c0001ff

def z468 : W := mkw 0x0000000000000000 0x24c4008001000180

def z469 : W := mkw 0x0200000040010210 0xffc86901ce074e73

def z470 : W := mkw 0x0200000160010218 0x10000001f000001c

def z471 : W := mkw 0x04000206140810a5 0x0800000e0c000063

def z472 : W := mkw 0x441e81da00b804e0 0x4dbf81fe00f80060

def z473 : W := mkw 0x2201280040434210 0xf7db6901c2e74e10

def z474 : W := mkw 0xce1e81db63b90ff8 0x7dff81fff3f80ffc

def z475 : W := mkw 0x0001282088000000 0xffeb6971cc004073

def z476 : W := mkw 0x880c518123048908 0x168c7181f100818c

def z477 : W := mkw 0xcc3faffe9fb80de0 0x6dff8ffe0ff80fe0

def z478 : W := mkw 0xc81e81d803b00d40 0x24ff01f003e00f80

def z479 : W := mkw 0xc00e800003900000 0xe39f9e0003f8f000

def z480 : W := mkw 0x7303ac30c8f36652 0xfffbef71ceff7e73

def z481 : W := mkw 0x042fffefbc0810a5 0x5faffffffc187063

def z482 : W := mkw 0x0410005a002804e0 0x0820007e00000060

def z483 : W := mkw 0x7000000000d26000 0x4010000000f87000

def z484 : W := mkw 0x0002804800000000 0x0923807e00000000

def z485 : W := mkw 0x002fffedbc000000 0x09279efe3c000000

def z486 : W := mkw 0x0000000000000000 0x03849e0000000000

def z487 : W := mkw 0xf00ffc208bd6e000 0xffbfff71cffff000

def z488 : W := mkw 0x000e800000000000 0x018f800000000000

def z489 : W := mkw 0x042fffefbc0810a5 0x1feffffffc0001ff

def z490 : W := mkw 0x840c5206170c90a5 0xffccfe8e3f1ff1ff

def z491 : W := mkw 0x000001c800000000 0x0c2001fe00000000

def z492 : W := mkw 0x0c3003ffbc280de0 0x1c6001fffc000fe0

def z493 : W := mkw 0xcc10021617b81de5 0xffd49e8e3ff8ffff

def z494 : W := mkw 0x4412825e14b814e5 0x49338e7e0cf87063

def z495 : W := mkw 0xcc1e83de17b81de5 0x7dff81fe3ff80fff

def z496 : W := mkw 0x23012830c8634652 0x5d730971cce04e73

def z497 : W := mkw 0x880c518123000900 0x36cc7181f3000f80

def z498 : W := mkw 0x040e81ca000800a0 0x6def81fe011801e0

def z499 : W := mkw 0x8a0d79a1eb058b18 0xbfef79f1ff078f9c

def z500 : W := mkw 0x230d79b1e8634652 0xffff79f1fee74e73

def z501 : W := mkw 0x000c018000000000 0x048c018000000000

def z502 : W := mkw 0x040ffe06140810a5 0xffcffe8e3d18f1ff

def z503 : W := mkw 0xef112832cbfb4ff2 0xfffb6971cfff4ff3

def z504 : W := mkw 0xfa0ffd8163d7eb18 0xe39fff01c3fffe00

def z505 : W := mkw 0x04000206140810a5 0x49049e8e3d18f1ef

def z506 : W := mkw 0x00217fedbc000000 0x1e207ffffc000000

def z507 : W := mkw 0x800c500003048000 0xb6cc70803307819c

def z508 : W := mkw 0x8e0c5387770d9bbd 0xb6ccf78ff31fbf9c

def z509 : W := mkw 0xc81e81d803b00d40 0x6dfb017002e00e60

def z510 : W := mkw 0x0000000000000000 0x000496000118b000

def z511 : W := mkw 0x0000020414001005 0x00000e000c007003

def z512 : W := mkw 0x002fffedbc000000 0x122b7f71fc000000

def z513 : W := mkw 0x2301281040634652 0xe3db680002e74e73

def z514 : W := mkw 0x0023fe6dbc000000 0x1b23fe7ffc000000

def z515 : W := mkw 0x7003fc0000d6e000 0xc313fe0000fff000

def z516 : W := mkw 0x0023ac6888000000 0x0023007000000000

def z517 : W := mkw 0x04000206140810a5 0x1f849e8e3d18b18c

def z518 : W := mkw 0x2300001040634652 0xf6d86101c2e74e73

def z519 : W := mkw 0x0023ae6c9c000000 0x1fa79efe3c000000

def z520 : W := mkw 0xf02ffe25bfd6e000 0xf39ffe01fffff000

def z521 : W := mkw 0x2001280000424000 0x4113080000e04000

def z522 : W := mkw 0x0000000000000000 0xf7c49e803118f19c

def z523 : W := mkw 0x042ed7cf340810a5 0x0004968e3118b18c

def z524 : W := mkw 0x8a0c518163058b18 0xa044108033078f9c

def z525 : W := mkw 0xf02ffe6c9fd6e000 0xebbffe7e0ffff000

def z526 : W := mkw 0x8a0c538577058b18 0xbfccff8fff078f9c

def z527 : W := mkw 0x230ffc30c8634652 0xffffff71cee74e73

def z528 : W := mkw 0xa00d78000346c000 0xe39f780003e7c000

def z529 : W := mkw 0x0e00038774091bbd 0xffc49f8ffd18ffff

def z530 : W := mkw 0xce1e81da43b90ff0 0xffffe1ffc3ff0ff0

def z531 : W := mkw 0x0000020414001005 0xffc01e003c00f07f

def z532 : W := mkw 0xfc1e81da03feede0 0xedff81fe03ffffe0

def z533 : W := mkw 0x04000206140810a5 0x0000860e00183000

def z534 : W := mkw 0xd00ed4000394a000 0xa28cf600031fb000

def z535 : W := mkw 0x200ffc0000424000 0xe39ffe0002e74000

def z536 : W := mkw 0xab0c51916367cf5a 0xf6dc7181f3e7cfff

def z537 : W := mkw 0x04000206140810a5 0x5f849e8e3c187063

def z538 : W := mkw 0x702fffedbcd26000 0x5fbffffffcf87000

def z539 : W := mkw 0x0a00018160010b18 0x00000101c0000e00

def z540 : W := mkw 0xd40ed606179cb0a5 0x0004968e3118b18c

def z541 : W := mkw 0x002ffde9a8000000 0x03afff71c0000000

def z542 : W := mkw 0x27000216546b56f7 0xffd49e8e3fffffff

def z543 : W := mkw 0xce3fffffffbd8ff8 0xffffffffffff8ffc

def z544 : W := mkw 0xcc1c019203b80de0 0x64dc018003f80fe0

def z545 : W := mkw 0x8800000003048908 0x000000000100818c

def z546 : W := mkw 0xf0017c0003d6e000 0xe2107e0003fff000

def z547 : W := mkw 0x7023ae6c9cd26000 0x49338e7e0cf87000

def z548 : W := mkw 0x8a0c518163058b18 0x92087101f2078e1c

def z549 : W := mkw 0x8e0c5387770d9bbd 0xbecc718fff078fff

def z550 : W := mkw 0x04000002000800a0 0xefc49e8e0118f1e0

def z551 : W := mkw 0x8e1c51db632d8ff8 0xbeec71fff3078ffc

def z552 : W := mkw 0xf40ffe0617def0a5 0xeb9ffe0e0ffff063

def z553 : W := mkw 0xb00d7c000346e000 0xa28c7e000307f000

def z554 : W := mkw 0xd00000000394a000 0x000000000118b000

def z555 : W := mkw 0x03000030c8210652 0x00200171c0000e00

def z556 : W := mkw 0x8c0c5387370c99ad 0xffc49e8e3d18f1ff

def z557 : W := mkw 0xf00ffe0417d6e000 0xff9ffe8e3ffff000

def z558 : W := mkw 0x002ffde9a8000000 0x16af71f1f0000000

def z559 : W := mkw 0xcc1e81da03b80de0 0x0c6481fe01180fe0

def z560 : W := mkw 0xfa0ffc0043d7eb18 0xe3dffe0003ffff9c

def z561 : W := mkw 0x2001280000424000 0x001b600002e70000

def z562 : W := mkw 0x0a00018160010b18 0xb6c41181f1008f9c

def z563 : W := mkw 0x0000000000000000 0x920008000c004013

def z564 : W := mkw 0xf00ffc0003d6e000 0xe39b680002e74000

def z565 : W := mkw 0x32017c016047e218 0x92007e01f007f01c

def z566 : W := mkw 0x0c1001da00280de0 0x6de481fe01180fe0

def z567 : W := mkw 0xf00ffc0003d6e000 0x039ffe0002e70000

def z568 : W := mkw 0x2100001000624442 0x4010000000e04063

def z569 : W := mkw 0x23012830c8634652 0xe3bb6971c2e74e00

def z570 : W := mkw 0xf10ffc308bf6e442 0xebbffe700ffff063

def z571 : W := mkw 0xcc3ed7cf379809a0 0x0004968e31180180

def z572 : W := mkw 0x042fffefbc0800a0 0x7feffffffd1801e0

def z573 : W := mkw 0xf81ffdd803f6ed40 0xe3bfff7003fffe00

def z574 : W := mkw 0xef3ffffffffb4ff2 0xffffffffffff4ff3

def z575 : W := mkw 0x0a2003edfc010b18 0x1c6001fffc000f9c

def z576 : W := mkw 0x0001283088200440 0x7ffb6971cee00e60

def z577 : W := mkw 0x04000002000810a5 0xe3c49e000118f1ff

def z578 : W := mkw 0x820c500163058218 0xb28c7001f307801c

def z579 : W := mkw 0x000c518120000000 0x00086101c0000000

def z580 : W := mkw 0x002001e9a8000000 0x00200171c0000000

def z581 : W := mkw 0xc00e801003b00440 0x6dff817003f80e60

def z582 : W := mkw 0x0001280000000000 0x038b680000000000

def z583 : W := mkw 0x000c538534000000 0x1f8cff8ffc000000

def z584 : W := mkw 0x27012a26dc4b52b7 0xffc4fe8ffd1ff1ff

def z585 : W := mkw 0x06005207740d92bd 0xffc4fe8ffd1ff1ff

def z586 : W := mkw 0x8a0c518163058b18 0xa28c7101c3078e00

def z587 : W := mkw 0x880c018003000900 0x0004008001000180

def z588 : W := mkw 0x04000206140810a5 0xe9408e0e0d18f1ff

def z589 : W := mkw 0x04000206140810a5 0xf2401e003d18f1ff

def z590 : W := mkw 0xcc1e83ce179819a5 0x0004968e3118b18c

def z591 : W := mkw 0xfc1fadda03fa6de0 0x6dff8ffe03f87fe0

def z592 : W := mkw 0x0000000000000000 0x0d84808e00000000

def z593 : W := mkw 0xef1fabfedffb5ff7 0xffffffffffffffff

def z594 : W := mkw 0x8e2fffefff0d9bbd 0xffefffffff1fffff

def z595 : W := mkw 0x0000000000000000 0xa288600002070000

def z596 : W := mkw 0x032003fdfc210652 0x1c6001fffc000e73

def z597 : W := mkw 0xfe0fff8777dffbbd 0xffdfff8fffffffff

def z598 : W := mkw 0x0c1001ca000809a0 0x0000008e00000180

def z599 : W := mkw 0x022fffedfc058218 0x9faffffffc07801c

def z600 : W := mkw 0x23217e35fc634652 0xfffb7f71fee74e73

def z601 : W := mkw 0x0200000040010210 0x14400101c0000e10

def z602 : W := mkw 0x002ffe25bc000000 0x138ffe01fc000000

def z603 : W := mkw 0x8a2fffedff058b18 0x1faffffffe070e00

def z604 : W := mkw 0x081001d800200d40 0x0020017000000e00

def z605 : W := mkw 0x30017e041446f005 0x92007e003c07f01f

def z606 : W := mkw 0x0000000000000000 0x16886101c0000000

def z607 : W := mkw 0xc000000003900000 0x6010000003f80000

def z608 : W := mkw 0xcc1e83de17b81de5 0x6dff8ffe0ff87fe3

def z609 : W := mkw 0xc41e805a03b804e0 0x69bf807e03f80060

def z610 : W := mkw 0xc40e8002039800a0 0x6ddf808e03f801e0

def z611 : W := mkw 0xfb0ffdb1ebf7ef5a 0xfffffff1ffffffff

def z612 : W := mkw 0x30017c000046e000 0xe39b7e0002e7f000

def z613 : W := mkw 0x002d7fa5bc000000 0x168c7f81fc000000

def z614 : W := mkw 0x03000030c8210652 0x7dfb0171cee00e73

def z615 : W := mkw 0x0800018000000900 0x0440018000000f80

def z616 : W := mkw 0x000ffdc800000000 0x0faffffe00000000

def z617 : W := mkw 0xcc3fffffbfb81de5 0xfffffffffff8ffff

def z618 : W := mkw 0x232ffdf9e8634652 0xfffb6971cee74e73

def z619 : W := mkw 0xf00c500003d6e000 0xe29c700003fff000

def z620 : W := mkw 0x8a0c538577059b1d 0xb6cc7f81ff07ff9f

def z621 : W := mkw 0xeb1fa9f8cbf34f52 0xfffb6971cee74e73

def z622 : W := mkw 0x2300001040634652 0xffd008000ee74e73

def z623 : W := mkw 0x7403ae0614da70a5 0x49138e0e0cf87063

def z624 : W := mkw 0x04000206140810a5 0xffc08e0e0c187073

def z625 : W := mkw 0x0000000000000000 0x1c4000000c000073

def z626 : W := mkw 0x23012820c8434212 0xb6c86901ce074e13

def z627 : W := mkw 0xef1e81da43fb4ff2 0xedff81fe03ff4ff3

def z628 : W := mkw 0x07000236dc2916f7 0xffe49ffffd18ffff

def z629 : W := mkw 0xe00fa80003d24000 0xe39fe80003ff4000

def z630 : W := mkw 0x0001282088000000 0x002b6171c0000000

def z631 : W := mkw 0x02217e25fc058218 0x92007e01fc07801c

def z632 : W := mkw 0x4412804a009800a0 0x0000800e00180000

def z633 : W := mkw 0x272ffffffc6b56f7 0xffffffffffffffff

def z634 : W := mkw 0x00200225bc000000 0x10000001fc000000

def z635 : W := mkw 0xcc3ed7df37b80de0 0x6dff97fe33f80fe0

def z636 : W := mkw 0x03000030c8210652 0xffe00971cc004e73

def z637 : W := mkw 0xc00e800003900000 0x0004800001180000

def z638 : W := mkw 0xe30fa830cbf34652 0xffffe971cfff4e73

def z639 : W := mkw 0x0000020414001005 0xf3849e003d18f01f

def z640 : W := mkw 0x880c018003000900 0x0008010002000e00

def z641 : W := mkw 0xab0000104367cf5a 0xe050000003e7cfff

def z642 : W := mkw 0x23017821e847c21a 0x92007801fc07c01f

def z643 : W := mkw 0x23012830c8634652 0xe97308700ee74e73

def z644 : W := mkw 0xc00e81c803900000 0x6dbf81fe03f80000

def z645 : W := mkw 0x8a00000043058b18 0xb6c86101c3078f9c

def z646 : W := mkw 0x0200500160058218 0xb6c87101f2078e1c

def z647 : W := mkw 0x0200000040010210 0xa040000002070e10

def z648 : W := mkw 0x23012830c8634652 0xb6fb6171c2e70e10

def z649 : W := mkw 0x2001280000424000 0xffdb68000ee74073

def z650 : W := mkw 0x23000030c8634652 0xfc700171cee74e73

def z651 : W := mkw 0x0200500160058218 0xb6c47081f107819c

def z652 : W := mkw 0x04012a269c0810a5 0xffeffffffd18f1ff

def z653 : W := mkw 0xfa0c518163d7eb18 0xf6dc7181f3ffff9c

def z654 : W := mkw 0x24012a06144a50a5 0xffdffe8e3ffff1ff

def z655 : W := mkw 0x30012c0000426000 0x00000e0000007000

def z656 : W := mkw 0xcc1e83de17b81de5 0x6dff97fe33f8bfec

def z657 : W := mkw 0x880c518123048908 0xa28c70803307818c

def z658 : W := mkw 0xdc1ed5ca039ca9a0 0x0004968e0118b180

def z659 : W := mkw 0x4012805800b00440 0x0033007000e00000

def z660 : W := mkw 0xfc1fffde17fefde5 0xfffffffe3fffffff

def z661 : W := mkw 0x23012a34dc635657 0xfffb7f71fee7fe7f

def z662 : W := mkw 0x800c000003000000 0x208c000003000000

def z663 : W := mkw 0x880c518003048900 0xa6cc718003078f80

def z664 : W := mkw 0x002fafec9c000000 0x0daf8ffe0c000000

def z665 : W := mkw 0xce1ed3df77bd9ffd 0xffffffffffffffff

def z666 : W := mkw 0x880c518123048908 0x24cc118033008f8c

def z667 : W := mkw 0x0000020414001005 0xb6c41e803d00f19f

def z668 : W := mkw 0x8c1c01da03280de0 0x2cec01fe03000fe0

def z669 : W := mkw 0x000ffc0000000000 0x000b600000000000

def z670 : W := mkw 0x00017c0000000000 0x02007e0000000000

def z671 : W := mkw 0x0000000000000000 0xb6c0000000000010

def z672 : W := mkw 0x000ffe0414000000 0x1f8ffe8e3c000000

def z673 : W := mkw 0xfa0ffd8163d7eb18 0x001b6101c2e70e00

def z674 : W := mkw 0xcc1fa9fa8bb80de0 0x7fffe9ffcff80fe0

def z675 : W := mkw 0xcc1e81da03b80de0 0x6054808e03f80fe0

def z676 : W := mkw 0x8a0c018043010b10 0xb6cc6181c3070f90

def z677 : W := mkw 0x000c500000000000 0x028c700000000000

def z678 : W := mkw 0xcc1001da03b80de0 0x6c7001fe03f80fe0

def z679 : W := mkw 0x0000020414001005 0x000016003000b00c

def z680 : W := mkw 0x8e000206570d9bbd 0xffc49e8e3f1fffff

def z681 : W := mkw 0x23012830c8634652 0x923b6971cee74e13

def z682 : W := mkw 0x8a0c018163010b18 0x34cc0181f3000f9c

def z683 : W := mkw 0x0000000000000000 0x0dab017000000000

def z684 : W := mkw 0x0000000000000000 0x000410803100818c

def z685 : W := mkw 0x0001282088000000 0x12006801cc000000

def z686 : W := mkw 0xc80e818003900900 0x65df818003f80f80

def z687 : W := mkw 0xf20ffc0163d7e218 0xf39ffe01f3fff01c

def z688 : W := mkw 0x0000020414000000 0x09008e0e0c000000

def z689 : W := mkw 0x0b0001b1e8210f5a 0x1c6001f1fc000fff

def z690 : W := mkw 0x04000206140810a5 0x6dc4968e3118b1ec

def z691 : W := mkw 0x23012830c8634652 0xe07b6171c2e74e73

def z692 : W := mkw 0x2101283088624442 0x0033007000e00000

def z693 : W := mkw 0x00217c21a8000000 0x00006001c0000000

def z694 : W := mkw 0x5002840000902000 0x0000860000183000

def z695 : W := mkw 0xf30ffc1043f7e652 0xe3dffe0003fffe73

def z696 : W := mkw 0x00217e25bc000000 0x1f84fe8ffc000000

def z697 : W := mkw 0xfc1ffdda03feede0 0x6dffe1fe03ff0fe0

def z698 : W := mkw 0x800ffc0003048000 0xa38ffe0003078000

def z699 : W := mkw 0x0000000000000000 0xe380080000004000

def z700 : W := mkw 0x0200000040010210 0x92006001c0070010

def z701 : W := mkw 0x27012a36dc6b56f7 0xfffb69fffee74fff

def z702 : W := mkw 0x0000000000000000 0x619b000002e00000

def z703 : W := mkw 0x04000206140810a5 0xbec4108e3d0081ff

def z704 : W := mkw 0x23012820c8434212 0x9fab6971cc074013

def z705 : W := mkw 0x8a00000043058b18 0xb6c4108033078f9c

def z706 : W := mkw 0x04000206140810a5 0xeb849e0e0d18f063

def z707 : W := mkw 0xc41e805a03b804e0 0x6dff817e03f80e60

def z708 : W := mkw 0x04000206140810a5 0xffef9ffe3d18f1ff

def z709 : W := mkw 0x8a0c518163058b18 0xf7cc7981f307cf9c

def z710 : W := mkw 0xcc1e81db23b80de8 0x6dff81fe33f80fec

def z711 : W := mkw 0xf80ffc0003d6e908 0xe39ffe0003fff18c

def z712 : W := mkw 0x8a23ae6cdf058b18 0xa9638e7e0f078f9c

def z713 : W := mkw 0xd02fffedbf94a000 0x7fbffffffff8b000

def z714 : W := mkw 0x0023ae6c9c000000 0x1d238f7fcc000000

def z715 : W := mkw 0x0a00500160058b18 0x92407001f0078f9c

def z716 : W := mkw 0xcc1e81da03b80de0 0x7dff81fe0ff80ff3

def z717 : W := mkw 0x23012830c8634652 0xfc7b6171cee74e73

def z718 : W := mkw 0x8a0c518163058b18 0xb6cc7f81f307ff9c

def z719 : W := mkw 0xf40ffe0617def0a5 0x1c5b608e3ee701ff

def z720 : W := mkw 0xcc1ed1db23bc8de8 0x7ffff1fff3f88fec

def z721 : W := mkw 0xcc1e81da03b80de0 0x0dff81fe02e00fe0

def z722 : W := mkw 0x000fabec9c000000 0x1faffffffc000000

def z723 : W := mkw 0xcc1ed1da03bc8de0 0xfffff1fe33ff8ffc

def z724 : W := mkw 0xcc1e81da03b80de0 0x6c7b01fe03f80fe0

def z725 : W := mkw 0xf02ffc21abd6e000 0xe39ffe01c3fff000

def z726 : W := mkw 0x0a0c518160058b18 0x96cc7181f0078f9c

def z727 : W := mkw 0x0023ae6c9c000000 0x092bef7fcc000000

def z728 : W := mkw 0x002003edbc000000 0x1c6001fffc00019c

def z729 : W := mkw 0x9a0c55816305ab18 0xb6cc7781f307bf9c

def z730 : W := mkw 0x23017a25fc47d21f 0x92007e01fc07f01f

def z731 : W := mkw 0xf02ffde9abd6e000 0xffbfff71cffff000

def z732 : W := mkw 0xcc1e81da03b80de0 0x003b817e02f80e00

def z733 : W := mkw 0x002003edbc000000 0x002001fff0000000

def z734 : W := mkw 0xf81ffdc803d6e900 0xe39ffe0003fff000

def z735 : W := mkw 0x8a0c518163058b18 0xffccff81ff1fffff

def z736 : W := mkw 0x702fffedbcd26000 0x1fbffffffce00000

def z737 : W := mkw 0xcc1ed1da03bc8de0 0x6dff91fe03f88fe0

def z738 : W := mkw 0xc00e81d803b00440 0x6dff81fe03f80e60

def z739 : W := mkw 0xcc1e81da03b80de0 0xefffe1fe03ff0fe0

def z740 : W := mkw 0x002fffedbc000000 0x5faffffffc187000

def z741 : W := mkw 0xcc1e81da03b81de5 0x6dff81fe03f80fff

def z742 : W := mkw 0x232ed7dd74634652 0xe054968e32e74e73

def z743 : W := mkw 0xc81e83dc17b01d45 0x923b1f703ee0fe1f

def z744 : W := mkw 0xda0ed5816395ab18 0xf7dff781f3ffbf9c

def z745 : W := mkw 0xf02fffedbfd6e000 0xfffffffffffff19c

def z746 : W := mkw 0xc02e83edbf900000 0x7dbf81fffff80000

def z747 : W := mkw 0xf02fffedbfd6e000 0x9faffffffd1ff000

def z748 : W := mkw 0x002fffedbc000000 0x7feffffffc000060

def z749 : W := mkw 0x882fffedbf048908 0x3fefffffff008f8c

def z750 : W := mkw 0xf000540003d6e000 0xe010160003fff000

def z751 : W := mkw 0xf70ffc1243fff6f7 0xe3dffe0003ffffff

def z752 : W := mkw 0xf02003edbfd6e000 0xfc3001fffffff000

def z753 : W := mkw 0x002fffedbc000000 0x5faffffffc004063

def z754 : W := mkw 0x3c117dda006eede0 0x8e607ffe0007ffe0

def z755 : W := mkw 0xf00ffdc803d6e000 0xe3bfff7003fff000

def z756 : W := mkw 0x23012830c8634652 0x083b6171cee70e63

def z757 : W := mkw 0x33217e25fc47e212 0x92007e01fc07f013

def z758 : W := mkw 0xcc1e81da03b80de0 0x6dff8ffe03f87fe0

def z759 : W := mkw 0x8a0c518163058b18 0xf7ccf181f31f8f9c

def z760 : W := mkw 0x04000206140810a5 0x5d449e8e3d18f1ff

def z761 : W := mkw 0xf0017c0003d6e000 0xe39b7e0003fff000

def z762 : W := mkw 0x002fffedbc000000 0x1d279ffffc000000

def z763 : W := mkw 0x882fffedbf048908 0xbfafffffff07818c

def z764 : W := mkw 0x000e81c920000000 0x1daf81fff0000000

def z765 : W := mkw 0xf000000003d6e000 0xe1108e0003fff000

def z766 : W := mkw 0x00012a249c000000 0x1fab69fffc000000

def z767 : W := mkw 0x8c0c019203280de0 0x6dff81fe03f80fe0

def z768 : W := mkw 0x202fffedbc424000 0x1fbffffffee70000

def z769 : W := mkw 0x002fffedbc000000 0x1b2bff7ffc000000

def z770 : W := mkw 0x0200001040210650 0xfffb6971cee74e73

def z771 : W := mkw 0x8a0c518163058b18 0x168c7181f3078f8c

def z772 : W := mkw 0x04000206140810a5 0xe9449e8e3d18f1ff

def z773 : W := mkw 0x8a0c518163058b18 0xb6ccf781f31fbf9c

def z774 : W := mkw 0x8a00500163058b18 0xb6c47081f3078f9c

def z775 : W := mkw 0x00212bedbc000000 0x1faffffffc000000

def z776 : W := mkw 0xa02fffedbf46c000 0xffbfffffffe7c000

def z777 : W := mkw 0x002fffedbc000000 0x092ffffffc000000

def z778 : W := mkw 0x082003edbc000908 0x1c2001fffc00018c

def z779 : W := mkw 0xf00ffdc923d6e000 0xffbffffff3fff000

def z780 : W := mkw 0xf80ffd8123d6e908 0xf7dffe8033fff19c

def z781 : W := mkw 0x040e81da002804e0 0x6dff81fe03f80fe0

def z782 : W := mkw 0xf00ffc0003d6e000 0xe7dffe8003fff180

def z783 : W := mkw 0xcc1e81da03b80de0 0x0dbf81fe03f80f80

def z784 : W := mkw 0xcc317e37bfb80de0 0x72507e01fff80fe0

def z785 : W := mkw 0x002ffde9a8000000 0x0fafffffc0000000

def z786 : W := mkw 0x27012a36dc6b56f7 0x003ff7fff3ffbf8c

def z787 : W := mkw 0xf80ffd8123d6e908 0xe39ffe0003fff000

def z788 : W := mkw 0xf00ffc0003d6e000 0xe214fe0003fff000

def z789 : W := mkw 0x002003edbc000000 0x0820017fcc000000

def z790 : W := mkw 0xf00ffc0003d6e000 0xe11bee0003fff000

def z791 : W := mkw 0xcc1ed1db23bc8de0 0xfffff1fff3ff8fe0

def z792 : W := mkw 0xff10001243ffeff2 0xe050000003fffff3

def z793 : W := mkw 0x002fffedbc000000 0x1e2b7ffffc000000

def z794 : W := mkw 0xcc1e81da03b80de0 0xedff81fe03f88ffc

def z795 : W := mkw 0xf00ffc0003d6e000 0xe1179e0003fff000

def z796 : W := mkw 0x0000001000200440 0x6dff81fe02e00e60

def z797 : W := mkw 0x002ed7edbc000000 0x1c2001fffc000000

def z798 : W := mkw 0x002ffde9a8000000 0x1faff1fff0000000

def z799 : W := mkw 0x000001d800200440 0x6dfb01fe02e00e60

def z800 : W := mkw 0xcc1e81da03b80de0 0xffff81fe03f80ff0

def z801 : W := mkw 0x23012830c8634652 0xdb3b6971cee74e73

def z802 : W := mkw 0x002003edbc000000 0x1dab01fffc000000

def z803 : W := mkw 0x04000206140810a5 0x9e449e8e3d18f1ff

def z804 : W := mkw 0x0023fe6dbc000000 0x1fabff7ffc000000

def z805 : W := mkw 0x0020026dbc000000 0x1820007ffc000000

def z806 : W := mkw 0x002003edbc000000 0x1ea861fffc000000

def z807 : W := mkw 0x8a0c518163058b18 0xbfcc7981ff078f9c

def z808 : W := mkw 0x23212e24dc434212 0x92006e01cc074013

def z809 : W := mkw 0x002ffe6c9c000000 0x1fafff7fcc000000

def z810 : W := mkw 0x042ffdeba80810a5 0xe06b6171c118f1ff

def z811 : W := mkw 0x2300021454634652 0xffd49e8e3ee74e73

def z812 : W := mkw 0x002003edbc000000 0xffa49ffffd18f000

def z813 : W := mkw 0xf000000003d6e000 0xe2101e0003fff000

def z814 : W := mkw 0xf0012c0003d6e000 0xe0100e0003fff000

def z815 : W := mkw 0x0c1001da00280de0 0x0c7b01fe02e00fe0

def z816 : W := mkw 0x802c53edbf048000 0xbeac71ffff078000

def z817 : W := mkw 0x8e0c5387770d9bbd 0x4908ef0fce1f7e63

def z818 : W := mkw 0xf00ffc208bd6e000 0xebbffe700ffff000

def z819 : W := mkw 0xf00ffc0123d6e000 0xf39ffe01f3fff000

def z820 : W := mkw 0x000ed1c920000000 0x0dafe1ffc0000000

def z821 : W := mkw 0x502fffedbc902000 0x1faffffffc183000

def z822 : W := mkw 0xdc1e81da03bcade0 0x6dff81fe03f8bfe0

def z823 : W := mkw 0x002fffedbc000000 0x3feffffffd000180

def z824 : W := mkw 0xf02ffde9abd6e000 0xefbfffffc3fff000

def z825 : W := mkw 0x820c500043058210 0xb6cc7181f3078f9c

def z826 : W := mkw 0x8a0c518163058b18 0xbfef71f1f3078f9c

def z827 : W := mkw 0xcc1e81da03b80de0 0x61bf81fe03f80f80

def z828 : W := mkw 0xc80e81c803900900 0x6dff81fe03f80f80

def z829 : W := mkw 0xcc1e81da03b80de0 0xffff9ffe33f8fffc

def z830 : W := mkw 0x882fffedbf000900 0x1faffffffe000e00

def z831 : W := mkw 0x0003a86888000000 0x1fabe97fcc000000

def z832 : W := mkw 0xf82fffedbfd6e900 0xffffffffffffff80

def z833 : W := mkw 0x7a03ad8160d36b18 0x55538f81f0f87f9c

def z834 : W := mkw 0xf02ffe6c9fd6e000 0xffbfff7fcffff000

def z835 : W := mkw 0xd82fffedbf94a908 0x1faffffffd18b18c

def z836 : W := mkw 0x23012830c8634652 0xfffb7971fee7ce7f

def z837 : W := mkw 0x0000021414201445 0xfffb1f703ee0fe7f

def z838 : W := mkw 0xa90d79b1ab66cd4a 0x493718f03de0c1ef

def z839 : W := mkw 0x302fffedbc46e000 0xffaffffffd1ff000

def z840 : W := mkw 0x002fffedbc001005 0xffeffffffc00f07f

def z841 : W := mkw 0xf00ffc208bd6e000 0xe3bfff71c3fff000

def z842 : W := mkw 0x8c1c01da03280de0 0x6dff01fe03e00fe0

def z843 : W := mkw 0xc81e81d803b00d40 0x6dff81fe02e00e60

def z844 : W := mkw 0xcc1e81da03b80de0 0x4d7b81fe02f80fe0

def z845 : W := mkw 0xf02fffedbfd6e000 0xebbfff7fcffff000

def z846 : W := mkw 0x002fffedbc000000 0x002be77fc0000000

def z847 : W := mkw 0x6710001240fb46f2 0xe050000002ff4e73

def z848 : W := mkw 0x23012830c8634652 0xbefb6171cee70e73

def z849 : W := mkw 0x082fffedbc000900 0x1feffffffc000f80

def z850 : W := mkw 0xce10001243b90ff8 0x6050000003f80ffc

def z851 : W := mkw 0x23012830c8634652 0xfffb7f71cee7fe73

def z852 : W := mkw 0x002ed7edbc000000 0x002497fff0000000

def z853 : W := mkw 0xcc1e805a03b80de0 0x69ff807e03f80fe0

def z854 : W := mkw 0x002fffedbc000000 0x1e24fffffc000000

def z855 : W := mkw 0xf00ffde88bd6e000 0xffbfffffcffff000

def z856 : W := mkw 0x002fffedbc048000 0x9faffffffc078000

def z857 : W := mkw 0x8a0c518163058b18 0x96447181f1078f9c

def z858 : W := mkw 0x20012a249c424000 0xffbffffffffff000

def z859 : W := mkw 0x23217e25fc434212 0x12007e01fc070000

def z860 : W := mkw 0x27000012406b56f7 0xe050000002ff7e73

def z861 : W := mkw 0xcc12805a03b80de0 0x6df780fe03f80fe0

def z862 : W := mkw 0xf00ffc0003d6e000 0xe3dffe0003fff19c

def z863 : W := mkw 0x23012830c8634652 0xebbb6971cee74e63

def z864 : W := mkw 0x0e10001240290ff8 0x0040000000000ffc

def z865 : W := mkw 0x002fffedbc000000 0xbfaffffffe070000

def z866 : W := mkw 0xcc1e81da03b81de5 0x6dff81fe03f87fe3

def z867 : W := mkw 0x002003edbc000000 0x1da481fffc000000

def z868 : W := mkw 0xcc1e81db23b80de0 0x7dff81fff3f80fe0

def z869 : W := mkw 0x002fffedbc000000 0x7fbffffffee00000

def z870 : W := mkw 0x32217e25fc47e218 0x92007e01fc07f01c

def z871 : W := mkw 0x002fffedbc001005 0x1faffffffc00b00c

def z872 : W := mkw 0xef1fa9eacbdb4bb2 0x9204e88fcd1f4193

def z873 : W := mkw 0x000ff9e9a8000000 0x1faff9fffc000000

def z874 : W := mkw 0xf00ffc0003d6e000 0xe39ffe8033fff18c

def z875 : W := mkw 0x03000030c8210652 0xfffb6171cee70e73

def z876 : W := mkw 0xdc1ed5da03bcade0 0x6dff81fe03f80fe0

def z877 : W := mkw 0x4412805a00b804e0 0x493b817e02f80e60

def z878 : W := mkw 0x23212a25fc434212 0x92006801fc074013

def z879 : W := mkw 0x4412805a00b804e0 0x6973807e02f80e60

def z880 : W := mkw 0xcc1e81da03b80de0 0x493f81fe03f80fe0

def z881 : W := mkw 0x33017e24dc47f217 0x92007e01fc07f01f

def z882 : W := mkw 0x07000012402916f7 0xe04000000118ffff

def z883 : W := mkw 0x7003ac0000d6e000 0xc1138e0000fff000

def z884 : W := mkw 0xc81e81d803b00d40 0x6dbf81fe03f80e00

def z885 : W := mkw 0x8a0c518163058b18 0xbfccf18ff3078f9c

def z886 : W := mkw 0xf00ffc0003d6e000 0xe39bee0002ff7000

def z887 : W := mkw 0x002ed7cd34000000 0x1faff7fff0000000

def z888 : W := mkw 0x802fffedbf048000 0x1faffffffd008000

def z889 : W := mkw 0x27000012406b46f2 0xe050000003ff4ff3

def z890 : W := mkw 0x002fafedbc000000 0x1daf8ffffc000000

def z891 : W := mkw 0x0a0c518160010b18 0xb6cc7181f2070f9c

def z892 : W := mkw 0x8a0c518163058b18 0xa28c7181f3078f8c

def z893 : W := mkw 0x0023ae6dbc000000 0x19238e7ffc000000

def z894 : W := mkw 0x30217fedbc46e000 0x9e207ffffc07f000

def z895 : W := mkw 0xf00ffc0003d6e000 0x619fee0003ff7000

def z896 : W := mkw 0xf00ffc208bd6e000 0xf39ffe01cffff000

def z897 : W := mkw 0x002fabedbc000000 0x1fafe9fffc000000

def z898 : W := mkw 0x8a0c500163058b18 0xb2cc7001f3078f9c

def z899 : W := mkw 0x23012a24dc435217 0x92006e01cc077013

def z900 : W := mkw 0x4c1281da00b80de0 0x6df781fe01f80fe0

def z901 : W := mkw 0x000001c920000000 0x1c2001fff0000000

def z902 : W := mkw 0x302fffedbc46e000 0x1faffffffc070000

def z903 : W := mkw 0x002fffedbc001005 0xbfeffffffd00f19f

def z904 : W := mkw 0x000c51c920000000 0x1eac71fff0000000

def z905 : W := mkw 0xcc1e81da03b80de0 0x697b817e03f80fe0

def z906 : W := mkw 0xcc1e81da03b81de5 0xefff9ffe03f8ffff

def z907 : W := mkw 0x002003edbc000000 0x1fa009fffc000000

def z908 : W := mkw 0x4c12805a00b80de0 0x4973807e00f80fe0

def z909 : W := mkw 0x8a0c518163058b18 0xb6cc7981ff07cf9f

def z910 : W := mkw 0x0023ffedbc000000 0x1f23fffffc000000

def z911 : W := mkw 0xcc1e81da03b80de0 0xefff91fe03f88fe0

def z912 : W := mkw 0x2101283088624442 0xfff718f03de0c1ff

def z913 : W := mkw 0xca0ed1c963958b18 0xfffff1fff3ff8f9c

def z914 : W := mkw 0xce10001243b90ff0 0xe050000003ff0ff0

def z915 : W := mkw 0x23012830c8634652 0x7dfb6171cee70e73

def z916 : W := mkw 0xca0ed18163958b18 0xb6df7181f3e78f9c

def z917 : W := mkw 0xf00ffc0003d6e000 0xf7dffe0003fff010

def z918 : W := mkw 0x212fffedbc424002 0x1faffffffc004003

def z919 : W := mkw 0x0f0003b7fc291fff 0x1c6001fffc000fff

def z920 : W := mkw 0xcc1e81da03b80de0 0x083b017e02e00e60

def z921 : W := mkw 0xc81e81d803b00d40 0x0c3b01fe02e00e00

def z922 : W := mkw 0x002c53edbc000000 0x1c2411fffc000000

def z923 : W := mkw 0xf02fffedbfd6e000 0x493bef7fceff7000

def z924 : W := mkw 0x0a00018160010b18 0xb6cc7181f3078f9c

def z925 : W := mkw 0x0a00018160010b18 0x96406181f0070f9c

def z926 : W := mkw 0xf00ffc0003d6e000 0xf79ffe8033fff000

def z927 : W := mkw 0x8a0ed1c963058b18 0xb6ccf18ff3078f9c

def z928 : W := mkw 0x002fffedbc000000 0x1fabef7fcc000000

def z929 : W := mkw 0x7003ac0000d26000 0xe1138e0002ff7000

def z930 : W := mkw 0xd30ed430cbb5a652 0x1c649771cd18be73

def z931 : W := mkw 0x882c03edbf000900 0x3cec01ffff000f80

def z932 : W := mkw 0x23012830c8634652 0x5d7b6971cee74e73

def z933 : W := mkw 0x002d7bedbc000000 0x1faf79fffc000000

def z934 : W := mkw 0x00212bedbc000000 0x1d2309fffc000000

def z935 : W := mkw 0x8a0ed58163058b18 0xb6ccf781f3078f9c

def z936 : W := mkw 0x002fffedbc000000 0x0dafefffcc000000

def z937 : W := mkw 0x002ed7edbc000000 0x1fa49ffffc000000

def z938 : W := mkw 0x0023fe6dbc000000 0x0923ee7fcc000000

def z939 : W := mkw 0x0a00518160058b18 0xb6c47181f1078f9c

def z940 : W := mkw 0xf02ffde9abd6e000 0x6dbfe1ffc3ff0000

def z941 : W := mkw 0xf02fffedbfd6e000 0x7fbfffffffff0000

def z942 : W := mkw 0xcc1ed1db23b80de0 0x6dffe1ffc3f80fe0

def z943 : W := mkw 0x8a0c518163058b18 0xffcc7181f3078ffc

def z944 : W := mkw 0xf02fffedbfd6e000 0x1fbfffffffffb000

def z945 : W := mkw 0xf00ffc0123d6e008 0xe39ffe0033fff00c

def z946 : W := mkw 0xf80ffd8123d6e900 0xf7dfff81f3ffff80

def z947 : W := mkw 0xc81e81d803b00d40 0x003f81fe02e00e00

def z948 : W := mkw 0x0002805800200440 0x6dfb817e02e00e60

def z949 : W := mkw 0x002fffedbc000000 0x1dafe1fffc000000

def z950 : W := mkw 0xdc1ed5db23bcade8 0x6dff97fe33f8bfec

def z951 : W := mkw 0x8a0ed1c963058b18 0xb6ef71f1f3078f9c

def z952 : W := mkw 0x23012830c8634652 0x9e7b6971cee74e73

def z953 : W := mkw 0x002fffedbc000000 0xffeffffffd18f19c

def z954 : W := mkw 0x020c518160010210 0xb6cc7181f3078f9c

def z955 : W := mkw 0x002fffedbc048008 0x1faffffffc00800c

def z956 : W := mkw 0xf00ed40003d6e000 0x0014960003ffb000

def z957 : W := mkw 0x002fffedbc000000 0x1feffffffc00019c

def z958 : W := mkw 0x002fffedbc000000 0x082b617fcc000000

def z959 : W := mkw 0x700ffc0000d6e000 0xc39ffe0000fff000

def z960 : W := mkw 0x8a0c518163058b18 0xf6cc7181f31fff9c

def z961 : W := mkw 0x000ed3cd34000000 0x1faffffffc000000

def z962 : W := mkw 0x002c53edbc000000 0x1c2861fffc000000

def z963 : W := mkw 0xcc1e81da03b80de0 0x6dfb01fe02e00fe0

def z964 : W := mkw 0xf00ffc0003d6e000 0x039ffe0003ffb000

def z965 : W := mkw 0x27012822c84b42b2 0xffc4e88fcd1f41f3

def z966 : W := mkw 0xf02fffedbfd6e000 0x1c3b61fffee70000

def z967 : W := mkw 0x00212a6c9c000000 0x1fab697fcc000000

def z968 : W := mkw 0xe00fa80003d24000 0xe39ffe0003fff000

def z969 : W := mkw 0xf00ffc0003d6e000 0xe21b7e0003fff000

def z970 : W := mkw 0xc40e801203b804e0 0x6dff81fe03f80fe0

def z971 : W := mkw 0x002ffe6dbc000000 0x1baffe7ffc000000

def z972 : W := mkw 0xdc1ed5da03bcade0 0xeffff7fe03ffbfe0

def z973 : W := mkw 0x23012830c8634652 0xfffbef71ceff7e73

def z974 : W := mkw 0x7023fe6dbcd6e000 0xdb33fe7ffcfff000

def z975 : W := mkw 0x33012c30c8636652 0xfffb6f71cee77e73

def z976 : W := mkw 0x8a0c518163058b18 0x96487181f2078f9c

def z977 : W := mkw 0x882fffedbf000900 0x1faffffffd000180

def z978 : W := mkw 0xf00ed40003d6e000 0xe29cf60003fff000

def z979 : W := mkw 0x06000206540912b5 0xffc8ef0fce1f7e73

def z980 : W := mkw 0x8a0c018163010b18 0xb6cc6181f3070f9c

def z981 : W := mkw 0x23012830c8634652 0xfffb6971cffffe73

def z982 : W := mkw 0x702fffedbcd6e000 0xdfbffffffcfff000

def z983 : W := mkw 0x0023ae6c9c000000 0x1faffffffc000000

def z984 : W := mkw 0x23012830c8634652 0x6dfb6971cee74e63

def z985 : W := mkw 0xf02fffedbfd6e000 0xbfbfffffffe78000

def z986 : W := mkw 0xf00ffc0003d6e000 0xef9ffe8e03fff000

def z987 : W := mkw 0xf02ffc688bd6e000 0xe3bffe7003fff000

def z988 : W := mkw 0xcc1e81da03b80de0 0xedff81fe03f8ffe0

def z989 : W := mkw 0xcc1ed1da03b80de0 0x6ffff1fe03f80fe0

def z990 : W := mkw 0x000e81c800000000 0x1fafe1ffc0000000

def z991 : W := mkw 0xf00ed40003d6e000 0xe19f960003fff000

def z992 : W := mkw 0xc83fffedbf900900 0x1faffffffc000000

def z993 : W := mkw 0x0f1003fedc291ff7 0x1c6001fffc000fff

def z994 : W := mkw 0x002c03edbc000000 0x1cac01fffc000000

def z995 : W := mkw 0xcc1ed1db23b80de0 0xfffff1fff3f88ffc

def z996 : W := mkw 0xf02fffedbfd6e000 0x5fbffffffeff7000

def z997 : W := mkw 0xd00ed4000394a000 0xe39ff60003ffb000

def z998 : W := mkw 0x700ffc0000d26000 0xe39ffe0002ff7000

def z999 : W := mkw 0xf00ffc0003d6e000 0x619ff60003ffb000

def z1000 : W := mkw 0x20212bedbc424000 0xffbb69fffee74000

def z1001 : W := mkw 0xf00fac0003d26000 0xe39fee0003ff7000

def z1002 : W := mkw 0xf00ffc0003d6e000 0xf39ffe0033fff01c

def z1003 : W := mkw 0x000ffde888000000 0x1fafffffcc000000

def z1004 : W := mkw 0xc81e81d803b00d40 0x2dff81fe03e00f80

def z1005 : W := mkw 0x23012830c8634652 0xffff69f1cfe74ff3

def z1006 : W := mkw 0x7003fc0000d6e000 0x4113ee0000ff7000

def z1007 : W := mkw 0xcc1e81da03b81de5 0xffff91fe33f8ffff

def z1008 : W := mkw 0x002003edbc000000 0x1d208ffffc000000

def z1009 : W := mkw 0xf80ffd8123d6e908 0xf79fff81f3fff18c

def z1010 : W := mkw 0x002e83edbc000000 0x1c2b01fffc000000

def z1011 : W := mkw 0x082003edbc000900 0x1c6001fffc000f80

def z1012 : W := mkw 0x00212fedbc000000 0x1c200ffffc000000

def z1013 : W := mkw 0x002d7fedbc000000 0x1eac7ffffc000000

def z1014 : W := mkw 0x00217e6dbc000000 0x1a207e7ffc000000

def z1015 : W := mkw 0x002fffedbc000000 0x16aff7fff0000000

def z1016 : W := mkw 0xf00ffc0003d6e000 0xf39ffe000ffff013

def z1017 : W := mkw 0xf02fffedbfd6e000 0xfffffffffffff073

def z1018 : W := mkw 0xe00fa9e88bd24000 0xffbfe9ffcfff4000

def z1019 : W := mkw 0x25012a369c6a54e7 0x4933087e0ce04063

def z1020 : W := mkw 0x23012830c8634652 0xe97b6971cee74e73

def z1021 : W := mkw 0xf00ffd8123d6e000 0xe39ffe8033fff000

def z1022 : W := mkw 0x8a0c518163058b18 0x920c7181f3078f9c

def z1023 : W := mkw 0x4c1281da00b80de0 0x6dfb81fe02f80fe0

def z1024 : W := mkw 0x00212bedbc000000 0x1e2069fffc000000

def z1025 : W := mkw 0xcc1e81da03b80de0 0x6dff89fe0ff84fe3

def z1026 : W := mkw 0xcc1ed1db23b80de0 0x6dff91fe33f80fe0

def z1027 : W := mkw 0x0020026c9c000000 0x1c20017fcc000000

def z1028 : W := mkw 0x8a0c518163058b18 0xb2447081f3078f9c

def z1029 : W := mkw 0xa00d78000346c000 0xe39ffe0003fff000

def z1030 : W := mkw 0xef1fa81243fb4ff2 0xe3dfe80003ff4ff3

def z1031 : W := mkw 0xcc1e81da03b80de0 0x7dff81fe33f80ffc

def z1032 : W := mkw 0xaf000012436fdfff 0xe050000003ffffff

def z1033 : W := mkw 0x23012830c8634652 0xfffffff1ffffffff

def z1034 : W := mkw 0xcc1ed1da03bc8de0 0xeffffffe03ffffe0

def z1035 : W := mkw 0x402fffedbc900000 0x5fbffffffcf80000

def z1036 : W := mkw 0xd02fffedbf94a000 0x1faffffffc000000

def z1037 : W := mkw 0x04000012002804e0 0x6dfb01fe02e00fe0

def z1038 : W := mkw 0x802fffedbf000000 0x3fafffffff000000

def z1039 : W := mkw 0x002003edbc000000 0x1c6001fffc000073

def z1040 : W := mkw 0x23217e25fc435217 0x92007e01fc07f01f

def z1041 : W := mkw 0x8a0ed18163058b18 0xb7cff181f3078f9c

def z1042 : W := mkw 0x000002249c000000 0x1c2001fffc000000

def z1043 : W := mkw 0xcc1c519323b80de0 0x76dc7181f3f80fe0

def z1044 : W := mkw 0x7003ac0000d26000 0x411bee0002ff7000

def z1045 : W := mkw 0x002fffedbc000000 0xffeffffffd00c1ff

def z1046 : W := mkw 0xf00fac0003d6e000 0xe19f8e0003fff000

def z1047 : W := mkw 0x23012830c8634652 0x1ffb6971cee70e73

def z1048 : W := mkw 0x002003edbc000000 0x1c2497fffc000000

def z1049 : W := mkw 0x002003edbc000000 0x1ea411fffc000000

def z1050 : W := mkw 0x0c1e81da00280de0 0x6dff81fe02e00fe0

def z1051 : W := mkw 0x8a0c518163058b18 0xf7df7181f3e78f9c

def z1052 : W := mkw 0x8a0c518163058b18 0x16cc7181f2070f9c

def z1053 : W := mkw 0xcc1e81da03b80de0 0x7fff91fe33f80fe0

def z1054 : W := mkw 0xcc1e81da03b80de0 0x7fffe1ffc3f80fe0

def z1055 : W := mkw 0x8a0c51c963058b18 0xbeec71fff3078f9c

def z1056 : W := mkw 0x072003fffc2916f7 0x1c6001fffc000fff

def z1057 : W := mkw 0xf00ffc0003d6e000 0xc31bfe0002fff000

def z1058 : W := mkw 0x04000206140810a5 0xffcc9f8e3f18ffff

def z1059 : W := mkw 0x002003edbc000000 0xffe009fffc004073

def z1060 : W := mkw 0x0c1001da00280de0 0x4d7301fe00e00fe0

def z1061 : W := mkw 0x8a00000043058b18 0xb6cc7181f3078f9c

def z1062 : W := mkw 0xf00ffc0003d6e000 0xefbfff7003fff000

def z1063 : W := mkw 0xcc1e81da03b80de0 0x003b01fe02e00f80

def z1064 : W := mkw 0x04000206140810a5 0xf2449e8e3d18f1ff

def z1065 : W := mkw 0xcc1ed1db23bc8de8 0x6dff81fe03f80fe0

def z1066 : W := mkw 0xf00ffc0003d6e000 0x411ffe0003fff000

def z1067 : W := mkw 0x2f100012406b4ff2 0xe050000002e74ff3

def z1068 : W := mkw 0xcc12805a03b80de0 0x6dfb817e03f80fe0

def z1069 : W := mkw 0x002fffedbc000000 0x1b27fefffc000000

def z1070 : W := mkw 0x00217fedbc000000 0x1c2061fffc000000

def z1071 : W := mkw 0xcc1ed1db23bc8de8 0xeffff1fe33ff8fec

def z1072 : W := mkw 0x70017c0000d6e000 0xc2107e0000fff000

def z1073 : W := mkw 0xf80ffd8123d6e908 0xe7dfff8033ffff8c

def z1074 : W := mkw 0x002fffedbc000000 0x1faffffffd00818c

def z1075 : W := mkw 0x8a0c518163058b18 0xb6c86181f2070f9c

def z1076 : W := mkw 0xf00ffc0003d6e000 0x439ffe0002ff7000

def z1077 : W := mkw 0xfe1ffc1243ffeff8 0xe3dffe0003fffffc

def z1078 : W := mkw 0xef10001243ffcffa 0xe050000003ffcfff

def z1079 : W := mkw 0x002e83edbc000000 0x1c2481fffc000000

def z1080 : W := mkw 0xcc1e81da03b80de0 0xffff99fe3ff8cfff

def z1081 : W := mkw 0x002fffedbc000000 0xbfeffffffc000010

def z1082 : W := mkw 0x202fffedbc424000 0xfffffffffee74073

def z1083 : W := mkw 0x002003edbc001005 0x1c2001fffc00001f

def z1084 : W := mkw 0x00012a249c000000 0x1fabef7fcc000000

def z1085 : W := mkw 0xf003fc0003d6e000 0xe313fe0003fff000

def z1086 : W := mkw 0x002fffedbc000000 0x9faffffffc004013

def z1087 : W := mkw 0x03000030c8210652 0xffe49f71cd18fe73

def z1088 : W := mkw 0x002ffde9a8000000 0x002fe1ffc0000000

def z1089 : W := mkw 0x002e81e9a8000000 0x0daf81ffc0000000

def z1090 : W := mkw 0x002fffedbc000000 0x0bafff7fcc000000

def z1091 : W := mkw 0x0023afedbc000000 0x09238f7fcc000000

def z1092 : W := mkw 0x000002249c000000 0x1fa49ffffc000000

def z1093 : W := mkw 0xcc1e81da03b80de0 0xefff89fe03f84fe0

def z1094 : W := mkw 0x002c53edbc000000 0x1facfffffc000000

def z1095 : W := mkw 0xcc1e81da03b80de0 0x24ff81fe03f80f80

def z1096 : W := mkw 0xff1ffc1243ffeff2 0xe3dffe0003fffff3

def z1097 : W := mkw 0x302fffedbc426000 0x1faffffffc007000

def z1098 : W := mkw 0xf700001243fff6f7 0xe050000003ffffff

def z1099 : W := mkw 0xf00ffda1abd6e000 0xffbffff1fffff000

def z1100 : W := mkw 0x0023fe6dbc000000 0x1fa7fefffc000000

def z1101 : W := mkw 0xcc10001203b80de0 0x6dff81fe03f80fe0

def z1102 : W := mkw 0xf02fffedbfd6e000 0x003ff7fff3ffb000

def z1103 : W := mkw 0xf02fffedbfd6e000 0xffbffffffee74000

def z1104 : W := mkw 0x4612d05b60bd86f8 0xdb33f07ff0ff807c

def z1105 : W := mkw 0x8a0c518163058b18 0x24cc7181f3078f8c

def z1106 : W := mkw 0x0023afedbc000000 0x1fabeffffc000000

def z1107 : W := mkw 0x04000206140810a5 0xffccff8ffd18f1ff

def z1108 : W := mkw 0xcc1e81da03b80de0 0x607f81fe03f80fe0

def z1109 : W := mkw 0x4412805a00b804e0 0x6dff81fe03f80fe0

def z1110 : W := mkw 0x0410005a002804e0 0x6dfb017e02e00e60

def z1111 : W := mkw 0xf02fffedbfd6e000 0x9fbffffffee7f000

def z1112 : W := mkw 0xf00ffe249fd6e000 0xffbffffffffff000

def z1113 : W := mkw 0x002fafec9c000000 0x1fafefffcc000000

def z1114 : W := mkw 0x702fffedbcd26000 0xffbffffffeff7000

def z1115 : W := mkw 0x8a00500163058b18 0xb6c87101f3078f9c

def z1116 : W := mkw 0x4c1281da00b80de0 0x0c7301fe00e00fe0

def z1117 : W := mkw 0x0023ae6c9c000000 0x1b23ee7fcc000000

def z1118 : W := mkw 0x000ffdc920000000 0x1faffffff0000000

def z1119 : W := mkw 0x202fffedbc424000 0xffbffffffffff000

def z1120 : W := mkw 0xf00ffc0003d6e000 0xff9ffe000ffff000

def z1121 : W := mkw 0x002fffedbc000000 0xbfaffffffd008000

def z1122 : W := mkw 0x8a0c518163058b18 0xf6cc7181f307cfff

def z1123 : W := mkw 0x0200000040010210 0xb6c86181f2070f9c

def z1124 : W := mkw 0x07000216542916f7 0x1c40008e3c000fff

def z1125 : W := mkw 0x8a0c518163058b18 0xbecc7181ff078fff

def z1126 : W := mkw 0xef10001243fb5ff7 0xe050000003ffffff

def z1127 : W := mkw 0xcc1ed1db23bc8de8 0xffff91fe33f88ffc

def z1128 : W := mkw 0xf10ffc208bd6e002 0xe39ffe000ffff003

def z1129 : W := mkw 0x002fffedbc000000 0x1c2ff7fffc000000

def z1130 : W := mkw 0x000d7ba5bc000000 0x1faffffffc000000

def z1131 : W := mkw 0x2000000000424000 0xe3949e0003fff000

def z1132 : W := mkw 0x002001e9a8000000 0x0c2001ffc0000000

def z1133 : W := mkw 0x04012822880810a5 0xffeb6971cd18f1ff

def z1134 : W := mkw 0x23012a24dc435217 0x92006801fc07401f

def z1135 : W := mkw 0x04000206140810a5 0xdb049e8e3d18f1ff

def z1136 : W := mkw 0xcc1e81da03b80de0 0x6dff91fe33f88fec

def z1137 : W := mkw 0xf00ffc0003d6e000 0xe3dffe0003fff073

def z1138 : W := mkw 0xf80ffd8003d6e900 0xf7dfff8033ffff9c

def z1139 : W := mkw 0xf00ffc4803d6e000 0xebbffe7e03fff000

def z1140 : W := mkw 0xcc1e81da03b80de0 0x6dff97fe03f8bfe0

def z1141 : W := mkw 0xf00ffc0003d6e000 0xf79fff01c3fff000

def z1142 : W := mkw 0x00217fedbc000000 0x1fab7ffffc000000

def z1143 : W := mkw 0x04000206140810a5 0xffdf9e8e3ff8f1ff

def z1144 : W := mkw 0x102fffedbc04a000 0x1faffffffc00b000

def z1145 : W := mkw 0xf00ffc0003d6e000 0xefdffe0003fff060

def z1146 : W := mkw 0x2001280000424000 0xe39bee0002ff7000

def z1147 : W := mkw 0x002e83edbc000000 0x1faf9ffffc000000

def z1148 : W := mkw 0xf00ffd8123d6e000 0xf7dfff81f3fff19c

def z1149 : W := mkw 0xf00ed40003d6e000 0xe3949e0003fff000

def z1150 : W := mkw 0xcc1e81da03b80de0 0x0c7f81fe03f80fe0

def z1151 : W := mkw 0xf02ffe6dbfd6e000 0xfbbffe7ffffff000

def z1152 : W := mkw 0x7503ae369cfa74e7 0x49338e7e0cf87063

def z1153 : W := mkw 0x882fffedbf048908 0xbfeffffffd00819c

def z1154 : W := mkw 0xf00c500003d6e000 0xe39cfe0003fff000

def z1155 : W := mkw 0xce10001243bd9ffd 0xe050000003ffffff

def z1156 : W := mkw 0x002ffde9a8000000 0x1fafe9ffcc000000

def z1157 : W := mkw 0x000129e888000000 0x1fab69ffcc000000

def z1158 : W := mkw 0x7003ac0000d26000 0xe39ffe0003fff000

def z1159 : W := mkw 0xd02fffedbf94a000 0xbfafffffff1fb000

def z1160 : W := mkw 0x27000012406b56f7 0xe050000002e74fff

def z1161 : W := mkw 0xcc1e81da03b80de0 0xffff9ffe0ff8fff3

def z1162 : W := mkw 0xcc1e81da03b80de0 0xedff81fe03f84ff3

def z1163 : W := mkw 0x002fffedbc000000 0x1d2beffffc000000

def z1164 : W := mkw 0xcc1e81da03bc8de8 0x6dff81fe03f88fec

def z1165 : W := mkw 0x002fffedbc000000 0x002b61fff0000000

def z1166 : W := mkw 0x0a00518160058b18 0xb6c87181f2078f9c

def z1167 : W := mkw 0x8a0c518163058b18 0xb7ccff81f3078f9c

def z1168 : W := mkw 0x07000012402916f7 0x0040000000000fff

def z1169 : W := mkw 0xf00e800003d6e000 0xe39f9e0003fff000

def z1170 : W := mkw 0xda0ed5816395ab18 0xb6cc7181f3078f9c

def z1171 : W := mkw 0x23012830c8634652 0xffff79f1fee74e73

def z1172 : W := mkw 0x0c1001da00280de0 0x6dff81fe03f80fe0

def z1173 : W := mkw 0x882fffedbf048908 0x1faffffffc000000

def z1174 : W := mkw 0x002fffedbc000000 0x3feffffffe000e00

def z1175 : W := mkw 0xe02fffedbfd24000 0xffbfffffffff4000

def z1176 : W := mkw 0xcc1ed5da03b80de0 0x6dff97fe03f80fe0

def z1177 : W := mkw 0x23012830c8634652 0xffff7971cfe7ce73

def z1178 : W := mkw 0x002ed7edbc000000 0x1daf97fffc000000

def z1179 : W := mkw 0xf00d7c0003d6e000 0xe29c7e0003fff000

def z1180 : W := mkw 0xf02fffedbfd6e000 0x5fbffffffdf8f000

def z1181 : W := mkw 0x8a0e81c843058b18 0xadef81fe03078f9c

def z1182 : W := mkw 0xf00ffc0003d6e000 0xe7dfff0003fffe00

def z1183 : W := mkw 0x002283edbc000000 0x1d2381fffc000000

def z1184 : W := mkw 0xc02fffedbf948000 0xffbfffffffff8000

def z1185 : W := mkw 0xcc3ed5db23b80de0 0x6dff81fe03f80fe0

def z1186 : W := mkw 0x00217fedbc000000 0x1fa4fffffc000000

def z1187 : W := mkw 0x0023afedbc000000 0x1c2301fffc000000

def z1188 : W := mkw 0x002fffedbc000000 0x1eaf71fffc000000

def z1189 : W := mkw 0x882c53edbf048908 0x1c2411fffd00818c

def z1190 : W := mkw 0x002fffedbc000000 0x0daff7fff0000000

def z1191 : W := mkw 0xd02fffedbf94a000 0xffaffffffd18f000

def z1192 : W := mkw 0x002fffedbc000000 0x7faffffffd180000

def z1193 : W := mkw 0x202fffedbc424000 0x5fbffffffce04000

def z1194 : W := mkw 0x7003fc0000d6e000 0xe397fe0001fff000

def z1195 : W := mkw 0xf00ffc208bd6e000 0xffffff71cffff073

def z1196 : W := mkw 0xcc1e81da03b81de5 0x6dff81fe03f8bfec

def z1197 : W := mkw 0xcf10001243b90ff2 0x6050000003f80ff3

def z1198 : W := mkw 0xb02fffedbf46e000 0xbfafffffff07f000

def z1199 : W := mkw 0xf80ffd8003d6e900 0xe39fff0003fffe00

def z1200 : W := mkw 0x0f10001240290ff2 0x0040000000000ff3

def z1201 : W := mkw 0x24012a06144a50a5 0xffdb688e3ee741ff

def z1202 : W := mkw 0xf0017c0003d6e000 0xe394fe0003fff000

def z1203 : W := mkw 0x302fffedbc46f005 0x9faffffffc07f01f

def z1204 : W := mkw 0xda0c51816395ab18 0xb6cc7181f31fbf9c

def z1205 : W := mkw 0x002fffedbc000000 0x122ffffffc000000

def z1206 : W := mkw 0xcc1e81da03bc8de0 0xedff81fe03ff8fe0

def z1207 : W := mkw 0x002fffedbc000000 0xffaffffffc004000

def z1208 : W := mkw 0x202fffedbc424000 0x9faffffffc074000

def z1209 : W := mkw 0x8a0c518163058b18 0x144c7181f3078f9c

def z1210 : W := mkw 0xcc12805a03b80de0 0x4933807e02f80e60

def z1211 : W := mkw 0xf00ffd8123d6e000 0xe39fff01c3fff000

def z1212 : W := mkw 0xf02fffedbfd6f005 0xffbffffffffff01f

def z1213 : W := mkw 0xf00ffc0003d6e000 0x821ffe0003fff000

def z1214 : W := mkw 0x200ffc0000424000 0xe39ffe0003fff000

def z1215 : W := mkw 0xf002840003d6e000 0xe010860003fff000

def z1216 : W := mkw 0x880e81d803200d40 0x6dff81fe03e00fe0

def z1217 : W := mkw 0x8a00518163058b18 0xb6407181f3078f9c

def z1218 : W := mkw 0x8a00018163058b18 0xb6c86181f3078f9c

def z1219 : W := mkw 0xc82fffedbf900900 0x7ffffffffff80f80

def z1220 : W := mkw 0x6513aa7e9cfa54e7 0x49338e7e0cf87063

def z1221 : W := mkw 0xda0ed5816395ab18 0xf7ccff81f31fff9c

def z1222 : W := mkw 0xf00ffc0003d6e000 0xffdffe803ffff1ff

def z1223 : W := mkw 0xef10001243fb4ff2 0x6050000003ff0fe0

def z1224 : W := mkw 0x002fffedbc000000 0xffeffffffd18f073

def z1225 : W := mkw 0xcc1e81da03b81de5 0xffff89fe0ff8ffff

def z1226 : W := mkw 0xc02fffedbf900000 0xffbffffffff8f000

def z1227 : W := mkw 0x8e100012432d8ff8 0xa040000003078ffc

def z1228 : W := mkw 0xcc1001da03b80de0 0x6dfb01fe03f80fe0

def z1229 : W := mkw 0xc00ed00003948000 0xe39ffe0003fff000

def z1230 : W := mkw 0xf003ac0003d6e000 0xe3979e0003fff000

def z1231 : W := mkw 0x002fffedbc000000 0x1feffffffc000073

def z1232 : W := mkw 0x000ffe249c000000 0x1faffffffc000000

def z1233 : W := mkw 0xf00ffc0003d6e000 0xa29ff60003ffb000

def z1234 : W := mkw 0xf000000003d6e000 0xe014960003fff000

def z1235 : W := mkw 0x002fffedbc000000 0x1fab69fffc000000

def z1236 : W := mkw 0x000e81d800200440 0x0dbf81fe02e00e00

def z1237 : W := mkw 0x8a0c518163058b18 0xb4486181f3078f9c

def z1238 : W := mkw 0x002fffedbc001005 0x1faffffffc007003

def z1239 : W := mkw 0x23012830c8634652 0xf27b6971cee74e73

def z1240 : W := mkw 0x441e81da00b804e0 0x6dff81fe02f80e60

def z1241 : W := mkw 0xf82fffedbfd6e908 0xffbffffffffff18c

def z1242 : W := mkw 0xca0ed18163958b18 0xf7dfff81f3ffff9c

def z1243 : W := mkw 0x082fffedbc000908 0x1faffffffc00018c

def z1244 : W := mkw 0x302fffedbc46e000 0xffbffffffee7f000

def z1245 : W := mkw 0xcc1ed3cf379c99ad 0x0004968e3118b18c

def z1246 : W := mkw 0xf001280003d6e000 0xe39ffe0003fff000

def z1247 : W := mkw 0xcc1e81da03b80de0 0x4dbf81fe02f80e60

def z1248 : W := mkw 0xf80ffdc803d6e900 0xeffffffe03ffff80

def z1249 : W := mkw 0xcc1e81da03b80de0 0x2cff01fe03e00fe0

def z1250 : W := mkw 0xf00ffc0003d6e000 0xc317fe0001fff000

def z1251 : W := mkw 0xdc1e85da03b82de0 0x6dff87fe03f83fe0

def z1252 : W := mkw 0x882fffedbf048900 0xbfefffffff078f80

def z1253 : W := mkw 0x002003edbc000000 0x1e201ffffc000000

def z1254 : W := mkw 0x23012830c8634652 0xffffff71cee74e73

def z1255 : W := mkw 0x002ffde9a8000000 0x092be17fc0000000

def z1256 : W := mkw 0xca0ed18163958b18 0xb6ccf181f31f8f9c

def z1257 : W := mkw 0xf00ffc0003d6e000 0xe01ff60003fff000

def z1258 : W := mkw 0x2523ae7e9c6a54e7 0x49338e7e0cf87063

def z1259 : W := mkw 0xf02ffde9abd6e000 0xf7bffff1f3fff000

def z1260 : W := mkw 0x002fffedbc000000 0x1faffffffd18b000

def z1261 : W := mkw 0x802fffedbf048000 0xffafffffff1ff000

def z1262 : W := mkw 0x4c1e81da00b80de0 0x4dff81fe00f80fe0

def z1263 : W := mkw 0xca0c518163958b18 0xf6dc7181f3ff8f9c

def z1264 : W := mkw 0xcc1e81da03b80de0 0x6dfb817e02f80e60

def z1265 : W := mkw 0x7023afedbcd26000 0x5d338ffffcf87000

def z1266 : W := mkw 0x00212bedbc000000 0x1c2b61fffc000000

def z1267 : W := mkw 0x23012830c8634652 0xfffb69f1fee74fff

def z1268 : W := mkw 0x07000236dc2916f7 0x1c60017fcc000e73

def z1269 : W := mkw 0x8a0c018043010b10 0xb6cc7181f3078f9c

def z1270 : W := mkw 0xce10001243bd8ff8 0x6050000003ff0fe0

def z1271 : W := mkw 0x002287edbc000000 0x1c2087fffc000000

def z1272 : W := mkw 0x002ed7edbc000000 0x1eacf7fffc000000

def z1273 : W := mkw 0x0e1003df74291ffd 0x1c6001fffc000fff

def z1274 : W := mkw 0x002ed3edbc000000 0x1faff1fffc000000

def z1275 : W := mkw 0x002fffedbc001005 0xffaffffffd18f01f

def z1276 : W := mkw 0xcc1e81da03b80de0 0x7fff89fe0ff80fe0

def z1277 : W := mkw 0x002ffde9a8000000 0x0c2b61ffc0000000

def z1278 : W := mkw 0xc81e81d803b00d40 0x093b817e02e00e00

def z1279 : W := mkw 0x0a00018160010b18 0x14486181f2070f9c

def z1280 : W := mkw 0x002fffedbc001005 0x1faffffffc00001f

def z1281 : W := mkw 0x23012830c8634652 0xffffe9ffcee74e73

def z1282 : W := mkw 0x23012830c8634652 0xfffb6971cfe7cfff

def z1283 : W := mkw 0xf02fffedbfd6e000 0xe3bffffff3fff000

def z1284 : W := mkw 0x00217e25bc000000 0x1faffffffc000000

def z1285 : W := mkw 0x30017c000046e000 0xe39ffe0003fff000

def z1286 : W := mkw 0x23217e25fc47c21a 0x92007e01fc07c01f

def z1287 : W := mkw 0xf80ffc0003d6e900 0xe3dffe0003ffff80

def z1288 : W := mkw 0x002fffedbc000000 0x9faffffffc00f000

def z1289 : W := mkw 0x802fffedbf048000 0xbfefffffff07819c

def z1290 : W := mkw 0xf02ffdc923d6e000 0xe39ffe0003fff000

def z1291 : W := mkw 0xc00ed1c923948000 0xffbff1fff3ff8000

def z1292 : W := mkw 0x0a00518160058b18 0x14406181f0070f9c

def z1293 : W := mkw 0x4c1281da00b80de0 0x4933817e00f80e60

def z1294 : W := mkw 0x000e81e888000000 0x1daf81ffcc000000

def z1295 : W := mkw 0x23012a24dc434212 0x92007e01fc074013

def z1296 : W := mkw 0x7023ae6c9cd26000 0xffbbef7fceff7000

def z1297 : W := mkw 0x7003ac0000d26000 0xc313ee0000ff7000

def z1298 : W := mkw 0x002fffedbc000000 0x03affffff0000000

def z1299 : W := mkw 0xce1ed01243bd8ff8 0xe3dff00003ff8ffc

def z1300 : W := mkw 0x0200500160058218 0xb6cc7181f3078f9c

def z1301 : W := mkw 0x27012812406b56f7 0xe3dffe0003ffffff

def z1302 : W := mkw 0xdc1ed5da03bcade0 0xefff9ffe03f8ffe0

def z1303 : W := mkw 0x000fa9e888000000 0x0dafe1ffc0000000

def z1304 : W := mkw 0x04000012002804e0 0x6dfb817e02f80e60

def z1305 : W := mkw 0xcc1e81da03b80de0 0x69bf817e03f80e60

def z1306 : W := mkw 0xcc1ed1da03bc8de0 0x6dffe1fe03ff0fe0

def z1307 : W := mkw 0x0001282088000000 0x1fafe9ffcc000000

def z1308 : W := mkw 0xcc1e81da03b80de0 0x6fff9ffe03f80fe0

def z1309 : W := mkw 0xca1ed1c963958b18 0xb6cc7181f3078f9c

def z1310 : W := mkw 0x002057edbc000000 0x1c2017fffc000000

def z1311 : W := mkw 0x8a0c518163058b18 0x00086181f2070f8c

def z1312 : W := mkw 0x002003edbc000000 0xbee411fffd00819c

def z1313 : W := mkw 0x23012830c8634652 0xffffe971cfff4e73

def z1314 : W := mkw 0x8a0c518163058b18 0x34cc6181f3070f9c

def z1315 : W := mkw 0xf02fffedbfd26000 0x7fbffffffff87000

def z1316 : W := mkw 0xf003ac0003d6e000 0x41138e0002ff7000

def z1317 : W := mkw 0x23012830c8634652 0x5fbb6971cee74e63

def z1318 : W := mkw 0xfe10001243ffeff8 0xe050000003fffffc

def z1319 : W := mkw 0x002053edbc000000 0x1e2071fffc000000

def z1320 : W := mkw 0xcc1e81da03b80de0 0x697780fe03f80fe0

def z1321 : W := mkw 0xf003ac0003d6e000 0xe39bee0003fff000

def z1322 : W := mkw 0xcc1281da03b80de0 0x6d7381fe03f80fe0

def z1323 : W := mkw 0x702fffedbcd26000 0xffbffffffdf8f000

def z1324 : W := mkw 0xf00ffc0003d6e000 0x001be60002ff3000

def z1325 : W := mkw 0xf00ffc0003d6e000 0xeb9ffe000ffff063

def z1326 : W := mkw 0xf00ffdc803d6e000 0xe39ffe8e03fff000

def z1327 : W := mkw 0x802fffedbf048000 0x1faffffffe070000

def z1328 : W := mkw 0x7003fc0000d6e000 0xe39bfe0002fff000

def z1329 : W := mkw 0x002fffedbc000000 0x9faffffffc00801c

def z1330 : W := mkw 0xc02fffedbf900000 0x1faffffffd180000

def z1331 : W := mkw 0xc02fffedbf900000 0x1fbffffffee00000

def z1332 : W := mkw 0x0023afedbc000000 0x1fa79ffffc000000

def z1333 : W := mkw 0xf00ffd8003d6e000 0xe79fff8003fff000

def z1334 : W := mkw 0x04000206140810a5 0xffccfe8e3f1ff1ff

def z1335 : W := mkw 0x8a0c518163058b18 0xa04c7181f3078f9c

def z1336 : W := mkw 0x000001e888000000 0x1c2001ffcc000000

def z1337 : W := mkw 0x002003edbc001005 0x9e201ffffc00f01f

def z1338 : W := mkw 0x882fffedbf000900 0xbfefffffff008f9c

def z1339 : W := mkw 0xcc1e81da03b80de0 0x4d7781fe01f80fe0

def z1340 : W := mkw 0x8a2ed5c963058b18 0xb6cc7181f3078f9c

def z1341 : W := mkw 0x8a0c518163058b18 0xb2487101f3078f9c

def z1342 : W := mkw 0xd02ed7edbf94a000 0x1c2497fffd18b000

def z1343 : W := mkw 0xf80ffd8003d6e900 0xe39ffe8003fff180

def z1344 : W := mkw 0x4412805a00b804e0 0x4d73817e00f80e60

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z10,z11]),(0,[z0,z1,z12,z13,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z14])],[(0,[z0,z1,z2,z4,z15,z5,z6]),(0,[z0,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z17,z2,z18,z4,z6])],[(0,[z0,z1,z2,z4,z19,z5,z6]),(0,[z20,z1,z2,z4,z5,z6,z8]),(0,[z7,z21,z1,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z23,z5,z6]),(1,[z0,z1,z2,z24,z5,z6]),(0,[z0,z25,z1,z2,z4,z5,z6]),(0,[z0,z26,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z27,z8]),(0,[z0,z1,z28,z2,z4,z5,z6]),(1,[z29,z0,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z31,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z32]),(0,[z1,z33,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z34,z6])],[(0,[z0,z1,z35,z2,z4,z5,z6]),(0,[z36,z0,z1,z2,z4,z5,z6]),(0,[z37,z1,z2,z38,z4,z5,z6]),(0,[z1,z39,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z40,z6])],[(0,[z21,z1,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z42,z43,z6]),(0,[z44,z0,z1,z2,z4,z5,z8]),(0,[z7,z7,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z45,z6])],[(0,[z0,z1,z2,z46,z4,z5,z6])]],
   [[(1,[z0,z47,z1,z2,z5,z6]),(0,[z0,z1,z2,z48,z4,z5,z6]),(0,[z0,z49,z1,z2,z4,z5,z6]),(0,[z0,z1,z50,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z51]),(0,[z0,z1,z52,z2,z4,z5,z6])],[(0,[z53,z0,z1,z54,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z55])],[(0,[z56,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z57,z5,z6])],[(0,[z58,z0,z1,z2,z4,z5,z6]),(0,[z59,z1,z2,z4,z5,z6,z8]),(0,[z60,z0,z1,z2,z4,z5,z6]),(0,[z37,z1,z2,z4,z5,z42,z6]),(0,[z29,z61,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z62,z63,z4,z5]),(0,[z0,z1,z64,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z65]),(0,[z53,z0,z1,z66,z4,z5,z6]),(0,[z0,z1,z2,z67,z68,z4,z5]),(1,[z0,z1,z2,z69,z5,z6])],[(0,[z70,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z5,z6]),(0,[z72,z0,z1,z2,z4,z5,z6]),(0,[z22,z0,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z74,z5,z6]),(0,[z0,z1,z2,z75,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z76])],[(0,[z0,z1,z2,z4,z77,z5,z6]),(0,[z0,z1,z2,z4,z78,z5,z6]),(0,[z0,z79,z1,z80,z4,z5,z6]),(1,[z0,z1,z2,z67,z4,z5]),(0,[z0,z1,z2,z4,z5,z81,z6])],[(0,[z0,z82,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z9,z6]),(0,[z22,z0,z1,z2,z4,z5,z83]),(0,[z0,z1,z84,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z85])]],
   [[(0,[z0,z1,z2,z4,z5,z86,z6]),(0,[z87,z7,z1,z2,z4,z5,z6]),(0,[z29,z0,z1,z2,z88,z5,z6]),(0,[z89,z0,z1,z2,z4,z5,z6]),(0,[z22,z0,z2,z4,z90,z5,z6]),(0,[z0,z91,z1,z2,z68,z5,z6]),(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z0,z1,z2,z4,z93,z5,z6])],[(0,[z0,z1,z2,z4,z94,z5,z6]),(0,[z0,z1,z2,z95,z4,z5,z6]),(0,[z96,z0,z1,z2,z4,z5,z6])],[(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z1,z17,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z6,z97]),(0,[z0,z1,z17,z2,z4,z98,z6]),(0,[z0,z1,z2,z4,z5,z6,z99])],[(0,[z0,z80,z2,z30,z4,z5,z6]),(0,[z0,z100,z1,z2,z4,z5,z6]),(0,[z53,z101,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z102])],[(0,[z59,z0,z1,z2,z4,z5,z103]),(0,[z0,z1,z2,z4,z104,z5,z6]),(0,[z0,z1,z2,z4,z105,z5,z6])],[(0,[z22,z0,z1,z2,z4,z5,z6])],[(0,[z0,z106,z1,z2,z4,z5,z6]),(0,[z79,z1,z2,z4,z5,z6,z8]),(0,[z107,z0,z1,z2,z4,z5,z6]),(0,[z108,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z109,z2,z4,z5,z6]),(0,[z110,z0,z1,z2,z4,z5,z6]),(0,[z111,z0,z1,z2,z4,z112,z6]),(0,[z53,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z40,z6])]],
   [[(1,[z113,z0,z1,z2,z4,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z115,z1,z2,z4,z5,z6,z8]),(0,[z0,z116,z1,z2,z4,z5,z6]),(0,[z1,z2,z63,z117,z4,z5,z6]),(0,[z118,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z119,z4,z5,z6]),(0,[z113,z0,z1,z2,z4,z5,z6]),(0,[z0,z73,z1,z2,z23,z5,z6]),(0,[z1,z2,z4,z5,z120,z121,z6])],[(0,[z1,z2,z4,z98,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z122,z6])],[(0,[z1,z84,z2,z4,z5,z6,z8]),(0,[z1,z2,z4,z5,z6,z8,z123]),(0,[z124,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z125,z2,z4,z5,z6])],[(0,[z1,z2,z4,z41,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z126,z6]),(0,[z0,z1,z2,z4,z5,z83,z6]),(0,[z0,z1,z2,z4,z5,z127,z6]),(0,[z0,z128,z1,z2,z62,z4,z5])],[(0,[z0,z1,z2,z4,z129,z5,z6]),(0,[z130,z0,z1,z2,z4,z5,z6])],[(0,[z7,z1,z84,z2,z4,z5,z6]),(1,[z0,z1,z131,z2,z4,z5]),(0,[z0,z1,z2,z68,z23,z5,z6]),(0,[z0,z1,z132,z2,z4,z5,z6])],[(0,[z0,z1,z133,z2,z4,z5,z6]),(0,[z7,z1,z2,z134,z4,z5,z6]),(0,[z7,z1,z2,z63,z4,z5,z6]),(0,[z0,z2,z23,z4,z90,z5,z6]),(0,[z0,z1,z2,z135,z4,z5,z6]),(0,[z136,z0,z1,z2,z137,z4,z6])]],
   [[(0,[z138,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z139,z6]),(0,[z0,z140,z1,z2,z4,z5,z6]),(0,[z37,z0,z1,z2,z4,z9,z6]),(0,[z0,z141,z1,z2,z4,z5,z6]),(0,[z142,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z143,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z144,z5,z6]),(1,[z0,z1,z2,z63,z5,z11])],[(0,[z145,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z146,z5,z6]),(0,[z0,z1,z147,z2,z4,z5,z6])],[(0,[z0,z148,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z8,z11]),(0,[z0,z149,z1,z2,z30,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z150]),(0,[z0,z1,z13,z2,z57,z5,z6])],[(0,[z151,z0,z1,z2,z4,z5,z152]),(0,[z1,z2,z23,z4,z5,z6,z8]),(1,[z0,z1,z2,z153,z4,z6]),(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z80,z4,z5,z6])],[(0,[z155,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z156]),(0,[z0,z1,z157,z2,z5,z158,z6]),(0,[z0,z159,z1,z2,z4,z5,z6])],[(0,[z53,z0,z1,z2,z4,z5,z160]),(0,[z111,z0,z1,z2,z4,z5,z6]),(0,[z0,z161,z1,z2,z4,z5,z6]),(1,[z162,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z163,z164,z4,z6]),(0,[z0,z165,z1,z2,z4,z5,z6]),(0,[z166,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z43,z6,z8]),(1,[z1,z2,z4,z5,z8,z11]),(0,[z22,z7,z1,z2,z4,z5,z6]),(1,[z167,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z63,z4,z168,z6])]],
   [[(0,[z0,z1,z2,z4,z169,z5,z6]),(0,[z1,z2,z30,z4,z5,z6,z8]),(0,[z1,z2,z4,z5,z6,z6,z8]),(0,[z170,z0,z1,z2,z4,z5,z6]),(0,[z171,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z172,z6]),(0,[z0,z1,z2,z137,z4,z6,z102])],[(0,[z0,z1,z2,z173,z4,z5,z6]),(0,[z53,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z174,z5,z6]),(0,[z175,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z176,z5,z6]),(0,[z0,z1,z177,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z4,z5,z6]),(0,[z0,z179,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z180,z6]),(0,[z0,z1,z84,z2,z4,z43,z6]),(0,[z0,z1,z2,z181,z4,z5,z6])],[(0,[z0,z1,z182,z2,z4,z5,z6]),(0,[z7,z91,z1,z2,z4,z5,z6])],[(0,[z37,z0,z1,z84,z2,z4,z6]),(0,[z183,z1,z2,z4,z5,z121,z6])],[(0,[z0,z1,z2,z184,z68,z4,z6]),(0,[z0,z185,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z152]),(0,[z151,z0,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z186,z4,z5,z6]),(0,[z0,z187,z1,z2,z4,z5,z6]),(1,[z0,z1,z13,z68,z5,z6]),(0,[z188,z1,z2,z18,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z189]),(0,[z0,z1,z2,z4,z5,z190,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z191,z6]),(0,[z0,z1,z2,z4,z5,z6,z192]),(0,[z0,z1,z2,z4,z5,z193,z6]),(0,[z29,z194,z1,z2,z4,z5,z6]),(0,[z29,z0,z1,z2,z195,z5,z6]),(0,[z0,z1,z2,z4,z196,z5,z6]),(0,[z0,z197,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z198,z5,z6]),(0,[z0,z91,z1,z4,z57,z5,z6]),(0,[z0,z1,z199,z2,z4,z5,z6]),(0,[z0,z1,z2,z200,z4,z5,z6])],[(0,[z37,z0,z1,z2,z4,z201,z6]),(0,[z0,z1,z2,z202,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z203,z6]),(0,[z0,z1,z157,z2,z4,z5,z6])],[(0,[z0,z1,z204,z2,z4,z5,z6]),(0,[z37,z1,z205,z2,z4,z5,z6]),(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z9,z6,z8]),(0,[z0,z79,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z30,z4,z5,z6]),(0,[z1,z2,z4,z5,z158,z207,z6]),(0,[z0,z1,z2,z208,z4,z5,z6]),(0,[z0,z1,z17,z2,z18,z4,z5])],[(0,[z0,z1,z209,z2,z4,z5,z6]),(0,[z0,z1,z2,z210,z4,z5,z6]),(1,[z179,z1,z2,z4,z5,z8]),(0,[z1,z2,z211,z4,z5,z6,z8]),(0,[z0,z1,z13,z2,z68,z5,z6]),(0,[z0,z1,z212,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z213,z6]),(0,[z0,z128,z1,z4,z5,z158,z6])],[(0,[z0,z1,z2,z4,z214,z5,z6]),(0,[z1,z2,z137,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z6,z215]),(0,[z0,z1,z17,z2,z4,z5,z102])],[(0,[z0,z1,z2,z38,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z216,z6]),(0,[z217,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z218,z4,z5,z6]),(0,[z0,z1,z2,z23,z5,z6,z11]),(1,[z219,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z220,z6]),(1,[z0,z1,z2,z184,z4,z6]),(0,[z0,z1,z2,z4,z5,z121,z6])],[(0,[z37,z221,z1,z2,z4,z5,z6]),(0,[z0,z1,z222,z2,z4,z5,z6]),(0,[z0,z1,z223,z2,z4,z5,z6]),(0,[z1,z12,z2,z4,z5,z6,z8]),(0,[z7,z1,z2,z224,z4,z5,z6]),(0,[z0,z225,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z226,z5,z6]),(0,[z227,z1,z2,z4,z5,z43,z6])],[(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z111,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z153,z4,z5,z6]),(0,[z0,z1,z2,z4,z112,z6,z102]),(0,[z0,z1,z2,z4,z229,z5,z6]),(0,[z0,z1,z2,z4,z230,z5,z6])]],
   [[(0,[z1,z231,z2,z4,z201,z5,z6]),(0,[z0,z179,z1,z2,z4,z5,z160]),(0,[z0,z232,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z233,z5,z6]),(0,[z7,z79,z1,z2,z4,z5,z6]),(0,[z7,z179,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z234,z4,z5,z6]),(1,[z235,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z236,z4,z5,z6])],[(0,[z37,z1,z231,z2,z4,z5,z6]),(0,[z0,z1,z2,z237,z4,z5,z6]),(0,[z0,z1,z238,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z5,z6]),(0,[z240,z1,z2,z4,z5,z6,z8]),(0,[z0,z241,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z242]),(0,[z0,z1,z2,z243,z4,z5,z6]),(0,[z1,z2,z68,z244,z4,z5,z6]),(1,[z0,z1,z33,z4,z5,z245]),(1,[z0,z1,z246,z2,z4,z6]),(1,[z0,z1,z247,z2,z5,z6])],[(0,[z0,z1,z248,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z42,z6]),(0,[z0,z1,z249,z2,z4,z5,z6]),(1,[z250,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z121,z6]),(0,[z0,z1,z2,z4,z5,z6,z245]),(0,[z251,z0,z1,z2,z4,z5,z6])],[(0,[z151,z0,z1,z2,z4,z216,z6]),(0,[z0,z1,z2,z252,z4,z5,z6]),(0,[z253,z0,z1,z2,z4,z5,z6]),(0,[z0,z254,z1,z2,z4,z5,z6])],[(0,[z255,z0,z1,z2,z4,z5,z6]),(0,[z151,z0,z1,z2,z4,z5,z189]),(0,[z151,z1,z2,z4,z201,z5,z6]),(0,[z0,z1,z2,z256,z4,z5,z6]),(0,[z0,z2,z4,z112,z5,z9,z6]),(0,[z0,z257,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z258,z4,z5,z6]),(1,[z1,z2,z259,z4,z5,z6])],[(0,[z260,z0,z1,z2,z4,z5,z6])],[(0,[z0,z261,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z193,z6]),(0,[z0,z1,z2,z137,z4,z9,z6]),(0,[z53,z0,z1,z2,z4,z5,z262]),(0,[z0,z1,z13,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z263]),(0,[z235,z1,z33,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z264,z6]),(0,[z1,z2,z68,z4,z5,z6,z8])],[(0,[z0,z1,z2,z4,z5,z6,z265]),(0,[z151,z0,z1,z2,z4,z266,z6]),(0,[z0,z1,z2,z4,z267,z5,z6]),(1,[z0,z268,z1,z2,z137,z6])],[(1,[z0,z1,z2,z4,z191,z6]),(0,[z0,z1,z2,z4,z195,z5,z6]),(0,[z0,z1,z269,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z8,z102]),(0,[z22,z0,z1,z2,z4,z270,z6]),(0,[z0,z1,z2,z4,z9,z43,z6]),(0,[z0,z1,z2,z271,z4,z5,z6])],[(0,[z1,z231,z2,z4,z5,z6,z8]),(0,[z110,z0,z1,z2,z38,z5,z6]),(0,[z7,z1,z2,z38,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z121,z6]),(0,[z0,z1,z17,z2,z4,z9,z6])],[(0,[z0,z1,z2,z4,z272,z5,z6]),(0,[z7,z1,z33,z2,z4,z5,z6]),(0,[z273,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z274,z4,z5,z6])],[(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z276]),(0,[z0,z1,z2,z4,z277,z5,z6]),(0,[z0,z73,z2,z23,z4,z5,z6]),(0,[z0,z1,z13,z68,z4,z5,z6]),(0,[z0,z1,z278,z2,z4,z5,z6]),(0,[z0,z1,z4,z279,z5,z121,z6]),(0,[z0,z1,z2,z5,z158,z280,z6]),(0,[z0,z268,z1,z2,z137,z4,z6])],[(1,[z0,z1,z2,z4,z216,z6]),(0,[z281,z0,z1,z2,z4,z5,z6]),(0,[z217,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z30,z4,z5,z6]),(0,[z22,z0,z1,z2,z90,z5,z6])]],
   [[(0,[z282,z0,z1,z2,z4,z5,z6]),(0,[z179,z1,z2,z4,z5,z6,z8]),(0,[z136,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z6,z283])],[(0,[z151,z1,z2,z4,z5,z6,z8]),(0,[z268,z1,z2,z4,z5,z6,z8]),(0,[z29,z0,z1,z2,z4,z5,z6]),(0,[z284,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z285,z5,z6])],[(0,[z286,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z287,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z42,z6]),(0,[z73,z1,z2,z4,z5,z6,z8]),(0,[z7,z1,z2,z4,z5,z6,z245]),(0,[z0,z1,z2,z4,z5,z6,z288]),(1,[z0,z240,z2,z4,z9,z6]),(0,[z0,z1,z2,z289,z4,z5,z6]),(1,[z227,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z290]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z22,z72,z1,z2,z4,z5,z6]),(0,[z0,z1,z291,z2,z4,z5,z6]),(0,[z0,z240,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z6,z292])],[(0,[z293,z1,z205,z2,z4,z5,z6]),(0,[z294,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z266,z6]),(0,[z0,z1,z295,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z296,z6]),(0,[z0,z1,z2,z297,z4,z5,z6]),(0,[z298,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z117,z4,z5,z6])],[(0,[z299,z0,z1,z2,z4,z5,z6]),(0,[z300,z0,z1,z2,z4,z5,z6]),(0,[z22,z0,z91,z1,z2,z5,z6]),(0,[z0,z1,z301,z2,z4,z5,z6])],[(0,[z7,z1,z13,z2,z4,z5,z6]),(0,[z0,z240,z2,z4,z5,z9,z6]),(0,[z0,z1,z2,z4,z5,z280,z6]),(1,[z1,z2,z4,z5,z302,z6]),(0,[z0,z303,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z18,z4,z5,z6])],[(0,[z293,z59,z1,z2,z4,z5,z6])]],
   [[(0,[z293,z221,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z137,z4,z201,z6]),(0,[z0,z1,z2,z4,z5,z6,z304]),(0,[z0,z305,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z84,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z6,z306]),(0,[z37,z0,z1,z2,z239,z5,z6]),(0,[z0,z1,z307,z2,z4,z5,z6]),(0,[z29,z0,z1,z30,z4,z5,z6]),(1,[z1,z2,z117,z4,z5,z6])],[(1,[z293,z231,z2,z4,z5,z6]),(0,[z0,z308,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z23,z5,z6]),(0,[z0,z179,z1,z2,z4,z5,z262]),(0,[z0,z1,z84,z4,z279,z5,z6])],[(0,[z0,z1,z2,z134,z4,z5,z6]),(0,[z309,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z310,z5,z6]),(0,[z0,z1,z2,z63,z4,z5,z6])],[(0,[z293,z1,z231,z2,z4,z5,z6]),(0,[z0,z311,z1,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z312,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z8]),(0,[z7,z1,z2,z62,z4,z5,z6]),(0,[z0,z1,z2,z313,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z314]),(0,[z0,z1,z2,z315,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z316]),(0,[z221,z317,z1,z2,z4,z5,z6]),(0,[z318,z0,z1,z2,z4,z5,z6]),(0,[z7,z110,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z319,z5,z6])],[(0,[z0,z317,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z320,z5,z6]),(0,[z0,z1,z2,z4,z321,z5,z6]),(0,[z0,z1,z2,z63,z5,z6,z11])],[(0,[z37,z0,z1,z2,z4,z5,z192]),(1,[z1,z2,z18,z4,z5,z8]),(0,[z0,z1,z2,z4,z322,z5,z6])]],
   [[(0,[z323,z0,z1,z2,z4,z5,z6]),(0,[z91,z1,z2,z4,z5,z6,z8]),(0,[z1,z2,z4,z5,z6,z8,z265]),(0,[z324,z0,z1,z2,z4,z5,z6]),(0,[z0,z325,z1,z2,z4,z5,z6]),(0,[z326,z0,z1,z2,z4,z5,z6])],[(0,[z327,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z328,z2,z4,z5,z6]),(0,[z0,z1,z2,z90,z5,z6,z11]),(1,[z0,z1,z66,z4,z5,z6]),(0,[z53,z0,z1,z33,z2,z4,z5]),(0,[z0,z1,z329,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z330,z6]),(0,[z0,z115,z1,z2,z4,z5,z6]),(0,[z331,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z152,z6]),(0,[z7,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z332,z4,z5,z6]),(1,[z1,z2,z4,z5,z120,z6]),(0,[z0,z268,z1,z2,z137,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z37,z0,z1,z2,z4,z42,z6]),(0,[z1,z2,z62,z4,z5,z6,z8]),(0,[z0,z1,z2,z333,z4,z5,z6]),(0,[z29,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z334,z2,z4,z5,z6]),(0,[z0,z335,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z336,z6]),(0,[z0,z1,z2,z18,z62,z4,z5])],[(0,[z1,z231,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z4,z337,z5,z6]),(0,[z0,z1,z2,z4,z5,z158,z160]),(0,[z0,z1,z2,z18,z4,z5,z160]),(0,[z0,z1,z2,z338,z4,z5,z6]),(0,[z0,z339,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z103]),(0,[z0,z1,z2,z4,z5,z340,z6]),(0,[z7,z1,z2,z4,z5,z158,z6]),(0,[z7,z1,z2,z18,z4,z5,z6]),(0,[z111,z0,z240,z2,z4,z5,z6]),(0,[z341,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z137,z4,z6])],[(0,[z1,z231,z2,z164,z4,z5,z6]),(0,[z59,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z63,z4,z5,z6,z8]),(0,[z53,z0,z1,z2,z4,z5,z8]),(0,[z0,z73,z1,z2,z90,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z342]),(0,[z0,z1,z2,z4,z5,z6,z11]),(0,[z0,z1,z2,z343,z4,z5,z6])],[(0,[z1,z205,z2,z4,z201,z5,z6]),(0,[z21,z110,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z344,z4,z5,z6]),(0,[z0,z1,z2,z54,z4,z5,z6]),(0,[z0,z91,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z345,z6])]],
   [[(0,[z1,z2,z4,z57,z5,z6,z8]),(0,[z1,z2,z95,z4,z5,z6,z8])],[(0,[z59,z37,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z283]),(0,[z0,z1,z346,z2,z4,z5,z6]),(0,[z0,z1,z68,z4,z57,z5,z6]),(0,[z0,z1,z347,z2,z4,z5,z6]),(0,[z0,z1,z2,z18,z4,z5,z11])],[(0,[z0,z1,z205,z2,z4,z5,z6]),(1,[z0,z1,z2,z163,z4,z6]),(0,[z0,z1,z2,z4,z348,z5,z6]),(0,[z37,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z349,z4,z5,z6]),(0,[z29,z0,z1,z2,z4,z350,z6]),(0,[z0,z1,z2,z4,z5,z351,z6]),(0,[z0,z91,z1,z2,z5,z6,z11]),(0,[z0,z1,z2,z352,z4,z5,z6])],[(0,[z353,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z354,z4,z5,z6]),(0,[z61,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z355,z2,z30,z4,z5]),(0,[z0,z1,z2,z68,z90,z5,z6]),(0,[z53,z0,z1,z2,z4,z5,z10])],[(0,[z37,z0,z1,z2,z4,z112,z6]),(0,[z0,z1,z2,z356,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z357]),(0,[z358,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z359,z5,z6]),(0,[z360,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z361,z6]),(0,[z0,z1,z2,z4,z5,z6,z362]),(0,[z7,z317,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z266,z5,z6]),(0,[z0,z1,z2,z4,z363,z5,z6]),(1,[z0,z1,z291,z4,z5,z6]),(0,[z111,z161,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z267,z6]),(0,[z0,z1,z12,z2,z4,z5,z6])],[(0,[z59,z1,z2,z4,z41,z5,z6]),(0,[z1,z2,z4,z5,z121,z6,z8]),(0,[z0,z1,z2,z364,z4,z5,z6]),(0,[z0,z1,z2,z4,z365,z5,z6]),(0,[z366,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z367,z5,z6]),(0,[z0,z1,z2,z63,z4,z5,z11]),(0,[z0,z1,z2,z4,z368,z5,z6])],[(0,[z113,z0,z1,z2,z164,z4,z6]),(0,[z110,z1,z2,z38,z4,z5,z6]),(0,[z124,z1,z2,z68,z4,z5,z6]),(0,[z369,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z59,z1,z2,z164,z4,z5,z6]),(0,[z7,z1,z328,z2,z4,z5,z6]),(1,[z142,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z370,z5,z6])],[(0,[z21,z0,z1,z2,z4,z9,z6]),(1,[z61,z1,z2,z4,z5,z6]),(0,[z0,z1,z33,z2,z4,z5,z245]),(0,[z0,z1,z2,z4,z371,z5,z6]),(0,[z0,z1,z372,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z168,z6])],[(0,[z0,z1,z2,z224,z4,z5,z6]),(0,[z0,z1,z373,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z374,z6]),(0,[z1,z205,z2,z4,z5,z6,z8]),(0,[z0,z1,z375,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z350,z6]),(0,[z227,z0,z1,z2,z4,z5,z6])],[(0,[z44,z1,z2,z4,z5,z6,z8]),(0,[z0,z179,z1,z33,z2,z4,z5]),(0,[z0,z1,z2,z376,z4,z5,z6])],[(0,[z110,z1,z2,z4,z5,z42,z6]),(0,[z114,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z11]),(0,[z0,z79,z1,z2,z4,z5,z6]),(0,[z142,z1,z2,z30,z4,z5,z6]),(0,[z0,z128,z1,z80,z4,z5,z6]),(0,[z22,z0,z1,z13,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z377]),(0,[z0,z1,z2,z4,z279,z5,z6])],[(0,[z0,z1,z378,z2,z4,z5,z6]),(1,[z221,z317,z2,z4,z5,z6]),(1,[z0,z1,z2,z88,z5,z6]),(0,[z0,z1,z66,z2,z4,z5,z6])],[(0,[z0,z379,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z8,z102]),(0,[z380,z0,z1,z2,z4,z5,z6]),(0,[z0,z128,z1,z33,z4,z5,z6])]],
   [[(0,[z59,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z205,z2,z4,z5,z6]),(0,[z1,z13,z2,z4,z5,z6,z8]),(0,[z0,z179,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z381,z4,z5,z6]),(0,[z0,z1,z2,z382,z4,z5,z6])],[(0,[z1,z2,z38,z4,z201,z5,z6]),(0,[z37,z0,z1,z2,z4,z5,z6]),(0,[z29,z0,z1,z2,z4,z5,z383]),(0,[z53,z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z12,z2,z62,z4,z5])],[(0,[z0,z1,z2,z384,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z385]),(0,[z0,z1,z2,z4,z5,z6,z262])],[(0,[z0,z1,z2,z4,z5,z386,z6]),(1,[z21,z1,z2,z4,z201,z6]),(0,[z7,z1,z12,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z383])],[(0,[z7,z221,z1,z2,z4,z5,z6]),(0,[z0,z1,z387,z2,z4,z5,z6]),(0,[z53,z0,z128,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z388,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z6])],[(0,[z389,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z390,z4,z5,z6]),(0,[z0,z1,z391,z2,z4,z5,z6]),(0,[z111,z0,z2,z4,z112,z5,z6]),(0,[z53,z0,z1,z2,z4,z45,z6]),(0,[z0,z179,z1,z2,z4,z5,z10])],[(0,[z0,z392,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z393,z4,z5,z6]),(1,[z0,z1,z2,z312,z5,z6]),(0,[z0,z1,z2,z394,z4,z5,z6]),(0,[z395,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z245,z262]),(0,[z0,z1,z2,z4,z396,z5,z6]),(0,[z0,z397,z1,z2,z4,z5,z6]),(0,[z1,z2,z211,z398,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z399,z6]),(0,[z0,z1,z2,z4,z5,z400,z6]),(1,[z0,z1,z17,z2,z18,z4]),(0,[z0,z401,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z402,z6]),(1,[z110,z1,z2,z38,z5,z6]),(0,[z1,z2,z403,z30,z4,z5,z6]),(0,[z0,z1,z131,z2,z30,z4,z5]),(0,[z0,z404,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z4,z5,z11])],[(0,[z7,z1,z231,z2,z4,z5,z6]),(0,[z155,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z405,z4,z5,z6]),(0,[z0,z1,z33,z2,z4,z5,z6])],[(0,[z0,z1,z2,z137,z4,z42,z6]),(0,[z21,z0,z1,z2,z4,z201,z6]),(0,[z0,z1,z2,z4,z5,z65,z6]),(0,[z0,z1,z2,z406,z4,z5,z6]),(0,[z1,z33,z50,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z407,z5,z6]),(0,[z408,z1,z2,z4,z5,z6,z8]),(0,[z0,z409,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z410,z4,z5,z6]),(0,[z411,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z376,z63,z4,z6]),(0,[z0,z1,z2,z259,z4,z5,z6])],[(0,[z293,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z412,z4,z5,z6]),(0,[z7,z1,z2,z4,z279,z5,z6]),(0,[z7,z1,z2,z4,z5,z43,z6]),(0,[z0,z1,z2,z4,z9,z6,z102]),(1,[z0,z1,z2,z198,z5,z6]),(0,[z413,z0,z1,z2,z4,z5,z6]),(0,[z0,z414,z1,z2,z4,z5,z6])],[(0,[z20,z0,z1,z205,z4,z5,z6]),(1,[z0,z1,z2,z4,z350,z6]),(0,[z136,z0,z1,z2,z4,z279,z6]),(0,[z0,z1,z2,z4,z5,z415,z6])],[(1,[z0,z1,z2,z4,z5,z362]),(0,[z0,z416,z1,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z30,z5,z6]),(0,[z0,z1,z2,z4,z417,z5,z6]),(0,[z0,z418,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z419,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z420]),(0,[z0,z1,z421,z2,z4,z5,z6]),(0,[z0,z1,z2,z422,z4,z5,z6]),(0,[z423,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z98,z102])],[(0,[z1,z2,z4,z5,z160,z6,z8]),(0,[z0,z1,z2,z4,z424,z5,z6])]],
   [[(0,[z0,z425,z1,z2,z4,z5,z6])],[(0,[z0,z426,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z67,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z427,z6]),(0,[z0,z1,z2,z4,z5,z6,z428]),(0,[z1,z2,z18,z259,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z262]),(0,[z0,z1,z2,z4,z5,z429,z6])],[(0,[z0,z1,z2,z4,z5,z160,z102]),(0,[z0,z1,z2,z4,z112,z121,z6]),(1,[z1,z2,z4,z5,z6,z420]),(0,[z0,z1,z2,z211,z4,z5,z6])],[(0,[z430,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z98,z5,z6]),(0,[z0,z1,z2,z403,z4,z5,z6]),(0,[z0,z73,z1,z13,z2,z5,z6]),(0,[z0,z1,z2,z24,z4,z5,z6]),(1,[z124,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z158,z6,z245]),(0,[z0,z1,z2,z431,z4,z5,z6])],[(0,[z221,z1,z2,z4,z201,z5,z6]),(0,[z1,z205,z2,z164,z4,z5,z6]),(0,[z432,z0,z1,z2,z4,z5,z6]),(0,[z7,z20,z1,z2,z4,z5,z6]),(0,[z37,z0,z1,z2,z312,z5,z6]),(0,[z0,z1,z2,z370,z30,z5,z6]),(0,[z0,z179,z2,z4,z5,z10,z6]),(0,[z0,z1,z13,z2,z5,z6,z11]),(0,[z0,z1,z2,z433,z4,z5,z6]),(0,[z0,z1,z434,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z435,z5,z6]),(1,[z0,z1,z2,z239,z5,z6]),(0,[z0,z1,z2,z4,z201,z5,z6]),(0,[z0,z1,z2,z4,z436,z5,z6]),(1,[z426,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z68,z4,z5,z263]),(0,[z0,z1,z2,z4,z5,z6,z437]),(0,[z0,z1,z33,z2,z62,z4,z5])],[(0,[z0,z1,z2,z4,z5,z438,z6]),(0,[z0,z1,z2,z153,z30,z4,z6]),(0,[z0,z1,z439,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z440,z2,z4,z5,z6]),(0,[z0,z1,z2,z62,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z441])],[(1,[z1,z2,z403,z4,z5,z6]),(0,[z0,z1,z442,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z158,z40,z6])],[(0,[z0,z1,z2,z38,z5,z43,z6]),(0,[z44,z0,z1,z2,z4,z5,z160]),(0,[z0,z1,z2,z4,z443,z5,z6]),(0,[z0,z91,z1,z12,z2,z5,z6]),(0,[z0,z1,z33,z4,z5,z6,z245]),(0,[z0,z1,z247,z2,z4,z5,z6])],[(0,[z408,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z189]),(0,[z444,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z445,z5,z6]),(0,[z0,z1,z2,z62,z5,z6,z11])],[(0,[z293,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z192]),(0,[z0,z1,z30,z4,z57,z5,z6]),(1,[z0,z73,z2,z23,z5,z6]),(0,[z0,z1,z33,z2,z4,z5,z11]),(0,[z0,z1,z2,z4,z5,z302,z6])],[(0,[z0,z1,z2,z4,z5,z6,z446]),(0,[z0,z1,z2,z4,z90,z5,z6])],[(0,[z7,z1,z2,z4,z424,z5,z6]),(0,[z7,z268,z1,z2,z4,z5,z6]),(1,[z194,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z195,z5,z6]),(1,[z0,z1,z313,z4,z5,z6]),(1,[z0,z1,z2,z4,z447,z6])],[(0,[z0,z1,z2,z4,z448,z5,z6]),(0,[z0,z1,z2,z23,z57,z5,z6]),(0,[z0,z449,z1,z2,z4,z5,z6])]],
   [[(0,[z450,z0,z1,z2,z4,z5,z6]),(0,[z317,z1,z2,z4,z5,z6,z8]),(0,[z22,z0,z1,z291,z4,z5,z6]),(0,[z111,z0,z1,z2,z4,z9,z6]),(0,[z0,z2,z4,z5,z10,z6,z262]),(0,[z0,z1,z2,z184,z4,z5,z6])],[(0,[z0,z1,z2,z451,z4,z5,z6]),(0,[z221,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z452,z2,z4,z5,z6]),(1,[z1,z2,z62,z4,z5,z8]),(1,[z1,z2,z244,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z453,z6]),(0,[z0,z1,z2,z4,z5,z158,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z221,z0,z1,z2,z4,z5,z316]),(0,[z0,z1,z2,z4,z5,z6,z8]),(0,[z7,z1,z2,z211,z4,z5,z6]),(0,[z0,z1,z80,z4,z57,z5,z6]),(0,[z0,z1,z2,z454,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z455,z6])],[(0,[z0,z1,z2,z456,z4,z5,z6]),(0,[z457,z0,z1,z2,z4,z5,z6]),(0,[z458,z0,z1,z2,z4,z5,z6]),(0,[z0,z317,z1,z2,z4,z169,z6]),(1,[z37,z1,z2,z4,z42,z6]),(0,[z0,z1,z84,z2,z137,z4,z6])],[(0,[z20,z0,z1,z164,z4,z5,z6]),(0,[z0,z459,z1,z2,z4,z5,z6]),(0,[z460,z0,z1,z2,z4,z5,z6]),(0,[z110,z1,z205,z2,z4,z5,z6]),(0,[z0,z1,z461,z2,z4,z5,z6]),(0,[z462,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z463]),(0,[z0,z1,z2,z464,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z7,z1,z2,z4,z201,z5,z6]),(0,[z1,z2,z4,z5,z6,z8,z245]),(0,[z0,z1,z2,z4,z5,z158,z8]),(0,[z0,z1,z2,z4,z5,z465,z6]),(0,[z0,z1,z2,z18,z4,z5,z8]),(0,[z0,z1,z466,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z203,z6])],[(0,[z0,z467,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z62,z4,z5,z160]),(0,[z468,z0,z1,z2,z4,z5,z6]),(0,[z0,z469,z1,z2,z4,z5,z6]),(0,[z0,z470,z1,z2,z4,z5,z6])],[(0,[z0,z471,z1,z2,z4,z5,z6]),(0,[z167,z1,z2,z4,z5,z158,z6])]],
   [[(0,[z0,z1,z2,z472,z4,z5,z6]),(0,[z1,z2,z18,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z120,z6]),(1,[z1,z2,z398,z4,z5,z6]),(0,[z0,z1,z473,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z62,z5,z6]),(1,[z188,z1,z2,z4,z5,z6])],[(0,[z1,z2,z333,z4,z5,z6,z8]),(1,[z0,z1,z54,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z474,z6])],[(0,[z475,z0,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z158,z8]),(0,[z29,z0,z1,z2,z4,z448,z6]),(0,[z0,z1,z2,z4,z447,z5,z6]),(0,[z0,z240,z1,z84,z2,z4,z6]),(0,[z1,z2,z4,z5,z10,z6,z420]),(0,[z0,z1,z2,z4,z5,z158,z10])],[(0,[z0,z1,z2,z476,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z477,z6]),(0,[z1,z2,z4,z201,z5,z42,z6]),(0,[z0,z1,z2,z4,z478,z5,z6]),(0,[z0,z1,z2,z4,z479,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z480,z4,z5,z6])],[(0,[z110,z1,z231,z2,z4,z5,z6]),(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z90,z5,z6]),(0,[z0,z79,z80,z2,z4,z5,z6]),(0,[z0,z1,z481,z2,z4,z5,z6]),(0,[z0,z1,z482,z2,z4,z5,z6])],[(0,[z0,z1,z2,z483,z4,z5,z6]),(0,[z484,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z43,z6,z11])],[(0,[z0,z91,z73,z1,z2,z5,z6]),(0,[z485,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z211,z4,z43,z6])],[(0,[z486,z0,z1,z2,z4,z5,z6]),(0,[z59,z0,z1,z2,z4,z5,z487]),(0,[z151,z37,z1,z2,z4,z5,z6]),(0,[z488,z0,z1,z2,z4,z5,z6]),(0,[z21,z1,z2,z4,z201,z5,z6]),(0,[z286,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z355,z2,z4,z5,z6]),(0,[z0,z1,z489,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z137,z4,z5,z6]),(0,[z0,z1,z2,z490,z4,z5,z6])],[(0,[z0,z1,z2,z41,z5,z43,z6]),(0,[z491,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z492,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6]),(0,[z0,z1,z2,z4,z201,z43,z6]),(0,[z7,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z494,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z495,z6]),(0,[z0,z1,z246,z2,z4,z158,z6]),(0,[z0,z1,z496,z2,z4,z5,z6])],[(0,[z0,z1,z2,z497,z4,z5,z6]),(0,[z0,z1,z33,z2,z4,z5,z158]),(0,[z0,z1,z2,z18,z4,z6,z102])],[(0,[z0,z1,z498,z2,z4,z5,z6]),(0,[z317,z1,z205,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z499,z5,z6]),(1,[z20,z1,z205,z4,z5,z6]),(0,[z0,z1,z2,z500,z4,z5,z6]),(0,[z501,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z502,z2,z4,z5,z6]),(1,[z101,z1,z2,z4,z5,z6])],[(0,[z151,z1,z2,z4,z41,z5,z6]),(0,[z21,z0,z1,z2,z4,z42,z6]),(0,[z0,z1,z2,z4,z5,z503,z6]),(0,[z0,z1,z2,z4,z5,z6,z504]),(0,[z0,z505,z1,z2,z4,z5,z6]),(0,[z506,z1,z2,z4,z98,z5,z6]),(0,[z0,z1,z247,z2,z98,z5,z6])],[(0,[z1,z2,z4,z5,z6,z8,z290]),(0,[z7,z1,z17,z2,z4,z5,z6]),(0,[z0,z1,z2,z507,z4,z5,z6]),(0,[z0,z1,z246,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z508,z5,z6]),(0,[z0,z1,z2,z4,z509,z5,z6]),(0,[z510,z0,z1,z2,z4,z5,z6]),(0,[z511,z0,z1,z2,z4,z5,z6]),(0,[z512,z0,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z4,z5,z121,z6]),(0,[z0,z1,z84,z2,z4,z6,z102]),(1,[z1,z2,z4,z5,z207,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z293,z0,z231,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z203,z6]),(1,[z423,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z279,z5,z6,z8]),(0,[z0,z1,z513,z2,z4,z5,z6]),(1,[z514,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z515,z4,z5])],[(0,[z110,z0,z1,z2,z41,z5,z6]),(1,[z53,z0,z2,z4,z5,z262]),(0,[z136,z0,z1,z17,z2,z4,z6])],[(1,[z53,z1,z2,z4,z5,z8])],[(0,[z317,z1,z231,z2,z4,z5,z6]),(0,[z516,z0,z1,z2,z4,z5,z6]),(0,[z221,z1,z2,z164,z4,z5,z6]),(0,[z0,z517,z1,z2,z4,z5,z6]),(0,[z0,z1,z518,z2,z4,z5,z6]),(0,[z21,z1,z2,z4,z5,z6,z8]),(0,[z53,z250,z1,z2,z4,z5,z6]),(0,[z235,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z376,z4,z6])],[(0,[z0,z1,z2,z164,z4,z5,z6]),(0,[z7,z240,z1,z2,z4,z5,z6]),(0,[z519,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z231,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z520]),(0,[z0,z1,z2,z4,z5,z8,z102]),(0,[z136,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z521,z2,z4,z5,z6]),(0,[z0,z1,z2,z515,z4,z5,z6]),(0,[z522,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z523,z2,z4,z5,z6]),(0,[z0,z1,z2,z524,z4,z5,z6]),(0,[z151,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z525]),(0,[z1,z2,z4,z5,z10,z6,z8]),(0,[z29,z0,z1,z2,z4,z5,z65]),(0,[z514,z1,z2,z211,z4,z5,z6])],[(0,[z0,z1,z2,z4,z526,z5,z6]),(0,[z0,z1,z2,z527,z4,z5,z6]),(0,[z7,z1,z2,z4,z112,z5,z6]),(0,[z136,z111,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z528,z5,z6]),(0,[z0,z1,z529,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z62,z4,z5,z262]),(0,[z0,z1,z2,z4,z5,z530,z6]),(0,[z531,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z43,z6])],[(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z4,z5,z6,z532]),(0,[z22,z426,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z45,z6])],[(0,[z1,z2,z4,z5,z42,z6,z8]),(0,[z0,z533,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z534,z6]),(0,[z0,z1,z2,z137,z211,z4,z6])],[(0,[z0,z1,z535,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z536,z5,z6]),(0,[z0,z537,z1,z2,z4,z5,z6]),(1,[z0,z149,z1,z2,z4,z6]),(0,[z111,z219,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z85])],[(0,[z0,z1,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z6,z102]),(0,[z0,z1,z2,z538,z4,z5,z6])],[(0,[z1,z80,z2,z4,z5,z6,z8]),(0,[z0,z1,z539,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z540,z6]),(0,[z541,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z542,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z543,z6]),(0,[z0,z1,z2,z4,z544,z5,z6]),(0,[z136,z0,z1,z2,z4,z43,z6])],[(0,[z1,z2,z4,z5,z465,z6,z8]),(0,[z7,z1,z513,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z316,z6]),(0,[z0,z1,z2,z545,z4,z5,z6]),(0,[z37,z0,z1,z2,z4,z5,z546]),(0,[z21,z0,z1,z84,z2,z4,z6]),(0,[z1,z2,z4,z5,z6,z8,z11]),(0,[z1,z2,z547,z4,z5,z6,z8]),(0,[z0,z1,z2,z548,z4,z5,z6]),(0,[z0,z1,z2,z4,z549,z5,z6]),(0,[z0,z550,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z551,z5,z6])],[(1,[z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z552]),(0,[z0,z1,z2,z4,z5,z158,z262]),(1,[z0,z179,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z553,z5,z6]),(1,[z1,z2,z538,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z554,z6]),(0,[z0,z555,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z556,z5,z6]),(1,[z183,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z5,z43,z6])],[(0,[z0,z1,z2,z4,z5,z6,z557]),(0,[z87,z0,z1,z2,z4,z5,z6]),(0,[z221,z0,z1,z2,z4,z5,z362]),(0,[z7,z1,z2,z164,z4,z5,z6]),(0,[z118,z1,z2,z62,z4,z5,z6])],[(0,[z221,z0,z231,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z103,z6]),(0,[z558,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z262,z11]),(0,[z0,z1,z2,z4,z559,z5,z6]),(0,[z0,z128,z1,z2,z4,z5,z245])],[(0,[z0,z1,z2,z4,z5,z6,z560]),(0,[z0,z1,z561,z2,z4,z5,z6]),(1,[z111,z0,z2,z4,z112,z6]),(0,[z0,z1,z562,z2,z4,z5,z6])],[(0,[z563,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z564,z6]),(1,[z0,z1,z2,z4,z168,z6]),(0,[z0,z1,z2,z565,z4,z5,z6])],[(0,[z59,z110,z1,z2,z4,z5,z6]),(0,[z44,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z160]),(0,[z0,z1,z566,z2,z4,z5,z6]),(0,[z1,z2,z4,z98,z230,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z567,z6]),(0,[z0,z1,z568,z2,z4,z5,z6]),(0,[z0,z1,z569,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z570]),(0,[z1,z2,z62,z538,z4,z5,z6]),(0,[z0,z1,z2,z4,z69,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z123]),(0,[z1,z2,z38,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z571,z6]),(1,[z1,z2,z4,z5,z8,z245]),(0,[z0,z1,z80,z2,z4,z5,z6]),(0,[z0,z1,z572,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z573])],[(0,[z0,z1,z2,z4,z5,z574,z6]),(0,[z0,z1,z575,z2,z4,z5,z6]),(0,[z576,z0,z1,z2,z4,z5,z6]),(0,[z22,z1,z2,z4,z5,z6,z8]),(0,[z0,z577,z1,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z4,z5,z6])],[(0,[z37,z21,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z270,z6]),(0,[z136,z0,z240,z1,z2,z4,z6]),(0,[z0,z1,z2,z578,z4,z5,z6])],[(0,[z579,z0,z1,z2,z4,z5,z6]),(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z110,z1,z2,z4,z5,z6,z8]),(0,[z53,z1,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z581,z5,z6])],[(0,[z582,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z41,z5,z42,z6]),(0,[z583,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z112,z279,z6]),(0,[z162,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z584,z4,z5,z6]),(0,[z0,z1,z585,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z5,z6,z11]),(0,[z188,z0,z1,z2,z4,z5,z6])],[(0,[z1,z205,z2,z4,z41,z5,z6]),(0,[z0,z1,z2,z137,z4,z112,z6]),(0,[z0,z1,z2,z586,z4,z5,z6])],[(0,[z37,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z160]),(0,[z0,z1,z2,z587,z4,z5,z6])]],
   [[(0,[z0,z588,z1,z2,z4,z5,z6]),(0,[z0,z589,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z9,z121,z6]),(0,[z0,z1,z2,z4,z5,z11,z102]),(1,[z506,z1,z2,z4,z5,z6])],[(0,[z59,z0,z1,z205,z4,z5,z6]),(0,[z151,z0,z1,z2,z38,z5,z6]),(0,[z0,z1,z2,z4,z5,z590,z6]),(0,[z0,z1,z2,z4,z5,z6,z591]),(0,[z0,z1,z2,z4,z98,z6,z102])],[(0,[z592,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z593,z6]),(1,[z1,z50,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z594,z5,z6]),(0,[z0,z327,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z4,z112,z6]),(0,[z595,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z157,z2,z5,z6]),(0,[z0,z1,z12,z2,z63,z5,z6])],[(0,[z0,z596,z1,z2,z4,z5,z6]),(0,[z0,z194,z1,z2,z4,z5,z6]),(0,[z0,z1,z30,z4,z5,z6,z245]),(0,[z0,z1,z2,z4,z5,z6,z597]),(0,[z0,z128,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z8,z262]),(0,[z162,z1,z2,z4,z5,z10,z6]),(0,[z0,z1,z598,z2,z4,z5,z6]),(0,[z514,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z112,z5,z6,z8]),(0,[z0,z599,z1,z2,z4,z5,z6])],[(0,[z59,z317,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z487]),(0,[z0,z1,z2,z600,z4,z5,z6]),(0,[z0,z1,z2,z62,z4,z5,z8]),(0,[z22,z0,z1,z2,z4,z5,z283]),(0,[z0,z601,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z244,z4,z5,z6]),(0,[z602,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z80,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z383]),(0,[z0,z1,z2,z4,z603,z5,z6]),(0,[z0,z1,z604,z2,z4,z5,z6]),(0,[z0,z1,z2,z605,z4,z5,z6])],[(0,[z44,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z547,z4,z5,z6]),(0,[z7,z577,z1,z2,z4,z5,z6]),(0,[z250,z0,z1,z2,z4,z5,z6]),(0,[z506,z0,z1,z2,z4,z5,z6])],[(0,[z293,z0,z317,z2,z4,z5,z6]),(0,[z606,z0,z1,z2,z4,z5,z6]),(0,[z20,z1,z205,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z607,z5,z6]),(0,[z111,z1,z2,z4,z5,z6,z8]),(0,[z0,z149,z1,z2,z4,z5,z6]),(0,[z0,z1,z80,z4,z5,z6,z245]),(0,[z0,z1,z2,z4,z5,z608,z6]),(0,[z0,z240,z1,z2,z4,z112,z6]),(0,[z0,z1,z2,z4,z609,z5,z6]),(1,[z0,z1,z12,z2,z62,z5])],[(0,[z0,z1,z2,z4,z610,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z611]),(0,[z0,z1,z2,z612,z4,z5,z6]),(0,[z613,z0,z1,z2,z4,z5,z6])],[(0,[z0,z128,z1,z30,z4,z5,z6]),(1,[z0,z1,z355,z2,z4,z5]),(0,[z0,z1,z2,z62,z4,z5,z10]),(0,[z0,z1,z2,z137,z4,z5,z6]),(0,[z0,z614,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z160,z245]),(1,[z0,z1,z2,z4,z270,z6]),(0,[z53,z0,z1,z2,z4,z267,z6]),(0,[z0,z1,z615,z2,z4,z5,z6]),(0,[z616,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z617,z6]),(0,[z0,z1,z2,z618,z4,z5,z6]),(0,[z20,z221,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z619,z6]),(0,[z580,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z88,z4,z5,z6]),(0,[z0,z1,z2,z4,z620,z5,z6]),(0,[z0,z1,z2,z4,z5,z621,z6]),(0,[z0,z1,z2,z398,z4,z5,z6]),(0,[z1,z2,z4,z5,z302,z43,z6])],[(0,[z0,z1,z622,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z623,z4,z5,z6]),(0,[z0,z624,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z163,z4,z5,z6]),(0,[z625,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z279,z9,z6]),(0,[z0,z1,z2,z211,z5,z43,z6]),(0,[z0,z1,z626,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z627,z6]),(0,[z1,z2,z38,z4,z41,z5,z6]),(0,[z0,z1,z628,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z4,z5,z6])],[(0,[z20,z1,z231,z2,z4,z5,z6]),(0,[z1,z177,z2,z4,z5,z6,z8]),(0,[z0,z1,z12,z2,z90,z5,z6])],[(0,[z110,z221,z1,z2,z4,z5,z6]),(0,[z7,z128,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z629,z6])],[(0,[z630,z0,z1,z2,z4,z5,z6]),(0,[z0,z631,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z632,z4,z5,z6]),(0,[z183,z0,z1,z2,z4,z5,z6])],[(1,[z72,z1,z2,z4,z5,z6]),(0,[z53,z0,z179,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z10,z245]),(1,[z0,z1,z2,z5,z280,z6]),(0,[z0,z268,z1,z2,z4,z43,z6])],[(0,[z0,z1,z2,z633,z4,z5,z6]),(0,[z634,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z370,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z635,z6]),(0,[z111,z0,z1,z84,z2,z4,z6]),(0,[z0,z636,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z637,z5,z6]),(0,[z0,z128,z1,z2,z4,z5,z11]),(0,[z0,z1,z2,z4,z5,z638,z6]),(0,[z639,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z59,z0,z1,z164,z4,z5,z6]),(0,[z1,z2,z4,z5,z158,z6,z8]),(0,[z408,z7,z1,z2,z4,z5,z6]),(0,[z29,z0,z79,z2,z4,z5,z6]),(0,[z0,z1,z2,z640,z4,z5,z6]),(0,[z0,z240,z1,z2,z4,z5,z6]),(0,[z219,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z641,z5,z6]),(0,[z0,z1,z2,z642,z4,z5,z6])],[(0,[z293,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z643,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z644,z5,z6]),(0,[z0,z101,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z645,z4,z5,z6]),(0,[z0,z646,z1,z2,z4,z5,z6])],[(0,[z0,z647,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z90,z5,z6,z8]),(0,[z0,z1,z648,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z112,z5,z6]),(0,[z0,z1,z649,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z263]),(0,[z0,z1,z2,z62,z4,z5,z102])],[(0,[z221,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z169,z6]),(0,[z0,z1,z650,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z83]),(0,[z0,z651,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z207,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z652,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z160,z6]),(0,[z0,z1,z2,z4,z5,z6,z653])],[(0,[z0,z1,z2,z654,z4,z5,z6]),(0,[z0,z1,z2,z137,z5,z43,z6]),(0,[z0,z1,z2,z655,z4,z5,z6])],[(0,[z221,z0,z317,z2,z4,z5,z6]),(0,[z1,z2,z164,z4,z5,z6,z8]),(0,[z1,z2,z4,z5,z6,z8,z446]),(0,[z0,z1,z2,z4,z5,z656,z6]),(1,[z161,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z84,z4,z5,z6]),(0,[z0,z1,z2,z657,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z658,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z487])],[(1,[z151,z1,z2,z41,z5,z6]),(0,[z29,z0,z2,z30,z4,z5,z6]),(0,[z0,z73,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z659,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z660]),(0,[z0,z1,z2,z4,z5,z6,z102])],[(0,[z29,z0,z1,z80,z4,z5,z6])],[(0,[z1,z2,z4,z644,z5,z6,z8]),(0,[z0,z1,z2,z661,z4,z5,z6]),(0,[z167,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z662,z4,z5,z6]),(0,[z0,z1,z2,z211,z4,z5,z85]),(0,[z0,z1,z2,z663,z4,z5,z6])],[(0,[z221,z1,z2,z4,z41,z5,z6]),(1,[z59,z1,z164,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z8,z8]),(0,[z53,z0,z1,z2,z198,z5,z6]),(0,[z664,z0,z1,z2,z4,z5,z6]),(0,[z423,z1,z2,z63,z4,z5,z6])],[(0,[z0,z1,z2,z4,z41,z5,z6]),(1,[z0,z1,z2,z4,z5,z546]),(1,[z44,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z665,z6]),(0,[z0,z1,z2,z4,z5,z10,z6]),(0,[z0,z1,z2,z666,z4,z5,z6]),(0,[z0,z268,z1,z12,z2,z5,z6]),(0,[z667,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z668,z5,z6])],[(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z670,z0,z1,z2,z4,z5,z6])],[(0,[z59,z20,z1,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z38,z5,z6]),(0,[z136,z37,z0,z1,z2,z4,z6]),(0,[z671,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z4,z5,z6]),(0,[z672,z0,z1,z2,z4,z5,z6]),(0,[z136,z0,z1,z2,z4,z6,z102])]],
   [[(0,[z0,z1,z2,z4,z5,z546,z6]),(0,[z21,z0,z1,z2,z4,z112,z6]),(0,[z634,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z673])],[(0,[z0,z317,z1,z2,z4,z191,z6]),(0,[z0,z1,z2,z4,z5,z674,z6]),(0,[z0,z1,z2,z4,z675,z5,z6]),(0,[z0,z1,z2,z676,z4,z5,z6]),(0,[z0,z1,z84,z2,z4,z279,z6])],[(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z201,z5,z6,z8]),(0,[z0,z1,z2,z4,z678,z5,z6]),(0,[z128,z1,z2,z4,z5,z6,z8]),(0,[z679,z0,z1,z2,z4,z5,z6]),(0,[z0,z91,z1,z13,z4,z5,z6]),(0,[z0,z1,z84,z2,z4,z121,z6]),(0,[z0,z1,z2,z98,z69,z5,z6])],[(0,[z0,z1,z2,z4,z680,z5,z6]),(0,[z0,z1,z681,z2,z4,z5,z6]),(0,[z0,z1,z2,z682,z4,z5,z6])],[(0,[z683,z0,z1,z2,z4,z5,z6]),(0,[z281,z1,z2,z4,z5,z6,z8]),(0,[z7,z1,z2,z4,z5,z160,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(1,[z22,z0,z2,z90,z5,z6]),(0,[z0,z1,z17,z2,z4,z43,z6])],[(0,[z685,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z174,z5,z6]),(0,[z0,z128,z1,z2,z4,z5,z158]),(0,[z0,z1,z2,z4,z686,z5,z6])],[(0,[z29,z1,z2,z4,z5,z6,z8]),(0,[z491,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z90,z57,z5,z6]),(0,[z0,z128,z179,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z687])],[(0,[z688,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z689,z2,z4,z5,z6]),(0,[z0,z690,z1,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z211,z5,z6]),(1,[z0,z1,z2,z211,z43,z6])]],
   [[(0,[z0,z1,z691,z2,z4,z5,z6]),(0,[z7,z0,z1,z2,z4,z5,z8]),(0,[z7,z73,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z102]),(0,[z0,z1,z2,z4,z5,z160,z11]),(1,[z0,z1,z2,z4,z448,z6]),(0,[z0,z1,z692,z2,z4,z5,z6]),(0,[z53,z0,z2,z4,z5,z6,z262])],[(0,[z693,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z694,z4,z5,z6]),(1,[z1,z2,z4,z230,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z136,z21,z0,z1,z2,z4,z6]),(0,[z696,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z697]),(1,[z136,z0,z1,z4,z121,z6])],[(0,[z0,z1,z2,z698,z4,z5,z6]),(0,[z0,z1,z39,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z57,z5,z6]),(0,[z0,z1,z2,z18,z4,z98,z5])],[(0,[z7,z1,z2,z4,z41,z5,z6]),(0,[z7,z1,z2,z4,z5,z10,z6]),(0,[z699,z0,z1,z2,z4,z5,z6]),(0,[z22,z0,z1,z313,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z447,z6]),(0,[z0,z700,z1,z2,z4,z5,z6]),(1,[z118,z1,z2,z4,z5,z6])],[(0,[z151,z110,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z68,z4,z5,z6]),(0,[z0,z1,z2,z701,z4,z5,z6]),(1,[z0,z91,z1,z57,z5,z6]),(0,[z702,z0,z1,z2,z4,z5,z6]),(0,[z0,z703,z1,z2,z4,z5,z6])],[(0,[z21,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z704,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z4,z5,z6]),(0,[z7,z1,z2,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z112,z43,z6])],[(0,[z0,z1,z2,z705,z4,z5,z6]),(0,[z59,z1,z2,z4,z201,z5,z6]),(0,[z1,z295,z2,z4,z5,z6,z8]),(0,[z0,z1,z2,z4,z5,z8,z245]),(0,[z0,z91,z1,z2,z57,z5,z6]),(0,[z0,z1,z2,z515,z211,z4,z5]),(0,[z0,z706,z1,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z309,z1,z2,z4,z5,z8]),(0,[z29,z0,z30,z4,z350,z6]),(0,[z0,z1,z2,z4,z707,z6])],[(0,[z0,z708,z2,z4,z5,z6]),(0,[z1,z2,z163,z4,z6,z8]),(0,[z1,z2,z4,z203,z6,z8]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z0,z179,z628,z2,z4,z5]),(0,[z0,z1,z2,z4,z710,z6])],[(0,[z0,z1,z131,z2,z4,z5]),(0,[z22,z0,z313,z90,z5,z6])],[(0,[z0,z1,z2,z4,z5,z711]),(0,[z1,z2,z4,z712,z5,z6]),(0,[z227,z1,z2,z41,z5,z6]),(0,[z0,z1,z291,z4,z5,z283])],[(0,[z72,z1,z2,z4,z5,z6]),(0,[z0,z47,z1,z2,z153,z6]),(0,[z1,z2,z4,z5,z713,z6]),(0,[z714,z1,z2,z4,z5,z6]),(0,[z423,z1,z2,z63,z5,z11]),(0,[z1,z2,z4,z98,z230,z102])],[(0,[z0,z1,z2,z4,z448,z383])],[(0,[z110,z1,z2,z4,z5,z362]),(0,[z0,z1,z715,z2,z5,z6]),(0,[z0,z149,z1,z131,z2,z4]),(0,[z22,z0,z2,z90,z270,z6])],[(0,[z0,z1,z54,z4,z5,z8]),(0,[z0,z1,z2,z4,z716,z6])],[(0,[z0,z1,z717,z4,z5,z6]),(0,[z0,z1,z2,z718,z5,z6]),(0,[z0,z179,z2,z4,z5,z719])],[(0,[z0,z1,z2,z4,z720,z6]),(0,[z1,z2,z4,z5,z42,z192]),(0,[z0,z1,z2,z4,z350,z65])],[(0,[z0,z1,z2,z4,z721,z6])],[(0,[z0,z1,z2,z4,z169,z6]),(0,[z7,z1,z12,z2,z62,z5]),(0,[z722,z1,z2,z4,z5,z6]),(0,[z118,z1,z12,z2,z62,z5])],[(0,[z0,z1,z54,z4,z5,z10]),(0,[z0,z1,z2,z4,z723,z6])],[(0,[z0,z1,z2,z4,z724,z6]),(0,[z0,z1,z2,z4,z5,z725]),(0,[z227,z1,z2,z239,z5,z6]),(0,[z0,z1,z726,z2,z5,z6]),(0,[z7,z1,z355,z2,z4,z5]),(0,[z53,z7,z2,z4,z5,z262]),(0,[z727,z1,z2,z4,z5,z6]),(0,[z1,z2,z244,z4,z5,z263])],[(0,[z7,z1,z2,z4,z270,z6])],[(0,[z0,z1,z2,z4,z216,z189]),(0,[z728,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z729,z5,z6])]],
   [[(0,[z250,z1,z2,z4,z5,z316]),(0,[z0,z1,z2,z398,z43,z6])],[(0,[z29,z0,z30,z195,z5,z6]),(0,[z0,z1,z2,z730,z4,z6]),(0,[z0,z1,z2,z4,z5,z731]),(0,[z0,z1,z2,z4,z732,z6])],[(0,[z281,z2,z4,z5,z6,z446]),(0,[z124,z1,z2,z67,z4,z5]),(1,[z0,z1,z2,z43,z85])],[(0,[z110,z1,z2,z4,z5,z189]),(0,[z165,z1,z2,z4,z5,z8]),(0,[z0,z1,z561,z4,z5,z245])],[(0,[z733,z1,z2,z4,z5,z383]),(0,[z0,z1,z2,z4,z5,z734]),(0,[z250,z1,z66,z4,z5,z6]),(0,[z0,z1,z2,z735,z5,z6])],[(0,[z260,z231,z2,z4,z5,z6]),(0,[z22,z0,z2,z90,z5,z83]),(0,[z1,z2,z736,z4,z5,z6]),(0,[z0,z1,z2,z4,z737,z6])],[(0,[z1,z2,z655,z4,z5,z8])],[(0,[z179,z1,z2,z4,z5,z8]),(0,[z1,z2,z4,z738,z6,z8]),(0,[z1,z2,z4,z5,z658,z8])],[(0,[z0,z1,z2,z4,z739,z6])],[(0,[z167,z1,z2,z4,z5,z160])],[(0,[z0,z1,z2,z195,z5,z65]),(0,[z740,z1,z2,z4,z5,z6]),(0,[z1,z50,z2,z4,z5,z158])],[],[(0,[z0,z1,z2,z4,z741,z6])],[(0,[z1,z742,z164,z4,z5,z6]),(0,[z1,z2,z153,z4,z6,z8]),(0,[z7,z1,z2,z4,z5,z83]),(0,[z0,z2,z4,z743,z9,z6]),(0,[z0,z1,z2,z5,z744,z6])],[(0,[z1,z2,z4,z5,z6,z745]),(0,[z1,z2,z4,z746,z5,z8]),(0,[z1,z2,z4,z5,z6,z747]),(0,[z0,z1,z246,z2,z4,z6]),(0,[z0,z1,z33,z4,z5,z245]),(0,[z0,z1,z247,z2,z5,z6])],[(0,[z250,z1,z2,z4,z5,z6]),(0,[z748,z1,z2,z4,z5,z6]),(0,[z1,z2,z749,z4,z5,z6])]],
   [[(0,[z317,z2,z542,z4,z5,z6]),(0,[z114,z1,z2,z4,z5,z487]),(0,[z1,z2,z38,z712,z5,z6]),(0,[z1,z2,z4,z5,z546,z8]),(0,[z1,z2,z4,z5,z8,z385]),(0,[z0,z1,z2,z4,z5,z750])],[(0,[z7,z1,z2,z4,z5,z487]),(0,[z522,z1,z2,z4,z5,z8]),(0,[z1,z2,z4,z5,z6,z751])],[(0,[z44,z1,z2,z4,z5,z752]),(0,[z753,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z754,z4])],[(0,[z0,z1,z2,z4,z5,z755]),(0,[z0,z1,z33,z54,z4,z5]),(0,[z0,z1,z2,z4,z5,z263]),(0,[z0,z1,z756,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z619]),(0,[z281,z179,z2,z4,z5,z8]),(0,[z1,z2,z5,z280,z6,z8])],[(0,[z1,z2,z757,z4,z6,z8]),(0,[z101,z1,z2,z24,z5,z6])],[(0,[z114,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z758,z6]),(0,[z0,z1,z2,z759,z5,z6]),(0,[z0,z760,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z761]),(0,[z1,z2,z4,z5,z8,z560]),(0,[z7,z1,z2,z4,z5,z8]),(0,[z118,z1,z2,z4,z5,z8]),(0,[z616,z1,z2,z4,z5,z8]),(0,[z762,z1,z2,z4,z5,z6]),(0,[z1,z2,z763,z4,z5,z6])],[(0,[z764,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z4,z5,z765]),(0,[z766,z1,z2,z4,z5,z6])],[(0,[z1,z205,z2,z239,z5,z6]),(0,[z29,z0,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z767,z6]),(0,[z1,z768,z2,z4,z5,z6]),(0,[z769,z1,z2,z4,z5,z6])],[(0,[z0,z770,z1,z4,z5,z6]),(0,[z179,z1,z50,z2,z4,z5])],[(0,[z0,z1,z2,z771,z5,z6]),(0,[z1,z2,z4,z168,z6,z8])],[(0,[z0,z772,z2,z4,z5,z6]),(0,[z1,z2,z701,z4,z5,z8]),(0,[z703,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z773,z5,z6])],[(0,[z0,z1,z2,z774,z5,z6]),(0,[z221,z1,z2,z239,z5,z6]),(0,[z775,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z776,z5,z6])],[(0,[z1,z2,z4,z5,z383,z8]),(0,[z53,z2,z4,z5,z8,z262]),(0,[z286,z1,z2,z134,z5,z6]),(0,[z167,z1,z157,z2,z5,z6])]],
   [[(0,[z221,z317,z2,z4,z191,z6]),(0,[z1,z205,z2,z4,z5,z192]),(0,[z7,z1,z2,z211,z43,z6]),(0,[z777,z1,z2,z4,z5,z6]),(0,[z1,z778,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z779])],[(0,[z1,z4,z5,z158,z8,z245]),(0,[z0,z1,z2,z4,z45,z8]),(0,[z7,z1,z2,z4,z448,z6]),(0,[z0,z1,z2,z4,z5,z780]),(0,[z639,z0,z2,z4,z112,z6])],[(0,[z0,z1,z781,z2,z4,z6]),(0,[z1,z13,z2,z5,z8,z11]),(0,[z72,z1,z2,z4,z270,z6]),(0,[z0,z1,z2,z4,z5,z782]),(0,[z124,z1,z13,z68,z5,z6])],[(0,[z0,z1,z2,z4,z783,z6]),(0,[z0,z1,z2,z4,z784,z6]),(0,[z785,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z184,z68,z6]),(0,[z183,z1,z2,z4,z5,z750]),(0,[z0,z1,z2,z69,z5,z6])],[(0,[z221,z1,z2,z4,z5,z192]),(0,[z0,z1,z786,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z787])],[(0,[z0,z1,z2,z4,z5,z788]),(0,[z1,z2,z117,z4,z5,z6]),(0,[z1,z2,z4,z5,z40,z8])],[(0,[z20,z1,z2,z4,z5,z362]),(0,[z37,z1,z2,z4,z784,z6]),(0,[z789,z1,z2,z4,z5,z283])],[(0,[z7,z268,z1,z2,z137,z6]),(0,[z0,z1,z654,z4,z5,z245])],[(0,[z0,z1,z2,z4,z5,z790]),(0,[z1,z205,z742,z4,z5,z6]),(0,[z1,z2,z62,z5,z8,z11]),(0,[z0,z1,z2,z4,z791,z6]),(0,[z1,z2,z4,z5,z6,z792]),(0,[z0,z268,z1,z2,z609,z6])],[(0,[z793,z1,z2,z4,z5,z6]),(0,[z124,z1,z2,z184,z4,z6])],[(0,[z1,z205,z119,z4,z5,z6])],[(0,[z53,z0,z2,z654,z4,z5]),(0,[z1,z2,z538,z4,z5,z102]),(0,[z1,z2,z18,z538,z4,z5])],[(0,[z0,z1,z2,z4,z794,z6]),(0,[z0,z1,z2,z4,z5,z795]),(1,[z1,z2,z4,z5,z752]),(0,[z360,z0,z30,z4,z5,z6])],[(0,[z796,z0,z1,z2,z4,z6]),(0,[z151,z1,z2,z712,z5,z6]),(0,[z797,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z120,z6])],[(0,[z798,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z93,z5,z8]),(0,[z799,z7,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z800,z6]),(0,[z0,z1,z801,z4,z5,z6]),(0,[z802,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z448,z65]),(0,[z72,z1,z2,z4,z5,z83]),(0,[z0,z803,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z189,z8]),(0,[z7,z1,z2,z4,z5,z520])],[(0,[z221,z317,z2,z4,z5,z316]),(0,[z124,z1,z2,z4,z5,z263]),(0,[z804,z1,z2,z4,z5,z6]),(0,[z805,z1,z2,z4,z5,z85])],[(0,[z806,z1,z2,z4,z5,z6])],[],[(1,[z1,z2,z198,z5,z8])],[(0,[z0,z1,z2,z807,z5,z6]),(0,[z0,z1,z2,z808,z4,z6]),(0,[z809,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z63,z5,z11])],[(1,[z810,z2,z4,z5,z6]),(0,[z1,z811,z2,z4,z5,z6]),(0,[z116,z1,z2,z4,z5,z8]),(0,[z812,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z85]),(0,[z219,z1,z2,z4,z5,z813]),(0,[z0,z1,z2,z4,z5,z814]),(0,[z1,z2,z117,z4,z5,z11])],[(0,[z0,z1,z291,z4,z5,z6]),(0,[z0,z1,z815,z2,z4,z6])],[(0,[z1,z2,z38,z5,z438,z6]),(0,[z1,z2,z5,z43,z8,z11]),(0,[z1,z2,z816,z4,z5,z6]),(0,[z0,z2,z23,z817,z5,z6]),(0,[z111,z161,z2,z4,z112,z6])],[(0,[z0,z1,z2,z4,z5,z818]),(0,[z0,z1,z2,z4,z5,z819]),(0,[z0,z1,z131,z2,z153,z4]),(0,[z820,z1,z2,z4,z5,z6]),(0,[z1,z2,z821,z4,z5,z6]),(0,[z1,z2,z376,z117,z4,z6])],[(0,[z162,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z822,z6]),(0,[z1,z2,z4,z5,z83,z8]),(0,[z1,z2,z54,z4,z5,z8]),(0,[z0,z1,z2,z4,z40,z160]),(0,[z149,z1,z2,z403,z4,z6]),(0,[z823,z1,z2,z4,z5,z6]),(0,[z188,z1,z17,z2,z18,z4])],[(0,[z61,z1,z2,z4,z5,z6])],[(1,[z1,z2,z4,z5,z824]),(0,[z219,z1,z2,z4,z112,z6])],[(0,[z0,z1,z2,z239,z5,z192]),(0,[z0,z1,z2,z825,z5,z6])]],
   [[(0,[z7,z1,z2,z4,z40,z6]),(0,[z0,z1,z2,z181,z4,z102])],[(0,[z426,z1,z2,z4,z447,z6])],[(0,[z110,z1,z2,z705,z5,z6])],[(0,[z0,z1,z2,z826,z5,z6]),(0,[z0,z1,z2,z4,z827,z6])],[(0,[z0,z1,z2,z4,z828,z6]),(0,[z53,z179,z2,z4,z5,z8]),(0,[z1,z157,z2,z5,z158,z8]),(0,[z0,z1,z2,z4,z829,z6]),(0,[z506,z1,z2,z69,z5,z6])],[(0,[z1,z2,z195,z5,z6,z8]),(0,[z0,z1,z2,z90,z5,z263]),(0,[z1,z2,z830,z4,z5,z6]),(0,[z0,z1,z13,z68,z5,z6])],[(0,[z0,z1,z80,z195,z5,z6]),(0,[z831,z1,z2,z4,z5,z6])],[(0,[z613,z1,z2,z4,z201,z6]),(0,[z1,z2,z224,z4,z5,z8]),(0,[z1,z2,z4,z5,z85,z832])],[(0,[z21,z1,z2,z4,z201,z6]),(0,[z22,z7,z2,z90,z5,z6]),(0,[z0,z1,z2,z833,z5,z6])],[],[(0,[z1,z2,z4,z5,z180,z8]),(0,[z0,z1,z157,z246,z2,z6])],[(0,[z1,z205,z237,z4,z5,z6]),(0,[z664,z1,z2,z38,z5,z6]),(0,[z1,z2,z4,z5,z6,z834])],[(0,[z219,z1,z2,z4,z5,z6]),(0,[z110,z1,z2,z38,z5,z6]),(0,[z0,z1,z2,z239,z112,z6]),(0,[z7,z1,z2,z153,z4,z6]),(0,[z0,z1,z2,z184,z4,z6]),(0,[z1,z2,z4,z5,z835,z6]),(1,[z0,z1,z2,z69,z102])],[(0,[z0,z1,z836,z4,z5,z6])],[(0,[z136,z7,z1,z4,z121,z6]),(0,[z837,z0,z1,z2,z4,z6]),(0,[z162,z179,z2,z4,z5,z10]),(1,[z0,z1,z838,z5,z6])],[(0,[z1,z2,z839,z4,z5,z6]),(0,[z53,z1,z50,z2,z4,z5]),(0,[z840,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z841]),(0,[z1,z2,z4,z198,z5,z8]),(0,[z1,z157,z2,z5,z207,z6])],[(0,[z53,z250,z2,z4,z5,z262]),(0,[z0,z1,z2,z198,z267,z6]),(0,[z0,z1,z2,z4,z842,z6])],[(0,[z0,z1,z2,z4,z112,z192]),(0,[z1,z387,z2,z4,z5,z8]),(0,[z53,z0,z2,z198,z5,z262]),(0,[z0,z1,z157,z2,z40,z6])],[(0,[z0,z1,z2,z4,z843,z6]),(1,[z1,z54,z4,z5,z8]),(0,[z0,z1,z2,z4,z844,z6]),(0,[z227,z1,z2,z4,z112,z6])],[(0,[z1,z2,z38,z201,z43,z6]),(0,[z1,z2,z259,z4,z5,z6]),(0,[z7,z1,z2,z88,z5,z6]),(0,[z1,z2,z4,z5,z6,z845]),(0,[z846,z1,z2,z4,z5,z6]),(0,[z1,z2,z847,z4,z5,z6])],[(0,[z1,z2,z18,z4,z746,z5]),(0,[z0,z1,z848,z4,z5,z6])],[(0,[z1,z39,z164,z4,z5,z6]),(0,[z73,z2,z23,z5,z6,z8]),(0,[z250,z1,z2,z4,z5,z8]),(0,[z61,z1,z2,z4,z350,z6])],[(0,[z7,z1,z2,z4,z5,z152]),(1,[z0,z2,z817,z5,z6])],[(0,[z1,z849,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z850,z6])],[(0,[z0,z1,z2,z4,z191,z6]),(0,[z0,z1,z851,z4,z5,z6])],[(0,[z0,z1,z2,z239,z5,z6]),(0,[z1,z2,z4,z5,z158,z420])],[(0,[z1,z2,z4,z784,z42,z6]),(0,[z0,z469,z1,z57,z5,z6]),(0,[z852,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z833,z5,z11])],[(0,[z7,z1,z2,z4,z853,z6])],[(0,[z257,z1,z2,z4,z5,z8]),(0,[z522,z0,z2,z90,z5,z6])],[(0,[z0,z1,z84,z2,z239,z6]),(0,[z1,z2,z4,z5,z8,z573]),(0,[z1,z2,z211,z43,z6,z8]),(0,[z0,z1,z2,z198,z5,z160]),(0,[z854,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z855]),(0,[z856,z1,z2,z4,z5,z6])],[(0,[z634,z1,z2,z4,z5,z192]),(0,[z0,z1,z313,z4,z5,z283]),(0,[z0,z1,z2,z857,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z192]),(0,[z1,z2,z4,z644,z42,z6]),(0,[z1,z858,z2,z4,z5,z6]),(0,[z166,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z859,z4,z6]),(0,[z1,z2,z860,z4,z5,z6])],[(0,[z0,z1,z2,z4,z861,z6]),(0,[z0,z1,z2,z4,z5,z862]),(0,[z227,z1,z2,z4,z5,z6]),(0,[z0,z1,z863,z4,z5,z6]),(0,[z0,z1,z13,z48,z5,z6]),(0,[z0,z1,z2,z754,z4,z102])],[(0,[z194,z1,z2,z4,z5,z6]),(0,[z1,z864,z2,z4,z5,z6]),(0,[z268,z1,z2,z5,z8,z11]),(0,[z0,z1,z39,z4,z5,z245]),(0,[z0,z1,z649,z4,z5,z245]),(0,[z0,z1,z2,z98,z69,z102])],[(0,[z0,z1,z2,z4,z266,z6])],[(0,[z1,z2,z312,z5,z6,z8]),(0,[z29,z0,z355,z30,z4,z5]),(0,[z865,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z866,z6]),(0,[z1,z2,z4,z448,z6,z8]),(0,[z1,z2,z62,z4,z5,z8]),(0,[z867,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z833,z4,z5])],[(0,[z1,z2,z5,z158,z280,z8]),(0,[z1,z2,z4,z98,z8,z102]),(0,[z7,z1,z2,z4,z868,z6]),(0,[z869,z1,z2,z4,z5,z6])],[(0,[z1,z2,z870,z4,z6,z8]),(0,[z61,z1,z2,z195,z5,z6]),(0,[z0,z1,z291,z4,z270,z6]),(0,[z0,z1,z2,z137,z4,z85]),(0,[z1,z2,z259,z4,z5,z11])],[(0,[z871,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z872,z121,z6])],[(1,[z0,z2,z4,z5,z719]),(0,[z873,z1,z2,z4,z5,z6])],[(0,[z0,z1,z30,z195,z5,z6]),(0,[z0,z1,z2,z4,z5,z874]),(0,[z0,z875,z1,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z8]),(0,[z510,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z88,z5,z383]),(0,[z29,z0,z30,z4,z448,z6]),(0,[z29,z0,z47,z30,z5,z6])],[(0,[z0,z1,z2,z4,z5,z316]),(0,[z1,z2,z398,z4,z5,z6]),(0,[z789,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z876,z6]),(0,[z0,z1,z2,z877,z4,z6]),(0,[z0,z2,z4,z112,z743,z6]),(0,[z101,z1,z66,z4,z5,z6])],[],[(0,[z0,z1,z2,z497,z43,z6]),(0,[z0,z1,z2,z878,z4,z6]),(0,[z0,z1,z54,z4,z267,z6]),(1,[z0,z1,z2,z754,z4])],[(0,[z1,z80,z4,z5,z8,z245]),(0,[z29,z0,z153,z30,z4,z6])]],
   [[(0,[z317,z1,z2,z4,z5,z487]),(0,[z0,z1,z2,z879,z4,z6]),(0,[z7,z1,z2,z4,z216,z6]),(0,[z0,z1,z2,z4,z880,z6]),(0,[z0,z1,z66,z4,z5,z6]),(0,[z0,z1,z2,z881,z4,z6]),(0,[z1,z2,z4,z5,z420,z11]),(0,[z136,z1,z4,z120,z121,z6]),(0,[z1,z882,z2,z4,z5,z6])],[(0,[z0,z1,z2,z883,z4,z5]),(0,[z1,z2,z4,z791,z6,z8]),(0,[z183,z1,z2,z4,z5,z855])],[(0,[z1,z2,z4,z884,z6,z8]),(0,[z111,z219,z2,z4,z112,z6]),(0,[z506,z1,z247,z2,z5,z6])],[(0,[z0,z1,z2,z885,z5,z6]),(0,[z53,z1,z66,z4,z5,z8]),(0,[z268,z1,z2,z137,z6,z8]),(0,[z7,z240,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z886]),(0,[z887,z1,z2,z4,z5,z6]),(0,[z1,z2,z888,z4,z5,z6]),(0,[z0,z1,z2,z686,z43,z6]),(0,[z130,z0,z1,z2,z5,z11])],[(0,[z0,z1,z2,z4,z5,z103]),(0,[z471,z1,z2,z4,z5,z8]),(0,[z1,z2,z4,z741,z6,z8])],[(0,[z1,z2,z889,z4,z5,z6]),(0,[z890,z1,z2,z4,z5,z6])],[(0,[z0,z1,z891,z2,z5,z6]),(0,[z0,z1,z2,z892,z5,z6]),(0,[z0,z1,z291,z4,z5,z83]),(0,[z893,z1,z2,z4,z5,z6])],[(0,[z101,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z479,z5,z8]),(0,[z1,z2,z894,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z283]),(0,[z0,z1,z2,z4,z5,z895])],[(0,[z0,z1,z2,z4,z5,z896])],[(0,[z37,z1,z2,z312,z42,z6]),(0,[z188,z1,z2,z4,z5,z160]),(0,[z897,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z423,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z898,z5,z6]),(0,[z1,z2,z4,z5,z336,z8]),(0,[z194,z1,z2,z4,z350,z6]),(0,[z0,z1,z2,z195,z350,z6]),(0,[z0,z1,z2,z899,z4,z6]),(0,[z0,z1,z2,z900,z4,z6])],[(0,[z0,z1,z2,z4,z884,z6]),(0,[z1,z355,z2,z4,z5,z8]),(0,[z901,z1,z2,z4,z5,z6]),(0,[z1,z2,z902,z4,z5,z6]),(1,[z1,z2,z4,z5,z779]),(0,[z903,z1,z2,z4,z5,z6]),(0,[z904,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z905,z6]),(0,[z1,z2,z4,z5,z340,z8]),(1,[z1,z2,z4,z45,z8]),(0,[z7,z1,z2,z4,z906,z6]),(0,[z1,z355,z2,z403,z4,z5]),(0,[z1,z2,z137,z398,z4,z6])],[(0,[z59,z1,z224,z4,z5,z6]),(0,[z53,z1,z2,z4,z5,z8]),(0,[z907,z1,z2,z4,z5,z65]),(0,[z53,z0,z2,z4,z267,z262])],[(1,[z1,z2,z4,z784,z6]),(0,[z0,z1,z2,z908,z4,z6]),(0,[z0,z1,z2,z909,z5,z6]),(0,[z0,z1,z2,z370,z5,z6]),(0,[z423,z1,z2,z376,z4,z6])]],
   [[(0,[z1,z2,z4,z5,z8,z263])],[(0,[z1,z2,z816,z4,z5,z8]),(0,[z910,z1,z2,z4,z5,z6])],[(0,[z486,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z911,z6]),(0,[z0,z1,z912,z2,z5,z6]),(0,[z0,z624,z2,z23,z5,z6])],[(0,[z1,z2,z333,z41,z5,z6]),(0,[z1,z2,z354,z4,z5,z8]),(0,[z1,z2,z4,z270,z6,z8]),(0,[z1,z2,z913,z5,z6,z8])],[],[(0,[z221,z317,z2,z4,z5,z6]),(0,[z0,z1,z54,z198,z5,z6]),(0,[z0,z1,z12,z2,z833,z5])],[(0,[z0,z1,z2,z833,z63,z5])],[(0,[z0,z1,z346,z68,z5,z6]),(0,[z1,z2,z4,z5,z914,z6]),(0,[z1,z2,z398,z4,z43,z6])],[(0,[z0,z1,z915,z4,z5,z6]),(0,[z0,z1,z2,z916,z5,z6]),(0,[z0,z1,z13,z5,z455,z6])],[(0,[z37,z1,z2,z4,z214,z6]),(0,[z0,z1,z2,z4,z5,z917]),(0,[z1,z918,z2,z4,z5,z6])],[(0,[z0,z1,z919,z2,z4,z5])],[(0,[z7,z1,z2,z163,z4,z6]),(0,[z0,z1,z2,z38,z216,z6]),(0,[z53,z101,z2,z4,z5,z262]),(0,[z0,z1,z2,z4,z920,z6])],[(0,[z0,z1,z2,z333,z5,z11]),(0,[z194,z1,z2,z195,z5,z6]),(0,[z1,z2,z63,z117,z5,z11])],[(0,[z0,z91,z1,z313,z5,z6]),(0,[z0,z1,z17,z2,z406,z4])],[(0,[z7,z1,z2,z4,z267,z6]),(0,[z61,z1,z2,z4,z448,z6]),(0,[z0,z91,z1,z2,z5,z263])],[(0,[z293,z1,z2,z4,z5,z487]),(0,[z1,z2,z23,z5,z8,z11]),(0,[z7,z1,z2,z4,z921,z6])]],
   [[(0,[z360,z1,z2,z4,z5,z8]),(0,[z922,z1,z2,z67,z4,z5])],[(0,[z0,z1,z2,z312,z5,z546]),(0,[z1,z2,z4,z5,z6,z923]),(0,[z1,z2,z4,z45,z6,z8]),(0,[z1,z2,z382,z4,z5,z8]),(0,[z0,z1,z924,z2,z5,z6]),(0,[z111,z0,z2,z4,z112,z6]),(0,[z179,z2,z4,z5,z10,z420]),(0,[z0,z1,z925,z2,z5,z6])],[(0,[z0,z1,z2,z4,z5,z926]),(0,[z0,z1,z2,z927,z5,z6]),(0,[z151,z1,z2,z424,z5,z6]),(0,[z217,z1,z2,z424,z5,z6]),(0,[z380,z0,z30,z4,z5,z6]),(0,[z928,z1,z2,z4,z5,z6]),(0,[z1,z2,z184,z244,z4,z6])],[(0,[z0,z1,z2,z929,z4,z5]),(0,[z1,z2,z4,z5,z8,z687])],[(0,[z0,z1,z2,z4,z350,z6]),(0,[z0,z1,z2,z666,z43,z6]),(0,[z0,z1,z2,z4,z5,z930]),(0,[z0,z1,z615,z2,z43,z6])],[(0,[z1,z2,z4,z549,z5,z8]),(0,[z1,z2,z931,z4,z5,z6]),(0,[z0,z1,z2,z4,z98,z102])],[(0,[z0,z1,z932,z4,z5,z6])],[(0,[z37,z1,z2,z4,z374,z6]),(0,[z0,z149,z1,z355,z2,z4]),(0,[z933,z1,z2,z4,z5,z6]),(0,[z934,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z935,z5,z6]),(0,[z936,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z14,z8]),(0,[z937,z1,z2,z4,z5,z6]),(0,[z938,z1,z2,z4,z5,z6]),(0,[z0,z1,z939,z2,z5,z6]),(0,[z0,z1,z2,z754,z4,z98])],[(0,[z118,z1,z2,z4,z5,z152]),(0,[z1,z2,z4,z5,z65,z8]),(0,[z1,z2,z406,z4,z5,z8]),(0,[z1,z247,z2,z5,z6,z8]),(0,[z29,z7,z30,z4,z5,z6]),(0,[z0,z1,z838,z57,z5,z6])],[(0,[z124,z1,z2,z4,z5,z6]),(0,[z0,z1,z131,z2,z370,z5])],[(0,[z1,z2,z4,z5,z6,z940])],[(0,[z142,z47,z1,z2,z5,z6]),(0,[z1,z2,z4,z5,z6,z941])],[(0,[z0,z1,z2,z4,z942,z6]),(0,[z0,z1,z2,z184,z67,z4])],[(0,[z1,z575,z2,z4,z5,z8]),(0,[z37,z1,z2,z4,z193,z6]),(0,[z577,z1,z2,z4,z5,z8]),(0,[z1,z2,z4,z424,z5,z8]),(1,[z1,z2,z398,z43,z6])]],
   [[(0,[z1,z2,z4,z201,z5,z487]),(0,[z7,z1,z2,z312,z5,z6]),(0,[z7,z1,z17,z2,z18,z4])],[(0,[z293,z652,z2,z4,z5,z6]),(0,[z0,z1,z2,z943,z5,z6]),(0,[z1,z2,z4,z5,z6,z944]),(0,[z0,z1,z2,z4,z5,z945])],[],[(0,[z1,z2,z4,z201,z627,z6]),(0,[z21,z1,z2,z4,z544,z6]),(0,[z0,z1,z2,z4,z5,z946])],[(0,[z1,z2,z4,z5,z362,z8]),(0,[z221,z589,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z947,z6]),(0,[z948,z0,z1,z2,z4,z6]),(0,[z949,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z950,z6])],[(0,[z0,z1,z2,z951,z5,z6]),(0,[z151,z1,z2,z41,z266,z6]),(0,[z7,z1,z2,z198,z5,z6]),(0,[z0,z1,z2,z195,z5,z6]),(0,[z0,z1,z313,z4,z5,z6]),(0,[z0,z1,z2,z507,z5,z11])],[(0,[z1,z205,z4,z5,z465,z6]),(0,[z136,z1,z2,z4,z8,z102]),(0,[z0,z1,z2,z4,z270,z283]),(0,[z0,z2,z4,z817,z5,z6]),(0,[z0,z1,z952,z4,z5,z6]),(0,[z953,z1,z2,z4,z5,z6])],[(0,[z475,z1,z164,z4,z5,z6]),(0,[z0,z954,z1,z2,z5,z6]),(0,[z7,z1,z2,z4,z5,z362]),(0,[z0,z1,z2,z88,z5,z65])],[(0,[z1,z2,z244,z4,z5,z6]),(0,[z149,z1,z2,z4,z6,z8]),(0,[z1,z39,z4,z5,z6,z265])],[(0,[z596,z1,z2,z4,z5,z8]),(0,[z87,z328,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z270,z6]),(0,[z955,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z168,z11])],[(0,[z0,z1,z2,z4,z5,z956]),(0,[z0,z1,z2,z173,z43,z6]),(0,[z0,z1,z2,z90,z5,z283]),(0,[z957,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z813])],[(0,[z0,z1,z742,z4,z5,z6]),(0,[z366,z1,z2,z4,z5,z8]),(0,[z958,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z959,z4,z5])],[(0,[z0,z1,z2,z960,z5,z6]),(0,[z0,z1,z2,z41,z216,z6]),(0,[z37,z1,z2,z4,z42,z546]),(0,[z961,z1,z2,z4,z5,z6]),(0,[z962,z1,z2,z4,z5,z6])],[],[(0,[z1,z2,z4,z5,z8,z97]),(0,[z22,z0,z2,z90,z447,z6]),(0,[z0,z1,z2,z198,z45,z6])]],
   [[(0,[z0,z1,z2,z4,z963,z6]),(0,[z0,z91,z1,z2,z5,z283])],[(0,[z0,z1,z2,z4,z5,z964]),(0,[z0,z1,z2,z5,z280,z6]),(0,[z227,z1,z2,z211,z43,z6])],[(0,[z188,z1,z2,z4,z5,z546]),(0,[z53,z0,z54,z4,z5,z262])],[(0,[z194,z1,z2,z4,z448,z6]),(0,[z142,z1,z131,z2,z4,z5])],[(0,[z7,z1,z2,z4,z5,z189]),(0,[z1,z2,z67,z244,z4,z5]),(0,[z0,z1,z2,z62,z682,z5])],[(0,[z7,z73,z2,z23,z5,z6])],[(0,[z0,z1,z2,z965,z4,z6]),(0,[z506,z1,z2,z4,z98,z102])],[(0,[z221,z459,z2,z4,z5,z6]),(0,[z113,z1,z205,z2,z4,z6]),(0,[z1,z2,z4,z5,z6,z966]),(0,[z7,z1,z2,z4,z447,z6]),(0,[z219,z1,z2,z4,z9,z6]),(0,[z967,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z663,z5,z11])],[(0,[z0,z1,z2,z870,z4,z6]),(0,[z0,z1,z2,z4,z5,z968]),(0,[z0,z1,z2,z4,z5,z83])],[(0,[z0,z1,z2,z4,z5,z969]),(0,[z87,z1,z2,z4,z5,z362]),(0,[z59,z1,z164,z4,z5,z103]),(0,[z0,z1,z2,z4,z970,z6]),(0,[z971,z1,z2,z4,z5,z6])],[(1,[z1,z2,z4,z5,z855])],[(0,[z286,z1,z2,z4,z5,z8]),(0,[z1,z2,z480,z4,z5,z8]),(0,[z0,z1,z2,z198,z5,z262]),(0,[z0,z1,z2,z4,z972,z6]),(0,[z1,z17,z2,z18,z259,z4])],[],[(0,[z136,z1,z4,z121,z6,z8])],[(0,[z59,z1,z2,z4,z169,z6]),(0,[z0,z1,z54,z4,z5,z160]),(0,[z0,z1,z973,z4,z5,z6]),(0,[z1,z2,z4,z207,z40,z6])],[(0,[z514,z1,z2,z4,z5,z6]),(0,[z1,z2,z974,z4,z5,z6]),(0,[z0,z1,z2,z663,z43,z6])]],
   [[(0,[z59,z1,z164,z4,z5,z6]),(0,[z491,z1,z2,z4,z193,z6])],[(0,[z323,z1,z2,z4,z5,z8]),(0,[z1,z492,z2,z4,z5,z8]),(0,[z634,z1,z2,z4,z5,z8]),(0,[z1,z2,z4,z5,z495,z8]),(0,[z1,z246,z2,z4,z158,z8]),(0,[z1,z2,z398,z5,z43,z6]),(0,[z0,z1,z975,z4,z5,z6]),(0,[z0,z1,z2,z69,z5,z102])],[(0,[z7,z1,z54,z4,z5,z6]),(0,[z0,z1,z2,z976,z5,z6]),(0,[z1,z2,z977,z4,z5,z6]),(0,[z0,z1,z2,z376,z4,z6])],[(0,[z1,z231,z2,z4,z169,z6]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z0,z1,z979,z2,z5,z6]),(0,[z219,z1,z84,z2,z4,z6]),(0,[z183,z1,z2,z4,z112,z6])],[(0,[z0,z1,z461,z2,z62,z5])],[(0,[z0,z1,z2,z239,z9,z6]),(0,[z136,z0,z1,z2,z239,z6]),(0,[z1,z2,z137,z4,z8,z102]),(0,[z0,z1,z2,z980,z5,z6])],[(0,[z0,z1,z981,z4,z5,z6]),(0,[z1,z2,z164,z4,z5,z487]),(0,[z1,z2,z982,z4,z5,z6])],[(0,[z983,z1,z2,z4,z5,z6]),(0,[z0,z1,z984,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z985])],[(0,[z0,z1,z2,z4,z5,z986]),(0,[z0,z1,z2,z4,z5,z987]),(0,[z0,z1,z2,z4,z988,z6]),(0,[z0,z1,z2,z4,z989,z6])],[(0,[z990,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z2,z5,z400])],[(0,[z0,z1,z2,z4,z5,z991]),(0,[z110,z1,z2,z134,z5,z6]),(0,[z53,z1,z2,z4,z5,z966]),(0,[z1,z2,z69,z5,z6,z8]),(0,[z0,z149,z1,z2,z4,z6]),(0,[z1,z2,z4,z992,z5,z6]),(0,[z1,z2,z515,z398,z4,z5])],[(0,[z457,z1,z2,z4,z201,z6]),(0,[z0,z1,z993,z2,z4,z5]),(0,[z0,z1,z2,z211,z43,z6]),(0,[z994,z1,z2,z515,z4,z5])],[(0,[z0,z1,z2,z4,z995,z6]),(0,[z0,z1,z2,z4,z448,z6]),(0,[z1,z2,z4,z5,z83,z996]),(0,[z227,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z4,z5,z997])],[(0,[z1,z246,z2,z4,z207,z6])],[(0,[z0,z1,z2,z998,z4,z5]),(0,[z0,z1,z17,z2,z4,z553])],[(0,[z0,z1,z2,z4,z5,z999])]],
   [[(0,[z1,z1000,z2,z4,z5,z158]),(0,[z7,z1,z2,z4,z203,z6]),(0,[z1,z2,z4,z5,z65,z944]),(0,[z0,z179,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z5,z1001])],[(0,[z183,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z738,z6]),(0,[z1,z2,z4,z5,z45,z8]),(0,[z1,z2,z4,z5,z966,z8]),(0,[z1,z2,z4,z5,z8,z215]),(0,[z7,z1,z2,z515,z4,z5]),(0,[z22,z72,z2,z90,z5,z6]),(0,[z0,z1,z2,z4,z5,z1002]),(0,[z167,z1,z246,z2,z4,z6])],[(0,[z0,z589,z2,z4,z112,z6]),(0,[z1003,z1,z2,z4,z5,z6])],[(0,[z20,z1,z622,z4,z5,z6]),(0,[z0,z1,z2,z4,z1004,z6]),(0,[z1,z2,z4,z5,z784,z6]),(0,[z0,z1,z313,z4,z270,z6]),(0,[z0,z1,z1005,z4,z5,z6]),(0,[z0,z1,z2,z1006,z4,z5])],[(0,[z1,z2,z198,z5,z6,z8]),(0,[z1,z2,z398,z4,z5,z85])],[],[(0,[z0,z1,z2,z4,z1007,z6]),(0,[z1008,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1009]),(0,[z1,z2,z547,z38,z5,z6]),(0,[z0,z1,z313,z90,z5,z6]),(0,[z1010,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z24,z267,z6]),(0,[z595,z0,z1,z2,z5,z11]),(0,[z0,z1,z2,z490,z5,z11])],[(0,[z1,z2,z4,z5,z316,z8]),(0,[z550,z1,z2,z4,z5,z8]),(0,[z0,z1,z54,z4,z5,z262]),(0,[z53,z0,z2,z24,z5,z262]),(0,[z227,z1,z84,z2,z4,z6]),(0,[z1,z1011,z2,z4,z5,z6])],[(0,[z22,z426,z2,z90,z5,z6]),(0,[z1012,z1,z2,z4,z5,z6]),(0,[z1013,z1,z2,z4,z5,z6])],[(0,[z1014,z1,z2,z4,z5,z6])],[(0,[z733,z1,z2,z4,z5,z6]),(0,[z1015,z1,z2,z4,z5,z6]),(0,[z72,z1,z2,z4,z447,z6])],[(0,[z1,z2,z4,z5,z103,z8]),(0,[z0,z1,z2,z4,z5,z1016]),(0,[z1,z2,z4,z5,z383,z1017]),(0,[z53,z0,z2,z4,z45,z262]),(0,[z0,z1,z2,z657,z5,z11])],[(0,[z227,z1,z2,z4,z201,z6]),(0,[z1,z2,z4,z5,z1018,z6]),(0,[z0,z1,z2,z1019,z5,z6])],[(0,[z0,z1,z1020,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1021]),(0,[z7,z1,z2,z4,z5,z160]),(0,[z118,z1,z2,z4,z5,z160]),(0,[z0,z1,z2,z1022,z5,z6]),(0,[z0,z1,z2,z1023,z4,z6]),(0,[z1024,z1,z2,z4,z5,z6])],[(0,[z506,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1025,z6])]],
   [[(0,[z0,z1,z2,z4,z1026,z6])],[(0,[z1,z50,z2,z4,z5,z6]),(0,[z29,z0,z30,z88,z5,z6]),(0,[z1027,z1,z2,z4,z5,z263]),(0,[z1,z2,z211,z398,z43,z6])],[(0,[z0,z1,z2,z1028,z5,z6]),(0,[z7,z1,z2,z4,z5,z752]),(0,[z1,z2,z370,z403,z5,z6]),(0,[z0,z1,z2,z4,z1029,z5]),(0,[z0,z1,z313,z4,z5,z83])],[(0,[z1,z2,z4,z5,z8,z276]),(0,[z0,z159,z2,z4,z9,z6]),(0,[z235,z1,z33,z4,z5,z245]),(0,[z0,z1,z2,z4,z5,z85])],[],[(0,[z7,z1,z2,z4,z5,z386]),(0,[z1,z2,z4,z5,z6,z1017]),(0,[z1,z2,z4,z5,z1030,z6]),(0,[z0,z1,z2,z4,z1031,z6]),(0,[z0,z1,z13,z838,z5,z6])],[(0,[z21,z1,z2,z4,z174,z6]),(0,[z1,z2,z4,z1032,z5,z6]),(0,[z0,z1,z2,z4,z270,z83]),(0,[z0,z1,z4,z5,z930,z6])],[(0,[z37,z1,z2,z4,z419,z6]),(0,[z47,z1,z2,z5,z6,z8]),(0,[z7,z1,z2,z4,z168,z6])],[(0,[z0,z1,z2,z4,z45,z160]),(0,[z0,z1,z1033,z4,z5,z6])],[(0,[z0,z1,z12,z2,z62,z5])],[(0,[z0,z1,z2,z4,z266,z152]),(0,[z0,z1,z2,z4,z1034,z6]),(0,[z1,z2,z1035,z4,z5,z6])],[(0,[z0,z1,z355,z2,z4,z5]),(0,[z1,z2,z4,z5,z1036,z6]),(0,[z0,z1037,z1,z2,z4,z6]),(0,[z1,z2,z4,z5,z43,z779])],[(0,[z7,z1,z2,z4,z45,z6]),(0,[z1,z2,z1038,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z402]),(0,[z1,z2,z38,z239,z5,z6]),(0,[z1039,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1040,z4,z6]),(0,[z0,z1,z2,z1041,z5,z6]),(0,[z1042,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z1043,z5,z6])]],
   [[(0,[z1,z2,z742,z4,z5,z6])],[(0,[z0,z1,z355,z2,z153,z4]),(0,[z0,z1,z2,z1044,z4,z5]),(0,[z1045,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1046]),(0,[z541,z1,z2,z4,z5,z8]),(0,[z0,z187,z1,z57,z5,z6])],[(0,[z0,z1,z1047,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z192]),(0,[z1,z2,z63,z5,z8,z11]),(0,[z1048,z1,z2,z4,z5,z6]),(0,[z1049,z1,z2,z4,z5,z6])],[(0,[z167,z1,z2,z4,z5,z103]),(0,[z0,z1,z1050,z2,z4,z6]),(0,[z7,z1,z157,z2,z5,z6]),(0,[z1,z50,z2,z4,z5,z11])],[(0,[z0,z1,z2,z1051,z5,z6])],[(0,[z1,z2,z90,z5,z8,z11]),(0,[z0,z1,z2,z195,z448,z6]),(0,[z667,z0,z2,z4,z112,z6]),(0,[z0,z1,z2,z376,z63,z11])],[(0,[z0,z1,z2,z1052,z5,z6])],[(0,[z0,z1,z2,z4,z1053,z6]),(0,[z1,z4,z5,z465,z8,z245]),(0,[z0,z1,z2,z5,z280,z8]),(0,[z22,z0,z2,z817,z5,z6])],[(0,[z1,z2,z4,z191,z6,z8]),(0,[z0,z1,z2,z4,z1054,z6]),(0,[z7,z1,z2,z1055,z5,z6]),(0,[z7,z1,z2,z4,z5,z383])],[(0,[z0,z47,z1,z57,z5,z6])],[(0,[z167,z1,z2,z4,z5,z6]),(0,[z20,z1,z513,z4,z5,z6]),(0,[z37,z25,z1,z2,z4,z6]),(0,[z1,z2,z333,z5,z8,z11]),(0,[z1,z2,z4,z5,z8,z11]),(0,[z1,z2,z4,z5,z6,z996]),(0,[z0,z706,z2,z23,z5,z6])],[(0,[z0,z1,z1056,z2,z4,z5])],[(0,[z7,z1,z2,z4,z5,z557]),(0,[z1,z2,z4,z5,z139,z8]),(0,[z142,z1,z2,z370,z5,z6]),(0,[z0,z1,z2,z5,z280,z10])],[(0,[z161,z1,z2,z4,z5,z6]),(0,[z29,z0,z149,z30,z4,z6]),(0,[z0,z1,z2,z4,z5,z1057]),(0,[z0,z1,z2,z4,z43,z85])],[(0,[z0,z1,z2,z4,z5,z487]),(0,[z1,z2,z4,z201,z216,z6]),(0,[z1,z2,z41,z5,z216,z6]),(0,[z91,z1,z2,z5,z8,z11]),(0,[z0,z2,z786,z4,z5,z6]),(0,[z380,z0,z2,z90,z5,z6]),(0,[z0,z1058,z2,z4,z5,z6])]],
   [[(0,[z228,z1,z2,z4,z5,z8]),(0,[z151,z1,z2,z41,z5,z6]),(0,[z1,z84,z2,z4,z8,z102]),(0,[z1059,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z23,z5,z263]),(0,[z0,z1,z1060,z2,z4,z6])],[(0,[z0,z1,z2,z1061,z5,z6]),(0,[z0,z1,z2,z4,z5,z1062]),(0,[z227,z1,z2,z4,z216,z6]),(0,[z430,z1,z2,z41,z5,z6]),(0,[z0,z1,z2,z4,z1063,z6])],[(0,[z0,z1064,z2,z4,z5,z6]),(0,[z37,z1,z2,z4,z5,z487]),(0,[z1,z2,z95,z4,z8,z102]),(0,[z0,z128,z1,z131,z4,z5]),(0,[z0,z1,z2,z4,z1065,z6])],[(0,[z0,z1,z2,z4,z5,z1066])],[(0,[z0,z1,z2,z4,z266,z189]),(0,[z44,z1,z2,z4,z5,z8]),(0,[z61,z1,z2,z88,z5,z6]),(0,[z1,z2,z1067,z4,z5,z6])],[(0,[z326,z1,z2,z4,z5,z8]),(0,[z0,z1,z131,z54,z4,z5]),(0,[z0,z2,z817,z90,z5,z6]),(0,[z0,z1,z2,z4,z427,z102])],[(0,[z317,z1,z2,z4,z5,z362]),(0,[z1,z2,z476,z41,z5,z6]),(0,[z1,z2,z230,z69,z5,z6])],[(0,[z1,z2,z4,z41,z5,z487]),(1,[z1,z742,z4,z5,z6]),(0,[z0,z1,z2,z4,z1068,z6]),(0,[z136,z0,z1,z287,z4,z6]),(0,[z227,z1,z2,z4,z42,z6]),(0,[z1,z2,z178,z4,z5,z8]),(0,[z1069,z1,z2,z4,z5,z6])],[(0,[z1070,z1,z2,z4,z5,z6]),(0,[z0,z128,z1,z2,z198,z5]),(0,[z0,z1,z2,z4,z1071,z6])],[(0,[z0,z1,z2,z1072,z4,z5]),(0,[z0,z1,z2,z4,z5,z1073])],[(0,[z0,z141,z2,z4,z9,z6]),(0,[z1074,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1075,z5,z6])],[(0,[z317,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z4,z5,z1076]),(0,[z0,z1,z54,z24,z5,z6]),(0,[z1,z2,z4,z5,z6,z1077])],[(0,[z0,z1,z2,z405,z5,z11]),(0,[z1,z2,z4,z5,z1078,z6]),(0,[z1079,z1,z2,z4,z5,z6])],[(0,[z60,z231,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z169,z6]),(0,[z1,z2,z497,z41,z5,z6]),(0,[z1,z2,z200,z4,z5,z8]),(0,[z0,z1,z2,z4,z1080,z6]),(0,[z1,z2,z211,z302,z43,z6])],[(0,[z0,z1,z2,z4,z9,z192]),(0,[z29,z194,z30,z4,z5,z6]),(0,[z1081,z1,z2,z4,z5,z6]),(0,[z1,z1082,z2,z4,z5,z6])],[(0,[z327,z1,z4,z5,z465,z6]),(0,[z1,z2,z208,z4,z5,z8]),(0,[z1083,z1,z2,z4,z5,z6]),(0,[z0,z1,z54,z4,z45,z6]),(0,[z0,z1,z2,z838,z5,z6]),(0,[z136,z227,z1,z2,z4,z6]),(0,[z514,z1,z2,z211,z43,z6]),(0,[z0,z1,z17,z2,z69,z6])]],
   [[(0,[z1,z2,z4,z230,z5,z6]),(0,[z128,z1,z4,z5,z158,z8]),(0,[z155,z1,z224,z4,z5,z6]),(0,[z1084,z1,z2,z4,z5,z6]),(0,[z111,z0,z2,z584,z4,z6]),(0,[z250,z1,z2,z4,z267,z6]),(0,[z522,z0,z2,z4,z5,z262])],[(0,[z0,z1,z2,z4,z5,z1085]),(0,[z0,z1,z2,z4,z868,z6]),(0,[z1086,z1,z2,z4,z5,z6])],[(0,[z111,z2,z4,z112,z6,z8])],[(0,[z0,z1087,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z203,z263]),(0,[z1088,z1,z2,z4,z5,z6])],[(0,[z59,z1,z3,z4,z5,z6]),(0,[z426,z1,z2,z4,z5,z283]),(0,[z1089,z1,z2,z4,z5,z6])],[(0,[z293,z328,z2,z4,z5,z6]),(0,[z0,z268,z1,z2,z137,z6])],[(0,[z7,z1,z2,z4,z5,z546]),(0,[z0,z1,z68,z838,z5,z6])],[(0,[z1,z2,z4,z267,z6,z8]),(0,[z1090,z1,z2,z4,z5,z6]),(0,[z1091,z1,z2,z4,z5,z6]),(0,[z1092,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1093,z6]),(0,[z426,z1,z291,z4,z5,z6]),(0,[z0,z1,z12,z2,z344,z5])],[(0,[z0,z1,z2,z239,z201,z6]),(0,[z1,z2,z4,z9,z8,z102]),(0,[z1,z2,z694,z4,z5,z8]),(0,[z907,z1,z2,z4,z5,z6]),(0,[z1094,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z4,z336])],[(0,[z0,z1,z84,z2,z4,z192]),(0,[z1,z2,z4,z5,z8,z570]),(0,[z0,z1,z2,z4,z1095,z6]),(0,[z0,z47,z1,z131,z2,z5]),(0,[z1,z2,z4,z5,z6,z1096])],[(0,[z0,z1,z2,z4,z216,z6]),(0,[z1,z2,z698,z4,z5,z8]),(0,[z1042,z1,z355,z2,z4,z5]),(0,[z0,z1,z2,z4,z743,z6]),(0,[z1,z2,z1097,z4,z5,z6]),(1,[z0,z1,z2,z833,z5])],[],[(0,[z37,z1,z2,z4,z674,z6]),(0,[z59,z1,z2,z239,z5,z6]),(0,[z250,z1,z2,z4,z5,z160])],[(0,[z113,z1,z2,z4,z6,z8]),(0,[z1,z2,z4,z5,z8,z428])],[(0,[z1,z2,z4,z5,z6,z1098]),(0,[z0,z1,z2,z4,z5,z1099])]],
   [[(0,[z7,z1,z247,z2,z5,z6]),(0,[z0,z1,z291,z4,z447,z6]),(0,[z1100,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1101,z6]),(0,[z1,z2,z4,z5,z6,z1102]),(0,[z1,z2,z4,z5,z6,z1103]),(0,[z0,z1,z2,z1104,z5,z6])],[(0,[z1,z231,z2,z239,z5,z6]),(0,[z281,z231,z2,z4,z5,z6]),(0,[z0,z1,z2,z1105,z5,z6]),(0,[z1106,z1,z2,z4,z5,z6])],[(0,[z0,z1107,z2,z4,z5,z6]),(0,[z59,z1,z2,z4,z5,z192]),(0,[z1,z2,z4,z5,z8,z437])],[(0,[z0,z1,z2,z4,z1108,z6]),(0,[z0,z1,z2,z1109,z4,z6]),(0,[z0,z1,z1110,z2,z4,z6])],[(0,[z293,z1,z2,z4,z5,z362]),(0,[z110,z1,z2,z524,z5,z6]),(0,[z670,z1,z2,z4,z5,z8]),(0,[z7,z1,z2,z4,z5,z263]),(0,[z1,z2,z4,z5,z6,z1111])],[(0,[z293,z231,z2,z4,z5,z6]),(0,[z7,z91,z1,z57,z5,z6]),(0,[z1,z2,z4,z5,z6,z1112]),(0,[z1,z2,z4,z5,z283,z745]),(0,[z0,z1,z2,z297,z43,z6]),(0,[z1113,z1,z2,z4,z5,z6]),(0,[z1,z2,z67,z1114,z4,z5]),(0,[z1,z12,z2,z62,z538,z5])],[(0,[z0,z1,z2,z1115,z5,z6]),(0,[z1,z33,z4,z5,z8,z245]),(0,[z0,z1,z2,z1116,z4,z6]),(0,[z250,z1,z2,z198,z5,z6]),(0,[z1117,z1,z2,z4,z5,z6]),(0,[z514,z1,z2,z4,z5,z85]),(0,[z1118,z1,z2,z4,z5,z6])],[(0,[z1,z231,z2,z4,z5,z192]),(0,[z1,z1119,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z534,z11])],[(0,[z1,z2,z4,z5,z296,z8]),(0,[z194,z1,z2,z88,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1120]),(0,[z1,z2,z908,z4,z6,z8]),(0,[z136,z0,z1,z258,z4,z6])],[(0,[z1,z2,z4,z5,z487,z8]),(0,[z59,z1,z742,z4,z5,z6]),(0,[z1,z2,z18,z4,z5,z8]),(0,[z7,z1,z2,z24,z5,z6]),(0,[z53,z0,z2,z4,z5,z357]),(0,[z1121,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1122,z5,z6]),(0,[z0,z1123,z1,z2,z5,z6]),(0,[z0,z1,z2,z515,z211,z43]),(0,[z0,z1,z2,z18,z754,z4])],[(0,[z0,z1,z1124,z2,z4,z5]),(0,[z1,z2,z4,z5,z8,z611]),(0,[z0,z1,z2,z4,z686,z102])],[(0,[z0,z1,z66,z4,z267,z6]),(0,[z0,z1,z2,z4,z40,z6])],[(0,[z113,z0,z1,z2,z4,z6]),(0,[z580,z577,z2,z4,z5,z6]),(0,[z0,z1,z2,z1125,z5,z6]),(0,[z1,z2,z4,z5,z1126,z6]),(0,[z0,z1,z33,z2,z198,z5])]],
   [[(0,[z37,z1,z223,z2,z4,z6]),(0,[z0,z1,z2,z312,z5,z192]),(0,[z0,z149,z1,z2,z370,z6]),(0,[z0,z1,z2,z4,z1127,z6]),(0,[z1049,z1,z2,z4,z5,z83]),(0,[z1,z2,z515,z982,z4,z5]),(0,[z0,z268,z1,z2,z1104,z6])],[(0,[z21,z1,z2,z4,z784,z6]),(0,[z341,z1,z2,z4,z5,z8]),(0,[z1,z2,z4,z5,z8,z463]),(0,[z7,z47,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z1128]),(0,[z167,z1,z2,z5,z280,z6])],[(0,[z113,z221,z1,z2,z4,z6]),(0,[z1129,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z525]),(0,[z1130,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z211,z43,z85])],[(0,[z0,z1,z1131,z2,z4,z5])],[(0,[z7,z1,z2,z4,z5,z65]),(0,[z1132,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z69,z5,z6])],[(0,[z1,z1133,z2,z4,z5,z6]),(0,[z1,z2,z4,z201,z5,z362]),(0,[z1,z329,z2,z4,z5,z8]),(0,[z0,z1,z2,z1134,z4,z6]),(0,[z179,z1,z2,z4,z5,z420]),(0,[z0,z1135,z2,z4,z5,z6])],[(0,[z1,z2,z4,z828,z6,z8]),(0,[z7,z1,z2,z67,z4,z5]),(0,[z0,z1,z2,z4,z1136,z6]),(0,[z0,z1,z2,z754,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1137]),(0,[z0,z1,z2,z5,z43,z85])],[(0,[z113,z1,z231,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1138])],[(0,[z59,z113,z1,z164,z4,z6]),(0,[z59,z1,z163,z164,z4,z6]),(0,[z0,z1,z2,z153,z4,z6])],[(0,[z1,z2,z4,z266,z6,z8])],[(0,[z142,z1,z2,z4,z5,z6]),(0,[z20,z1,z742,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1139]),(0,[z1,z2,z344,z4,z5,z8]),(0,[z53,z1,z2,z4,z267,z8]),(0,[z183,z1,z2,z4,z9,z6]),(0,[z0,z1,z2,z1104,z43,z6]),(0,[z1,z2,z117,z4,z168,z6])],[(0,[z0,z1,z2,z4,z1140,z6])],[],[(0,[z1,z133,z2,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z1141]),(0,[z1,z2,z4,z5,z351,z8]),(0,[z1,z2,z18,z4,z8,z102]),(0,[z111,z0,z2,z4,z743,z6]),(0,[z1,z2,z1114,z4,z5,z6]),(0,[z1142,z1,z2,z4,z5,z6]),(0,[z1,z247,z2,z230,z5,z6])]],
   [[(0,[z0,z1,z4,z838,z5,z6]),(0,[z0,z1143,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z872,z6]),(0,[z1,z1144,z2,z4,z5,z6])],[(0,[z1,z2,z4,z169,z6,z8]),(0,[z1,z2,z4,z5,z8,z504]),(0,[z1,z157,z2,z5,z6,z8])],[(0,[z1,z2,z376,z4,z6,z8]),(0,[z167,z1,z2,z4,z5,z8]),(0,[z0,z1,z2,z88,z5,z6])],[(0,[z1,z2,z4,z201,z5,z189]),(0,[z0,z1,z2,z239,z42,z6]),(0,[z0,z1,z2,z4,z5,z1145]),(0,[z29,z0,z30,z4,z5,z383]),(0,[z0,z786,z30,z4,z5,z6]),(0,[z0,z1,z131,z4,z5,z245]),(0,[z0,z1,z1146,z2,z4,z5]),(0,[z1147,z1,z2,z4,z5,z6])],[(0,[z59,z1,z164,z4,z5,z487]),(0,[z250,z1,z54,z4,z5,z6])],[(0,[z37,z1,z2,z4,z617,z6]),(0,[z0,z1,z2,z4,z5,z1148]),(0,[z0,z1,z2,z4,z5,z1149]),(0,[z0,z1,z2,z4,z5,z152]),(0,[z0,z1,z66,z198,z5,z6]),(0,[z0,z1,z13,z68,z203,z6])],[(0,[z37,z1,z2,z239,z42,z6])],[(0,[z59,z1,z210,z4,z5,z6]),(0,[z7,z1,z131,z2,z4,z5]),(0,[z0,z1,z2,z4,z1150,z6]),(0,[z1,z2,z4,z5,z6,z1151])],[(0,[z142,z149,z1,z2,z4,z6]),(0,[z136,z0,z1,z381,z4,z6]),(0,[z0,z1,z2,z4,z69,z102])],[(0,[z1,z291,z4,z5,z6,z8]),(0,[z1027,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z63,z5,z11])],[(0,[z0,z1,z2,z4,z853,z6]),(0,[z0,z2,z4,z5,z10,z719])],[(0,[z576,z37,z1,z2,z4,z6]),(0,[z7,z1,z291,z4,z5,z6]),(0,[z0,z1,z17,z2,z18,z4])],[(1,[z1,z2,z41,z216,z6]),(0,[z37,z1,z2,z4,z42,z192]),(0,[z240,z2,z4,z9,z6,z8]),(0,[z0,z1,z2,z1152,z5,z6])],[(0,[z317,z810,z2,z4,z5,z6]),(0,[z151,z1,z2,z239,z5,z6]),(0,[z1,z2,z1153,z4,z5,z6]),(0,[z1,z2,z4,z5,z420,z245])],[(0,[z0,z1,z2,z63,z168,z11])],[(0,[z0,z1,z2,z4,z5,z1154]),(0,[z1,z2,z4,z5,z1155,z6])]],
   [[(0,[z235,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z8,z85]),(0,[z1,z2,z4,z5,z193,z8]),(0,[z0,z232,z2,z4,z9,z6])],[(0,[z1,z2,z4,z5,z192,z8]),(0,[z1,z313,z4,z5,z6,z8]),(0,[z1,z2,z4,z43,z8,z102]),(0,[z0,z1,z355,z2,z370,z5]),(0,[z1156,z1,z2,z4,z5,z6])],[(0,[z115,z2,z4,z5,z6,z27]),(0,[z29,z142,z30,z4,z5,z6]),(0,[z1157,z1,z2,z4,z5,z6])],[(0,[z151,z1,z2,z4,z5,z192]),(0,[z53,z1,z2,z198,z5,z8]),(0,[z0,z1,z2,z1158,z4,z5]),(0,[z0,z240,z2,z4,z743,z6]),(0,[z0,z240,z212,z2,z4,z6])],[(1,[z1,z2,z5,z280,z8]),(0,[z1,z2,z4,z5,z400,z8]),(0,[z111,z7,z2,z4,z112,z6]),(0,[z1,z2,z4,z5,z1159,z6])],[(0,[z1,z2,z1160,z4,z5,z6])],[(0,[z1,z13,z68,z5,z6,z8]),(0,[z0,z1,z2,z4,z1161,z6])],[(0,[z1,z2,z4,z5,z6,z420]),(0,[z7,z1,z13,z68,z5,z6]),(0,[z136,z183,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1162,z6]),(0,[z286,z1,z2,z4,z5,z189]),(0,[z1163,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1164,z6]),(0,[z1,z2,z236,z4,z5,z8])],[(0,[z426,z1,z2,z4,z5,z6]),(0,[z59,z113,z1,z2,z4,z6]),(0,[z1,z177,z2,z547,z5,z6]),(0,[z1,z295,z2,z95,z4,z6]),(0,[z0,z1,z12,z2,z5,z180])],[(0,[z0,z1,z2,z88,z350,z6])],[(0,[z221,z317,z2,z4,z5,z362]),(0,[z0,z2,z4,z5,z719,z262]),(0,[z1,z13,z68,z244,z5,z6]),(0,[z0,z1,z2,z18,z4,z668])],[(0,[z1,z2,z403,z4,z5,z6]),(0,[z1,z2,z62,z816,z4,z5]),(0,[z1165,z1,z2,z4,z5,z6])],[(0,[z59,z1,z287,z4,z5,z6]),(0,[z1,z2,z67,z4,z5,z8]),(0,[z1,z2,z4,z5,z427,z8]),(0,[z7,z1,z2,z184,z4,z6]),(0,[z531,z0,z2,z4,z112,z6]),(0,[z0,z1,z2,z137,z338,z6])],[(0,[z0,z1,z2,z4,z5,z189]),(0,[z0,z1,z2,z4,z447,z283]),(0,[z0,z2,z4,z743,z5,z6]),(0,[z0,z1,z1166,z2,z5,z6])]],
   [[(0,[z110,z1,z2,z4,z5,z487]),(0,[z1,z2,z18,z4,z230,z5])],[(0,[z0,z1,z2,z1167,z5,z6]),(0,[z37,z1,z2,z4,z216,z6]),(0,[z0,z240,z2,z4,z9,z6]),(0,[z0,z1,z246,z2,z280,z6]),(0,[z1,z2,z259,z62,z4,z5])],[(0,[z1,z1168,z2,z4,z5,z6])],[(0,[z7,z1,z33,z4,z5,z245]),(0,[z7,z1,z246,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z1169]),(0,[z0,z1,z2,z5,z1170,z6])],[(0,[z0,z1,z1171,z4,z5,z6]),(0,[z1,z2,z4,z5,z302,z6]),(0,[z0,z1,z1172,z2,z4,z6]),(0,[z0,z1,z2,z23,z5,z283])],[(0,[z145,z231,z2,z4,z5,z6]),(0,[z1,z2,z4,z41,z216,z6]),(0,[z1,z2,z95,z4,z201,z6]),(0,[z1,z2,z184,z4,z6,z8]),(0,[z1,z2,z4,z5,z8,z591]),(0,[z61,z1,z2,z4,z5,z383])],[(0,[z1,z2,z4,z41,z5,z189]),(0,[z0,z1,z2,z137,z578,z6])],[(0,[z1,z2,z1173,z4,z5,z6]),(0,[z0,z1,z4,z5,z872,z6])],[(0,[z1,z30,z4,z5,z8,z245]),(0,[z142,z1,z355,z2,z4,z5]),(0,[z444,z0,z1,z4,z121,z6]),(0,[z0,z1,z2,z4,z371,z102])],[(0,[z0,z1,z28,z2,z18,z4]),(0,[z53,z1,z2,z4,z5,z420]),(0,[z1174,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1175,z6])],[(0,[z7,z1,z2,z4,z191,z6]),(0,[z0,z1,z2,z4,z906,z6]),(0,[z0,z1,z84,z661,z4,z6]),(0,[z0,z268,z1,z2,z5,z85]),(0,[z1,z2,z4,z230,z5,z102])],[(0,[z293,z810,z2,z4,z5,z6]),(0,[z7,z1,z2,z239,z5,z6]),(0,[z188,z1,z2,z4,z5,z6]),(0,[z922,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1176,z6]),(0,[z1,z301,z2,z4,z5,z8]),(0,[z29,z0,z370,z30,z5,z6]),(0,[z0,z1,z1177,z4,z5,z6]),(0,[z1178,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1179]),(0,[z1,z2,z4,z5,z158,z8]),(0,[z1,z2,z4,z5,z280,z8]),(0,[z250,z1,z2,z4,z45,z6]),(0,[z1,z2,z4,z5,z6,z1180])],[(0,[z1,z2,z4,z5,z455,z8]),(0,[z1,z715,z2,z5,z6,z8]),(0,[z72,z1,z291,z4,z5,z6]),(0,[z0,z1,z33,z480,z4,z5])]],
   [[(0,[z1,z2,z4,z1181,z5,z6]),(0,[z0,z268,z1,z2,z472,z6]),(0,[z1,z2,z4,z644,z6,z290]),(0,[z219,z1,z2,z4,z5,z824])],[(0,[z1,z2,z547,z5,z8,z11]),(0,[z0,z1,z2,z4,z5,z1182])],[(0,[z0,z550,z2,z4,z9,z6]),(0,[z53,z0,z66,z4,z5,z262]),(0,[z1183,z1,z2,z4,z5,z6])],[(0,[z22,z2,z90,z5,z6,z8]),(0,[z1,z2,z4,z1184,z5,z6])],[(0,[z0,z1,z2,z4,z1185,z6]),(0,[z1186,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z266,z6]),(0,[z0,z1,z2,z4,z40,z8]),(0,[z1187,z1,z2,z4,z5,z6]),(0,[z1188,z1,z2,z4,z5,z6])],[(0,[z1,z2,z1189,z4,z5,z6]),(0,[z1190,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1191,z6]),(0,[z1192,z1,z2,z4,z5,z6])],[(0,[z810,z231,z2,z4,z5,z6]),(0,[z1,z2,z239,z5,z42,z6]),(0,[z1,z1193,z2,z4,z5,z6]),(0,[z0,z1,z2,z69,z6,z102])],[(0,[z0,z1,z2,z1194,z4,z5]),(0,[z101,z1,z2,z4,z267,z6]),(0,[z0,z1,z2,z24,z45,z6]),(0,[z1,z33,z50,z4,z5,z245])],[(0,[z0,z1,z2,z4,z5,z1195]),(0,[z0,z1,z2,z163,z4,z6]),(0,[z1,z2,z4,z5,z6,z752])],[(0,[z1,z2,z4,z5,z152,z8]),(0,[z0,z1,z33,z4,z5,z930])],[(0,[z0,z1,z2,z4,z644,z102]),(0,[z114,z1,z513,z4,z5,z6]),(0,[z1,z2,z5,z207,z280,z6])],[(0,[z221,z140,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1196,z6]),(0,[z110,z1,z2,z252,z5,z6]),(0,[z0,z1,z2,z4,z267,z6]),(0,[z0,z1,z2,z515,z4,z5])],[(0,[z0,z1,z2,z712,z5,z6]),(0,[z0,z1,z2,z4,z921,z6]),(0,[z136,z219,z1,z2,z4,z6]),(0,[z53,z0,z2,z4,z5,z262]),(0,[z1,z2,z4,z5,z1197,z6])],[(0,[z7,z1,z2,z4,z5,z316]),(0,[z0,z1,z13,z384,z5,z6]),(0,[z1,z2,z4,z1198,z5,z6])],[(0,[z29,z0,z30,z4,z5,z65]),(0,[z0,z1,z2,z4,z5,z1199])]],
   [[(0,[z1,z1200,z2,z4,z5,z6])],[(0,[z136,z0,z1,z2,z4,z192]),(0,[z0,z1,z2,z1201,z4,z5])],[(0,[z7,z1,z66,z4,z5,z6]),(0,[z22,z0,z2,z90,z5,z283])],[(0,[z0,z1,z2,z4,z5,z1202]),(0,[z1,z2,z4,z5,z283,z8]),(0,[z1,z2,z1203,z4,z5,z6]),(0,[z136,z0,z1,z422,z4,z6])],[(0,[z0,z1,z2,z5,z1204,z6]),(0,[z426,z1,z313,z4,z5,z6])],[(0,[z29,z30,z4,z5,z6,z8]),(0,[z1205,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z103]),(0,[z1,z2,z4,z5,z8,z102]),(0,[z22,z0,z291,z90,z5,z6]),(0,[z1,z2,z4,z5,z6,z779])],[(0,[z151,z1,z2,z41,z5,z152]),(0,[z0,z128,z1,z2,z5,z280])],[(0,[z0,z1,z2,z4,z1206,z6]),(0,[z0,z1,z80,z4,z5,z383]),(0,[z1207,z1,z2,z4,z5,z6]),(0,[z426,z1,z2,z4,z270,z6]),(0,[z1,z2,z62,z117,z4,z5])],[(0,[z1,z810,z2,z4,z5,z6]),(0,[z136,z183,z1,z4,z121,z6]),(0,[z1,z1208,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z283]),(0,[z0,z1,z2,z1209,z5,z6]),(0,[z0,z73,z2,z289,z5,z6])],[(0,[z0,z1,z2,z4,z1210,z6]),(0,[z0,z1,z2,z4,z5,z1211]),(0,[z1,z2,z4,z5,z6,z1212]),(0,[z194,z1,z2,z4,z5,z383]),(0,[z1,z2,z4,z5,z6,z824]),(0,[z183,z1,z84,z2,z4,z6])],[(0,[z1,z2,z527,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z1213]),(0,[z0,z1,z313,z4,z447,z6]),(0,[z0,z257,z2,z4,z5,z10])],[(0,[z0,z1,z1214,z2,z4,z5]),(0,[z1,z2,z538,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1215]),(0,[z0,z1,z2,z62,z833,z5])],[(0,[z0,z1,z2,z1216,z4,z6]),(0,[z0,z1,z2,z312,z5,z6]),(0,[z227,z1,z2,z38,z5,z6]),(0,[z0,z1,z2,z1217,z5,z6])],[(0,[z0,z1,z2,z1218,z5,z6]),(0,[z1,z2,z4,z5,z534,z8]),(0,[z0,z1,z2,z913,z5,z6]),(0,[z101,z1,z2,z198,z5,z6]),(0,[z360,z0,z2,z4,z5,z262])]],
   [[(0,[z20,z1,z2,z4,z5,z487]),(0,[z1,z535,z2,z4,z5,z8]),(0,[z1,z2,z4,z1219,z5,z6])],[(0,[z7,z1,z2,z370,z5,z6])],[(0,[z1,z131,z2,z403,z4,z5]),(0,[z0,z1,z2,z1220,z5,z6]),(0,[z0,z1,z313,z23,z5,z6]),(0,[z0,z1,z2,z234,z5,z11]),(0,[z0,z1,z2,z4,z168,z6]),(0,[z423,z1,z2,z4,z168,z6])],[(0,[z7,z1,z2,z4,z5,z306]),(0,[z0,z1,z2,z88,z448,z6]),(0,[z0,z1,z2,z5,z1221,z6]),(0,[z0,z1,z2,z198,z5,z6]),(0,[z0,z1,z2,z4,z5,z1222])],[(0,[z1,z2,z24,z5,z6,z8]),(0,[z634,z1,z2,z4,z174,z6]),(0,[z1,z2,z4,z5,z1223,z6]),(0,[z1,z2,z62,z4,z5,z420]),(0,[z1224,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z362]),(0,[z0,z1,z2,z4,z1225,z6]),(1,[z0,z2,z4,z743,z6]),(0,[z1,z2,z4,z1226,z5,z6]),(0,[z1,z2,z4,z1227,z5,z6])],[(0,[z0,z1,z2,z4,z1228,z6]),(0,[z432,z1,z2,z4,z5,z8]),(0,[z21,z1,z2,z433,z4,z6]),(0,[z1,z2,z4,z553,z5,z8])],[(0,[z1,z2,z4,z5,z8,z695]),(0,[z401,z1,z2,z4,z5,z8]),(0,[z426,z1,z2,z4,z5,z83]),(0,[z0,z1,z2,z4,z1229,z5])],[(0,[z0,z1,z2,z4,z5,z1230]),(0,[z37,z1,z2,z4,z5,z362]),(0,[z7,z1,z2,z4,z5,z264]),(0,[z1231,z1,z2,z4,z5,z6])],[(0,[z1,z2,z405,z4,z5,z8]),(0,[z1232,z1,z2,z4,z5,z6])],[(0,[z1,z2,z333,z5,z6,z123]),(0,[z0,z1,z13,z68,z5,z263])],[(0,[z1,z2,z4,z407,z5,z8]),(0,[z1,z2,z565,z4,z5,z8]),(0,[z0,z1,z2,z4,z5,z1233]),(0,[z0,z1,z2,z4,z5,z1234]),(0,[z1235,z1,z2,z4,z5,z6]),(0,[z1236,z0,z1,z2,z4,z6]),(0,[z0,z651,z1,z2,z137,z6]),(0,[z0,z91,z1,z16,z5,z6]),(0,[z124,z1,z2,z4,z203,z6])],[(0,[z0,z1,z2,z371,z5,z11])],[(0,[z0,z1,z2,z1237,z5,z6]),(0,[z1,z2,z4,z41,z5,z362]),(0,[z1,z2,z4,z5,z567,z8]),(0,[z1238,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z280,z40,z6]),(0,[z0,z1,z496,z2,z5,z11]),(0,[z0,z1,z2,z18,z69,z5])],[(0,[z0,z1,z1239,z4,z5,z6])],[(0,[z1,z2,z164,z4,z5,z362]),(1,[z1,z2,z239,z42,z6]),(0,[z0,z1,z2,z4,z447,z83]),(0,[z0,z1,z157,z2,z5,z6])]],
   [[(0,[z221,z810,z2,z4,z5,z6]),(0,[z0,z1,z2,z1240,z4,z6]),(0,[z151,z1,z2,z41,z216,z6]),(0,[z0,z1,z2,z239,z5,z546]),(0,[z1,z2,z4,z5,z6,z1241]),(0,[z0,z1,z2,z153,z370,z6]),(0,[z0,z1,z2,z1242,z5,z6]),(0,[z1,z1243,z2,z4,z5,z6]),(0,[z1,z2,z1244,z4,z5,z6])],[(0,[z1,z2,z4,z5,z8,z32]),(0,[z0,z1,z4,z5,z1245,z6]),(0,[z0,z1,z2,z184,z4,z263]),(0,[z1,z2,z4,z5,z263,z1241])],[(0,[z0,z1,z2,z4,z5,z1246]),(0,[z61,z1,z2,z4,z5,z65])],[(0,[z0,z1,z2,z4,z1247,z6]),(0,[z0,z73,z2,z23,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1248]),(0,[z0,z1,z2,z4,z5,z383]),(0,[z797,z1,z131,z2,z4,z5]),(0,[z0,z1,z2,z4,z1249,z6]),(0,[z0,z1,z2,z4,z5,z1250]),(0,[z0,z1,z2,z4,z1251,z6])],[(0,[z37,z1,z2,z4,z5,z189]),(0,[z179,z2,z4,z5,z10,z8]),(0,[z1,z2,z4,z40,z6,z8]),(0,[z29,z61,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z447,z6]),(0,[z0,z1,z2,z4,z168,z11]),(0,[z1,z2,z1252,z4,z5,z6])],[(0,[z1,z2,z4,z436,z5,z8]),(0,[z1,z54,z4,z5,z6,z8]),(0,[z1,z2,z4,z5,z8,z55]),(0,[z7,z1,z2,z4,z350,z6])],[(0,[z1,z1000,z2,z4,z5,z6]),(0,[z0,z179,z2,z4,z5,z27]),(0,[z7,z1,z2,z4,z98,z102]),(0,[z1253,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1254,z4,z5,z6]),(0,[z0,z1,z2,z757,z4,z6]),(0,[z1,z2,z173,z4,z42,z6]),(0,[z1,z2,z244,z4,z203,z6]),(0,[z1255,z1,z2,z4,z5,z6])],[(0,[z1,z39,z4,z5,z8,z245]),(0,[z1,z2,z4,z158,z40,z8]),(0,[z0,z1,z2,z1256,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1257]),(0,[z37,z1,z2,z4,z42,z6]),(0,[z0,z47,z149,z1,z2,z6]),(0,[z0,z1,z2,z62,z352,z5])],[(0,[z0,z1,z2,z1258,z5,z6]),(0,[z484,z1,z2,z4,z42,z6]),(0,[z21,z1,z2,z239,z5,z6]),(0,[z0,z416,z1,z2,z137,z6])],[(0,[z0,z1,z30,z4,z5,z383]),(0,[z0,z1,z2,z4,z5,z1259]),(0,[z101,z1,z54,z4,z5,z6])],[(0,[z1,z131,z1119,z2,z4,z5]),(0,[z1260,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z313,z5,z6]),(0,[z1,z2,z1261,z4,z5,z6]),(0,[z250,z1,z2,z24,z5,z6])],[(0,[z29,z0,z131,z30,z4,z5]),(0,[z72,z1,z2,z4,z5,z283]),(0,[z0,z1,z13,z2,z5,z263]),(0,[z1,z2,z4,z5,z121,z855]),(0,[z0,z1,z33,z2,z5,z280]),(0,[z167,z1,z2,z4,z40,z6])],[(0,[z113,z7,z1,z2,z4,z6]),(0,[z0,z1,z2,z1262,z4,z6]),(0,[z1,z66,z4,z5,z6,z8]),(0,[z1,z2,z4,z5,z6,z832]),(0,[z0,z1,z2,z1104,z211,z6])]],
   [[(0,[z0,z1,z2,z1263,z5,z6]),(0,[z1,z2,z612,z4,z5,z8]),(0,[z799,z0,z1,z2,z4,z6]),(0,[z0,z1,z54,z4,z5,z6]),(0,[z0,z1,z2,z4,z1264,z6]),(0,[z136,z0,z1,z4,z872,z6])],[(0,[z221,z577,z2,z4,z5,z6]),(0,[z21,z1,z2,z4,z5,z192]),(0,[z0,z1,z2,z4,z479,z102])],[(0,[z1,z2,z1265,z4,z5,z6]),(0,[z1266,z1,z2,z4,z5,z6]),(0,[z0,z425,z80,z4,z5,z6])],[(0,[z1,z2,z4,z447,z6,z8]),(0,[z53,z1,z54,z4,z5,z8]),(0,[z188,z1,z2,z4,z5,z8]),(0,[z0,z1,z1267,z4,z5,z6]),(0,[z0,z1,z1268,z2,z4,z5]),(0,[z0,z1,z2,z67,z4,z203]),(0,[z0,z1,z2,z43,z11,z102])],[(0,[z0,z1,z2,z1269,z5,z6]),(0,[z1,z2,z4,z5,z1270,z6]),(0,[z1271,z1,z2,z4,z5,z6]),(0,[z1272,z1,z2,z4,z5,z6])],[(0,[z1,z205,z4,z5,z503,z6]),(0,[z7,z1,z2,z4,z5,z192]),(0,[z0,z1,z1273,z2,z4,z5]),(0,[z1274,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z168,z6,z11])],[(0,[z0,z47,z1,z313,z5,z6]),(0,[z1275,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1276,z6]),(0,[z7,z1,z2,z195,z5,z6]),(0,[z7,z1,z313,z4,z5,z6]),(0,[z1277,z1,z2,z4,z5,z6])],[(0,[z1,z12,z2,z62,z5,z8]),(0,[z142,z1,z2,z153,z4,z6])],[(0,[z1,z2,z4,z239,z42,z6]),(0,[z0,z1,z13,z67,z68,z5])],[(0,[z20,z1,z205,z4,z5,z6]),(0,[z0,z1,z2,z4,z1278,z6]),(0,[z0,z1,z1279,z2,z5,z6]),(0,[z1280,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1281,z4,z5,z6]),(0,[z1,z205,z2,z4,z169,z6]),(0,[z0,z1,z1282,z4,z5,z6]),(0,[z29,z0,z786,z4,z5,z6]),(0,[z0,z47,z1,z355,z2,z5])],[(0,[z1,z2,z4,z5,z6,z1283]),(0,[z1284,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1285,z4,z5])],[(0,[z0,z1,z2,z1286,z4,z6]),(0,[z1,z2,z4,z5,z207,z6]),(0,[z0,z1,z2,z4,z350,z383]),(0,[z0,z1,z12,z2,z168,z6])],[(0,[z1,z246,z2,z4,z6,z8]),(0,[z0,z1,z2,z4,z203,z6])],[(0,[z221,z1,z2,z4,z169,z6]),(0,[z110,z1,z2,z4,z216,z6]),(0,[z0,z1,z2,z4,z5,z1287]),(0,[z0,z1,z2,z5,z280,z160]),(0,[z1288,z1,z2,z4,z5,z6]),(0,[z1,z2,z1289,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1290]),(0,[z1,z2,z4,z1291,z5,z6]),(0,[z0,z1,z562,z2,z62,z5]),(0,[z514,z1,z2,z515,z4,z5])],[(0,[z0,z1,z2,z4,z5,z546]),(0,[z1,z2,z4,z5,z8,z156])],[(0,[z221,z317,z2,z4,z169,z6]),(0,[z0,z1,z1292,z2,z5,z6]),(0,[z268,z1,z2,z398,z5,z6])],[(0,[z7,z1,z2,z878,z4,z6]),(0,[z7,z1,z2,z5,z280,z6]),(0,[z0,z1,z2,z1293,z4,z6]),(0,[z1294,z1,z2,z4,z5,z6]),(0,[z227,z1,z2,z4,z5,z779]),(0,[z0,z1,z2,z754,z4,z6])],[(0,[z1,z2,z4,z201,z784,z6]),(0,[z1,z2,z4,z5,z6,z855])],[(0,[z0,z1,z2,z1295,z4,z6]),(0,[z22,z0,z334,z2,z5,z6]),(0,[z0,z91,z1,z838,z5,z6])],[(0,[z1,z2,z1296,z4,z5,z6]),(0,[z0,z1,z2,z1297,z4,z5]),(0,[z0,z1,z2,z137,z1104,z6])],[(0,[z1,z2,z4,z746,z5,z6]),(0,[z194,z1,z2,z4,z5,z65])],[(0,[z1,z2,z4,z350,z6,z8]),(0,[z22,z0,z2,z90,z5,z6]),(0,[z0,z1,z334,z57,z5,z6])],[(0,[z1,z2,z4,z5,z752,z8]),(0,[z1298,z1,z2,z4,z5,z6]),(0,[z53,z0,z2,z4,z5,z719])],[(0,[z1,z2,z4,z5,z1299,z6]),(0,[z0,z1300,z1,z2,z5,z6]),(0,[z994,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1104,z4,z6])],[(0,[z1,z2,z4,z216,z6,z8]),(0,[z1,z2,z1301,z4,z5,z6]),(0,[z805,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1302,z6]),(0,[z0,z1,z66,z24,z5,z6])],[(0,[z1303,z1,z2,z4,z5,z6]),(0,[z0,z1304,z1,z2,z4,z6])],[(0,[z1,z2,z515,z4,z5,z8]),(0,[z0,z1,z2,z4,z1305,z6])],[(0,[z1,z2,z239,z5,z6,z8]),(0,[z0,z1,z2,z195,z5,z383]),(0,[z0,z1,z2,z4,z1306,z6]),(0,[z136,z0,z1,z4,z121,z6])],[(0,[z1307,z1,z2,z4,z5,z6]),(0,[z0,z1,z66,z4,z45,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1308,z6]),(0,[z118,z1,z2,z4,z5,z6]),(0,[z1,z2,z41,z42,z43,z6]),(0,[z0,z1,z2,z4,z5,z752]),(0,[z7,z1,z2,z898,z5,z6]),(0,[z1,z2,z4,z5,z160,z752]),(0,[z0,z47,z1,z13,z5,z6]),(0,[z0,z1,z13,z2,z5,z283])],[(1,[z1,z2,z4,z40,z8]),(0,[z0,z1,z2,z1309,z5,z6]),(0,[z0,z91,z1,z57,z5,z6]),(0,[z1310,z1,z2,z4,z5,z6]),(0,[z1,z50,z2,z4,z5,z245]),(0,[z0,z1,z2,z1311,z5,z6])],[(0,[z1,z2,z4,z644,z8,z102]),(0,[z1312,z1,z2,z4,z5,z6]),(0,[z1,z1168,z355,z2,z4,z5]),(0,[z0,z1,z1313,z4,z5,z6]),(0,[z0,z1,z2,z1314,z5,z6])],[],[(0,[z1,z2,z712,z41,z5,z6]),(0,[z1,z131,z2,z4,z5,z8]),(0,[z1,z2,z4,z112,z8,z102]),(0,[z7,z1,z2,z376,z4,z6]),(0,[z1,z2,z4,z5,z6,z1315])],[(0,[z0,z1,z2,z4,z5,z1316]),(0,[z91,z1,z57,z5,z6,z8]),(0,[z29,z403,z30,z4,z5,z6]),(0,[z0,z73,z2,z817,z5,z6])],[(0,[z0,z1,z1317,z4,z5,z6]),(0,[z101,z1,z2,z4,z45,z6]),(0,[z0,z1,z4,z5,z930,z245]),(0,[z1,z2,z4,z5,z6,z1318]),(0,[z1319,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1320,z6]),(0,[z0,z1,z2,z4,z5,z1321]),(0,[z0,z1,z2,z4,z1322,z6])],[(0,[z1,z2,z4,z5,z8,z245]),(0,[z1,z2,z1323,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1324])],[(1,[z1,z2,z712,z5,z6]),(0,[z53,z1,z2,z24,z5,z8]),(0,[z0,z1,z2,z4,z5,z1325]),(0,[z0,z1,z2,z5,z280,z262])],[(0,[z0,z1,z2,z4,z5,z1326]),(0,[z1,z2,z4,z201,z86,z6]),(0,[z0,z1,z2,z198,z5,z8]),(0,[z1,z2,z1327,z4,z5,z6]),(0,[z0,z1,z2,z4,z45,z6])],[(0,[z47,z1,z2,z403,z5,z6]),(0,[z72,z1,z313,z4,z5,z6]),(0,[z0,z1,z2,z1328,z4,z5]),(0,[z227,z1,z2,z4,z5,z814])],[(0,[z0,z810,z2,z4,z5,z6]),(0,[z7,z149,z1,z2,z4,z6]),(0,[z0,z47,z1,z2,z5,z6]),(0,[z1329,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z1330,z5,z6])],[(0,[z53,z1,z2,z4,z45,z8]),(0,[z0,z1,z2,z817,z5,z6])],[(0,[z110,z1,z2,z712,z5,z6]),(0,[z0,z1,z2,z412,z43,z6]),(0,[z179,z2,z4,z5,z27,z8]),(0,[z1,z17,z2,z18,z4,z8])],[(0,[z58,z1,z2,z41,z5,z6]),(0,[z1,z2,z4,z1331,z5,z6]),(0,[z0,z1,z2,z198,z5,z10]),(0,[z0,z1,z2,z5,z168,z11])]],
   [[(0,[z0,z1,z2,z4,z5,z65])],[(0,[z1332,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z43,z6,z85])],[(0,[z0,z1,z2,z4,z5,z1333]),(0,[z0,z1,z2,z4,z5,z824]),(0,[z0,z1,z2,z67,z4,z5]),(0,[z0,z1334,z2,z4,z5,z6])],[(0,[z21,z1,z2,z4,z105,z6])],[(0,[z0,z1,z2,z1335,z5,z6]),(0,[z151,z1,z2,z41,z5,z189]),(0,[z1336,z1,z2,z4,z5,z6]),(0,[z1,z2,z153,z403,z4,z6])],[(0,[z0,z1,z2,z4,z216,z152]),(0,[z0,z703,z2,z4,z5,z10]),(0,[z0,z1,z247,z2,z98,z102])],[(0,[z87,z1,z2,z4,z5,z8]),(0,[z1,z2,z88,z5,z6,z8])],[(0,[z0,z1,z2,z1055,z5,z6]),(0,[z1337,z1,z2,z4,z5,z6]),(0,[z1,z2,z1338,z4,z5,z6]),(0,[z0,z1,z2,z4,z1339,z6])],[(0,[z111,z1,z2,z4,z5,z824])],[],[(0,[z0,z1,z2,z1340,z5,z6])],[(0,[z0,z1,z2,z1341,z5,z6]),(0,[z1,z2,z4,z5,z1342,z6]),(0,[z0,z2,z4,z5,z6,z719]),(0,[z0,z128,z1,z701,z4,z5]),(0,[z0,z1,z2,z62,z4,z168])],[(0,[z0,z128,z1,z54,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1343]),(0,[z0,z1,z2,z1344,z4,z6])],[(0,[z1,z2,z370,z5,z6,z8]),(0,[z1,z1000,z2,z4,z5,z8]),(0,[z1,z50,z2,z62,z4,z5])],[(0,[z0,z1,z2,z4,z5,z719]),(1,[z0,z1,z2,z1104,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 501).take 504) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1005).take 324) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1329)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [501, 504, 324] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 139).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 139).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 273).take 125).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 398).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [139, 134, 125, 114] = true :=
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

end PEqualNP.Outside.L_meta_38555

theorem PEqualNP.Outside.L_meta_38555 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008372392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008372392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38555.solve