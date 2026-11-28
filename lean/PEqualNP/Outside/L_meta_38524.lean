import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38524

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
  Nat.testBit (4008373472 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x81045671190e31bc#64 ++ 0xfb4cfef13b1e73fc#64 : BitVec 128),
   (0xc01130174060d455#64 ++ 0xffb3313fc4e3fc7f#64 : BitVec 128),
   (0x00c2c180af030a8a#64 ++ 0xb9c3c1c1ff038f8f#64 : BitVec 128),
   (0x02ec01ea06b40f60#64 ++ 0x7ffc01fe07fc0ff0#64 : BitVec 128),
   (0x04fbea0007dbe000#64 ++ 0xf6fffe0007fff000#64 : BitVec 128),
   (0x08ffbdfdf0000000#64 ++ 0xecfffffff8000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x00c2c180af030a8a 0xb9c3c1c1ff038f8f

def z1 : W := mkw 0x02ec01ea06b40f60 0x7ffc01fe07fc0ff0

def z2 : W := mkw 0x04fbe80007d3c000 0xb4f3c00007e38000

def z3 : W := mkw 0x04fbea0007dbe000 0xf6fffe0007fff000

def z4 : W := mkw 0x08ffbdfdf0000000 0xecfffffff8000000

def z5 : W := mkw 0x81045671190e31bc 0xfb4cfef13b1e73fc

def z6 : W := mkw 0xc01130174060d455 0xffb3313fc4e3fc7f

def z7 : W := mkw 0x00e8000006900000 0x76fc000007fc0000

def z8 : W := mkw 0x08ffbdfdf6900000 0xfefffffffffc0000

def z9 : W := mkw 0x4000000640200441 0x0000010ec0000c03

def z10 : W := mkw 0x00c2c180af030a8a 0xb0c3c0c03f038380

def z11 : W := mkw 0x0011301540000000 0xecb3313fc0000000

def z12 : W := mkw 0x81004200090e31bc 0x13000000031e73fc

def z13 : W := mkw 0x0000400009020088 0x8000c0013802000c

def z14 : W := mkw 0xc01130174060d455 0x0db3013fc4e18c7f

def z15 : W := mkw 0x04f92a0006d8e000 0x76fc3e0007fc7000

def z16 : W := mkw 0x04eacb80af9b2a8a 0x004ccec03b1c0380

def z17 : W := mkw 0x04fbeb80afdbea8a 0xffffffc1ffffff8f

def z18 : W := mkw 0x02ec01ea06b40f60 0x0db001fe04e00ff0

def z19 : W := mkw 0x0000000000000000 0xb9830101c4038c0f

def z20 : W := mkw 0x81045671190e31bc 0xfbcffff1ff1fffff

def z21 : W := mkw 0xc8ffbdfff060d455 0xeefffffff8e07070

def z22 : W := mkw 0xc1157677596ef5fd 0xffffffffffffffff

def z23 : W := mkw 0x8004107100041134 0xfb4c30f1031e73fc

def z24 : W := mkw 0x08ffbdfdf0000000 0x0cb301fff8000000

def z25 : W := mkw 0xc1153677506cf575 0x463c3e3e00fc7070

def z26 : W := mkw 0xc000101740201455 0xb983013fc4038c7f

def z27 : W := mkw 0x0000400009020088 0xb940c0c13b02038c

def z28 : W := mkw 0xc01130174060d455 0x4630303e00e07070

def z29 : W := mkw 0x0002c000af030a8a 0x9103c001ff038f8f

def z30 : W := mkw 0x00c2c182af230eca 0xfff3c1ffffe38fff

def z31 : W := mkw 0x8513fe11194bf09c 0x8003fe013803f00c

def z32 : W := mkw 0xc1041477582415fd 0x090001fff8000fff

def z33 : W := mkw 0x0004006000040120 0x420c0030001c0070

def z34 : W := mkw 0x04396a0007dbe000 0x563c3e0007fff000

def z35 : W := mkw 0x00c28180a0000000 0xa8c3c1c1f8000000

def z36 : W := mkw 0x083d3c7d50000000 0x443c3e3e00000000

def z37 : W := mkw 0xc0d3f197ef63dedf 0xfff3f1ffffe3ffff

def z38 : W := mkw 0x00fba80000000000 0xe4fffe0000000000

def z39 : W := mkw 0x080415fdf0000000 0x080001fff8000000

def z40 : W := mkw 0x04eaca00079b2000 0x004cce00031c0000

def z41 : W := mkw 0xc4fbfa1747fbf455 0xffffff3fc7fffc7f

def z42 : W := mkw 0x0400420007dbe000 0xf24cfe0007fff000

def z43 : W := mkw 0x85fbea000fdff1bc 0xf7fffe0007fff3fc

def z44 : W := mkw 0x04280a0000982000 0x000c0e00001c0000

def z45 : W := mkw 0x00c28180a6000a00 0xb9c3c1c1ff000f80

def z46 : W := mkw 0x0200000206b40f60 0x1300000007fc0ff0

def z47 : W := mkw 0xc200000206f4df75 0x1300000007ffffff

def z48 : W := mkw 0x0004147110000000 0xe84cfef138000000

def z49 : W := mkw 0xc00000020060d455 0x1300000004e3fc7f

def z50 : W := mkw 0x08ee8de8b0000000 0x004ccec038000000

def z51 : W := mkw 0x08fffdfdff030a8a 0xfdffffffff038f8f

def z52 : W := mkw 0x810415f1b8041bbe 0x090001f1f8000fff

def z53 : W := mkw 0x89fffffdf90e31bc 0xfffffffffb1e73fc

def z54 : W := mkw 0x0cfffffdffdbea8a 0xffffffffffffff8f

def z55 : W := mkw 0xc4fbfb97effbfedf 0xffffffffffffffff

def z56 : W := mkw 0xc0117217416af455 0xffffff3fc7fffc7f

def z57 : W := mkw 0x0000000200200440 0x7fb0013e04e00c70

def z58 : W := mkw 0x04392a0000d8e000 0x463c3e0000fc7000

def z59 : W := mkw 0x0004006000040120 0x090000f0000003f0

def z60 : W := mkw 0x81ec57f9190e31bc 0xfffcffff3b1e73fc

def z61 : W := mkw 0x00c28180a6010a02 0xa8c3c1c1fc018c03

def z62 : W := mkw 0x02ec01ea06b40f60 0x467c00fe03fc03f0

def z63 : W := mkw 0x80005211010a3014 0xfb4cfe31031e707c

def z64 : W := mkw 0x020401ea00240f60 0x090001fe00000ff0

def z65 : W := mkw 0x00ec006006940120 0x7ffc00f007fc03f0

def z66 : W := mkw 0x02ec01ea06b00e40 0x6cfc01fe04e00c00

def z67 : W := mkw 0x8106d671b90f31be 0xfb4ffef1fb1ff3ff

def z68 : W := mkw 0x81c6d6711f0f31bc 0xfbcffef13f1ff3fc

def z69 : W := mkw 0x81041671100c3134 0x420c3e30001c7070

def z70 : W := mkw 0x81c6d7f1bf0f3bbe 0xfbcffff1ff1fffff

def z71 : W := mkw 0x00c2c200070b2000 0xf2cffe00071ff000

def z72 : W := mkw 0x0affbdfff6b40f60 0xfffffffffffc0ff0

def z73 : W := mkw 0x0813bc15f0000000 0x8003fe01f8000000

def z74 : W := mkw 0x00c28180ae010a8a 0x098301c1fc018f8f

def z75 : W := mkw 0x810457f1b90e3bbe 0xfb4cfff1fb1e7fff

def z76 : W := mkw 0x0000000000000000 0x0000000000000000

def z77 : W := mkw 0x01044660190e21a8 0x004ccec03b1c0380

def z78 : W := mkw 0x0000000000040120 0x13000000031c03f0

def z79 : W := mkw 0x801130110040d014 0xffb3303104e3f07c

def z80 : W := mkw 0x04fba80006d1c000 0x04b3000004e18000

def z81 : W := mkw 0x81041471180411bc 0x090000f1380003fc

def z82 : W := mkw 0x0000000000000000 0xb90000010002000c

def z83 : W := mkw 0xc0fd31ff4060d455 0xffff31ffc4e3fc7f

def z84 : W := mkw 0x0400420007dbe000 0x1200000007fff000

def z85 : W := mkw 0x02ec01ea06b40f60 0x094c01fe031c0ff0

def z86 : W := mkw 0x001120000040c000 0xf6b3300004e3f000

def z87 : W := mkw 0x08ffbdfdf040c000 0xfefffffffce3f000

def z88 : W := mkw 0x00000000a800008a 0x00000001f800000f

def z89 : W := mkw 0xc2fd31ff46f4df75 0x7ffc31fe07fc7ff0

def z90 : W := mkw 0x063d2a6a00fce560 0x463c3e3e00fc7070

def z91 : W := mkw 0x00ec15f910000000 0xecfcffff38000000

def z92 : W := mkw 0x0c3d3e7d50d8e000 0x463c3e3e00fc7000

def z93 : W := mkw 0x022c006a00b40560 0x463c003e00fc0070

def z94 : W := mkw 0x81005611190a309c 0x8000fe013802700c

def z95 : W := mkw 0x00c2c00007030000 0xb0c3c00007038000

def z96 : W := mkw 0x0400000006d1c000 0x0000000004e18000

def z97 : W := mkw 0x02e8018a06b00e40 0x7fb0013e04e00c70

def z98 : W := mkw 0x0000000000000000 0xb083000004038000

def z99 : W := mkw 0x08ffbc7d50000000 0xe4fffe3e00000000

def z100 : W := mkw 0x08ffbdfdf0000000 0x447cfefe38000000

def z101 : W := mkw 0x00ffa9e800000000 0xecfffffe00000000

def z102 : W := mkw 0xc1117617596af4dd 0xffb3ff3ffce3fc7f

def z103 : W := mkw 0x81005611190a309c 0xfb00fe313802707c

def z104 : W := mkw 0x0cfffffdf7dbe000 0xfefffffffffff000

def z105 : W := mkw 0xc8ffbdfff060d455 0xfffffffffce3fc7f

def z106 : W := mkw 0x00004200010a2000 0xf24cfe00031e7000

def z107 : W := mkw 0x85fffe711fdff1bc 0xfffffef13ffff3fc

def z108 : W := mkw 0x401120064060c441 0x04b3010ec4e18c03

def z109 : W := mkw 0x0817bc75f0000000 0xe84ffef1f8000000

def z110 : W := mkw 0x022c006a06b40f60 0x573c003e07fc0ff0

def z111 : W := mkw 0x04fbaa0000d8e000 0xe6fffe0000fc7000

def z112 : W := mkw 0x08fffdfdf9020088 0xfdfffffffb02038c

def z113 : W := mkw 0x0004147110040120 0xfb4cfef13b1c03f0

def z114 : W := mkw 0x08ffbdfdf0040120 0xfffffffffb1c03f0

def z115 : W := mkw 0xc8ffbdfdf040d015 0xecfffffff803f00f

def z116 : W := mkw 0x04fffe7117dbe000 0xfefffef13ffff000

def z117 : W := mkw 0x0cffefe8b7dbe000 0xf6fffec03ffff000

def z118 : W := mkw 0x04fba980a6d1ca02 0x04b30100c4e18c03

def z119 : W := mkw 0x02ec01e806940b20 0x004c00c0031c0380

def z120 : W := mkw 0x01044660190e21a8 0xb94ccec13b1e038c

def z121 : W := mkw 0x0004006000040120 0x7b4c00f0031c03f0

def z122 : W := mkw 0x02e8018a06b00e40 0x04b0010e04e00c00

def z123 : W := mkw 0xc1004202096ef5fd 0x1300000007ffffff

def z124 : W := mkw 0x0002c00001030000 0x8003c00000038000

def z125 : W := mkw 0x0004147110000000 0x400c3e3000000000

def z126 : W := mkw 0x04fbea000fdbe088 0xfffffec13ffff38c

def z127 : W := mkw 0x08fba98ce0000000 0xacf3c1cff8000000

def z128 : W := mkw 0x810042000f0f3bbe 0x13000000071fffff

def z129 : W := mkw 0x06ffebea07ffef60 0xfffffffe07fffff0

def z130 : W := mkw 0x83ec57fb1fbe3ffc 0xfffcffff3ffe7ffc

def z131 : W := mkw 0x830042020fbe3ffc 0x1300000007fe7ffc

def z132 : W := mkw 0xc400420207fbf455 0x1300000007fffc7f

def z133 : W := mkw 0x0228000a00b00440 0x0430000e00e00000

def z134 : W := mkw 0x0000000008000a8a 0x0100000000000f8f

def z135 : W := mkw 0x00eac180af930a8a 0xffffc1c1ffff8f8f

def z136 : W := mkw 0xc01130154040d015 0xf6b33001c4e3f00f

def z137 : W := mkw 0x04fba80006d1c000 0x76ff000007fd8000

def z138 : W := mkw 0x000040000f030a8a 0xb940c0c13f038f8f

def z139 : W := mkw 0x000040000f030a8a 0x1100000007038f8f

def z140 : W := mkw 0x0413ea00014be000 0x8003fe000003f000

def z141 : W := mkw 0x0813bc15f0000000 0xecb3ff3ff8000000

def z142 : W := mkw 0x8000101100001014 0xfb0030310002707c

def z143 : W := mkw 0x0000400009020088 0xb9c3c1c1ff038f8f

def z144 : W := mkw 0x00000180a0000a02 0x00000100c0000c03

def z145 : W := mkw 0x00ec01e806000a00 0x7dfc01fe07000f80

def z146 : W := mkw 0x08fba98ce6010a02 0x04b3010ec4018c03

def z147 : W := mkw 0xc0d3b197e661de57 0xffb3313fc4e3fc7f

def z148 : W := mkw 0x08fffdfdff030a8a 0xecfffffffb000380

def z149 : W := mkw 0x81041471180411bc 0xe94cfef1380003fc

def z150 : W := mkw 0x04fbeb80a7dbea02 0xf6ffff00c7fffc03

def z151 : W := mkw 0x08fba98ce0000000 0x04b3010ec0000000

def z152 : W := mkw 0xc00010174060d455 0x1b00013fc4e3fc7f

def z153 : W := mkw 0x00fbb81540000000 0xecffff3fc0000000

def z154 : W := mkw 0xc01130154040d015 0x80033001c003f00f

def z155 : W := mkw 0x0804147d50000000 0x0000003e00000000

def z156 : W := mkw 0x08ffbdfdf0000000 0x804ffec1f8000000

def z157 : W := mkw 0xc20411ff40241f75 0x090001ffc0000fff

def z158 : W := mkw 0x04004200079b2000 0x00000000031c0000

def z159 : W := mkw 0x04112a000048e000 0x00003e0000007000

def z160 : W := mkw 0x00000180a8000a8a 0x090001c1f8000f8f

def z161 : W := mkw 0x0413ea0007dbe000 0x9203fe0007fff000

def z162 : W := mkw 0x00ec01e800000000 0x6cfc01fe00000000

def z163 : W := mkw 0x08ffadecf0000000 0x04ffcfcef8000000

def z164 : W := mkw 0xc01130174060d455 0x8903313fc003fc7f

def z165 : W := mkw 0x08fbbd9df0000000 0x84b3ff0ff8000000

def z166 : W := mkw 0x81000000080411bc 0x01000000000003fc

def z167 : W := mkw 0x09eecfe8b90e21a8 0x004ccec03b1c0380

def z168 : W := mkw 0xc8fffdffff63dedf 0xffffffffffe3ffff

def z169 : W := mkw 0x00c28180a6010a02 0x00830100c4018c03

def z170 : W := mkw 0x02ee81eaa6b50f62 0x7fff01fec7fd8ff3

def z171 : W := mkw 0x02e8018806900a00 0x0000000000000000

def z172 : W := mkw 0x00c2c180af030a8a 0x39c0c1c03f000f80

def z173 : W := mkw 0xc01130154040d015 0x0000300000007000

def z174 : W := mkw 0x00c2c180af030a8a 0x0040c0c03b000380

def z175 : W := mkw 0xc0113197e860dedf 0xffb331fffce3ffff

def z176 : W := mkw 0x02eec1e8af970baa 0xb9cfc1c1ff1f8f8f

def z177 : W := mkw 0x00fba80000000000 0x04b3000000000000

def z178 : W := mkw 0x81045671190e31bc 0xc20cfe31381e707c

def z179 : W := mkw 0x0affbdfff0b40560 0xeefffffff8fc0070

def z180 : W := mkw 0x00000180a8000a8a 0x000000c038000380

def z181 : W := mkw 0x00004180af030a8a 0x190001c1ff038f8f

def z182 : W := mkw 0x88ffbdfdf0001014 0xfffffffff802707c

def z183 : W := mkw 0x8104147110041134 0x0000003000000070

def z184 : W := mkw 0x81005611190e31bc 0x9300fe013b1e73fc

def z185 : W := mkw 0x81041671180c31bc 0x4b0c3ef1381c73fc

def z186 : W := mkw 0x022c006a00b40560 0x7f7c00fe03fc03f0

def z187 : W := mkw 0x0000400001020000 0xb040c00003020000

def z188 : W := mkw 0x890457fdf90e31bc 0xfb4cfffffb1e73fc

def z189 : W := mkw 0xc00000020060d455 0x0200000000e07070

def z190 : W := mkw 0x08ffbdfdf6010a02 0xecfffffffc018c03

def z191 : W := mkw 0x81c2d791bf0b3a9e 0xb9c3ffc1ff03ff8f

def z192 : W := mkw 0x893d3e7d500c3134 0x463c3e3e001c7070

def z193 : W := mkw 0x89fffffdf90a309c 0xecfffffff802700c

def z194 : W := mkw 0xc000101740201455 0x0000003e00000070

def z195 : W := mkw 0xc000101540001015 0x00000001c000000f

def z196 : W := mkw 0x04ffea6007dfe120 0xfffffef007fff3f0

def z197 : W := mkw 0x01044660190e21a8 0xf24cfec03b1e7380

def z198 : W := mkw 0x84fbfa1107dbf014 0xfffffe3107fff07c

def z199 : W := mkw 0x08ec15fdf0000000 0x6cfc01fff8000000

def z200 : W := mkw 0x00116200014ae000 0xf6fffe0007fff000

def z201 : W := mkw 0x830457fb192e3ffc 0xfb4cffff3b1e7ffc

def z202 : W := mkw 0x00ec01e806900000 0x7efc01fe07fc0000

def z203 : W := mkw 0x001130154040c000 0xfeb3313fc4e3f000

def z204 : W := mkw 0x0200000206b40f60 0x7fb0013e07fc0ff0

def z205 : W := mkw 0x02eec1eaafb70fea 0xffffc1ffffff8fff

def z206 : W := mkw 0x02ec01ea06b40f60 0x46bc013e04fc0c70

def z207 : W := mkw 0x0efffffff7ffef60 0xfffffffffffffff0

def z208 : W := mkw 0x8913fe15f90a309c 0x8003fe01f802700c

def z209 : W := mkw 0x0011301540000000 0xfdb3313fc4038c0f

def z210 : W := mkw 0x0011301540000000 0x4430303e00000000

def z211 : W := mkw 0xc1153677506cf575 0xffbf3f3fc4fffc7f

def z212 : W := mkw 0x00044260010e2120 0xfb4cfef0031e73f0

def z213 : W := mkw 0x83eed7fbbfbf3ffe 0xffffffffffffffff

def z214 : W := mkw 0x00c0018206200e40 0x7ff001fe07e00ff0

def z215 : W := mkw 0x81157675590e31bc 0xfffffffffb1e73fc

def z216 : W := mkw 0x00c0018006000a00 0x0080010004000c00

def z217 : W := mkw 0x04fbea0007dbe000 0xffffff01c7fffc0f

def z218 : W := mkw 0x02fd21ea06f4cf60 0xffff31fe07fffff0

def z219 : W := mkw 0x02ec01e806940b20 0x7b4c00f0031c03f0

def z220 : W := mkw 0x040042000fdbea8a 0x1300000007ffff8f

def z221 : W := mkw 0x08ffbdfdf8000a8a 0xedfffffff8000f8f

def z222 : W := mkw 0x0013a80000000000 0x8003fe0000000000

def z223 : W := mkw 0x830415fb18241ffc 0x090001ff38000ffc

def z224 : W := mkw 0xc1117217496ef5fd 0xffb3313fc7ffffff

def z225 : W := mkw 0x00c0018006000a00 0x004000c003000380

def z226 : W := mkw 0x00c6c1e0af070baa 0xfbcfc1f1ff1f8fff

def z227 : W := mkw 0x00c0018006000a00 0xb9c301c1c7038f8f

def z228 : W := mkw 0x00fd31fd40000000 0xecff31ffc0000000

def z229 : W := mkw 0x0cffbdfdf6d1c000 0xecfffffffce18000

def z230 : W := mkw 0x00e8000206b00440 0x7ffc013e07fc0c70

def z231 : W := mkw 0x09fffffdf90e21a8 0xecfffffffb1c0380

def z232 : W := mkw 0x02eac18aafb30eca 0xbdf3c1cfffe38f8f

def z233 : W := mkw 0x04ffebe807dbe000 0xfefffffe07fff000

def z234 : W := mkw 0x00c0018006000a00 0x39c001c007000f80

def z235 : W := mkw 0x04fbeb8007dbea00 0xffffffc007ffff80

def z236 : W := mkw 0x06ffebeaafffefea 0xffffffffffffffff

def z237 : W := mkw 0x04fbea00afdbe08a 0xf6fffe01fffff00f

def z238 : W := mkw 0x00c28180a0000000 0x0040c0c038000000

def z239 : W := mkw 0x01c6c7e0bf0f2baa 0x004ccec03b1c0380

def z240 : W := mkw 0x0000000000000000 0x7b00003000000070

def z241 : W := mkw 0x0413ea00a94be08a 0x8003fe01f803f00f

def z242 : W := mkw 0xc2fd31ff46f4df75 0xffff31ffc7ffffff

def z243 : W := mkw 0x001120000040c000 0xffb33101c4e3fc0f

def z244 : W := mkw 0x001120000040c000 0x4630300000e07000

def z245 : W := mkw 0x02ee81eaa6b40f60 0xffffc1fffffc0ff0

def z246 : W := mkw 0x08fbbc15f0000000 0xe4fffe01f8000000

def z247 : W := mkw 0x00c2c180af030a8a 0xb940c0c13b02038c

def z248 : W := mkw 0x83ec57f91f9e3bbc 0xfb4cfef13b1e73fc

def z249 : W := mkw 0xc4393a1740f8f455 0xffbf3f3fc4fffc7f

def z250 : W := mkw 0x06eecbe8079f2b20 0x004ccec0031c0380

def z251 : W := mkw 0x04fbfa1547dbe000 0xfeffff3fc7fff000

def z252 : W := mkw 0x0aee8deab6b40f60 0x7ffccffe3ffc0ff0

def z253 : W := mkw 0x00f9200006d0c000 0xf6ff300007fff000

def z254 : W := mkw 0xc000101740201455 0x0900013fc0000c7f

def z255 : W := mkw 0x00c2c180af030a8a 0x11830100c7038f8f

def z256 : W := mkw 0x0a0415fff0240f60 0x090001fff8000ff0

def z257 : W := mkw 0x04eacb80af9b2a8a 0xb9cfcfc1ff1f8f8f

def z258 : W := mkw 0xc8ffbdfff0201455 0xedfffffff8000c7f

def z259 : W := mkw 0x000040000f030a8a 0x0000000003000380

def z260 : W := mkw 0x0200000006940b20 0x00000000031c0380

def z261 : W := mkw 0x04fbeb80afdbea8a 0xf6fffec03ffff380

def z262 : W := mkw 0x0011301540000000 0x80033001c0000000

def z263 : W := mkw 0x0002c000a903008a 0x0000c00038000000

def z264 : W := mkw 0x00e8000000000000 0x64fc000000000000

def z265 : W := mkw 0x06fd2bea06fcef60 0x7ffc3ffe07fc7ff0

def z266 : W := mkw 0xc1157677596ef5fd 0xff7cfeff3bfe73fc

def z267 : W := mkw 0x0affbdfdf6940b20 0xecfffffffb1c0380

def z268 : W := mkw 0x080405e8b0000000 0x000000c038000000

def z269 : W := mkw 0x083fbc7df0000000 0xc43ffe3ff8000000

def z270 : W := mkw 0x0813fc15f903008a 0x8003fe01f803800f

def z271 : W := mkw 0x401120064060c441 0x7fb3013ec4e18c73

def z272 : W := mkw 0x02ec15fb16b40f60 0xfffcffff3ffc0ff0

def z273 : W := mkw 0xc8fbb99fe060d455 0xffb3313fc4e3fc7f

def z274 : W := mkw 0x02c401ea06240f60 0x39c001fe07000ff0

def z275 : W := mkw 0x832c567b19be35fc 0xff7cfeff3bfe73fc

def z276 : W := mkw 0x81045471190611bc 0xb940c0f13b0203fc

def z277 : W := mkw 0x04392a0000d8e000 0xf6bf3e0004fff000

def z278 : W := mkw 0x02ec01ea00240f60 0x6dfc01fe00000ff0

def z279 : W := mkw 0x00e8000006900000 0x004c0000031c0000

def z280 : W := mkw 0x08001415f0000000 0x00000001f8000000

def z281 : W := mkw 0x08c6d5fdff030a8a 0xb9c3c1ffff038f8f

def z282 : W := mkw 0xc01120020060d455 0xf7b3300004e3fc7f

def z283 : W := mkw 0x81041471180411bc 0xfb0030f1380273fc

def z284 : W := mkw 0x8000101100001014 0x4200303000007070

def z285 : W := mkw 0x00ea880000000000 0x004cce0000000000

def z286 : W := mkw 0x04ea880006910000 0x0000000000000000

def z287 : W := mkw 0x81044260090e31bc 0x7b4c00f0031e73fc

def z288 : W := mkw 0x02ec43ea07be2f60 0xfffcfffe07fe7ff0

def z289 : W := mkw 0x022c006800940120 0x000c0000001c0000

def z290 : W := mkw 0x08fffdfdf7030000 0xfcffffffff038000

def z291 : W := mkw 0x0000020000082000 0x420c3e00001c7000

def z292 : W := mkw 0x083d3c7d50000000 0xec7cfeff38000000

def z293 : W := mkw 0x020401ea06b40f60 0x1b0001fe07fc0ff0

def z294 : W := mkw 0x00000180a8000a8a 0xb98301c1fc038f8f

def z295 : W := mkw 0x81c457f11f0e3bbc 0xfbccfff13f1e7ffc

def z296 : W := mkw 0x08c695fdf0000000 0xa8c3c1fff8000000

def z297 : W := mkw 0x8102d611b90b309e 0x8003fe01f803f00f

def z298 : W := mkw 0x00c2c180a9020088 0xb9c3c1c1fb02038c

def z299 : W := mkw 0x04fba80006d1c000 0xf6b3300004e3f000

def z300 : W := mkw 0x00e84200079a2000 0xf6fcfe0007fe7000

def z301 : W := mkw 0x0cfba98ce6d1c000 0x04b3010ec4e18000

def z302 : W := mkw 0x00c0000006000000 0x30c0000007000000

def z303 : W := mkw 0x0028000000900000 0x463c000000fc0000

def z304 : W := mkw 0x04fbea000fdbea8a 0xf7fffe0007ffff8f

def z305 : W := mkw 0x0000000200200440 0x04b0010e04e00c00

def z306 : W := mkw 0x06ffa9ea06f5cf60 0x7fff01fe07fd8ff0

def z307 : W := mkw 0x00c2c180a903008a 0xa8c3c1c1f803800f

def z308 : W := mkw 0xc1157675594ef1bd 0xfb4ffef1fb1ff3ff

def z309 : W := mkw 0x0aec15fff6b40f60 0x7ffc01fffffc0ff0

def z310 : W := mkw 0x04fbea0007dbe000 0x804ffe00031ff000

def z311 : W := mkw 0x04fbea0007dbe000 0x04ffce0007fd8000

def z312 : W := mkw 0x00c041800f030a8a 0x39c001c007038f8f

def z313 : W := mkw 0x00c2800000000000 0xa0c3c00000000000

def z314 : W := mkw 0x00c2c00007030000 0x0040c00003000000

def z315 : W := mkw 0x00d3b195e0000000 0xecf3f1fff8000000

def z316 : W := mkw 0x0600420207ffef60 0x1300000007fffff0

def z317 : W := mkw 0x0cfbeb8ce7dbe000 0xf6ffff0ec7fff000

def z318 : W := mkw 0x400000020060c441 0x0000000004e18c03

def z319 : W := mkw 0x81041471180411bc 0x7b4c00f13b1c03fc

def z320 : W := mkw 0xc83d3c7f5060d455 0xffbf3f3fc4e3fc7f

def z321 : W := mkw 0x89ffbffdf00c3134 0xeefffffff81c7070

def z322 : W := mkw 0x810456711f0f3bbe 0xfb4cfef13f1fffff

def z323 : W := mkw 0x83ec17fb16bc3f74 0x7ffc3ffe07fc7ff0

def z324 : W := mkw 0x81045673192e35fc 0xfffcffff3ffe7ffc

def z325 : W := mkw 0x02ffa9ea06b40f60 0xfffffffe07fc0ff0

def z326 : W := mkw 0x89eedff9b90e31bc 0xfb4cfef13b1e73fc

def z327 : W := mkw 0x0002c000a903008a 0x8003c001f803800f

def z328 : W := mkw 0x02ec01ea00b40560 0x6efc01fe00fc0070

def z329 : W := mkw 0x04d3eb80af4bea8a 0xb9c3ffc1ff03ff8f

def z330 : W := mkw 0x89ffbdfdf80411bc 0xedfffffff80003fc

def z331 : W := mkw 0x0204006a00240560 0x0000003e00000070

def z332 : W := mkw 0x0affbdfff0240f60 0xedfffffff8000ff0

def z333 : W := mkw 0x00ffbc7110000000 0xecfffef138000000

def z334 : W := mkw 0xc4fbea0207fbf455 0xf7fffe0007fffc7f

def z335 : W := mkw 0x00fba980a0000000 0xecffffc1f8000000

def z336 : W := mkw 0x000000000040c000 0x1200000004e3f000

def z337 : W := mkw 0x00e8018800000000 0x04b0010e00000000

def z338 : W := mkw 0x04fbea00014be000 0xe4fffe000003f000

def z339 : W := mkw 0xc000000200201455 0x0100000000000c7f

def z340 : W := mkw 0x81005611190a309c 0xf24cfe013b1e700c

def z341 : W := mkw 0xc0fbb8174060d455 0xffffff3fc4e3fc7f

def z342 : W := mkw 0x02c0018206b40f60 0x3bc001c007fc0ff0

def z343 : W := mkw 0x401120044040c001 0x00030000c0018003

def z344 : W := mkw 0x44fba80646f1c441 0x04b3010ec4e18c03

def z345 : W := mkw 0x40d3a186e661ce43 0x04b3010ec4e18c03

def z346 : W := mkw 0xc23d307f40f4d575 0x463c303e00fc7070

def z347 : W := mkw 0x083d3dfdf0000000 0x4c3c3ffff8000000

def z348 : W := mkw 0xc00000000040d015 0x000000000003f00f

def z349 : W := mkw 0x81fffe71190e31bc 0xfffffef13b1e73fc

def z350 : W := mkw 0x08ffbdfdf0000000 0xfdfffffffc038c0f

def z351 : W := mkw 0x0cfffffdf14be000 0xecfffffff803f000

def z352 : W := mkw 0x00ec01e800000000 0x004c00c000000000

def z353 : W := mkw 0xc9fffffff96ef5fd 0xffffffffffffffff

def z354 : W := mkw 0x08eecde8bf030a8a 0xb9cfcfc1ff038f8f

def z355 : W := mkw 0x0411620007dbe000 0xf6b3300007fff000

def z356 : W := mkw 0x00004200090a2088 0xfb4cfec13b1e738c

def z357 : W := mkw 0x001120000040c000 0x800330000003f000

def z358 : W := mkw 0x00044060090601a8 0xfb4cc0f13b1e03fc

def z359 : W := mkw 0x0200000206b00e40 0x0000000004e00c00

def z360 : W := mkw 0x85fffff1bfdffbbe 0xfffffff1ffffffff

def z361 : W := mkw 0x00028000a0000000 0x8003c001f8000000

def z362 : W := mkw 0x04c2c380afdbea8a 0xbbc3c1c1ffffff8f

def z363 : W := mkw 0x8100161110083014 0x00003e0000007000

def z364 : W := mkw 0x81ec56711f9e31bc 0xfffcfef13ffe73fc

def z365 : W := mkw 0x001120000040c000 0x04b3000004e18000

def z366 : W := mkw 0x0cffbffdf0d8e000 0xeefffffff8fc7000

def z367 : W := mkw 0x08ffbdfff0200440 0xfffffffffce00c70

def z368 : W := mkw 0x0015347550000000 0xecfffffff8000000

def z369 : W := mkw 0x0000000006000a00 0x1100000007000f80

def z370 : W := mkw 0x08eecde8bf030a8a 0x004ccec03b000380

def z371 : W := mkw 0x04fbaa0006d9e000 0x46bf3e0004fdf000

def z372 : W := mkw 0xc01170174962d4dd 0xfff3f1ffffe3ffff

def z373 : W := mkw 0x04396a0001dae000 0xf67cfe0003fe7000

def z374 : W := mkw 0x08fffffdf10a2000 0xfefffffffb1e7000

def z375 : W := mkw 0x8011301540001014 0xffb3313fc002707c

def z376 : W := mkw 0x0002c180a9030a8a 0x8903c1c1f8038f8f

def z377 : W := mkw 0x401130174060c441 0xecb3313fc4e18c03

def z378 : W := mkw 0x00ec01e800040120 0x7ffc01fe031c03f0

def z379 : W := mkw 0x00c2c180af030a8a 0x00c3c1c0ff018f83

def z380 : W := mkw 0x0400020000d8e000 0x0200000000fc7000

def z381 : W := mkw 0x0000000006010a02 0x0000000004018c03

def z382 : W := mkw 0x42f9218e46f0ce41 0x04b3010ec4e18c03

def z383 : W := mkw 0xc0c2d197ef231edf 0xb9c3c1ffff038fff

def z384 : W := mkw 0x081535fdf0000000 0xecb331fff8000000

def z385 : W := mkw 0x02eec1e8af970baa 0x004cc0c03b1c0380

def z386 : W := mkw 0x0800018ce0000000 0x0000010ec0000000

def z387 : W := mkw 0x0000101540000000 0x0800013fc0000000

def z388 : W := mkw 0x00c2c380af0b2a8a 0xfbcfffc1ff1fff8f

def z389 : W := mkw 0x0aee8de8b6940b20 0x004ccec03b1c0380

def z390 : W := mkw 0xccfffffff7fbf455 0xfffffffffffffc7f

def z391 : W := mkw 0xc211301746f4df75 0xffb3313fc7ffffff

def z392 : W := mkw 0x890415fdf80411bc 0x090001fff80003fc

def z393 : W := mkw 0x0affa9eee6b40f60 0x7fff01fec7fc0ff0

def z394 : W := mkw 0x0000400009020088 0x110000000302038c

def z395 : W := mkw 0xc0d3f195ef43da9f 0xb9c3f1c1ff03ff8f

def z396 : W := mkw 0x04fbea0007dbe000 0x467cfe0003fc7000

def z397 : W := mkw 0x00eac00007930000 0xf6ffc00007ff8000

def z398 : W := mkw 0x0204006206b40f60 0x7b4c00f007fc0ff0

def z399 : W := mkw 0x000040000903008a 0x000000000003800f

def z400 : W := mkw 0x89fffffdff0f3bbe 0xffffffffff1fffff

def z401 : W := mkw 0x81041671100c3134 0xea4cfef1381c7070

def z402 : W := mkw 0x00e8018006900a00 0x7ffc01c007fc0f80

def z403 : W := mkw 0x401120064060c441 0xbdb3010fc4e38c0f

def z404 : W := mkw 0x04eaca00079b2000 0xb0cfce00071f8000

def z405 : W := mkw 0xc1117615594af09d 0x8003fe01f803f00f

def z406 : W := mkw 0x04004200014be000 0x000000000003f000

def z407 : W := mkw 0x08ffade8b0000000 0xe4fffec038000000

def z408 : W := mkw 0x0011200440000000 0x04b3010ec0000000

def z409 : W := mkw 0x00c401e006040b20 0x7bcc01f0071c0ff0

def z410 : W := mkw 0xc01130174060d455 0x84b3310fc4e3fc0f

def z411 : W := mkw 0x81000200000c3134 0x02000000001c7070

def z412 : W := mkw 0x082c0c6810000000 0x000c0e0000000000

def z413 : W := mkw 0xc01130174060d455 0x93033001c4e3fc7f

def z414 : W := mkw 0x06ffebe807dfeb20 0xf6fffec007fff380

def z415 : W := mkw 0x06ec43ea07ffef60 0x7ffc01fe07fffff0

def z416 : W := mkw 0xc01130154040d015 0xb9833101c403fc0f

def z417 : W := mkw 0x022c006a00b40560 0x7fbc013e04fc0c70

def z418 : W := mkw 0x02c6c1eaaf270fea 0xb9c3c1ffff038fff

def z419 : W := mkw 0x00c28180a0000000 0xb9c3c1c1fc038c0f

def z420 : W := mkw 0x8000101100001014 0x800030010002700c

def z421 : W := mkw 0x81045671190e31bc 0x424cfef03b1c73f0

def z422 : W := mkw 0x00c28180a6010a02 0x39c301c0c7018f83

def z423 : W := mkw 0x8000101100001014 0x090000310000007c

def z424 : W := mkw 0x40d3e186ef63cecb 0xbdf3c1cfffe38f8f

def z425 : W := mkw 0x02ec006a06b40560 0x76fc003e07fc0070

def z426 : W := mkw 0x0000000000000000 0xa840c0c138000000

def z427 : W := mkw 0xc1045673196ef5fd 0xfb4cfef13fffffff

def z428 : W := mkw 0x8000101100001014 0xfb833131c403fc7f

def z429 : W := mkw 0x03ec47e81f9e2ba8 0x004ccec03b1c0380

def z430 : W := mkw 0x0011301740200440 0xffb3313fc4e00c70

def z431 : W := mkw 0xc413fa15414bf015 0x8003fe01c003f00f

def z432 : W := mkw 0xc01120064060d455 0x17b3010ec4e3fc7f

def z433 : W := mkw 0x04eaca0007dbe000 0x124cce0007fff000

def z434 : W := mkw 0xc01130174060d455 0xeeb3313fc0e07070

def z435 : W := mkw 0xc00000020060d455 0xbb830101c4e3fc7f

def z436 : W := mkw 0x0000000000000000 0x00830100c4018c03

def z437 : W := mkw 0x81157671194ef1bc 0xfffffef13ffff3fc

def z438 : W := mkw 0x00fba8000040c000 0xf6fffe0004e3f000

def z439 : W := mkw 0x0a3d3c7f50b40560 0x463c3e3e00fc0070

def z440 : W := mkw 0x0ceecfe8b79b2000 0x004ccec03b1c0000

def z441 : W := mkw 0x08ee9dfdf0000000 0x084ccffff8000000

def z442 : W := mkw 0x08ea8988a0000000 0x0000000000000000

def z443 : W := mkw 0x000040000f030a8a 0xb9830101c7038f8f

def z444 : W := mkw 0x853d7e7119def1bc 0xff7cfef13bfe73fc

def z445 : W := mkw 0x0817bdfdf0000000 0x8803fffff8000000

def z446 : W := mkw 0x8917fe75f90e31bc 0xfb4ffef1fb1e73fc

def z447 : W := mkw 0x0439280000d0c000 0x0430000000e00000

def z448 : W := mkw 0x401120064060c441 0x0430000e00e00000

def z449 : W := mkw 0xc013f015e943d09f 0x8003f001f803f00f

def z450 : W := mkw 0xc411721747fbf455 0xffb3313fc7fffc7f

def z451 : W := mkw 0x80c2d191af031a9e 0xfbc3f1f1ff03ffff

def z452 : W := mkw 0x0002c000a903008a 0xb983c101fc038c0f

def z453 : W := mkw 0xc2ec01ea06f4df75 0x7ffc01fe07ffffff

def z454 : W := mkw 0x401120064060c441 0xf6b3310ec4e3fc03

def z455 : W := mkw 0xc4393a1740f8f455 0x463c3e3e00fc7070

def z456 : W := mkw 0xc00040020f63dedf 0x1300000007e3ffff

def z457 : W := mkw 0x06fbea0207ffef60 0xf7fffe0007fffff0

def z458 : W := mkw 0x04fbea0207fbe440 0xffffff3e07fffc70

def z459 : W := mkw 0x020401ea00240f60 0x7fb001fe04e00ff0

def z460 : W := mkw 0x00fbea00010a2000 0xf6fffe00031e7000

def z461 : W := mkw 0x08ffbdfdf6000a00 0xfdffffffff000f80

def z462 : W := mkw 0x0002c000a903008a 0xb943c0c1fb03838f

def z463 : W := mkw 0x043bea0001dbe000 0xc63ffe0000fff000

def z464 : W := mkw 0x00000180a0000000 0x080001c1f8000000

def z465 : W := mkw 0x81045671190e31bc 0x8900fef1380273fc

def z466 : W := mkw 0xc813bc15f040d015 0x8003fe01f803f00f

def z467 : W := mkw 0x080415fdf8000a8a 0x090001fff8000f8f

def z468 : W := mkw 0x00d3f195ef030a8a 0xfdf3f1ffff038f8f

def z469 : W := mkw 0x08ffbdfdf0000000 0x44bf3f3ec0000000

def z470 : W := mkw 0x01040660100c2120 0x000c0e00001c0000

def z471 : W := mkw 0x02eec1eaafb70fea 0x7ffcc1fe3ffc0ff0

def z472 : W := mkw 0x00fba80006900000 0xf6fffe0007fc0000

def z473 : W := mkw 0x830456731fbe3ffc 0xfb4cfef13ffe7ffc

def z474 : W := mkw 0xc81535fff060d455 0xffb331fffce3fc7f

def z475 : W := mkw 0x02ec41ea0fb60fe8 0xfffcc1ff3ffe0ffc

def z476 : W := mkw 0xc0001197e8201edf 0x090001fff8000fff

def z477 : W := mkw 0xc01130174060d455 0xf6b3303e04e3f070

def z478 : W := mkw 0x00c28180a6010a02 0x0000000000000000

def z479 : W := mkw 0x00ec01ea00200440 0x7ffc01fe04e00c70

def z480 : W := mkw 0x04d3ea00074be000 0xb0c3fe000703f000

def z481 : W := mkw 0x00eec1e8af030a8a 0xfdffc1ffff038f8f

def z482 : W := mkw 0xc4fbfa1547dbf015 0xf6fffe01c7fff00f

def z483 : W := mkw 0x0000000000000000 0x6cb0013e00000000

def z484 : W := mkw 0x00fbe980af030a8a 0xfdffffc1ff038f8f

def z485 : W := mkw 0x853d3e7110dcf134 0x463c3e3000fc7070

def z486 : W := mkw 0x8004147110001014 0xfb4cfef13802707c

def z487 : W := mkw 0x0000000200200440 0xffb3013fc4e38c7f

def z488 : W := mkw 0x0000000200200440 0x4630003e00e00070

def z489 : W := mkw 0xc0d3b197e060d455 0xfff3f1fffce3fc7f

def z490 : W := mkw 0xc6fffbff47ffff75 0xffffffffc7ffffff

def z491 : W := mkw 0x81004200090e31bc 0xbb40c0c13b1e73fc

def z492 : W := mkw 0x06fbeb8a07fbee40 0xf6ffff0e07fffc00

def z493 : W := mkw 0x00004200010a2000 0x12000000031e7000

def z494 : W := mkw 0xc0c2c182af63dedf 0xbbc3c1c1ffe3ffff

def z495 : W := mkw 0x00c2c00007030000 0xb9c3c101c7038c0f

def z496 : W := mkw 0x8000000000001014 0x130000000002707c

def z497 : W := mkw 0x8517fe71194ff1bc 0xfb4ffef13b1ff3fc

def z498 : W := mkw 0x81045671190e31bc 0x804cfec13b1e738c

def z499 : W := mkw 0x0cfffffdf79b2000 0xecfffffffb1c0000

def z500 : W := mkw 0xc2fff1ffeff7dfff 0xfffff1ffffffffff

def z501 : W := mkw 0x0000000000000000 0x80030001c003800f

def z502 : W := mkw 0x81045671190e31bc 0x094ccef13b1c03fc

def z503 : W := mkw 0x08ee8de8b0000000 0x6cfccffe38000000

def z504 : W := mkw 0x0c13fe15f14be000 0x8003fe01f803f000

def z505 : W := mkw 0x020401e800040b20 0x000000c000000380

def z506 : W := mkw 0x00045671110a2000 0xfa4cfef13b1e7000

def z507 : W := mkw 0x0000000000000000 0xf200300000027000

def z508 : W := mkw 0x00ee81e8a0000000 0xecffc1fff8000000

def z509 : W := mkw 0x03ec47ea1fbe2fe8 0x7ffccffe3ffc0ff0

def z510 : W := mkw 0x04fbeb80a7dbe000 0xfeffffc1fffff000

def z511 : W := mkw 0x850456711fdff1bc 0xfb4cfef13ffff3fc

def z512 : W := mkw 0x04c2c20007dbe000 0xb2c3c00007fff000

def z513 : W := mkw 0x0402ca00010b2000 0x0000ce0000000000

def z514 : W := mkw 0x0000000000000000 0x1100000004038c0f

def z515 : W := mkw 0x0839280c40000000 0x0430000e00000000

def z516 : W := mkw 0x0000000000000000 0x76b0000004e00000

def z517 : W := mkw 0xcaffbdfff6f4df75 0xffffffffffffffff

def z518 : W := mkw 0x00c2c0000f030088 0xb9c3c0c13f03838c

def z519 : W := mkw 0x0000101100000000 0xe800303100000000

def z520 : W := mkw 0x0cfffe7d57dbe000 0xf6fffe3e07fff000

def z521 : W := mkw 0x001120020060c440 0xffb3313e04e3fc70

def z522 : W := mkw 0x00c6d5f1bf030a8a 0xf9cffff1ff038f8f

def z523 : W := mkw 0x00d3e180af43ca8a 0xfff3f1c1ffe3ff8f

def z524 : W := mkw 0x08fba98ce0000000 0xe4ffff0ec0000000

def z525 : W := mkw 0x00c28180a0000000 0x00830100c0000000

def z526 : W := mkw 0x083d3c7d50000000 0xecbf3f3fc0000000

def z527 : W := mkw 0x8000101300201454 0xffb0313f04e27c7c

def z528 : W := mkw 0x00c2c180a7030000 0xb8c3c1c1ff038000

def z529 : W := mkw 0x81041671100c3134 0xfb0c3e31001e707c

def z530 : W := mkw 0x0200000200240f60 0x0100000000000ff0

def z531 : W := mkw 0x0000141110000000 0x8000fe0138000000

def z532 : W := mkw 0xc0d3f0174763d455 0xfff3f13fc7e3fc7f

def z533 : W := mkw 0x00c00180ae000a8a 0x39c001c1ff000f8f

def z534 : W := mkw 0x08fd3dfd50000000 0x6cfc3ffe00000000

def z535 : W := mkw 0xc01130174060d455 0xff30303f00e2707c

def z536 : W := mkw 0x81004200090e31bc 0xf34cfe00031e73fc

def z537 : W := mkw 0xc01534775060d455 0xfffffffffce3fc7f

def z538 : W := mkw 0x800050110902109c 0xfb40f0f13b0273fc

def z539 : W := mkw 0x0011200000000000 0xe4b3300000000000

def z540 : W := mkw 0x08ee8de8b0000000 0xa8cfcfc1f8000000

def z541 : W := mkw 0x48ffbdfff060c441 0xecfffffffce18c03

def z542 : W := mkw 0xc01130174060d455 0x7fb0313e04e07c70

def z543 : W := mkw 0x000401e800000000 0x080001fe00000000

def z544 : W := mkw 0x0039280000000000 0x443c3e0000000000

def z545 : W := mkw 0x8bffffffffbe3ffc 0xfffffffffffe7ffc

def z546 : W := mkw 0x020040020fb70fea 0x1300000007ff8fff

def z547 : W := mkw 0x00c695f1b0000000 0xe8cffff1f8000000

def z548 : W := mkw 0xc4fbfa1747fbf455 0xf6fffe3e07fff070

def z549 : W := mkw 0x00c28180a8000a8a 0xa9c3c1c1f8000f8f

def z550 : W := mkw 0x00c2c180af030a8a 0x0940c1c1fb000f8f

def z551 : W := mkw 0x0000000000000000 0x724c0000031c0000

def z552 : W := mkw 0x48fba98ee060c441 0x04b3010ec4e18c03

def z553 : W := mkw 0x08fbb99de0000000 0xecb3313fc0000000

def z554 : W := mkw 0x02ec01eaaeb40fea 0x7ffc01fffffc0fff

def z555 : W := mkw 0x00c2c18007030a00 0xb9c3c1c007038f80

def z556 : W := mkw 0x0cfbfe15f7dbe000 0xf6fffe01fffff000

def z557 : W := mkw 0x0413ea00014be000 0xf24ffe00031ff000

def z558 : W := mkw 0xc2f9319f46f0de55 0xffb3313fc4e3fc7f

def z559 : W := mkw 0x04fba80006d1c000 0xe4fffe0004e18000

def z560 : W := mkw 0x0000000200200440 0x1300000004e00c70

def z561 : W := mkw 0x080415fdf0000000 0xe84cfffff8000000

def z562 : W := mkw 0x02eec1ea07b70f60 0xffffc1fe07ff8ff0

def z563 : W := mkw 0xc21531ff4064df75 0xffb331ffc4e3ffff

def z564 : W := mkw 0xc000101740201455 0x7fb0013fc4e00c7f

def z565 : W := mkw 0x85fffe7117dff134 0xf6fffe3007fff070

def z566 : W := mkw 0x81044660190e31bc 0x134ccec03b1e73fc

def z567 : W := mkw 0xc011301740201455 0xedb3313fc0000c7f

def z568 : W := mkw 0x0004147110000000 0x080000f138000000

def z569 : W := mkw 0x0200000200b40560 0x0200000000fc0070

def z570 : W := mkw 0x02ec01ea06b40f60 0xffff01ffc7ff8fff

def z571 : W := mkw 0x81c6d5f1bf071bbe 0xb9c3c1f1ff038fff

def z572 : W := mkw 0x81c6d7f1b90e31bc 0xfbcffff1fb1e73fc

def z573 : W := mkw 0x08028c00b0000000 0x0000ce0038000000

def z574 : W := mkw 0x0004006200240560 0x7ffc01fe07fc0ff0

def z575 : W := mkw 0xc01130174060d455 0xc633303fc0e3f07f

def z576 : W := mkw 0x85fbfe111fdbf09c 0xf6fffe013ffff00c

def z577 : W := mkw 0xc5fffe775ffff5fd 0xffffffffffffffff

def z578 : W := mkw 0x05ffee601fdfe1a8 0xf6fffec03ffff380

def z579 : W := mkw 0xc01130154040d015 0xecb3313fc003f00f

def z580 : W := mkw 0x81005211090e31bc 0xfb003031031e73fc

def z581 : W := mkw 0x00c0018000000000 0x28c001c000000000

def z582 : W := mkw 0x0004547119020088 0xf94cfef13b02038c

def z583 : W := mkw 0xc01130154040d015 0xfb033031c003f07f

def z584 : W := mkw 0x8dfffffdffdff1bc 0xfffffffffffff3fc

def z585 : W := mkw 0x002c006800000000 0x443c003e00000000

def z586 : W := mkw 0xc01130174060d455 0x46b3313ec4e1fc73

def z587 : W := mkw 0x02e8018a06b00e40 0x3df001ce07e00f80

def z588 : W := mkw 0x0afffdffffb70fea 0xffffffffffff8fff

def z589 : W := mkw 0x0004006000040120 0x004c00c0031c0380

def z590 : W := mkw 0x01045671190e21a8 0xe84cfef13b1c0380

def z591 : W := mkw 0x05eece601f9f21a8 0x004ccec03b1c0380

def z592 : W := mkw 0x04fbea00079b2000 0xe4fffe00031c0000

def z593 : W := mkw 0x02ec01e806940b20 0x76fc00c007fc0380

def z594 : W := mkw 0x81c2c380af0f3bbe 0xbbc3c1c1ff1fffff

def z595 : W := mkw 0x0000000000000000 0x09000101c0000c0f

def z596 : W := mkw 0x87fffffb1ffffffc 0xffffffff3ffffffc

def z597 : W := mkw 0x04fbe980afd3ca8a 0xbdf3c1c1ffe38f8f

def z598 : W := mkw 0x01004600190a2088 0x0000ce0038000000

def z599 : W := mkw 0x00004180a9020a8a 0xb940c1c1fb020f8f

def z600 : W := mkw 0x83ec43ea0fbe3ffc 0x7ffc01fe07fe7ffc

def z601 : W := mkw 0x01040460180401a8 0x000000c038000380

def z602 : W := mkw 0x85eede711f9f31bc 0xfb4cfef13b1e73fc

def z603 : W := mkw 0x08ee9df9b0000000 0xe84cfef138000000

def z604 : W := mkw 0x00004200010a2000 0x8000fe0000027000

def z605 : W := mkw 0x81045671190a309c 0xe84cfef13802700c

def z606 : W := mkw 0x04e8420007dbe000 0x76fc000007fff000

def z607 : W := mkw 0x00c2c180af030a8a 0x8083c101fc038c0f

def z608 : W := mkw 0x08113c1550000000 0x00003e0000000000

def z609 : W := mkw 0x81005611190a309c 0xb940fec13b02738c

def z610 : W := mkw 0x06ffea6a07ffe560 0xf6fffe3e07fff070

def z611 : W := mkw 0x06fba98a06f1ce40 0x04b3010e04e18c00

def z612 : W := mkw 0x81045671190e31bc 0x1b0000f13b1e73fc

def z613 : W := mkw 0x01004200090e21a8 0x00000000031c0380

def z614 : W := mkw 0x0413a8000041c000 0x0003000000018000

def z615 : W := mkw 0x81004200090a309c 0x000000000002700c

def z616 : W := mkw 0x00c2c180af030a8a 0x8043c0c1fb03838f

def z617 : W := mkw 0x02e8000206b40f60 0x77fc000007fc0ff0

def z618 : W := mkw 0x0000000008000088 0x090000c13800038c

def z619 : W := mkw 0x02ec41ea0fb70fea 0x7ffc01fe07ff8fff

def z620 : W := mkw 0xc0f9301746f0d455 0xffff313fc7fffc7f

def z621 : W := mkw 0x0000400007030000 0x1000000007038000

def z622 : W := mkw 0x0200018a00200e40 0x0000010e00000c00

def z623 : W := mkw 0x04fbea0007dbe000 0x84b3fe0004e3f000

def z624 : W := mkw 0xc3fd77ff5ffefffd 0xffffffffffffffff

def z625 : W := mkw 0x08fbe98cef030a8a 0xbdf3c1cfff038f8f

def z626 : W := mkw 0x0813a804e0000000 0x00030000c0000000

def z627 : W := mkw 0xc01530774064d575 0xffff31ffc7ffffff

def z628 : W := mkw 0x893d7e7d590e31bc 0xff7cfeff3b1e73fc

def z629 : W := mkw 0x0000000006900000 0x1200000007fc0000

def z630 : W := mkw 0x00c2c180af030a8a 0x1140c0c03f038f8f

def z631 : W := mkw 0xc23d307f40f4d575 0xffbf313fc4fffc7f

def z632 : W := mkw 0x01044660190e21a8 0x7b4ccef03b1c03f0

def z633 : W := mkw 0xc01130174060d455 0x4f30313fc0e07c7f

def z634 : W := mkw 0x022c01ea00b40f60 0x4f3c01fe00fc0ff0

def z635 : W := mkw 0x810014111800109c 0x000000013800000c

def z636 : W := mkw 0x00c28180a6010a02 0xb9830101c4038c0f

def z637 : W := mkw 0x020401eaa8240fea 0x090001fff8000fff

def z638 : W := mkw 0x00fbe80007030000 0xf4fffe0007038000

def z639 : W := mkw 0xc413fa17416bf455 0xffb3ff3fc4e3fc7f

def z640 : W := mkw 0x00004200010a2000 0x004cce00031c0000

def z641 : W := mkw 0x850042000fdff1bc 0x1300000007fff3fc

def z642 : W := mkw 0xc000101740201455 0xfb00313fc0027c7f

def z643 : W := mkw 0x00c2c180af030a8a 0xa8c3c1c1fb000380

def z644 : W := mkw 0x0000018000000a00 0x090001c000000f80

def z645 : W := mkw 0x02c2c182afb70fea 0xbbc3c1c1ffff8fff

def z646 : W := mkw 0xc11534775864d5fd 0xffb331fffce3ffff

def z647 : W := mkw 0x0afd3dff56b40f60 0x7ffc3ffe07fc0ff0

def z648 : W := mkw 0x00c041800f020a88 0xb9c0c1c13f020f8c

def z649 : W := mkw 0x81045671190e31bc 0x530c3e30031e73fc

def z650 : W := mkw 0xc013f017e963d4df 0xffb3f13ffce3fc7f

def z651 : W := mkw 0x020401ea00240f60 0x7b4c01fe031c0ff0

def z652 : W := mkw 0x0000000000000000 0xe04cfe0000000000

def z653 : W := mkw 0x82ec11fb06b41f74 0xfffc31ff07fe7ffc

def z654 : W := mkw 0x02ec01ea06b40f60 0x04fc01ce07fc0f80

def z655 : W := mkw 0xc4fbb81746f1d455 0xffb3313fc4e3fc7f

def z656 : W := mkw 0x00028000a0010002 0x00030000c0018003

def z657 : W := mkw 0xc813bc17f060d455 0xffb3ff3ffce3fc7f

def z658 : W := mkw 0x832c167b10bc3574 0x463c3e3e00fc7070

def z659 : W := mkw 0x02ec01e806940b20 0x6cfc01fe031c0380

def z660 : W := mkw 0x00c2c000af03008a 0xb0c3c001ff03800f

def z661 : W := mkw 0x02e8018a06b40f60 0x17b0010e07fc0ff0

def z662 : W := mkw 0xc01130174060d455 0x5730303e04e3fc7f

def z663 : W := mkw 0x00d3e0000743c000 0xf6f3f00007e3f000

def z664 : W := mkw 0xc00010130060d455 0xfb00303104e3fc7f

def z665 : W := mkw 0x0000400009020088 0x0040c0c03b000380

def z666 : W := mkw 0x0000000200200440 0x0900013e00000c70

def z667 : W := mkw 0x0413ea00014be000 0xf6b3fe0004e3f000

def z668 : W := mkw 0x81045671110e3134 0xf24cfe30031e7070

def z669 : W := mkw 0xc83d3c7f5060d455 0x463c3e3e00e07070

def z670 : W := mkw 0x81c6d7f1bf0f3bbe 0xfb4cfef13b1e73fc

def z671 : W := mkw 0x02ec01ea06b40f60 0x134c00c007fc0ff0

def z672 : W := mkw 0x44fbea0647fbe441 0xf6ffff0ec7fffc03

def z673 : W := mkw 0x81041671100c3134 0x7b4c3ef0031c73f0

def z674 : W := mkw 0x0000000000000000 0xa8830101c0000000

def z675 : W := mkw 0xc00000020060d455 0x7fb0013e04e3fc7f

def z676 : W := mkw 0x0004006000000000 0x684c00f000000000

def z677 : W := mkw 0x0affbdfff6b00e40 0xecfffffffce00c00

def z678 : W := mkw 0x04eaca00079b2000 0x76fcce0007fc0000

def z679 : W := mkw 0x00c2c0000f030a8a 0xb1c3c00007038f8f

def z680 : W := mkw 0xc2ec11ff46b41f75 0x7ffc01ffc7fc0fff

def z681 : W := mkw 0x04eaca00079b2000 0xf24cfe00031e7000

def z682 : W := mkw 0xc0d131974660de55 0xfff331ffc7e3ffff

def z683 : W := mkw 0x02e8018a06b00e40 0x76fc010e07fc0c00

def z684 : W := mkw 0xc1045677592e35fd 0xfb4cfffffb1e7fff

def z685 : W := mkw 0x83ec15fb1eb41ffc 0x7ffc01ff3ffc0ffc

def z686 : W := mkw 0x0afba98ee6b00e40 0x04b3010ec4e00c00

def z687 : W := mkw 0x04fbea0007dbe000 0x16b3000007fff000

def z688 : W := mkw 0x42fd21ee46f4cf61 0x7fff01fec7fd8ff3

def z689 : W := mkw 0xc01170174f63dedf 0xffb3313fc7e3ffff

def z690 : W := mkw 0x00c2c180a7030a02 0xb0c3c100c7038c03

def z691 : W := mkw 0x0004046010000000 0x004ccec038000000

def z692 : W := mkw 0x01c6c7e0bf0f2baa 0xb9cfcfc1ff1f8f8f

def z693 : W := mkw 0x0000000000000000 0x3980010004000c00

def z694 : W := mkw 0x08d3fd95ff030a8a 0xb9c3ffc1ff038f8f

def z695 : W := mkw 0x02ec01e806940b20 0x39cc01c0071c0f80

def z696 : W := mkw 0x08ffa9ece0000000 0x6cff01fec0000000

def z697 : W := mkw 0x02ea818aa6b10e42 0x04b3010ec4e18c03

def z698 : W := mkw 0x08fffdfdf903008a 0xecfffffff803800f

def z699 : W := mkw 0x02fd31ff46b40f60 0xffff31ffc7fc0ff0

def z700 : W := mkw 0x0000000000000000 0x394000c003000380

def z701 : W := mkw 0x08d3bd95f0000000 0xa8c3ffc1f8000000

def z702 : W := mkw 0xc1d7f7f7ff6fffff 0xffffffffffffffff

def z703 : W := mkw 0x00e8000006900000 0x04b0000004e00000

def z704 : W := mkw 0x06eecbea07bf2f60 0x7ffccffe07fc0ff0

def z705 : W := mkw 0x00c2800006010000 0x0083000004018000

def z706 : W := mkw 0xc80415fff0201455 0x090001fff8000c7f

def z707 : W := mkw 0x040042000fdbea8a 0xfb4cfec13fffff8f

def z708 : W := mkw 0x04fbeb80afdbea8a 0x467cfec03bfc7380

def z709 : W := mkw 0x08ffadecf0000000 0x047ccece38000000

def z710 : W := mkw 0x04fbeb80afdbe08a 0xfeffffc1fffff00f

def z711 : W := mkw 0x0011341550000000 0xecb3ff3ff8000000

def z712 : W := mkw 0x81045675590e31bc 0xfb4cfffffb1e73fc

def z713 : W := mkw 0x41156666596ee5e9 0x04ffcfcefffd8f83

def z714 : W := mkw 0x0817bc7df0000000 0x8003fe3ff8000000

def z715 : W := mkw 0x02ec01ea00b40560 0x7ffc01fe03fc03f0

def z716 : W := mkw 0x0200000206b40f60 0x5730003e07fc0ff0

def z717 : W := mkw 0x0413ea0007dbe000 0xf24ffe0007fff000

def z718 : W := mkw 0x08ffbdfdf0000000 0xedfffffff8000c0f

def z719 : W := mkw 0x04eacb80af9b2a8a 0xffffcfc1ffff8f8f

def z720 : W := mkw 0x08ffbdfdf0000000 0x6cfcfffe38000000

def z721 : W := mkw 0x022ec06aa9b705ea 0xc63fc03ff8ff807f

def z722 : W := mkw 0x830415fbb8241ffe 0x090001fff8000fff

def z723 : W := mkw 0x04396a0009dae088 0xff7cfec13bfe738c

def z724 : W := mkw 0x02ec01ea06b40f60 0x7ffc01fe07ff8fff

def z725 : W := mkw 0x0affbdfdf6900a00 0xecfffffff8000000

def z726 : W := mkw 0x89fbeb8ce90e31bc 0x17b3010ec31e73fc

def z727 : W := mkw 0x04fbea0007dbea00 0xf7fffe0007ffff80

def z728 : W := mkw 0x02ec006a06b40560 0x7ffc00fe07fc03f0

def z729 : W := mkw 0x00c2c380af0b2a8a 0xb9cfcfc1ff1f8f8f

def z730 : W := mkw 0x04392a0000d8e000 0xffbf3f01c4fffc0f

def z731 : W := mkw 0x04fbea0007dbe000 0xfffffec007fff380

def z732 : W := mkw 0x870042020ffffffc 0x1300000007fffffc

def z733 : W := mkw 0xc11534775064d575 0x4630303e00e07070

def z734 : W := mkw 0x083fbc7df0000000 0xecbfff3ff8000000

def z735 : W := mkw 0x0cfbea04e7dbe000 0xf6fffe00c7fff000

def z736 : W := mkw 0xc0d3f197ef63dedf 0x4670f0fe3be073f0

def z737 : W := mkw 0x04fbeb80a7dbea02 0xf6fffe0007fff000

def z738 : W := mkw 0x00c041800f020a88 0xb9c3c1c1ff038f8f

def z739 : W := mkw 0x02ee81eaa6b50f62 0xffffc1fffffd8ff3

def z740 : W := mkw 0x81045671190e31bc 0xfb4ffef1fb1ff3ff

def z741 : W := mkw 0x81c697f1b60d3b36 0x428f3f30c41dfc73

def z742 : W := mkw 0x08ffbdfdf6900000 0xecfffffffb1c0000

def z743 : W := mkw 0x04396a0007dbe000 0x463c3e0003fc7000

def z744 : W := mkw 0x02eac188af930a8a 0xb9c3c1c1ff038f8f

def z745 : W := mkw 0x0400420007dbe000 0x520c3e0007fff000

def z746 : W := mkw 0x8904567d590e31bc 0xfb4cfeff3b1e73fc

def z747 : W := mkw 0x83e8579b1fba3edc 0x84b0ff0f3ce27c0c

def z748 : W := mkw 0x8300420209be35fc 0x1300000003fe73fc

def z749 : W := mkw 0x00c28180a6000a00 0xb9c3c1c1ff038f8f

def z750 : W := mkw 0x043baa0000d8e000 0xc63ffe0000fc7000

def z751 : W := mkw 0x04392a0000d8e000 0xf63c3e0000fe7000

def z752 : W := mkw 0x0804147d50000000 0xe84cfeff38000000

def z753 : W := mkw 0x02ec01ea06b40f60 0x76fc00fe07fc03f0

def z754 : W := mkw 0x08ffbdfdf0000000 0xfefffffff8027000

def z755 : W := mkw 0x04fbeb80afdbea8a 0xfeffffc1fffff380

def z756 : W := mkw 0x08c695fdf0000000 0xe8cffffff8000000

def z757 : W := mkw 0x083d3c7d50000000 0xecfffffff8000000

def z758 : W := mkw 0x00c28180ae010a8a 0xa9c3c1c1fc018f8f

def z759 : W := mkw 0x06ee89ea06b50f60 0x7ffc01fe07fc0ff0

def z760 : W := mkw 0x00fbb995e0000000 0xecfffffff8000000

def z761 : W := mkw 0x04fbeb800fdbea88 0xffffffc13fffff8c

def z762 : W := mkw 0xc413fa15e94bf09f 0x8003fe01f803f00f

def z763 : W := mkw 0x00eac980af030a8a 0xb9cfcfc1ff038f8f

def z764 : W := mkw 0x00c28180ae010a8a 0xb98301c1fc038f8f

def z765 : W := mkw 0x00eac380af9b2a8a 0xffffffc1ffffff8f

def z766 : W := mkw 0x04fbeb80afdbe088 0xffffffc1fffff38c

def z767 : W := mkw 0x0aee89eaa6b40f60 0x7ffc01fe07fc0ff0

def z768 : W := mkw 0x04fbaa0006d9e000 0x463c3e0000fc7000

def z769 : W := mkw 0x8304147b10241574 0x0000003e00000070

def z770 : W := mkw 0x01044660190e21a8 0xfb4cfef03b1e73f0

def z771 : W := mkw 0x00c2c180af030a8a 0xfdf3c1ffff038f8f

def z772 : W := mkw 0x0004147110000000 0xecfcffff38000000

def z773 : W := mkw 0x00c28180a8000a8a 0xb9c3c1c1fc038f8f

def z774 : W := mkw 0xc2fd31fd46d4db35 0x804f30c1c31ff38f

def z775 : W := mkw 0x00c2c380af0b2a8a 0xb9c3ffc1ff03ff8f

def z776 : W := mkw 0x4afba98ee6f0ce41 0x04b3010ec4e18c03

def z777 : W := mkw 0x02ec01ea06b40f60 0xfffc31fe07fe7ff0

def z778 : W := mkw 0x81004200090e31bc 0xfb4cfec13b1e73fc

def z779 : W := mkw 0x0617ebea016fef60 0x8903fffe0003fff0

def z780 : W := mkw 0x00fbea00014ae000 0xf6fffe0007fff000

def z781 : W := mkw 0x08ffbdfdf0000000 0xfcfffffffc038000

def z782 : W := mkw 0x04fbeb8007dbea00 0xf6ffff0007fffc00

def z783 : W := mkw 0x08ffadecf0000000 0xacffcfcff8000000

def z784 : W := mkw 0x08ffbdfdf0040120 0xedfffffff80003f0

def z785 : W := mkw 0x08ee8de8b0000000 0x04fccfce38000000

def z786 : W := mkw 0x02ee81eaa6b50f62 0x7ffc01fe07fc0ff0

def z787 : W := mkw 0x44fbea0447dbe001 0xf6fffe00c7fff003

def z788 : W := mkw 0x04fbeb80afdbea8a 0xf6fffec1fffff38f

def z789 : W := mkw 0x04eac980af930a8a 0xb9c3c1c1ff038f8f

def z790 : W := mkw 0x04fbaa0000d8e000 0x46bf3e0000fc7000

def z791 : W := mkw 0x043bea0001dbe000 0xf67ffe0003fff000

def z792 : W := mkw 0x00ee95f9b0000000 0xecfffffff8000000

def z793 : W := mkw 0x08fba98ce0000000 0xecffffcff8000000

def z794 : W := mkw 0x08ffbdfdf6940120 0xfffffffffffc03f0

def z795 : W := mkw 0x04fbeb80a7dbe000 0xf6ffff00c7fff000

def z796 : W := mkw 0x02ec01ea06b40f60 0xfffc01ff07fe0ffc

def z797 : W := mkw 0x0002c180a9030a8a 0xb943c1c1fb038f8f

def z798 : W := mkw 0x04c2c380af9b2a8a 0xb9c3c1c1ff1f8f8f

def z799 : W := mkw 0x04fbea0001dae000 0xf6fffe0003fe7000

def z800 : W := mkw 0x04f92a0006d8e000 0xf6ff3e0007fff000

def z801 : W := mkw 0x06fba98aa6f1ce42 0x04b3010ec4e18c03

def z802 : W := mkw 0x02ec01eaa6b40f62 0x7ffc01fec7fc0ff3

def z803 : W := mkw 0x02ec01ea06b40f60 0x7ffc01ffc7fc0fff

def z804 : W := mkw 0x08ee9dfdf0000000 0xa8cfcffff8000000

def z805 : W := mkw 0x001122000048e000 0xf6bf3e0004fff000

def z806 : W := mkw 0x81045671190e31bc 0x894cfef13b1e73fc

def z807 : W := mkw 0x00004200079a2000 0xf24cfe0007fe7000

def z808 : W := mkw 0xc513fe15594bf09d 0x8003fe01f803f00f

def z809 : W := mkw 0x0002c180af030a8a 0x9903c1c1ff038f8f

def z810 : W := mkw 0x08ffbdfdf0040120 0xeefffffff81c0070

def z811 : W := mkw 0x08ffbdfdf0000000 0xc47ffefff8000000

def z812 : W := mkw 0x04fbea0007dbe000 0x567cfe0007fff000

def z813 : W := mkw 0x0813bc15f0000000 0x84b3ff0ff8000000

def z814 : W := mkw 0x00c2c180af030a8a 0xfff3c1c1ffe38f8f

def z815 : W := mkw 0x81045671190e31bc 0xfb4cfff1fb1e7fff

def z816 : W := mkw 0x04fbeb80a7dbea02 0xfeffffc1fffffc03

def z817 : W := mkw 0xc104147750241575 0x0000003e00000070

def z818 : W := mkw 0x8304147b182415fc 0x090000ff380003fc

def z819 : W := mkw 0x00d3e200074be000 0xf6fffe0007fff000

def z820 : W := mkw 0x02ec01ea06b40f60 0x1fb001fe07fc0ff0

def z821 : W := mkw 0x04fbea000fdbe088 0xffffffc1ffffff8f

def z822 : W := mkw 0x08ee9dfdf0000000 0x004ccefe38000000

def z823 : W := mkw 0x830042020fbf3ffe 0x1300000007ffffff

def z824 : W := mkw 0x08d7bdfdf0000000 0xa8c3fffff8000000

def z825 : W := mkw 0x0cfbea0c47dbe000 0xf6fffe0e07fff000

def z826 : W := mkw 0x00eac188af030a8a 0xbdf3c1cfff038f8f

def z827 : W := mkw 0x04fbeb80a7dbe000 0xffffffc1fffffc0f

def z828 : W := mkw 0xc00000020060d455 0xffb3013fc4e3fc7f

def z829 : W := mkw 0x04392b80a8d8ea8a 0x4f3c3fc1f8fc7f8f

def z830 : W := mkw 0x0204147316b40f60 0xfb4cfef13ffc0ff0

def z831 : W := mkw 0x02ec01ea06b40f60 0xfffcc1ff3ffc0ff0

def z832 : W := mkw 0x00116200014ae000 0xf67cfe0003fe7000

def z833 : W := mkw 0x0cffbdfdf0d0c000 0xecfffffff8e00000

def z834 : W := mkw 0x04396a0001dae000 0x563c3e0003fe7000

def z835 : W := mkw 0x04392a0000d8e000 0x46bf3e0004fdf000

def z836 : W := mkw 0xc8113c175060d455 0xffb33f3fc4e3fc7f

def z837 : W := mkw 0x002c147910000000 0xec7cfeff38000000

def z838 : W := mkw 0x04fbea00afdbe08a 0xffffff01fffffc0f

def z839 : W := mkw 0x0813bd9df0000000 0x8003ff0ff8000000

def z840 : W := mkw 0x04fbaa0006d9e000 0x76ff3e0007fdf000

def z841 : W := mkw 0x08ee8de8b0000000 0x084ccffe38000000

def z842 : W := mkw 0x00116200094ae088 0xffffffc1ffffff8f

def z843 : W := mkw 0x022c006a06b40f60 0x7fbc013e07fc0ff0

def z844 : W := mkw 0x04396a0001dae000 0xf6fffe0007fff000

def z845 : W := mkw 0x08ffbdfdf0000000 0x8cb3fffff8000000

def z846 : W := mkw 0xc4eada1747bb3455 0x094ccf3fc31c0c7f

def z847 : W := mkw 0x04fbea0007dbe000 0xe6fffe0003fc7000

def z848 : W := mkw 0x0affbdfdf6940b20 0xfefffffffffc0380

def z849 : W := mkw 0x04fbea000fdbe088 0xf6fffe013ffff00c

def z850 : W := mkw 0x08ffbdfdf040c000 0xfffffffffce3fc0f

def z851 : W := mkw 0x00fbea00079a2000 0xf6fffe0007fe7000

def z852 : W := mkw 0x00028180a8010a8a 0x090301c1f8018f8f

def z853 : W := mkw 0x04fbab80a0d8e000 0xeeffffc1f8fc7000

def z854 : W := mkw 0x0cffbdfdf6d1ca02 0xecfffffffce18c03

def z855 : W := mkw 0x0a13bc17f6b40f60 0x9303fe01fffc0ff0

def z856 : W := mkw 0x0817bc75f0000000 0xecfffffff8000000

def z857 : W := mkw 0x04c2c20007dbe000 0xf2cffe0007fff000

def z858 : W := mkw 0x08ffbdfdf0000000 0x884ffffff8000000

def z859 : W := mkw 0x00c401e206240f60 0x7ffc01fe07fc0ff0

def z860 : W := mkw 0x81041473182415fc 0x090001ff38000ffc

def z861 : W := mkw 0x81117215490e31bc 0xffb3313fc31e73fc

def z862 : W := mkw 0x00c2c180a9030a8a 0xa9c3c1c1f8038f8f

def z863 : W := mkw 0xc8ffbdfdf040d015 0xfefffffffce3f00f

def z864 : W := mkw 0x04fbeb8807dbe000 0xf6ffff0e07fff000

def z865 : W := mkw 0x85ffbc711ed5d1bc 0x0db300f13ce183fc

def z866 : W := mkw 0x0204006206b40f60 0x7ffc01fe07fc0ff0

def z867 : W := mkw 0x08ffbdfdf0000000 0xecfffffff803800f

def z868 : W := mkw 0x02ec01ea06b40f60 0xffff01fe07ff8ff0

def z869 : W := mkw 0x060042020fffefea 0x1300000007ffffff

def z870 : W := mkw 0x04fbeb80afdbea8a 0xffffffc03fffff80

def z871 : W := mkw 0x001120020060c440 0xffb3313fc4e3fc7f

def z872 : W := mkw 0x0400420001dae000 0xf24cfe0003fe7000

def z873 : W := mkw 0x04fbab80a6d9ea02 0x46bf3f00c4fdfc03

def z874 : W := mkw 0x0817bdfdf0000000 0xecb3fffff8000000

def z875 : W := mkw 0x03eec7e8bf9f2baa 0x004ccec03b1c0380

def z876 : W := mkw 0x02ec01ea06b40f60 0x7fff01fec7fd8ff3

def z877 : W := mkw 0x00eac180af930a8a 0xbdf3c1c1ffe38f8f

def z878 : W := mkw 0x02e8018a06b40f60 0x7fb0013e07fc0ff0

def z879 : W := mkw 0xc8ee8deab060d455 0x134ccec03ce3fc7f

def z880 : W := mkw 0x022c01ea00b40f60 0x7f7c01fe03fc0ff0

def z881 : W := mkw 0x0028020000982000 0x463c3e0000fc7000

def z882 : W := mkw 0x04fbeb80a7dbea00 0xffffffc1ffffff80

def z883 : W := mkw 0x00c2c180af030a8a 0x8983c1c1fc038f8f

def z884 : W := mkw 0x08ffbdfdf0000000 0xfefffffffce00000

def z885 : W := mkw 0x083d7c7d5f030a8a 0x553c3e3e07038f8f

def z886 : W := mkw 0x00c2c180af030a8a 0xfbcfc1c1ff1f8f8f

def z887 : W := mkw 0x0817bdfdf0000000 0xe84ffffff8000000

def z888 : W := mkw 0x08fbbd9df0000000 0xe4ffff0ff8000000

def z889 : W := mkw 0x00c2c180af030a8a 0x9143c0c1ff038f8f

def z890 : W := mkw 0x04eacb80af9b2a8a 0xfbcfffc1ff1fff8f

def z891 : W := mkw 0x043bea00a9dbe08a 0xc63ffe01f8fff00f

def z892 : W := mkw 0xc30042020ffefffd 0x1300000007ffffff

def z893 : W := mkw 0x0004147550000000 0xe84cfffff8000000

def z894 : W := mkw 0x02ec05ea16b40f60 0x7ffccffe3ffc0ff0

def z895 : W := mkw 0x89ffbdfdf0041134 0xecfffffff8000070

def z896 : W := mkw 0x022c006a06b40f60 0x7f7c00fe07fc0ff0

def z897 : W := mkw 0x02c0018206b40f60 0x7ff001fe07fc0ff0

def z898 : W := mkw 0x0aec05eab6b40f60 0x7ffc01fe3ffc0ff0

def z899 : W := mkw 0x08ffbdfdf040c000 0xecfffffffce18000

def z900 : W := mkw 0x02ec01ea06b40f60 0x0dfc01fe07fc0ff0

def z901 : W := mkw 0x04392a0000d8e000 0xc63f3e0000fff000

def z902 : W := mkw 0x02ec01eaa6b40f60 0x7ffc01fffffc0ff0

def z903 : W := mkw 0x04fbeb80afdbea8a 0xf7ffff00c7ffff8f

def z904 : W := mkw 0x04eaca0007dbe000 0xf24cfe0007fff000

def z905 : W := mkw 0x0000000200240560 0x7fb0013e07fc0ff0

def z906 : W := mkw 0x8000101300201454 0xffb3313fc4e3fc7f

def z907 : W := mkw 0x04fbeb8007dbea00 0xffffffc1c7ffff8f

def z908 : W := mkw 0x00ec006206b40560 0x7ffc01fe07fc0ff0

def z909 : W := mkw 0x04f92b8006d8ea00 0x7ffc3fc007fc7f80

def z910 : W := mkw 0x04fbea0007dbe000 0xc6bffe0004fff000

def z911 : W := mkw 0x81045671190e31bc 0xc24cfef13b1e73fc

def z912 : W := mkw 0x08ffbdfdf6010000 0xecfffffffc018000

def z913 : W := mkw 0x80005211090a309c 0xfb4cfef13b1e73fc

def z914 : W := mkw 0x88ffbdfdf0001014 0xeefffffff8007070

def z915 : W := mkw 0x0cfbeb88a7dbe000 0xf6fffe0007fff000

def z916 : W := mkw 0x81045671190e31bc 0x934cfec13b1e73fc

def z917 : W := mkw 0x00f9620007dae000 0xf6fffe0007fff000

def z918 : W := mkw 0xc50042020ffff5fd 0x1300000007ffffff

def z919 : W := mkw 0x08ffbdfdf6010a02 0xfdfffffffc038c0f

def z920 : W := mkw 0x04fbea0007dbe000 0xfffffe0107fff00c

def z921 : W := mkw 0x04fbea00afdbea8a 0xf7fffe01ffffff8f

def z922 : W := mkw 0x08ffbdfdf6900a00 0xfffffffffffc0f80

def z923 : W := mkw 0x08fbbd9df0000000 0xecb3ff3ff8000000

def z924 : W := mkw 0x81045671190e31bc 0xea4cfef13b1c73f0

def z925 : W := mkw 0x08ee9dfdf0000000 0xe84cfffff8000000

def z926 : W := mkw 0x083bbc1df0000000 0x8433fe0ff8000000

def z927 : W := mkw 0xc01130174060d455 0x8db3313fc4e3fc7f

def z928 : W := mkw 0x00004180af030a8a 0xb98301c1ff038f8f

def z929 : W := mkw 0x0411620007dbe000 0xf6fffe0007fff000

def z930 : W := mkw 0xc40042020ffbfedf 0x1300000007ffffff

def z931 : W := mkw 0xc30415ff58241ffd 0x090001fff8000fff

def z932 : W := mkw 0x04fbaa0000d8e000 0x467cfe0000fc7000

def z933 : W := mkw 0x00c2c180af030a8a 0xfbc3f1c1ff03ff8f

def z934 : W := mkw 0x00eac180af930a8a 0xb9cfc1c1ff1f8f8f

def z935 : W := mkw 0x00004200010a2000 0xf6fcfe0007fe7000

def z936 : W := mkw 0x02ec01ea06b40f60 0xfffcfffe07fc0ff0

def z937 : W := mkw 0x00004180a9020a8a 0xb9c3c1c1ff038f8f

def z938 : W := mkw 0x043baa0000d9e000 0x463f3e0000fdf000

def z939 : W := mkw 0x00000180a8000a8a 0x890301c1f8038f8f

def z940 : W := mkw 0x00c2c180a9020088 0xb9c3c1c1ff038f8f

def z941 : W := mkw 0xc01130174060d455 0xffffff3fc4e3fc7f

def z942 : W := mkw 0xc53d3e7750fcf575 0x463c3e3e00fc7070

def z943 : W := mkw 0x00e8018206b00e40 0x7ffc01fe07fc0ff0

def z944 : W := mkw 0x04fbeb8007dbe000 0xfeffffc007fff000

def z945 : W := mkw 0xc01130174060d455 0x57b3313ec4e3fc7f

def z946 : W := mkw 0x02ec01ea06b40f60 0xffff01ffc7fc0ff0

def z947 : W := mkw 0x08ffbdfdf6040b20 0xffffffffff1c0ff0

def z948 : W := mkw 0x04fbeb80a7dbe000 0xf6fffec03ffff000

def z949 : W := mkw 0x83c6d5fbbf271ffe 0xb9c3c1ffff038fff

def z950 : W := mkw 0x00fd35fd50000000 0xecfffffff8000000

def z951 : W := mkw 0xc1117215494af09d 0x80033001c003f00f

def z952 : W := mkw 0x04fbeb80afdbea8a 0xf6ffffc0ffffff83

def z953 : W := mkw 0x000040000f030a8a 0xb9c3c1c1ff038f8f

def z954 : W := mkw 0x81044660190e31bc 0xf34cfec03b1e73fc

def z955 : W := mkw 0x020401ea00240f60 0x7ffc01fe07fc0ff0

def z956 : W := mkw 0x06eecbe8af9f2baa 0x004ccec03b1c0380

def z957 : W := mkw 0x08ee8de8b0000000 0x447ccefe38000000

def z958 : W := mkw 0xc913fe15f94af09d 0x8003fe01f803f00f

def z959 : W := mkw 0x04fbea00afdbe08a 0xf6fffe003ffff000

def z960 : W := mkw 0x830415fb10241f74 0x090001fe00000ff0

def z961 : W := mkw 0xc90415fff82415fd 0x090001fff8000fff

def z962 : W := mkw 0x04c2c380afdbea8a 0xfbcfffc1ffffff8f

def z963 : W := mkw 0x04fbea0007dbe000 0xfeffff01c7fff000

def z964 : W := mkw 0x04fbea0007dbe000 0x924ffe0007fff000

def z965 : W := mkw 0x04fbea00a7dbe000 0xf6fffe01fffff000

def z966 : W := mkw 0xc01130174060d455 0x1fb3013fc4e3fc7f

def z967 : W := mkw 0x00ec05e810000000 0x6cfccffe38000000

def z968 : W := mkw 0x08ffbdfdf6010a02 0xfdffffffff018f83

def z969 : W := mkw 0xc8ffbdfdf0001015 0xecfffffff800000f

def z970 : W := mkw 0x04f92a0006d8e000 0x46bc3e0004fc7000

def z971 : W := mkw 0xc104147750241575 0x0900013fc0000c7f

def z972 : W := mkw 0x04c2cb80af0b2a8a 0xb9c3cfc1ff038f8f

def z973 : W := mkw 0x00c2c180af030a8a 0x80c3c1c1ff038f8f

def z974 : W := mkw 0x04f96a0007dae000 0xf6fcfe0007fe7000

def z975 : W := mkw 0x0affbdfdf6940b20 0xfffffffffb1c03f0

def z976 : W := mkw 0x0813bc15f0000000 0xc433fe3ff8000000

def z977 : W := mkw 0x08ffbdfdf0000000 0x0cffcffff8000000

def z978 : W := mkw 0x0c0457fdf7dbe000 0x1a0001fffffff000

def z979 : W := mkw 0x022c01ea06b40f60 0x5f3c01fe07fc0ff0

def z980 : W := mkw 0x04396a0007dbe000 0xf6bf3e0007fff000

def z981 : W := mkw 0x08ffbdfdf0010002 0xecfffffff8018003

def z982 : W := mkw 0xc8ffbdfdf040d015 0xecfffffff8007000

def z983 : W := mkw 0x00ec01e806940120 0x7ffc01fe07fc03f0

def z984 : W := mkw 0x08ffbdfdf6000a00 0xfdffffffff038f8f

def z985 : W := mkw 0x81045671190e31bc 0xfbccfff13f1e7ffc

def z986 : W := mkw 0x0affbdfdf0040b20 0xecfffffff8000380

def z987 : W := mkw 0x08ffbdfdf0000000 0xfdfffffff802000c

def z988 : W := mkw 0x00ec01ea00240560 0x7ffc01fe07fc0ff0

def z989 : W := mkw 0x04fbea0007dbe000 0xf6fffe01c7fff00f

def z990 : W := mkw 0x022c006a00b40560 0x7ffc01fe07fc0ff0

def z991 : W := mkw 0x00c2c180af030a8a 0x8943c1c1fb038f8f

def z992 : W := mkw 0x00c2c380af0b2a8a 0xbbc3c1c1ff1fff8f

def z993 : W := mkw 0x08ffbdfdf0000000 0xec7cfeff38000000

def z994 : W := mkw 0xc1041477582415fd 0x090000ff380003fc

def z995 : W := mkw 0x04392a0000d8e000 0x767c3e0003fc7000

def z996 : W := mkw 0x08ffbdfdf0000000 0xfffffffff8000070

def z997 : W := mkw 0x083d3c7d50000000 0xc43cfe3f38000000

def z998 : W := mkw 0x08ffbdfdf0000000 0xe4fffefe38000000

def z999 : W := mkw 0x0400020000d8e000 0x420c3e0000fc7000

def z1000 : W := mkw 0x08069dfdf0000000 0x0800cffff8000000

def z1001 : W := mkw 0x08ffbdfdf040c000 0xeefffffff8e07000

def z1002 : W := mkw 0x08ffbdfdf0040120 0xecfffffffb1c0380

def z1003 : W := mkw 0x04fbeb80a7dbea02 0xffffffc0c7ffff83

def z1004 : W := mkw 0x02ee81eaa6b40f60 0x7ffcc1fe3ffc0ff0

def z1005 : W := mkw 0xc00414731060d455 0xfb4cfef13ce3fc7f

def z1006 : W := mkw 0x04fbea0007dbe000 0x76fcfe0007fc7000

def z1007 : W := mkw 0x081535fdf0000000 0xecfffffff8000000

def z1008 : W := mkw 0x0813bc15f0000000 0x8803ff3ff8000000

def z1009 : W := mkw 0x04fbeb8007dbea00 0xf6fffec007fff380

def z1010 : W := mkw 0x44fba986e6f1ce43 0x04b3010ec4e18c03

def z1011 : W := mkw 0x08ffbdfdf6010a02 0xecfffffff8000000

def z1012 : W := mkw 0x0cfbeb8ce7dbea02 0xf6ffff0ec7fffc03

def z1013 : W := mkw 0x04fbaa0000d8e000 0xf6fffe0004fff000

def z1014 : W := mkw 0x02ec006a06b40f60 0x77fc003e07fc0ff0

def z1015 : W := mkw 0x00c00180ae000a8a 0xb9c301c1ff038f8f

def z1016 : W := mkw 0x080415fdf0000000 0x8800fffff8000000

def z1017 : W := mkw 0x08ee8de8b0000000 0xecffcffff8000000

def z1018 : W := mkw 0xc8ffbdfdf040d015 0xfdfffffffc03fc0f

def z1019 : W := mkw 0x88ffbdfdf0001014 0xecfffffff802700c

def z1020 : W := mkw 0x00ffa9e8a0000000 0xecfffffff8000000

def z1021 : W := mkw 0x81045671190e31bc 0x4b4cfef13b1c73fc

def z1022 : W := mkw 0x0000000008000088 0xb98301c1fc038f8f

def z1023 : W := mkw 0x08d3bd95f0000000 0xecf3fffff8000000

def z1024 : W := mkw 0xc1045675590e31bd 0xfb4cfef1fb1e73ff

def z1025 : W := mkw 0x00c2c180af030a8a 0xfbc3c1f1ff038fff

def z1026 : W := mkw 0x083fbdfdf0000000 0xcc3ffffff8000000

def z1027 : W := mkw 0xc01130174060d455 0xc6b3313fc4e3fc7f

def z1028 : W := mkw 0x08ee9dfdf0000000 0x6cfccffff8000000

def z1029 : W := mkw 0x04fbeb800fdbea8a 0xffffffc007ffff8f

def z1030 : W := mkw 0x83c455fb1f261ffc 0xb9c0c1ff3f020ffc

def z1031 : W := mkw 0x04fbeb80afdbea8a 0xf7fffec03fffff8f

def z1032 : W := mkw 0x08ffbdfdf0000000 0xfdfffffffb000380

def z1033 : W := mkw 0x0cfbeb8cefdbea8a 0xffffffcfffffff8f

def z1034 : W := mkw 0xc1041473182415fd 0x090000f138000fff

def z1035 : W := mkw 0xc1c6d5f7ff271fff 0xb9c3c1ffff038fff

def z1036 : W := mkw 0x00eac180af030a8a 0xfdffc1c1ff038f8f

def z1037 : W := mkw 0x08fbbc15f0000000 0xecffff3ff8000000

def z1038 : W := mkw 0x0cffbdfdf041c000 0xecfffffff8018000

def z1039 : W := mkw 0x00fba80006d0c000 0xf6fffe0007fff000

def z1040 : W := mkw 0xca0415fff0241f75 0x090001fff8000fff

def z1041 : W := mkw 0x0cffbdfdf6d1c000 0xfefffffffffd8000

def z1042 : W := mkw 0x81045671190e31bc 0xfbcffef13f1ff3fc

def z1043 : W := mkw 0x00044260090e21a8 0xfb4cfef13b1e73fc

def z1044 : W := mkw 0xc01130174060d455 0xffff313fc7fffc7f

def z1045 : W := mkw 0x08ec15fdf0000000 0xecfcfffff8000000

def z1046 : W := mkw 0x88ffbdfdf0001014 0xedfffffff800007c

def z1047 : W := mkw 0xc1004202092e35fd 0x13000000031e7fff

def z1048 : W := mkw 0x04392a0000d8e000 0x563c3e0004fff000

def z1049 : W := mkw 0x08ffadecf0000000 0xe4ffffcef8000000

def z1050 : W := mkw 0x04fbea000fdbea8a 0xffffff01c7ffff8f

def z1051 : W := mkw 0x04fbea0007dbe000 0xc67ffe0003fff000

def z1052 : W := mkw 0x83004202092e3ffc 0x13000000031e7ffc

def z1053 : W := mkw 0x0c392a0c40d8e000 0x463c3e0e00fc7000

def z1054 : W := mkw 0x04fbea0007dbe000 0xffffff0007fffc00

def z1055 : W := mkw 0x00e843800f9a2a88 0xfffcffc13ffe7f8c

def z1056 : W := mkw 0x0cfbab8ce0d8e000 0x46bf3f0ec0fc7000

def z1057 : W := mkw 0xc1045477592615fd 0xb9c3c1ffff038fff

def z1058 : W := mkw 0x04396a0001dae000 0xc63cfe0000fe7000

def z1059 : W := mkw 0x02ee81eaa6b40f60 0xffffc1ffffff8fff

def z1060 : W := mkw 0x04fbea00afdbe08a 0xfffffec1fffff38f

def z1061 : W := mkw 0x08ffbdfdf6000000 0xfcffffffff000000

def z1062 : W := mkw 0x08ffbc7df0000000 0xe4fffe3ff8000000

def z1063 : W := mkw 0x04fbaa0006d9e000 0xe6fffe0004fdf000

def z1064 : W := mkw 0x04fbea0007dbe000 0xf67cfe0003fe7000

def z1065 : W := mkw 0x08ffbdfdf0000000 0xfefffffffb1c0000

def z1066 : W := mkw 0x022c006a06b40f60 0x463c003e03fc03f0

def z1067 : W := mkw 0xc33d367f50fcf575 0x463c3e3e00fc7070

def z1068 : W := mkw 0x08ee9df9b0000000 0xecfcffff38000000

def z1069 : W := mkw 0xca3d3c7f50f4d575 0x463c3e3e00fc7070

def z1070 : W := mkw 0xc93d3e7f506cf575 0x463c3e3e00fc7070

def z1071 : W := mkw 0x0aec0dea16b40f60 0x7ffc0ffe07fc0ff0

def z1072 : W := mkw 0x04392a0000d8e000 0xe6bf3e0000fc7000

def z1073 : W := mkw 0x08ffbdfdf6000a00 0xecfffffffb000380

def z1074 : W := mkw 0x0002c000af030a8a 0xb943c0c1ff038f8f

def z1075 : W := mkw 0x00c2c0000f030088 0xb9c3c1c1ff038f8f

def z1076 : W := mkw 0x030042020fbe2fe8 0x1300000007fc0ff0

def z1077 : W := mkw 0x04fbea00a7dbe002 0xf6fffe00c7fff003

def z1078 : W := mkw 0x083d3c7d50000000 0x447cfefe38000000

def z1079 : W := mkw 0x08ffbdfdf0000000 0x44fffffef8000000

def z1080 : W := mkw 0x04396a0001dbe000 0x463c3e0000fff000

def z1081 : W := mkw 0x083fbc7df0000000 0xec7ffefff8000000

def z1082 : W := mkw 0x08ffbdfdf0900000 0xeefffffff8fc0000

def z1083 : W := mkw 0x04fbea0007dbe000 0xfefffec13ffff000

def z1084 : W := mkw 0x02ec01ea06b50f62 0x7ffc01fe07fd8ff3

def z1085 : W := mkw 0x08ffbdfdf6900000 0xecfffffffce00000

def z1086 : W := mkw 0x04e8420007dbe000 0xf6fcfe0007fff000

def z1087 : W := mkw 0x043bea0001dbe000 0x463cfe0000fc7000

def z1088 : W := mkw 0x04fbea0007dbe000 0xfffffe3007fff070

def z1089 : W := mkw 0x04392a0006d9e000 0x463c3e0004fdf000

def z1090 : W := mkw 0x022c006a00b40560 0x573c003e03fc03f0

def z1091 : W := mkw 0x02ee81eaa6b40f60 0x7fff01fec7fc0ff0

def z1092 : W := mkw 0x04396a0007dbe000 0xf67cfe0007fff000

def z1093 : W := mkw 0x88ffbdfdf0001014 0xfffffffffc03fc7f

def z1094 : W := mkw 0xc10415f7f8241fff 0x090001fff8000fff

def z1095 : W := mkw 0x00c28180ae010a8a 0x39c301c1ff018f8f

def z1096 : W := mkw 0xc1004202096af4dd 0x1300000004e3fc7f

def z1097 : W := mkw 0x88ffbdfdf0041134 0xfffffffffb1e73fc

def z1098 : W := mkw 0xc1117615594af09d 0x8000fe013802700c

def z1099 : W := mkw 0x00ffbdf910000000 0xecffffff38000000

def z1100 : W := mkw 0x04fbeb80afdbea8a 0xf6ffff01fffffc0f

def z1101 : W := mkw 0x81045671190e31bc 0xfb4cfef13f1fffff

def z1102 : W := mkw 0x04fbea000fdbe08a 0xf6fffe0007fff00f

def z1103 : W := mkw 0x81045671190f31be 0xfb4cfef13b1ff3ff

def z1104 : W := mkw 0x08fbbd9df0000000 0xacf3ffcff8000000

def z1105 : W := mkw 0xc113f615f94bf09f 0x8003fe01f803f00f

def z1106 : W := mkw 0x81045671190e31bc 0xfffcffff3b1e73fc

def z1107 : W := mkw 0xc01120064060d455 0x7fb3013ec4e3fc7f

def z1108 : W := mkw 0x0413ea00014be000 0xf6fffe0007fff000

def z1109 : W := mkw 0x06fbeb8807dbea00 0xf6fffe0007fff000

def z1110 : W := mkw 0x020401ea06b40f60 0x7fb001fe07fc0ff0

def z1111 : W := mkw 0x08ffbc7d50000000 0xecfffeff38000000

def z1112 : W := mkw 0xc813bc17f060d455 0x9303fe01fce3fc7f

def z1113 : W := mkw 0x0aee8deab6b40f60 0x134ccec03ffc0ff0

def z1114 : W := mkw 0x04eaca00079b2000 0xf6fcfe0007fe7000

def z1115 : W := mkw 0x0002c000a903008a 0xb9c3c1c1ff038f8f

def z1116 : W := mkw 0x02ee89ea06b40f60 0x7ffccffe07fc0ff0

def z1117 : W := mkw 0x8d13fe15f94bf09c 0x8003fe01f803f00c

def z1118 : W := mkw 0x48ffbdfdf040c001 0xecfffffff8018003

def z1119 : W := mkw 0x00ffbc7550000000 0xecfffffff8000000

def z1120 : W := mkw 0x04fbea0007dbe000 0xf6ffff00c7fffc03

def z1121 : W := mkw 0xc1004202096ef5fd 0x1300000003fe73fc

def z1122 : W := mkw 0x88ffbdfdf040d014 0xfffffffffce3f07c

def z1123 : W := mkw 0x08ffbdfdf0000000 0xc4bfff3ff8000000

def z1124 : W := mkw 0x04396a000fdbea8a 0x573c3e0007ffff8f

def z1125 : W := mkw 0x02e8000206b40f60 0x7ffc013e07fc0ff0

def z1126 : W := mkw 0x080415fdf0000000 0x084ccffff8000000

def z1127 : W := mkw 0x04f96a0007dbe000 0x76fc3e0007fff000

def z1128 : W := mkw 0x04fbea0007dbe000 0x46fffe0007fdf000

def z1129 : W := mkw 0x81041671100c3134 0xfb4cfef13b1c73f0

def z1130 : W := mkw 0x04fbaa0006d9e000 0xf6bf3e0004fff000

def z1131 : W := mkw 0xc8ffbdfdf040d015 0xfffffffff803f07f

def z1132 : W := mkw 0x08eac988af030a8a 0xb9c3c1c1ff038f8f

def z1133 : W := mkw 0x0cffbdfdf6d1c000 0xfefffffffce3f000

def z1134 : W := mkw 0x02ec01ea06b40f60 0x577c00fe07fc0ff0

def z1135 : W := mkw 0x04396a0001dae000 0x467cfe0003fc7000

def z1136 : W := mkw 0x00000180a8000a8a 0x098301c1fc018f8f

def z1137 : W := mkw 0x81045671190e31bc 0xfbcffff1fb1e73fc

def z1138 : W := mkw 0x02ec01ea06b40f60 0x7f7c00fe03fc03f0

def z1139 : W := mkw 0x04fbea000fdbea8a 0xf6fffe0007fff380

def z1140 : W := mkw 0x0015347550000000 0xec7cfeff38000000

def z1141 : W := mkw 0x00045671110e2120 0xfb4cfef13b1e73f0

def z1142 : W := mkw 0x083d3dfdf0000000 0xec7cfffff8000000

def z1143 : W := mkw 0x81045671190e31bc 0x534cfef03b1e73fc

def z1144 : W := mkw 0x8b0415fff8241ffc 0x090001fff8000ffc

def z1145 : W := mkw 0x0affbdfdf6940b20 0xfdffffffff1c0f80

def z1146 : W := mkw 0x81004202092e35fc 0x1300000007fe7ffc

def z1147 : W := mkw 0x08ffbdfdf0000a02 0xecfffffff8000c03

def z1148 : W := mkw 0x04fbea0007dbe000 0x84fffe0007fff000

def z1149 : W := mkw 0x04fbea000fdbe088 0xf7fffe0007fff38c

def z1150 : W := mkw 0x08ffbdfdf040c000 0xecfffffff803f000

def z1151 : W := mkw 0xc01130174060d455 0xfff331ffc7e3ffff

def z1152 : W := mkw 0x00004200014ae000 0xf24cfe0007fff000

def z1153 : W := mkw 0x81045671190e31bc 0x7b4cfef03b1c73f0

def z1154 : W := mkw 0x08ffbdfdf6d0c000 0xfefffffffffff000

def z1155 : W := mkw 0x04fbeb80a7dbea02 0xffffff01c7fffc0f

def z1156 : W := mkw 0x0004006200240560 0x7f7c00fe03fc03f0

def z1157 : W := mkw 0x08fbad8cf0000000 0x04b3cf0ef8000000

def z1158 : W := mkw 0x0affbdfdf0940120 0xecfffffff81c0000

def z1159 : W := mkw 0x08ee8decf0000000 0x004ccfcef8000000

def z1160 : W := mkw 0x043bea0001dbe000 0xf6bffe0004fff000

def z1161 : W := mkw 0x00284200019a2000 0xf67cfe0003fe7000

def z1162 : W := mkw 0x02ee81ea06b40f60 0xffffc1fe07fc0ff0

def z1163 : W := mkw 0x043bea0007dbe000 0xd63ffe0007fff000

def z1164 : W := mkw 0x00d7b5f5f0000000 0xecfffffff8000000

def z1165 : W := mkw 0x08ffbdfdf0000000 0xfdfffffffc000c00

def z1166 : W := mkw 0x04fbea0001dbe000 0xe6fffe0000fff000

def z1167 : W := mkw 0x04fbea000fdbea8a 0xfffffec13fffff8f

def z1168 : W := mkw 0x04fbea0447dbe000 0xf6ffff0ec7fff000

def z1169 : W := mkw 0x08fd3dfd50000000 0xecfcffff38000000

def z1170 : W := mkw 0x8304147318241ffc 0x090000f138000ffc

def z1171 : W := mkw 0x81045671190e31bc 0xf24cfef03b1e73f0

def z1172 : W := mkw 0x001122000048e000 0x463c3e0000fc7000

def z1173 : W := mkw 0x81ec43e8090e31bc 0x7ffc01fe031e73fc

def z1174 : W := mkw 0x08ffbdfdf0000000 0x84ffffcff8000000

def z1175 : W := mkw 0xc10042020f6fffff 0x1300000007ffffff

def z1176 : W := mkw 0x04fbea0007dbe000 0xfeffff3e07fff000

def z1177 : W := mkw 0x04fbaa0006d8e000 0xf6fffe0007fc7000

def z1178 : W := mkw 0x08ffbdfdf0000000 0xecfffffffc018c03

def z1179 : W := mkw 0x083fbc7df0000000 0x443cfe3e38000000

def z1180 : W := mkw 0x00c2c180af030a8a 0xf9cfffc1ff038f8f

def z1181 : W := mkw 0x022c006a00b40560 0x467c00fe03fc03f0

def z1182 : W := mkw 0xc01134175060d455 0xffb3ff3ffce3fc7f

def z1183 : W := mkw 0x00c2c180af030a8a 0x09c3c1c1ff018f8f

def z1184 : W := mkw 0x04392a0000d8e000 0xe67cfe0000fc7000

def z1185 : W := mkw 0x02ec01ea06b40f60 0x4f7c01fe03fc0ff0

def z1186 : W := mkw 0x81045671190e31bc 0xfffcfef13ffe73fc

def z1187 : W := mkw 0x08ffbdfdf0000a00 0xedfffffff8000f80

def z1188 : W := mkw 0x04fbea000fdbe088 0xf6fffec03ffff380

def z1189 : W := mkw 0xc01130174060d455 0xfff3f1fffce3fc7f

def z1190 : W := mkw 0x02ec01ea06b40f60 0x46fc01fe07fc0ff0

def z1191 : W := mkw 0x00c2c180af030a8a 0x198301c1ff038f8f

def z1192 : W := mkw 0x0aee8deab6b40f60 0xffffcffffffc0ff0

def z1193 : W := mkw 0x08ffadecf0000000 0x6cffcffef8000000

def z1194 : W := mkw 0x04fbea0007dbea02 0xf6fffe0007fffc03

def z1195 : W := mkw 0x0002c180a9030a8a 0xb983c1c1fc038f8f

def z1196 : W := mkw 0x02ec01ea06b40f60 0x6efc01fe03fc03f0

def z1197 : W := mkw 0x00eac200079b2000 0xf6fffe0007fff000

def z1198 : W := mkw 0x08ffbdfdf0000000 0x4c7cfffff8000000

def z1199 : W := mkw 0x04fbea0007dbe000 0x56bf3e0007fff000

def z1200 : W := mkw 0x04fbea0007dbe000 0xf7fffe0007fffc0f

def z1201 : W := mkw 0x0efba98ee6f1ce40 0x04b3010ec4e18c00

def z1202 : W := mkw 0x08ffbdfdf6000a00 0xecfffffffc000c00

def z1203 : W := mkw 0x00e8020006982000 0x76fc3e0007fc7000

def z1204 : W := mkw 0x00c2c180af930a8a 0xbbc3c1c1ffff8f8f

def z1205 : W := mkw 0x0cfbeb8ce7dbe000 0xfeffffcffffff000

def z1206 : W := mkw 0x8004147110041134 0xfb4cfef13b1e73fc

def z1207 : W := mkw 0x04392a0000d8e000 0x76bc3e0004fc7000

def z1208 : W := mkw 0x04392a0006d8e000 0x563c3e0007fc7000

def z1209 : W := mkw 0x00d3e380af4bea8a 0xffffffc1ffffff8f

def z1210 : W := mkw 0x02ee81eaa6b50f62 0xffff01ffc7ff8fff

def z1211 : W := mkw 0x08ffade8b0000000 0xecfffffe38000000

def z1212 : W := mkw 0x04f92a0000d8e000 0x66fc3e0000fc7000

def z1213 : W := mkw 0x02ec01ea06b40f60 0x57bc013e07fc0ff0

def z1214 : W := mkw 0x04f92a0006d8e000 0x467c3e0003fc7000

def z1215 : W := mkw 0x000415f910000000 0xe84cffff38000000

def z1216 : W := mkw 0x02ee81ea06b50f60 0x7fff01fe07fd8ff0

def z1217 : W := mkw 0x0cffbdfdf6910000 0xecfffffff8000000

def z1218 : W := mkw 0x04fbeb80afdbea8a 0xfffffec13ffff38c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z8,z5,z6]),(0,[z0,z1,z3,z4,z9,z5,z6]),(0,[z10,z0,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z12,z5,z6])],[(0,[z13,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z14,z6])],[(1,[z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z16,z17,z4,z5,z6]),(0,[z0,z18,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z20,z6]),(0,[z0,z1,z3,z4,z5,z6,z21]),(0,[z0,z1,z3,z4,z5,z6,z22])],[(0,[z0,z1,z3,z4,z23,z5,z6]),(0,[z0,z1,z3,z24,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z25,z22])],[(0,[z0,z1,z3,z4,z5,z26,z6]),(0,[z27,z1,z3,z4,z5,z28,z6]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z0,z30,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z31,z6]),(0,[z0,z1,z3,z4,z5,z6,z32])],[(0,[z33,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z34,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z36,z5,z6]),(1,[z19,z1,z3,z4,z5,z37]),(0,[z0,z38,z1,z3,z39,z5,z6]),(0,[z0,z1,z40,z3,z4,z5,z41]),(1,[z0,z1,z42,z4,z5,z6])],[(0,[z0,z1,z17,z4,z12,z5,z6]),(0,[z0,z1,z3,z4,z5,z43,z6])]],
   [[(0,[z0,z1,z44,z3,z4,z5,z6]),(0,[z45,z0,z1,z3,z4,z5,z6]),(0,[z0,z46,z1,z3,z12,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z47]),(0,[z48,z0,z1,z3,z5,z49,z6])],[(0,[z0,z1,z3,z50,z51,z5,z6]),(0,[z0,z1,z3,z4,z52,z5,z6]),(0,[z48,z0,z1,z3,z4,z12,z6]),(1,[z48,z0,z1,z3,z53,z6])],[(0,[z0,z1,z3,z4,z54,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z55]),(0,[z0,z1,z3,z4,z5,z6,z56])],[(0,[z57,z0,z1,z58,z4,z5,z6]),(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z60,z6]),(0,[z61,z0,z1,z3,z4,z5,z6])],[(1,[z0,z62,z3,z4,z5,z6]),(0,[z0,z1,z3,z39,z12,z5,z6]),(0,[z0,z1,z3,z4,z63,z5,z6])],[(0,[z0,z64,z1,z17,z4,z5,z6]),(0,[z0,z65,z1,z3,z4,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z67,z6]),(0,[z0,z1,z3,z4,z5,z68,z6]),(0,[z1,z3,z4,z69,z5,z70,z6]),(0,[z0,z71,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z72,z5,z49,z6])],[(1,[z1,z58,z17,z4,z5,z6]),(0,[z0,z1,z3,z73,z51,z5,z6]),(1,[z74,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z75,z6]),(0,[z76,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z36,z12,z5,z6]),(0,[z0,z77,z1,z3,z4,z69,z6]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z79,z5,z6]),(0,[z0,z1,z80,z4,z81,z5,z6])],[(0,[z82,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z83]),(0,[z0,z1,z84,z4,z81,z5,z6]),(0,[z0,z85,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z87,z5,z6])],[(0,[z88,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z89]),(0,[z0,z1,z3,z90,z4,z5,z6]),(1,[z0,z91,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z92,z5,z6])],[(0,[z0,z93,z3,z4,z94,z5,z6]),(0,[z95,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z96,z3,z4,z5,z6]),(0,[z0,z97,z1,z3,z4,z5,z6])],[(0,[z98,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z0,z1,z3,z100,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z102]),(0,[z0,z1,z3,z4,z103,z5,z6]),(0,[z0,z1,z3,z104,z5,z6,z105]),(1,[z106,z0,z1,z4,z107,z6]),(0,[z0,z1,z3,z4,z5,z6,z105]),(0,[z0,z77,z1,z3,z4,z108,z5])],[(1,[z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z109,z4,z5,z6])],[(0,[z48,z0,z1,z58,z4,z5,z6]),(0,[z35,z0,z110,z3,z4,z5,z6]),(0,[z0,z1,z111,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z112,z5,z6]),(0,[z113,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z114,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z115]),(0,[z0,z1,z3,z116,z4,z5,z6]),(0,[z0,z1,z3,z5,z53,z6,z105]),(0,[z0,z1,z3,z4,z117,z5,z6])],[(0,[z0,z1,z118,z17,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z28,z6]),(0,[z0,z1,z58,z4,z5,z49,z6]),(0,[z0,z1,z3,z73,z36,z5,z6])]],
   [[(0,[z0,z119,z1,z58,z4,z5,z6])],[(0,[z0,z120,z1,z3,z4,z5,z6]),(0,[z121,z0,z122,z3,z4,z5,z6]),(0,[z0,z1,z80,z3,z4,z107,z6]),(1,[z0,z1,z3,z5,z6,z123])],[(0,[z124,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z17,z4,z5,z28,z6]),(1,[z0,z1,z111,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z126,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z70,z6]),(0,[z0,z1,z3,z127,z4,z5,z6]),(0,[z106,z86,z0,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z128,z5,z6]),(0,[z0,z64,z1,z129,z4,z5,z6]),(0,[z0,z122,z1,z3,z4,z130,z6]),(1,[z0,z1,z3,z5,z131,z6]),(0,[z0,z1,z4,z81,z5,z107,z6]),(0,[z0,z1,z3,z4,z5,z6,z132])],[(0,[z0,z133,z1,z3,z4,z5,z6]),(0,[z134,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z51,z72,z5,z6]),(0,[z7,z135,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z136,z6]),(0,[z0,z1,z137,z3,z4,z5,z6]),(0,[z138,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z32,z22])],[(1,[z139,z1,z3,z36,z5,z6]),(0,[z0,z1,z140,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z141,z5,z6])],[],[(0,[z0,z1,z3,z4,z142,z5,z6]),(1,[z143,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z17,z4,z5,z53,z6]),(0,[z144,z0,z1,z3,z4,z5,z6]),(0,[z0,z145,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z146,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z147]),(0,[z0,z1,z3,z4,z148,z5,z6]),(0,[z0,z1,z4,z104,z81,z5,z6]),(0,[z0,z1,z3,z4,z149,z5,z6])],[(0,[z0,z1,z58,z17,z4,z5,z6]),(1,[z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z3,z151,z72,z5,z6]),(0,[z0,z1,z3,z4,z5,z152,z6]),(1,[z0,z1,z80,z4,z81,z6]),(0,[z0,z1,z3,z4,z87,z5,z6]),(0,[z0,z153,z1,z3,z4,z5,z6])],[(0,[z0,z1,z17,z4,z5,z154,z6]),(0,[z0,z1,z3,z155,z4,z5,z6]),(0,[z11,z0,z1,z3,z72,z5,z6]),(0,[z0,z1,z3,z156,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z157]),(0,[z0,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z158,z3,z4,z5,z6]),(1,[z0,z1,z3,z151,z12,z6])],[(0,[z0,z1,z159,z3,z4,z5,z6]),(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z64,z1,z58,z4,z5,z6]),(0,[z27,z0,z1,z126,z4,z5,z6]),(0,[z0,z1,z161,z3,z4,z5,z6]),(0,[z0,z162,z1,z3,z12,z5,z6]),(0,[z0,z38,z1,z4,z104,z5,z6]),(0,[z0,z1,z40,z3,z4,z5,z6]),(1,[z0,z1,z3,z163,z5,z6])],[(0,[z0,z1,z3,z4,z5,z70,z6]),(0,[z0,z1,z3,z4,z5,z164,z6]),(0,[z121,z0,z1,z3,z165,z5,z6]),(0,[z0,z1,z3,z4,z166,z5,z6]),(0,[z0,z1,z3,z4,z167,z5,z6])],[(0,[z0,z1,z3,z36,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z168])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z58,z80,z4,z5,z6]),(0,[z169,z0,z170,z3,z4,z5,z6]),(0,[z57,z0,z3,z4,z72,z5,z6]),(0,[z0,z171,z1,z3,z4,z5,z6]),(0,[z172,z0,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z41])]],
   [[(0,[z0,z1,z3,z4,z5,z173,z6]),(0,[z174,z0,z1,z17,z4,z5,z6]),(0,[z0,z77,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z175]),(0,[z0,z1,z176,z3,z4,z5,z6]),(0,[z0,z177,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z80,z4,z5,z6])],[(0,[z0,z1,z3,z4,z178,z5,z6]),(0,[z0,z1,z3,z4,z179,z5,z6]),(0,[z180,z0,z1,z3,z4,z5,z6]),(0,[z0,z64,z1,z4,z81,z5,z6]),(0,[z181,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z142,z5,z182,z6])],[],[(0,[z0,z1,z17,z4,z5,z130,z6]),(0,[z0,z1,z17,z4,z183,z5,z6]),(0,[z0,z1,z3,z4,z184,z5,z6]),(0,[z0,z46,z1,z3,z72,z5,z6])],[(0,[z0,z1,z3,z4,z185,z5,z6]),(0,[z0,z1,z17,z39,z4,z5,z6]),(0,[z139,z35,z1,z3,z4,z5,z6]),(0,[z0,z186,z1,z3,z4,z5,z6])],[(0,[z187,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z6])],[(0,[z0,z1,z3,z4,z5,z189,z6]),(0,[z169,z0,z1,z3,z190,z5,z6]),(0,[z0,z1,z3,z4,z5,z191,z6]),(0,[z0,z1,z3,z4,z5,z192,z6]),(0,[z0,z1,z3,z50,z5,z53,z6])],[(0,[z0,z1,z3,z39,z72,z5,z6]),(0,[z0,z1,z3,z4,z5,z193,z6])]],
   [[(0,[z0,z1,z17,z4,z5,z194,z6]),(0,[z0,z1,z58,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z195,z6]),(0,[z0,z1,z3,z196,z4,z5,z6]),(0,[z0,z197,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z198,z6])],[(0,[z19,z27,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z190,z5,z6]),(0,[z0,z1,z3,z199,z4,z5,z6]),(1,[z0,z122,z3,z4,z94,z6]),(0,[z200,z0,z1,z4,z5,z6,z22])],[(0,[z169,z1,z3,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z201,z6]),(0,[z0,z202,z1,z3,z4,z5,z6]),(0,[z203,z0,z1,z3,z4,z5,z6]),(0,[z0,z204,z1,z3,z4,z5,z6])],[(0,[z0,z205,z3,z4,z94,z5,z6]),(0,[z0,z206,z1,z3,z4,z5,z6]),(0,[z19,z0,z62,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z207,z5,z6]),(0,[z0,z1,z3,z4,z5,z208,z6])],[(0,[z209,z0,z1,z3,z4,z5,z6]),(0,[z210,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z211])],[(0,[z212,z0,z1,z3,z4,z5,z6])],[(0,[z93,z1,z205,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z213,z6]),(0,[z214,z0,z1,z3,z4,z5,z6]),(0,[z121,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z215,z6])],[(0,[z216,z0,z1,z3,z4,z5,z6]),(0,[z57,z0,z1,z17,z4,z5,z6]),(0,[z0,z122,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z217,z4,z5,z6]),(0,[z0,z1,z218,z3,z4,z5,z6]),(0,[z0,z219,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z220,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z221,z5,z6]),(0,[z0,z1,z58,z4,z5,z6,z37])],[(0,[z0,z1,z58,z58,z4,z5,z6]),(0,[z0,z7,z1,z129,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z5,z6])],[(0,[z106,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z223,z6]),(0,[z0,z1,z3,z4,z5,z6,z224])],[(0,[z225,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z73,z4,z5,z6]),(0,[z0,z226,z1,z3,z4,z5,z6]),(0,[z227,z0,z1,z3,z4,z5,z6]),(0,[z0,z228,z1,z3,z4,z5,z6]),(0,[z0,z1,z80,z3,z229,z5,z6]),(0,[z0,z230,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z231,z5,z6])],[(0,[z76,z0,z1,z17,z4,z5,z6]),(0,[z19,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z169,z0,z1,z3,z4,z70,z6]),(0,[z0,z232,z1,z3,z4,z5,z6])],[(0,[z0,z93,z119,z3,z4,z5,z6]),(0,[z0,z1,z3,z233,z4,z5,z6])],[(0,[z234,z0,z1,z235,z4,z5,z6]),(0,[z0,z1,z3,z236,z4,z5,z6]),(1,[z0,z1,z237,z4,z5,z6]),(0,[z0,z1,z58,z4,z81,z5,z6]),(0,[z238,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z36,z4,z51,z5,z6]),(0,[z0,z239,z1,z3,z4,z5,z6]),(0,[z240,z0,z1,z3,z4,z5,z6])],[(0,[z95,z1,z3,z17,z4,z5,z6]),(0,[z0,z1,z241,z17,z4,z5,z6]),(0,[z0,z0,z1,z58,z4,z5,z6]),(0,[z174,z0,z1,z58,z4,z5,z6])]],
   [[(0,[z0,z93,z3,z4,z5,z6,z242]),(0,[z243,z0,z1,z3,z4,z5,z6]),(0,[z244,z0,z1,z3,z4,z5,z6]),(1,[z0,z245,z3,z4,z5,z6]),(0,[z0,z1,z3,z246,z4,z5,z6]),(0,[z0,z1,z3,z104,z12,z5,z6]),(0,[z0,z1,z3,z50,z104,z5,z6]),(0,[z0,z1,z3,z4,z12,z5,z6]),(0,[z247,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z235,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z248,z6])],[(0,[z48,z0,z1,z17,z4,z5,z6]),(0,[z0,z7,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z249]),(0,[z0,z1,z3,z250,z4,z5,z6]),(0,[z0,z1,z3,z251,z4,z5,z6]),(1,[z0,z3,z4,z252,z5,z6])],[(0,[z0,z253,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z81,z5,z254,z6]),(0,[z255,z0,z1,z3,z4,z5,z6])],[(0,[z0,z119,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z6]),(0,[z0,z1,z257,z3,z4,z5,z6])],[(0,[z0,z1,z58,z4,z94,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z258])],[(0,[z259,z0,z1,z3,z4,z5,z6]),(0,[z0,z260,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z73,z104,z5,z6]),(0,[z0,z77,z1,z3,z4,z142,z6])],[(0,[z174,z0,z1,z3,z4,z5,z28]),(0,[z0,z162,z1,z3,z72,z5,z6])]],
   [[(1,[z0,z1,z261,z4,z5,z6]),(0,[z262,z0,z1,z3,z4,z5,z6])],[(0,[z263,z0,z1,z3,z4,z5,z6]),(0,[z0,z264,z1,z3,z4,z5,z6])],[(0,[z0,z1,z58,z265,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z266]),(0,[z0,z1,z3,z4,z267,z5,z6]),(0,[z0,z1,z3,z268,z4,z5,z6]),(0,[z86,z0,z1,z40,z4,z5,z6])],[(0,[z234,z0,z1,z3,z269,z5,z6]),(1,[z35,z1,z3,z51,z5,z6]),(0,[z0,z1,z3,z270,z4,z5,z6]),(0,[z0,z46,z1,z3,z50,z5,z6]),(0,[z0,z1,z3,z4,z271,z5,z6]),(0,[z0,z1,z40,z3,z4,z5,z254]),(0,[z0,z1,z272,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z273])],[(0,[z0,z274,z1,z58,z4,z5,z6]),(0,[z0,z1,z44,z58,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z275,z6])],[(0,[z160,z1,z3,z4,z5,z70,z6]),(0,[z0,z1,z58,z4,z276,z5,z6]),(0,[z169,z0,z186,z3,z4,z5,z6]),(0,[z0,z1,z277,z3,z4,z5,z6]),(0,[z0,z3,z4,z94,z5,z154,z6]),(0,[z0,z278,z1,z3,z4,z5,z6])],[(0,[z0,z279,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z280,z4,z5,z6]),(0,[z0,z1,z3,z281,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z282,z6]),(0,[z0,z1,z3,z4,z283,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z284,z5,z6]),(0,[z0,z285,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z229,z5,z6]),(0,[z0,z1,z286,z3,z4,z5,z6])],[(0,[z0,z1,z40,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z287,z5,z6]),(0,[z0,z1,z288,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z182,z6]),(1,[z0,z1,z3,z4,z142,z22])],[(0,[z0,z289,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z290,z5,z6]),(0,[z291,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z6,z41]),(0,[z169,z0,z1,z3,z292,z5,z6]),(0,[z0,z293,z1,z3,z4,z5,z6]),(0,[z294,z1,z40,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z295,z6]),(0,[z0,z1,z17,z4,z5,z28,z6]),(0,[z0,z1,z17,z4,z5,z49,z6]),(0,[z19,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z296,z4,z5,z6]),(0,[z0,z1,z3,z36,z50,z5,z6]),(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z297,z5,z6]),(0,[z298,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z299,z3,z4,z5,z6])],[(1,[z0,z7,z129,z4,z5,z6]),(1,[z0,z300,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z301,z5,z6])],[(0,[z302,z0,z1,z3,z4,z5,z6]),(0,[z303,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z304,z4,z5,z6]),(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z306,z4,z5,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z19,z174,z1,z3,z4,z5,z6]),(0,[z307,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z94,z5,z130,z6])],[(1,[z0,z1,z277,z4,z5,z6]),(0,[z106,z0,z7,z1,z4,z5,z6]),(0,[z0,z46,z1,z3,z73,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z308]),(0,[z0,z1,z84,z3,z104,z5,z6]),(0,[z0,z1,z3,z4,z309,z5,z6]),(0,[z74,z0,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z110,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z8,z5,z6]),(0,[z0,z1,z310,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z4,z5,z6]),(0,[z0,z1,z311,z3,z4,z5,z6])],[(0,[z35,z1,z3,z4,z51,z5,z6]),(0,[z0,z122,z1,z3,z4,z94,z6]),(0,[z0,z1,z3,z4,z5,z53,z6]),(0,[z11,z0,z1,z3,z4,z5,z6])],[(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z4,z5,z105])],[(0,[z313,z0,z1,z3,z4,z5,z6]),(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z245,z3,z4,z5,z6]),(0,[z27,z1,z3,z4,z5,z70,z6]),(0,[z19,z0,z1,z3,z4,z5,z28]),(0,[z0,z315,z1,z3,z4,z5,z6]),(0,[z174,z0,z1,z261,z4,z5,z6]),(0,[z0,z1,z3,z316,z4,z5,z6]),(1,[z0,z1,z4,z317,z5,z6])],[(0,[z0,z93,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z107,z6]),(0,[z0,z1,z3,z4,z5,z154,z6]),(0,[z0,z1,z3,z4,z318,z5,z6])],[(0,[z0,z1,z3,z4,z319,z5,z6]),(0,[z106,z0,z1,z4,z5,z107,z6]),(0,[z0,z1,z3,z4,z252,z5,z6])],[(0,[z0,z1,z17,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z320]),(0,[z0,z77,z1,z3,z4,z70,z6]),(0,[z0,z1,z3,z4,z5,z321,z6]),(0,[z121,z0,z1,z3,z4,z130,z6]),(0,[z0,z300,z1,z4,z5,z130,z6])],[(0,[z0,z1,z3,z4,z5,z322,z6]),(0,[z0,z1,z3,z4,z5,z323,z6]),(0,[z0,z1,z3,z4,z5,z324,z6]),(0,[z0,z1,z325,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z326,z6])]],
   [[(0,[z327,z0,z1,z3,z4,z5,z6]),(0,[z0,z205,z3,z4,z5,z6,z242]),(0,[z0,z328,z1,z3,z4,z5,z6]),(0,[z0,z1,z329,z3,z4,z5,z6]),(0,[z106,z74,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z330,z6])],[(0,[z0,z331,z1,z3,z4,z5,z6]),(0,[z0,z1,z140,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z332,z5,z6]),(0,[z0,z46,z1,z3,z4,z5,z6]),(0,[z0,z333,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z5,z49,z6]),(0,[z0,z1,z3,z4,z5,z6,z334])],[(0,[z0,z335,z1,z3,z4,z5,z6]),(0,[z336,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z50,z5,z49])],[(0,[z0,z122,z1,z17,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z5,z6]),(0,[z0,z337,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z72,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z339,z6])],[(0,[z0,z1,z3,z4,z183,z5,z6]),(0,[z139,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z340,z5,z6]),(0,[z0,z1,z3,z4,z5,z130,z6]),(0,[z0,z300,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z341])],[(0,[z0,z342,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z343,z5,z6]),(1,[z0,z1,z3,z5,z6,z115]),(0,[z0,z1,z3,z39,z4,z5,z6])],[(0,[z160,z95,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z344,z5,z6])],[(0,[z234,z0,z1,z3,z4,z5,z6]),(0,[z0,z38,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z345,z5,z6]),(0,[z0,z91,z1,z3,z5,z130,z6]),(0,[z0,z1,z3,z4,z5,z6,z346])]],
   [[(0,[z0,z1,z3,z347,z4,z5,z6]),(0,[z160,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z348,z6]),(0,[z0,z1,z3,z4,z5,z349,z6]),(0,[z0,z1,z84,z3,z39,z5,z6])],[(0,[z0,z1,z3,z4,z350,z5,z6]),(0,[z0,z1,z3,z4,z351,z5,z6]),(0,[z0,z352,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z154,z6,z115]),(0,[z0,z1,z3,z4,z5,z6,z353]),(0,[z0,z1,z3,z354,z4,z5,z6]),(0,[z0,z1,z355,z3,z4,z5,z6])],[(0,[z356,z0,z1,z17,z4,z5,z6]),(0,[z19,z160,z1,z3,z4,z5,z6]),(0,[z174,z0,z1,z277,z4,z5,z6]),(0,[z357,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z72,z5,z154,z6])],[(0,[z0,z1,z205,z3,z4,z5,z6]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z0,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z17,z4,z5,z6,z242]),(0,[z0,z359,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z131,z130,z6]),(0,[z0,z1,z3,z4,z104,z5,z6])],[(0,[z0,z1,z17,z4,z5,z360,z6]),(0,[z0,z1,z17,z129,z4,z5,z6]),(0,[z294,z0,z1,z3,z4,z5,z6])],[(0,[z361,z0,z1,z3,z4,z5,z6]),(1,[z327,z93,z3,z4,z5,z6]),(0,[z48,z0,z1,z3,z51,z5,z6]),(0,[z0,z1,z362,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z25])],[(0,[z0,z1,z3,z4,z363,z5,z6]),(0,[z0,z7,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z364,z6]),(0,[z365,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z4,z5,z6])],[(0,[z0,z1,z3,z4,z366,z5,z6]),(0,[z0,z1,z3,z4,z367,z5,z6]),(0,[z48,z11,z0,z1,z3,z5,z6]),(1,[z368,z0,z1,z3,z5,z6])]],
   [[(0,[z1,z3,z17,z4,z5,z70,z6]),(0,[z0,z119,z3,z4,z5,z154,z6])],[(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z15,z3,z4,z5,z6]),(0,[z0,z1,z3,z370,z4,z5,z6]),(0,[z27,z0,z1,z371,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z372]),(0,[z0,z1,z373,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z374,z5,z6]),(1,[z0,z1,z3,z87,z5,z6]),(0,[z0,z1,z3,z4,z375,z5,z6]),(1,[z11,z0,z1,z3,z5,z105])],[(0,[z0,z1,z58,z4,z5,z6,z242]),(1,[z0,z1,z217,z4,z5,z6]),(0,[z376,z0,z1,z3,z4,z5,z6]),(1,[z0,z64,z140,z4,z5,z6]),(0,[z0,z1,z3,z50,z151,z5,z6]),(0,[z0,z1,z3,z4,z377,z5,z6])],[(0,[z0,z1,z3,z4,z5,z20,z6]),(1,[z0,z119,z3,z4,z5,z154]),(0,[z0,z378,z1,z3,z4,z5,z6]),(0,[z379,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z17,z4,z5,z6,z37]),(0,[z0,z1,z380,z3,z4,z5,z6]),(0,[z381,z0,z1,z3,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z73,z4,z5,z6]),(0,[z0,z1,z3,z4,z382,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z383])],[(0,[z0,z1,z17,z4,z108,z5,z6]),(0,[z35,z0,z1,z34,z4,z5,z6]),(0,[z48,z0,z1,z3,z36,z5,z6]),(0,[z1,z3,z4,z69,z5,z28,z6]),(1,[z0,z1,z3,z350,z5,z6]),(0,[z376,z7,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z384,z4,z5,z6]),(0,[z0,z1,z3,z151,z4,z53,z6]),(0,[z0,z1,z3,z4,z108,z6,z22])],[(0,[z0,z1,z385,z3,z4,z5,z6]),(0,[z0,z1,z3,z386,z4,z5,z6]),(0,[z387,z0,z1,z3,z4,z5,z6]),(1,[z388,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z389,z5,z6]),(0,[z0,z1,z3,z73,z5,z53,z6]),(0,[z0,z1,z3,z4,z5,z6,z390])]],
   [[(0,[z169,z1,z3,z4,z69,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z391]),(0,[z0,z1,z3,z73,z151,z5,z6]),(0,[z0,z1,z3,z4,z5,z392,z6]),(0,[z0,z1,z3,z4,z393,z5,z6]),(0,[z0,z1,z151,z4,z317,z5,z6])],[(0,[z394,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z395])],[(0,[z327,z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z17,z4,z81,z5,z6]),(0,[z121,z0,z1,z58,z4,z5,z6]),(1,[z0,z1,z396,z4,z5,z6]),(0,[z0,z1,z3,z5,z49,z6,z105])],[(0,[z0,z397,z1,z3,z4,z5,z6]),(1,[z174,z1,z3,z4,z5,z28]),(0,[z0,z398,z1,z3,z4,z5,z6]),(0,[z0,z77,z1,z3,z4,z108,z6])],[(1,[z0,z1,z235,z4,z5,z6]),(0,[z399,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z51,z5,z6]),(0,[z0,z1,z58,z4,z108,z5,z6]),(0,[z0,z1,z3,z4,z5,z400,z6]),(0,[z0,z1,z3,z4,z401,z5,z6])],[(0,[z160,z327,z1,z3,z4,z5,z6]),(0,[z0,z402,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z4,z5,z254,z6]),(0,[z0,z1,z3,z4,z403,z5,z6]),(0,[z0,z1,z404,z3,z4,z5,z6]),(1,[z376,z1,z3,z4,z5,z6]),(0,[z0,z162,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z405,z22])],[(0,[z0,z1,z406,z3,z4,z5,z6]),(0,[z57,z0,z3,z4,z94,z5,z6]),(0,[z0,z1,z3,z407,z4,z5,z6]),(0,[z408,z0,z1,z3,z4,z5,z6])],[(0,[z0,z119,z205,z3,z4,z5,z6]),(0,[z0,z409,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z410,z6])]],
   [[(0,[z0,z1,z3,z4,z411,z5,z6]),(0,[z0,z1,z3,z412,z4,z5,z6]),(1,[z0,z1,z3,z190,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z37]),(0,[z0,z1,z3,z4,z5,z413,z6]),(0,[z0,z1,z3,z414,z4,z5,z6]),(0,[z0,z1,z3,z415,z4,z5,z6]),(0,[z0,z1,z84,z39,z4,z5,z6]),(0,[z0,z1,z3,z163,z142,z5,z6])],[(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z0,z1,z17,z4,z94,z5,z6]),(0,[z0,z417,z1,z3,z4,z5,z6]),(0,[z0,z418,z1,z3,z4,z5,z6]),(0,[z419,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z420,z5,z6])],[(1,[z0,z1,z3,z100,z5,z6]),(1,[z0,z1,z3,z4,z421,z6]),(0,[z422,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z154,z6,z242]),(0,[z0,z1,z3,z4,z423,z5,z6]),(1,[z0,z1,z4,z5,z6,z32]),(0,[z0,z1,z3,z4,z424,z5,z6])],[(0,[z0,z425,z1,z3,z4,z5,z6]),(0,[z244,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z254,z6]),(0,[z426,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z80,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z427]),(0,[z368,z0,z1,z3,z4,z5,z6])],[(1,[z1,z205,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z428,z5,z6]),(0,[z0,z1,z429,z3,z4,z5,z6]),(0,[z0,z1,z84,z3,z4,z5,z6]),(0,[z106,z0,z1,z4,z5,z254,z6])],[(1,[z0,z162,z3,z72,z5,z6]),(0,[z430,z0,z1,z3,z4,z5,z6]),(0,[z57,z0,z1,z3,z4,z5,z242]),(0,[z0,z1,z3,z4,z5,z6,z431]),(0,[z0,z1,z3,z4,z5,z432,z6]),(0,[z0,z1,z433,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z50,z5,z6])],[(0,[z0,z1,z17,z4,z5,z6,z22]),(1,[z160,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z434,z6]),(0,[z0,z1,z3,z4,z5,z435,z6]),(0,[z436,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z437,z6]),(0,[z0,z438,z1,z3,z4,z5,z6])]],
   [[(0,[z11,z0,z1,z3,z4,z5,z105])],[(1,[z0,z1,z3,z269,z5,z6]),(0,[z0,z1,z3,z4,z439,z5,z6]),(0,[z0,z1,z3,z4,z440,z5,z6]),(0,[z0,z1,z3,z441,z4,z5,z6]),(0,[z0,z1,z3,z442,z4,z5,z6]),(0,[z443,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z58,z4,z5,z444,z6]),(0,[z0,z1,z3,z445,z4,z5,z6]),(0,[z0,z7,z1,z4,z81,z5,z6]),(0,[z0,z1,z3,z4,z5,z446,z6])],[(0,[z0,z1,z447,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z448,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z449]),(0,[z0,z1,z3,z4,z5,z6,z450]),(0,[z106,z0,z1,z3,z4,z107,z6]),(0,[z0,z1,z3,z4,z451,z5,z6])],[(0,[z327,z0,z93,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z28,z6]),(0,[z174,z1,z3,z4,z5,z28,z6]),(0,[z452,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z49,z6]),(0,[z0,z1,z3,z4,z5,z6,z453])],[(0,[z0,z46,z93,z3,z4,z5,z6]),(0,[z0,z1,z140,z17,z4,z5,z6]),(0,[z0,z162,z46,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z454,z5,z6])],[(0,[z0,z46,z1,z17,z4,z5,z6]),(0,[z0,z1,z17,z4,z5,z6,z55]),(0,[z0,z1,z17,z4,z5,z6,z41]),(0,[z0,z1,z58,z4,z5,z6,z22]),(0,[z0,z1,z3,z4,z5,z6,z455])],[(0,[z139,z1,z3,z36,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z456,z6]),(0,[z0,z1,z3,z457,z4,z5,z6]),(0,[z121,z0,z3,z4,z5,z154,z6]),(0,[z0,z1,z3,z458,z4,z5,z6]),(0,[z0,z459,z1,z3,z4,z5,z6]),(0,[z0,z460,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z4,z12,z6])]],
   [[(0,[z0,z1,z3,z4,z461,z5,z6]),(0,[z0,z1,z58,z4,z5,z26,z6]),(0,[z462,z0,z1,z3,z4,z5,z6])],[(0,[z234,z0,z1,z463,z4,z5,z6]),(0,[z464,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z139,z0,z1,z304,z4,z5,z6]),(0,[z0,z1,z3,z4,z465,z5,z6]),(0,[z11,z0,z1,z3,z73,z5,z6]),(0,[z0,z1,z3,z39,z50,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z466])],[(0,[z0,z38,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z467,z4,z5,z6]),(1,[z57,z0,z3,z4,z5,z242]),(0,[z0,z468,z1,z3,z4,z5,z6]),(0,[z0,z77,z1,z3,z4,z5,z22])],[(1,[z234,z205,z3,z4,z5,z6]),(0,[z160,z1,z205,z3,z4,z5,z6]),(0,[z160,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z469,z4,z5,z6]),(0,[z0,z470,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z5,z37]),(1,[z0,z1,z3,z445,z5,z6]),(1,[z0,z1,z3,z165,z5,z6])],[(0,[z0,z1,z471,z3,z4,z5,z6]),(0,[z0,z472,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z473,z6]),(0,[z0,z1,z3,z4,z5,z6,z474])],[(1,[z1,z17,z4,z5,z70,z6]),(0,[z291,z0,z1,z58,z4,z5,z6]),(0,[z139,z0,z1,z111,z4,z5,z6])],[(0,[z0,z1,z3,z17,z4,z5,z6]),(0,[z169,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z475,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z476,z6]),(0,[z121,z0,z3,z4,z5,z130,z6]),(1,[z0,z1,z84,z39,z5,z6])]],
   [[(0,[z0,z1,z17,z4,z5,z6,z105]),(0,[z0,z1,z17,z4,z5,z107,z6]),(0,[z0,z1,z3,z4,z5,z477,z6]),(1,[z0,z1,z126,z4,z5,z6]),(0,[z478,z0,z1,z3,z4,z5,z6]),(0,[z0,z479,z1,z3,z4,z5,z6]),(0,[z200,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z480,z3,z4,z5,z6]),(0,[z19,z0,z1,z217,z4,z5,z6]),(0,[z0,z481,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z223,z130,z6]),(1,[z0,z1,z3,z267,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z482])],[(1,[z95,z1,z17,z4,z5,z6]),(0,[z169,z0,z1,z373,z4,z5,z6]),(0,[z483,z0,z1,z3,z4,z5,z6]),(0,[z0,z484,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z485,z6]),(0,[z0,z1,z3,z4,z486,z5,z6])],[(0,[z487,z0,z1,z3,z4,z5,z6]),(0,[z488,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z489]),(0,[z0,z1,z3,z4,z5,z6,z490])],[(0,[z0,z1,z3,z4,z491,z5,z6]),(0,[z19,z0,z1,z3,z350,z5,z6]),(0,[z121,z0,z1,z3,z4,z94,z6]),(0,[z0,z91,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z492,z4,z5,z6])],[(0,[z11,z0,z1,z58,z4,z5,z6]),(0,[z493,z0,z1,z3,z4,z5,z6]),(0,[z0,z204,z3,z50,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z494])],[(0,[z121,z0,z205,z3,z4,z5,z6]),(0,[z0,z1,z3,z39,z73,z5,z6]),(0,[z495,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z496,z5,z6])],[(0,[z160,z169,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z6,z105]),(0,[z0,z1,z3,z4,z5,z497,z6]),(0,[z0,z1,z3,z4,z498,z5,z6]),(1,[z0,z1,z3,z229,z5,z6]),(0,[z0,z1,z3,z4,z499,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z500]),(0,[z501,z0,z1,z3,z4,z5,z6]),(0,[z0,z93,z1,z58,z4,z5,z6]),(1,[z0,z186,z3,z4,z5,z6]),(0,[z0,z7,z3,z129,z4,z5,z6]),(0,[z0,z140,z3,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z502,z5,z6]),(1,[z0,z1,z3,z5,z182,z6])],[(0,[z234,z0,z1,z3,z461,z5,z6]),(0,[z27,z0,z1,z17,z4,z5,z6]),(0,[z19,z0,z1,z396,z4,z5,z6]),(0,[z0,z1,z3,z503,z4,z5,z6])],[(0,[z0,z1,z3,z4,z504,z5,z6])],[(0,[z95,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z4,z142,z5,z6]),(0,[z0,z505,z1,z3,z4,z5,z6]),(0,[z506,z0,z1,z3,z4,z5,z6]),(0,[z507,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z405])],[(0,[z327,z234,z1,z3,z4,z5,z6]),(0,[z0,z508,z1,z3,z4,z5,z6]),(0,[z327,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z17,z4,z69,z5,z6]),(0,[z0,z1,z3,z150,z4,z5,z6]),(1,[z0,z1,z3,z292,z5,z6]),(0,[z0,z1,z3,z4,z69,z6,z22]),(0,[z0,z1,z3,z4,z5,z6,z242]),(0,[z48,z0,z1,z3,z104,z5,z6]),(0,[z0,z1,z42,z151,z4,z5,z6]),(0,[z0,z1,z509,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z121,z0,z93,z3,z4,z5,z6]),(0,[z0,z46,z1,z58,z4,z5,z6]),(0,[z35,z0,z1,z510,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z511,z6])],[(0,[z121,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z0,z1,z513,z3,z4,z5,z6])],[(0,[z0,z1,z118,z3,z4,z5,z6]),(0,[z35,z0,z1,z58,z4,z5,z6]),(0,[z514,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z515,z4,z5,z6]),(1,[z0,z1,z3,z8,z5,z6]),(0,[z516,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z517]),(0,[z121,z0,z1,z3,z114,z5,z6]),(0,[z0,z1,z3,z503,z5,z154,z6]),(0,[z518,z0,z1,z3,z4,z5,z6]),(0,[z519,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z139,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z520,z5,z6]),(0,[z521,z0,z1,z3,z4,z5,z6]),(0,[z57,z0,z119,z3,z4,z5,z6]),(0,[z0,z522,z1,z3,z4,z5,z6])],[(0,[z0,z1,z17,z4,z5,z70,z6]),(0,[z0,z523,z1,z3,z4,z5,z6])],[(0,[z0,z1,z58,z4,z142,z5,z6]),(0,[z19,z0,z1,z3,z100,z5,z6]),(0,[z0,z162,z1,z3,z50,z5,z6]),(0,[z0,z1,z3,z72,z104,z5,z6]),(0,[z0,z1,z3,z73,z5,z49,z6]),(0,[z0,z122,z3,z4,z94,z5,z6]),(0,[z0,z1,z3,z524,z4,z5,z6])],[(0,[z0,z1,z463,z3,z4,z5,z6]),(0,[z234,z0,z1,z58,z4,z5,z6]),(0,[z19,z1,z3,z17,z4,z5,z6]),(0,[z0,z1,z58,z4,z69,z5,z6]),(0,[z0,z1,z159,z58,z4,z5,z6]),(0,[z525,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z371,z3,z4,z5,z6]),(0,[z0,z1,z3,z526,z4,z5,z6]),(0,[z0,z1,z3,z4,z527,z5,z6]),(0,[z57,z0,z3,z4,z5,z6,z242]),(0,[z528,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z194,z6]),(0,[z0,z1,z3,z510,z4,z5,z6]),(0,[z0,z1,z3,z4,z529,z5,z6]),(0,[z0,z530,z1,z3,z4,z5,z6]),(0,[z531,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z532]),(0,[z0,z1,z3,z4,z5,z6,z37]),(0,[z533,z0,z1,z3,z4,z5,z6]),(0,[z48,z0,z46,z1,z3,z5,z6])],[(0,[z0,z1,z3,z534,z4,z5,z6]),(1,[z19,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z535,z6]),(0,[z0,z1,z3,z4,z536,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z537])],[(0,[z0,z1,z205,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z538,z5,z6]),(0,[z539,z0,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z254])]],
   [[(0,[z243,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z58,z4,z5,z70,z6]),(1,[z27,z1,z3,z4,z70,z6]),(0,[z0,z1,z3,z4,z421,z5,z6]),(0,[z0,z1,z3,z540,z4,z5,z6]),(0,[z0,z1,z3,z4,z541,z5,z6])],[(0,[z0,z1,z3,z4,z5,z542,z6]),(1,[z327,z1,z17,z4,z5,z6]),(0,[z0,z1,z58,z36,z4,z5,z6]),(0,[z543,z0,z1,z3,z4,z5,z6])],[(0,[z544,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z545,z6])],[(0,[z0,z546,z1,z3,z4,z5,z6]),(0,[z0,z547,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z548]),(1,[z0,z38,z1,z104,z5,z6]),(0,[z549,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z81,z5,z6]),(0,[z550,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z40,z4,z5,z254,z6])],[(0,[z551,z0,z1,z3,z4,z5,z6]),(0,[z48,z0,z162,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z552,z5,z6]),(0,[z0,z1,z3,z553,z4,z5,z6])],[(0,[z86,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z554,z3,z4,z5,z6]),(0,[z160,z1,z3,z4,z5,z28,z6]),(0,[z555,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z556,z5,z6]),(0,[z0,z1,z3,z165,z4,z5,z6]),(0,[z0,z1,z557,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z558]),(0,[z48,z0,z1,z3,z39,z5,z6]),(0,[z0,z1,z559,z3,z4,z5,z6])],[(0,[z327,z0,z1,z237,z4,z5,z6]),(0,[z0,z162,z1,z3,z73,z5,z6]),(0,[z560,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z42,z3,z4,z5,z6])],[(0,[z0,z1,z58,z40,z4,z5,z6]),(1,[z0,z1,z34,z4,z5,z6]),(0,[z0,z64,z1,z140,z4,z5,z6]),(0,[z0,z1,z3,z561,z4,z5,z6])]],
   [[(0,[z0,z1,z17,z4,z51,z5,z6]),(0,[z27,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z380,z58,z4,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z223,z6]),(0,[z0,z77,z1,z3,z4,z5,z6])],[(0,[z1,z205,z3,z17,z4,z5,z6]),(0,[z0,z1,z562,z3,z4,z5,z6]),(0,[z1,z58,z3,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z563]),(0,[z0,z1,z3,z4,z5,z564,z6])],[(0,[z0,z1,z3,z4,z5,z565,z6]),(0,[z0,z46,z3,z4,z5,z154,z6]),(0,[z0,z1,z3,z4,z94,z5,z6])],[(0,[z0,z1,z3,z4,z566,z5,z6])],[(0,[z0,z93,z3,z4,z72,z5,z6]),(1,[z0,z170,z3,z4,z5,z6]),(0,[z0,z3,z73,z4,z72,z5,z6]),(0,[z0,z1,z3,z4,z5,z567,z6]),(0,[z568,z0,z1,z3,z4,z5,z6])],[],[(0,[z0,z569,z1,z3,z4,z5,z6]),(1,[z0,z570,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z571,z6]),(0,[z0,z1,z3,z4,z5,z6,z405])],[(0,[z0,z1,z3,z265,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z572,z6]),(0,[z0,z1,z3,z573,z4,z5,z6]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z574,z0,z3,z4,z5,z6,z22])]],
   [[(0,[z0,z1,z3,z4,z5,z575,z6]),(0,[z0,z1,z3,z237,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z576,z6]),(0,[z0,z1,z3,z4,z5,z6,z577]),(0,[z0,z1,z3,z578,z4,z5,z6])],[(0,[z327,z93,z1,z3,z4,z5,z6]),(0,[z0,z162,z1,z58,z4,z5,z6]),(0,[z19,z1,z3,z4,z5,z6,z37]),(0,[z0,z1,z3,z4,z5,z579,z6]),(0,[z0,z119,z1,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z580,z5,z6])],[(0,[z581,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z236,z4,z5,z6]),(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z583,z6]),(0,[z0,z1,z3,z4,z5,z584,z6]),(0,[z106,z0,z1,z84,z4,z5,z6]),(0,[z0,z1,z3,z12,z5,z53,z6])],[(0,[z585,z0,z1,z3,z4,z5,z6]),(0,[z169,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z276,z5,z6]),(0,[z0,z1,z3,z4,z5,z586,z6]),(0,[z0,z587,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z25]),(1,[z0,z77,z1,z3,z4,z108])],[(0,[z0,z1,z3,z4,z588,z5,z6]),(0,[z139,z0,z1,z3,z36,z5,z6]),(0,[z589,z0,z1,z3,z4,z5,z6]),(0,[z0,z590,z1,z3,z4,z5,z6]),(1,[z574,z0,z3,z4,z5,z6])],[(0,[z0,z274,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z591,z4,z5,z6]),(0,[z0,z1,z592,z3,z4,z5,z6])],[(0,[z0,z593,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z594,z6])],[(0,[z595,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z596,z6]),(0,[z0,z1,z3,z4,z114,z5,z6]),(0,[z57,z0,z1,z3,z4,z5,z6]),(0,[z106,z388,z1,z3,z4,z5,z6]),(0,[z0,z1,z597,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z441,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z41])]],
   [[(0,[z327,z0,z205,z3,z4,z5,z6]),(0,[z0,z1,z220,z3,z4,z5,z6]),(0,[z0,z598,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z267,z5,z6]),(0,[z599,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z600,z6])],[(0,[z0,z46,z205,z3,z4,z5,z6]),(0,[z11,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z84,z58,z4,z5,z6]),(0,[z0,z601,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z602,z6])],[(0,[z0,z1,z3,z261,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z123]),(0,[z0,z1,z3,z603,z4,z5,z6])],[(0,[z0,z1,z58,z4,z12,z5,z6]),(0,[z604,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z605,z5,z6]),(0,[z0,z1,z606,z3,z4,z5,z6]),(0,[z607,z0,z1,z3,z4,z5,z6])],[(0,[z76,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z608,z4,z5,z6]),(0,[z0,z93,z1,z17,z4,z5,z6]),(0,[z86,z0,z1,z58,z4,z5,z6]),(0,[z27,z0,z1,z3,z4,z69,z6]),(0,[z19,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z131,z6]),(0,[z0,z388,z1,z3,z4,z5,z6]),(1,[z294,z1,z3,z4,z5,z6]),(0,[z0,z3,z50,z4,z252,z5,z6])],[(0,[z0,z1,z3,z4,z609,z5,z6]),(0,[z0,z1,z58,z4,z5,z6,z249]),(0,[z0,z1,z3,z51,z5,z6,z105])],[(0,[z0,z1,z3,z269,z4,z5,z6]),(0,[z0,z1,z3,z610,z4,z5,z6]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z0,z1,z3,z611,z4,z5,z6]),(0,[z0,z1,z3,z4,z612,z5,z6]),(0,[z0,z613,z1,z3,z4,z5,z6])],[(1,[z0,z1,z463,z4,z5,z6]),(0,[z234,z0,z205,z3,z4,z5,z6]),(0,[z0,z1,z241,z3,z4,z5,z6]),(0,[z0,z1,z447,z58,z4,z5,z6]),(0,[z0,z1,z614,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z615,z5,z6]),(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z0,z617,z1,z3,z4,z5,z6]),(0,[z0,z1,z80,z3,z4,z81,z6])]],
   [[(0,[z327,z0,z1,z17,z4,z5,z6]),(0,[z618,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z619,z3,z4,z5,z6]),(0,[z169,z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z620])],[(0,[z621,z0,z1,z3,z4,z5,z6]),(0,[z0,z331,z1,z17,z4,z5,z6]),(0,[z0,z1,z17,z4,z54,z5,z6]),(0,[z0,z622,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z107,z6]),(0,[z86,z0,z1,z4,z81,z5,z6]),(1,[z0,z1,z40,z4,z5,z254])],[(0,[z0,z335,z1,z17,z4,z5,z6]),(0,[z0,z46,z3,z73,z4,z5,z6]),(0,[z0,z1,z623,z3,z4,z5,z6]),(0,[z48,z0,z1,z3,z4,z5,z6])],[(0,[z35,z0,z1,z17,z4,z5,z6]),(1,[z169,z1,z17,z4,z5,z6]),(1,[z0,z1,z304,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z624]),(0,[z0,z1,z3,z625,z4,z5,z6]),(0,[z0,z1,z3,z151,z5,z6,z105])],[(0,[z139,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z626,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z627]),(0,[z0,z119,z1,z3,z4,z5,z6]),(0,[z1,z40,z257,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z5,z6,z105])],[(0,[z0,z7,z1,z140,z4,z5,z6]),(0,[z0,z1,z80,z3,z561,z5,z6]),(0,[z48,z0,z1,z3,z5,z53,z6]),(0,[z0,z1,z3,z4,z108,z142,z5])],[(0,[z234,z0,z93,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z628,z6]),(0,[z629,z0,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z5,z242]),(0,[z48,z0,z1,z3,z151,z5,z6]),(0,[z630,z0,z1,z3,z4,z5,z6])],[(0,[z234,z1,z205,z3,z4,z5,z6]),(0,[z234,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z170,z3,z4,z5,z6]),(0,[z57,z0,z46,z3,z4,z5,z6]),(0,[z57,z121,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z631]),(0,[z0,z632,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z633,z6]),(0,[z0,z1,z570,z3,z4,z5,z6]),(0,[z106,z0,z64,z1,z4,z5,z6])],[],[(0,[z0,z1,z205,z17,z4,z5,z6]),(0,[z0,z634,z1,z3,z4,z5,z6]),(0,[z160,z1,z58,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z635,z5,z6]),(0,[z0,z1,z3,z72,z5,z53,z6]),(1,[z0,z204,z3,z4,z5,z6]),(0,[z636,z0,z1,z3,z4,z5,z6])],[(0,[z0,z205,z3,z4,z72,z5,z6]),(0,[z0,z637,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z151,z4,z5,z6]),(0,[z303,z0,z1,z58,z4,z5,z6]),(0,[z0,z638,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z20,z6]),(0,[z0,z1,z3,z4,z5,z6,z639]),(0,[z0,z46,z1,z3,z5,z6,z105]),(0,[z640,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z641,z6])],[(0,[z0,z162,z3,z4,z72,z5,z6]),(1,[z121,z0,z3,z4,z130,z6]),(0,[z0,z1,z3,z4,z5,z642,z6]),(0,[z0,z1,z3,z4,z317,z5,z6]),(0,[z643,z0,z1,z3,z4,z5,z6])],[(0,[z644,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z296,z4,z5,z6]),(0,[z0,z62,z1,z3,z4,z5,z6]),(0,[z0,z645,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z646])],[(1,[z0,z1,z3,z461,z5,z6]),(0,[z0,z1,z3,z4,z647,z5,z6]),(0,[z0,z1,z3,z4,z70,z6,z22]),(0,[z648,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z649,z5,z6]),(0,[z0,z64,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z39,z5,z6,z105])],[(0,[z0,z1,z3,z4,z5,z6,z650]),(0,[z0,z651,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z254,z6,z41])],[(1,[z0,z1,z3,z503,z5,z6]),(0,[z652,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z58,z151,z4,z5,z6]),(1,[z135,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z653,z6]),(0,[z0,z654,z1,z3,z4,z5,z6])],[(0,[z0,z1,z58,z4,z5,z53,z6]),(0,[z0,z1,z3,z36,z5,z6,z105]),(1,[z0,z1,z3,z441,z5,z6])],[(1,[z0,z1,z371,z4,z5,z6]),(0,[z19,z0,z570,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z4,z5,z6,z655]),(0,[z86,z0,z1,z4,z5,z6,z41])],[(0,[z1,z3,z4,z5,z28,z6,z37]),(0,[z0,z1,z3,z4,z142,z6,z22])],[(0,[z95,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z17,z4,z72,z5,z6]),(0,[z0,z1,z58,z4,z5,z154,z6]),(1,[z0,z1,z510,z4,z5,z6])]],
   [[(0,[z656,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z360,z6]),(0,[z0,z1,z3,z292,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z657]),(0,[z0,z1,z3,z4,z5,z658,z6]),(0,[z0,z659,z1,z3,z4,z5,z6])],[(1,[z0,z1,z58,z4,z5,z6]),(0,[z660,z0,z1,z3,z4,z5,z6]),(0,[z0,z661,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z4,z5,z49])],[(0,[z0,z1,z17,z155,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z662,z6]),(0,[z0,z1,z3,z141,z4,z5,z6])],[(0,[z0,z663,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z664,z6]),(0,[z0,z1,z3,z5,z6,z123,z22])],[(0,[z665,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z373,z4,z5,z6]),(0,[z666,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z667,z3,z4,z5,z6]),(0,[z143,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z17,z36,z4,z5,z6]),(0,[z0,z402,z1,z17,z4,z5,z6]),(0,[z0,z162,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z668,z5,z6]),(0,[z19,z0,z1,z3,z4,z421,z6]),(0,[z0,z7,z1,z3,z445,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z669])],[(0,[z0,z1,z58,z4,z72,z5,z6]),(0,[z169,z0,z1,z3,z4,z69,z6]),(0,[z0,z1,z3,z4,z5,z670,z6]),(1,[z0,z46,z3,z73,z5,z6]),(1,[z0,z1,z3,z141,z5,z6]),(1,[z86,z0,z1,z4,z5,z41]),(1,[z1,z257,z3,z4,z5,z6]),(0,[z368,z0,z1,z3,z5,z6,z22])],[(0,[z0,z1,z17,z4,z104,z5,z6]),(0,[z0,z1,z58,z4,z5,z130,z6]),(0,[z27,z169,z1,z3,z4,z5,z6]),(0,[z0,z38,z1,z84,z4,z5,z6]),(0,[z48,z0,z1,z3,z4,z53,z6]),(0,[z0,z671,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z672,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z673,z5,z6]),(0,[z0,z1,z58,z39,z4,z5,z6]),(0,[z0,z1,z3,z36,z72,z5,z6])],[(0,[z674,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z5,z6]),(0,[z19,z1,z3,z4,z69,z5,z6]),(0,[z0,z1,z3,z4,z5,z675,z6]),(0,[z0,z1,z3,z4,z108,z5,z6])],[(0,[z0,z1,z17,z50,z4,z5,z6]),(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z677,z5,z6])],[(0,[z0,z122,z1,z3,z4,z5,z6]),(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z679,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z680]),(0,[z0,z1,z681,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z682]),(0,[z0,z1,z80,z17,z4,z5,z6]),(0,[z0,z7,z64,z3,z4,z5,z6]),(0,[z0,z1,z39,z4,z104,z5,z6]),(0,[z0,z683,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z684]),(0,[z143,z1,z3,z4,z5,z6,z22])],[(0,[z0,z1,z58,z3,z4,z5,z6]),(0,[z0,z1,z84,z17,z4,z5,z6]),(0,[z0,z38,z1,z3,z104,z5,z6]),(0,[z0,z1,z3,z4,z5,z685,z6]),(0,[z0,z1,z3,z12,z5,z49,z6])],[(0,[z544,z0,z1,z58,z4,z5,z6]),(0,[z0,z1,z58,z4,z104,z5,z6]),(0,[z0,z135,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z686,z5,z6]),(0,[z106,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z561,z5,z6]),(0,[z0,z1,z687,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z688,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z689]),(0,[z106,z0,z1,z4,z104,z5,z6]),(0,[z690,z0,z1,z3,z4,z5,z6]),(0,[z691,z0,z1,z3,z4,z5,z6]),(0,[z0,z692,z1,z3,z4,z5,z6])]],
   [[(0,[z693,z0,z1,z3,z4,z5,z6]),(0,[z0,z162,z1,z3,z5,z6,z105]),(0,[z0,z1,z3,z694,z4,z5,z6])],[(0,[z0,z1,z58,z50,z4,z5,z6]),(0,[z0,z1,z3,z51,z12,z5,z6]),(0,[z0,z695,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z696,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z254,z6])],[(0,[z0,z697,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z698,z5,z6]),(0,[z356,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z366,z5,z6]),(0,[z0,z64,z140,z3,z4,z5,z6]),(0,[z0,z1,z699,z3,z4,z5,z6]),(0,[z0,z1,z3,z163,z4,z5,z6]),(0,[z0,z1,z3,z4,z142,z5,z22])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(1,[z200,z0,z1,z4,z5,z6])],[(0,[z700,z0,z1,z3,z4,z5,z6]),(0,[z327,z1,z3,z17,z4,z5,z6]),(0,[z0,z1,z3,z701,z4,z5,z6]),(0,[z0,z77,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z702])],[(1,[z1,z17,z4,z5,z28,z6]),(0,[z0,z703,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z704,z4,z5,z6])],[(0,[z35,z0,z245,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z51,z5,z6]),(1,[z169,z1,z3,z4,z69,z6]),(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z3,z4,z81,z6]),(0,[z0,z1,z3,z50,z4,z5,z49])],[(0,[z705,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z73,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z444,z6]),(0,[z0,z110,z1,z3,z4,z5,z6]),(0,[z139,z0,z1,z3,z51,z5,z6]),(0,[z0,z1,z3,z151,z12,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z4,z5,z6]),(0,[z528,z1,z17,z4,z5,z6]),(0,[z0,z62,z217,z4,z5,z6]),(0,[z0,z1,z80,z229,z81,z6])],[(0,[z0,z1,z708,z4,z5,z6]),(0,[z1,z17,z354,z4,z5,z6]),(0,[z599,z1,z58,z4,z5,z6]),(0,[z1,z126,z4,z5,z28,z6]),(0,[z0,z1,z3,z709,z5,z6]),(0,[z0,z186,z150,z4,z5,z6]),(0,[z0,z1,z710,z4,z5,z6]),(0,[z711,z0,z1,z3,z5,z6]),(0,[z0,z1,z4,z301,z81,z6]),(0,[z0,z1,z3,z4,z712,z6]),(0,[z0,z1,z3,z4,z713,z6]),(0,[z143,z3,z4,z5,z6,z405])],[(0,[z0,z1,z17,z714,z5,z6]),(0,[z243,z0,z1,z4,z5,z41]),(0,[z0,z715,z3,z4,z5,z6]),(0,[z0,z716,z3,z4,z5,z6]),(0,[z0,z1,z717,z4,z5,z6]),(0,[z0,z204,z3,z4,z5,z6])],[(0,[z30,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z718,z5,z6]),(0,[z0,z1,z3,z4,z20,z6]),(0,[z19,z570,z3,z4,z5,z37]),(0,[z0,z62,z3,z350,z5,z6]),(0,[z1,z719,z3,z4,z5,z6])],[(0,[z0,z1,z3,z720,z5,z6]),(0,[z93,z721,z3,z4,z5,z6]),(0,[z327,z93,z17,z4,z5,z6]),(0,[z0,z1,z58,z267,z5,z6]),(0,[z121,z0,z3,z4,z130,z6]),(0,[z388,z1,z4,z5,z107,z6])],[(0,[z0,z508,z3,z72,z5,z6])],[(0,[z0,z1,z4,z5,z722,z6]),(0,[z0,z1,z723,z4,z5,z6]),(0,[z0,z724,z3,z4,z5,z6]),(0,[z0,z1,z3,z725,z5,z6]),(0,[z0,z1,z3,z5,z726,z6])],[(0,[z0,z1,z727,z4,z5,z6]),(0,[z0,z728,z3,z4,z5,z6]),(0,[z729,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z12,z6])]],
   [[(0,[z0,z1,z730,z4,z5,z6]),(0,[z0,z1,z17,z87,z5,z6])],[(0,[z0,z1,z731,z4,z5,z6]),(0,[z0,z1,z3,z5,z732,z6]),(0,[z0,z1,z3,z503,z5,z6]),(0,[z1,z3,z4,z5,z6,z733])],[(0,[z0,z1,z3,z734,z5,z6]),(0,[z46,z205,z17,z4,z5,z6]),(0,[z0,z1,z4,z735,z5,z6]),(0,[z0,z1,z3,z12,z726,z6])],[(0,[z487,z0,z3,z4,z5,z242]),(0,[z135,z1,z58,z4,z5,z6]),(1,[z1,z3,z4,z5,z736]),(0,[z0,z1,z4,z81,z201,z6]),(0,[z0,z1,z3,z441,z5,z6])],[(0,[z227,z205,z3,z4,z5,z6]),(0,[z0,z1,z17,z350,z5,z6]),(0,[z10,z1,z17,z4,z5,z6]),(0,[z0,z1,z737,z4,z5,z6]),(0,[z738,z1,z3,z4,z5,z6]),(0,[z0,z739,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z740,z6]),(0,[z388,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z741,z6]),(0,[z1,z3,z4,z5,z6,z736]),(0,[z0,z1,z3,z742,z5,z6]),(0,[z0,z1,z743,z4,z5,z6]),(0,[z200,z368,z0,z1,z5,z6])],[(0,[z0,z1,z510,z4,z5,z6]),(0,[z1,z261,z4,z5,z28,z6])],[(0,[z1,z396,z17,z4,z5,z6]),(0,[z0,z1,z58,z292,z5,z6]),(0,[z0,z1,z3,z12,z473,z6]),(0,[z744,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z58,z4,z5,z6]),(0,[z327,z425,z3,z4,z5,z6]),(0,[z0,z170,z17,z4,z5,z6]),(0,[z0,z1,z745,z4,z5,z6])],[(0,[z0,z1,z17,z4,z746,z6]),(0,[z0,z77,z1,z58,z4,z108]),(0,[z0,z62,z3,z4,z421,z6]),(0,[z174,z1,z277,z4,z5,z28]),(0,[z0,z3,z4,z94,z747,z6]),(0,[z574,z0,z3,z4,z142,z22])],[(0,[z0,z1,z3,z5,z748,z6]),(0,[z0,z570,z17,z4,z5,z6]),(0,[z174,z1,z17,z4,z5,z28]),(0,[z0,z58,z4,z5,z6,z405]),(0,[z0,z1,z58,z8,z5,z6]),(0,[z749,z1,z3,z4,z5,z6]),(0,[z0,z1,z750,z4,z5,z6]),(0,[z0,z1,z751,z4,z5,z6])],[(0,[z1,z205,z235,z4,z5,z6]),(0,[z0,z1,z373,z4,z5,z6]),(0,[z1,z723,z17,z4,z5,z6]),(0,[z1,z17,z4,z5,z571,z6])],[(0,[z227,z1,z17,z4,z5,z6]),(0,[z376,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z752,z5,z6]),(0,[z0,z753,z3,z4,z5,z6]),(0,[z0,z1,z3,z754,z5,z6]),(0,[z0,z1,z50,z317,z5,z6]),(0,[z0,z1,z3,z5,z49,z224]),(0,[z0,z1,z755,z4,z5,z6])],[(0,[z1,z257,z3,z4,z5,z6]),(0,[z0,z274,z140,z4,z5,z6]),(0,[z0,z1,z3,z756,z5,z6]),(0,[z19,z1,z126,z4,z5,z6]),(0,[z0,z1,z3,z757,z5,z6]),(0,[z0,z46,z3,z73,z5,z6]),(0,[z0,z1,z3,z141,z5,z6]),(0,[z758,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z4,z5,z56]),(0,[z0,z3,z759,z4,z5,z6]),(0,[z86,z0,z1,z4,z5,z41])],[(0,[z0,z760,z1,z3,z5,z6]),(0,[z0,z1,z761,z4,z5,z6]),(0,[z388,z1,z447,z4,z5,z6])],[(0,[z0,z1,z17,z190,z5,z6]),(0,[z616,z1,z17,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z762])]],
   [[(0,[z356,z1,z17,z4,z70,z6]),(0,[z1,z170,z17,z4,z5,z6]),(0,[z574,z0,z17,z4,z5,z6]),(0,[z636,z1,z17,z4,z5,z6]),(0,[z0,z617,z3,z73,z5,z6]),(0,[z763,z1,z3,z4,z5,z6]),(0,[z764,z1,z3,z4,z5,z6])],[(0,[z765,z1,z3,z4,z5,z6]),(0,[z0,z1,z766,z4,z5,z6]),(0,[z0,z3,z4,z767,z5,z6])],[(0,[z1,z570,z17,z4,z5,z6]),(0,[z0,z1,z17,z4,z421,z6]),(0,[z0,z398,z3,z73,z5,z6]),(0,[z106,z0,z1,z229,z5,z6]),(0,[z143,z1,z768,z4,z5,z6])],[(0,[z0,z1,z4,z5,z769,z6]),(0,[z0,z335,z1,z104,z5,z6]),(0,[z27,z1,z58,z4,z70,z6]),(0,[z0,z770,z1,z3,z4,z6])],[(0,[z771,z1,z3,z4,z5,z6]),(0,[z772,z0,z1,z3,z5,z6]),(0,[z773,z1,z3,z4,z5,z6]),(0,[z574,z0,z3,z5,z6,z123])],[(0,[z0,z331,z241,z4,z5,z6]),(0,[z0,z162,z17,z72,z5,z6]),(0,[z0,z170,z150,z4,z5,z6]),(0,[z0,z3,z4,z5,z774,z242]),(0,[z0,z1,z3,z561,z5,z6])],[(0,[z775,z1,z3,z4,z5,z6])],[(0,[z1,z16,z17,z4,z5,z28]),(0,[z645,z1,z17,z4,z5,z6]),(0,[z1,z58,z4,z5,z6,z25]),(0,[z0,z342,z3,z73,z5,z6]),(0,[z0,z1,z3,z4,z776,z6]),(0,[z106,z388,z1,z4,z107,z6]),(0,[z0,z1,z3,z4,z713,z22])]],
   [[(0,[z294,z1,z17,z4,z5,z6]),(0,[z0,z777,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z726,z6]),(1,[z0,z1,z3,z4,z713])],[(0,[z19,z1,z17,z4,z5,z28]),(0,[z0,z1,z3,z4,z778,z6]),(0,[z19,z1,z3,z4,z20,z37]),(0,[z0,z1,z779,z4,z5,z6]),(0,[z0,z780,z1,z4,z5,z6])],[(0,[z0,z1,z3,z781,z5,z6]),(0,[z0,z3,z51,z252,z5,z6]),(0,[z106,z0,z1,z8,z5,z6]),(0,[z0,z1,z559,z104,z5,z6]),(0,[z0,z3,z252,z5,z49,z6])],[(0,[z0,z1,z782,z4,z5,z6]),(0,[z656,z1,z17,z4,z5,z6]),(0,[z1,z58,z257,z4,z5,z6]),(0,[z0,z1,z3,z783,z5,z6]),(0,[z0,z1,z3,z784,z5,z6]),(0,[z0,z1,z3,z5,z579,z105]),(0,[z0,z1,z3,z785,z5,z6])],[(0,[z0,z245,z3,z4,z5,z6]),(0,[z1,z17,z4,z5,z28,z6]),(0,[z0,z1,z150,z190,z5,z6]),(0,[z0,z786,z3,z4,z5,z6]),(0,[z0,z1,z4,z787,z5,z6]),(0,[z0,z1,z788,z4,z5,z6]),(0,[z1,z789,z3,z4,z5,z6]),(0,[z48,z0,z1,z3,z726,z6]),(0,[z0,z1,z790,z4,z5,z6]),(0,[z0,z1,z3,z151,z726,z6]),(0,[z143,z1,z4,z5,z6,z32])],[(0,[z0,z1,z791,z4,z5,z6]),(0,[z0,z792,z1,z3,z5,z6]),(0,[z0,z1,z17,z793,z5,z6]),(0,[z27,z1,z3,z4,z20,z6]),(0,[z0,z1,z3,z794,z5,z6])],[(0,[z402,z205,z17,z4,z5,z6]),(0,[z1,z176,z17,z4,z5,z6]),(0,[z1,z17,z4,z5,z6,z455]),(0,[z169,z1,z58,z4,z69,z6]),(0,[z106,z0,z1,z4,z444,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z0,z796,z3,z4,z5,z6]),(0,[z797,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z252,z5,z6]),(0,[z1,z798,z3,z4,z5,z6])],[(0,[z0,z1,z799,z4,z5,z6]),(0,[z0,z62,z3,z4,z20,z6]),(0,[z0,z7,z129,z445,z5,z6])]],
   [[(0,[z0,z205,z3,z267,z5,z6]),(0,[z0,z1,z800,z4,z5,z6]),(0,[z0,z1,z17,z801,z4,z6]),(0,[z1,z58,z597,z4,z5,z6]),(0,[z1,z3,z4,z69,z20,z6]),(0,[z0,z3,z151,z252,z5,z6])],[(0,[z0,z1,z220,z155,z5,z6]),(0,[z169,z1,z373,z4,z69,z6]),(1,[z0,z779,z4,z5,z6]),(0,[z11,z0,z1,z3,z5,z657]),(0,[z57,z0,z3,z114,z5,z6])],[(0,[z0,z802,z3,z4,z5,z6]),(0,[z0,z803,z3,z4,z5,z6]),(0,[z0,z1,z58,z804,z5,z6]),(0,[z0,z1,z84,z24,z5,z6])],[(0,[z234,z205,z17,z4,z5,z6]),(0,[z0,z1,z17,z165,z5,z6]),(0,[z0,z1,z17,z445,z5,z6]),(0,[z805,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z806,z6]),(0,[z807,z0,z1,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z808]),(0,[z0,z1,z3,z726,z53,z6])],[(0,[z0,z697,z3,z4,z94,z6]),(0,[z388,z1,z4,z5,z254,z6])],[(0,[z327,z93,z237,z4,z5,z6]),(0,[z809,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z810,z5,z6]),(0,[z19,z1,z58,z4,z5,z37]),(0,[z0,z1,z396,z350,z5,z6])],[(0,[z0,z1,z3,z811,z5,z6]),(0,[z0,z204,z17,z4,z5,z6]),(0,[z35,z1,z3,z51,z5,z6]),(0,[z0,z1,z812,z4,z5,z6]),(0,[z139,z1,z304,z36,z5,z6]),(0,[z27,z1,z3,z4,z741,z6]),(0,[z106,z0,z1,z87,z5,z6]),(0,[z0,z1,z3,z813,z5,z6])]],
   [[(0,[z0,z1,z17,z267,z5,z6]),(0,[z169,z1,z3,z4,z668,z6]),(0,[z814,z1,z3,z4,z5,z6])],[(0,[z0,z46,z3,z701,z5,z6]),(0,[z436,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z815,z6]),(0,[z0,z1,z816,z4,z5,z6]),(0,[z1,z4,z5,z6,z817,z25])],[(0,[z0,z93,z3,z461,z5,z6]),(0,[z0,z1,z4,z5,z818,z6]),(0,[z0,z64,z241,z4,z5,z6]),(0,[z1,z3,z4,z69,z741,z6])],[(0,[z0,z1,z17,z461,z5,z6]),(0,[z0,z819,z1,z4,z5,z6]),(0,[z0,z820,z3,z4,z5,z6]),(0,[z143,z1,z821,z4,z5,z6])],[(0,[z585,z0,z3,z72,z5,z6]),(0,[z1,z17,z4,z70,z6,z22]),(0,[z0,z1,z17,z822,z5,z6]),(0,[z0,z1,z217,z100,z5,z6]),(0,[z0,z3,z503,z72,z5,z6]),(0,[z0,z1,z3,z151,z287,z6])],[(0,[z0,z1,z3,z5,z823,z6]),(0,[z0,z1,z58,z824,z5,z6]),(0,[z0,z1,z3,z4,z5,z774]),(0,[z0,z3,z39,z252,z5,z6]),(0,[z0,z1,z151,z317,z12,z6]),(0,[z0,z1,z3,z4,z142,z22])],[(0,[z74,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z503,z5,z6]),(0,[z0,z245,z34,z4,z5,z6]),(0,[z0,z1,z4,z825,z5,z6]),(0,[z826,z1,z3,z4,z5,z6]),(0,[z121,z0,z4,z223,z130,z6]),(1,[z0,z1,z3,z726,z6]),(0,[z0,z1,z827,z4,z5,z6])],[(0,[z135,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z828]),(0,[z1,z58,z829,z4,z5,z6]),(0,[z0,z830,z1,z3,z5,z6])]],
   [[(0,[z29,z1,z17,z4,z5,z6]),(0,[z0,z831,z3,z4,z5,z6]),(0,[z832,z0,z1,z4,z5,z6]),(0,[z0,z7,z129,z4,z5,z6])],[(0,[z0,z1,z58,z833,z5,z6]),(0,[z0,z1,z834,z4,z5,z6]),(0,[z0,z1,z835,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z836]),(0,[z837,z0,z1,z3,z5,z6]),(0,[z169,z1,z126,z4,z5,z6]),(0,[z0,z7,z129,z8,z5,z6]),(0,[z0,z1,z3,z389,z5,z49]),(0,[z0,z1,z838,z4,z5,z6]),(0,[z0,z1,z3,z839,z5,z6])],[(0,[z697,z1,z17,z4,z5,z6]),(0,[z0,z1,z840,z4,z5,z6]),(0,[z0,z1,z277,z4,z5,z6]),(0,[z0,z1,z17,z292,z5,z6]),(0,[z443,z1,z3,z36,z5,z6]),(0,[z0,z1,z3,z841,z5,z6]),(0,[z0,z140,z779,z4,z5,z6])],[(0,[z0,z1,z17,z4,z5,z6]),(0,[z842,z0,z1,z4,z5,z6]),(0,[z0,z843,z3,z4,z5,z6]),(0,[z0,z1,z844,z4,z5,z6]),(0,[z0,z1,z396,z100,z5,z6]),(0,[z0,z1,z3,z845,z5,z6]),(0,[z86,z0,z1,z4,z5,z846])],[(0,[z0,z1,z3,z114,z5,z6])],[(0,[z0,z1,z847,z4,z5,z6]),(0,[z0,z1,z3,z848,z5,z6])],[(0,[z0,z1,z849,z4,z5,z6]),(0,[z0,z1,z17,z850,z5,z6]),(0,[z0,z851,z1,z4,z5,z6]),(0,[z852,z300,z1,z4,z5,z6]),(0,[z0,z91,z1,z5,z223,z6]),(0,[z0,z1,z4,z317,z5,z6])]],
   [[(0,[z0,z1,z853,z4,z5,z6]),(0,[z0,z1,z17,z854,z5,z6]),(0,[z160,z570,z3,z4,z5,z6]),(0,[z0,z3,z73,z855,z5,z6]),(0,[z0,z1,z3,z856,z5,z6]),(0,[z86,z1,z257,z4,z5,z6])],[(0,[z35,z1,z34,z51,z5,z6]),(0,[z0,z1,z857,z4,z5,z6]),(0,[z0,z1,z3,z858,z5,z6])],[(0,[z0,z46,z17,z73,z5,z6]),(0,[z1,z17,z4,z5,z6,z669]),(0,[z0,z859,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z131,z6]),(0,[z0,z1,z4,z860,z5,z6]),(0,[z0,z1,z3,z5,z861,z6]),(0,[z0,z1,z3,z142,z182,z22])],[(0,[z61,z1,z17,z4,z5,z6]),(0,[z636,z1,z3,z4,z69,z6]),(0,[z862,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z863]),(0,[z0,z1,z864,z4,z5,z6]),(0,[z106,z0,z1,z4,z865,z6]),(0,[z0,z1,z87,z81,z5,z6]),(0,[z0,z866,z3,z4,z5,z6])],[(0,[z0,z1,z3,z867,z5,z6]),(0,[z0,z868,z3,z4,z5,z6]),(0,[z0,z1,z17,z869,z5,z6]),(0,[z0,z1,z16,z4,z5,z194]),(0,[z139,z1,z3,z36,z5,z6]),(0,[z0,z1,z870,z4,z5,z6])],[(0,[z871,z0,z1,z3,z4,z5]),(0,[z243,z0,z1,z4,z5,z55]),(0,[z0,z1,z872,z4,z5,z6]),(0,[z174,z1,z261,z4,z5,z28]),(0,[z135,z1,z129,z4,z5,z6]),(0,[z0,z3,z779,z4,z5,z6])],[(0,[z0,z1,z873,z4,z5,z6]),(0,[z1,z17,z4,z5,z535,z6]),(0,[z0,z204,z58,z4,z5,z6]),(0,[z143,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z874,z5,z6]),(0,[z0,z1,z3,z50,z5,z49]),(0,[z200,z0,z4,z5,z6,z405])],[(0,[z27,z1,z17,z4,z70,z6]),(0,[z0,z1,z58,z4,z20,z6]),(0,[z121,z0,z3,z131,z130,z6])]],
   [[(0,[z0,z1,z875,z3,z4,z5]),(0,[z121,z0,z58,z4,z130,z6]),(0,[z312,z1,z3,z36,z5,z6]),(0,[z0,z1,z150,z292,z5,z6]),(0,[z0,z876,z3,z4,z5,z6]),(0,[z877,z1,z3,z4,z5,z6]),(0,[z0,z878,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z879]),(0,[z574,z3,z4,z5,z6,z25])],[(0,[z1,z17,z4,z5,z542,z6]),(0,[z0,z880,z3,z4,z5,z6]),(0,[z0,z1,z150,z4,z5,z6]),(0,[z881,z0,z1,z4,z5,z6]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z115]),(0,[z121,z0,z300,z4,z130,z6]),(0,[z0,z1,z80,z4,z81,z6])],[(0,[z0,z1,z58,z461,z5,z6]),(0,[z1,z829,z3,z4,z5,z6]),(0,[z883,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z884,z5,z6]),(0,[z1,z3,z4,z142,z25,z22])],[(0,[z443,z1,z17,z4,z5,z6]),(0,[z0,z1,z58,z151,z12,z6]),(0,[z1,z3,z885,z51,z5,z6]),(0,[z886,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z887,z5,z6]),(0,[z0,z1,z3,z888,z5,z6]),(0,[z889,z1,z3,z4,z5,z6]),(0,[z0,z119,z3,z267,z5,z154]),(0,[z0,z1,z3,z163,z5,z6]),(0,[z1,z890,z3,z4,z5,z6])],[(0,[z0,z1,z891,z4,z5,z6]),(0,[z0,z77,z1,z17,z4,z108]),(0,[z0,z1,z3,z5,z6,z892]),(0,[z893,z0,z1,z3,z5,z6])],[(0,[z0,z402,z129,z4,z5,z6]),(0,[z690,z1,z17,z4,z5,z6]),(0,[z0,z1,z58,z503,z5,z6]),(0,[z86,z0,z1,z4,z5,z249]),(0,[z0,z64,z4,z5,z685,z6]),(0,[z0,z894,z3,z4,z5,z6])],[(0,[z0,z1,z17,z5,z895,z6]),(0,[z0,z17,z4,z5,z6,z405]),(0,[z0,z896,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z741,z6]),(0,[z0,z162,z272,z3,z5,z6]),(0,[z0,z46,z3,z5,z600,z6])],[(0,[z48,z0,z1,z17,z53,z6]),(0,[z71,z1,z17,z4,z5,z6]),(0,[z0,z1,z58,z441,z5,z6]),(0,[z0,z897,z3,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z898,z5,z6]),(0,[z0,z1,z3,z50,z5,z282]),(0,[z0,z1,z3,z899,z5,z6]),(1,[z0,z1,z4,z5,z846])],[(0,[z721,z205,z3,z4,z5,z6]),(0,[z19,z62,z3,z4,z5,z37]),(0,[z0,z900,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z405,z25])],[(0,[z169,z1,z17,z4,z69,z6]),(0,[z0,z7,z779,z4,z5,z6]),(0,[z0,z1,z901,z4,z5,z6])],[(0,[z135,z1,z4,z81,z5,z6]),(0,[z376,z7,z129,z4,z5,z6]),(0,[z0,z1,z4,z865,z107,z6]),(0,[z368,z0,z1,z3,z5,z6]),(0,[z200,z0,z1,z5,z6,z123])],[(0,[z0,z902,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z154,z102]),(0,[z0,z1,z4,z5,z254,z646]),(0,[z86,z0,z1,z441,z5,z41]),(0,[z0,z1,z903,z4,z5,z6])],[(0,[z0,z1,z40,z4,z5,z26]),(0,[z11,z0,z1,z3,z5,z105])],[(0,[z124,z1,z17,z4,z5,z6]),(0,[z765,z1,z4,z5,z130,z6]),(0,[z0,z1,z904,z4,z5,z6]),(0,[z905,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z906,z5]),(0,[z1,z17,z265,z4,z5,z6]),(0,[z48,z0,z1,z58,z53,z6]),(0,[z549,z1,z58,z4,z5,z6]),(0,[z1,z126,z4,z5,z70,z6]),(0,[z0,z119,z3,z4,z5,z154])]],
   [[(0,[z0,z91,z1,z17,z5,z6]),(0,[z0,z1,z84,z296,z5,z6]),(0,[z0,z122,z3,z4,z94,z6]),(0,[z0,z1,z907,z4,z5,z6]),(0,[z0,z908,z3,z4,z5,z6])],[(0,[z327,z1,z909,z4,z5,z6]),(0,[z0,z46,z58,z73,z5,z6]),(0,[z0,z1,z58,z141,z5,z6]),(0,[z0,z1,z58,z756,z5,z6]),(0,[z0,z119,z3,z4,z5,z774])],[(0,[z0,z1,z910,z4,z5,z6]),(0,[z0,z1,z3,z4,z911,z6]),(0,[z0,z1,z3,z912,z5,z6]),(0,[z1,z17,z4,z5,z26,z6]),(0,[z19,z1,z17,z4,z5,z37]),(0,[z0,z1,z3,z4,z913,z6]),(0,[z0,z1,z3,z5,z914,z6]),(0,[z0,z1,z3,z4,z747,z6]),(0,[z0,z3,z4,z5,z6,z774]),(0,[z86,z388,z1,z4,z5,z6]),(0,[z0,z1,z4,z915,z5,z6]),(0,[z143,z368,z1,z3,z5,z6])],[(1,[z1,z17,z4,z20,z6]),(0,[z1,z17,z4,z5,z6,z25]),(0,[z0,z1,z3,z4,z916,z6]),(0,[z0,z917,z1,z4,z5,z6]),(0,[z0,z3,z4,z94,z6,z308]),(0,[z0,z1,z3,z5,z6,z918]),(0,[z0,z1,z3,z919,z5,z6])],[(0,[z234,z205,z3,z269,z5,z6]),(0,[z0,z1,z920,z4,z5,z6])],[(0,[z1,z3,z4,z5,z736,z37]),(0,[z0,z1,z921,z4,z5,z6]),(0,[z0,z1,z73,z317,z5,z6]),(1,[z765,z1,z4,z5,z6]),(0,[z0,z1,z687,z39,z5,z6])],[(0,[z0,z1,z396,z4,z5,z6]),(0,[z0,z1,z17,z922,z5,z6]),(0,[z1,z17,z4,z5,z594,z6]),(0,[z160,z1,z3,z4,z20,z6]),(0,[z0,z1,z3,z923,z5,z6]),(1,[z0,z1,z3,z5,z879])],[(0,[z303,z0,z265,z4,z5,z6]),(0,[z0,z1,z3,z4,z924,z6]),(0,[z0,z186,z3,z190,z5,z6]),(0,[z169,z1,z150,z4,z69,z6]),(0,[z0,z1,z3,z925,z5,z6])]],
   [[(0,[z0,z62,z17,z4,z5,z6]),(0,[z0,z91,z1,z58,z5,z6]),(0,[z0,z1,z3,z926,z5,z6]),(0,[z0,z1,z3,z4,z5,z927]),(0,[z928,z1,z3,z4,z5,z6]),(0,[z0,z1,z929,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z817]),(0,[z0,z1,z3,z5,z6,z930]),(0,[z0,z1,z58,z561,z5,z6]),(0,[z0,z1,z4,z5,z6,z931]),(0,[z0,z1,z932,z4,z5,z6])],[(0,[z98,z1,z17,z4,z5,z6]),(0,[z19,z1,z17,z350,z5,z6]),(0,[z0,z3,z267,z5,z154,z6]),(0,[z933,z1,z3,z4,z5,z6]),(0,[z11,z0,z3,z252,z5,z6])],[(0,[z1,z17,z4,z5,z67,z6]),(0,[z934,z1,z3,z4,z5,z6])],[(0,[z935,z0,z1,z4,z5,z6]),(0,[z57,z0,z3,z4,z5,z774]),(0,[z0,z936,z3,z4,z5,z6]),(0,[z937,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z254,z846]),(0,[z0,z3,z4,z142,z405,z22]),(0,[z574,z368,z0,z3,z5,z6])],[(0,[z0,z1,z237,z4,z5,z6]),(0,[z1,z159,z17,z4,z5,z6]),(0,[z462,z1,z17,z4,z5,z6]),(0,[z19,z1,z3,z4,z5,z175]),(0,[z0,z3,z4,z855,z5,z6]),(0,[z0,z1,z938,z4,z5,z6]),(0,[z939,z1,z3,z4,z5,z6]),(0,[z940,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z941]),(0,[z1,z3,z4,z5,z6,z942]),(0,[z0,z1,z3,z151,z580,z6])],[(0,[z1,z17,z4,z92,z5,z6]),(0,[z0,z943,z3,z4,z5,z6]),(0,[z181,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z100,z5,z6]),(0,[z368,z0,z1,z5,z6,z32])]],
   [[(0,[z0,z1,z944,z4,z5,z6]),(1,[z1,z829,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z945]),(0,[z0,z946,z3,z4,z5,z6]),(0,[z0,z1,z3,z947,z5,z6]),(0,[z0,z1,z42,z151,z12,z6])],[(0,[z0,z93,z3,z114,z5,z6]),(0,[z0,z1,z948,z4,z5,z6]),(0,[z0,z1,z217,z350,z5,z6]),(0,[z0,z1,z4,z5,z949,z6]),(0,[z0,z950,z1,z3,z5,z6]),(0,[z388,z1,z84,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z951]),(0,[z0,z1,z952,z4,z5,z6])],[(0,[z48,z0,z1,z3,z628,z6]),(0,[z174,z1,z3,z4,z5,z736]),(0,[z121,z0,z3,z4,z747,z6]),(0,[z953,z1,z3,z4,z5,z6])],[(0,[z607,z93,z3,z4,z5,z6]),(0,[z160,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z4,z954,z6]),(0,[z106,z0,z1,z4,z437,z6]),(0,[z0,z955,z3,z4,z5,z6])],[(0,[z0,z1,z3,z956,z4,z5]),(0,[z0,z1,z3,z957,z5,z6]),(0,[z607,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z428,z22]),(0,[z0,z3,z4,z5,z6,z958])],[(0,[z0,z1,z3,z269,z5,z6]),(0,[z501,z1,z17,z4,z5,z6]),(0,[z0,z1,z959,z4,z5,z6]),(0,[z0,z1,z17,z5,z6,z123]),(0,[z518,z1,z17,z4,z5,z6])],[(0,[z0,z205,z3,z461,z5,z6]),(0,[z160,z1,z373,z4,z5,z6]),(0,[z61,z1,z3,z51,z5,z6]),(0,[z0,z1,z4,z5,z960,z6]),(0,[z0,z1,z4,z5,z6,z961]),(0,[z0,z1,z962,z4,z5,z6])],[(0,[z170,z3,z17,z4,z5,z6]),(0,[z0,z1,z261,z4,z5,z6]),(0,[z0,z570,z217,z4,z5,z6]),(0,[z0,z3,z5,z6,z123,z405])]],
   [[(0,[z19,z1,z17,z100,z5,z6]),(0,[z19,z1,z17,z4,z421,z6])],[(0,[z1,z17,z4,z5,z633,z6]),(0,[z35,z1,z510,z51,z5,z6]),(0,[z0,z1,z963,z4,z5,z6]),(0,[z0,z1,z964,z4,z5,z6]),(0,[z0,z202,z3,z72,z5,z6]),(0,[z0,z3,z503,z252,z5,z6]),(0,[z143,z574,z3,z4,z5,z6])],[(0,[z0,z1,z965,z4,z5,z6]),(0,[z0,z274,z159,z4,z5,z6]),(0,[z0,z570,z3,z350,z5,z6]),(0,[z0,z1,z8,z81,z5,z6]),(0,[z0,z1,z3,z4,z5,z966]),(0,[z0,z967,z1,z3,z5,z6])],[(0,[z0,z1,z17,z4,z20,z6]),(0,[z35,z1,z58,z51,z5,z6]),(0,[z0,z1,z3,z968,z5,z6]),(0,[z0,z1,z104,z612,z5,z6])],[(0,[z205,z17,z4,z72,z5,z6]),(0,[z121,z0,z17,z4,z130,z6]),(0,[z0,z1,z3,z5,z6,z969]),(0,[z0,z1,z970,z4,z5,z6]),(0,[z143,z200,z1,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z971]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z121,z0,z3,z114,z130,z6]),(0,[z973,z1,z3,z4,z5,z6]),(0,[z0,z765,z1,z4,z5,z6]),(0,[z0,z1,z3,z50,z5,z879])],[(0,[z139,z1,z111,z36,z5,z6])],[(0,[z0,z1,z974,z4,z5,z6]),(0,[z0,z1,z17,z151,z12,z6]),(0,[z0,z62,z58,z4,z5,z6]),(0,[z0,z570,z396,z4,z5,z6]),(0,[z0,z1,z217,z4,z421,z6]),(0,[z143,z1,z3,z5,z6,z123]),(0,[z0,z1,z3,z975,z5,z6])]],
   [[(0,[z0,z760,z1,z17,z5,z6]),(0,[z0,z1,z3,z976,z5,z6]),(0,[z0,z1,z3,z977,z5,z6])],[(0,[z0,z119,z3,z4,z5,z416]),(0,[z0,z1,z58,z4,z142,z22]),(0,[z19,z1,z3,z4,z5,z736]),(0,[z48,z0,z1,z317,z5,z6])],[(0,[z1,z17,z4,z5,z70,z6]),(0,[z74,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z350,z421,z6]),(0,[z0,z38,z1,z978,z5,z6]),(0,[z0,z1,z3,z50,z5,z664])],[(0,[z0,z979,z3,z4,z5,z6]),(0,[z0,z1,z17,z441,z5,z6]),(0,[z0,z1,z980,z4,z5,z6]),(0,[z0,z170,z3,z190,z5,z6]),(0,[z0,z300,z1,z4,z5,z6]),(0,[z0,z1,z84,z39,z5,z6]),(0,[z0,z1,z3,z5,z879,z105])],[(0,[z0,z1,z3,z981,z5,z6]),(0,[z226,z1,z17,z4,z5,z6]),(0,[z106,z74,z1,z4,z107,z6]),(0,[z0,z204,z3,z50,z5,z49]),(0,[z0,z1,z3,z4,z713,z142]),(0,[z1,z3,z5,z6,z123,z25])],[(0,[z119,z205,z17,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z982]),(0,[z1,z708,z17,z4,z5,z6]),(0,[z232,z1,z17,z4,z5,z6]),(0,[z74,z1,z373,z4,z5,z6]),(0,[z143,z1,z3,z4,z20,z6]),(0,[z0,z7,z288,z4,z5,z6]),(0,[z0,z983,z3,z4,z5,z6])],[(0,[z95,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z984,z5,z6]),(0,[z0,z1,z4,z5,z865,z6]),(0,[z0,z1,z3,z5,z49,z879]),(0,[z574,z200,z0,z4,z5,z6])],[(0,[z0,z110,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z985,z6]),(0,[z0,z1,z396,z4,z421,z6]),(0,[z0,z1,z3,z986,z5,z6])]],
   [[(0,[z0,z1,z829,z4,z5,z6]),(0,[z0,z1,z3,z987,z5,z6]),(0,[z0,z570,z3,z100,z5,z6]),(0,[z0,z570,z3,z4,z421,z6]),(0,[z388,z64,z1,z4,z5,z6]),(0,[z0,z122,z3,z4,z747,z6]),(1,[z0,z3,z4,z5,z774]),(0,[z0,z988,z3,z4,z5,z6])],[(0,[z0,z1,z989,z4,z5,z6]),(0,[z169,z1,z723,z4,z5,z6]),(0,[z0,z1,z58,z114,z5,z6]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z991,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z978,z5,z6]),(0,[z992,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z993,z5,z6]),(0,[z0,z1,z4,z5,z6,z994]),(0,[z0,z378,z3,z72,z5,z6]),(0,[z0,z1,z995,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z713])],[(0,[z1,z17,z4,z5,z191,z6]),(0,[z419,z1,z17,z4,z5,z6]),(0,[z0,z186,z3,z292,z5,z6]),(0,[z0,z1,z3,z996,z5,z6]),(0,[z0,z1,z3,z229,z5,z6])],[(0,[z0,z186,z3,z4,z5,z6]),(0,[z160,z1,z15,z4,z5,z6]),(0,[z0,z1,z17,z752,z5,z6]),(0,[z0,z1,z58,z5,z6,z123]),(0,[z0,z1,z3,z997,z5,z6]),(0,[z0,z1,z3,z5,z182,z6])],[(0,[z1,z257,z17,z4,z5,z6]),(0,[z0,z1,z17,z141,z5,z6]),(0,[z0,z1,z3,z998,z5,z6]),(0,[z0,z1,z999,z4,z5,z6]),(0,[z294,z1,z396,z4,z5,z6]),(0,[z0,z1,z3,z1000,z5,z6])],[(0,[z0,z1,z58,z5,z131,z6]),(0,[z0,z1,z58,z1001,z5,z6]),(0,[z0,z1,z3,z1002,z5,z6]),(0,[z0,z1,z1003,z4,z5,z6]),(0,[z574,z0,z4,z5,z6,z32])],[(0,[z0,z1,z235,z269,z5,z6]),(0,[z244,z1,z17,z4,z5,z6]),(0,[z422,z1,z17,z4,z5,z6]),(0,[z550,z1,z58,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z405])]],
   [[(0,[z0,z1004,z3,z4,z5,z6]),(0,[z0,z1,z3,z100,z421,z6]),(0,[z0,z1,z3,z5,z1005,z6])],[(0,[z205,z241,z17,z4,z5,z6]),(0,[z0,z3,z855,z72,z5,z6])],[(0,[z0,z1,z1006,z4,z5,z6]),(0,[z143,z1,z58,z4,z5,z6]),(0,[z0,z1,z606,z39,z5,z6]),(0,[z0,z1,z3,z1007,z5,z6]),(0,[z0,z1,z3,z1008,z5,z6])],[(0,[z0,z1,z1009,z4,z5,z6]),(1,[z721,z3,z4,z5,z6]),(0,[z1,z17,z4,z5,z213,z6]),(0,[z0,z1,z3,z4,z1010,z6]),(0,[z0,z1,z3,z1011,z5,z6]),(0,[z0,z1,z3,z8,z5,z6]),(0,[z0,z1,z355,z39,z5,z6]),(0,[z200,z0,z1,z4,z142,z22])],[(0,[z243,z1,z17,z4,z5,z28]),(0,[z0,z1,z4,z1012,z5,z6]),(0,[z0,z1,z1013,z4,z5,z6])],[(0,[z0,z1,z17,z561,z5,z6]),(0,[z0,z1014,z3,z4,z5,z6]),(0,[z1015,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1016,z5,z6])],[(0,[z0,z1,z3,z1017,z5,z6]),(0,[z0,z1,z3,z5,z6,z1018]),(0,[z57,z0,z3,z4,z5,z391])],[(0,[z0,z1,z58,z163,z5,z6]),(0,[z0,z1,z3,z5,z1019,z6])]],
   [[(0,[z291,z0,z1,z4,z444,z6]),(0,[z852,z1,z3,z4,z5,z6]),(0,[z0,z1,z84,z978,z5,z6])],[(0,[z0,z1,z17,z4,z778,z6]),(0,[z0,z110,z34,z4,z5,z6])],[(0,[z234,z205,z235,z4,z5,z6]),(0,[z0,z1020,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1021,z6]),(0,[z19,z1,z17,z4,z5,z6]),(0,[z169,z1,z17,z190,z5,z6]),(0,[z0,z1,z3,z714,z5,z6]),(0,[z1022,z1,z3,z4,z5,z6]),(0,[z368,z1,z3,z5,z6,z25]),(0,[z0,z1,z5,z6,z123,z32])],[(0,[z533,z1,z58,z4,z5,z6]),(0,[z376,z1,z3,z445,z5,z6]),(0,[z0,z3,z4,z5,z747,z6]),(0,[z0,z1,z4,z5,z6,z846])],[(0,[z327,z93,z3,z4,z5,z6]),(0,[z121,z205,z17,z4,z5,z6]),(0,[z0,z1,z3,z1023,z5,z6]),(0,[z0,z245,z17,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z25]),(0,[z0,z1,z3,z4,z6,z1024]),(0,[z0,z119,z3,z503,z5,z154])],[(0,[z327,z1,z17,z4,z5,z6]),(0,[z0,z7,z265,z4,z5,z6]),(0,[z0,z1,z396,z4,z20,z6]),(0,[z106,z0,z1,z4,z364,z6]),(0,[z1025,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1026,z5,z6]),(0,[z0,z1,z3,z4,z5,z1027]),(0,[z0,z1,z3,z1028,z5,z6]),(0,[z0,z1,z1029,z4,z5,z6])],[(0,[z0,z1,z463,z269,z5,z6]),(0,[z1,z17,z4,z5,z444,z6]),(0,[z0,z1,z4,z5,z1030,z6]),(0,[z0,z1,z80,z4,z276,z6]),(0,[z0,z38,z1,z104,z5,z6]),(0,[z0,z1,z1031,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z1032,z5,z6]),(0,[z307,z93,z3,z4,z5,z6]),(0,[z0,z1,z4,z1033,z5,z6]),(0,[z0,z1,z3,z87,z5,z6]),(0,[z0,z1,z4,z5,z6,z1034])],[(0,[z307,z1,z17,z4,z5,z6]),(0,[z0,z1,z217,z4,z5,z6]),(0,[z0,z64,z140,z4,z5,z6])],[(0,[z19,z1,z708,z4,z5,z6]),(0,[z169,z186,z3,z4,z69,z6]),(0,[z0,z1,z80,z561,z81,z6]),(0,[z0,z1,z3,z4,z713,z5]),(0,[z0,z1,z4,z5,z6,z1035])],[(0,[z0,z1,z16,z4,z5,z254]),(0,[z1036,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1037,z5,z6]),(0,[z0,z1,z3,z1038,z5,z6]),(0,[z0,z1039,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z846,z41])],[(0,[z487,z1,z17,z4,z5,z6]),(0,[z0,z122,z58,z4,z94,z6]),(0,[z0,z1,z3,z350,z5,z6]),(0,[z0,z481,z3,z72,z5,z6]),(0,[z0,z1,z4,z5,z6,z1040])],[(0,[z388,z1,z3,z4,z5,z6]),(0,[z0,z659,z3,z72,z5,z6]),(0,[z0,z1,z3,z1041,z5,z6])],[(0,[z0,z1,z3,z4,z1042,z6]),(0,[z1043,z0,z1,z17,z4,z6]),(0,[z143,z1,z3,z4,z69,z6]),(0,[z0,z1,z3,z100,z20,z6]),(0,[z0,z1,z3,z4,z5,z1044]),(0,[z0,z1,z3,z1045,z5,z6]),(0,[z0,z472,z1,z104,z5,z6]),(0,[z388,z1,z4,z104,z5,z6]),(0,[z0,z1,z3,z5,z1046,z6]),(0,[z86,z0,z1,z87,z5,z41]),(0,[z0,z1,z3,z5,z6,z1047]),(0,[z0,z1,z1048,z4,z5,z6])],[(0,[z45,z205,z3,z4,z5,z6]),(0,[z35,z1,z17,z51,z5,z6]),(0,[z77,z1,z17,z4,z70,z6]),(0,[z1,z3,z17,z4,z20,z6]),(0,[z0,z170,z3,z292,z5,z6]),(0,[z48,z0,z1,z3,z60,z6]),(0,[z0,z1,z3,z1049,z5,z6]),(0,[z0,z1,z1050,z4,z5,z6])]],
   [[(0,[z0,z1,z1051,z4,z5,z6]),(0,[z0,z170,z3,z4,z5,z6]),(0,[z169,z1,z17,z4,z70,z6]),(0,[z0,z1,z3,z5,z1052,z6]),(0,[z0,z46,z3,z252,z5,z6]),(0,[z0,z119,z3,z141,z5,z154]),(0,[z0,z1,z4,z1053,z5,z6]),(0,[z0,z1,z768,z4,z5,z6]),(0,[z0,z4,z5,z6,z32,z405])],[(0,[z0,z1,z1054,z4,z5,z6]),(0,[z0,z1055,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z746,z6]),(0,[z0,z1,z4,z1056,z5,z6]),(0,[z0,z1,z4,z5,z6,z1057]),(0,[z0,z1,z3,z50,z5,z413]),(0,[z0,z1,z1058,z4,z5,z6]),(0,[z0,z1059,z3,z4,z5,z6])],[(0,[z0,z570,z3,z4,z5,z6]),(0,[z174,z1,z3,z4,z5,z28]),(0,[z0,z1,z1060,z4,z5,z6])],[(0,[z0,z1,z235,z4,z5,z6]),(0,[z0,z1,z3,z1061,z5,z6]),(0,[z0,z1,z3,z1062,z5,z6]),(0,[z0,z721,z3,z4,z5,z6]),(0,[z0,z1,z1063,z4,z5,z6]),(0,[z0,z1,z1064,z4,z5,z6]),(0,[z0,z1,z3,z1065,z5,z6]),(0,[z0,z1066,z3,z4,z5,z6])],[(0,[z376,z1,z3,z4,z5,z6]),(0,[z1,z17,z281,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1067]),(0,[z0,z1,z3,z1068,z5,z6]),(0,[z1,z257,z4,z5,z254,z6])],[(0,[z0,z205,z3,z114,z5,z6]),(0,[z0,z1,z17,z4,z142,z22]),(1,[z0,z3,z4,z747,z6])],[(0,[z721,z1,z3,z4,z5,z6]),(0,[z1,z17,z4,z5,z68,z6]),(0,[z74,z1,z17,z4,z5,z6]),(0,[z376,z1,z3,z8,z5,z6]),(0,[z1,z3,z4,z5,z6,z1069])],[(0,[z871,z0,z1,z17,z4,z5]),(0,[z0,z1,z3,z190,z5,z6]),(0,[z57,z0,z3,z4,z5,z627])]],
   [[(0,[z1,z17,z4,z297,z5,z6]),(0,[z356,z1,z3,z4,z70,z6]),(0,[z574,z0,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1070])],[(0,[z0,z1,z220,z39,z5,z6]),(0,[z0,z245,z510,z4,z5,z6])],[(0,[z1,z17,z4,z5,z6,z89]),(0,[z1,z17,z90,z4,z5,z6]),(0,[z0,z1,z3,z4,z421,z6]),(0,[z483,z0,z3,z72,z5,z6]),(0,[z0,z1,z4,z5,z6,z32])],[(0,[z19,z570,z17,z4,z5,z6]),(0,[z0,z245,z58,z4,z5,z6])],[(0,[z1,z205,z17,z4,z5,z6]),(0,[z57,z0,z3,z267,z5,z6]),(0,[z0,z1,z3,z4,z865,z6])],[(0,[z0,z1,z17,z114,z5,z6]),(0,[z0,z3,z4,z1071,z5,z6]),(0,[z0,z162,z3,z72,z5,z6]),(0,[z0,z1,z1072,z4,z5,z6]),(0,[z1,z4,z5,z6,z32,z25]),(0,[z368,z0,z3,z5,z6,z405])],[(0,[z0,z1,z3,z1073,z5,z6]),(0,[z327,z93,z15,z4,z5,z6]),(0,[z495,z1,z17,z4,z5,z6]),(0,[z419,z1,z3,z51,z5,z6]),(0,[z19,z1,z3,z4,z5,z372]),(0,[z1074,z1,z3,z4,z5,z6]),(0,[z1075,z1,z3,z4,z5,z6]),(0,[z0,z1,z1076,z3,z5,z6])],[(0,[z0,z1,z1077,z4,z5,z6]),(0,[z0,z1,z118,z4,z183,z6]),(0,[z484,z1,z58,z4,z5,z6]),(1,[z1,z3,z885,z5,z6]),(0,[z143,z1,z3,z4,z142,z22])]],
   [[(0,[z294,z1,z3,z4,z5,z6]),(0,[z255,z1,z17,z4,z5,z6]),(0,[z0,z1,z4,z978,z5,z6]),(0,[z0,z1,z3,z1078,z5,z6])],[(0,[z0,z58,z4,z252,z5,z6]),(0,[z0,z1,z3,z1079,z5,z6]),(0,[z0,z1,z1080,z4,z5,z6])],[(0,[z234,z205,z3,z461,z5,z6]),(0,[z1,z15,z17,z4,z5,z6]),(0,[z169,z186,z17,z4,z5,z6]),(0,[z0,z1,z17,z5,z131,z6]),(0,[z1,z373,z17,z4,z5,z6])],[],[(0,[z0,z1,z3,z1081,z5,z6]),(0,[z0,z1,z3,z1082,z5,z6]),(0,[z139,z1,z17,z36,z5,z6]),(0,[z544,z0,z1,z366,z5,z6]),(0,[z0,z1,z1083,z4,z5,z6]),(0,[z0,z1084,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z28,z736]),(0,[z0,z1,z3,z1085,z5,z6]),(0,[z0,z1,z1086,z4,z5,z6]),(0,[z0,z1,z1087,z4,z5,z6]),(0,[z0,z1,z3,z163,z142,z22])],[(0,[z205,z17,z4,z5,z6,z242]),(0,[z368,z0,z1,z17,z5,z6]),(0,[z0,z1,z1088,z4,z5,z6]),(0,[z0,z1,z1089,z4,z5,z6]),(0,[z0,z1090,z3,z4,z5,z6])],[(0,[z402,z205,z3,z4,z5,z6]),(0,[z169,z1,z17,z292,z5,z6]),(0,[z0,z1,z17,z50,z5,z49]),(0,[z143,z1,z17,z4,z5,z6]),(0,[z1,z3,z4,z741,z70,z6]),(0,[z169,z170,z3,z4,z69,z6]),(0,[z135,z1,z3,z445,z5,z6])],[(0,[z169,z1,z17,z4,z5,z6]),(0,[z19,z1,z217,z4,z5,z37]),(0,[z244,z1,z257,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z801,z4,z6]),(0,[z0,z1091,z3,z4,z5,z6]),(0,[z0,z1,z1092,z4,z5,z6]),(0,[z0,z1,z3,z5,z1093,z6]),(0,[z0,z1,z4,z5,z6,z1094]),(0,[z1095,z1,z3,z4,z5,z6])],[(0,[z452,z93,z3,z4,z5,z6]),(0,[z0,z1,z17,z5,z6,z115]),(0,[z0,z1,z3,z5,z6,z1096]),(0,[z0,z1,z3,z5,z1097,z6]),(0,[z203,z0,z1,z3,z5,z105]),(0,[z0,z1,z821,z4,z5,z6])],[(0,[z1,z829,z17,z4,z5,z6]),(0,[z452,z1,z17,z4,z5,z6]),(0,[z679,z1,z17,z4,z5,z6]),(0,[z19,z1,z3,z350,z5,z37]),(0,[z0,z3,z4,z5,z6,z1098]),(0,[z0,z1099,z1,z3,z5,z6]),(0,[z0,z3,z4,z747,z130,z6]),(0,[z57,z0,z3,z4,z5,z242]),(0,[z0,z1,z4,z142,z32,z22])],[(0,[z234,z205,z3,z4,z5,z6]),(0,[z356,z0,z1,z4,z360,z6]),(0,[z0,z1,z17,z163,z5,z6]),(0,[z0,z1,z3,z445,z5,z6]),(0,[z0,z1,z3,z165,z5,z6])],[(0,[z397,z1,z17,z4,z5,z6]),(0,[z1,z17,z4,z5,z6,z346]),(0,[z0,z1,z1100,z4,z5,z6]),(0,[z1,z40,z257,z4,z5,z254]),(0,[z368,z0,z1,z3,z142,z22])],[(0,[z0,z1,z909,z4,z5,z6]),(0,[z660,z1,z17,z4,z5,z6]),(0,[z368,z0,z1,z58,z5,z6]),(0,[z0,z1,z3,z4,z1101,z6]),(0,[z169,z1,z3,z190,z69,z6])],[(0,[z376,z1,z15,z4,z5,z6]),(0,[z1,z404,z17,z4,z5,z6]),(0,[z523,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z301,z12,z6]),(0,[z0,z3,z252,z104,z5,z6])],[(0,[z0,z1,z1102,z4,z5,z6]),(0,[z0,z1,z3,z4,z1103,z6]),(0,[z0,z1,z3,z1104,z5,z6]),(0,[z0,z1,z126,z4,z5,z6]),(0,[z11,z0,z1,z58,z5,z105]),(0,[z0,z245,z3,z51,z5,z6]),(0,[z19,z1,z396,z4,z5,z37]),(0,[z0,z1,z39,z978,z5,z6])]],
   [[(0,[z1,z17,z4,z5,z173,z6]),(0,[z0,z3,z4,z5,z6,z1105]),(0,[z0,z1,z3,z4,z1106,z6]),(0,[z0,z1,z3,z267,z5,z6]),(0,[z0,z1,z3,z4,z5,z1107])],[(0,[z0,z110,z510,z4,z5,z6]),(0,[z0,z1,z72,z317,z5,z6]),(0,[z0,z1,z1108,z4,z5,z6]),(0,[z48,z0,z1,z3,z188,z6])],[(0,[z422,z205,z3,z4,z5,z6]),(0,[z95,z1,z829,z4,z5,z6]),(0,[z418,z1,z17,z4,z5,z6]),(0,[z0,z1,z1109,z4,z5,z6]),(0,[z0,z1110,z3,z4,z5,z6])],[(0,[z0,z1,z3,z461,z5,z6]),(0,[z0,z1,z3,z1111,z5,z6]),(0,[z0,z110,z58,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1112]),(0,[z0,z1,z3,z1113,z5,z6]),(0,[z0,z1,z1114,z4,z5,z6]),(0,[z1115,z1,z3,z4,z5,z6]),(0,[z0,z1116,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1117,z6])],[(0,[z0,z1,z3,z822,z5,z6]),(0,[z244,z0,z1,z4,z5,z249]),(0,[z0,z1,z44,z4,z5,z26]),(0,[z0,z1,z3,z1118,z5,z6]),(0,[z0,z1119,z1,z3,z5,z6])],[(0,[z19,z1,z261,z4,z5,z6]),(0,[z0,z62,z396,z4,z5,z6]),(0,[z0,z77,z1,z3,z4,z713])],[(0,[z0,z1,z118,z4,z81,z6]),(0,[z0,z1,z1120,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1121])],[(0,[z135,z1,z3,z4,z5,z6]),(0,[z1,z909,z17,z4,z5,z6]),(0,[z0,z119,z17,z4,z5,z154]),(0,[z0,z1,z58,z229,z5,z6]),(0,[z0,z245,z3,z36,z5,z6]),(0,[z0,z1,z3,z885,z5,z6]),(0,[z0,z1,z3,z5,z1122,z6])]],
   [[(0,[z0,z1,z3,z1123,z5,z6]),(0,[z1,z17,z4,z5,z20,z6]),(0,[z0,z122,z17,z4,z94,z6]),(0,[z0,z186,z58,z4,z5,z6]),(0,[z0,z1,z58,z5,z182,z6]),(0,[z19,z1,z3,z100,z5,z37]),(0,[z19,z1,z3,z4,z421,z37]),(0,[z0,z3,z114,z5,z154,z6]),(0,[z0,z1,z3,z142,z123,z22])],[(0,[z0,z1,z371,z4,z5,z6]),(0,[z0,z1,z1124,z4,z5,z6]),(0,[z19,z1,z17,z4,z20,z6]),(0,[z1,z17,z4,z5,z6,z383]),(0,[z135,z1,z3,z8,z5,z6]),(0,[z652,z0,z1,z104,z5,z6]),(0,[z0,z1125,z3,z4,z5,z6]),(0,[z0,z1,z3,z1126,z5,z6])],[(0,[z0,z1,z1127,z4,z5,z6]),(0,[z0,z1,z17,z4,z913,z6]),(0,[z35,z245,z3,z51,z5,z6]),(0,[z27,z1,z126,z4,z70,z6]),(0,[z0,z1,z1128,z4,z5,z6]),(0,[z48,z0,z1,z3,z215,z6]),(0,[z0,z1,z317,z5,z6,z105])],[(0,[z205,z17,z4,z94,z5,z6]),(0,[z0,z1,z3,z4,z1129,z6]),(0,[z0,z1,z3,z292,z5,z6]),(0,[z0,z1,z1130,z4,z5,z6]),(0,[z0,z186,z373,z4,z5,z6]),(0,[z169,z1,z3,z4,z741,z6]),(0,[z0,z3,z72,z5,z413,z6]),(0,[z0,z1,z3,z5,z6,z1131]),(0,[z1,z3,z1132,z4,z5,z6]),(0,[z0,z1,z3,z1133,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z1,z447,z17,z4,z5,z6]),(0,[z0,z1134,z3,z4,z5,z6]),(0,[z0,z46,z3,z156,z5,z6]),(0,[z106,z0,z1,z4,z511,z6])],[(0,[z0,z1,z380,z296,z5,z6]),(0,[z0,z1,z58,z50,z5,z49]),(0,[z0,z1,z4,z81,z6,z684])],[(0,[z169,z170,z17,z4,z5,z6]),(0,[z0,z62,z3,z100,z5,z6]),(0,[z0,z3,z50,z252,z5,z49]),(0,[z0,z1,z1135,z4,z5,z6]),(0,[z1136,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z850,z5,z6]),(0,[z0,z1,z3,z4,z1137,z6]),(0,[z0,z1,z373,z292,z5,z6]),(0,[z0,z1138,z3,z4,z5,z6]),(0,[z0,z1,z3,z855,z5,z6]),(0,[z388,z1,z80,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z854,z5,z6]),(0,[z0,z1,z58,z5,z6,z115]),(0,[z0,z1,z217,z4,z20,z6])],[(0,[z1,z118,z17,z4,z70,z6]),(0,[z0,z1,z17,z5,z6,z930]),(0,[z0,z3,z4,z5,z154,z774])],[(0,[z35,z1,z3,z885,z5,z6]),(0,[z45,z1,z3,z51,z5,z6]),(0,[z0,z1,z1139,z4,z5,z6])],[(0,[z0,z1,z3,z350,z20,z6]),(0,[z1140,z0,z1,z3,z5,z6]),(0,[z1141,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z375,z5,z105])],[(0,[z0,z1,z3,z869,z5,z6]),(0,[z0,z1,z3,z1142,z5,z6]),(0,[z0,z1,z3,z4,z1143,z6]),(0,[z209,z0,z1,z3,z5,z105]),(0,[z27,z1,z371,z4,z70,z6]),(0,[z0,z64,z779,z4,z5,z6]),(0,[z0,z1,z4,z5,z1144,z6])],[(0,[z0,z1,z3,z1145,z5,z6]),(0,[z0,z46,z3,z5,z6,z466]),(0,[z0,z1,z3,z1146,z5,z6]),(0,[z0,z1,z3,z4,z5,z846])],[(0,[z0,z1,z3,z1147,z5,z6]),(0,[z0,z46,z3,z503,z5,z6]),(0,[z0,z1,z1148,z4,z5,z6]),(0,[z0,z300,z91,z1,z5,z6])],[(0,[z0,z1,z17,z100,z5,z6]),(0,[z0,z943,z17,z4,z5,z6]),(0,[z0,z1,z1149,z4,z5,z6]),(0,[z27,z1,z3,z4,z70,z6]),(0,[z0,z1,z3,z1150,z5,z6]),(1,[z0,z3,z855,z5,z6]),(0,[z0,z1,z3,z5,z6,z879])]],
   [[(0,[z0,z1,z3,z4,z5,z1151]),(0,[z327,z93,z58,z4,z5,z6]),(0,[z1152,z0,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1153,z6]),(0,[z0,z570,z3,z4,z20,z6]),(0,[z0,z1,z3,z1154,z5,z6]),(0,[z0,z1,z1155,z4,z5,z6])],[(0,[z1,z17,z4,z428,z5,z6]),(0,[z481,z1,z17,z4,z5,z6]),(0,[z1156,z0,z3,z4,z5,z6]),(0,[z0,z1,z40,z4,z5,z846])],[(0,[z379,z1,z17,z4,z5,z6]),(0,[z160,z1,z829,z4,z5,z6])],[(0,[z0,z1,z17,z956,z4,z5]),(0,[z0,z1,z58,z87,z5,z6]),(0,[z0,z1,z978,z104,z5,z6]),(0,[z0,z1,z229,z81,z5,z6]),(0,[z294,z1,z40,z4,z5,z254])],[(0,[z0,z1,z235,z461,z5,z6]),(0,[z0,z1,z17,z269,z5,z6]),(0,[z0,z1,z3,z1157,z5,z6])],[(0,[z0,z1,z3,z1158,z5,z6]),(0,[z0,z1,z34,z4,z5,z6]),(0,[z0,z17,z4,z5,z6,z762]),(0,[z0,z1,z3,z5,z895,z6]),(0,[z0,z119,z58,z4,z5,z154]),(0,[z0,z1,z447,z4,z276,z6]),(0,[z0,z38,z1,z366,z5,z6]),(0,[z300,z765,z1,z4,z5,z6]),(0,[z0,z1,z524,z104,z5,z6]),(0,[z0,z1,z3,z1159,z5,z6]),(0,[z0,z1,z80,z4,z865,z6])],[(0,[z0,z1,z1160,z4,z5,z6]),(0,[z1161,z0,z1,z4,z5,z6]),(0,[z0,z1162,z3,z4,z5,z6]),(0,[z139,z1,z3,z885,z5,z6]),(0,[z0,z1,z4,z5,z223,z6]),(0,[z0,z46,z3,z855,z5,z6]),(0,[z0,z671,z3,z73,z5,z6]),(0,[z200,z0,z1,z4,z5,z6])]],
   [[(0,[z0,z1,z1163,z4,z5,z6]),(0,[z1,z17,z4,z448,z5,z6]),(0,[z1,z17,z4,z451,z5,z6]),(0,[z0,z1,z58,z350,z5,z6]),(0,[z0,z1164,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z736])],[(0,[z0,z1,z3,z1165,z5,z6]),(0,[z388,z1,z58,z4,z5,z6]),(0,[z169,z1,z3,z292,z69,z6]),(0,[z135,z1,z140,z4,z5,z6])],[(0,[z0,z1,z1166,z4,z5,z6]),(0,[z1,z17,z4,z5,z6,z266]),(0,[z35,z110,z3,z51,z5,z6]),(0,[z0,z1,z3,z146,z12,z6]),(0,[z169,z1,z3,z4,z69,z6]),(0,[z0,z1,z1167,z4,z5,z6]),(0,[z0,z1,z1168,z4,z5,z6])],[(0,[z0,z1,z3,z1169,z5,z6]),(0,[z1,z58,z329,z4,z5,z6]),(0,[z255,z1,z3,z36,z5,z6]),(0,[z113,z0,z1,z3,z53,z6]),(0,[z0,z1,z4,z5,z1170,z6])],[(0,[z0,z1,z3,z4,z1171,z6]),(0,[z0,z170,z58,z4,z5,z6]),(0,[z0,z119,z3,z5,z154,z115]),(1,[z0,z1,z4,z865,z6])],[(0,[z234,z205,z463,z4,z5,z6]),(0,[z1172,z0,z1,z4,z5,z6]),(0,[z0,z77,z1,z3,z4,z403]),(0,[z0,z1,z3,z5,z1173,z6]),(0,[z11,z0,z1,z3,z5,z879])],[(0,[z0,z1,z15,z4,z5,z6]),(0,[z0,z402,z236,z4,z5,z6]),(0,[z0,z570,z58,z4,z5,z6]),(0,[z174,z1,z58,z4,z5,z28]),(0,[z0,z1,z3,z804,z5,z6]),(0,[z0,z162,z3,z855,z5,z6]),(0,[z0,z1,z3,z1174,z5,z6]),(0,[z0,z1,z5,z131,z223,z6])],[(0,[z234,z721,z3,z4,z5,z6]),(0,[z57,z0,z17,z4,z5,z242]),(0,[z356,z0,z1,z4,z107,z6]),(0,[z0,z1,z3,z5,z6,z1175]),(0,[z0,z170,z373,z4,z5,z6]),(0,[z0,z1,z1176,z4,z5,z6])]],
   [[(0,[z0,z1,z1177,z4,z5,z6]),(0,[z705,z1,z17,z4,z5,z6]),(0,[z376,z1,z58,z4,z5,z6]),(0,[z0,z1,z3,z1178,z5,z6]),(0,[z0,z1,z3,z1179,z5,z6]),(0,[z1180,z1,z3,z4,z5,z6]),(0,[z200,z1,z4,z5,z6,z25]),(0,[z0,z1181,z3,z4,z5,z6])],[(0,[z522,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z50,z5,z435])],[(0,[z19,z1,z3,z4,z5,z37]),(0,[z0,z162,z3,z252,z5,z6]),(0,[z0,z3,z4,z389,z5,z154]),(0,[z0,z1,z3,z4,z5,z1182]),(0,[z0,z1,z42,z4,z5,z6]),(0,[z1183,z1,z3,z4,z5,z6]),(0,[z0,z1,z1184,z4,z5,z6]),(0,[z0,z1,z3,z486,z53,z6]),(0,[z0,z77,z1,z3,z4,z108])],[(0,[z0,z1185,z3,z4,z5,z6]),(0,[z0,z1,z58,z190,z5,z6]),(0,[z0,z1,z3,z4,z1186,z6])],[(0,[z0,z1,z3,z1187,z5,z6]),(0,[z0,z93,z3,z267,z5,z6]),(0,[z574,z0,z58,z4,z5,z6]),(0,[z0,z1,z1188,z4,z5,z6]),(0,[z143,z1,z3,z4,z70,z6])],[(0,[z0,z1,z463,z461,z5,z6]),(0,[z121,z0,z3,z4,z275,z6]),(0,[z0,z17,z4,z252,z5,z6]),(0,[z0,z1,z3,z4,z5,z1189]),(0,[z0,z1190,z3,z4,z5,z6]),(0,[z121,z0,z91,z3,z130,z6]),(0,[z1191,z1,z3,z4,z5,z6]),(0,[z48,z0,z1,z3,z53,z6])],[(0,[z0,z1,z3,z922,z5,z6]),(0,[z0,z1,z58,z100,z5,z6]),(0,[z0,z1,z58,z4,z421,z6]),(0,[z0,z1,z373,z190,z5,z6]),(0,[z0,z3,z4,z1192,z5,z6]),(0,[z0,z1,z3,z1193,z5,z6]),(0,[z1172,z1,z4,z5,z6,z25])],[(0,[z0,z110,z17,z4,z5,z6]),(0,[z1,z17,z4,z5,z485,z6]),(0,[z0,z1,z1194,z4,z5,z6]),(0,[z1,z3,z4,z5,z28,z211]),(0,[z1195,z1,z3,z4,z5,z6]),(0,[z11,z0,z1,z3,z5,z537]),(0,[z0,z3,z252,z5,z53,z6])]],
   [[(0,[z0,z62,z3,z4,z5,z6]),(0,[z1,z58,z362,z4,z5,z6]),(0,[z0,z1196,z3,z4,z5,z6]),(0,[z0,z779,z129,z4,z5,z6])],[(0,[z0,z1197,z1,z4,z5,z6]),(0,[z0,z1,z3,z824,z5,z6]),(0,[z0,z1,z3,z1198,z5,z6]),(0,[z0,z162,z58,z72,z5,z6]),(0,[z0,z145,z3,z72,z5,z6]),(0,[z106,z135,z1,z4,z5,z6]),(0,[z0,z300,z1,z5,z131,z6])],[(0,[z1,z16,z3,z4,z5,z28]),(0,[z0,z1,z1199,z4,z5,z6]),(0,[z1,z3,z36,z885,z5,z6])],[(0,[z1,z58,z17,z4,z5,z6]),(0,[z0,z1,z17,z229,z5,z6]),(0,[z1,z3,z885,z4,z5,z6]),(0,[z121,z0,z3,z165,z130,z6])],[(0,[z0,z1,z58,z269,z5,z6]),(0,[z0,z186,z17,z4,z5,z6]),(0,[z0,z1020,z1,z17,z5,z6]),(0,[z0,z1,z17,z5,z182,z6]),(0,[z294,z1,z58,z4,z5,z6]),(0,[z0,z1,z1200,z4,z5,z6]),(0,[z0,z1,z3,z4,z1201,z6])],[(0,[z692,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z833,z5,z6]),(1,[z1,z3,z4,z741,z6]),(0,[z0,z1,z4,z81,z865,z6])],[(0,[z0,z1,z463,z4,z5,z6]),(0,[z0,z3,z36,z252,z5,z6]),(0,[z0,z91,z1,z3,z5,z6]),(0,[z0,z1,z317,z12,z5,z6])],[(0,[z0,z1,z3,z1202,z5,z6])]],
   [[(1,[z170,z17,z4,z5,z6]),(0,[z0,z1,z3,z793,z5,z6]),(0,[z0,z1,z58,z1082,z5,z6]),(0,[z0,z1203,z1,z4,z5,z6]),(0,[z1204,z1,z3,z4,z5,z6]),(0,[z106,z0,z1,z4,z107,z6]),(0,[z0,z1,z40,z4,z5,z254])],[(0,[z1043,z0,z1,z3,z4,z6]),(0,[z19,z62,z17,z4,z5,z6]),(0,[z0,z1,z4,z1205,z5,z6]),(0,[z0,z1,z3,z4,z1206,z6]),(0,[z0,z1,z1207,z4,z5,z6]),(0,[z0,z438,z1,z104,z5,z6])],[(0,[z1,z562,z17,z4,z5,z6]),(1,[z570,z17,z4,z5,z6]),(0,[z11,z0,z1,z17,z5,z105]),(0,[z0,z1,z304,z4,z5,z6]),(0,[z0,z1,z1208,z4,z5,z6]),(0,[z0,z1209,z1,z4,z5,z6]),(0,[z0,z1210,z3,z4,z5,z6])],[(0,[z0,z1,z17,z4,z1010,z6]),(0,[z0,z1,z17,z8,z5,z6]),(0,[z160,z170,z3,z4,z5,z6]),(0,[z135,z1,z159,z4,z5,z6]),(0,[z7,z135,z129,z4,z5,z6])],[(0,[z327,z1,z235,z4,z5,z6]),(0,[z327,z721,z3,z4,z5,z6]),(0,[z570,z3,z17,z4,z5,z6]),(0,[z160,z1,z396,z4,z5,z6]),(0,[z0,z1,z3,z1211,z5,z6]),(0,[z0,z1,z1212,z4,z5,z6]),(1,[z0,z1,z978,z5,z6])],[(0,[z327,z205,z17,z4,z5,z6]),(0,[z0,z335,z1,z54,z5,z6]),(0,[z555,z1,z17,z4,z5,z6]),(0,[z0,z1213,z3,z4,z5,z6]),(0,[z0,z1,z1214,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z123])],[(0,[z0,z1,z111,z4,z5,z6]),(0,[z57,z0,z58,z4,z5,z242]),(0,[z388,z7,z1,z4,z5,z6]),(0,[z1215,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z12,z6,z427])],[(0,[z234,z205,z58,z4,z5,z6]),(0,[z0,z1216,z3,z4,z5,z6]),(0,[z0,z1,z58,z165,z5,z6]),(0,[z0,z1,z58,z445,z5,z6]),(0,[z0,z1,z3,z1001,z5,z6]),(0,[z1,z3,z4,z69,z6,z266]),(0,[z121,z0,z3,z4,z324,z6]),(0,[z0,z1,z3,z1217,z5,z6]),(0,[z0,z1,z1218,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1041).take 209) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1250)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 520, 209] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 95).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 195).take 61).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [95, 100, 61] = true :=
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

end PEqualNP.Outside.L_meta_38524

theorem PEqualNP.Outside.L_meta_38524 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373472 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373472 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38524.solve