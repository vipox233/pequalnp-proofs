import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39217

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
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
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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
  Nat.testBit (4277071598 * 2 ^ 32 + 4209043456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
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
  [(0x0004418c417870da#64 ++ 0x20008831882f0e1b#64 ++ 0xd02cd39cc3f8f1ff#64 ++ 0xda059a73987f1e3f#64 : BitVec 256),
   (0x004504a5231b1629#64 ++ 0x4008a094a46362c5#64 ++ 0xe8d72ce7231f1e3f#64 ++ 0xbd1ae59ce463e3c7#64 : BitVec 256),
   (0x131830f80c0dbb45#64 ++ 0x8263061f0181b768#64 ++ 0xb71830f83c1fffc7#64 ++ 0x76e3061f0783fff8#64 : BitVec 256),
   (0x25e03f0036a00db6#64 ++ 0x04bc07e006d401b6#64 ++ 0xf7e03f003fe01ffe#64 ++ 0xfefc07e007fc03ff#64 : BitVec 256),
   (0x0effc0003bd6c000#64 ++ 0x01dff800077ad800#64 ++ 0xbfffc0003fffe005#64 ++ 0xf7fff80007fffc00#64 : BitVec 256),
   (0x07baba5280000000#64 ++ 0x00f7574a50000000#64 ++ 0xcfffffffc0000003#64 ++ 0xf9fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [9, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0004008401181008 0x0000801080230201 0xc8d72ce70318103f 0xb91ae59ce0630207

def z1 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd02cd39cc3f8f1ff 0xda059a73987f1e3f

def z2 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8d72ce7231f1e3f 0xbd1ae59ce463e3c7

def z3 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xcfffffffc0000003 0xf9fffffff8000000

def z4 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffc0003fffe005 0xf7fff80007fffc00

def z5 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb71830f83c1fffc7 0x76e3061f0783fff8

def z6 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e03f003fe01ffe 0xfefc07e007fc03ff

def z7 : W := mkw 0x04a28a0280000000 0x0094514050000000 0x08c30c0300000000 0x0118618060000000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8d72ce700000003 0xb91ae59ce0000000

def z9 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x372013003fe01ffc 0x46e4026007fc03ff

def z10 : W := mkw 0x000000a000091201 0x0000001400012240 0xa01020e0201f1e07 0x3402041c0403e3c0

def z11 : W := mkw 0x135d34fd2f1fbf6d 0xc26ba69fa5e3f7ed 0xffdf3cff3f1fffff 0xfffbe79fe7e3ffff

def z12 : W := mkw 0x031830000c048904 0x0063060001809120 0xb71830003c1fffc7 0x76e306000783fff8

def z13 : W := mkw 0x2fffff003ff6cdb6 0x05ffffe007fed9b6 0xffffff003fffffff 0xffffffe007ffffff

def z14 : W := mkw 0x000001044020009a 0x2000002088040013 0x40000304c0000038 0x0800006098000007

def z15 : W := mkw 0x121800f80c0dbb45 0x8243001f0181b768 0x301800f83c1fffc5 0x0603001f0783fff8

def z16 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf73cf3fcfc1fffc7 0xfee79e7f9f83fff8

def z17 : W := mkw 0x21003b0004200996 0x0420076000840132 0x00001300000001c0 0x0000026000000038

def z18 : W := mkw 0x0040040022000420 0x0008008004400084 0xe0c02c0023001e3e 0xbc180580046003c7

def z19 : W := mkw 0x25e53fa537bb1fbf 0x44bca7f4a6f763f7 0xfff73fe73fff1fff 0xfffee7fce7ffe3ff

def z20 : W := mkw 0x0004400001504000 0x00008800002a0800 0xd02cd39cc3f8e007 0xda059a73987f1c00

def z21 : W := mkw 0x0218000008048000 0x0043000001009000 0xb71800003c1fe005 0x76e300000783fc00

def z22 : W := mkw 0x084540003bd6c000 0x0108a800077ad800 0x300000003fffe004 0x0600000007fffc00

def z23 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x102cd39cc0f8e1c1 0x42059a73981f1c38

def z24 : W := mkw 0x24e00f0032a004b2 0x049c01e006540096 0x40e00f0003e00038 0x881c01e0007c0007

def z25 : W := mkw 0x0100300004000904 0x0020060000800120 0xb70030003c001fc6 0x76e00600078003f8

def z26 : W := mkw 0x0ce7c00033d24000 0x019cf800067a4800 0x08e7c00003e00000 0x811cf800007c0000

def z27 : W := mkw 0x0045040523120428 0x4008a080a4624085 0xe8d70c07231f003d 0xbd1ae180e463e007

def z28 : W := mkw 0x00000188002830d2 0x000000310005061a 0xd028139803f8f1ff 0xda050273007f1e3f

def z29 : W := mkw 0x31003ff804293ff7 0x862007ff008527fe 0x40003ff800001ffa 0x080007ff000003ff

def z30 : W := mkw 0x37f83ff83eadbff7 0x86ff07ff07d5b7fe 0xf7f83ff83fffffff 0xfeff07ff07ffffff

def z31 : W := mkw 0x000000a800093241 0x0000001500012648 0xb01830f8201fffc7 0x7603061f0403fff8

def z32 : W := mkw 0x100000a80c0dbb45 0x820000150181b768 0x300000003c1fffc4 0x060000000783fff8

def z33 : W := mkw 0x24a00b0010a00092 0x0494016002140012 0x0020030000e00000 0x00040060001c0000

def z34 : W := mkw 0x0effc4003bd6c420 0x01dff880077ad884 0xffffec003ffffe3f 0xfffffd8007ffffc7

def z35 : W := mkw 0x104504ad2f1fbf6d 0xc208a095a5e3f7ed 0xf8d72ce73f1fffff 0xbf1ae59ce7e3ffff

def z36 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x28d32c63231f1e3c 0x251a658c6463e3c7

def z37 : W := mkw 0x07befbdec17870da 0x20f7df7bd82f0e1b 0xdfffffffc3f8f1ff 0xfbfffffff87f1e3f

def z38 : W := mkw 0x17befbfecd7dfbdf 0xa2f7df7fd9afbf7b 0xffffffffffffffff 0xffffffffffffffff

def z39 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4fd33fffc0000002 0x29fa67fff8000000

def z40 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x8fffec6300000001 0xf1fffd8c60000000

def z41 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffece73fffe007 0xfffffd9ce7fffc00

def z42 : W := mkw 0x135d34fd2f1fbf6d 0xc26ba69fa5e3f7ed 0xb71830f83f1fffff 0x76e3061f07e3ffff

def z43 : W := mkw 0x04a28a0280000000 0x0094514050000000 0x0020c300c0000000 0x0004186018000000

def z44 : W := mkw 0x110030f804093b45 0x8220061f00812768 0x000030f800001fc2 0x0000061f000003f8

def z45 : W := mkw 0x1ffff0f83fdffb45 0x83fffe1f07fbff68 0xbffff0f83fffffc7 0xf7fffe1f07fffff8

def z46 : W := mkw 0x0000000800002040 0x0000000100000408 0x100810180000e1c0 0x4201020300001c38

def z47 : W := mkw 0x000500a5011b1209 0x4000a014a0236241 0x081700e7001f0001 0x0102e01ce003e000

def z48 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x371020603c1fffc4 0x26e2040c0783fff8

def z49 : W := mkw 0x01003a5280000000 0x0020074a50000000 0x00002c6300000000 0x0000058c60000000

def z50 : W := mkw 0x000441844178509a 0x20008830882f0a13 0xc024c384c3f8103f 0x98049870987f0207

def z51 : W := mkw 0x24e00f0032a004b2 0x049c01e006540096 0xd0e01f0003e011fe 0xda1c03e0007c023f

def z52 : W := mkw 0x27babf5284200db6 0x04f757ea508401b6 0xcfffffffc0001ffb 0xf9fffffff80003ff

def z53 : W := mkw 0x004504ad231b3669 0x4008a095a46366cd 0xf8df3cff231fffff 0xff1be79fe463ffff

def z54 : W := mkw 0x0100308804083944 0x0020061100810728 0xb70830983c18ffc7 0x76e1061307831ff8

def z55 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x370810183c1fffc4 0x46e102030783fff8

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00000000300103e 0x9800000000600207

def z57 : W := mkw 0x004545ad637b76fb 0x6008a8b5ac6f6edf 0xf02cd39ce3ffffff 0xde059a739c7fffff

def z58 : W := mkw 0x0ffffa52bbd6c000 0x01ffff4a577ad800 0xffffffffffffe007 0xfffffffffffffc00

def z59 : W := mkw 0x0845418c7bfef0da 0x2108a8318f7fde1b 0xf02cd39cfffff1ff 0xde059a739ffffe3f

def z60 : W := mkw 0x084544a53bdfd629 0x4108a894a77bfac5 0xf8d72ce73ffffe3f 0xbf1ae59ce7ffffc7

def z61 : W := mkw 0x000540ad415b7249 0x6000a815a82b6e49 0x081fc0ffc01fe001 0x0103f81ff803fc00

def z62 : W := mkw 0x25e03f8836a83df6 0x04bc07f106d507be 0xf7e83f983ff8ffff 0xfefd07f307ff1fff

def z63 : W := mkw 0x0004408c41587048 0x20008811882b0e09 0x000cc09cc018e001 0x0001981398031c00

def z64 : W := mkw 0x21003f0004200db6 0x042007e0008401b6 0x40003f0000001ffa 0x080007e0000003ff

def z65 : W := mkw 0x25e03f8c76a83dfe 0x24bc07f18ed507bf 0xf7e03f9cffe01ffe 0xfefc07f39ffc03ff

def z66 : W := mkw 0x25e03e0036800d24 0x04bc07c006d001a4 0x27c02c003c000e00 0x24f80580078001c0

def z67 : W := mkw 0x0045040523120428 0x4008a080a4624085 0x0000000003000038 0x0000000000600007

def z68 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd004008403f8f1ff 0x9a008010807f1e3f

def z69 : W := mkw 0x2de7ff0037f24db6 0x05bcffe006fe49b6 0xffe7ff003fe01ffe 0xfffcffe007fc03ff

def z70 : W := mkw 0x0040040022000420 0x0008008004400084 0x2000000023001e3c 0x04000000046003c7

def z71 : W := mkw 0x0effc4a53bdfd629 0x41dff894a77bfac5 0xffffece73ffffe3f 0xfffffd9ce7ffffc7

def z72 : W := mkw 0x2fffffa53fffdfbf 0x45fffff4a7fffbf7 0xffffffe73fffffff 0xfffffffce7ffffff

def z73 : W := mkw 0x004500a5231b1209 0x4008a014a4636241 0xa8d700e7231f0005 0xb51ae01ce463e000

def z74 : W := mkw 0x0effc0843bded008 0x01dff810877bda01 0xffffc0843ffff03f 0xfffff81087fffe07

def z75 : W := mkw 0x021a805280000000 0x0043500a50000000 0x0813006300000000 0x0102600c60000000

def z76 : W := mkw 0x131c71fc4d7dfbdf 0xa2638e3f89afbf7b 0xf73cf3fcffffffff 0xfee79e7f9fffffff

def z77 : W := mkw 0x0000005280000000 0x0000000a50000000 0x000000ffc0000000 0x0000001ff8000000

def z78 : W := mkw 0x06ba8a5280000000 0x00d7514a50000000 0x48ffcfffc0000001 0x891ff9fff8000000

def z79 : W := mkw 0x06f800003a848000 0x00df000007509000 0xb7f800003fffe005 0xf6ff000007fffc00

def z80 : W := mkw 0x131830780c05ab45 0x8263060f0180b568 0x371830783c07efc0 0x66e3060f0780fdf8

def z81 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x1000000003f8f1fc 0x02000000007f1e3f

def z82 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0fd32c6300000000 0x21fa658c60000000

def z83 : W := mkw 0x004104a1220b1621 0x40082094244162c4 0xa8d32ce3201f1e07 0x351a659c6403e3c0

def z84 : W := mkw 0x0040040022000420 0x0008008004400084 0x40c00c0003000038 0x8818018000600007

def z85 : W := mkw 0x0045040523120428 0x4008a080a4624085 0x48c70c0703000038 0x8918e180e0600007

def z86 : W := mkw 0x131830580c04a944 0x8263060b01809528 0x170810181c00e1c0 0x42e1020303801c38

def z87 : W := mkw 0x04a28a0280000000 0x0094514050000000 0x48e7cf07c0000000 0x891cf9e0f8000000

def z88 : W := mkw 0x0effca02bbd6c000 0x01dff940577ad800 0xffffcf07ffffe005 0xfffff9e0fffffc00

def z89 : W := mkw 0x25a03b0014a00996 0x04b4076002940132 0xd7e03f001ce001c2 0xfafc07e0039c0038

def z90 : W := mkw 0x0004410c417060da 0x20008821882e0c1b 0x502cd31cc3e0e1f8 0xca059a63987c1c3f

def z91 : W := mkw 0x100441ac4d7dfbdf 0xa200883589afbf7b 0xf02cd39cffffffff 0xde059a739fffffff

def z92 : W := mkw 0x25e57fad77fb7fff 0x64bcaff5aeff6fff 0xffffffffffffffff 0xffffffffffffffff

def z93 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0x1028d318c0e0e1c0 0x42051a63181c1c38

def z94 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xc72cd39cc0000003 0xd8e59a7398000000

def z95 : W := mkw 0x004544ad635b7669 0x6008a895ac6b6ecd 0xe8dfecffe31ffe3f 0xbd1bfd9ffc63ffc7

def z96 : W := mkw 0x0effc08c7bdef048 0x21dff8118f7bde09 0xbfffc09cffffe005 0xf7fff8139ffffc00

def z97 : W := mkw 0x121800f8080db241 0x8243001f0101b648 0x901810f8001ff1c7 0x5203021f0003fe38

def z98 : W := mkw 0x0ebac00018c4c000 0x01d7580003189800 0xb738c0003cffe005 0x76e71800079ffc00

def z99 : W := mkw 0x204505a537bb1fbf 0x4408a0b4a6f763f7 0xf8d72ce73fff1fff 0xbf1ae59ce7ffe3ff

def z100 : W := mkw 0x031aba5280000000 0x0063574a50000000 0x481fffffc0000003 0x0903fffff8000000

def z101 : W := mkw 0x131830d80c0cb944 0x8263061b01819728 0x970810981c18f1c7 0x52e1021303831e38

def z102 : W := mkw 0x000400a401191209 0x0000801480232241 0xe01420e4231f1e3f 0xbc02841c8463e3c7

def z103 : W := mkw 0x01453ef7a31b1629 0x4028a7def46362c5 0xe8d73fffe31f1e3f 0xbd1ae7fffc63e3c7

def z104 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3fd300003fffe004 0x27fa600007fffc00

def z105 : W := mkw 0x25e47f8c77f87dfe 0x24bc8ff18eff0fbf 0xf7ecff9cfff8ffff 0xfefd9ff39fff1fff

def z106 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x1fefc0001fe0e000 0xc3fdf80003fc1c00

def z107 : W := mkw 0x004545ad637b76fb 0x6008a8b5ac6f6edf 0xf8ffffffe3ffffff 0xff1ffffffc7fffff

def z108 : W := mkw 0x07babaf280091201 0x00f7575e50012240 0xefffffffe01f1e07 0xfdfffffffc03e3c0

def z109 : W := mkw 0x0efb80003a868000 0x01df70000750d000 0x2fd300003c070000 0x25fa60000780e000

def z110 : W := mkw 0x021c40000954c000 0x00438800012a9800 0xb73cc0003fffe005 0xf6e7980007fffc00

def z111 : W := mkw 0x17bab0f80c0dbb45 0x82f7561f0181b768 0xbffff0f83c1fffc7 0xf7fffe1f0783fff8

def z112 : W := mkw 0x06ba800008048000 0x00d7500001009000 0xbfffc0003c1fe005 0xf7fff8000783fc00

def z113 : W := mkw 0x000441044170409a 0x20008820882e0813 0xd024d304c3e011fe 0xda049a60987c023f

def z114 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe0040084231f1e3f 0x9c0080108463e3c7

def z115 : W := mkw 0x17babafa880db241 0x82f7575f5101b648 0xcfffffffc01fe003 0xf9fffffff803fc00

def z116 : W := mkw 0x07fbbe73a2030621 0x40ff77ce744060c4 0xefffffffe0070e03 0xfdfffffffc00e1c0

def z117 : W := mkw 0x0045000023120000 0x0008a00004624000 0x20000000231f0004 0x040000000463e000

def z118 : W := mkw 0x04e0000032800000 0x009c000006500000 0xb7e000003fe00004 0xf6fc000007fc0000

def z119 : W := mkw 0x27fabf52b6a00db6 0x04ff57ea56d401b6 0xffffffffffe01fff 0xfffffffffffc03ff

def z120 : W := mkw 0x07baba5284000904 0x00f7574a50800120 0xfffffffffc001fc7 0xffffffffff8003f8

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0xc02cd39cc0000003 0xd8059a7398000000

def z122 : W := mkw 0x0effc1003bf6c092 0x01dff820077ed812 0xffffd3003ffff1ff 0xfffffa6007fffe3f

def z123 : W := mkw 0x0044048423181428 0x0008809084630285 0xe0c42c8423181e3f 0xbc188590846303c7

def z124 : W := mkw 0x25a03b0014a00996 0x04b4076002940132 0x172013001ce001c0 0x42e40260039c0038

def z125 : W := mkw 0x17b83af80c0dbb45 0x82f7075f0181b768 0xf7f83ff83c1fffc7 0xfeff07ff0783fff8

def z126 : W := mkw 0x1b1ff0f80d5ffb45 0x8363fe1f01abff68 0xbf1ff0f83c1fffc7 0x77e3fe1f0783fff8

def z127 : W := mkw 0x0000010000200092 0x0000002000040012 0xd020130003e011fe 0xda040260007c023f

def z128 : W := mkw 0x131830500c048904 0x8263060a01809120 0x070000001c000000 0x00e0000003800000

def z129 : W := mkw 0x0ffffa52bbd6c000 0x01ffff4a577ad800 0xbfffd318ffffe005 0xf7fffa631ffffc00

def z130 : W := mkw 0x121800f8080db241 0x8243001f0101b648 0x001800f8001fe001 0x0003001f0003fc00

def z131 : W := mkw 0x0effc1087bf6e0d2 0x21dff8210f7edc1a 0xbfffd318ffffe1c5 0xf7fffa631ffffc38

def z132 : W := mkw 0x110030f804093b45 0x8220061f00812768 0x900830f80018ffc7 0x5201061f00031ff8

def z133 : W := mkw 0x0000040000000420 0x0000008000000084 0x40002c0000001e3a 0x08000580000003c7

def z134 : W := mkw 0x110034fd04093f6d 0xc220069fa08127ed 0x40003cff00001ffa 0x0800079fe00003ff

def z135 : W := mkw 0x021f80f7811b1209 0x4043f01ef0236241 0x081fc0ffc01f0001 0x0103f81ff803e000

def z136 : W := mkw 0x0045000023120000 0x0008a00004624000 0xa8d70000231f0005 0xb51ae0000463e000

def z137 : W := mkw 0x000004a500091629 0x40000094a00122c5 0xc8d72ce700001e3b 0xb91ae59ce00003c7

def z138 : W := mkw 0x0318305000000000 0x0063060a00000000 0x871830f800000003 0x70e3061f00000000

def z139 : W := mkw 0x3ffffff83ffffff7 0x87ffffff07fffffe 0xfffffff83fffffff 0xffffffff07ffffff

def z140 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0x1000000000e0e1c0 0x02000000001c1c38

def z141 : W := mkw 0x131830700c058b05 0x8263060e0180b160 0xb71820603c1fee05 0x76e3040c0783fdc0

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x40002ce700000002 0x0800059ce0000000

def z143 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xffdf3cff3c1fffc7 0xfffbe79fe783fff8

def z144 : W := mkw 0x03183a5280000000 0x0063074a50000000 0xc7183fffc0000003 0x78e307fff8000000

def z145 : W := mkw 0x084100003a868000 0x010820000750d000 0x200000003c070000 0x040000000780e000

def z146 : W := mkw 0x0100310004200996 0x0020062000840132 0xf72033003fe01ffe 0xfee4066007fc03ff

def z147 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0728d318c0000000 0x40e51a6318000000

def z148 : W := mkw 0x2140350036a00db6 0x042806a006d401b6 0xb70030003fe01ffe 0x76e0060007fc03ff

def z149 : W := mkw 0x2044458c77f87dfe 0x240888b18eff0fbf 0xf02cd39cfff8ffff 0xde059a739fff1fff

def z150 : W := mkw 0x0ebfc0000956c000 0x01d7f800012ad800 0x8fffc000001fe001 0xf1fff8000003fc00

def z151 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x4024d39cc3e011fa 0x88049a73987c023f

def z152 : W := mkw 0x0004408401585008 0x00008810802b0a01 0xd02cc08403f8f03f 0xda059810807f1e07

def z153 : W := mkw 0x05a03a0000000000 0x00b4074000000000 0xc7e03f0000000002 0xf8fc07e000000000

def z154 : W := mkw 0x07bab05000000000 0x00f7560a00000000 0x8ffff0f800000003 0xf1fffe1f00000000

def z155 : W := mkw 0x004545ad637b76fb 0x6008a8b5ac6f6edf 0x3000000023fffffc 0x06000000047fffff

def z156 : W := mkw 0x06fa800032800000 0x00df500006500000 0xbfffc0003fe00005 0xf7fff80007fc0000

def z157 : W := mkw 0x24e28f02b2a004b2 0x049c51e056540096 0x48e7cf07c3e00038 0x891cf9e0f87c0007

def z158 : W := mkw 0x0004408c41587048 0x20008811882b0e09 0xc02cd39cc018e003 0xd8059a7398031c00

def z159 : W := mkw 0x004544a5235b5629 0x4008a894a46b6ac5 0xf8ffece723fffe3f 0xff1ffd9ce47fffc7

def z160 : W := mkw 0x0004400001504000 0x00008800002a0800 0x000cc0000018e001 0x0001980000031c00

def z161 : W := mkw 0x0ce7ca02b3d24000 0x019cf940567a4800 0x48e7cf07c3e00000 0x891cf9e0f87c0000

def z162 : W := mkw 0x0100305000000000 0x0020060a00000000 0x000030f800000002 0x0000061f00000000

def z163 : W := mkw 0x1100307004010b05 0x8220060e00802160 0x0000206000000e00 0x0000040c000001c0

def z164 : W := mkw 0x24e00f0036a00db6 0x049c01e006d401b6 0x70e00f003fe01ffc 0x8e1c01e007fc03ff

def z165 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe0c02c00231f1e3e 0xbc1805800463e3c7

def z166 : W := mkw 0x24e50f0533b204ba 0x449ca1e0a6764097 0x48e70f0703e00038 0x891ce1e0e07c0007

def z167 : W := mkw 0x25a47b8c55f879de 0x24b48f718abf0f3b 0xd72cd39cdff8f1ff 0xdae59a739bff1e3f

def z168 : W := mkw 0x2040050036a00db6 0x040800a006d401b6 0x300000003fe01ffc 0x0600000007fc03ff

def z169 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x48c72ce703001e3a 0x8918e59ce06003c7

def z170 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xfff73fe73fe01fff 0xfffee7fce7fc03ff

def z171 : W := mkw 0x07babef780091629 0x40f757def00122c5 0xcfffffffc0001e3b 0xf9fffffff80003c7

def z172 : W := mkw 0x0effc0a03bdfd201 0x01dff814077bfa40 0xbfffe0e03ffffe07 0xf7fffc1c07ffffc0

def z173 : W := mkw 0x37fc7ffc7ffdffff 0xa6ff8fff8fffbfff 0xf7fcfffcffffffff 0xfeff9fff9fffffff

def z174 : W := mkw 0x0318305000000000 0x0063060a00000000 0x0708101800000000 0x40e1020300000000

def z175 : W := mkw 0x2de57f003ff6cdb6 0x05bcafe007fed9b6 0xf7e03f003ffffffe 0xfefc07e007ffffff

def z176 : W := mkw 0x025f84f7a31b1629 0x404bf09ef46362c5 0xe8dfecffe31f1e3f 0xbd1bfd9ffc63e3c7

def z177 : W := mkw 0x0ffff0003fd6c904 0x01fffe0007fad920 0xbffff0003fffffc7 0xf7fffe0007fffff8

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8ffffffc0000003 0xf91ffffff8000000

def z179 : W := mkw 0x06ba800000000000 0x00d7500000000000 0xcfffece700000003 0xf9fffd9ce0000000

def z180 : W := mkw 0x0ebac00018c4c000 0x01d7580003189800 0x1728c0001ce0e000 0x42e51800039c1c00

def z181 : W := mkw 0x0ebfc00019d6c000 0x01d7f800033ad800 0x1f3fc0001cffe001 0x43e7f800039ffc00

def z182 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x271820f83c1fee01 0x24e3041f0783fdc0

def z183 : W := mkw 0x07baba0000000000 0x00f7574000000000 0xcfffff0000000003 0xf9ffffe000000000

def z184 : W := mkw 0x0000008800083040 0x0000001100010608 0x900810980018f1c7 0x5201021300031e38

def z185 : W := mkw 0x0a5d40003bd6c000 0x014ba800077ad800 0xb71800003fffe005 0x76e3000007fffc00

def z186 : W := mkw 0x05e0300036800904 0x00bc060006d00120 0xb7e030003fe01fc6 0xf6fc060007fc03f8

def z187 : W := mkw 0x2000010014a00996 0x0400002002940132 0x100000001ce001c0 0x02000000039c0038

def z188 : W := mkw 0x01003a0000000000 0x0020074000000000 0x40003f0000000002 0x080007e000000000

def z189 : W := mkw 0x000441044170409a 0x20008820882e0813 0x0000000003e00038 0x00000000007c0007

def z190 : W := mkw 0x2ffbbf003ea68db6 0x05ff77e007d4d1b6 0xfff33f003fe71ffe 0xfffe67e007fce3ff

def z191 : W := mkw 0x01003a5280000000 0x0020074a50000000 0x40003fffc0000002 0x080007fff8000000

def z192 : W := mkw 0x0effc18c7bfef0da 0x21dff8318f7fde1b 0xffffd39cfffff1ff 0xfffffa739ffffe3f

def z193 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x20000000231f1e3c 0x040000000463e3c7

def z194 : W := mkw 0x00044108417060d2 0x20008821082e0c1a 0x902cd318c3f8e1c5 0xd2059a63187f1c38

def z195 : W := mkw 0x121c40fc495df249 0xa243881f892bbe49 0x001cc0fcc01fe001 0x0003981f9803fc00

def z196 : W := mkw 0x00450485231a1428 0x4008a090a4634285 0xc8c70c870318103f 0x9918e190e0630207

def z197 : W := mkw 0x07fabe52a2000420 0x00ff57ca54400084 0xefffffffe3001e3f 0xfdfffffffc6003c7

def z198 : W := mkw 0x0218005000000000 0x0043000a00000000 0x001800f800000001 0x0003001f00000000

def z199 : W := mkw 0x014534a5271b1f2d 0x4028a694a4e363e5 0xffd73ce73f1f1fff 0xfffae79ce7e3e3ff

def z200 : W := mkw 0x25e03b0036a00996 0x04bc076006d40132 0xb7e013003fe001c4 0xf6fc026007fc0038

def z201 : W := mkw 0x0000000004000904 0x0000000000800120 0x300000003c001fc4 0x06000000078003f8

def z202 : W := mkw 0x131830700c058b05 0x8263060e0180b160 0x271020603c070e00 0x24e2040c0780e1c0

def z203 : W := mkw 0x0000040500000428 0x40000080a0000085 0x40000c0700000038 0x08000180e0000007

def z204 : W := mkw 0x000541ad417b72db 0x6000a835a82f6e5b 0xd83fd3ffc3fff1ff 0xdb07fa7ff87ffe3f

def z205 : W := mkw 0x0000008000081000 0x0000001000010200 0x8000008000181007 0x1000001000030200

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0x9020000003e00004 0xd2040000007c0000

def z207 : W := mkw 0x07befb56c170409a 0x20f7df6ad82e0813 0xcfffffffc3e0003b 0xf9fffffff87c0007

def z208 : W := mkw 0x06ba800000000000 0x00d7500000000000 0x8fffc00000000001 0xf1fff80000000000

def z209 : W := mkw 0x06ff800023120000 0x00dff00004624000 0xafffc000231f0005 0xf5fff8000463e000

def z210 : W := mkw 0x1ffff4fd3fdfff6d 0xc3fffe9fa7fbffed 0xfffffcff3fffffff 0xffffff9fe7ffffff

def z211 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x08ffc00003ffe001 0x811ff800007ffc00

def z212 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4ff7ef67c0000000 0xa9fefdecf8000000

def z213 : W := mkw 0x000004a500091629 0x40000094a00122c5 0x40002ce700001e3a 0x0800059ce00003c7

def z214 : W := mkw 0x0041042122030621 0x40082084244060c4 0x28d32c6320070e00 0x251a658c6400e1c0

def z215 : W := mkw 0x07ffbef7a31b1629 0x40fff7def46362c5 0xefffffffe31f1e3f 0xfdfffffffc63e3c7

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0x88d7000000000001 0xb11ae00000000000

def z217 : W := mkw 0x031830f000091201 0x0063061e00012240 0xa71830f8201f1e07 0x74e3061f0403e3c0

def z218 : W := mkw 0x27f83f003ea48db6 0x04ff07e007d491b6 0xf7f83f003fffffff 0xfeff07e007ffffff

def z219 : W := mkw 0x0efb80003a868000 0x01df70000750d000 0xbff300003fe70004 0xf7fe600007fce000

def z220 : W := mkw 0x21403f0026200db6 0x042807e004c401b6 0xe0c03f0023001ffe 0xbc1807e0046003ff

def z221 : W := mkw 0x0004008401181008 0x0000801080230201 0xc00400840318103f 0x9800801080630207

def z222 : W := mkw 0x05a2ba0280000000 0x00b4574050000000 0xcfe7ff07c0000002 0xf9fcffe0f8000000

def z223 : W := mkw 0x04e4400033d04000 0x009c8800067a0800 0xb7ecc0003ff8e005 0xf6fd980007ff1c00

def z224 : W := mkw 0x100000f800093241 0x8200001f00012648 0x000000f800000000 0x0000001f00000000

def z225 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8ffffffe31f1e3f 0xfd1ffffffc63e3c7

def z226 : W := mkw 0x1100305804002944 0x8220060b00800528 0x00001018000001c0 0x0000020300000038

def z227 : W := mkw 0x0004008c01183048 0x0000801180230609 0xd00c109c0318f1ff 0xda01821380631e3f

def z228 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x28d72ce7201f0e01 0x251ae59ce403e1c0

def z229 : W := mkw 0x000500a5011b1209 0x4000a014a0236241 0xc81700e7031f103f 0x9902e01ce063e207

def z230 : W := mkw 0x04a0000010800000 0x0094000002100000 0x172000001ce00000 0x42e40000039c0000

def z231 : W := mkw 0x131830f8080db241 0x8263061f0101b648 0x871830f8001fe003 0x70e3061f0003fc00

def z232 : W := mkw 0x06ba805280000000 0x00d7500a50000000 0x8fffc0ffc0000001 0xf1fff81ff8000000

def z233 : W := mkw 0x0004008401181008 0x0000801080230201 0x0004008400180001 0x0000801080030000

def z234 : W := mkw 0x004004a022091621 0x00080094044122c4 0xe0d02ce0231f1e3f 0xbc1a059c0463e3c7

def z235 : W := mkw 0x000441ac417972db 0x20008835882f2e5b 0xf03cf3fce3ffffff 0xfe079e7f9c7fffff

def z236 : W := mkw 0x0045040523120428 0x4008a080a4624085 0xc8d72ce70300003b 0xb91ae59ce0600007

def z237 : W := mkw 0x131830f00c0d9b05 0x8263061e0181b360 0xa71020e03c1f1e07 0x34e2041c0783e3c0

def z238 : W := mkw 0x07ffbef7a31b1629 0x40fff7def46362c5 0xefd72ce7231f1e3f 0xbdfae59ce463e3c7

def z239 : W := mkw 0x000441044170409a 0x20008820882e0813 0x4024c304c3e00038 0x88049860987c0007

def z240 : W := mkw 0x25a03f0004200db6 0x04b407e0008401b6 0xc7e03f0000001ffa 0xf8fc07e0000003ff

def z241 : W := mkw 0x17baba728c058b05 0x82f7574e5180b160 0x2fd32c633c070e00 0x25fa658c6780e1c0

def z242 : W := mkw 0x0040040022000420 0x0008008004400084 0xe8d72ce723001e3f 0xbd1ae59ce46003c7

def z243 : W := mkw 0x07baba5288048000 0x00f7574a51009000 0xfffffffffc1fe007 0xffffffffff83fc00

def z244 : W := mkw 0x04e0000032800000 0x009c000006500000 0x27c000003c000000 0x24f8000007800000

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x90001000000011c6 0x5200020000000238

def z246 : W := mkw 0x04a28a0280000000 0x0094514050000000 0xc8f7efe7c0000003 0xb91efdfcf8000000

def z247 : W := mkw 0x17babafa8c0dbb45 0x82f7575f5181b768 0xfffffffffc1fffc7 0xffffffffff83fff8

def z248 : W := mkw 0x021a805280000000 0x0043500a50000000 0x081fc0ffc0000001 0x0103f81ff8000000

def z249 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd020130003f8f1fe 0xda040260007f1e3f

def z250 : W := mkw 0x0effc052bbd6c000 0x01dff80a577ad800 0xbfffc0ffffffe005 0xf7fff81ffffffc00

def z251 : W := mkw 0x125d04fd2b1fb669 0xc24ba09fa563f6cd 0xe8df2cff231ffe3f 0xbd1be59fe463ffc7

def z252 : W := mkw 0x33183ff80c2dbff7 0x866307ff0185b7fe 0xf7183ff83c1fffff 0x7ee307ff0783ffff

def z253 : W := mkw 0x0effc18c7bfef0da 0x21dff8318f7fde1b 0xbfffc0003ffff1fd 0xf7fff80007fffe3f

def z254 : W := mkw 0x000500a5011b1209 0x4000a014a0236241 0x00000000001f0000 0x000000000003e000

def z255 : W := mkw 0x04e0040032800420 0x009c008006500084 0xf7e02c003fe01e3e 0xfefc058007fc03c7

def z256 : W := mkw 0x1ffffafabfdffb45 0x83ffff5f57fbff68 0xffffffffffffffc7 0xfffffffffffffff8

def z257 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x37e03f003ce00fc0 0x66fc07e0079c01f8

def z258 : W := mkw 0x1ffbb0f83e8fbb45 0x83ff761f07d1f768 0xbfdb30f83c1fffc7 0x77fb661f0783fff8

def z259 : W := mkw 0x2044458c77f87dfe 0x240888b18eff0fbf 0x300000003ff8fffc 0x0600000007ff1fff

def z260 : W := mkw 0x06ba8a0280000000 0x00d7514050000000 0xcfffcf07c0000001 0xf9fff9e0f8000000

def z261 : W := mkw 0x0218000008048000 0x0043000001009000 0x170800001c00e000 0x42e1000003801c00

def z262 : W := mkw 0x121800a80c0dbb45 0x824300150181b768 0xb71800003c1fffc5 0x76e300000783fff8

def z263 : W := mkw 0x110030f804093b45 0x8220061f00812768 0xb70030f83c001fc6 0x76e0061f078003f8

def z264 : W := mkw 0x07befadec1587048 0x20f7df5bd82b0e09 0xcfffffffc018e003 0xf9fffffff8031c00

def z265 : W := mkw 0x0005000501120008 0x4000a000a0224001 0x0807000700000000 0x0100e000e0000000

def z266 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x5024c304c3f8f1fc 0x8a049860987f1e3f

def z267 : W := mkw 0x04a2800000000000 0x0094500000000000 0x08e7c00000000000 0x811cf80000000000

def z268 : W := mkw 0x0000008800083040 0x0000001100010608 0x00001098000011c2 0x0000021300000238

def z269 : W := mkw 0x37f83f583ea4adf6 0x86ff07eb07d495be 0xf7e83f183fe0fffe 0xfefd07e307fc1fff

def z270 : W := mkw 0x0045000023120000 0x0008a00004624000 0xe8d72ce7231f0007 0xbd1ae59ce463e000

def z271 : W := mkw 0x335835f83eadbff7 0x866b06bf07d5b7fe 0xb71830f83fffffff 0x76e3061f07ffffff

def z272 : W := mkw 0x110031fc44293bdf 0xa220063f8885277b 0x400033fcc0001ffa 0x0800067f980003ff

def z273 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x5000139cc3f8f1fe 0x0a000273987f1e3f

def z274 : W := mkw 0x25e03e0036800d24 0x04bc07c006d001a4 0xb7c03c003c001fc6 0x76f80780078003f8

def z275 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x902cc00003f8f1fd 0xd2059800007f1e3f

def z276 : W := mkw 0x0ce7c00033d24000 0x019cf800067a4800 0xbfe7c0003fe00004 0xf7fcf80007fc0000

def z277 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0xd02cd39cc0e0e1c3 0xda059a73981c1c38

def z278 : W := mkw 0x21003f0004200db6 0x042007e0008401b6 0xf7003f003c001ffe 0x7ee007e0078003ff

def z279 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0ffbff7bc0000000 0x61ff7fef78000000

def z280 : W := mkw 0x37fd3ffd3fbfbfff 0xc6ffa7ffa7f7f7ff 0xffff3fff3fffffff 0xffffe7ffe7ffffff

def z281 : W := mkw 0x0efac0003ac4c000 0x01df580007589800 0xb7e8c0003fe0e004 0xf6fd180007fc1c00

def z282 : W := mkw 0x2ffffe003fd6cd24 0x05ffffc007fad9a4 0xbfffec003fffee05 0xf7fffd8007fffdc0

def z283 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x9008109803f8f1ff 0x52010213007f1e3f

def z284 : W := mkw 0x07ffffffe37b76fb 0x60fffffffc6f6edf 0xffffffffe3ffffff 0xfffffffffc7fffff

def z285 : W := mkw 0x0041000022020000 0x0008200004404000 0x28d3000020070000 0x251a60000400e000

def z286 : W := mkw 0x0effc0a53bdfd209 0x41dff814a77bfa41 0xbfffc0e73fffe005 0xf7fff81ce7fffc00

def z287 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xa8d70000231f1e3d 0xb51ae0000463e3c7

def z288 : W := mkw 0x0040000032800000 0x0008000006500000 0x300000003fe00004 0x0600000007fc0000

def z289 : W := mkw 0x04a6cb8ec17870da 0x2094d971d82f0e1b 0xd8efdf9fc3f8f1ff 0xdb1dfbf3f87f1e3f

def z290 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x37c02c003fe01ffc 0x26f8058007fc03ff

def z291 : W := mkw 0x080540000956c000 0x0100a800012ad800 0x00000000001fe000 0x000000000003fc00

def z292 : W := mkw 0x0044458c637874fa 0x200888b18c6f0e9f 0xf0ecff9ce3f8ffff 0xfe1d9ff39c7f1fff

def z293 : W := mkw 0x021800a0080d9201 0x004300140101b240 0xb71820e03c1ffe07 0x76e3041c0783ffc0

def z294 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87e0000000000000 0xf0fc000000000000

def z295 : W := mkw 0x0ffbba52ba868000 0x01ff774a5750d000 0x2fd32c633c070000 0x25fa658c6780e000

def z296 : W := mkw 0x0fbafa5298c4c000 0x01f75f4a53189800 0x1728d318dce0e000 0x42e51a631b9c1c00

def z297 : W := mkw 0x121a80fa880db241 0x8243501f5101b648 0x081fc0ffc01fe001 0x0103f81ff803fc00

def z298 : W := mkw 0x27babb5294a00996 0x04f7576a52940132 0xdfffffffdce001c3 0xfbfffffffb9c0038

def z299 : W := mkw 0x05a03a0000000000 0x00b4074000000000 0xc7ecff9cc0000003 0xf8fd9ff398000000

def z300 : W := mkw 0x084540003bd6c000 0x0108a800077ad800 0xb8d700003fffe005 0xb71ae00007fffc00

def z301 : W := mkw 0x1fbaf0f81ccdfb45 0x83f75e1f0399bf68 0xb738f0f83cffffc7 0x76e71e1f079ffff8

def z302 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x100cc09cc3f8f1fd 0x02019813987f1e3f

def z303 : W := mkw 0x184540a83fdffb45 0x8308a81507fbff68 0x300000003fffffc4 0x0600000007fffff8

def z304 : W := mkw 0x0000010000200092 0x0000002000040012 0x1020130000e001c0 0x42040260001c0038

def z305 : W := mkw 0x2040040036800d24 0x0408008006d001a4 0x200000003c000e00 0x04000000078001c0

def z306 : W := mkw 0x25e47f0037f04db6 0x04bc8fe006fe09b6 0xf7ecff003ff8ffff 0xfefd9fe007ff1fff

def z307 : W := mkw 0x0845418c7bfef0da 0x2108a8318f7fde1b 0x300000003ffff1fc 0x0600000007fffe3f

def z308 : W := mkw 0x25a03b0014a00996 0x04b4076002940132 0xb72033003ce01fc6 0x76e40660079c03f8

def z309 : W := mkw 0x25e47f0477f04dbe 0x24bc8fe08efe09b7 0xf7e4ff04ffe01ffe 0xfefc9fe09ffc03ff

def z310 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x57e01f001fe001f8 0xcafc03e003fc003f

def z311 : W := mkw 0x01047bdec17870da 0x20208f7bd82f0e1b 0xd02cffffc3f8f1ff 0xda059ffff87f1e3f

def z312 : W := mkw 0x0effc4a53bdfd629 0x41dff894a77bfac5 0xbfffc0003ffffe3d 0xf7fff80007ffffc7

def z313 : W := mkw 0x0ebac00018c4c000 0x01d7580003189800 0x9fffc0001ce0e001 0xf3fff800039c1c00

def z314 : W := mkw 0x07bafb5ac06060d2 0x20f75f6b580c0c1a 0xdfffffffc0e0e1c3 0xfbfffffff81c1c38

def z315 : W := mkw 0x17ffbeffaf1fbf6d 0xc2fff7dff5e3f7ed 0xffffffffff1fffff 0xffffffffffe3ffff

def z316 : W := mkw 0x100000080c04a944 0x8200000101809528 0x100000001c00e1c0 0x0200000003801c38

def z317 : W := mkw 0x0045418c637a70da 0x2008a8318c6f4e1b 0xf8ffd39ce3fff1ff 0xff1ffa739c7ffe3f

def z318 : W := mkw 0x25e2bf02b6a00db6 0x04bc57e056d401b6 0xffe7ff07ffe01ffe 0xfffcffe0fffc03ff

def z319 : W := mkw 0x000441044170409a 0x20008820882e0813 0xc02cd39cc3e0003b 0xd8059a73987c0007

def z320 : W := mkw 0x0000008c40083048 0x2000001188010609 0x0000009cc0000000 0x0000001398000000

def z321 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xcff33f6300000002 0xf9fe67ec60000000

def z322 : W := mkw 0x0a1fc0000956c000 0x0143f800012ad800 0xbf1fc0003c1fe005 0x77e3f8000783fc00

def z323 : W := mkw 0x25a03a0014800904 0x04b4074002900120 0x070000001c000000 0x00e0000003800000

def z324 : W := mkw 0x0eff84a53b9f9629 0x41dff094a773f2c5 0xefd72ce73f1f1e3f 0xbdfae59ce7e3e3c7

def z325 : W := mkw 0x05a47b8c417870da 0x20b48f71882f0e1b 0xd7ecff9cc3f8f1ff 0xfafd9ff3987f1e3f

def z326 : W := mkw 0x110030f804093b45 0x8220061f00812768 0xa01030f8201f1fc7 0x3402061f0403e3f8

def z327 : W := mkw 0x0000042100010621 0x40000084200020c4 0x00002c6300000e00 0x0000058c600001c0

def z328 : W := mkw 0x0000018c402830da 0x200000318805061b 0x4000139cc00011fa 0x080002739800023f

def z329 : W := mkw 0x0ce7c10473f2409a 0x219cf8208e7e4813 0x48e7c304c3e00038 0x891cf860987c0007

def z330 : W := mkw 0x000000a000091201 0x0000001400012240 0x20000000201f1e04 0x040000000403e3c0

def z331 : W := mkw 0x2040050036a00db6 0x040800a006d401b6 0xf0c02c003fe01ffe 0xbe18058007fc03ff

def z332 : W := mkw 0x0040000022000000 0x0008000004400000 0xa0c0000023000004 0xb418000004600000

def z333 : W := mkw 0x27fabf0036a00db6 0x04ff57e006d401b6 0xffffff003fe01fff 0xffffffe007fc03ff

def z334 : W := mkw 0x110030a80c0dbb45 0x822006150181b768 0xb70030003c1fffc6 0x76e006000783fff8

def z335 : W := mkw 0x0318305000000000 0x0063060a00000000 0xcfdf3cff00000003 0xf9fbe79fe0000000

def z336 : W := mkw 0x2fffff52bff6cdb6 0x05ffffea57fed9b6 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x021ec1dec17870da 0x2043d83bd82f0e1b 0xd83fd3ffc3f8f1ff 0xdb07fa7ff87f1e3f

def z338 : W := mkw 0x131ab0fa8c0dbb45 0x8263561f5181b768 0xbf1ff0fffc1fffc7 0x77e3fe1fff83fff8

def z339 : W := mkw 0x07bfbaf7811b1209 0x40f7f75ef0236241 0xcfffffffc01f0003 0xf9fffffff803e000

def z340 : W := mkw 0x0218000008048000 0x0043000001009000 0x00180000001fe001 0x000300000003fc00

def z341 : W := mkw 0x2ffffb003ff6c996 0x05ffff6007fed932 0xbfffd3003fffe1c5 0xf7fffa6007fffc38

def z342 : W := mkw 0x0ce7c4a533db5629 0x419cf894a67b6ac5 0xe8f7ece723ff1e3f 0xbd1efd9ce47fe3c7

def z343 : W := mkw 0x0100300004000904 0x0020060000800120 0x270020003c000e00 0x24e00400078001c0

def z344 : W := mkw 0x21003fa504291fbf 0x442007f4a08523f7 0x40003fe700001ffa 0x080007fce00003ff

def z345 : W := mkw 0x24e44f0473f044ba 0x249c89e08e7e0897 0x40e4cf04c3e00038 0x881c99e0987c0007

def z346 : W := mkw 0x131c71dc4d7cf9de 0xa2638e3b89af9f3b 0xd72cd39cdff8f1ff 0xdae59a739bff1e3f

def z347 : W := mkw 0x06bec18c417870da 0x20d7d831882f0e1b 0xdfffd39cc3f8f1ff 0xfbfffa73987f1e3f

def z348 : W := mkw 0x07fbbe73a2030621 0x40ff77ce744060c4 0x2fd32c6320070e00 0x25fa658c6400e1c0

def z349 : W := mkw 0x37b83bf81cadbbd7 0x86f7077f0395b77a 0xb73833f83cffffc7 0x76e7067f079ffff8

def z350 : W := mkw 0x0004000001100000 0x0000800000220000 0x8004000003180005 0x9000800000630000

def z351 : W := mkw 0x0000418c406870da 0x20000831880d0e1b 0x5028d39cc0e0f1fa 0x4a051a73981c1e3f

def z352 : W := mkw 0x27fabe52b6800d24 0x04ff57ca56d001a4 0x2fd32c633c000e00 0x25fa658c678001c0

def z353 : W := mkw 0x000504a5011b1629 0x4000a094a02362c5 0x48172ce7001f1e3b 0x0902e59ce003e3c7

def z354 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x1028d318c3f8f1fc 0x42051a63187f1e3f

def z355 : W := mkw 0x2040050036a00db6 0x040800a006d401b6 0xf02013003fe01ffe 0xde04026007fc03ff

def z356 : W := mkw 0x13183afa8c0dbb45 0x8263075f5181b768 0xf7183ffffc1fffc7 0x7ee307ffff83fff8

def z357 : W := mkw 0x27f83f5036a00db6 0x04ff07ea06d401b6 0xf7f83ff83fe01fff 0xfeff07ff07fc03ff

def z358 : W := mkw 0x05a2ba5280000000 0x00b4574a50000000 0x48e7ffffc0000002 0x891cfffff8000000

def z359 : W := mkw 0x0000018c402830da 0x200000318805061b 0xd008139cc018f1ff 0x5a01027398031e3f

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z361 : W := mkw 0x0004400001504000 0x00008800002a0800 0x902cc00003f8e005 0xd2059800007f1c00

def z362 : W := mkw 0x25e03fa036a91fb7 0x04bc07f406d523f6 0xf7f03fe03fff1fff 0xfefe07fc07ffe3ff

def z363 : W := mkw 0x121c41fc497df2db 0xa243883f892fbe5b 0xd03cd3fcc3fff1ff 0xda079a7f987ffe3f

def z364 : W := mkw 0x0045040523120428 0x4008a080a4624085 0xe8c72c0723001e3e 0xbd18e580e46003c7

def z365 : W := mkw 0x021ec0dec1587048 0x2043d81bd82b0e09 0x081fc0ffc018e001 0x0103f81ff8031c00

def z366 : W := mkw 0x135d30f82f1fbb45 0x826ba61f05e3f768 0xbfdf30f83f1fffc7 0xf7fbe61f07e3fff8

def z367 : W := mkw 0x0045000023120000 0x0008a00004624000 0x08c7000003000000 0x8118e00000600000

def z368 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x40e03f0003e01ffa 0x881c07e0007c03ff

def z369 : W := mkw 0x07ffba52a3120000 0x00fff74a54624000 0xefffffffe31f0007 0xfdfffffffc63e000

def z370 : W := mkw 0x0effc4053bd6c428 0x41dff880a77ad885 0xffffcc073fffe03d 0xfffff980e7fffc07

def z371 : W := mkw 0x0ce7c00033d24000 0x019cf800067a4800 0xa8f7c00023ff0005 0xb51ef800047fe000

def z372 : W := mkw 0x05e53ea5231b1629 0x40bca7d4a46362c5 0xeff73fe7231f1e3f 0xfdfee7fce463e3c7

def z373 : W := mkw 0x24e00f0032a004b2 0x049c01e006540096 0xf7e00f003fe0003c 0xfefc01e007fc0007

def z374 : W := mkw 0x0a5fc4a52b5fd629 0x414bf894a56bfac5 0xe8dfece7231ffe3f 0xbd1bfd9ce463ffc7

def z375 : W := mkw 0x031c71dc417870da 0x20638e3b882f0e1b 0xd73cf3fcc3f8f1ff 0xfae79e7f987f1e3f

def z376 : W := mkw 0x0efbc0003ac6c000 0x01df78000758d800 0x3ffbc0003ce7e000 0x67ff7800079cfc00

def z377 : W := mkw 0x25a03b0014a00996 0x04b4076002940132 0xd72013001fe011fe 0xdae4026003fc023f

def z378 : W := mkw 0x004104a5220b1629 0x40082094a44162c5 0x68d32ce720071e3a 0x2d1a659ce400e3c7

def z379 : W := mkw 0x27fabf52b6a00db6 0x04ff57ea56d401b6 0xfff33f633fe01ffe 0xfffe67ec67fc03ff

def z380 : W := mkw 0x25e03f0032a004b2 0x04bc07e006540096 0xc7e03f0003e0003a 0xf8fc07e0007c0007

def z381 : W := mkw 0x05e03a0032800000 0x00bc074006500000 0xf7e03f003fe00006 0xfefc07e007fc0000

def z382 : W := mkw 0x0a5fc0003bd6c000 0x014bf800077ad800 0x381fc0003fffe005 0x0703f80007fffc00

def z383 : W := mkw 0x0004410001704092 0x00008820002e0812 0xd02cd30003f8f1ff 0xda059a60007f1e3f

def z384 : W := mkw 0x284545003ff6cdb6 0x0508a8a007fed9b6 0x300000003ffffffc 0x0600000007ffffff

def z385 : W := mkw 0x21047f8c45787dfe 0x24208ff188af0fbf 0xd02cff9cc3f8ffff 0xda059ff3987f1fff

def z386 : W := mkw 0x0000008800083040 0x0000001100010608 0x100000000018f1c4 0x0200000000031e38

def z387 : W := mkw 0x000004a500091629 0x40000094a00122c5 0xe0102ce7201f1e3f 0x3c02059ce403e3c7

def z388 : W := mkw 0x2ce7cf0033f244b2 0x059cf9e0067e4896 0x48e7cf0003e00038 0x891cf9e0007c0007

def z389 : W := mkw 0x110471fc45797bdf 0xa2208e3f88af2f7b 0xd02cf3fcc3f8ffff 0xda059e7f987f1fff

def z390 : W := mkw 0x135934f92e0fbf65 0xc26b269f25c1f7ec 0xbfdb3cfb3c1fffc7 0x77fb679f6783fff8

def z391 : W := mkw 0x004545ad637b76fb 0x6008a8b5ac6f6edf 0xf8d72ce723ffffff 0xbf1ae59ce47fffff

def z392 : W := mkw 0x0041042122030621 0x40082084244060c4 0xe8d32c6323071e3e 0xbd1a658c6460e3c7

def z393 : W := mkw 0x0004408c41587048 0x20008811882b0e09 0xc00cc09cc318f03f 0x9801981398631e07

def z394 : W := mkw 0x0a5fc0002b56c000 0x014bf800056ad800 0xa8dfc000231fe005 0xb51bf8000463fc00

def z395 : W := mkw 0x17baba5a8c04a944 0x82f7574b51809528 0x1728d318dc00e1c0 0x42e51a631b801c38

def z396 : W := mkw 0x000500a5011b1209 0x4000a014a0236241 0xc8d72ce7001f0003 0xb91ae59ce003e000

def z397 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffd39cffffe007 0xfffffa739ffffc00

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0xc020130000000002 0xd804026000000000

def z399 : W := mkw 0x25a07b0854e069d6 0x24b40f610a9c0d3a 0x1728d318dce0e1c0 0x42e51a631b9c1c38

def z400 : W := mkw 0x0a1fc0528956c000 0x0143f80a512ad800 0x081fc0ffc01fe001 0x0103f81ff803fc00

def z401 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd8ffffffc3f8f1ff 0xfb1ffffff87f1e3f

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000200020001e06 0x34000400040003c0

def z403 : W := mkw 0x121800f8080db241 0x8243001f0101b648 0xb71800f83c1fe005 0x76e3001f0783fc00

def z404 : W := mkw 0x100000a80c0dbb45 0x820000150181b768 0xb00810983c1fffc7 0x560102130783fff8

def z405 : W := mkw 0x131830580c04a944 0x8263060b01809528 0xb71810183c1fe1c5 0x76e302030783fc38

def z406 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0xd028d318c3e0f1fe 0xda051a63187c1e3f

def z407 : W := mkw 0x0a1fc0000956c000 0x0143f800012ad800 0x081fc000001fe001 0x0103f8000003fc00

def z408 : W := mkw 0x07bebad681181008 0x00f7d75ad0230201 0xcfffffffc318103f 0xf9fffffff8630207

def z409 : W := mkw 0x21403f0036a00db6 0x042807e006d401b6 0x70003f003fe01ffe 0x0e0007e007fc03ff

def z410 : W := mkw 0x04e0010032a00092 0x009c002006540012 0xf7e013003fe011fe 0xfefc026007fc023f

def z411 : W := mkw 0x01003a5280000000 0x0020074a50000000 0xc8d73fffc0000003 0xb91ae7fff8000000

def z412 : W := mkw 0x0000000008048000 0x0000000001009000 0x300000003c1fe004 0x060000000783fc00

def z413 : W := mkw 0x0045042523130629 0x4008a084a46260c5 0x68d72c6723070e38 0xad1ae58ce460e1c7

def z414 : W := mkw 0x07ffbe57a3120428 0x40fff7caf4624085 0xcfffffffc300003b 0xf9fffffff8600007

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x4024c304c0000000 0x8804986098000000

def z416 : W := mkw 0x25e53f0037b20db6 0x04bca7e006f641b6 0xfff73f003fff1fff 0xfffee7e007ffe3ff

def z417 : W := mkw 0x24e00f0032a004b2 0x049c01e006540096 0xe0e02f0023e01e3e 0xbc1c05e0047c03c7

def z418 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xa01020e0231f1e3f 0x3402041c0463e3c7

def z419 : W := mkw 0x07b83a5000000000 0x00f7074a00000000 0xc7f83ff800000003 0xf8ff07ff00000000

def z420 : W := mkw 0x131c70f80d5dfb45 0x82638e1f01abbf68 0xb73cf0f83fffffc7 0xf6e79e1f07fffff8

def z421 : W := mkw 0x35e03ff836a93ff7 0x86bc07ff06d527fe 0xf7e03ff83fe01ffe 0xfefc07ff07fc03ff

def z422 : W := mkw 0x100000200c058b05 0x820000040180b160 0x200000003c070e00 0x040000000780e1c0

def z423 : W := mkw 0x0effc0883bdef040 0x01dff811077bde08 0xbfffd0983ffff1c7 0xf7fffa1307fffe38

def z424 : W := mkw 0x0045458d637a74fa 0x6008a8b1ac6f4e9f 0xd8efdf9fc3f8f1ff 0xdb1dfbf3f87f1e3f

def z425 : W := mkw 0x06ff84a5231b1629 0x40dff094a46362c5 0xefffece7231f1e3f 0xfdfffd9ce463e3c7

def z426 : W := mkw 0x021c418c497cf0da 0x20438831892f9e1b 0xf73cd39cfffff1ff 0xfee79a739ffffe3f

def z427 : W := mkw 0x031830d800083040 0x0063061b00010608 0x971830f80018f1c7 0x72e3061f00031e38

def z428 : W := mkw 0x17babafa8c0dbb45 0x82f7575f5181b768 0xb738f3f8fc1fffc7 0x76e71e7f1f83fff8

def z429 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x171810f81c1fe1c1 0x42e3021f0383fc38

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000139cc0000002 0x0800027398000000

def z431 : W := mkw 0x100000a80c0dbb45 0x820000150181b768 0xb01020e03c1fffc7 0x3602041c0783fff8

def z432 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x8fffd318c0000001 0xf1fffa6318000000

def z433 : W := mkw 0x25a03f0014a00db6 0x04b407e0029401b6 0x57203f001ce01ffa 0x4ae407e0039c03ff

def z434 : W := mkw 0x25e53f0537b20dbe 0x44bca7e0a6f641b7 0xffe73f073fe01ffe 0xfffce7e0e7fc03ff

def z435 : W := mkw 0x0ffff0503bd6c000 0x01fffe0a077ad800 0xbffff0f83fffe007 0xf7fffe1f07fffc00

def z436 : W := mkw 0x11003afa84093b45 0x8220075f50812768 0x40003fffc0001fc2 0x080007fff80003f8

def z437 : W := mkw 0x0318305004000904 0x0063060a00800120 0xb71830f83c001fc7 0x76e3061f078003f8

def z438 : W := mkw 0x01003a5280000000 0x0020074a50000000 0x00001318c0000000 0x0000026318000000

def z439 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4fefdf1fc0000000 0xc9fdfbe3f8000000

def z440 : W := mkw 0x0efb84213a878621 0x41df70842750f0c4 0x2fd32c633c070e00 0x25fa658c6780e1c0

def z441 : W := mkw 0x084544a53bdfd629 0x4108a894a77bfac5 0x300000003ffffe3c 0x0600000007ffffc7

def z442 : W := mkw 0x000441044170409a 0x20008820882e0813 0xd02cc304c3f8e03d 0xda059860987f1c07

def z443 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0700000000000000 0x00e0000000000000

def z444 : W := mkw 0x135d34f52f1f9f2d 0xc26ba69ea5e3f3e5 0xefd72ce73f1f1e3f 0xbdfae59ce7e3e3c7

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004008400000003 0x9800801080000000

def z446 : W := mkw 0x0000400840406040 0x2000080108080c08 0x0008c018c000e000 0x0001180318001c00

def z447 : W := mkw 0x0000000000000000 0x0000000000000000 0xb70000003c000004 0x76e0000007800000

def z448 : W := mkw 0x0effc00033d24000 0x01dff800067a4800 0x8fffc00003e00001 0xf1fff800007c0000

def z449 : W := mkw 0x131d30fd0d1fbb4d 0xc263a61fa1a3f769 0xbf1f30ff3c1fffc7 0x77e3e61fe783fff8

def z450 : W := mkw 0x04e78e07a3120428 0x409cf1c0f4624085 0x48e7cf07c3000038 0x891cf9e0f8600007

def z451 : W := mkw 0x0041042122030621 0x40082084244060c4 0x2000000020070e00 0x040000000400e1c0

def z452 : W := mkw 0x000000a000091201 0x0000001400012240 0x000020e000001e02 0x0000041c000003c0

def z453 : W := mkw 0x01003ef780091629 0x402007def00122c5 0x40003fffc0001e3a 0x080007fff80003c7

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0100000201f0005 0x340200000403e000

def z455 : W := mkw 0x000401840138109a 0x0000803080270213 0xd024138403f811ff 0xda048270807f023f

def z456 : W := mkw 0x25e13e2136830f25 0x44bc27c426d061e4 0x2fd32c633c070e00 0x25fa658c6780e1c0

def z457 : W := mkw 0x05a03a5280000000 0x00b4074a50000000 0xc7e03fffc0000002 0xf8fc07fff8000000

def z458 : W := mkw 0x0040040022000420 0x0008008004400084 0x20c02c0020000e00 0x24180580040001c0

def z459 : W := mkw 0x025d00002b168000 0x004ba0000562d000 0xbfdf00003f1fe005 0xf7fbe00007e3fc00

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x000cc09cc0000001 0x0001981398000000

def z461 : W := mkw 0x0045040023120420 0x0008a08004624084 0xe8d72c00231f1e3f 0xbd1ae5800463e3c7

def z462 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x402cc39cc3f8e039 0x88059873987f1c07

def z463 : W := mkw 0x07babb5280200092 0x00f7576a50040012 0xdfffffffc3e011ff 0xfbfffffff87c023f

def z464 : W := mkw 0x0800400018c4c000 0x0100080003189800 0x100000001ce0e000 0x02000000039c1c00

def z465 : W := mkw 0x104504ad2f1fbf6d 0xc208a095a5e3f7ed 0x300000003f1ffffc 0x0600000007e3ffff

def z466 : W := mkw 0x35e03fa83eadbff7 0x86bc07f507d5b7fe 0xf7e03f003ffffffe 0xfefc07e007ffffff

def z467 : W := mkw 0x04a28a0280000000 0x0094514050000000 0xc8efdf9fc0000003 0xd91dfbf3f8000000

def z468 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3728c0003fffe004 0x46e5180007fffc00

def z469 : W := mkw 0x1fbaf0581cc4e944 0x83f75e0b03989d28 0x1728d0181ce0e1c0 0x42e51a03039c1c38

def z470 : W := mkw 0x0001002100030201 0x4000200420006040 0x0813006300070000 0x0102600c6000e000

def z471 : W := mkw 0x25e03e0036800d24 0x04bc07c006d001a4 0xe7c02c003f001e3e 0xbcf8058007e003c7

def z472 : W := mkw 0x02180088080cb040 0x0043001101019608 0xb71810983c1ff1c7 0x76e302130783fe38

def z473 : W := mkw 0x000404a501191629 0x40008094a02322c5 0xc0042ce703181e3f 0x9800859ce06303c7

def z474 : W := mkw 0x25e13f2136a30fb7 0x44bc27e426d461f6 0xfff33f633fe71ffe 0xfffe67ec67fce3ff

def z475 : W := mkw 0x0ffffa52b3d24000 0x01ffff4a567a4800 0xcfffffffc3e00003 0xf9fffffff87c0000

def z476 : W := mkw 0x00454505637244ba 0x6008a8a0ac6e4897 0x48e7cf07c3e00038 0x891cf9e0f87c0007

def z477 : W := mkw 0x021a805280000000 0x0043500a50000000 0x0008c018c0000000 0x0001180318000000

def z478 : W := mkw 0x01003a5280000000 0x0020074a50000000 0xc02cffffc0000003 0xd8059ffff8000000

def z479 : W := mkw 0x004500a0231b1201 0x0008a01404636240 0xa8d720e0231f1e07 0xb51ae41c0463e3c0

def z480 : W := mkw 0x121800580804a040 0x8243000b01009408 0x000800180000e000 0x0001000300001c00

def z481 : W := mkw 0x04e78ea7a31b1629 0x409cf1d4f46362c5 0xe8f7efe7e31f1e3f 0xbd1efdfcfc63e3c7

def z482 : W := mkw 0x0ce7c00033d24000 0x019cf800067a4800 0x98efc00003f8e005 0xd31df800007f1c00

def z483 : W := mkw 0x21003f8c44283dfe 0x242007f1888507bf 0x40003f9cc0001ffa 0x080007f3980003ff

def z484 : W := mkw 0x0ffffa003bd6c000 0x01ffff40077ad800 0xffffff003fffe007 0xffffffe007fffc00

def z485 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x400cd39cc018f1fb 0x08019a7398031e3f

def z486 : W := mkw 0x25e43f8437b81dbe 0x04bc87f086f703b7 0xf7e43f843ff81fff 0xfefc87f087ff03ff

def z487 : W := mkw 0x17babafa8c0dbb45 0x82f7575f5181b768 0xbfdb3cfb3c1fffc7 0x77fb679f6783fff8

def z488 : W := mkw 0x131830f804093b45 0x8263061f00812768 0x871830f800001fc3 0x70e3061f000003f8

def z489 : W := mkw 0x135d75fd6f7fffff 0xe26baebfadefffff 0xffffffffffffffff 0xffffffffffffffff

def z490 : W := mkw 0x000004a500091629 0x40000094a00122c5 0x0000000000001e38 0x00000000000003c7

def z491 : W := mkw 0x2000050004200db6 0x040000a0008401b6 0x0000000000001ff8 0x00000000000003ff

def z492 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x2fdfc0003c1fe001 0x25fbf8000783fc00

def z493 : W := mkw 0x021a805280000000 0x0043500a50000000 0xc83fd3ffc0000003 0xd907fa7ff8000000

def z494 : W := mkw 0x000000a000091201 0x0000001400012240 0x001000e0001f0001 0x0002001c0003e000

def z495 : W := mkw 0x135834f82e0dbf65 0x826b069f05c1b7ec 0xf7d83cf83f1fffff 0xfefb079f07e3ffff

def z496 : W := mkw 0x0000008400081008 0x0000001080010201 0x400000840000103a 0x0800001080000207

def z497 : W := mkw 0x000000a500091209 0x40000014a0012241 0x000000e700000000 0x0000001ce0000000

def z498 : W := mkw 0x0100300004000904 0x0020060000800120 0x170010001c0001c0 0x42e0020003800038

def z499 : W := mkw 0x37f83e703e858f25 0x86ff07ce07d0b1e4 0x27d02c603c070e00 0x24fa058c0780e1c0

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x48c70c0700000000 0x8918e180e0000000

def z501 : W := mkw 0x0000008800083040 0x0000001100010608 0xd02cd39cc018f1c7 0xda059a7398031e38

def z502 : W := mkw 0x0041040122020420 0x4008208024404084 0x08c30c0300000000 0x0118618060000000

def z503 : W := mkw 0x06ba800000000000 0x00d7500000000000 0xcfffd39cc0000003 0xf9fffa7398000000

def z504 : W := mkw 0x07babada80083040 0x00f7575b50010608 0xdfffffffc018f1c7 0xfbfffffff8031e38

def z505 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7ecff9cffe01fff 0xfefd9ff39ffc03ff

def z506 : W := mkw 0x01003bdec02830da 0x2020077bd805061b 0x40003fffc00011fa 0x080007fff800023f

def z507 : W := mkw 0x131830580c04a944 0x8263060b01809528 0xb70830183c00ffc6 0x76e1060307801ff8

def z508 : W := mkw 0x04a00a0000000000 0x0094014000000000 0x40e00f0000000000 0x881c01e000000000

def z509 : W := mkw 0x121d00fd091fb249 0xc243a01fa123f649 0x081f00ff001fe001 0x0103e01fe003fc00

def z510 : W := mkw 0x07faba52b2800000 0x00ff574a56500000 0xffffffffffe00007 0xfffffffffffc0000

def z511 : W := mkw 0x21453fa5273b1fbf 0x4428a7f4a4e763f7 0xe8d73fe7231f1fff 0xbd1ae7fce463e3ff

def z512 : W := mkw 0x0004400001504000 0x00008800002a0800 0x0024c00003e00000 0x80049800007c0000

def z513 : W := mkw 0x0140340026000d24 0x0028068004c001a4 0xf7c03c003f001ffe 0xfef8078007e003ff

def z514 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x68c70c07231f1e3c 0x8d18e180e463e3c7

def z515 : W := mkw 0x2fbafb001ce4c996 0x05f75f60039c9932 0x1728d3001ce0e1c0 0x42e51a60039c1c38

def z516 : W := mkw 0x17f830f83e8dbb45 0x82ff061f07d1b768 0xb7f830f83fffffc7 0xf6ff061f07fffff8

def z517 : W := mkw 0x0eff80003b968000 0x01dff0000772d000 0xafd700003f1f0005 0xb5fae00007e3e000

def z518 : W := mkw 0x21003e0004000d24 0x042007c0008001a4 0x00002c0000000e00 0x00000580000001c0

def z519 : W := mkw 0x0318305000000000 0x0063060a00000000 0xc73cf3fcc0000003 0xf8e79e7f98000000

def z520 : W := mkw 0x04a6cb06c170409a 0x2094d960d82e0813 0x48e7cf07c3e00038 0x891cf9e0f87c0007

def z521 : W := mkw 0x0ce540003bd6c000 0x019ca800077ad800 0xb7e000003fffe004 0xf6fc000007fffc00

def z522 : W := mkw 0x0ce7c18c73fa70da 0x219cf8318e7f4e1b 0xd8efd39cc3f8f1ff 0xdb1dfa73987f1e3f

def z523 : W := mkw 0x0000018c402830da 0x200000318805061b 0xd020139cc3e011fe 0xda040273987c023f

def z524 : W := mkw 0x0000010000200092 0x0000002000040012 0x1000000003e011fc 0x02000000007c023f

def z525 : W := mkw 0x0ffffa52bbd6c000 0x01ffff4a577ad800 0xbfffec633fffe005 0xf7fffd8c67fffc00

def z526 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x170830f81c00ffc2 0x42e1061f03801ff8

def z527 : W := mkw 0x0005000001120000 0x0000a00000224000 0x08170000001f0001 0x0102e0000003e000

def z528 : W := mkw 0x2fffff8c7ffefdfe 0x25fffff18fffdfbf 0xffffff9cffffffff 0xfffffff39fffffff

def z529 : W := mkw 0x0effc1047bf6c09a 0x21dff8208f7ed813 0xffffc304ffffe03d 0xfffff8609ffffc07

def z530 : W := mkw 0x07befbdec17870da 0x20f7df7bd82f0e1b 0xd72cd39cc3f8f1ff 0xdae59a73987f1e3f

def z531 : W := mkw 0x0a1fc0a5095fd209 0x4143f814a12bfa41 0x081fc0e7001fe001 0x0103f81ce003fc00

def z532 : W := mkw 0x010030a004091b05 0x0020061400812360 0xb71030e03c1f1fc7 0x76e2061c0783e3f8

def z533 : W := mkw 0x000445ad417976fb 0x600088b5a82f2edf 0xd02cffffc3f8ffff 0xda059ffff87f1fff

def z534 : W := mkw 0x1ffff1fc7ffffbdf 0xa3fffe3f8fffff7b 0xfffff3fcffffffff 0xfffffe7f9fffffff

def z535 : W := mkw 0x0a1fc0000956c000 0x0143f800012ad800 0x983fc00003ffe005 0xd307f800007ffc00

def z536 : W := mkw 0x131c30fc0d1dbb4d 0x8263861f81a3b769 0xf71c30fc3f1fffff 0xfee3861f87e3ffff

def z537 : W := mkw 0x100441ac4d7dfbdf 0xa200883589afbf7b 0x300000003ffffffc 0x0600000007ffffff

def z538 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0fdfecffc0000001 0x21fbfd9ff8000000

def z539 : W := mkw 0x131c71fc4d7dfbdf 0xa2638e3f89afbf7b 0xb71830f83fffffff 0x76e3061f07ffffff

def z540 : W := mkw 0x25e03fa536a91fbf 0x44bc07f4a6d523f7 0xf7e03fe73fe01ffe 0xfefc07fce7fc03ff

def z541 : W := mkw 0x110030f80c0dbb45 0x8220061f0181b768 0x300030f83c1fffc6 0x0600061f0783fff8

def z542 : W := mkw 0x25e47f8c77f87dfe 0x24bc8ff18eff0fbf 0xf7e03f003ff8fffe 0xfefc07e007ff1fff

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x801020e000000003 0x3002041c00000000

def z544 : W := mkw 0x0ffbba52ba868000 0x01ff774a5750d000 0xeffffffffc070003 0xfdffffffff80e000

def z545 : W := mkw 0x131871584c64e9d6 0xa2630e2b098c9d3a 0x1728d318dce0e1c0 0x42e51a631b9c1c38

def z546 : W := mkw 0x17baba5a8c04a944 0x82f7574b51809528 0xdfffffffdc00e1c3 0xfbfffffffb801c38

def z547 : W := mkw 0x000500a5011b1209 0x4000a014a0236241 0xa81720e7201f1e07 0x3502e41ce403e3c0

def z548 : W := mkw 0x0000008800083040 0x0000001100010608 0x000800980018e001 0x0001001300031c00

def z549 : W := mkw 0x27fabe52b6800d24 0x04ff57ca56d001a4 0xeffffffffc000e03 0xfdffffffff8001c0

def z550 : W := mkw 0x25e53fa537bb1fbf 0x44bca7f4a6f763f7 0xf7e03f003fff1ffe 0xfefc07e007ffe3ff

def z551 : W := mkw 0x035d34f5231b1629 0x406ba69ea46362c5 0xefdf3cff231f1e3f 0xfdfbe79fe463e3c7

def z552 : W := mkw 0x0ebec00019d4c000 0x01d7d800033a9800 0x972cc0001ff8e005 0xd2e5980003ff1c00

def z553 : W := mkw 0x21003f0004200db6 0x042007e0008401b6 0xd0203f0003e01ffe 0xda0407e0007c03ff

def z554 : W := mkw 0x0845400033d24000 0x0108a800067a4800 0x0000000003e00000 0x00000000007c0000

def z555 : W := mkw 0x0041042122030621 0x40082084244060c4 0xe8d72ce720070e03 0xbd1ae59ce400e1c0

def z556 : W := mkw 0x131834fd0c0dbf6d 0xc263069fa181b7ed 0xf7183cff3c1fffff 0x7ee3079fe783ffff

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c02c0000000002 0xb818058000000000

def z558 : W := mkw 0x121800f8080db241 0x8243001f0101b648 0xa01820f8201ffe07 0x3403041f0403ffc0

def z559 : W := mkw 0x0a1fc08c495ef048 0x2143f811892bde09 0x081fc09cc01fe001 0x0103f8139803fc00

def z560 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x281700e7231f1e3d 0x0502e01ce463e3c7

def z561 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xcfd72ce700000003 0xb9fae59ce0000000

def z562 : W := mkw 0x0ce3800032820000 0x019c700006504000 0x08c3000000000000 0x0118600000000000

def z563 : W := mkw 0x0045400023524000 0x0008a800046a4800 0xb8ffc00023ffe005 0xf71ff800047ffc00

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x0028d318c0000000 0x40051a6318000000

def z565 : W := mkw 0x05a03b0000200092 0x00b4076000040012 0xd7e03f0003e011fe 0xfafc07e0007c023f

def z566 : W := mkw 0x100000a8080db241 0x820000150101b648 0x00000000001fe000 0x000000000003fc00

def z567 : W := mkw 0x21003f5284200db6 0x042007ea508401b6 0x40003fffc0001ffa 0x080007fff80003ff

def z568 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x48d70ce7031f0039 0x891ae19ce063e007

def z569 : W := mkw 0x131871f84c6dfbd7 0xa2630e3f098dbf7a 0xb738f3f8fcffffc7 0x76e71e7f1f9ffff8

def z570 : W := mkw 0x1ffff0703fd7cb05 0x83fffe0e07faf960 0xbfffe0603fffee05 0xf7fffc0c07fffdc0

def z571 : W := mkw 0x37f83ef83e8dbf65 0x86ff07df07d1b7ec 0xb7d83cf83c1fffc7 0x76fb079f0783fff8

def z572 : W := mkw 0x25e03f52b6a00db6 0x04bc07ea56d401b6 0xf7e03fffffe01ffe 0xfefc07fffffc03ff

def z573 : W := mkw 0x24e44f8c73f874fa 0x249c89f18e7f0e9f 0xd0ecdf9cc3f8f1ff 0xda1d9bf3987f1e3f

def z574 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0f3fd3ffc0000001 0x41e7fa7ff8000000

def z575 : W := mkw 0x0a1fc18c497ef0da 0x2143f831892fde1b 0xd83fd39cc3fff1ff 0xdb07fa73987ffe3f

def z576 : W := mkw 0x0004008401181008 0x0000801080230201 0x000000000318103c 0x0000000000630207

def z577 : W := mkw 0x031ab05280000000 0x0063560a50000000 0x8f1ff0ffc0000003 0x71e3fe1ff8000000

def z578 : W := mkw 0x04e5000033920000 0x009ca00006724000 0xbff700003fff0005 0xf7fee00007ffe000

def z579 : W := mkw 0x0effc4213bd7c621 0x41dff884277af8c4 0xbfffec633fffee05 0xf7fffd8c67fffdc0

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x802cc00000000001 0xd005980000000000

def z581 : W := mkw 0x0fbffa528956c000 0x01f7ff4a512ad800 0xcfffffffc01fe003 0xf9fffffff803fc00

def z582 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x001830f8001fffc3 0x0003061f0003fff8

def z583 : W := mkw 0x2ffaff003ee4cdb6 0x05ff5fe007dc99b6 0xf7e8ff003fe0fffe 0xfefd1fe007fc1fff

def z584 : W := mkw 0x1a1fc0f8095ff241 0x8343f81f012bfe48 0x081fc0f8001fe001 0x0103f81f0003fc00

def z585 : W := mkw 0x17babafa84093b45 0x82f7575f50812768 0xcfffffffc0001fc3 0xf9fffffff80003f8

def z586 : W := mkw 0x131c70fc4d5dfb4d 0xa2638e1f89abbf69 0xb71cf0fcfc1fffc7 0x76e39e1f9f83fff8

def z587 : W := mkw 0x37fabffabeadbff7 0x86ff57ff57d5b7fe 0xffffffffffffffff 0xffffffffffffffff

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008109800000003 0x5001021300000000

def z589 : W := mkw 0x06bec00001504000 0x00d7d800002a0800 0x9fffc00003f8e005 0xf3fff800007f1c00

def z590 : W := mkw 0x0004400441504008 0x20008800882a0801 0x0004c004c0000000 0x0000980098000000

def z591 : W := mkw 0x05a03a0000000000 0x00b4074000000000 0x07c02c0000000000 0x20f8058000000000

def z592 : W := mkw 0x004505a5233b16bb 0x4008a0b4a46762d7 0xf8f73fe723ff1fff 0xff1ee7fce47fe3ff

def z593 : W := mkw 0x00000a0280000000 0x0000014050000000 0x40000f07c0000000 0x080001e0f8000000

def z594 : W := mkw 0x25e07f0876e06df6 0x24bc0fe10edc0dbe 0xf7e8ff18ffe0fffe 0xfefd1fe31ffc1fff

def z595 : W := mkw 0x0000018c402830da 0x200000318805061b 0x00000000000011f8 0x000000000000023f

def z596 : W := mkw 0x24e0050036a00db6 0x049c00a006d401b6 0xb7e000003fe01ffc 0xf6fc000007fc03ff

def z597 : W := mkw 0x0ebec18c59fcf0da 0x21d7d8318b3f9e1b 0xd72cd39cdff8f1ff 0xdae59a739bff1e3f

def z598 : W := mkw 0x0004408801587040 0x00008811002b0e08 0x902cd09803f8f1c7 0xd2059a13007f1e38

def z599 : W := mkw 0x04e504a5339b1629 0x409ca094a67362c5 0xfff72ce73fff1e3f 0xfffee59ce7ffe3c7

def z600 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x67e02f003fe00e38 0xacfc05e007fc01c7

def z601 : W := mkw 0x0fbafa5298c4c000 0x01f75f4a53189800 0xdfffffffdce0e003 0xfbfffffffb9c1c00

def z602 : W := mkw 0x2040050032a004b2 0x040800a006540096 0x0000000003e00038 0x00000000007c0007

def z603 : W := mkw 0x27babb5294a00996 0x04f7576a52940132 0x1728d318dce001c0 0x42e51a631b9c0038

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x08d32c6300000000 0x211a658c60000000

def z605 : W := mkw 0x021a805280000000 0x0043500a50000000 0xc8dfecffc0000003 0xb91bfd9ff8000000

def z606 : W := mkw 0x06ba800000000000 0x00d7500000000000 0x0fd3000000000000 0x21fa600000000000

def z607 : W := mkw 0x05a03a0000000000 0x00b4074000000000 0xcff73fe700000003 0xf9fee7fce0000000

def z608 : W := mkw 0x204505a537bb1fbf 0x4408a0b4a6f763f7 0x300000003fff1ffc 0x0600000007ffe3ff

def z609 : W := mkw 0x0004000401100008 0x0000800080220001 0x4004000403000038 0x8800800080600007

def z610 : W := mkw 0x1ffff0583fd6e944 0x83fffe0b07fadd28 0xbfffd0183fffe1c5 0xf7fffa0307fffc38

def z611 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x60002ce7231f1e3e 0x0c00059ce463e3c7

def z612 : W := mkw 0x07bafb5ac06060d2 0x20f75f6b580c0c1a 0x1728d318c0e0e1c0 0x42e51a63181c1c38

def z613 : W := mkw 0x0004400001504000 0x00008800002a0800 0x1000000003f8e004 0x02000000007f1c00

def z614 : W := mkw 0x04e4418c73f870da 0x209c88318e7f0e1b 0xf7ecd39cfff8f1ff 0xfefd9a739fff1e3f

def z615 : W := mkw 0x0a1b800008068000 0x014370000100d000 0x0813000000070000 0x010260000000e000

def z616 : W := mkw 0x135934712e078f25 0xc26b268e25c0f1e4 0x2fd32c633c070e00 0x25fa658c6780e1c0

def z617 : W := mkw 0x0000410040604092 0x20000820080c0812 0x0020c300c0e00000 0x00041860181c0000

def z618 : W := mkw 0x1218007008058201 0x8243000e0100b040 0x0010006000070000 0x0002000c0000e000

def z619 : W := mkw 0x131830580c04a944 0x8263060b01809528 0x971830f81c00e1c3 0x72e3061f03801c38

def z620 : W := mkw 0x025d04a52b1f9629 0x404ba094a563f2c5 0xffdf2ce73f1ffe3f 0xfffbe59ce7e3ffc7

def z621 : W := mkw 0x004004a522091629 0x40080094a44122c5 0xe0c02ce723001e3e 0xbc18059ce46003c7

def z622 : W := mkw 0x000005ad402936fb 0x600000b5a80526df 0x40003fffc0001ffa 0x080007fff80003ff

def z623 : W := mkw 0x25e03e0036800d24 0x04bc07c006d001a4 0xb7e02c003fe00e04 0xf6fc058007fc01c0

def z624 : W := mkw 0x17baba728c058b05 0x82f7574e5180b160 0xeffffffffc070e03 0xfdffffffff80e1c0

def z625 : W := mkw 0x304005a83eadbff7 0x860800b507d5b7fe 0x300000003ffffffc 0x0600000007ffffff

def z626 : W := mkw 0x0318305000000000 0x0063060a00000000 0x0710206000000000 0x20e2040c00000000

def z627 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x8fdb3cfb00000003 0x71fb679f60000000

def z628 : W := mkw 0x04e0000032800000 0x009c000006500000 0x00e0000003e00000 0x801c0000007c0000

def z629 : W := mkw 0x07befa5281504000 0x00f7df4a502a0800 0xdfffffffc3f8e007 0xfbfffffff87f1c00

def z630 : W := mkw 0x05a03a0000000000 0x00b4074000000000 0x0720130000000000 0x40e4026000000000

def z631 : W := mkw 0x0000010000200092 0x0000002000040012 0xd02cd39cc3e011ff 0xda059a73987c023f

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x081700e700000001 0x0102e01ce0000000

def z633 : W := mkw 0x0100300000000000 0x0020060000000000 0x8700300000000002 0x70e0060000000000

def z634 : W := mkw 0x021a800000000000 0x0043500000000000 0x081fc00000000001 0x0103f80000000000

def z635 : W := mkw 0x100000a804093b45 0x8200001500812768 0x0000000000001fc0 0x00000000000003f8

def z636 : W := mkw 0x1effc0a83fdffb45 0x83dff81507fbff68 0xbfffc0003fffffc5 0xf7fff80007fffff8

def z637 : W := mkw 0x2effcf003bf6c4b2 0x05dff9e0077ed896 0xffffcf003fffe03d 0xfffff9e007fffc07

def z638 : W := mkw 0x0004018c413830da 0x200080318827061b 0xc004139cc31811ff 0x980082739863023f

def z639 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x8738f3f8c0000003 0x70e71e7f18000000

def z640 : W := mkw 0x0004408c41587048 0x20008811882b0e09 0x902cc09cc3f8e005 0xd2059813987f1c00

def z641 : W := mkw 0x0eba800018848000 0x01d7500003109000 0x070000001c000000 0x00e0000003800000

def z642 : W := mkw 0x00450084231a1008 0x0008a01084634201 0xe8d70084231f103f 0xbd1ae0108463e207

def z643 : W := mkw 0x0002800280000000 0x0000500050000000 0x0807c007c0000000 0x0100f800f8000000

def z644 : W := mkw 0x0000010000200092 0x0000002000040012 0x4020030003e00038 0x88040060007c0007

def z645 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4728ffffc0000002 0x48e51ffff8000000

def z646 : W := mkw 0x000000a000091201 0x0000001400012240 0xe8d72ce7201f1e07 0xbd1ae59ce403e3c0

def z647 : W := mkw 0x0000002000010201 0x0000000400002040 0x2010206020070e00 0x2402040c0400e1c0

def z648 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xc7e8ff18c0000002 0xf8fd1fe318000000

def z649 : W := mkw 0x2ffbbe003e868d24 0x05ff77c007d0d1a4 0x2fd32c003c070e00 0x25fa65800780e1c0

def z650 : W := mkw 0x131830700c058b05 0x8263060e0180b160 0xb71030603c071fc6 0x76e2060c0780e3f8

def z651 : W := mkw 0x05e03e0022000420 0x00bc07c004400084 0xe7e03f0023001e3e 0xfcfc07e0046003c7

def z652 : W := mkw 0x114534fd271b3f6d 0xc228a69fa4e367ed 0xe8d73cff231f1fff 0xbd1ae79fe463e3ff

def z653 : W := mkw 0x0ca2c00010c04000 0x0194580002180800 0x0020c00000e00000 0x00041800001c0000

def z654 : W := mkw 0x0100300004000904 0x0020060000800120 0x0000300000001fc2 0x00000600000003f8

def z655 : W := mkw 0x004505ad633b36fb 0x6008a0b5ac6766df 0xe8d73fffe31f1fff 0xbd1ae7fffc63e3ff

def z656 : W := mkw 0x004545a5637b56bb 0x6008a8b4ac6f6ad7 0xe8f7efe7e3ff1e3f 0xbd1efdfcfc7fe3c7

def z657 : W := mkw 0x0ffffbdefbfef0da 0x21ffff7bdf7fde1b 0xfffffffffffff1ff 0xfffffffffffffe3f

def z658 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x2ff7c0003fe70000 0xa5fef80007fce000

def z659 : W := mkw 0x37b83b581ca4a9d6 0x86f7076b0394953a 0x172813181ce0e1c0 0x42e50263039c1c38

def z660 : W := mkw 0x0218000000000000 0x0043000000000000 0x8718000000000001 0x70e3000000000000

def z661 : W := mkw 0x1ffbb0703e878b05 0x83ff760e07d0f160 0x2fd320603c070e00 0x25fa640c0780e1c0

def z662 : W := mkw 0x37f83f703ea58fb7 0x86ff07ee07d4b1f6 0xf7f03f603fe71ffe 0xfefe07ec07fce3ff

def z663 : W := mkw 0x0218000008048000 0x0043000001009000 0x271000003c070000 0x24e200000780e000

def z664 : W := mkw 0x27fabf52b6a00db6 0x04ff57ea56d401b6 0xf7e8ff18ffe01ffe 0xfefd1fe31ffc03ff

def z665 : W := mkw 0x0807c00001524000 0x0100f800002a4800 0x0807c00000000000 0x0100f80000000000

def z666 : W := mkw 0x0efb80003a868000 0x01df70000750d000 0xafffc0003c070001 0xf5fff8000780e000

def z667 : W := mkw 0x0efb80003a868000 0x01df70000750d000 0xbfdb00003c1fe005 0x77fb60000783fc00

def z668 : W := mkw 0x131831f80c2dbbd7 0x8263063f0185b77a 0xf73833f83fffffff 0xfee7067f07ffffff

def z669 : W := mkw 0x0004408c41587048 0x20008811882b0e09 0x900cd09cc018f1c7 0x52019a1398031e38

def z670 : W := mkw 0x24e50fa533bb16bb 0x449ca1f4a67762d7 0xe8f72fe723ff1e3f 0xbd1ee5fce47fe3c7

def z671 : W := mkw 0x06ba800000000000 0x00d7500000000000 0x0728c00000000000 0x40e5180000000000

def z672 : W := mkw 0x0a1ac0000844c000 0x0143580001089800 0x0008c0000000e000 0x0001180000001c00

def z673 : W := mkw 0x0000400000404000 0x0000080000080800 0x1028c00000e0e000 0x42051800001c1c00

def z674 : W := mkw 0x27feffdef7f87dfe 0x24ffdffbdeff0fbf 0xfffffffffff8ffff 0xffffffffffff1fff

def z675 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x271030f83c071fc2 0x24e2061f0780e3f8

def z676 : W := mkw 0x0000010000200092 0x0000002000040012 0x40001300000011fa 0x080002600000023f

def z677 : W := mkw 0x1b5d70f83fdffb45 0x836bae1f07fbff68 0xb71830f83fffffc7 0x76e3061f07fffff8

def z678 : W := mkw 0x00000108402020d2 0x200000210804041a 0x00001318c00001c0 0x0000026318000038

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x900800000018e005 0x5201000000031c00

def z680 : W := mkw 0x27ffbff7b7bb1fbf 0x44fff7fef6f763f7 0xffffffffffff1fff 0xffffffffffffe3ff

def z681 : W := mkw 0x0318305008048000 0x0063060a01009000 0xb71830f83c1fe007 0x76e3061f0783fc00

def z682 : W := mkw 0x27fabf52b2a004b2 0x04ff57ea56540096 0xcfffffffc3e0003b 0xf9fffffff87c0007

def z683 : W := mkw 0x0ebac10858e4e0d2 0x21d758210b1c9c1a 0x1728d318dce0e1c0 0x42e51a631b9c1c38

def z684 : W := mkw 0x0004008401181008 0x0000801080230201 0xc02cd39cc318103f 0xd8059a7398630207

def z685 : W := mkw 0x0004408c41587048 0x20008811882b0e09 0x000000000018e000 0x0000000000031c00

def z686 : W := mkw 0x00400500222004b2 0x000800a004440096 0xf0e03f0023e01ffe 0xfe1c07e0047c03ff

def z687 : W := mkw 0x131831fc4c2dbbdf 0xa263063f8985b77b 0xf71833fcfc1fffff 0x7ee3067f9f83ffff

def z688 : W := mkw 0x0ce7c40533d24428 0x419cf880a67a4885 0x48e7cc0703e00038 0x891cf980e07c0007

def z689 : W := mkw 0x1effc0f83bdff241 0x83dff81f077bfe48 0xbfffc0f83fffe005 0xf7fff81f07fffc00

def z690 : W := mkw 0x05a03a0004000904 0x00b4074000800120 0xf7e03f003c001fc6 0xfefc07e0078003f8

def z691 : W := mkw 0x0104718c457879de 0x20208e3188af0f3b 0xf72cf39cfff8ffff 0xfee59e739fff1fff

def z692 : W := mkw 0x131830700c058b05 0x8263060e0180b160 0xa71830f83c070e03 0x74e3061f0780e1c0

def z693 : W := mkw 0x084540003bd6c000 0x0108a800077ad800 0xb02cc0003fffe005 0xd605980007fffc00

def z694 : W := mkw 0x24e00e0032800420 0x049c01c006500084 0x00c00c0000000000 0x0018018000000000

def z695 : W := mkw 0x0000018c402830da 0x200000318805061b 0xc02cd39cc00011fb 0xd8059a739800023f

def z696 : W := mkw 0x0ce7c0003bd6c000 0x019cf800077ad800 0x38e7c0003fffe004 0x871cf80007fffc00

def z697 : W := mkw 0x07babbdec02830da 0x20f7577bd805061b 0xcfffffffc00011fb 0xf9fffffff800023f

def z698 : W := mkw 0x00004188406870d2 0x20000831080d0e1a 0x9028d398c0f8f1c7 0x52051a73181f1e38

def z699 : W := mkw 0x20000f00002004b2 0x040001e000040096 0x40000f0000000038 0x080001e000000007

def z700 : W := mkw 0x25e03e0036800d24 0x04bc07c006d001a4 0xe7e03f003c000e02 0xfcfc07e0078001c0

def z701 : W := mkw 0x25e53ea5379b1f2d 0x44bca7d4a6f363e5 0xefd72ce73f1f1e3f 0xbdfae59ce7e3e3c7

def z702 : W := mkw 0x2effc5003ff6cdb6 0x05dff8a007fed9b6 0xbfffc0003ffffffd 0xf7fff80007ffffff

def z703 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x67c03f003c001ffa 0x2cf807e0078003ff

def z704 : W := mkw 0x0045042123130621 0x4008a084246260c4 0xa8d72c63231f0e05 0xb51ae58c6463e1c0

def z705 : W := mkw 0x0ffffef7bbdfd629 0x41ffffdef77bfac5 0xfffffffffffffe3f 0xffffffffffffffc7

def z706 : W := mkw 0x0effc5ad7bfff6fb 0x61dff8b5af7ffedf 0xffffffffffffffff 0xffffffffffffffff

def z707 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf71830f83f1fffff 0xfee3061f07e3ffff

def z708 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb738f3f8fc1fffc7 0x76e71e7f1f83fff8

def z709 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xdfffffffc3e00007 0xfbfffffff87c0000

def z710 : W := mkw 0x110030a80c0dbb45 0x822006150181b768 0xb70830983c1fffc7 0x76e106130783fff8

def z711 : W := mkw 0x131ab0fa8c0dbb45 0x8263561f5181b768 0xff3ff3fffc1fffc7 0xffe7fe7fff83fff8

def z712 : W := mkw 0x14a28aaa8c0dbb45 0x829451555181b768 0x78e7cf07fc1fffc4 0x8f1cf9e0ff83fff8

def z713 : W := mkw 0x25e47e8c77d87d6c 0x24bc8fd18efb0fad 0x27ccec9cfc18ee01 0x24f99d939f831dc0

def z714 : W := mkw 0x00004188406870d2 0x20000831080d0e1a 0xd028d398c3f8f1ff 0xda051a73187f1e3f

def z715 : W := mkw 0x010030000c048904 0x0020060001809120 0xb70030003c1fffc6 0x76e006000783fff8

def z716 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x370000003c1fffc4 0x06e000000783fff8

def z717 : W := mkw 0x07befbdec17870da 0x20f7df7bd82f0e1b 0x1fd32c6303f8f1fc 0x23fa658c607f1e3f

def z718 : W := mkw 0x004544a5235b5629 0x4008a894a46b6ac5 0xf8d72ce723fffe3f 0xbf1ae59ce47fffc7

def z719 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd8efdf9fc3f8f1ff 0xdb1dfbf3f87f1e3f

def z720 : W := mkw 0x225a8552b6a00db6 0x044b50aa56d401b6 0x381fc0ffffe01ffd 0x0703f81ffffc03ff

def z721 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x5028d39cc3f8f1fe 0x4a051a73987f1e3f

def z722 : W := mkw 0x24e0050036a00db6 0x049c00a006d401b6 0xf7e02c003fe01ffe 0xfefc058007fc03ff

def z723 : W := mkw 0x09457a52bbd6c000 0x0128af4a577ad800 0x70003fffffffe006 0x0e0007fffffffc00

def z724 : W := mkw 0x21003fad44293fff 0x642007f5a88527ff 0x40003fffc0001ffa 0x080007fff80003ff

def z725 : W := mkw 0x05a03b0004200996 0x00b4076000840132 0xf7e03f003fe01ffe 0xfefc07e007fc03ff

def z726 : W := mkw 0x00414529626366f3 0x600828a52c4c6cde 0x38fbff7be0e7efc0 0x671f7fef7c1cfdf8

def z727 : W := mkw 0x2140350036a00db6 0x042806a006d401b6 0xf72033003fe01ffe 0xfee4066007fc03ff

def z728 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb73830f83fffffc7 0xf6e7061f07fffff8

def z729 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x68d72c67231f1e3c 0xad1ae58ce463e3c7

def z730 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x67e03f003fe01ffa 0xacfc07e007fc03ff

def z731 : W := mkw 0x0ce540003bd6c000 0x019ca800077ad800 0xbff700003fffe005 0xf7fee00007fffc00

def z732 : W := mkw 0x104545ad6f7fffff 0xe208a8b5adefffff 0x300000003ffffffc 0x0600000007ffffff

def z733 : W := mkw 0x004504ad231b3669 0x4008a095a46366cd 0xf8d72ce7231fffff 0xbf1ae59ce463ffff

def z734 : W := mkw 0x2de3bf0036a20db6 0x05bc77e006d441b6 0xffe33f003fe01ffe 0xfffc67e007fc03ff

def z735 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x502cd39cc3e0f1fa 0xca059a73987c1e3f

def z736 : W := mkw 0x31003ffd04293fff 0xc62007ffa08527ff 0x40003fff00001ffa 0x080007ffe00003ff

def z737 : W := mkw 0x004544ad635b7669 0x6008a895ac6b6ecd 0xe8ffffffe31ffe3f 0xfd1ffffffc63ffc7

def z738 : W := mkw 0x25a53ba515bb1b9f 0x44b4a774a2b76373 0x1f3713e71cff01c1 0x43e6e27ce39fe038

def z739 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x371830783c1fffc4 0x66e3060f0783fff8

def z740 : W := mkw 0x084540003bd6c000 0x0108a800077ad800 0xb70000003fffe004 0x76e0000007fffc00

def z741 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfd700003fffe005 0xb7fae00007fffc00

def z742 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8f73fe7231f1e3f 0xfd1ee7fce463e3c7

def z743 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xefffffffe01f0007 0xfdfffffffc03e000

def z744 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8dfecffe31f1e3f 0xbd1bfd9ffc63e3c7

def z745 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x9028d398c3f8f1ff 0x52051a73187f1e3f

def z746 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xf03cd39ce3fff1ff 0xfe079a739c7ffe3f

def z747 : W := mkw 0x004544a5235b5629 0x4008a894a46b6ac5 0xf8ffffffe3fffe3f 0xff1ffffffc7fffc7

def z748 : W := mkw 0x25e03f5036a00db6 0x04bc07ea06d401b6 0xf7e03ff83fe01ffe 0xfefc07ff07fc03ff

def z749 : W := mkw 0x0041042122030621 0x40082084244060c4 0xe8d72ce723071e3f 0xbd1ae59ce460e3c7

def z750 : W := mkw 0x0ce540003bd6c000 0x019ca800077ad800 0x372000003fffe004 0x46e4000007fffc00

def z751 : W := mkw 0x2ce7c50033f244b2 0x059cf8a0067e4896 0x08e7c00003e00038 0x811cf800007c0007

def z752 : W := mkw 0x07baba528c048904 0x00f7574a51809120 0xfffffffffc1fffc7 0xffffffffff83fff8

def z753 : W := mkw 0x121800a80c0dbb45 0x824300150181b768 0x371000003c1fffc4 0x26e200000783fff8

def z754 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf7183cff3c1fffc7 0x7ee3079fe783fff8

def z755 : W := mkw 0x0effca02bbd6c000 0x01dff940577ad800 0xffffdf9fffffe007 0xfffffbf3fffffc00

def z756 : W := mkw 0x0041042122030621 0x40082084244060c4 0x68d32c6323070e38 0xad1a658c6460e1c7

def z757 : W := mkw 0x0efac0003ac4c000 0x01df580007589800 0xb7f8c0003fffe005 0xf6ff180007fffc00

def z758 : W := mkw 0x21403f0036a00db6 0x042807e006d401b6 0xf7003f003fe01ffe 0x7ee007e007fc03ff

def z759 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x370000003fffe004 0x06e0000007fffc00

def z760 : W := mkw 0x004544a5635b5629 0x6008a894ac6b6ac5 0xe8d7ece7e31f1e3f 0xbd1afd9cfc63e3c7

def z761 : W := mkw 0x0fbaba5298848000 0x01f7574a53109000 0xcfffffffdc000003 0xf9fffffffb800000

def z762 : W := mkw 0x13183afa8c0dbb45 0x8263075f5181b768 0xf73cfffffc1fffc7 0xfee79fffff83fff8

def z763 : W := mkw 0x05a2ba5280000000 0x00b4574a50000000 0xc8efffffc0000003 0xd91dfffff8000000

def z764 : W := mkw 0x2140350036a00db6 0x042806a006d401b6 0x370020003fe01ffc 0x26e0040007fc03ff

def z765 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xb7e013003fe01ffc 0xf6fc026007fc03ff

def z766 : W := mkw 0x24e0050036a00db6 0x049c00a006d401b6 0x372000003fe01ffc 0x46e4000007fc03ff

def z767 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xfffffffffc000007 0xffffffffff800000

def z768 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xfff33f633fe01ffe 0xfffe67ec67fc03ff

def z769 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x48d72ce7031f1e3b 0x891ae59ce063e3c7

def z770 : W := mkw 0x07ffbef7a31b1629 0x40fff7def46362c5 0x2728d318e31f1e3c 0x44e51a631c63e3c7

def z771 : W := mkw 0x121800a80c0dbb45 0x824300150181b768 0xb71820e03c1fffc7 0x76e3041c0783fff8

def z772 : W := mkw 0x0000418c406870da 0x20000831880d0e1b 0xd028d39cc3e0f1fe 0xda051a73987c1e3f

def z773 : W := mkw 0x135d345d2f16ad6c 0xc26ba68ba5e2d5ad 0x5fcf1c1f1f00e1f8 0xcbf9e383e3e01c3f

def z774 : W := mkw 0x131830fc0c0dbb4d 0x8263061f8181b769 0xf71830fc3c1fffff 0x7ee3061f8783ffff

def z775 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3fdfc0003fffe005 0x27fbf80007fffc00

def z776 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf73833f83c1fffc7 0xfee7067f0783fff8

def z777 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffd0003ffff1c7 0xf7fffa0007fffe38

def z778 : W := mkw 0x06fd00003b968000 0x00dfa0000772d000 0xbfff00003fffe005 0xf7ffe00007fffc00

def z779 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x68d72ce7201f1e3b 0x2d1ae59ce403e3c7

def z780 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd03cf3fcc3f8f1ff 0xfa079e7f987f1e3f

def z781 : W := mkw 0x25e2bf02b6a00db6 0x04bc57e056d401b6 0xfff7ffe7ffe01fff 0xfffefffcfffc03ff

def z782 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xffd72ce73f1f1e3f 0xfffae59ce7e3e3c7

def z783 : W := mkw 0x06fa80003a848000 0x00df500007509000 0xbfffc0003fffe005 0xf7fff80007fffc00

def z784 : W := mkw 0x021800000c048904 0x0043000001809120 0xb71800003c1fffc5 0x76e300000783fff8

def z785 : W := mkw 0x310035f804293ff7 0x862006bf008527fe 0x000030f800001ffa 0x0000061f000003ff

def z786 : W := mkw 0x0effca02bbd6c000 0x01dff940577ad800 0xbfffcc033fffe005 0xf7fff98067fffc00

def z787 : W := mkw 0x0effc0053bd6c008 0x41dff800a77ad801 0xbfffc0073fffe005 0xf7fff800e7fffc00

def z788 : W := mkw 0x05a03a0000000000 0x00b4074000000000 0xcfffffffc0000003 0xf9fffffff8000000

def z789 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xb72033003fe01ffe 0x76e4066007fc03ff

def z790 : W := mkw 0x07baba5288048000 0x00f7574a51009000 0xcfffffffc01fe003 0xf9fffffff803fc00

def z791 : W := mkw 0x0a5fc0003bd6c000 0x014bf800077ad800 0xbf1fc0003fffe005 0x77e3f80007fffc00

def z792 : W := mkw 0x025d40002b56c000 0x004ba800056ad800 0xbfffc0003fffe005 0xf7fff80007fffc00

def z793 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xdfffffffc00011c7 0xfbfffffff8000238

def z794 : W := mkw 0x1a1fc0fd095ff249 0xc343f81fa12bfe49 0x081fc0ff001fe001 0x0103f81fe003fc00

def z795 : W := mkw 0x31003ffa84293ff7 0x862007ff508527fe 0x40003fffc0001ffa 0x080007fff80003ff

def z796 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x502cd39cc3f8e1f9 0xca059a73987f1c3f

def z797 : W := mkw 0x0004410001704092 0x00008820002e0812 0xd02cd39cc3f8f1ff 0xda059a73987f1e3f

def z798 : W := mkw 0x25e03f02b6a00db6 0x04bc07e056d401b6 0xf7e03f07ffe01ffe 0xfefc07e0fffc03ff

def z799 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4fefffffc0000002 0xc9fdfffff8000000

def z800 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf71c30fc3c1fffc7 0xfee3861f8783fff8

def z801 : W := mkw 0x0005418c417a70da 0x2000a831882f4e1b 0xd83fd39cc3fff1ff 0xdb07fa73987ffe3f

def z802 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb71030603c1fffc6 0x76e2060c0783fff8

def z803 : W := mkw 0x01003a5280000000 0x0020074a50000000 0xc8ffffffc0000003 0xf91ffffff8000000

def z804 : W := mkw 0x131c71744d75cb9f 0xa2638e2e89aeb973 0x6734e364ffe70e38 0xace69c6c9ffce1c7

def z805 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xb7e8c0003fffe004 0xf6fd180007fffc00

def z806 : W := mkw 0x0045040023120420 0x0008a08004624084 0xe8d72ce7231f1e3f 0xbd1ae59ce463e3c7

def z807 : W := mkw 0x131ab0fa8c0dbb45 0x8263561f5181b768 0xb718f0f8fc1fffc7 0x76e31e1f1f83fff8

def z808 : W := mkw 0x000504a5011b1629 0x4000a094a02362c5 0xc8d72ce7001f1e3b 0xb91ae59ce003e3c7

def z809 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x0fffffffc0000001 0x61fffffff8000000

def z810 : W := mkw 0x17baba528c048904 0x82f7574a51809120 0xcfffffffdc000003 0xf9fffffffb800000

def z811 : W := mkw 0x0efb818c7aaeb0da 0x21df70318f55d61b 0x6fd3139cfc0711fa 0x2dfa62739f80e23f

def z812 : W := mkw 0x000441ac417972db 0x20008835882f2e5b 0xd03cd3fcc3fff1ff 0xda079a7f987ffe3f

def z813 : W := mkw 0x0218000008048000 0x0043000001009000 0xb73800003fffe005 0xf6e7000007fffc00

def z814 : W := mkw 0x0effc052bbd6c000 0x01dff80a577ad800 0xbfffc018ffffe005 0xf7fff8031ffffc00

def z815 : W := mkw 0x0ebac4a518cdd629 0x41d75894a319bac5 0x5728ece71ce0fe3a 0x4ae51d9ce39c1fc7

def z816 : W := mkw 0x0effc002bbd6c000 0x01dff800577ad800 0xbfffc007ffffe005 0xf7fff800fffffc00

def z817 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb73cf0f83c1fffc7 0xf6e79e1f0783fff8

def z818 : W := mkw 0x2b1fff000d76cdb6 0x0563ffe001aed9b6 0x481fff00001ffffb 0x0903ffe00003ffff

def z819 : W := mkw 0x0a5d40003bd6c000 0x014ba800077ad800 0x371000003fffe004 0x26e2000007fffc00

def z820 : W := mkw 0x0effca02bbd6c000 0x01dff940577ad800 0xbfffc300ffffe005 0xf7fff8601ffffc00

def z821 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffc0843fffe007 0xfffff81087fffc00

def z822 : W := mkw 0x06b8000018848000 0x00d7000003109000 0xb73800003cffe005 0x76e70000079ffc00

def z823 : W := mkw 0x24e00f0036a00db6 0x049c01e006d401b6 0xf7e00f003fe01ffc 0xfefc01e007fc03ff

def z824 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb70810983c1fffc7 0x56e102130783fff8

def z825 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4fffefffc0000001 0xa9fffdfff8000000

def z826 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffd0983fffe007 0xf7fffa1307fffc00

def z827 : W := mkw 0x25e03f52b6a00db6 0x04bc07ea56d401b6 0xf7e03f633fe01ffe 0xfefc07ec67fc03ff

def z828 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7c02c003fe01ffe 0xbef8058007fc03ff

def z829 : W := mkw 0x37babb5a9ca4a9d6 0x86f7576b5394953a 0x1728d318dce0e1c0 0x42e51a631b9c1c38

def z830 : W := mkw 0x000400a401191209 0x0000801480232241 0xe8d72ce7231f1e3f 0xbd1ae59ce463e3c7

def z831 : W := mkw 0x021840000844c000 0x0043080001089800 0xb738c0003cffe005 0x76e71800079ffc00

def z832 : W := mkw 0x0140350026200db6 0x002806a004c401b6 0xf7e03f003fe01ffe 0xfefc07e007fc03ff

def z833 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e03f9cffe01ffe 0xfefc07f39ffc03ff

def z834 : W := mkw 0x07baba5290800000 0x00f7574a52100000 0xdfffffffdce00003 0xfbfffffffb9c0000

def z835 : W := mkw 0x06ba800000000000 0x00d7500000000000 0xcfffffffc0000003 0xf9fffffff8000000

def z836 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf72013003fe01ffe 0xdee4026007fc03ff

def z837 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xa8d32ce3231f1e3f 0x351a659c6463e3c7

def z838 : W := mkw 0x004004a022091621 0x00080094044122c4 0xe8d72ce7231f1e3f 0xbd1ae59ce463e3c7

def z839 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xb72cc0003fffe005 0xd6e5980007fffc00

def z840 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xb7e02c003fe01ffc 0xf6fc058007fc03ff

def z841 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4fffdfffc0000001 0xc9fffbfff8000000

def z842 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffffffffffe007 0xfffffffffffffc00

def z843 : W := mkw 0x07baba5284000904 0x00f7574a50800120 0xcfffffffc0001fc3 0xf9fffffff80003f8

def z844 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3fefc0003fffe004 0xc7fdf80007fffc00

def z845 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffc09cffffe005 0xf7fff8139ffffc00

def z846 : W := mkw 0x0ce540003bd6c000 0x019ca800077ad800 0x37c000003fffe004 0x26f8000007fffc00

def z847 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3fffc0003cffe001 0x67fff800079ffc00

def z848 : W := mkw 0x25e2bf0036a00db6 0x04bc57e006d401b6 0xffe7ff003fe01ffe 0xfffcffe007fc03ff

def z849 : W := mkw 0x04a28a0280000000 0x0094514050000000 0xc8ffffffc0000003 0xf91ffffff8000000

def z850 : W := mkw 0x021a805280000000 0x0043500a50000000 0xc8ffffffc0000003 0xf91ffffff8000000

def z851 : W := mkw 0x131830fa8c0dbb45 0x8263061f5181b768 0xb71830fffc1fffc7 0x76e3061fff83fff8

def z852 : W := mkw 0x0ebec00019d4c000 0x01d7d800033a9800 0xb73cc0003fffe005 0xf6e7980007fffc00

def z853 : W := mkw 0x05e0310036a00996 0x00bc062006d40132 0xf7e033003fe01ffe 0xfefc066007fc03ff

def z854 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb71cf0fcfc1fffc7 0x76e39e1f9f83fff8

def z855 : W := mkw 0x24e54f0573f244ba 0x649ca9e0ae7e4897 0x48e7cf07c3e00038 0x891cf9e0f87c0007

def z856 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x370000003fe01ffc 0x06e0000007fc03ff

def z857 : W := mkw 0x131830fc4c0dbb4d 0xa263061f8981b769 0xb71830fcfc1fffc7 0x76e3061f9f83fff8

def z858 : W := mkw 0x004104a5220b1629 0x40082094a44162c5 0x28d32c6320071e38 0x251a658c6400e3c7

def z859 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x371030f83c1fffc6 0x26e2061f0783fff8

def z860 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xfff73f003fe01fff 0xfffee7e007fc03ff

def z861 : W := mkw 0x0effc4053bd6c428 0x41dff880a77ad885 0xffffece73fffe03f 0xfffffd9ce7fffc07

def z862 : W := mkw 0x025800003a848000 0x004b000007509000 0xb71800003fffe005 0x76e3000007fffc00

def z863 : W := mkw 0x36f80ff83aadb6f3 0x86df01ff0755b6de 0x40f80ff803ffe039 0x881f01ff007ffc07

def z864 : W := mkw 0x00044108417060d2 0x20008821082e0c1a 0xd02cd318c3f8f1ff 0xda059a63187f1e3f

def z865 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e83f003ff8ffff 0xfefd07e007ff1fff

def z866 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffec633fffe005 0xf7fffd8c67fffc00

def z867 : W := mkw 0x25e03f52b6a00db6 0x04bc07ea56d401b6 0xf7ecffffffe01fff 0xfefd9ffffffc03ff

def z868 : W := mkw 0x13183afa8c0dbb45 0x8263075f5181b768 0xffdf3ffffc1fffc7 0xfffbe7ffff83fff8

def z869 : W := mkw 0x2ce7cf02b3f244b2 0x059cf9e0567e4896 0x48e7cf07c3e00038 0x891cf9e0f87c0007

def z870 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e83f983fe01fff 0xfefd07f307fc03ff

def z871 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd8ffd39cc3f8f1ff 0xfb1ffa73987f1e3f

def z872 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e03fe73fe01ffe 0xfefc07fce7fc03ff

def z873 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xbfdb3cfb3c1fffc7 0x77fb679f6783fff8

def z874 : W := mkw 0x25a03f0014a00db6 0x04b407e0029401b6 0xd7203f001fe01ffe 0xdae407e003fc03ff

def z875 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8d32c63231f1e3e 0xbd1a658c6463e3c7

def z876 : W := mkw 0x0100310004200996 0x0020062000840132 0xb70030003fe01ffe 0x76e0060007fc03ff

def z877 : W := mkw 0x004504ad231b3669 0x4008a095a46366cd 0xf8ffffffe31fffff 0xff1ffffffc63ffff

def z878 : W := mkw 0x2fbafb529ce4c996 0x05f75f6a539c9932 0x1728d318dce0e1c0 0x42e51a631b9c1c38

def z879 : W := mkw 0x131ab0f80c0dbb45 0x8263561f0181b768 0xbf1ff0f83c1fffc7 0x77e3fe1f0783fff8

def z880 : W := mkw 0x0effc4003bd6c420 0x01dff880077ad884 0xbfffc0003ffffe3d 0xf7fff80007ffffc7

def z881 : W := mkw 0x13183af80c0dbb45 0x8263075f0181b768 0xf7183ff83c1fffc7 0x7ee307ff0783fff8

def z882 : W := mkw 0x000541ad417b72db 0x6000a835a82f6e5b 0xd02cd39cc3fff1ff 0xda059a73987ffe3f

def z883 : W := mkw 0x031830500c048904 0x0063060a01809120 0xb71830f83c1fffc7 0x76e3061f0783fff8

def z884 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x371820f83c1fffc5 0x26e3041f0783fff8

def z885 : W := mkw 0x2040050036a00db6 0x040800a006d401b6 0xb70000003fe01ffc 0x76e0000007fc03ff

def z886 : W := mkw 0x204545ad77fb7fff 0x6408a8b5aeff6fff 0x300000003ffffffc 0x0600000007ffffff

def z887 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd0ecff9cc3f8f1ff 0xfa1d9ff3987f1e3f

def z888 : W := mkw 0x0a5d40003bd6c000 0x014ba800077ad800 0xb73cc0003fffe005 0xf6e7980007fffc00

def z889 : W := mkw 0x021800a8080db241 0x004300150101b648 0xb71830f83c1fffc7 0x76e3061f0783fff8

def z890 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xa8d72c63231f1e3d 0xb51ae58c6463e3c7

def z891 : W := mkw 0x121c40fc495df249 0xa243881f892bbe49 0x001800f8001fe001 0x0003001f0003fc00

def z892 : W := mkw 0x0effc4053bd6c428 0x41dff880a77ad885 0xffffec073ffffe3f 0xfffffd80e7ffffc7

def z893 : W := mkw 0x0ebac00018c4c000 0x01d7580003189800 0xbfffc0003cffe005 0xf7fff800079ffc00

def z894 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb71810183c1fffc5 0x76e302030783fff8

def z895 : W := mkw 0x1a1fc0fc495ff249 0xa343f81f892bfe49 0x081fc0fcc01fe001 0x0103f81f9803fc00

def z896 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb70830183c1fffc6 0x76e106030783fff8

def z897 : W := mkw 0x0ebfc00019d6c000 0x01d7f800033ad800 0x9f3fc0001fffe005 0xd3e7f80003fffc00

def z898 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x271830f83c1fffc3 0x24e3061f0783fff8

def z899 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x68d72ce7231f0e39 0xad1ae59ce463e1c7

def z900 : W := mkw 0x07baba5288048000 0x00f7574a51009000 0xdfffffffdc00e003 0xfbfffffffb801c00

def z901 : W := mkw 0x0004410c417060da 0x20008821882e0c1b 0xd02cd31cc3e0f1fe 0xda059a63987c1e3f

def z902 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8d73fffe31f1e3f 0xbd1ae7fffc63e3c7

def z903 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xbfdf30f83c1fffc7 0xf7fbe61f0783fff8

def z904 : W := mkw 0x0efd40003bd6c000 0x01dfa800077ad800 0xb7f800003fffe005 0xf6ff000007fffc00

def z905 : W := mkw 0x000541ad417b72db 0x6000a835a82f6e5b 0xd8ffffffc3fff1ff 0xfb1ffffff87ffe3f

def z906 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xfffffffffc1fffc7 0xffffffffff83fff8

def z907 : W := mkw 0x0effc052bbd6c000 0x01dff80a577ad800 0xffffd3ffffffe007 0xfffffa7ffffffc00

def z908 : W := mkw 0x25e2bf52b6a00db6 0x04bc57ea56d401b6 0xffe7ffffffe01ffe 0xfffcfffffffc03ff

def z909 : W := mkw 0x17bafb5acc64e9d6 0xa2f75f6b598c9d3a 0x1728d318dce0e1c0 0x42e51a631b9c1c38

def z910 : W := mkw 0x07baba5288048000 0x00f7574a51009000 0xeffffffffc070003 0xfdffffffff80e000

def z911 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0xd02cd39cc3e0f1ff 0xda059a73987c1e3f

def z912 : W := mkw 0x110030a80c0dbb45 0x822006150181b768 0xb71030e03c1fffc7 0x76e2061c0783fff8

def z913 : W := mkw 0x0ebac00018c4c000 0x01d7580003189800 0x3728c0003cffe004 0x46e51800079ffc00

def z914 : W := mkw 0x004544ad635b7669 0x6008a895ac6b6ecd 0xf8ffecffe3fffe3f 0xff1ffd9ffc7fffc7

def z915 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xffffffffffe01fff 0xfffffffffffc03ff

def z916 : W := mkw 0x05a2ba5280000000 0x00b4574a50000000 0xcfe7ffffc0000002 0xf9fcfffff8000000

def z917 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffc0003ffff03f 0xfffff80007fffe07

def z918 : W := mkw 0x004104a5220b1629 0x40082094a44162c5 0xe8d32ce7201f1e3f 0x3d1a659ce403e3c7

def z919 : W := mkw 0x07baba5284000904 0x00f7574a50800120 0xeffffffffc000e03 0xfdffffffff8001c0

def z920 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8f7efe7e31f1e3f 0xbd1efdfcfc63e3c7

def z921 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x68d72ce723071e3a 0xad1ae59ce460e3c7

def z922 : W := mkw 0x0045042523130629 0x4008a084a46260c5 0x28d32c6323070e38 0x251a658c6460e1c7

def z923 : W := mkw 0x121d40fd495ff249 0xe243a81fa92bfe49 0x081fc0ffc01fe001 0x0103f81ff803fc00

def z924 : W := mkw 0x084544a533db5629 0x4108a894a67b6ac5 0xe8d72ce723ff1e3f 0xbd1ae59ce47fe3c7

def z925 : W := mkw 0x031830a00c0d9b05 0x006306140181b360 0xb71830e03c1fffc7 0x76e3061c0783fff8

def z926 : W := mkw 0x0041042122030621 0x40082084244060c4 0x68d32c6320071e3a 0x2d1a658c6400e3c7

def z927 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbff300003fffe004 0xf7fe600007fffc00

def z928 : W := mkw 0x25e2bf02b6a00db6 0x04bc57e056d401b6 0xf7e0ff00ffe01ffe 0xfefc1fe01ffc03ff

def z929 : W := mkw 0x110030a80c0dbb45 0x822006150181b768 0x370020003c1fffc4 0x26e004000783fff8

def z930 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb71020e03c1fffc7 0x36e2041c0783fff8

def z931 : W := mkw 0x131abafa8c0dbb45 0x8263575f5181b768 0xff1ffffffc1fffc7 0x7fe3ffffff83fff8

def z932 : W := mkw 0x010030a804093b45 0x0020061500812768 0xb71830f83c1fffc7 0x76e3061f0783fff8

def z933 : W := mkw 0x0effc052bbd6c000 0x01dff80a577ad800 0xbfffc0633fffe005 0xf7fff80c67fffc00

def z934 : W := mkw 0x2ce7cf0473f244ba 0x259cf9e08e7e4897 0x48e7cf04c3e00038 0x891cf9e0987c0007

def z935 : W := mkw 0x1de7f0f837db7b45 0x83bcfe1f06fb6f68 0x08e7f0f803e01fc2 0x811cfe1f007c03f8

def z936 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xcfffffffc300103f 0xf9fffffff8600207

def z937 : W := mkw 0x110035fd44293fff 0xe22006bfa88527ff 0x40003fffc0001ffa 0x080007fff80003ff

def z938 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xefffffffe0001e07 0xfdfffffffc0003c0

def z939 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0x5028d318c3e0e1f8 0xca051a63187c1c3f

def z940 : W := mkw 0x121ec0fec95df249 0xa243d81fd92bbe49 0x081fc0ffc01fe001 0x0103f81ff803fc00

def z941 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xb738c0003fffe005 0x76e7180007fffc00

def z942 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3ffbc0003fffe004 0x67ff780007fffc00

def z943 : W := mkw 0x121800a80c0dbb45 0x824300150181b768 0xb71810983c1fffc7 0x76e302130783fff8

def z944 : W := mkw 0x0004410c417060da 0x20008821882e0c1b 0xd02cd31cc3f8e1fd 0xda059a63987f1c3f

def z945 : W := mkw 0x21003f0004200db6 0x042007e0008401b6 0xf7203f003fe01ffe 0xfee407e007fc03ff

def z946 : W := mkw 0x0045042523130629 0x4008a084a46260c5 0xe8d72c6723071e3e 0xbd1ae58ce460e3c7

def z947 : W := mkw 0x0041042122030621 0x40082084244060c4 0x28d32c6323071e3c 0x251a658c6460e3c7

def z948 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xf02cf39ce3f8ffff 0xfe059e739c7f1fff

def z949 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e43f843fe01fff 0xfefc87f087fc03ff

def z950 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x402cd39cc3f8f1fb 0x88059a73987f1e3f

def z951 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e8ff18ffe01ffe 0xfefd1fe31ffc03ff

def z952 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x77c03f003fe01ffe 0x2ef807e007fc03ff

def z953 : W := mkw 0x0045042123130621 0x4008a084246260c4 0xe8d72c63231f1e3f 0xbd1ae58c6463e3c7

def z954 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x48ffffffc0000003 0x891ffffff8000000

def z955 : W := mkw 0x04e0050032a004b2 0x009c00a006540096 0xf7e03f003fe01ffe 0xfefc07e007fc03ff

def z956 : W := mkw 0x31003ffc44293fff 0xa62007ff888527ff 0x40003ffcc0001ffa 0x080007ff980003ff

def z957 : W := mkw 0x121800a80c0dbb45 0x824300150181b768 0x370800003c1fffc4 0x46e100000783fff8

def z958 : W := mkw 0x04e5400033d24000 0x009ca800067a4800 0xbfffc0003fffe005 0xf7fff80007fffc00

def z959 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffc0e73fffe005 0xf7fff81ce7fffc00

def z960 : W := mkw 0x0effc0503bd6c000 0x01dff80a077ad800 0xbfffc0f83fffe005 0xf7fff81f07fffc00

def z961 : W := mkw 0x06ba8a5280000000 0x00d7514a50000000 0xcfffcfffc0000001 0xf9fff9fff8000000

def z962 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x502cd31cc3f8f1fc 0xca059a63987f1e3f

def z963 : W := mkw 0x0004410c417060da 0x20008821882e0c1b 0x1028d318c3e0e1f8 0x42051a63187c1c3f

def z964 : W := mkw 0x00004108406060d2 0x20000821080c0c1a 0x1028d318c3e0f1fc 0x42051a63187c1e3f

def z965 : W := mkw 0x04a28a5280000000 0x0094514a50000000 0x48e7cfffc0000000 0x891cf9fff8000000

def z966 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x37e03f003fe01ffc 0x66fc07e007fc03ff

def z967 : W := mkw 0x05e0340036800d24 0x00bc068006d001a4 0xf7e03c003fe01ffe 0xfefc078007fc03ff

def z968 : W := mkw 0x0a1fc0ad495ff249 0x6143f815a92bfe49 0x081fc0ffc01fe001 0x0103f81ff803fc00

def z969 : W := mkw 0x131ab0fa8c0dbb45 0x8263561f5181b768 0xbf1b30fb3c1fffc7 0x77e3661f6783fff8

def z970 : W := mkw 0x0effc4003bd6c420 0x01dff880077ad884 0xffffcc003fffe03d 0xfffff98007fffc07

def z971 : W := mkw 0x0effc0043bd6c008 0x01dff800877ad801 0xffffc0043fffe03d 0xfffff80087fffc07

def z972 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8df3cff231f1e3f 0xfd1be79fe463e3c7

def z973 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4fdfffffc0000003 0x29fbfffff8000000

def z974 : W := mkw 0x25e2bf02b6a00db6 0x04bc57e056d401b6 0xffe33f033fe01ffe 0xfffc67e067fc03ff

def z975 : W := mkw 0x00000188002830d2 0x000000310005061a 0xd02cd39cc3f8f1ff 0xda059a73987f1e3f

def z976 : W := mkw 0x000541ad417b72db 0x6000a835a82f6e5b 0xf83ff3ffe3ffffff 0xff07fe7ffc7fffff

def z977 : W := mkw 0x000441ac417972db 0x20008835882f2e5b 0xf02cd39ce3ffffff 0xde059a739c7fffff

def z978 : W := mkw 0x06bec0000954c000 0x00d7d800012a9800 0xbfffc0003fffe005 0xf7fff80007fffc00

def z979 : W := mkw 0x25a03b0014a00996 0x04b4076002940132 0xf72033003fe01ffe 0xfee4066007fc03ff

def z980 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xe8ffece7231f1e3f 0xfd1ffd9ce463e3c7

def z981 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3ff7c0003fffe004 0xa7fef80007fffc00

def z982 : W := mkw 0x131ab0fa8c0dbb45 0x8263561f5181b768 0xffdffcfffc1fffc7 0xfffbff9fff83fff8

def z983 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x371830f83c1fefc1 0x66e3061f0783fdf8

def z984 : W := mkw 0x0ce7c50573f244ba 0x619cf8a0ae7e4897 0x48e7cf07c3e00038 0x891cf9e0f87c0007

def z985 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffcc073fffe005 0xfffff980e7fffc00

def z986 : W := mkw 0x2ce54f0033f244b2 0x059ca9e0067e4896 0x40e00f0003e00038 0x881c01e0007c0007

def z987 : W := mkw 0x110031fc44293bdf 0xa220063f8885277b 0x000030f800001ffa 0x0000061f000003ff

def z988 : W := mkw 0x004504ad231b3669 0x4008a095a46366cd 0xe8df2cff231ffe3f 0xbd1be59fe463ffc7

def z989 : W := mkw 0x0effc0047bd6c008 0x21dff8008f7ad801 0xbfffc004ffffe005 0xf7fff8009ffffc00

def z990 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x57e03f001fe01ffa 0xcafc07e003fc03ff

def z991 : W := mkw 0x0041042522030629 0x40082084a44060c5 0x68d32c6720070e38 0x2d1a658ce400e1c7

def z992 : W := mkw 0x0effc052bbd6c000 0x01dff80a577ad800 0xffffecffffffe007 0xfffffd9ffffffc00

def z993 : W := mkw 0x000004a500091629 0x40000094a00122c5 0xe8d72ce7201f1e3f 0xbd1ae59ce403e3c7

def z994 : W := mkw 0x100000a80c0dbb45 0x820000150181b768 0xb70000003c1fffc4 0x76e000000783fff8

def z995 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xf8df2ce7231ffe3f 0xff1be59ce463ffc7

def z996 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd028d318c3f8f1fe 0xda051a63187f1e3f

def z997 : W := mkw 0x000441ac417972db 0x20008835882f2e5b 0xd02cf3fcc3f8ffff 0xda059e7f987f1fff

def z998 : W := mkw 0x0effca52bbd6c000 0x01dff94a577ad800 0xffffcfffffffe005 0xfffff9fffffffc00

def z999 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffd3003fffe007 0xfffffa6007fffc00

def z1000 : W := mkw 0x0efb80003a868000 0x01df70000750d000 0xbffb00003fffe005 0xf7ff600007fffc00

def z1001 : W := mkw 0x0ce540003bd6c000 0x019ca800077ad800 0xb7ecc0003fffe005 0xf6fd980007fffc00

def z1002 : W := mkw 0x0effca02bbd6c000 0x01dff940577ad800 0xffffefe7ffffe007 0xfffffdfcfffffc00

def z1003 : W := mkw 0x13183afa8c0dbb45 0x8263075f5181b768 0xb7183cfb3c1fffc7 0x76e3079f6783fff8

def z1004 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7f03fe03fe01fff 0xfefe07fc07fc03ff

def z1005 : W := mkw 0x000441ac417972db 0x20008835882f2e5b 0xf8ffffffe3ffffff 0xff1ffffffc7fffff

def z1006 : W := mkw 0x0004410c417060da 0x20008821882e0c1b 0xd02cd39cc3e0e1fb 0xda059a73987c1c3f

def z1007 : W := mkw 0x2ffbbe52be868d24 0x05ff77ca57d0d1a4 0x2fd32c633c070e00 0x25fa658c6780e1c0

def z1008 : W := mkw 0x004504a5339b1629 0x4008a094a67362c5 0xf8d72ce73fff1e3f 0xbf1ae59ce7ffe3c7

def z1009 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x77e01f003fe01ffc 0xcefc03e007fc03ff

def z1010 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd83fd3ffc3f8f1ff 0xdb07fa7ff87f1e3f

def z1011 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xf8f72ce723ff1e3f 0xff1ee59ce47fe3c7

def z1012 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xbf1f30ff3c1fffc7 0x77e3e61fe783fff8

def z1013 : W := mkw 0x031aba5280000000 0x0063574a50000000 0xc8dfffffc0000003 0xb91bfffff8000000

def z1014 : W := mkw 0x27baba5294800904 0x04f7574a52900120 0xcfffffffdc000003 0xf9fffffffb800000

def z1015 : W := mkw 0x25e13f0036a20db6 0x04bc27e006d441b6 0xfff33f003fe71ffe 0xfffe67e007fce3ff

def z1016 : W := mkw 0x25e2bf02b6a00db6 0x04bc57e056d401b6 0xffefff9fffe01fff 0xfffdfff3fffc03ff

def z1017 : W := mkw 0x0ebac00018c4c000 0x01d7580003189800 0x1738c0001cffe001 0x42e71800039ffc00

def z1018 : W := mkw 0x25e13f0136a20db6 0x44bc27e026d441b6 0xffe33f033fe01ffe 0xfffc67e067fc03ff

def z1019 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffc304ffffe005 0xfffff8609ffffc00

def z1020 : W := mkw 0x110031f804293bd7 0x8220063f0085277a 0x400033f800001ffa 0x0800067f000003ff

def z1021 : W := mkw 0x25e03f52b6a00db6 0x04bc07ea56d401b6 0xfff73fffffe01fff 0xfffee7fffffc03ff

def z1022 : W := mkw 0x0ce7c0003bd6c000 0x019cf800077ad800 0xbfe7c0003fffe004 0xf7fcf80007fffc00

def z1023 : W := mkw 0x084545ad7bfff6fb 0x6108a8b5af7ffedf 0x300000003ffffffc 0x0600000007ffffff

def z1024 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7f03f003fff1fff 0xfefe07e007ffe3ff

def z1025 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffd318ffffe005 0xf7fffa631ffffc00

def z1026 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0xdfffffffc018e007 0xfbfffffff8031c00

def z1027 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xd02cffffc3f8f1ff 0xda059ffff87f1e3f

def z1028 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x77203f003fe01ffe 0x4ee407e007fc03ff

def z1029 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf7d83cf83c1fffc7 0xfefb079f0783fff8

def z1030 : W := mkw 0x0a5d40003bd6c000 0x014ba800077ad800 0xbfdf00003fffe005 0xf7fbe00007fffc00

def z1031 : W := mkw 0x31003bf804293bd7 0x8620077f0085277a 0x000033f800001fc2 0x0000067f000003f8

def z1032 : W := mkw 0x0045042523130629 0x4008a084a46260c5 0xe8d72c67231f0e3d 0xbd1ae58ce463e1c7

def z1033 : W := mkw 0x11003bfec4293bdf 0xa220077fd885277b 0x40003fffc0001ffa 0x080007fff80003ff

def z1034 : W := mkw 0x06fc40003bd4c000 0x00df8800077a9800 0xb7fcc0003fffe005 0xf6ff980007fffc00

def z1035 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7e4ff04ffe01ffe 0xfefc9fe09ffc03ff

def z1036 : W := mkw 0x004104a5220b1629 0x40082094a44162c5 0xe8d72ce720071e3b 0xbd1ae59ce400e3c7

def z1037 : W := mkw 0x131830fd0c0dbb4d 0xc263061fa181b769 0xb71830ff3c1fffc7 0x76e3061fe783fff8

def z1038 : W := mkw 0x031830880c0cb944 0x0063061101819728 0xb71830983c1fffc7 0x76e306130783fff8

def z1039 : W := mkw 0x0a1fc0000956c000 0x0143f800012ad800 0xbf3fc0003fffe005 0xf7e7f80007fffc00

def z1040 : W := mkw 0x2140350036a00db6 0x042806a006d401b6 0xf7c03c003fe01ffe 0xfef8078007fc03ff

def z1041 : W := mkw 0x110031f844293bd7 0xa220063f0885277a 0x000033f8c0001fc2 0x0000067f180003f8

def z1042 : W := mkw 0x0effc4053bd6c428 0x41dff880a77ad885 0xbfffc0003fffe03d 0xf7fff80007fffc07

def z1043 : W := mkw 0x0ebfc00019d6c000 0x01d7f800033ad800 0x9fffc0001cffe001 0xf3fff800039ffc00

def z1044 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x1fffc0001fffe001 0xc3fff80003fffc00

def z1045 : W := mkw 0x131830580c04a944 0x8263060b01809528 0xb71830183c1fffc7 0x76e306030783fff8

def z1046 : W := mkw 0x0a5d40003bd6c000 0x014ba800077ad800 0x370800003fffe004 0x46e1000007fffc00

def z1047 : W := mkw 0x24e0050036a00db6 0x049c00a006d401b6 0xf7e013003fe01ffe 0xfefc026007fc03ff

def z1048 : W := mkw 0x07baba5284000904 0x00f7574a50800120 0xdfffffffdc0001c3 0xfbfffffffb800038

def z1049 : W := mkw 0x004544ad235b7669 0x4008a895a46b6ecd 0xf8fffcff23ffffff 0xff1fff9fe47fffff

def z1050 : W := mkw 0x004104a5220b1629 0x40082094a44162c5 0xe8d32ce723071e3e 0xbd1a659ce460e3c7

def z1051 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x371810f83c1fffc5 0x46e3021f0783fff8

def z1052 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0x370830f83c1fffc6 0x46e1061f0783fff8

def z1053 : W := mkw 0x021c40000954c000 0x00438800012a9800 0xb71800003fffe005 0x76e3000007fffc00

def z1054 : W := mkw 0x004504ad631b3669 0x6008a095ac6366cd 0xe8d72cffe31f1e3f 0xbd1ae59ffc63e3c7

def z1055 : W := mkw 0x004104a1220b1621 0x40082094244162c4 0xe8d32ce3231f1e3f 0xbd1a659c6463e3c7

def z1056 : W := mkw 0x121800f80c0dbb45 0x8243001f0181b768 0xb71800f83c1fffc5 0x76e3001f0783fff8

def z1057 : W := mkw 0x0effc4003bd6c420 0x01dff880077ad884 0xbfffec003fffee05 0xf7fffd8007fffdc0

def z1058 : W := mkw 0x0ebfc00019d6c000 0x01d7f800033ad800 0x1728c0001cffe000 0x42e51800039ffc00

def z1059 : W := mkw 0x131830700c058b05 0x8263060e0180b160 0xb71830603c1fffc7 0x76e3060c0783fff8

def z1060 : W := mkw 0x04e000003a848000 0x009c000007509000 0xb7e000003fffe004 0xf6fc000007fffc00

def z1061 : W := mkw 0x13183afa8c0dbb45 0x8263075f5181b768 0xb71833f8fc1fffc7 0x76e3067f1f83fff8

def z1062 : W := mkw 0x37fabe72be858f25 0x86ff57ce57d0b1e4 0x2fd32c633c070e00 0x25fa658c6780e1c0

def z1063 : W := mkw 0x0effc4013bd6c420 0x41dff880277ad884 0xbfffcc033fffe005 0xf7fff98067fffc00

def z1064 : W := mkw 0x25e03f52b6a00db6 0x04bc07ea56d401b6 0xf7e03f18ffe01ffe 0xfefc07e31ffc03ff

def z1065 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffe0e03fffe007 0xf7fffc1c07fffc00

def z1066 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0xf72cd39cfff8f1ff 0xfee59a739fff1e3f

def z1067 : W := mkw 0x25e0350036a00db6 0x04bc06a006d401b6 0xb7e030003fe01ffe 0xf6fc060007fc03ff

def z1068 : W := mkw 0x0effc4003bd6c420 0x01dff880077ad884 0xffffece73ffffe3f 0xfffffd9ce7ffffc7

def z1069 : W := mkw 0x0318305000000000 0x0063060a00000000 0xcfffffffc0000003 0xf9fffffff8000000

def z1070 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x68d32ce7231f1e3e 0x2d1a659ce463e3c7

def z1071 : W := mkw 0x05a2ba5280000000 0x00b4574a50000000 0xc8f7ffffc0000003 0xb91efffff8000000

def z1072 : W := mkw 0x24e0050036a00db6 0x049c00a006d401b6 0x37c000003fe01ffc 0x26f8000007fc03ff

def z1073 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x2fffc0003fffe001 0xa5fff80007fffc00

def z1074 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0x3f3fc0003fffe005 0x47e7f80007fffc00

def z1075 : W := mkw 0x0ebfc00019d6c000 0x01d7f800033ad800 0xbf3fc0003cffe005 0x77e7f800079ffc00

def z1076 : W := mkw 0x2140350036a00db6 0x042806a006d401b6 0x370010003fe01ffc 0x46e0020007fc03ff

def z1077 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xf7ecff003fe01fff 0xfefd9fe007fc03ff

def z1078 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0x77e02f003fe01ffc 0xaefc05e007fc03ff

def z1079 : W := mkw 0x0005418d417a70da 0x6000a831a82f4e1b 0xd82fd39fc3f8f1ff 0xdb05fa73f87f1e3f

def z1080 : W := mkw 0x004544a5235b5629 0x4008a894a46b6ac5 0xe8dfece7231ffe3f 0xbd1bfd9ce463ffc7

def z1081 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x902cd318c3f8f1fd 0xd2059a63187f1e3f

def z1082 : W := mkw 0x0effce07bbd6c428 0x41dff9c0f77ad885 0xffffcf07ffffe03d 0xfffff9e0fffffc07

def z1083 : W := mkw 0x06ba8a5280000000 0x00d7514a50000000 0xc8ffefffc0000003 0xb91ffdfff8000000

def z1084 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xb7c03c003fe01ffe 0x76f8078007fc03ff

def z1085 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0x28d72ce7231f1e3d 0x251ae59ce463e3c7

def z1086 : W := mkw 0x0efbc0003ac6c000 0x01df78000758d800 0xbffbc0003cffe005 0x77ff7800079ffc00

def z1087 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfdb00003fffe005 0x77fb600007fffc00

def z1088 : W := mkw 0x000441ad417972db 0x60008835a82f2e5b 0xd02cd3ffc3f8f1ff 0xda059a7ff87f1e3f

def z1089 : W := mkw 0x110030a80c0dbb45 0x822006150181b768 0x370010003c1fffc4 0x46e002000783fff8

def z1090 : W := mkw 0x131830a80c0dbb45 0x826306150181b768 0xb71830003c1fffc7 0x76e306000783fff8

def z1091 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xf71833fcfc1fffc7 0x7ee3067f9f83fff8

def z1092 : W := mkw 0x25e03f0036a00db6 0x04bc07e006d401b6 0xffe73f073fe01ffe 0xfffce7e0e7fc03ff

def z1093 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xffffec003fffe007 0xfffffd8007fffc00

def z1094 : W := mkw 0x110030f80c0dbb45 0x8220061f0181b768 0xb70030f83c1fffc6 0x76e0061f0783fff8

def z1095 : W := mkw 0x004544a5235b5629 0x4008a894a46b6ac5 0xe8f7ece723ff1e3f 0xbd1efd9ce47fe3c7

def z1096 : W := mkw 0x004504ad231b3669 0x4008a095a46366cd 0xe8d73cff231f1fff 0xbd1ae79fe463e3ff

def z1097 : W := mkw 0x2effce003bd6c420 0x05dff9c0077ad884 0xbfffcc003fffe005 0xf7fff98007fffc00

def z1098 : W := mkw 0x0effca003bd6c000 0x01dff940077ad800 0xffffcf003fffe005 0xfffff9e007fffc00

def z1099 : W := mkw 0x004544ad635b7669 0x6008a895ac6b6ecd 0xf8dffcffe31fffff 0xff1bff9ffc63ffff

def z1100 : W := mkw 0x07baba5280000000 0x00f7574a50000000 0x4ff7ffffc0000002 0xa9fefffff8000000

def z1101 : W := mkw 0x06ba8a5280000000 0x00d7514a50000000 0xc8ffdfffc0000003 0xd91ffbfff8000000

def z1102 : W := mkw 0x0004418c417870da 0x20008831882f0e1b 0x102cd39cc3f8f1fd 0x42059a73987f1e3f

def z1103 : W := mkw 0x0effc0003bd6c000 0x01dff800077ad800 0xbfffe0003ffffe07 0xf7fffc0007ffffc0

def z1104 : W := mkw 0x004504a5231b1629 0x4008a094a46362c5 0xf8d73ce7231f1fff 0xff1ae79ce463e3ff

def z1105 : W := mkw 0x2ce7cf0533f244ba 0x459cf9e0a67e4897 0x48e7cf0703e00038 0x891cf9e0e07c0007

def z1106 : W := mkw 0x131830780c05ab45 0x8263060f0180b568 0xb71830783c1fefc5 0x76e3060f0783fdf8

def z1107 : W := mkw 0x131830f80c0dbb45 0x8263061f0181b768 0xb71820603c1fffc5 0x76e3040c0783fff8

def z1108 : W := mkw 0x0045042523130629 0x4008a084a46260c5 0xe8d72ce723070e3b 0xbd1ae59ce460e1c7

def z1109 : W := mkw 0x004544ad635b7669 0x6008a895ac6b6ecd 0xe8d72ce7231ffe3f 0xbd1ae59ce463ffc7

def z1110 : W := mkw 0x0a18400018c4c000 0x0143080003189800 0xb71800003cffe005 0x76e30000079ffc00

def z1111 : W := mkw 0x31003fa804293ff7 0x862007f5008527fe 0x40003f0000001ffa 0x080007e0000003ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z9]),(0,[z10,z1,z3,z4,z5,z11,z6]),(0,[z1,z2,z12,z3,z4,z6,z13])],[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z15,z5,z6])],[(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z5,z17,z6]),(1,[z1,z18,z3,z4,z5,z19]),(0,[z20,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z22,z5,z6])],[],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z24,z6]),(0,[z1,z2,z25,z3,z26,z4,z6]),(0,[z1,z27,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z29,z30])],[(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z11,z6]),(0,[z1,z2,z3,z4,z5,z33,z6]),(0,[z1,z18,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z35,z5,z6])],[(1,[z1,z36,z3,z4,z5,z6]),(0,[z1,z2,z3,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z38,z6]),(0,[z1,z2,z39,z3,z4,z5,z6]),(0,[z1,z2,z40,z3,z4,z5,z6]),(1,[z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z1,z2,z43,z3,z4,z5,z6]),(0,[z1,z2,z3,z44,z5,z45,z6])],[(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z1,z47,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z48,z6]),(0,[z1,z2,z49,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z51,z6]),(0,[z1,z2,z3,z4,z5,z6,z52])],[(0,[z1,z2,z53,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z5,z6])],[(0,[z56,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z57,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z58,z5,z6]),(0,[z1,z2,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z60,z4,z5,z6]),(1,[z1,z2,z12,z3,z4,z6])],[(0,[z1,z61,z2,z3,z4,z5,z6]),(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z62]),(0,[z63,z1,z2,z25,z3,z4,z5]),(0,[z1,z2,z3,z44,z5,z64,z6])],[(0,[z1,z2,z3,z4,z5,z6,z65]),(0,[z63,z1,z2,z3,z4,z5,z66]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z69])],[(0,[z1,z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z22,z71,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z72]),(0,[z1,z73,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z74,z5,z6]),(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z6]),(1,[z1,z2,z3,z34,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z25,z78,z4,z5,z6]),(0,[z1,z2,z79,z3,z5,z6,z30])]],
   [[(0,[z1,z2,z3,z4,z80,z5,z6]),(0,[z81,z2,z82,z3,z4,z5,z6]),(0,[z1,z83,z2,z3,z4,z5,z6]),(0,[z1,z84,z2,z3,z4,z5,z6]),(0,[z1,z85,z3,z4,z86,z5,z6]),(0,[z1,z2,z87,z3,z88,z5,z6])],[(0,[z1,z2,z3,z4,z5,z89,z6]),(1,[z90,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z91,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z92]),(0,[z93,z81,z2,z3,z4,z5,z6]),(0,[z1,z2,z94,z3,z4,z5,z6]),(0,[z63,z1,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z1,z2,z3,z4,z97,z5,z6]),(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z99,z6]),(0,[z1,z2,z100,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z101,z5,z6]),(0,[z1,z2,z3,z4,z48,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z103,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z32,z6])],[(1,[z1,z2,z3,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z105]),(0,[z1,z2,z3,z106,z4,z5,z6])],[(0,[z1,z107,z3,z4,z71,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z5,z6])],[(0,[z1,z2,z3,z22,z109,z5,z6]),(1,[z1,z2,z110,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6])],[(0,[z1,z114,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z6])]],
   [[(0,[z1,z2,z3,z116,z4,z5,z6]),(0,[z1,z117,z2,z3,z4,z5,z6]),(0,[z1,z2,z118,z3,z4,z5,z119]),(1,[z1,z2,z120,z4,z5,z6])],[(0,[z121,z1,z36,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z122,z5,z6]),(0,[z1,z123,z2,z3,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z124]),(0,[z1,z2,z3,z4,z5,z125,z6]),(0,[z1,z2,z3,z4,z5,z126,z6])],[(0,[z127,z2,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z6]),(1,[z1,z47,z3,z4,z5,z124])],[(0,[z1,z2,z3,z4,z129,z5,z6]),(0,[z1,z2,z3,z4,z130,z5,z24])],[(0,[z1,z2,z3,z4,z131,z5,z6]),(0,[z1,z2,z3,z4,z132,z5,z6]),(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z5,z6])],[(0,[z1,z2,z135,z3,z4,z5,z6]),(1,[z1,z136,z3,z71,z5,z6]),(0,[z1,z2,z3,z4,z5,z124,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z138,z3,z4,z32,z6]),(0,[z1,z2,z3,z4,z5,z45,z6]),(0,[z1,z2,z3,z4,z5,z6,z139])],[(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z141,z5,z6]),(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z1,z2,z3,z4,z32,z86,z6]),(0,[z1,z2,z144,z3,z4,z5,z6])],[(0,[z1,z2,z3,z145,z4,z5,z6]),(0,[z1,z2,z146,z3,z4,z5,z76]),(0,[z8,z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z148,z6]),(0,[z1,z2,z3,z4,z5,z149,z6]),(0,[z1,z2,z3,z150,z4,z5,z6]),(0,[z151,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z118,z3,z5,z6]),(0,[z1,z2,z3,z5,z64,z6,z13])]],
   [[(0,[z152,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z87,z3,z4,z5,z148]),(0,[z1,z2,z153,z3,z4,z5,z119]),(0,[z1,z2,z21,z3,z4,z44,z6]),(0,[z1,z2,z154,z3,z4,z5,z6])],[(0,[z1,z2,z155,z107,z4,z5,z6]),(0,[z1,z136,z3,z4,z71,z5,z6]),(0,[z1,z2,z156,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z157,z6]),(0,[z158,z1,z2,z3,z4,z5,z6])],[(1,[z1,z159,z3,z4,z5,z6]),(0,[z160,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z161,z4,z5,z6]),(0,[z1,z2,z162,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z163,z5,z6]),(0,[z1,z2,z3,z4,z5,z164,z6]),(0,[z1,z165,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z64,z6])],[(0,[z1,z2,z3,z4,z5,z166,z6]),(0,[z1,z2,z3,z4,z5,z167,z6]),(0,[z1,z2,z3,z4,z130,z5,z168]),(0,[z1,z169,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z24,z6])],[(1,[z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z3,z171,z4,z5,z6]),(0,[z1,z2,z3,z4,z172,z5,z6]),(0,[z1,z2,z25,z3,z4,z5,z119])],[(0,[z1,z2,z3,z4,z5,z6,z173]),(0,[z1,z2,z174,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z175]),(0,[z1,z2,z176,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z177,z5,z6])],[(0,[z178,z1,z2,z107,z4,z5,z6]),(0,[z1,z2,z95,z3,z4,z5,z6]),(0,[z1,z2,z179,z3,z4,z5,z6]),(0,[z1,z2,z3,z180,z5,z6,z13]),(0,[z1,z18,z2,z3,z181,z5,z6])]],
   [[(0,[z1,z2,z118,z3,z4,z5,z168])],[(0,[z127,z93,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z182,z5,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z1,z2,z183,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z5,z6]),(1,[z184,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z185,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z187,z6]),(0,[z1,z2,z3,z22,z4,z5,z6]),(0,[z1,z2,z188,z3,z4,z5,z6])],[(0,[z189,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z25,z3,z4,z30])],[(0,[z1,z2,z3,z4,z5,z6,z190]),(0,[z1,z2,z191,z22,z4,z5,z6])],[(0,[z2,z3,z109,z4,z192,z5,z6]),(0,[z1,z2,z3,z4,z5,z168,z105]),(0,[z1,z193,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z194,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z195,z5]),(0,[z1,z196,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z197,z4,z5,z6]),(0,[z1,z2,z198,z3,z4,z5,z6]),(0,[z1,z2,z199,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z200,z6]),(0,[z201,z1,z2,z3,z4,z5,z6])],[(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z202,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z181,z5,z6]),(0,[z47,z204,z2,z3,z4,z5,z6]),(0,[z1,z2,z138,z87,z4,z5,z6])],[(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z206,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z207,z4,z5,z6]),(0,[z1,z2,z208,z3,z22,z5,z6])],[(0,[z1,z2,z3,z4,z192,z5,z6]),(0,[z1,z2,z209,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z26,z4,z32,z6]),(0,[z1,z2,z3,z211,z4,z5,z6])],[(0,[z81,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z170]),(0,[z213,z1,z2,z3,z71,z5,z6]),(0,[z1,z2,z3,z4,z130,z24,z6])],[(0,[z1,z214,z3,z215,z4,z5,z6]),(0,[z216,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z217,z3,z4,z5,z6]),(0,[z1,z2,z25,z3,z4,z5,z168]),(0,[z1,z2,z3,z4,z5,z6,z218])],[(0,[z1,z2,z3,z219,z4,z5,z6]),(0,[z63,z2,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z4,z5,z220,z6]),(0,[z10,z90,z2,z3,z4,z5,z6])],[(0,[z221,z1,z107,z3,z4,z5,z6]),(0,[z127,z1,z2,z3,z4,z5,z105]),(0,[z1,z2,z222,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z223,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z44,z5,z6]),(0,[z1,z2,z3,z4,z224,z5,z6])],[(0,[z93,z1,z214,z3,z4,z5,z6]),(0,[z1,z2,z225,z3,z4,z5,z6]),(0,[z184,z2,z3,z4,z5,z76,z6]),(0,[z1,z2,z3,z4,z226,z5,z6]),(0,[z227,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z155,z3,z4,z5,z6]),(0,[z1,z228,z2,z3,z4,z5,z6]),(0,[z1,z229,z2,z3,z4,z5,z6]),(0,[z1,z2,z230,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6])],[(0,[z121,z2,z3,z37,z4,z5,z6]),(0,[z1,z2,z208,z3,z58,z5,z6]),(0,[z1,z2,z118,z3,z4,z5,z13]),(0,[z1,z2,z232,z3,z4,z5,z6])],[(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z234,z2,z3,z4,z5,z6])],[(1,[z235,z2,z3,z4,z5,z6]),(0,[z1,z47,z3,z4,z5,z124,z6])],[(0,[z1,z2,z3,z4,z5,z19,z119]),(0,[z1,z236,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z237,z5,z6]),(0,[z1,z2,z82,z3,z4,z5,z6]),(0,[z1,z2,z3,z238,z4,z5,z6]),(0,[z239,z1,z2,z3,z4,z5,z6]),(1,[z1,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z240,z6]),(0,[z1,z2,z3,z4,z5,z241,z6]),(0,[z1,z242,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z243,z4,z5,z6])]],
   [[(0,[z178,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z244,z3,z4,z5,z6]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z246,z3,z4,z5,z6]),(0,[z1,z2,z25,z3,z4,z247,z6]),(0,[z1,z2,z248,z87,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z248,z3,z250,z5,z6]),(0,[z1,z2,z3,z26,z4,z44,z6])],[(0,[z1,z2,z4,z5,z247,z6,z119]),(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z251,z5,z6])],[(0,[z1,z2,z3,z58,z5,z64,z6]),(0,[z1,z2,z3,z4,z5,z6,z252])],[(0,[z1,z2,z3,z4,z253,z5,z6]),(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z1,z2,z255,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z1,z2,z3,z26,z4,z45,z6]),(1,[z1,z2,z3,z26,z44,z6])],[(0,[z1,z2,z3,z4,z5,z257,z6]),(0,[z1,z2,z3,z4,z5,z258,z6]),(0,[z239,z2,z3,z4,z202,z5,z6]),(0,[z1,z2,z3,z4,z5,z259,z6]),(0,[z1,z2,z260,z3,z4,z5,z6])],[(0,[z1,z2,z261,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z262,z6]),(1,[z1,z2,z3,z250,z5,z6]),(0,[z1,z2,z3,z4,z263,z5,z6])],[(0,[z1,z2,z3,z264,z4,z5,z6]),(0,[z1,z265,z2,z3,z4,z5,z6])],[(0,[z266,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z184,z239,z2,z3,z4,z5,z6]),(0,[z1,z2,z267,z3,z4,z5,z6])],[(0,[z268,z1,z2,z3,z4,z5,z6]),(0,[z213,z1,z136,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z269]),(0,[z1,z270,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z271])],[(0,[z1,z2,z3,z272,z5,z76,z6]),(0,[z1,z2,z21,z3,z71,z5,z6]),(0,[z1,z2,z87,z3,z4,z247,z6])],[(0,[z273,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z274,z6]),(0,[z1,z2,z3,z4,z5,z168,z124]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z191,z87,z4,z5,z6]),(0,[z1,z2,z3,z276,z4,z5,z6])],[(0,[z1,z214,z3,z4,z71,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z208,z58,z5,z6]),(0,[z1,z2,z3,z4,z5,z278,z6])],[(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z280]),(0,[z1,z2,z3,z281,z4,z5,z6])],[(0,[z127,z63,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z282]),(0,[z1,z47,z2,z3,z4,z5,z19])]],
   [[(0,[z1,z2,z3,z4,z76,z247,z6]),(0,[z1,z2,z3,z71,z58,z5,z6]),(0,[z283,z1,z2,z3,z4,z5,z6])],[(0,[z2,z107,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z284,z4,z5,z6]),(0,[z1,z285,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z76,z6]),(0,[z213,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z286,z5,z6]),(0,[z1,z287,z2,z3,z4,z5,z6]),(0,[z1,z288,z2,z3,z4,z5,z6]),(0,[z1,z2,z289,z3,z4,z5,z6]),(0,[z1,z2,z87,z4,z32,z5,z6])],[(0,[z1,z193,z107,z3,z4,z5,z6]),(0,[z93,z2,z3,z4,z5,z66,z6]),(1,[z1,z2,z3,z4,z5,z290]),(0,[z1,z2,z3,z291,z4,z5,z6])],[(0,[z1,z136,z2,z3,z71,z5,z6]),(0,[z1,z292,z2,z3,z4,z5,z6]),(1,[z1,z2,z191,z22,z5,z6])],[(0,[z81,z2,z107,z3,z4,z5,z6]),(0,[z1,z2,z293,z3,z4,z5,z6]),(0,[z1,z2,z294,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z295,z5,z6]),(0,[z1,z2,z3,z4,z296,z5,z6])],[(0,[z1,z2,z3,z4,z297,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z298])],[(0,[z1,z85,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z195,z5,z76]),(0,[z1,z2,z299,z3,z4,z5,z6]),(0,[z1,z2,z3,z300,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z301,z6]),(0,[z1,z2,z3,z4,z5,z124,z119]),(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z303,z6]),(0,[z1,z2,z118,z3,z4,z5,z64])]],
   [[(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z305,z6]),(0,[z1,z2,z3,z4,z5,z6,z306]),(0,[z1,z2,z3,z307,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z9]),(0,[z10,z1,z85,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z308,z6])],[(0,[z213,z1,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z309]),(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z1,z2,z311,z3,z4,z5,z6]),(1,[z1,z2,z153,z4,z5,z119])],[(0,[z1,z2,z3,z4,z312,z5,z6]),(0,[z1,z2,z3,z313,z4,z5,z6])],[(0,[z1,z2,z3,z314,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z315,z6]),(0,[z1,z2,z3,z4,z316,z5,z6]),(0,[z1,z2,z317,z3,z4,z5,z6]),(0,[z1,z2,z87,z3,z4,z5,z318]),(0,[z319,z1,z2,z3,z4,z5,z6])],[(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z2,z3,z322,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z1,z2,z3,z324,z4,z5,z6]),(0,[z1,z2,z3,z71,z44,z5,z6]),(1,[z1,z2,z3,z88,z5,z6]),(0,[z1,z2,z325,z3,z4,z5,z6]),(0,[z1,z2,z248,z153,z4,z5,z6])],[(0,[z121,z1,z2,z3,z4,z48,z6]),(0,[z1,z2,z3,z4,z272,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z6]),(0,[z1,z235,z2,z3,z4,z5,z6])],[(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z328,z1,z2,z3,z192,z5,z6]),(0,[z1,z2,z3,z329,z4,z5,z6]),(0,[z330,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z1,z332,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z333]),(1,[z1,z2,z3,z4,z334,z6])]],
   [[(1,[z1,z2,z155,z4,z5,z6]),(0,[z1,z2,z335,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z336]),(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z1,z2,z248,z3,z4,z338,z6]),(0,[z1,z2,z3,z120,z4,z5,z6])],[(1,[z328,z2,z3,z109,z5,z6]),(1,[z8,z1,z215,z4,z5,z6]),(0,[z1,z2,z3,z339,z4,z5,z6]),(0,[z1,z2,z248,z4,z5,z168,z6]),(0,[z1,z2,z340,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z30])],[(0,[z1,z214,z193,z3,z4,z5,z6]),(0,[z1,z193,z147,z3,z4,z5,z6]),(0,[z10,z235,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z341]),(0,[z1,z2,z3,z342,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z343,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z344,z6])],[(0,[z1,z2,z3,z4,z5,z345,z6]),(0,[z8,z1,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z22,z180,z5,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z1,z2,z347,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z130,z5,z30])],[(1,[z1,z53,z3,z4,z5,z6]),(0,[z1,z2,z3,z348,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z349]),(1,[z1,z2,z3,z4,z338,z6])],[(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z22,z192,z5,z6]),(0,[z8,z1,z2,z3,z4,z55,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z208,z4,z58,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z352]),(0,[z1,z353,z2,z3,z4,z5,z6]),(1,[z1,z2,z78,z4,z5,z6])],[(1,[z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z355,z6]),(0,[z1,z2,z3,z4,z202,z5,z6]),(0,[z127,z2,z3,z4,z5,z6,z105]),(1,[z1,z2,z3,z4,z356,z6]),(0,[z1,z2,z3,z4,z5,z6,z357]),(0,[z1,z2,z21,z358,z4,z5,z6]),(0,[z359,z1,z2,z3,z4,z5,z6])],[(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z361,z1,z2,z3,z192,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z362]),(0,[z1,z2,z3,z4,z363,z5,z6]),(0,[z1,z364,z2,z3,z4,z5,z6])],[(0,[z93,z214,z2,z3,z4,z5,z6]),(0,[z121,z1,z2,z3,z104,z5,z6]),(0,[z1,z2,z365,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z366,z6]),(0,[z1,z367,z2,z3,z4,z5,z6]),(0,[z1,z2,z191,z3,z22,z5,z6]),(0,[z1,z2,z3,z4,z5,z368,z6])],[(0,[z8,z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z369,z4,z5,z6]),(0,[z1,z2,z3,z4,z370,z5,z6]),(1,[z1,z85,z3,z4,z86,z6]),(0,[z1,z2,z3,z371,z4,z5,z6]),(0,[z1,z2,z372,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z373,z6]),(0,[z1,z2,z3,z374,z4,z5,z6])],[(0,[z1,z2,z22,z4,z58,z5,z6]),(0,[z1,z2,z375,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z26,z5,z6])],[(0,[z1,z2,z3,z376,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z377,z6]),(0,[z81,z1,z2,z37,z4,z5,z6]),(1,[z1,z378,z3,z4,z5,z6]),(0,[z184,z1,z53,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z148])],[(0,[z1,z2,z3,z4,z5,z6,z379])],[(0,[z1,z2,z3,z4,z5,z380,z6]),(0,[z1,z2,z25,z3,z4,z5,z24])]],
   [[(0,[z1,z136,z2,z3,z4,z5,z6]),(1,[z213,z1,z3,z180,z5,z6]),(0,[z1,z2,z381,z3,z4,z5,z6]),(0,[z1,z2,z3,z382,z4,z5,z6]),(0,[z383,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z384]),(0,[z1,z2,z3,z4,z5,z385,z6])],[(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z85,z2,z3,z370,z5,z6]),(0,[z1,z2,z138,z3,z4,z5,z6]),(1,[z1,z2,z138,z4,z247,z6])],[(0,[z387,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z388])],[(0,[z1,z2,z191,z3,z58,z5,z6]),(0,[z1,z2,z153,z3,z4,z5,z168]),(0,[z1,z2,z3,z4,z389,z5,z6])],[(0,[z1,z2,z3,z4,z5,z390,z6]),(0,[z1,z2,z391,z3,z4,z5,z6]),(0,[z63,z1,z392,z3,z4,z5,z6]),(0,[z1,z204,z2,z3,z4,z5,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z394,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z395,z6]),(0,[z1,z396,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z397,z5,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z399,z6]),(0,[z1,z2,z3,z400,z4,z5,z6])],[(0,[z121,z1,z193,z2,z4,z5,z6]),(0,[z1,z401,z2,z3,z4,z5,z6]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z403,z5,z6])],[(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z1,z2,z3,z4,z405,z5,z6]),(0,[z406,z47,z2,z3,z4,z5,z6]),(0,[z1,z2,z118,z3,z407,z5,z6])]],
   [[(0,[z1,z2,z3,z408,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z409,z6])],[(0,[z1,z2,z410,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z6]),(0,[z1,z2,z411,z3,z4,z5,z6]),(0,[z1,z2,z118,z3,z22,z5,z6])],[(0,[z1,z2,z3,z407,z71,z5,z6]),(0,[z412,z1,z2,z3,z4,z5,z6])],[(1,[z1,z413,z3,z4,z5,z6]),(0,[z1,z2,z3,z414,z4,z5,z6]),(0,[z1,z18,z2,z3,z4,z5,z6])],[(0,[z415,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z416]),(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z1,z418,z2,z3,z4,z5,z6]),(0,[z1,z2,z419,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z420,z6]),(0,[z1,z2,z3,z4,z5,z6,z421])],[(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z1,z2,z3,z4,z423,z5,z6]),(0,[z1,z2,z3,z4,z11,z247,z6]),(0,[z1,z2,z424,z3,z4,z5,z6]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z1,z2,z426,z3,z4,z5,z6]),(0,[z1,z2,z358,z3,z4,z5,z6]),(0,[z1,z2,z25,z120,z4,z5,z6])],[(0,[z1,z2,z427,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z428,z6]),(0,[z1,z2,z3,z4,z86,z5,z6]),(0,[z1,z2,z3,z4,z429,z5,z6])]],
   [[(0,[z430,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z431,z5,z6]),(0,[z1,z2,z432,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z11,z6]),(0,[z1,z18,z2,z3,z4,z5,z19]),(0,[z1,z2,z248,z3,z4,z5,z6])],[(0,[z81,z1,z2,z82,z4,z5,z6]),(0,[z127,z1,z2,z3,z4,z130,z5]),(0,[z2,z3,z4,z5,z66,z6,z105]),(0,[z1,z2,z3,z4,z5,z433,z6]),(0,[z1,z2,z3,z4,z5,z6,z434]),(0,[z1,z2,z3,z4,z435,z5,z6]),(0,[z1,z2,z3,z4,z436,z5,z6]),(0,[z1,z2,z437,z3,z4,z5,z6])],[(0,[z1,z2,z438,z3,z4,z5,z6]),(0,[z1,z2,z439,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z118,z3,z58,z5,z6]),(0,[z1,z2,z87,z3,z185,z5,z6])],[(0,[z1,z18,z214,z3,z4,z5,z6]),(0,[z8,z1,z3,z215,z4,z5,z6]),(0,[z1,z2,z3,z440,z4,z5,z6]),(0,[z1,z2,z3,z441,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z24,z6]),(0,[z442,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z29])],[(1,[z178,z1,z2,z4,z5,z6]),(0,[z1,z2,z443,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z444,z6]),(0,[z1,z2,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z4,z5,z338,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z105,z119]),(0,[z1,z2,z3,z58,z44,z5,z6]),(0,[z447,z1,z2,z3,z4,z5,z6])],[(0,[z10,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z448,z4,z5,z6]),(1,[z1,z2,z358,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z449,z6]),(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z1,z2,z3,z26,z4,z5,z6])]],
   [[(0,[z1,z2,z450,z3,z4,z5,z6]),(0,[z1,z3,z4,z86,z5,z11,z6])],[(0,[z1,z451,z2,z3,z4,z5,z6]),(0,[z452,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z334,z5,z6])],[(0,[z1,z2,z3,z4,z32,z202,z6]),(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z454,z1,z2,z3,z4,z5,z6]),(0,[z455,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z456]),(0,[z1,z2,z457,z3,z4,z5,z6])],[(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z202,z5,z76,z6]),(0,[z1,z2,z459,z3,z4,z5,z6]),(0,[z1,z2,z78,z3,z4,z5,z6])],[(0,[z460,z1,z2,z3,z4,z5,z6]),(0,[z1,z392,z2,z3,z4,z5,z6]),(1,[z1,z2,z248,z4,z5,z168]),(0,[z1,z2,z21,z3,z5,z45,z6]),(0,[z1,z461,z2,z3,z4,z5,z6]),(0,[z462,z1,z2,z3,z4,z5,z6])],[(0,[z1,z214,z85,z3,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z463,z4,z5,z6]),(0,[z1,z2,z3,z464,z4,z5,z6]),(0,[z1,z2,z3,z4,z465,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z466])],[(0,[z1,z2,z467,z3,z4,z5,z6]),(1,[z1,z2,z3,z468,z5,z6])],[(0,[z1,z214,z3,z4,z5,z124,z6]),(0,[z1,z2,z191,z3,z4,z262,z6]),(0,[z1,z2,z3,z4,z5,z469,z6]),(0,[z1,z2,z118,z3,z44,z5,z6])]],
   [[(0,[z470,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z471,z6]),(0,[z1,z2,z472,z3,z4,z5,z6]),(0,[z473,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z195,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z388]),(0,[z1,z2,z3,z4,z6,z388,z13])],[(0,[z1,z2,z3,z4,z5,z6,z474]),(0,[z328,z1,z2,z3,z44,z5,z6]),(0,[z1,z2,z21,z3,z5,z64,z6])],[(0,[z1,z2,z147,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z475,z5,z6])],[(0,[z1,z2,z476,z3,z4,z5,z6]),(1,[z1,z225,z3,z4,z5,z6]),(1,[z1,z2,z146,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z63,z1,z2,z3,z4,z5,z105]),(0,[z1,z2,z477,z3,z4,z5,z6])],[(0,[z1,z2,z478,z3,z4,z5,z6]),(1,[z204,z2,z3,z4,z5,z6]),(0,[z1,z479,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z480,z5,z6]),(0,[z1,z2,z208,z3,z4,z5,z6]),(0,[z1,z2,z481,z3,z4,z5,z6]),(0,[z1,z2,z25,z3,z4,z32,z6]),(0,[z1,z2,z3,z407,z4,z5,z6]),(1,[z1,z2,z3,z407,z5,z64]),(0,[z1,z2,z3,z4,z130,z5,z6])]],
   [[(0,[z121,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z482,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z483,z6]),(1,[z401,z2,z3,z4,z5,z6]),(0,[z213,z1,z3,z180,z4,z5,z6]),(0,[z1,z2,z25,z3,z4,z130,z6])],[(0,[z2,z107,z3,z4,z5,z76,z6]),(0,[z1,z2,z3,z4,z5,z6,z19]),(0,[z1,z2,z3,z22,z5,z64,z6]),(0,[z1,z2,z3,z4,z484,z5,z6])],[(0,[z1,z107,z3,z4,z5,z124,z6]),(0,[z485,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z118,z3,z5,z13])],[(0,[z221,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z2,z3,z4,z5,z487,z6]),(0,[z1,z2,z3,z4,z488,z5,z6])],[(0,[z1,z214,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z489,z6]),(0,[z361,z1,z2,z3,z44,z5,z6]),(0,[z328,z2,z3,z109,z4,z5,z6]),(0,[z1,z2,z146,z3,z4,z5,z6]),(0,[z490,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z58,z5,z6]),(0,[z1,z2,z3,z4,z5,z491,z6])],[(0,[z1,z2,z3,z492,z4,z5,z6]),(0,[z1,z2,z493,z3,z4,z5,z6]),(0,[z8,z1,z2,z215,z4,z5,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z495,z6]),(0,[z1,z2,z138,z4,z5,z247,z6]),(0,[z1,z2,z248,z3,z4,z334,z6])],[(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z497,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z498,z3,z4,z5,z6]),(0,[z1,z2,z4,z32,z5,z247,z6]),(0,[z1,z2,z3,z4,z5,z6,z499])],[(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z86,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z9,z6]),(0,[z1,z2,z21,z3,z180,z5,z6]),(0,[z501,z1,z2,z3,z4,z5,z6])],[(0,[z1,z502,z2,z3,z4,z5,z6]),(0,[z1,z2,z503,z3,z4,z5,z6]),(0,[z1,z2,z3,z504,z4,z5,z6]),(1,[z239,z2,z3,z4,z202,z6]),(0,[z1,z2,z87,z3,z4,z32,z6])],[(0,[z239,z2,z107,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z505])],[(0,[z221,z1,z214,z3,z4,z5,z6]),(0,[z8,z81,z1,z2,z4,z5,z6])],[(1,[z221,z107,z3,z4,z5,z6]),(0,[z1,z2,z506,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z507,z5,z6]),(0,[z1,z2,z508,z3,z4,z5,z6])],[(1,[z127,z2,z3,z4,z5,z105]),(0,[z1,z2,z3,z71,z5,z6,z13])],[(0,[z1,z2,z3,z4,z5,z168,z66]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z3,z510,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z511,z6]),(0,[z1,z2,z79,z3,z4,z5,z6])],[(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z513,z3,z4,z5,z6]),(0,[z1,z514,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z515])]],
   [[(0,[z121,z1,z2,z3,z4,z5,z290]),(0,[z1,z2,z3,z4,z5,z516,z6]),(0,[z1,z2,z25,z3,z4,z6,z30])],[(0,[z1,z2,z3,z517,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z518,z6]),(0,[z328,z1,z2,z21,z3,z5,z6]),(0,[z1,z2,z519,z3,z4,z5,z6]),(0,[z1,z136,z2,z3,z180,z5,z6]),(0,[z1,z2,z3,z4,z44,z5,z6])],[(0,[z1,z2,z520,z3,z4,z5,z6]),(0,[z239,z1,z2,z3,z4,z76,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z248,z3,z521,z5,z6]),(0,[z1,z2,z3,z522,z4,z5,z6]),(0,[z523,z1,z2,z3,z4,z5,z6])],[(0,[z524,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z525,z5,z6]),(0,[z1,z193,z2,z215,z4,z5,z6]),(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z527,z2,z3,z4,z5,z6]),(0,[z1,z2,z248,z4,z5,z247,z6])],[(0,[z1,z2,z3,z4,z5,z6,z528]),(0,[z1,z2,z3,z4,z529,z5,z6]),(0,[z1,z2,z3,z530,z4,z5,z6]),(0,[z1,z2,z3,z531,z4,z5,z6]),(0,[z1,z2,z532,z3,z4,z5,z6])],[(0,[z1,z2,z3,z192,z58,z5,z6]),(0,[z127,z1,z2,z25,z3,z4,z5]),(0,[z1,z533,z2,z3,z4,z5,z6]),(1,[z1,z2,z87,z4,z32,z6]),(0,[z1,z2,z3,z4,z5,z168,z6])],[(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z127,z1,z2,z3,z4,z5,z66]),(0,[z1,z2,z3,z535,z4,z5,z6]),(1,[z1,z2,z3,z521,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z536,z6]),(0,[z1,z2,z3,z4,z537,z5,z6]),(0,[z1,z2,z538,z3,z4,z5,z6]),(0,[z8,z1,z193,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z124,z6,z19])],[(0,[z1,z2,z3,z4,z5,z6,z505]),(0,[z1,z2,z3,z4,z5,z539,z6]),(0,[z1,z2,z3,z4,z5,z6,z540])],[(0,[z1,z2,z3,z4,z541,z5,z6]),(0,[z1,z2,z191,z3,z4,z356,z6])],[(1,[z81,z2,z82,z4,z5,z6]),(0,[z361,z1,z2,z21,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z168,z19]),(0,[z1,z2,z3,z521,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z542]),(0,[z543,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z544,z5,z6]),(0,[z1,z2,z3,z4,z5,z545,z6]),(0,[z1,z2,z3,z4,z5,z546,z6]),(0,[z1,z547,z2,z3,z4,z5,z6])],[(0,[z1,z413,z2,z3,z4,z5,z6]),(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z110,z3,z5,z76,z6]),(0,[z1,z2,z3,z4,z5,z6,z549]),(0,[z1,z2,z3,z4,z5,z6,z550]),(1,[z1,z2,z3,z98,z5,z6]),(1,[z1,z2,z3,z4,z130,z24])],[(0,[z127,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z551,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z191,z4,z5,z247,z6]),(0,[z1,z2,z3,z4,z250,z5,z6]),(0,[z1,z2,z25,z3,z4,z5,z30])],[(0,[z1,z2,z3,z552,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z553,z6]),(0,[z1,z2,z3,z554,z4,z5,z6])],[(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z556,z6]),(0,[z1,z2,z248,z3,z4,z5,z119])],[(0,[z361,z2,z3,z4,z192,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6])],[(0,[z121,z81,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z558,z5,z6]),(0,[z1,z2,z21,z3,z4,z247,z6])],[(0,[z1,z2,z3,z559,z4,z5,z6]),(0,[z1,z2,z3,z4,z202,z247,z6]),(0,[z1,z560,z2,z3,z4,z5,z6])],[(0,[z1,z2,z561,z3,z4,z5,z6]),(0,[z1,z2,z3,z562,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z119]),(1,[z1,z2,z3,z4,z55,z6]),(0,[z1,z2,z4,z5,z168,z6,z119])],[(0,[z1,z2,z563,z3,z4,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z565,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z566,z5,z6]),(0,[z1,z2,z3,z4,z5,z567,z6]),(0,[z1,z568,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z1,z2,z3,z4,z5,z570,z6]),(0,[z1,z2,z3,z4,z5,z6,z571]),(0,[z1,z2,z3,z4,z5,z6,z572]),(0,[z1,z2,z3,z4,z5,z573,z6])],[(0,[z1,z2,z574,z3,z4,z5,z6]),(0,[z1,z2,z3,z575,z4,z5,z6])],[(0,[z576,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z58,z5,z6]),(0,[z1,z47,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z407,z5,z64,z6]),(0,[z1,z2,z577,z3,z4,z5,z6])],[(0,[z1,z2,z3,z215,z4,z5,z6]),(0,[z1,z2,z578,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z579,z5,z6]),(0,[z580,z1,z2,z3,z4,z5,z6]),(1,[z361,z2,z3,z192,z5,z6]),(0,[z1,z2,z87,z4,z58,z5,z6]),(0,[z1,z2,z3,z4,z581,z5,z6])],[(0,[z1,z2,z3,z4,z582,z5,z6])],[(0,[z1,z2,z107,z3,z4,z5,z6]),(0,[z184,z1,z413,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z583]),(0,[z1,z2,z138,z3,z4,z247,z6]),(1,[z1,z2,z21,z3,z45,z6]),(0,[z1,z2,z3,z4,z5,z584,z6]),(0,[z1,z2,z3,z4,z5,z585,z6])],[(0,[z1,z2,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z586,z6]),(0,[z1,z2,z3,z4,z5,z6,z587]),(0,[z1,z2,z25,z21,z3,z4,z6])]],
   [[(0,[z588,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z589,z3,z4,z5,z6]),(0,[z1,z378,z2,z3,z4,z5,z6]),(0,[z590,z1,z2,z3,z4,z5,z6]),(1,[z10,z1,z3,z4,z11,z6])],[(0,[z2,z82,z3,z37,z4,z5,z6]),(0,[z1,z2,z591,z3,z4,z5,z6]),(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z593,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z594]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z596,z6]),(0,[z1,z2,z248,z3,z4,z5,z168])],[(0,[z121,z1,z2,z3,z397,z5,z6]),(0,[z361,z1,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z598,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z599,z3,z4,z5,z6])],[(0,[z328,z1,z2,z3,z109,z5,z6]),(0,[z1,z2,z3,z4,z5,z600,z6]),(0,[z8,z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z6]),(0,[z1,z2,z3,z4,z601,z5,z6]),(0,[z1,z2,z3,z4,z5,z602,z6]),(0,[z1,z2,z3,z4,z5,z6,z603])],[(0,[z93,z1,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z213,z1,z2,z3,z180,z5,z6]),(0,[z1,z2,z3,z407,z4,z5,z64])],[(0,[z604,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z119])],[(0,[z81,z1,z193,z2,z4,z5,z6]),(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z2,z191,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z247,z24,z6]),(1,[z1,z2,z3,z185,z5,z6])]],
   [[(0,[z1,z2,z606,z3,z4,z5,z6]),(0,[z1,z2,z3,z407,z180,z5,z6]),(0,[z1,z2,z3,z4,z88,z5,z6])],[(0,[z121,z1,z2,z37,z4,z5,z6]),(0,[z1,z2,z607,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z2,z3,z407,z4,z5,z119]),(0,[z1,z2,z3,z4,z130,z5,z119])],[(0,[z609,z1,z2,z3,z4,z5,z6]),(1,[z121,z2,z37,z4,z5,z6]),(1,[z63,z2,z3,z4,z5,z66]),(0,[z1,z2,z3,z180,z58,z5,z6]),(0,[z1,z2,z3,z4,z5,z610,z6]),(0,[z1,z611,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z6,z30])],[(0,[z2,z107,z3,z37,z4,z5,z6]),(0,[z1,z2,z3,z612,z4,z5,z6]),(0,[z613,z1,z2,z3,z4,z5,z6]),(0,[z361,z1,z378,z3,z4,z5,z6]),(0,[z406,z1,z2,z3,z4,z5,z6])],[(0,[z1,z18,z107,z3,z4,z5,z6]),(0,[z93,z2,z3,z37,z4,z5,z6]),(0,[z1,z2,z3,z4,z86,z247,z6]),(1,[z1,z2,z3,z4,z5,z596]),(0,[z1,z2,z614,z3,z4,z5,z6])],[(0,[z1,z2,z3,z615,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z616,z6])],[(0,[z617,z1,z2,z3,z4,z5,z6]),(0,[z361,z1,z2,z3,z109,z5,z6]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z1,z2,z3,z4,z619,z5,z6]),(0,[z1,z2,z620,z3,z4,z5,z6]),(0,[z1,z621,z2,z3,z4,z5,z6])],[(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z623,z6]),(0,[z1,z2,z3,z4,z5,z624,z6]),(0,[z1,z2,z118,z3,z5,z6,z13]),(0,[z1,z2,z3,z4,z5,z6,z625])]],
   [[(0,[z1,z2,z626,z3,z4,z5,z6]),(0,[z1,z2,z627,z3,z4,z5,z6]),(0,[z1,z2,z3,z181,z4,z5,z6]),(0,[z1,z2,z3,z4,z262,z5,z6]),(0,[z1,z2,z628,z3,z4,z5,z6])],[(0,[z121,z8,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z1,z2,z21,z243,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z290,z6]),(0,[z1,z2,z630,z3,z4,z5,z6]),(0,[z1,z85,z2,z3,z4,z11,z6]),(0,[z631,z1,z2,z3,z4,z5,z6])],[(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z71,z5,z6]),(0,[z1,z2,z191,z3,z4,z5,z596]),(0,[z1,z2,z633,z3,z4,z5,z6])],[(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z1,z2,z3,z22,z44,z5,z6]),(0,[z1,z2,z3,z26,z4,z247,z6])],[(0,[z93,z2,z3,z4,z5,z76,z6]),(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z635,z5,z6]),(0,[z1,z2,z3,z4,z5,z636,z6]),(0,[z1,z2,z3,z4,z5,z6,z637])],[(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z639,z3,z4,z5,z6]),(0,[z1,z2,z118,z3,z4,z5,z6]),(0,[z640,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z641,z4,z5,z6]),(0,[z1,z642,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z130,z5]),(0,[z1,z2,z3,z180,z44,z5,z6]),(0,[z643,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z644,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z645,z3,z4,z5,z6]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z45,z6])],[(0,[z647,z1,z2,z3,z4,z5,z6]),(0,[z328,z1,z2,z3,z4,z5,z6]),(0,[z1,z147,z3,z215,z4,z5,z6]),(0,[z1,z2,z3,z407,z4,z5,z168])],[(0,[z1,z2,z110,z3,z4,z5,z6]),(0,[z1,z2,z648,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z649])],[(1,[z1,z2,z3,z4,z16,z6]),(0,[z239,z1,z2,z3,z4,z202,z6]),(0,[z1,z2,z3,z4,z650,z5,z6]),(0,[z1,z2,z651,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z652,z5,z6])],[(0,[z214,z2,z107,z3,z4,z5,z6]),(1,[z1,z392,z3,z4,z5,z6]),(0,[z1,z2,z3,z653,z4,z5,z6])],[(0,[z121,z1,z2,z82,z4,z5,z6]),(0,[z328,z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z654,z3,z4,z5,z6])],[(0,[z1,z2,z655,z3,z4,z5,z6]),(0,[z1,z2,z656,z3,z4,z5,z6]),(0,[z1,z2,z4,z58,z5,z247,z6]),(0,[z1,z2,z153,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z657,z5,z6]),(0,[z1,z2,z3,z658,z4,z5,z6]),(1,[z406,z2,z3,z4,z5,z6]),(0,[z1,z2,z153,z4,z5,z6,z119]),(0,[z1,z2,z3,z4,z5,z6,z659])]],
   [[(0,[z1,z2,z3,z4,z397,z5,z6]),(0,[z1,z47,z2,z3,z4,z5,z124]),(0,[z1,z2,z660,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z661,z6])],[(0,[z1,z2,z3,z4,z5,z6,z662]),(1,[z1,z2,z79,z3,z5,z6])],[(0,[z121,z1,z225,z3,z4,z5,z6]),(0,[z1,z2,z663,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z18,z3,z4,z5,z6,z19])],[(0,[z361,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z272,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z664]),(1,[z1,z2,z3,z4,z5,z318]),(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z1,z2,z25,z3,z4,z5,z6])],[(0,[z93,z239,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z666,z4,z5,z6]),(0,[z1,z2,z3,z667,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z668,z6]),(0,[z1,z85,z2,z3,z98,z5,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z670,z6])],[(0,[z213,z1,z107,z3,z4,z5,z6]),(0,[z1,z2,z671,z3,z4,z5,z6]),(0,[z1,z2,z3,z672,z4,z5,z6])],[(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z674]),(0,[z1,z2,z3,z4,z675,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z677,z6])],[(0,[z678,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z680]),(0,[z1,z2,z681,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z682])],[(0,[z1,z2,z3,z683,z4,z5,z6]),(0,[z684,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z13])],[(0,[z1,z214,z3,z4,z5,z11,z6]),(0,[z685,z1,z2,z3,z4,z5,z6])],[(0,[z1,z686,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6]),(0,[z8,z1,z2,z3,z468,z5,z6]),(0,[z1,z2,z3,z688,z4,z5,z6]),(0,[z1,z85,z2,z3,z4,z86,z6]),(0,[z1,z2,z191,z208,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z572]),(0,[z1,z2,z3,z407,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z689,z6])],[(0,[z1,z3,z180,z4,z71,z5,z6]),(0,[z1,z2,z87,z3,z4,z5,z6])],[(0,[z121,z1,z2,z3,z4,z16,z6]),(0,[z1,z2,z690,z3,z4,z5,z6]),(0,[z1,z2,z87,z4,z5,z6,z119]),(0,[z1,z2,z3,z4,z5,z6,z29])],[(0,[z93,z221,z2,z3,z4,z5,z6]),(1,[z1,z2,z243,z4,z5,z6]),(0,[z1,z2,z691,z3,z4,z5,z6])]],
   [[(0,[z121,z1,z2,z3,z4,z5,z505]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z184,z1,z2,z3,z4,z76,z6]),(1,[z1,z2,z3,z370,z5,z6])],[(0,[z1,z2,z3,z4,z692,z5,z6]),(0,[z1,z2,z3,z693,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z694,z6]),(0,[z1,z193,z2,z3,z4,z5,z6]),(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z696,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z6])],[(0,[z1,z2,z3,z697,z4,z5,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z318]),(0,[z1,z2,z3,z4,z5,z699,z6])],[(0,[z1,z2,z3,z4,z5,z700,z6]),(0,[z1,z2,z191,z3,z4,z5,z572])],[],[(0,[z1,z107,z3,z215,z4,z5,z6]),(0,[z1,z107,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z701]),(0,[z8,z401,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z702])],[(0,[z221,z2,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z703,z6]),(0,[z1,z704,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z85,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z706,z5,z6]),(1,[z93,z214,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z143,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z707,z6]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z1,z2,z709,z4,z5,z6]),(0,[z127,z2,z691,z3,z4,z5]),(0,[z1,z2,z3,z41,z5,z9]),(0,[z1,z621,z3,z180,z5,z6]),(0,[z1,z2,z3,z4,z130,z157])],[(0,[z277,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z2,z25,z3,z4,z668]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z138,z4,z712,z6]),(0,[z1,z2,z25,z4,z247,z119])],[(0,[z2,z3,z4,z5,z66,z713]),(0,[z8,z1,z215,z4,z143,z6]),(0,[z714,z2,z3,z4,z5,z6]),(0,[z1,z2,z715,z3,z4,z6]),(0,[z1,z2,z358,z4,z247,z6])],[(0,[z178,z1,z2,z4,z716,z6]),(0,[z121,z2,z717,z4,z5,z6]),(0,[z1,z2,z3,z5,z64,z421])],[(0,[z239,z53,z3,z4,z5,z6]),(0,[z8,z1,z215,z4,z55,z6]),(0,[z1,z2,z4,z5,z247,z572])],[(0,[z1,z718,z3,z4,z5,z6]),(0,[z719,z2,z3,z4,z5,z6]),(0,[z1,z85,z3,z370,z86,z6]),(0,[z1,z2,z358,z22,z5,z6]),(1,[z1,z2,z4,z5,z720]),(0,[z1,z2,z118,z3,z5,z218])],[(0,[z1,z2,z146,z3,z4,z32]),(0,[z127,z95,z3,z4,z5,z6]),(0,[z721,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z2,z22,z723,z5,z6])],[]],
   [[(0,[z121,z225,z37,z4,z5,z6]),(0,[z1,z2,z3,z104,z5,z290]),(0,[z354,z2,z3,z4,z143,z6])],[(0,[z31,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z5,z724,z6]),(0,[z81,z2,z561,z4,z5,z6]),(0,[z1,z2,z725,z3,z4,z5]),(0,[z8,z354,z215,z4,z5,z6]),(0,[z8,z1,z215,z41,z5,z6])],[(1,[z726,z3,z4,z5,z6]),(0,[z61,z2,z3,z4,z5,z66]),(0,[z1,z2,z21,z3,z420,z6])],[(0,[z1,z392,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z3,z4,z728,z6])],[(0,[z1,z729,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z2,z3,z731,z5,z6])],[(0,[z1,z726,z3,z4,z5,z6]),(0,[z1,z2,z4,z732,z5,z6]),(0,[z225,z3,z37,z4,z5,z6]),(0,[z1,z733,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z734]),(0,[z184,z2,z3,z4,z76,z6]),(0,[z735,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z736]),(0,[z1,z2,z358,z58,z5,z6]),(0,[z1,z2,z248,z4,z5,z148]),(0,[z1,z737,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z738,z6])]],
   [[(0,[z1,z2,z3,z4,z739,z6]),(0,[z121,z401,z2,z4,z5,z6]),(0,[z1,z2,z3,z740,z5,z6])],[(0,[z1,z2,z3,z741,z5,z6]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z1,z159,z21,z3,z5,z6]),(0,[z1,z2,z4,z5,z168,z720])],[(0,[z1,z2,z3,z272,z5,z6]),(0,[z1,z2,z743,z4,z5,z6]),(0,[z235,z85,z3,z4,z5,z6])],[(0,[z1,z744,z3,z4,z5,z6]),(0,[z1,z2,z690,z4,z5,z119])],[(0,[z609,z107,z3,z4,z5,z6]),(0,[z121,z2,z37,z4,z16,z6]),(0,[z745,z2,z3,z4,z5,z6]),(0,[z746,z2,z3,z4,z5,z6]),(0,[z1,z2,z243,z180,z5,z6]),(0,[z1,z242,z3,z4,z5,z19]),(0,[z1,z747,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z748])],[(0,[z1,z749,z3,z4,z5,z6]),(0,[z401,z3,z215,z4,z5,z6]),(0,[z1,z2,z3,z181,z5,z6]),(0,[z1,z2,z3,z750,z5,z6]),(0,[z1,z2,z3,z4,z6,z751]),(0,[z1,z2,z120,z26,z4,z6]),(0,[z1,z2,z12,z752,z4,z6])],[(0,[z1,z2,z503,z58,z5,z6]),(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z3,z4,z754,z6]),(0,[z1,z2,z358,z4,z32,z6])],[(0,[z1,z2,z3,z755,z5,z6]),(0,[z1,z756,z3,z4,z5,z6])]],
   [[(0,[z328,z2,z3,z389,z5,z6]),(0,[z1,z2,z3,z757,z5,z6]),(0,[z1,z2,z3,z4,z5,z758])],[(0,[z178,z1,z2,z759,z5,z6]),(0,[z1,z225,z3,z4,z16,z6])],[(0,[z1,z2,z3,z759,z5,z6]),(0,[z1,z760,z3,z4,z5,z6])],[(0,[z1,z2,z4,z761,z5,z6]),(0,[z81,z2,z57,z4,z5,z6]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z1,z2,z763,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z2,z3,z4,z5,z765])],[(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z767,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z768]),(0,[z1,z36,z3,z397,z5,z6]),(0,[z1,z769,z3,z4,z5,z6])],[],[(0,[z726,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z397,z48,z6]),(0,[z1,z770,z215,z4,z5,z6]),(0,[z1,z2,z3,z4,z771,z6]),(0,[z772,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z370,z5,z6]),(0,[z1,z3,z4,z773,z11,z6])]],
   [[(0,[z1,z2,z3,z4,z774,z6])],[(0,[z178,z221,z107,z4,z5,z6]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z4,z776,z6]),(0,[z1,z2,z3,z777,z5,z6]),(1,[z2,z3,z4,z5,z713])],[(0,[z1,z18,z3,z4,z5,z474]),(0,[z1,z2,z778,z3,z5,z6])],[(0,[z178,z401,z2,z4,z5,z6]),(0,[z1,z779,z3,z4,z5,z6]),(0,[z780,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z782,z3,z4,z5,z6])],[],[(0,[z1,z2,z783,z3,z5,z6]),(0,[z1,z2,z784,z3,z4,z6])],[(0,[z221,z155,z107,z4,z5,z6]),(0,[z1,z2,z3,z4,z143,z6]),(0,[z1,z2,z3,z5,z6,z785])],[(0,[z1,z214,z3,z370,z5,z6]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z1,z2,z3,z787,z5,z6]),(0,[z1,z2,z3,z26,z44,z6]),(0,[z1,z2,z25,z3,z4,z218]),(0,[z1,z2,z21,z3,z303,z6])]],
   [[(0,[z1,z2,z788,z4,z5,z6]),(0,[z239,z2,z3,z4,z237,z6]),(0,[z1,z2,z3,z4,z5,z789]),(0,[z8,z1,z215,z4,z5,z170]),(0,[z1,z2,z790,z4,z5,z6])],[(0,[z1,z18,z3,z4,z5,z19]),(0,[z1,z2,z3,z4,z262,z6]),(0,[z1,z2,z191,z185,z5,z6]),(0,[z1,z2,z3,z791,z5,z6])],[(0,[z1,z2,z792,z3,z5,z6]),(0,[z1,z2,z793,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z21,z58,z247,z6]),(0,[z1,z2,z358,z4,z262,z6]),(0,[z1,z2,z87,z4,z712,z6])],[(0,[z1,z2,z437,z4,z247,z6]),(0,[z1,z2,z3,z5,z6,z795])],[(0,[z796,z2,z3,z4,z5,z6]),(0,[z797,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z798])],[(0,[z354,z2,z3,z4,z5,z170]),(0,[z1,z2,z799,z4,z5,z6])],[(0,[z1,z2,z3,z468,z143,z6])]],
   [[(0,[z1,z2,z3,z4,z800,z6]),(0,[z801,z2,z3,z4,z5,z6]),(0,[z1,z2,z118,z3,z5,z336]),(0,[z1,z2,z3,z4,z5,z720])],[(0,[z1,z2,z3,z4,z802,z6]),(0,[z1,z2,z208,z58,z5,z6])],[(0,[z1,z2,z803,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z6])],[(0,[z107,z3,z4,z5,z536,z6]),(0,[z239,z2,z3,z4,z804,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z1,z806,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z808,z3,z4,z5,z6]),(0,[z1,z2,z78,z740,z5,z6])],[(0,[z152,z107,z3,z4,z5,z6]),(0,[z204,z18,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z516,z6])],[(0,[z1,z2,z809,z4,z5,z6]),(0,[z1,z2,z4,z5,z810,z6]),(0,[z2,z3,z811,z4,z5,z6]),(0,[z63,z2,z3,z4,z5,z713]),(0,[z812,z2,z3,z4,z5,z6]),(0,[z1,z2,z12,z118,z3,z6])],[(0,[z121,z36,z37,z4,z5,z6]),(0,[z1,z2,z813,z3,z5,z6]),(0,[z1,z3,z770,z4,z5,z6]),(0,[z1,z2,z3,z814,z5,z6]),(0,[z213,z1,z3,z815,z5,z6]),(0,[z1,z2,z191,z22,z5,z6]),(0,[z1,z2,z3,z816,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z817,z6])],[(0,[z121,z2,z37,z4,z48,z6]),(0,[z184,z2,z3,z4,z195,z76]),(0,[z401,z2,z3,z4,z143,z6]),(0,[z1,z2,z78,z4,z32,z6])],[(0,[z81,z193,z107,z4,z5,z6]),(0,[z1,z2,z118,z3,z5,z818])],[(0,[z1,z2,z3,z104,z5,z6]),(0,[z1,z2,z3,z819,z5,z6]),(0,[z1,z2,z3,z4,z130,z586]),(0,[z1,z2,z3,z820,z5,z6]),(0,[z1,z2,z87,z4,z32,z318]),(0,[z1,z2,z25,z3,z4,z271])],[(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z2,z822,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z823])],[(0,[z1,z2,z110,z3,z5,z6]),(0,[z1,z2,z25,z3,z29,z30])],[(0,[z1,z2,z3,z4,z824,z6]),(0,[z1,z225,z3,z4,z48,z6]),(0,[z1,z2,z825,z4,z5,z6])],[(0,[z1,z2,z3,z826,z5,z6]),(0,[z1,z2,z3,z4,z5,z827]),(0,[z1,z2,z222,z4,z5,z119]),(0,[z1,z2,z3,z4,z5,z818])]],
   [[(0,[z1,z2,z3,z4,z5,z828]),(0,[z401,z2,z3,z41,z5,z6]),(0,[z1,z3,z4,z5,z6,z829]),(0,[z1,z2,z3,z4,z32,z148]),(0,[z1,z2,z118,z3,z5,z384])],[(0,[z2,z717,z37,z4,z5,z6]),(0,[z1,z47,z3,z4,z5,z124]),(0,[z1,z2,z4,z5,z712,z6])],[(0,[z1,z3,z4,z5,z124,z738]),(0,[z1,z2,z3,z161,z44,z6])],[(0,[z830,z1,z3,z4,z5,z6]),(0,[z319,z2,z3,z4,z202,z6]),(0,[z8,z401,z215,z4,z5,z6])],[(0,[z1,z2,z155,z4,z5,z6]),(0,[z1,z2,z831,z3,z5,z6]),(0,[z1,z136,z3,z71,z5,z6])],[(0,[z1,z2,z832,z3,z4,z5]),(0,[z194,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z833]),(0,[z121,z2,z37,z104,z5,z6]),(0,[z328,z2,z3,z109,z5,z6]),(0,[z1,z2,z834,z4,z5,z6])],[(0,[z1,z2,z835,z4,z5,z6]),(0,[z214,z726,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z836]),(0,[z1,z47,z3,z4,z5,z738]),(0,[z1,z2,z87,z4,z334,z6]),(0,[z1,z2,z3,z250,z334,z6])],[(0,[z1,z837,z3,z4,z5,z6]),(0,[z184,z413,z3,z4,z76,z6]),(0,[z1,z3,z815,z71,z5,z6]),(0,[z1,z2,z723,z58,z5,z6]),(0,[z1,z838,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z839,z5,z6]),(0,[z1,z36,z3,z4,z16,z6]),(0,[z1,z2,z3,z4,z5,z840]),(0,[z1,z2,z478,z22,z5,z6]),(0,[z1,z2,z841,z4,z5,z6])],[(0,[z1,z159,z3,z4,z5,z6]),(0,[z1,z53,z3,z4,z5,z6]),(0,[z178,z1,z2,z842,z5,z6]),(0,[z1,z2,z243,z5,z64,z6]),(0,[z1,z2,z843,z4,z5,z6])],[(0,[z393,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z225,z3,z104,z5,z6]),(0,[z1,z36,z3,z4,z5,z505]),(0,[z2,z3,z109,z811,z5,z6]),(0,[z1,z2,z3,z844,z5,z6])],[(0,[z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z845,z5,z6]),(0,[z1,z2,z3,z846,z5,z6]),(0,[z1,z2,z3,z185,z247,z6])],[(0,[z1,z2,z3,z847,z5,z6]),(0,[z1,z2,z3,z4,z48,z505]),(0,[z1,z2,z467,z4,z32,z6]),(0,[z95,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z3,z250,z338,z6])],[(0,[z1,z396,z3,z4,z5,z124]),(0,[z1,z2,z3,z26,z436,z6])],[(0,[z1,z2,z3,z407,z5,z220]),(0,[z1,z2,z3,z4,z5,z848])],[(0,[z1,z2,z849,z4,z5,z6]),(0,[z1,z85,z3,z4,z86,z6]),(1,[z1,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z5,z738])]],
   [[(0,[z1,z2,z850,z4,z5,z6]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z4,z5,z720,z6]),(0,[z1,z2,z248,z4,z338,z168])],[(0,[z1,z378,z3,z4,z5,z6]),(0,[z1,z2,z3,z852,z5,z6]),(0,[z1,z2,z853,z3,z4,z5])],[(0,[z1,z2,z3,z4,z854,z6]),(0,[z1,z2,z232,z58,z5,z6])],[(0,[z361,z2,z426,z3,z5,z6]),(0,[z1,z2,z3,z22,z5,z596]),(0,[z1,z2,z25,z3,z4,z30])],[(0,[z1,z2,z3,z4,z855,z6]),(0,[z354,z2,z3,z468,z5,z6]),(0,[z213,z1,z3,z180,z5,z6])],[(0,[z178,z1,z2,z4,z5,z856]),(0,[z1,z2,z3,z4,z857,z6]),(0,[z1,z2,z3,z468,z5,z170]),(0,[z1,z858,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z856]),(0,[z1,z2,z3,z4,z859,z6]),(0,[z1,z2,z3,z104,z16,z6]),(0,[z1,z2,z3,z4,z195,z5])],[(0,[z698,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z1,z3,z4,z5,z738,z19]),(0,[z1,z2,z577,z4,z247,z6]),(0,[z1,z2,z3,z861,z5,z6]),(0,[z1,z2,z862,z3,z5,z6]),(1,[z1,z2,z3,z5,z818]),(0,[z1,z2,z3,z4,z24,z863])]],
   [[(0,[z1,z2,z3,z104,z5,z505]),(0,[z63,z392,z3,z4,z5,z66]),(0,[z864,z2,z3,z4,z5,z6])],[(0,[z227,z107,z3,z4,z5,z6]),(0,[z2,z3,z717,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z865])],[(0,[z1,z2,z3,z866,z5,z6]),(0,[z646,z1,z3,z4,z11,z6])],[(0,[z184,z2,z146,z3,z4,z76])],[(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z4,z868,z6]),(0,[z1,z2,z3,z58,z5,z596]),(0,[z1,z2,z3,z185,z5,z318])],[(0,[z1,z2,z3,z4,z6,z869]),(0,[z1,z2,z191,z22,z356,z6])],[(0,[z1,z2,z3,z4,z5,z870]),(0,[z871,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z872])],[(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z875,z3,z4,z5,z6]),(0,[z1,z2,z876,z3,z4,z5]),(0,[z401,z2,z3,z4,z5,z170]),(0,[z1,z27,z3,z71,z5,z6]),(0,[z1,z2,z255,z3,z5,z13]),(0,[z1,z877,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z5,z6,z878])],[(0,[z354,z2,z3,z4,z5,z9])],[(0,[z93,z555,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z2,z87,z185,z32,z6])],[(0,[z1,z2,z411,z22,z5,z6])],[(0,[z235,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z880,z5,z6]),(0,[z1,z3,z815,z4,z5,z6])],[(0,[z1,z2,z3,z4,z881,z6])],[(0,[z1,z95,z3,z4,z5,z6]),(0,[z1,z2,z3,z41,z55,z6]),(0,[z882,z2,z3,z4,z5,z6]),(0,[z1,z2,z883,z3,z4,z6])],[(0,[z1,z2,z3,z4,z884,z6]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z1,z2,z3,z4,z130,z863])]],
   [[(0,[z178,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z886,z6]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z1,z2,z358,z4,z5,z885])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z397,z5,z290]),(0,[z1,z2,z3,z888,z5,z6])],[(0,[z576,z107,z3,z4,z5,z6]),(0,[z1,z2,z358,z4,z5,z6]),(0,[z1,z2,z185,z58,z5,z6]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z1,z2,z21,z3,z636,z6]),(0,[z1,z2,z79,z3,z24,z6])],[],[(0,[z1,z2,z3,z250,z5,z6]),(0,[z1,z2,z3,z88,z5,z148])],[(0,[z1,z2,z889,z3,z4,z6]),(0,[z1,z890,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z891,z5]),(0,[z1,z2,z118,z243,z5,z6])],[(0,[z1,z85,z3,z4,z773,z6]),(0,[z1,z2,z100,z4,z5,z168]),(0,[z1,z2,z21,z3,z177,z6]),(0,[z1,z2,z3,z892,z5,z6])],[(0,[z1,z2,z3,z4,z863,z30])]],
   [[(0,[z1,z18,z3,z34,z5,z19]),(0,[z1,z2,z248,z4,z5,z168])],[(0,[z2,z3,z811,z192,z5,z6])],[(0,[z1,z2,z3,z468,z5,z6]),(0,[z1,z2,z3,z893,z5,z6])],[(0,[z2,z3,z4,z804,z76,z6]),(0,[z1,z2,z3,z4,z894,z6]),(0,[z1,z2,z248,z250,z5,z168]),(0,[z1,z2,z3,z521,z338,z6])],[(0,[z1,z2,z3,z4,z5,z895]),(0,[z1,z2,z3,z4,z896,z6])],[(0,[z1,z2,z3,z897,z5,z6]),(0,[z1,z2,z3,z4,z898,z6]),(0,[z1,z899,z3,z4,z5,z6]),(1,[z2,z3,z4,z804,z6]),(0,[z1,z2,z900,z4,z5,z6]),(0,[z901,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z804,z6])],[(0,[z1,z902,z3,z4,z5,z6])]],
   [[(0,[z726,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z804,z6]),(0,[z1,z2,z146,z3,z4,z5]),(0,[z1,z2,z3,z4,z262,z596]),(0,[z1,z2,z243,z4,z24,z6])],[(0,[z1,z2,z3,z4,z5,z290]),(0,[z1,z2,z3,z4,z903,z6]),(0,[z1,z2,z3,z904,z5,z6]),(0,[z905,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z906,z6]),(0,[z1,z2,z3,z907,z5,z6]),(0,[z1,z2,z4,z334,z247,z6]),(0,[z1,z2,z3,z4,z297,z24]),(0,[z1,z2,z3,z4,z5,z908])],[(0,[z1,z3,z4,z5,z909,z6]),(0,[z1,z2,z910,z4,z5,z6]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z912,z6]),(0,[z1,z2,z21,z3,z677,z6]),(0,[z1,z2,z3,z913,z5,z6]),(0,[z1,z2,z3,z407,z5,z64]),(0,[z1,z914,z3,z4,z5,z6])],[(0,[z178,z1,z2,z4,z5,z915]),(0,[z1,z2,z100,z22,z5,z6]),(0,[z1,z2,z916,z4,z5,z6])],[(0,[z1,z2,z3,z917,z5,z6]),(0,[z31,z1,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z2,z3,z4,z202,z804,z6]),(0,[z1,z136,z3,z815,z5,z6]),(1,[z1,z3,z4,z773,z6]),(0,[z1,z2,z3,z4,z773,z6])],[(0,[z1,z918,z3,z4,z5,z6]),(0,[z1,z2,z919,z4,z5,z6]),(0,[z1,z2,z3,z400,z5,z64])],[(0,[z93,z726,z3,z4,z5,z6]),(0,[z1,z920,z3,z4,z5,z6]),(0,[z1,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z25,z3,z4,z466])]],
   [[(0,[z1,z85,z3,z98,z86,z6]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z1,z2,z153,z4,z5,z119])],[(0,[z1,z2,z3,z4,z923,z5]),(0,[z213,z1,z3,z552,z5,z6]),(0,[z23,z214,z3,z4,z5,z6]),(0,[z127,z2,z3,z4,z5,z713]),(0,[z1,z3,z924,z4,z5,z6])],[(0,[z127,z2,z3,z4,z5,z594]),(0,[z1,z2,z925,z3,z4,z6]),(1,[z1,z2,z4,z712,z6]),(0,[z1,z926,z3,z4,z5,z6])],[(0,[z102,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z927,z5,z6]),(0,[z1,z2,z3,z4,z5,z928]),(0,[z1,z2,z4,z32,z712,z6])],[(0,[z93,z228,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z929,z6]),(0,[z1,z2,z3,z88,z5,z6])],[(0,[z401,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z170]),(0,[z1,z2,z3,z815,z5,z6])],[(0,[z1,z2,z191,z22,z5,z596]),(0,[z1,z2,z3,z4,z334,z6])],[]],
   [[(0,[z221,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z930,z6]),(0,[z1,z193,z225,z4,z5,z6]),(0,[z1,z225,z3,z4,z5,z290]),(0,[z2,z82,z717,z4,z5,z6]),(0,[z361,z159,z3,z192,z5,z6]),(0,[z8,z1,z215,z4,z5,z6]),(0,[z1,z2,z3,z468,z5,z9]),(0,[z1,z2,z3,z4,z931,z6])],[(0,[z684,z107,z3,z4,z5,z6]),(0,[z178,z1,z215,z4,z5,z6]),(0,[z127,z2,z3,z4,z5,z105])],[(0,[z1,z2,z932,z3,z4,z6]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z2,z3,z4,z6,z934]),(0,[z1,z2,z4,z5,z720,z119]),(0,[z1,z2,z3,z5,z935,z6])],[],[(0,[z1,z2,z936,z4,z5,z6]),(0,[z1,z2,z3,z937,z5,z6]),(0,[z1,z2,z938,z4,z5,z6]),(0,[z1,z2,z3,z4,z338,z6])],[(0,[z1,z2,z78,z4,z5,z6]),(0,[z1,z2,z248,z4,z334,z168])],[(0,[z939,z2,z3,z4,z5,z6])],[(0,[z1,z107,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z356,z6]),(0,[z1,z2,z25,z243,z4,z6]),(0,[z1,z2,z3,z44,z935,z6])]],
   [[(0,[z221,z726,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z940,z5])],[(0,[z1,z2,z519,z4,z247,z6]),(0,[z8,z1,z215,z468,z5,z6]),(0,[z1,z2,z3,z941,z5,z6]),(0,[z1,z270,z3,z71,z5,z6])],[(0,[z1,z2,z110,z3,z247,z6]),(0,[z401,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z942,z5,z6]),(0,[z1,z2,z3,z4,z943,z6]),(0,[z1,z2,z12,z3,z71,z6]),(0,[z944,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z521,z5,z6]),(0,[z1,z2,z12,z118,z3,z13])],[(0,[z1,z2,z770,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z148])],[],[(0,[z20,z2,z3,z192,z5,z6]),(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z946,z3,z4,z5,z6]),(0,[z1,z947,z3,z4,z5,z6])],[(0,[z81,z2,z82,z4,z5,z6]),(0,[z948,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z3,z4,z262,z572]),(0,[z1,z2,z87,z4,z5,z572]),(0,[z1,z2,z138,z4,z247,z6]),(0,[z950,z2,z3,z4,z5,z6])],[(0,[z229,z107,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z388])],[(0,[z1,z2,z3,z4,z5,z951]),(0,[z1,z2,z3,z4,z5,z952]),(0,[z1,z953,z3,z4,z5,z6]),(0,[z1,z2,z3,z98,z5,z6]),(0,[z1,z236,z3,z4,z86,z6]),(0,[z1,z2,z248,z521,z5,z168]),(0,[z1,z2,z954,z4,z5,z6]),(0,[z1,z2,z3,z4,z130,z24])],[(0,[z0,z107,z3,z4,z5,z6]),(0,[z1,z2,z955,z3,z4,z5]),(0,[z1,z2,z3,z5,z6,z956]),(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z2,z3,z4,z356,z596])],[(0,[z1,z2,z3,z397,z5,z6]),(0,[z81,z225,z3,z4,z5,z6])],[(0,[z1,z2,z958,z3,z5,z6]),(0,[z1,z2,z12,z3,z64,z6])],[(0,[z1,z2,z3,z959,z5,z6]),(0,[z8,z1,z215,z4,z5,z9]),(0,[z1,z2,z3,z960,z5,z6])],[(0,[z1,z2,z961,z4,z5,z6])]],
   [[(0,[z962,z2,z3,z4,z5,z6]),(0,[z963,z2,z3,z4,z5,z6]),(0,[z964,z2,z3,z4,z5,z6]),(0,[z1,z2,z965,z4,z5,z6])],[(0,[z1,z2,z457,z4,z5,z119]),(0,[z1,z2,z3,z935,z45,z6])],[(0,[z1,z2,z3,z4,z5,z966]),(0,[z1,z413,z3,z4,z5,z6]),(0,[z1,z2,z967,z3,z4,z5]),(0,[z1,z2,z3,z185,z32,z6])],[(0,[z1,z2,z3,z968,z4,z5]),(0,[z1,z2,z3,z4,z969,z6]),(0,[z406,z47,z3,z4,z5,z124]),(0,[z1,z2,z723,z4,z5,z6]),(0,[z1,z2,z112,z58,z5,z6])],[(0,[z1,z2,z3,z970,z5,z6])],[(0,[z1,z2,z3,z971,z5,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z2,z973,z4,z5,z6])],[(0,[z121,z2,z37,z397,z5,z6]),(0,[z1,z2,z110,z3,z32,z6]),(0,[z1,z2,z191,z22,z5,z572]),(0,[z1,z2,z21,z3,z935,z6])],[(0,[z1,z2,z3,z4,z5,z974]),(0,[z1,z2,z3,z41,z143,z6]),(0,[z1,z2,z3,z26,z6,z637])]],
   [[(0,[z1,z2,z3,z723,z5,z6]),(0,[z1,z2,z4,z712,z247,z6]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z976,z2,z3,z4,z5,z6])],[(0,[z1,z461,z3,z71,z5,z6]),(0,[z1,z2,z12,z965,z4,z6])],[(0,[z977,z2,z3,z4,z5,z6]),(0,[z1,z2,z78,z4,z334,z6]),(0,[z1,z2,z248,z4,z5,z720]),(0,[z1,z2,z3,z5,z6,z29]),(0,[z1,z2,z3,z4,z6,z863])],[(0,[z1,z225,z3,z397,z5,z6]),(0,[z1,z2,z978,z3,z5,z6])],[(0,[z1,z2,z3,z44,z687,z6]),(0,[z137,z1,z3,z180,z5,z6]),(0,[z1,z2,z12,z3,z180,z6]),(0,[z10,z1,z3,z4,z11,z6])],[(0,[z1,z2,z3,z4,z5,z979]),(0,[z1,z980,z3,z4,z5,z6]),(0,[z1,z2,z87,z88,z32,z6]),(0,[z1,z2,z3,z5,z64,z818])],[(0,[z1,z2,z3,z981,z5,z6]),(0,[z1,z2,z3,z4,z982,z6])],[(0,[z1,z85,z3,z4,z101,z6]),(0,[z1,z2,z146,z3,z272,z5]),(0,[z1,z2,z21,z120,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z983,z6]),(0,[z1,z36,z3,z4,z48,z6]),(0,[z204,z3,z4,z5,z124,z6]),(0,[z1,z2,z3,z521,z334,z6]),(0,[z1,z2,z25,z78,z4,z30])],[(0,[z1,z2,z3,z984,z4,z6])],[(0,[z184,z2,z3,z4,z804,z6]),(0,[z501,z2,z3,z4,z76,z6]),(0,[z1,z2,z3,z985,z5,z6])],[(0,[z63,z95,z3,z4,z5,z66])],[(0,[z1,z2,z3,z4,z6,z986])],[(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z988,z3,z4,z5,z6]),(0,[z1,z2,z3,z989,z5,z6])],[(0,[z121,z2,z37,z4,z5,z6]),(0,[z63,z2,z3,z4,z5,z66]),(0,[z1,z2,z3,z4,z5,z990]),(0,[z1,z2,z250,z5,z247,z6]),(0,[z1,z2,z25,z79,z3,z30])],[(0,[z1,z2,z3,z397,z16,z6]),(0,[z184,z2,z3,z272,z76,z6]),(0,[z1,z991,z3,z4,z5,z6])]],
   [[(0,[z107,z3,z408,z4,z5,z6]),(0,[z1,z2,z3,z992,z5,z6]),(0,[z1,z2,z3,z4,z5,z596]),(0,[z993,z1,z3,z4,z5,z6]),(0,[z1,z2,z78,z4,z5,z148]),(0,[z1,z2,z3,z44,z6,z252]),(0,[z1,z2,z3,z4,z994,z6])],[(0,[z1,z2,z3,z397,z5,z505]),(0,[z1,z995,z3,z4,z5,z6]),(0,[z695,z2,z3,z109,z5,z6]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z1,z2,z25,z3,z4,z587]),(0,[z1,z2,z3,z998,z5,z6])],[(0,[z1,z2,z3,z999,z5,z6]),(0,[z235,z3,z4,z5,z11,z6]),(0,[z1,z2,z21,z186,z3,z6]),(0,[z1,z2,z3,z4,z5,z863])],[(0,[z1,z225,z3,z4,z5,z6]),(0,[z1,z107,z3,z370,z5,z6]),(0,[z1,z2,z3,z1000,z5,z6]),(0,[z63,z2,z3,z4,z363,z5]),(0,[z1,z2,z3,z4,z356,z572]),(0,[z1,z2,z752,z4,z5,z6])],[(0,[z178,z1,z2,z4,z906,z6]),(0,[z1,z36,z3,z104,z5,z6]),(0,[z1,z2,z3,z1001,z5,z6]),(0,[z1,z2,z3,z272,z195,z5]),(0,[z1,z2,z3,z1002,z5,z6])],[(0,[z204,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1003,z6]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z8,z1,z770,z4,z5,z6]),(0,[z1005,z2,z3,z4,z5,z6]),(0,[z1,z2,z87,z4,z32,z148]),(0,[z1,z2,z25,z120,z4,z30])],[(0,[z1,z2,z3,z104,z48,z6]),(0,[z1006,z2,z3,z4,z5,z6]),(0,[z1,z2,z243,z71,z5,z6]),(0,[z2,z3,z4,z5,z6,z1007]),(0,[z1,z1008,z3,z4,z5,z6]),(0,[z1,z2,z358,z4,z5,z908])],[(0,[z401,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1009]),(0,[z1010,z2,z3,z4,z5,z6]),(1,[z1,z2,z723,z5,z6]),(0,[z1,z2,z3,z4,z334,z119])],[(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z1011,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z713,z105]),(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z1013,z4,z5,z6]),(0,[z1,z2,z118,z3,z5,z13])],[(0,[z1,z2,z4,z5,z6,z1014]),(0,[z1,z2,z3,z4,z24,z69])],[(0,[z328,z2,z3,z811,z5,z6]),(0,[z1,z169,z3,z180,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z2,z3,z22,z262,z6]),(0,[z1,z2,z3,z1017,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z1018]),(0,[z1,z2,z3,z1019,z5,z6]),(0,[z121,z2,z37,z4,z5,z290]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z2,z3,z4,z143,z170]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z2,z3,z1022,z5,z6]),(0,[z1,z2,z3,z5,z818,z13])],[(0,[z107,z3,z4,z5,z257,z6]),(0,[z1,z2,z3,z4,z16,z6]),(0,[z354,z2,z3,z4,z55,z6]),(0,[z1,z18,z3,z4,z5,z738]),(0,[z1,z2,z681,z4,z247,z6]),(0,[z1,z2,z78,z4,z5,z119])]],
   [[(0,[z1,z2,z1023,z4,z5,z6]),(0,[z239,z2,z3,z4,z202,z6]),(0,[z401,z2,z3,z468,z5,z6]),(0,[z1,z2,z3,z4,z5,z1024]),(1,[z1,z3,z815,z5,z6])],[(0,[z178,z2,z37,z4,z5,z6]),(0,[z1,z2,z3,z1025,z5,z6]),(0,[z1,z2,z3,z4,z5,z505]),(0,[z1,z2,z1026,z4,z5,z6]),(0,[z1,z2,z4,z262,z247,z6]),(0,[z1,z2,z25,z3,z4,z625])],[(0,[z1027,z2,z3,z4,z5,z6]),(0,[z1,z2,z153,z4,z5,z720]),(0,[z1,z2,z21,z3,z699,z6])],[(0,[z406,z2,z3,z4,z5,z6]),(0,[z158,z2,z3,z4,z5,z66])],[(0,[z354,z2,z3,z41,z5,z6]),(0,[z1,z3,z180,z815,z5,z6]),(0,[z1,z2,z605,z4,z5,z168]),(0,[z1,z2,z208,z723,z5,z6]),(0,[z1,z2,z260,z58,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1028]),(0,[z1,z2,z3,z41,z5,z170]),(0,[z1,z2,z3,z58,z262,z6]),(0,[z1,z2,z3,z521,z5,z119]),(0,[z1,z2,z118,z3,z5,z702]),(0,[z1,z2,z79,z3,z5,z6])],[(0,[z1,z2,z3,z4,z1029,z6]),(0,[z1,z2,z3,z1030,z5,z6]),(0,[z1,z2,z3,z5,z6,z1031])],[(1,[z2,z3,z811,z5,z6]),(0,[z1,z1032,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z713]),(0,[z1,z2,z3,z4,z5,z318])]],
   [[(0,[z1,z2,z3,z1033,z5,z6]),(0,[z81,z2,z717,z4,z5,z6]),(0,[z1,z2,z179,z58,z5,z6]),(0,[z1,z2,z21,z3,z256,z6]),(0,[z1,z2,z3,z4,z334,z168])],[],[(0,[z1,z2,z3,z811,z5,z6]),(0,[z1,z3,z4,z86,z773,z6])],[(0,[z121,z2,z37,z4,z5,z505]),(0,[z361,z378,z3,z192,z5,z6]),(0,[z1,z2,z1034,z3,z5,z6]),(0,[z1,z2,z118,z3,z388,z13])],[(0,[z1,z2,z3,z4,z5,z1035]),(0,[z1,z1036,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1037,z6])],[(0,[z1,z193,z391,z4,z5,z6]),(0,[z1,z2,z1038,z3,z4,z6]),(0,[z1,z2,z3,z1039,z5,z6]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z18,z3,z181,z5,z19]),(0,[z1,z2,z87,z4,z32,z6])],[(0,[z1,z2,z3,z1041,z5,z6]),(0,[z361,z2,z3,z811,z5,z6]),(0,[z631,z2,z3,z4,z5,z105]),(0,[z1,z2,z3,z1042,z5,z6]),(0,[z1,z2,z3,z1043,z5,z6]),(0,[z1,z2,z3,z1044,z5,z6])],[(0,[z1,z2,z3,z4,z16,z290]),(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z2,z3,z1046,z5,z6]),(0,[z1,z2,z78,z4,z5,z168]),(0,[z1,z2,z25,z3,z4,z863])]],
   [[(0,[z1,z225,z3,z4,z5,z505]),(0,[z47,z204,z3,z4,z5,z124]),(0,[z1,z2,z3,z4,z5,z572]),(0,[z1,z2,z3,z407,z5,z818])],[(0,[z1,z2,z3,z4,z5,z1047]),(0,[z1,z2,z1048,z4,z5,z6]),(0,[z1,z1049,z3,z4,z5,z6])],[(0,[z178,z81,z2,z4,z5,z6]),(0,[z1,z1050,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1051,z6])],[(0,[z2,z107,z146,z3,z4,z5]),(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z2,z243,z4,z5,z6]),(0,[z1,z2,z191,z723,z5,z6]),(0,[z1,z2,z3,z5,z6,z818])],[],[(0,[z1,z2,z1053,z3,z5,z6]),(0,[z81,z401,z2,z4,z5,z6]),(0,[z1,z2,z3,z688,z44,z6]),(0,[z1,z2,z3,z521,z5,z168]),(0,[z1,z2,z78,z998,z5,z6])],[(0,[z1,z1054,z3,z4,z5,z6]),(0,[z1,z1055,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z2,z3,z185,z5,z148]),(0,[z1,z2,z3,z4,z935,z6])],[(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z3,z1058,z5,z6])]],
   [[(0,[z178,z1,z193,z4,z5,z6]),(0,[z1,z2,z3,z4,z1059,z6]),(0,[z1,z2,z1060,z3,z5,z6])],[(0,[z1,z563,z3,z71,z5,z6]),(0,[z1,z2,z3,z4,z5,z713])],[(0,[z184,z2,z110,z3,z76,z6]),(0,[z1,z2,z3,z4,z1061,z6]),(0,[z1,z2,z78,z4,z247,z6]),(0,[z2,z3,z4,z5,z6,z1062])],[(0,[z93,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z1,z2,z3,z4,z5,z1064]),(0,[z1,z2,z3,z26,z935,z6])],[(0,[z1,z2,z3,z4,z16,z505]),(0,[z1,z2,z3,z1065,z5,z6]),(0,[z1,z2,z21,z3,z301,z6]),(0,[z10,z1,z3,z4,z773,z6]),(0,[z1066,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z55,z6]),(0,[z10,z90,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z2,z3,z1068,z5,z6])],[(0,[z1,z2,z1069,z4,z5,z6]),(0,[z1,z1070,z3,z4,z5,z6]),(0,[z53,z3,z4,z5,z76,z6]),(1,[z1,z2,z3,z4,z863])],[(0,[z1,z2,z110,z3,z195,z5])]],
   [[(0,[z1,z2,z1071,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1072]),(0,[z1,z2,z3,z1073,z5,z6]),(0,[z1,z2,z87,z4,z262,z6]),(0,[z1,z2,z3,z4,z247,z148]),(0,[z1,z2,z87,z250,z5,z6]),(0,[z1,z2,z25,z79,z3,z6])],[(0,[z1,z36,z3,z4,z5,z6]),(0,[z56,z107,z3,z4,z5,z6]),(0,[z93,z2,z146,z3,z4,z5]),(0,[z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z88,z5,z318]),(0,[z1,z2,z3,z407,z5,z567])],[(0,[z8,z1,z225,z4,z5,z6]),(0,[z361,z2,z3,z192,z5,z6]),(0,[z1,z2,z3,z1074,z5,z6]),(0,[z1,z2,z3,z1075,z5,z6]),(0,[z1,z2,z3,z4,z5,z1076])],[(0,[z178,z1,z225,z4,z5,z6]),(0,[z1,z2,z3,z4,z48,z6]),(1,[z2,z717,z4,z5,z6])],[(0,[z93,z83,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z21,z3,z45,z6])],[(0,[z184,z53,z3,z4,z76,z6]),(0,[z1,z2,z3,z468,z55,z6])],[(0,[z1,z2,z717,z4,z5,z6]),(0,[z1,z2,z299,z4,z5,z119]),(0,[z1,z2,z607,z4,z5,z119])]],
   [[(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z1,z2,z144,z4,z247,z6])],[(0,[z1,z1080,z3,z4,z5,z6]),(0,[z1081,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1082,z5,z6]),(0,[z1,z2,z1083,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1084])],[(0,[z1,z2,z3,z34,z5,z6])],[(0,[z1,z1085,z3,z4,z5,z6]),(0,[z10,z235,z3,z4,z11,z6])],[(0,[z90,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1086,z5,z6]),(0,[z1,z2,z146,z110,z3,z5]),(0,[z1,z2,z4,z5,z148,z119])],[(0,[z1,z2,z3,z1087,z5,z6]),(0,[z1,z2,z146,z3,z4,z247]),(0,[z1088,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z185,z5,z6]),(0,[z1,z2,z118,z3,z5,z175]),(0,[z1,z2,z21,z243,z45,z6]),(1,[z1,z2,z3,z935,z6])],[(0,[z1,z2,z493,z4,z5,z168]),(0,[z1,z3,z4,z5,z773,z6]),(0,[z1,z2,z3,z4,z1089,z6]),(0,[z1,z2,z191,z22,z262,z6]),(0,[z1,z2,z3,z4,z1090,z6]),(0,[z1,z2,z358,z185,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1091,z6]),(0,[z401,z2,z3,z4,z55,z6]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z2,z3,z1093,z5,z6]),(0,[z1,z2,z3,z4,z1094,z6])],[(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z1096,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1097]),(0,[z1,z2,z3,z4,z143,z9]),(0,[z1,z2,z335,z4,z247,z6]),(0,[z1,z2,z3,z1098,z5,z6])],[(0,[z1,z36,z3,z4,z5,z290]),(0,[z1,z159,z3,z44,z5,z6]),(0,[z1,z1099,z3,z4,z5,z6])],[(0,[z1,z61,z3,z4,z5,z124]),(0,[z1,z214,z3,z34,z5,z6]),(0,[z1,z2,z1100,z4,z5,z6]),(0,[z1,z2,z1101,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z9]),(0,[z1102,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z21,z358,z45,z6])],[(0,[z1,z2,z3,z4,z48,z290]),(0,[z1,z2,z246,z4,z32,z6]),(0,[z1,z2,z120,z4,z5,z6])],[(0,[z1,z1104,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z1105])],[],[(0,[z1,z2,z3,z4,z1106,z6]),(0,[z1,z2,z3,z4,z1107,z6]),(0,[z1,z1108,z3,z4,z5,z6]),(0,[z1,z1109,z3,z4,z5,z6]),(0,[z1,z2,z3,z1110,z5,z6]),(0,[z1,z2,z3,z5,z6,z1111])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 552) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 552).take 529) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1081)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [552, 529] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 165).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 165).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [165, 91] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

end PEqualNP.Outside.L_meta_39217

theorem PEqualNP.Outside.L_meta_39217 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4209043456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4209043456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39217.solve