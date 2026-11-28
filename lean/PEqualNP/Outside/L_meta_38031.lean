import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38031

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01000005403115c0#64 ++ 0x001000005403115c#64 ++ 0xbec5204fc1733fcf#64 ++ 0x7bec5204fc1733fc#64 : BitVec 256),
   (0x0200419302144c52#64 ++ 0x00200419302144c5#64 ++ 0x7dcac3b3069cccfe#64 ++ 0xf7dcac3b3069cccf#64 : BitVec 256),
   (0x34130c2c18e0b0a4#64 ++ 0x534130c2c18e0b0a#64 ++ 0xebb31c3c38e0f0fd#64 ++ 0xeebb31c3c38e0f0f#64 : BitVec 256),
   (0x582c16c02f00ea08#64 ++ 0x8582c16c02f00ea0#64 ++ 0xe7bc1fc03f00ff0b#64 ++ 0xde7bc1fc03f00ff0#64 : BitVec 256),
   (0x603fa00035ca0000#64 ++ 0xe603fa00035ca000#64 ++ 0x1fffe0003fff0007#64 ++ 0xc1fffe0003fff000#64 : BitVec 256),
   (0x803ffb7a80000000#64 ++ 0xf803ffb7a8000000#64 ++ 0xffbfffffc0000000#64 ++ 0x3ffbfffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec5204fc1733fcf 0x7bec5204fc1733fc

def z1 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcac3b3069cccfe 0xf7dcac3b3069cccf

def z2 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x00301c0038000000 0x000301c003800000

def z3 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c3c38e0f0fd 0xeebb31c3c38e0f0f

def z4 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03f00ff0b 0xde7bc1fc03f00ff0

def z5 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z6 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z7 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x0bb7200039e30005 0xc0bb7200039e3000

def z8 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffffffffffff0007 0xfffffffffffff000

def z9 : W := mkw 0xe13ffb7ff5fb15c0 0xfe13ffb7ff5fb15c 0xffffffffffff3fcf 0xfffffffffffff3fc

def z10 : W := mkw 0x0000000100100440 0x0000000010010044 0x3cc0000300100cce 0x73cc0000300100cc

def z11 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0xffcfe3ffc7ffffff 0xfffcfe3ffc7fffff

def z12 : W := mkw 0x803fba6880000000 0xf803fba688000000 0xbeb53c4fc0000000 0x3beb53c4fc000000

def z13 : W := mkw 0x3c131eec1ae0faac 0x53c131eec1ae0faa 0xebb31ffc38e0fffd 0xfebb31ffc38e0fff

def z14 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x7fffe0303fffc0ff 0xe7fffe0303fffc0f

def z15 : W := mkw 0x5a0004812f14ee5a 0x05a0004812f14ee5 0x004000003f9cffff 0xc004000003f9cfff

def z16 : W := mkw 0x03004117403515d2 0x003004117403515d 0xbec7e07fc1ff3fff 0x7bec7e07fc1ff3ff

def z17 : W := mkw 0x100004000800a000 0x0100004000800a00 0xe3b01c003800f009 0xce3b01c003800f00

def z18 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe0001fffc0000000 0x3e0001fffc000000

def z19 : W := mkw 0x7c3fbeec3feafaac 0xf7c3fbeec3feafaa 0xfffffffc3fffffff 0xffffffffc3ffffff

def z20 : W := mkw 0x4a2c53d327144e5a 0x84a2c53d327144e5 0x7dcec3f3079ccffe 0xf7dcec3f3079ccff

def z21 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1843e00000ff0004 0x01843e00000ff000

def z22 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7fcfe3b307ffccff 0xf7fcfe3b307ffccf

def z23 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0xbfbfe04fc0000000 0x3bfbfe04fc000000

def z24 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbd3fcfff00ff0b 0xfffbd3fcfff00ff0

def z25 : W := mkw 0x802c5b7a80000000 0x9802c5b7a8000000 0xe7bc1fffc0000000 0x3e7bc1fffc000000

def z26 : W := mkw 0x3400040418e0b0a4 0x03400040418e0b0a 0xe3b01c0038e0f0fd 0xce3b01c0038e0f0f

def z27 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x033fe0003fef0001 0x8033fe0003fef000

def z28 : W := mkw 0x633fe19777ff5dd2 0xe633fe19777ff5dd 0xffffe3ffffffffff 0xfffffe3fffffffff

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x1ec5200001730007 0x41ec520000173000

def z30 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe1321c3c3880f0f8 0xae1321c3c3880f0f

def z31 : W := mkw 0x813ffb7fc03115c0 0xf813ffb7fc03115c 0xffbfffffc0003fc8 0x3ffbfffffc0003fc

def z32 : W := mkw 0x0000411200000000 0x0000041120000000 0x1408c38300000000 0x11408c3830000000

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dcac000069c0006 0xc1dcac000069c000

def z34 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa205204fc1633fc9 0x3a205204fc1633fc

def z35 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x1c4ac3b3069c0cf6 0x31c4ac3b3069c0cf

def z36 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xe0001c3c0000f0f8 0x2e0001c3c0000f0f

def z37 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0bb3000038e00005 0xc0bb3000038e0000

def z38 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0xf40cffffc0000000 0x3f40cffffc000000

def z39 : W := mkw 0x15000c2d4831b5e4 0x115000c2d4831b5e 0xfec53c7fc173ffff 0x7fec53c7fc173fff

def z40 : W := mkw 0x012c1245403115c0 0x8012c1245403115c 0xfffd3fcfc1733fcf 0x7fffd3fcfc1733fc

def z41 : W := mkw 0x35130c2d58f1b5e4 0x535130c2d58f1b5e 0xebb31c7ff8e0fffd 0xfebb31c7ff8e0fff

def z42 : W := mkw 0x623fe19337de4c52 0xe623fe19337de4c5 0x7fffe3b33fffccff 0xf7fffe3b33fffccf

def z43 : W := mkw 0x743fac2c3deab0a4 0xf743fac2c3deab0a 0xfffffc3c3ffff0ff 0xefffffc3c3ffff0f

def z44 : W := mkw 0x402c000025000000 0x8402c00002500000 0x040c000007000002 0x0040c00000700000

def z45 : W := mkw 0x5c2c1eec2f20faac 0x95c2c1eec2f20faa 0xe7bc1ffc3f00fffb 0xfe7bc1ffc3f00fff

def z46 : W := mkw 0x34130c2d18f0b4e4 0x534130c2d18f0b4e 0xfff31c3f38f0fcff 0xffff31c3f38f0fcf

def z47 : W := mkw 0x823ffbfb82144c52 0xf823ffbfb82144c5 0xffffffffc69cccfe 0xfffffffffc69cccf

def z48 : W := mkw 0x01000005403115c0 0x001000005403115c 0x1841200fc07300c4 0x21841200fc07300c

def z49 : W := mkw 0x5a2c57d32f14ee5a 0x85a2c57d32f14ee5 0xf7fcdfc33f1cff0b 0xdf7fcdfc33f1cff0

def z50 : W := mkw 0x0000000100100440 0x0000000010010044 0x3ec5200301730ccf 0x73ec5200301730cc

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3b01c0000000000 0x0e3b01c000000000

def z52 : W := mkw 0x100004000800a000 0x0100004000800a00 0x000000003800f009 0xc000000003800f00

def z53 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0803000000e00004 0x00803000000e0000

def z54 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7d8ac3b30000ccf8 0x37d8ac3b30000ccf

def z55 : W := mkw 0x613fa00575fb15c0 0xe613fa00575fb15c 0xbfffe04fffff3fcf 0xfbfffe04fffff3fc

def z56 : W := mkw 0x3400040418e0b0a4 0x03400040418e0b0a 0xaa81000c38e0f0fd 0xeaa81000c38e0f0f

def z57 : W := mkw 0xa43ffb7e90e010a4 0xfa43ffb7e90e010a 0xffbfffffc0e000f4 0x3ffbfffffc0e000f

def z58 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbac1200fc07330cd 0x6bac1200fc07330c

def z59 : W := mkw 0x01000005403115c0 0x001000005403115c 0x14442043c1733fcf 0x514442043c1733fc

def z60 : W := mkw 0x580016c02f00ea08 0x0580016c02f00ea0 0xe0001fc03f00ff0b 0xde0001fc03f00ff0

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0x698200300080c0fc 0xe698200300080c0f

def z62 : W := mkw 0x35130c2d58f1b5e4 0x535130c2d58f1b5e 0xfff73c7ff9f3ffff 0xffff73c7ff9f3fff

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe85204fc0000000 0x3be85204fc000000

def z64 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x017ac0003fff0007 0xc017ac0003fff000

def z65 : W := mkw 0x8213e9bb82144c52 0x78213e9bb82144c5 0x7dcbe3bfc69cccfe 0xf7dcbe3bfc69cccf

def z66 : W := mkw 0x0100000040010100 0x0010000004001010 0x00042040c1030300 0x000042040c103030

def z67 : W := mkw 0xb53fff7fd8f1b5e4 0xfb53fff7fd8f1b5e 0xfffffffff9f3ffff 0xffffffffff9f3fff

def z68 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfff73c3c39f3f0ff 0xefff73c3c39f3f0f

def z69 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x167de0003f7f0003 0x0167de0003f7f000

def z70 : W := mkw 0x0000000000000000 0x0000000000000000 0x6588038000000000 0x1658803800000000

def z71 : W := mkw 0x8000e11280000000 0x28000e1128000000 0x1000e003c0000000 0x01000e003c000000

def z72 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0xe00003ffc000fff8 0x3e00003ffc000fff

def z73 : W := mkw 0x592c16c16f11ef48 0x8592c16c16f11ef4 0xf7fc3fc3ff13ff0b 0xdf7fc3fc3ff13ff0

def z74 : W := mkw 0x802cf35280000000 0xa802cf3528000000 0x7d8ee3f3c0000000 0x37d8ee3f3c000000

def z75 : W := mkw 0x2413a82c10ea10a4 0x72413a82c10ea10a 0x1843e03c00ff00f4 0x21843e03c00ff00f

def z76 : W := mkw 0x7c2c16c43fe0faac 0x87c2c16c43fe0faa 0xe7bc1fc03fe0ffff 0xde7bc1fc03fe0fff

def z77 : W := mkw 0x2113a00550fb15c0 0x62113a00550fb15c 0xbec7e04fc1ff3fcf 0x7bec7e04fc1ff3fc

def z78 : W := mkw 0x01000005403115c0 0x001000005403115c 0x0000000000003fc8 0x00000000000003fc

def z79 : W := mkw 0x37134dbf5af5fdf6 0x537134dbf5af5fdf 0xffffffffffffffff 0xffffffffffffffff

def z80 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x41321c303880c030 0x841321c303880c03

def z81 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0x40001fb000000000 0x040001fb00000000

def z82 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x0000038300000c00 0x10000038300000c0

def z83 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0xbe87e07fc0000000 0x3be87e07fc000000

def z84 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbffffffe8c0000 0xbffbffffffe8c000

def z85 : W := mkw 0x002c124000000000 0x8002c12400000000 0xe7bc1fc000000000 0x1e7bc1fc00000000

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x618000000000c008 0xc618000000000c00

def z87 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x027520003fff0007 0xc027520003fff000

def z88 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0xffbfffffff00ff0b 0xfffbfffffff00ff0

def z89 : W := mkw 0x813ffb7ec0211180 0xf813ffb7ec021118 0xffbfffffc1633301 0x3ffbfffffc163330

def z90 : W := mkw 0x01000005403115c0 0x001000005403115c 0x00400000007300c4 0x000400000007300c

def z91 : W := mkw 0x100004000800a000 0x0100004000800a00 0x41301c003800c000 0x841301c003800c00

def z92 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0x7dcbe3bfc6ffccfe 0xf7dcbe3bfc6ffccf

def z93 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0x000000003e00c000 0x8000000003e00c00

def z94 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa000004fc0003fc8 0x3a000004fc0003fc

def z95 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x013ac0003e8c0000 0x8013ac0003e8c000

def z96 : W := mkw 0x002c124000000000 0x8002c12400000000 0x82341c4000000000 0x082341c400000000

def z97 : W := mkw 0x592c16c56f31ffc8 0x8592c16c56f31ffc 0xfffd3fcfff73ffcf 0xffffd3fcfff73ffc

def z98 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0xffffffc03fffff0f 0xdffffffc03fffff0

def z99 : W := mkw 0x0200411300140452 0x0020041130014045 0x1842c033009c00f4 0x21842c033009c00f

def z100 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0x82341c4039003301 0x082341c403900330

def z101 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x00400000069cccfe 0xc00400000069cccf

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x03b0000038000001 0xc03b000003800000

def z103 : W := mkw 0x403fa000250a0000 0xe403fa000250a000 0x1fffe000071f0002 0x01fffe000071f000

def z104 : W := mkw 0x74130c2c3deab0a4 0x574130c2c3deab0a 0xebf31c3c3ffff0ff 0xeebf31c3c3ffff0f

def z105 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0xefbf1ffc3fe0ffff 0xfefbf1ffc3fe0fff

def z106 : W := mkw 0x0200419202044812 0x0020041920204481 0x400003b00000c030 0x0400003b00000c03

def z107 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x600003b30000ccf8 0x3600003b30000ccf

def z108 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x0235200039630001 0x0023520003963000

def z109 : W := mkw 0x002c124000000000 0x8002c12400000000 0x040c03c000000000 0x1040c03c00000000

def z110 : W := mkw 0xe03fba68b5ca0000 0xfe03fba68b5ca000 0x82353c4cf9630001 0x082353c4cf963000

def z111 : W := mkw 0x603fa00135da0440 0xe603fa00135da044 0x3fffe0033fff0ccf 0xf3fffe0033fff0cc

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0xa684004001003f0b 0x5a684004001003f0

def z113 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc1003f0b 0x7ffbfffffc1003f0

def z114 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x0803003c00e000f4 0x20803003c00e000f

def z115 : W := mkw 0x0100000140110540 0x0010000014011054 0x14442043c1130f02 0x114442043c1130f0

def z116 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xfe853fffc0000000 0x3fe853fffc000000

def z117 : W := mkw 0x36134dbf1af4fcf6 0x536134dbf1af4fcf 0xfffbdfbf3efcfcff 0xffffbdfbf3efcfcf

def z118 : W := mkw 0x0000000000000000 0x0000000000000000 0x1448c000061c0002 0x01448c000061c000

def z119 : W := mkw 0x492c12c567315fc8 0x8492c12c567315fc 0xbecd23cfc7733fcf 0x7becd23cfc7733fc

def z120 : W := mkw 0x3400040418e0b0a4 0x03400040418e0b0a 0x0000000038e0f0fd 0xc0000000038e0f0f

def z121 : W := mkw 0xb43fff7e98e0b0a4 0xfb43fff7e98e0b0a 0xffbffffff8e0f0fd 0xfffbffffff8e0f0f

def z122 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x69b21c303880c0fc 0xe69b21c303880c0f

def z123 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x594ac3b3069cc0f4 0xa594ac3b3069cc0f

def z124 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7cc003b30010ccfe 0x77cc003b30010ccf

def z125 : W := mkw 0x580004002d00a208 0x0580004002d00a20 0x0000000039003301 0x0000000003900330

def z126 : W := mkw 0x6100000575fb15c0 0x06100000575fb15c 0xbec5204fffff3fcf 0xfbec5204fffff3fc

def z127 : W := mkw 0x0200419202044812 0x0020041920204481 0x410ac3b0068cc030 0x8410ac3b0068cc03

def z128 : W := mkw 0x590004856f31ffc8 0x0590004856f31ffc 0x004000003f73ffcf 0xc004000003f73ffc

def z129 : W := mkw 0x802cf35280000000 0xa802cf3528000000 0xf7bcffc3c0000000 0x1f7bcffc3c000000

def z130 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x41381f803e00c000 0x841381f803e00c00

def z131 : W := mkw 0x813ffb7fc03115c0 0xf813ffb7fc03115c 0xffffffffc1733fcf 0x7ffffffffc1733fc

def z132 : W := mkw 0x0000008002004800 0x0000000800200480 0x658803800600cc0a 0xd658803800600cc0

def z133 : W := mkw 0x0000000400201080 0x0000000040020108 0xae85004c01603fcf 0x7ae85004c01603fc

def z134 : W := mkw 0x2513082d50f115e4 0x52513082d50f115e 0xbec7207fc1f33fff 0x7bec7207fc1f33ff

def z135 : W := mkw 0x0000000100100440 0x0000000010010044 0x2000000300000cc8 0x32000000300000cc

def z136 : W := mkw 0x482c12c027004a08 0x8482c12c027004a0 0x040c03c007000f02 0x1040c03c007000f0

def z137 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x144ce000071f0002 0x0144ce000071f000

def z138 : W := mkw 0xa03ffb7a90ca0000 0xfa03ffb7a90ca000 0xffffffffc0ff0004 0x3ffffffffc0ff000

def z139 : W := mkw 0x01000005403115c0 0x001000005403115c 0x0040000001733fcf 0x40040000001733fc

def z140 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x41321c3038e0f0fd 0xc41321c3038e0f0f

def z141 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xbfffe04fffff0007 0xfbfffe04fffff000

def z142 : W := mkw 0x01000005403115c0 0x001000005403115c 0x3cc1200fc0730cce 0x73cc1200fc0730cc

def z143 : W := mkw 0x803ff35280000000 0xe803ff3528000000 0x1fbfe3c3c0000000 0x11fbfe3c3c000000

def z144 : W := mkw 0x4a2c53d327144e5a 0x84a2c53d327144e5 0x144cc3c3071c0f02 0x1144cc3c3071c0f0

def z145 : W := mkw 0x01000005403115c0 0x001000005403115c 0xb444204fc1133fca 0x3b444204fc1133fc

def z146 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe3b01fc03800ff09 0xde3b01fc03800ff0

def z147 : W := mkw 0x402c124025000000 0x8402c12402500000 0xe7bc1fc03f000003 0xde7bc1fc03f00000

def z148 : W := mkw 0x34000c2c18e0b0a4 0x134000c2c18e0b0a 0xe0001c3c38e0f0fd 0xee0001c3c38e0f0f

def z149 : W := mkw 0x492c12c167114f48 0x8492c12c167114f4 0x144c23c3c7130f02 0x1144c23c3c7130f0

def z150 : W := mkw 0x0000411300100440 0x0000041130010044 0x7dcac3b300100cce 0x77dcac3b300100cc

def z151 : W := mkw 0x582c04802f00ea08 0x8582c04802f00ea0 0x07bc00003f00ff0b 0xc07bc00003f00ff0

def z152 : W := mkw 0x0100000440211180 0x0010000044021118 0x8205204cc1633301 0x08205204cc163330

def z153 : W := mkw 0x0013082c00201080 0x50013082c0020108 0xebb31c3c006030cd 0x6ebb31c3c006030c

def z154 : W := mkw 0x0000411200000000 0x0000041120000000 0x7d8ac3b300000000 0x37d8ac3b30000000

def z155 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x1448c383069cccfe 0xd1448c383069cccf

def z156 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbe85204fc0003fc8 0x3be85204fc0003fc

def z157 : W := mkw 0x5a2c57d32f14ee5a 0x85a2c57d32f14ee5 0xfffedff33f9cffff 0xffffedff33f9cfff

def z158 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x593bffbfc0000000 0x2593bffbfc000000

def z159 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x17fce0003f1f0003 0xc17fce0003f1f000

def z160 : W := mkw 0x203fa00010c00000 0xe203fa00010c0000 0x1fbfe00038e00005 0xc1fbfe00038e0000

def z161 : W := mkw 0xf43fff7ebdeab0a4 0xff43fff7ebdeab0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z162 : W := mkw 0x0000000400201080 0x0000000040020108 0xaa81000c006030cd 0x6aa81000c006030c

def z163 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x8a331c3c38e030f5 0x28a331c3c38e030f

def z164 : W := mkw 0x3413ac2c18eab0a4 0x73413ac2c18eab0a 0xfbf3fc3c38fff0fd 0xefbf3fc3c38fff0f

def z165 : W := mkw 0x80001a6880000000 0x180001a688000000 0x80001c4cc0000000 0x080001c4cc000000

def z166 : W := mkw 0xc83ffbfaa7004a08 0xfc83ffbfaa7004a0 0xffbfffffc7000f02 0x3ffbfffffc7000f0

def z167 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x453c1fc03f00cf02 0x9453c1fc03f00cf0

def z168 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x1448c383061c0c02 0x11448c383061c0c0

def z169 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x82311c0c38603001 0x082311c0c3860300

def z170 : W := mkw 0x01000005403115c0 0x001000005403115c 0xffc7207fc1f3ffff 0xfffc7207fc1f3fff

def z171 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbfcfe04fc7ff3fcf 0xfbfcfe04fc7ff3fc

def z172 : W := mkw 0x943fff7e8820b0a4 0xf943fff7e8820b0a 0xffbfffffc000f0f8 0x3ffbfffffc000f0f

def z173 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x004000003fff0007 0xc004000003fff000

def z174 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xebb73c7cf9e3f3fd 0xeebb73c7cf9e3f3f

def z175 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0132000038800000 0x8013200003880000

def z176 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xfd8adfffc0000000 0x3fd8adfffc000000

def z177 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x698203b30080ccfc 0xf698203b30080ccf

def z178 : W := mkw 0x3500040558f1b5e4 0x03500040558f1b5e 0xbec5204ff9f3ffff 0xfbec5204ff9f3fff

def z179 : W := mkw 0x002c000000000000 0x8002c00000000000 0x07bc000000000000 0x007bc00000000000

def z180 : W := mkw 0x603fa82835ca0000 0xf603fa82835ca000 0xfffffc3c3fff0007 0xefffffc3c3fff000

def z181 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0xe7bedff03f00ff0b 0xde7bedff03f00ff0

def z182 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc69c0006 0xfffffffffc69c000

def z183 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0x000000003f00ff0b 0xc000000003f00ff0

def z184 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe0001fc00000ff08 0x1e0001fc00000ff0

def z185 : W := mkw 0x613fa00575fb15c0 0xe613fa00575fb15c 0x1fffe00fffff00c7 0xe1fffe00fffff00c

def z186 : W := mkw 0x01000005403115c0 0x001000005403115c 0xaac1000c01733fcf 0x6aac1000c01733fc

def z187 : W := mkw 0x5a2c57d32f14ee5a 0x85a2c57d32f14ee5 0xe7bc1ff33f00fffb 0xfe7bc1ff33f00fff

def z188 : W := mkw 0x802cf35280000000 0xa802cf3528000000 0x140ce3c3c0000000 0x1140ce3c3c000000

def z189 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fbfe00000000000 0x01fbfe0000000000

def z190 : W := mkw 0x2013082810c00000 0x52013082810c0000 0xebb31c3c38e00005 0xeebb31c3c38e0000

def z191 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0x1803e03fc0000000 0x21803e03fc000000

def z192 : W := mkw 0x01004117403115c0 0x001004117403115c 0xffcfe3ffc1733fcf 0x7ffcfe3ffc1733fc

def z193 : W := mkw 0x01000005403115c0 0x001000005403115c 0x1841200fc1733fcf 0x61841200fc1733fc

def z194 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x5fbfffb000000000 0x05fbfffb00000000

def z195 : W := mkw 0x002ca00000000000 0xa002ca0000000000 0x140ce00000000000 0x0140ce0000000000

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x28800000000000cc 0x628800000000000c

def z197 : W := mkw 0x0000000100100440 0x0000000010010044 0x18400003001000c4 0x218400003001000c

def z198 : W := mkw 0x0200419702345cd2 0x00200419702345cd 0xffcbc3bf06fcfcff 0xfffcbc3bf06fcfcf

def z199 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x963dffcfc0000000 0x1963dffcfc000000

def z200 : W := mkw 0x01000005403115c0 0x001000005403115c 0xb841204fc0733fcc 0x3b841204fc0733fc

def z201 : W := mkw 0x0000000100100440 0x0000000010010044 0x0040000000100cce 0x40040000000100cc

def z202 : W := mkw 0x833ffbffc2355dd2 0xf833ffbffc2355dd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z203 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0xe7bedfc03f8cff0b 0xde7bedfc03f8cff0

def z204 : W := mkw 0x0113082d403115c0 0x50113082d403115c 0xfff73c7fc1733fcf 0x7fff73c7fc1733fc

def z205 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb31c3c00000000 0x2ebb31c3c0000000

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z207 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x0004200001030000 0x0000420000103000

def z208 : W := mkw 0x402c000025000000 0x8402c00002500000 0x1ffec0003f9c0007 0xc1ffec0003f9c000

def z209 : W := mkw 0x0000411200000000 0x0000041120000000 0x7dcac3b3069c0006 0xf7dcac3b3069c000

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0xbec5204fc1730007 0x7bec5204fc173000

def z211 : W := mkw 0x01000005403115c0 0x001000005403115c 0x1ec5200001733fcf 0x41ec5200001733fc

def z212 : W := mkw 0x82005bfb82144c52 0x182005bfb82144c5 0xfdcadfffc69cccfe 0xffdcadfffc69cccf

def z213 : W := mkw 0x0000124000000000 0x0000012400000000 0xe0001fc000000000 0x1e0001fc00000000

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x1444200001130002 0x0144420000113000

def z215 : W := mkw 0x0000000100100440 0x0000000010010044 0x3dcac003069c0cce 0xf3dcac003069c0cc

def z216 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0x413adfb03e8c0000 0x8413adfb03e8c000

def z217 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x000000000000ccf8 0x0000000000000ccf

def z218 : W := mkw 0x0200419202044812 0x0020041920204481 0x0008c380060c0000 0x00008c380060c000

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e85200000000000 0x01e8520000000000

def z220 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbe1ff03f80ffff 0xfefbe1ff03f80fff

def z221 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xf7fcffc03f1fff0b 0xdf7fcffc03f1fff0

def z222 : W := mkw 0x8000535280000000 0x0800053528000000 0x000003c3c0000000 0x1000003c3c000000

def z223 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe2341fc03900ff09 0x1e2341fc03900ff0

def z224 : W := mkw 0x813ffb7bc0110540 0xf813ffb7bc011054 0xffffffffc1130f02 0x3ffffffffc1130f0

def z225 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe1381fc03e00ff08 0x9e1381fc03e00ff0

def z226 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x413adfb000000000 0x0413adfb00000000

def z227 : W := mkw 0x0100000440211180 0x0010000044021118 0xaa85204cc16333cd 0x6aa85204cc16333c

def z228 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0x658803803f00ff0b 0xd658803803f00ff0

def z229 : W := mkw 0xd93fffffef31ffc8 0xfd93fffffef31ffc 0xffffffffff73ffcf 0xfffffffffff73ffc

def z230 : W := mkw 0x40000000250a0000 0x040000000250a000 0x00400000071f0002 0x000400000071f000

def z231 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xaab11c0c386030cd 0x6aab11c0c386030c

def z232 : W := mkw 0x0000008002004800 0x0000000800200480 0x6d8a03b00680ccfe 0xf6d8a03b00680ccf

def z233 : W := mkw 0x14130c2c0820b0a4 0x514130c2c0820b0a 0xebb31c3c0000f0f8 0x2ebb31c3c0000f0f

def z234 : W := mkw 0x802cf35280000000 0xa802cf3528000000 0xbe8de3cfc0000000 0x3be8de3cfc000000

def z235 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x82311c0c38e0f0fd 0xc82311c0c38e0f0f

def z236 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x157ee0003f9f0002 0x8157ee0003f9f000

def z237 : W := mkw 0x14000c280800a024 0x114000c280800a02 0x40001c300000c030 0x040001c300000c03

def z238 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1a77e00039ff0005 0x01a77e00039ff000

def z239 : W := mkw 0x740004043deab0a4 0x0740004043deab0a 0x004000003ffff0ff 0xc004000003ffff0f

def z240 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x414ac3b0069cccfe 0xc414ac3b0069cccf

def z241 : W := mkw 0x080012c002004a08 0x0080012c002004a0 0x000003c000000f00 0x1000003c000000f0

def z242 : W := mkw 0x0000411200000000 0x0000041120000000 0x7d8ac3b30080c0fc 0xf7d8ac3b30080c0f

def z243 : W := mkw 0x6013000035ca0000 0x46013000035ca000 0x0bf300003fff0007 0xc0bf300003fff000

def z244 : W := mkw 0x592c16c46f21fb88 0x8592c16c46f21fb8 0xe7bd3fccff63ff0b 0xde7bd3fccff63ff0

def z245 : W := mkw 0x482c12c027004a08 0x8482c12c027004a0 0xa68c03c007003f0b 0x5a68c03c007003f0

def z246 : W := mkw 0x81005b7fc03115c0 0x181005b7fc03115c 0xe0001fffc0003fc8 0x3e0001fffc0003fc

def z247 : W := mkw 0x100004800a00e800 0x0100004800a00e80 0xe7b81f803e00fc0b 0xde7b81f803e00fc0

def z248 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xffbffffff8e00005 0xfffbffffff8e0000

def z249 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x49331c3c38e0c0f4 0xa49331c3c38e0c0f

def z250 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0x87bc1c403f003303 0xc87bc1c403f00330

def z251 : W := mkw 0x803ffb7e80201080 0xf803ffb7e8020108 0xffbfffffc06030cd 0x7ffbfffffc06030c

def z252 : W := mkw 0x743fac2c3deab0a4 0xf743fac2c3deab0a 0xebbbdc3c3eecf0fd 0xeebbbdc3c3eecf0f

def z253 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x9a37fc7fc0000000 0x29a37fc7fc000000

def z254 : W := mkw 0x623fe11335de0452 0xe623fe11335de045 0x1fffe0333fff00f7 0xe1fffe0333fff00f

def z255 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x0002c000008c0000 0x00002c000008c000

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000004fc0000000 0x3a000004fc000000

def z257 : W := mkw 0x7c3f1e6c3de0b2ac 0xd7c3f1e6c3de0b2a 0xebb71c7c39e0f3fd 0xeebb71c7c39e0f3f

def z258 : W := mkw 0x803fba6880000000 0xf803fba688000000 0x9fbffc4cc0000000 0x09fbffc4cc000000

def z259 : W := mkw 0x403fa00025000000 0xe403fa0002500000 0x1fbfe0003f000003 0xc1fbfe0003f00000

def z260 : W := mkw 0x8113e93fc03115c0 0x78113e93fc03115c 0xbec7e07fc1733fcf 0x7bec7e07fc1733fc

def z261 : W := mkw 0x3400040418e0b0a4 0x03400040418e0b0a 0x0000000038603001 0x0000000003860300

def z262 : W := mkw 0x813fba6dc03115c0 0xf813fba6dc03115c 0xbef53c4fc1733fcf 0x7bef53c4fc1733fc

def z263 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x4bb31c3038e0c035 0xc4bb31c3038e0c03

def z264 : W := mkw 0x0000411200000000 0x0000041120000000 0x1802c03300000000 0x21802c0330000000

def z265 : W := mkw 0x743fac283dcaa024 0xf743fac283dcaa02 0x413adc303e8cc030 0x8413adc303e8cc03

def z266 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x1dcac000069cccfe 0xc1dcac000069cccf

def z267 : W := mkw 0x0300419342154d52 0x00300419342154d5 0x7dcee3f3c79fcffe 0xf7dcee3f3c79fcff

def z268 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xefb71c7c39e0ffff 0xfefb71c7c39e0fff

def z269 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x07bec0003f8c0003 0xc07bec0003f8c000

def z270 : W := mkw 0x422c419327144c52 0x8422c419327144c5 0x7ffec3b33f9cccff 0xf7ffec3b33f9cccf

def z271 : W := mkw 0x0300008542355dd2 0x00300008542355dd 0xbec5204fc7ffffff 0xfbec5204fc7fffff

def z272 : W := mkw 0x120045930a14ec52 0x0120045930a14ec5 0xfffadfb33e9cfcff 0xffffadfb33e9cfcf

def z273 : W := mkw 0x360045971af4fcf6 0x0360045971af4fcf 0x7dcac3b33efcfcff 0xf7dcac3b33efcfcf

def z274 : W := mkw 0x0000008002004800 0x0000000800200480 0xe78c03c00700ff0b 0xde78c03c00700ff0

def z275 : W := mkw 0x3013040018c0a000 0x43013040018c0a00 0xebb31c0038e0f00d 0xcebb31c0038e0f00

def z276 : W := mkw 0x100004040820b080 0x0100004040820b08 0xebb11c0c3860f0cd 0xeebb11c0c3860f0c

def z277 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcfe3ffc69cccfe 0xfffcfe3ffc69cccf

def z278 : W := mkw 0x002c124000000000 0x8002c12400000000 0xe7bc1fc001003f0b 0x5e7bc1fc001003f0

def z279 : W := mkw 0x803fba6880000000 0xf803fba688000000 0x82353c4cc0000000 0x082353c4cc000000

def z280 : W := mkw 0x002c124000000000 0x8002c12400000000 0xffbd3fcfc0000000 0x3ffbd3fcfc000000

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x6982003000000000 0x2698200300000000

def z282 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa6c4004001733fcf 0x5a6c4004001733fc

def z283 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0xe7bd1fcc3f60ff0b 0xde7bd1fcc3f60ff0

def z284 : W := mkw 0x402c000025000000 0x8402c00002500000 0x07bc00003f000003 0xc07bc00003f00000

def z285 : W := mkw 0x0013082800000000 0x5001308280000000 0xffb73c7fc0000000 0x3ffb73c7fc000000

def z286 : W := mkw 0x0200419202044812 0x0020041920204481 0x698ac3b0068cc0fc 0xe698ac3b0068cc0f

def z287 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x1c0fe3ffc0000000 0x31c0fe3ffc000000

def z288 : W := mkw 0x16004dbf0a34fcf6 0x116004dbf0a34fcf 0xfdcadfbf069cfcfe 0xffdcadfbf069cfcf

def z289 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xbfffe0403fff3f0f 0xdbfffe0403fff3f0

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000080c0fc 0xc000000000080c0f

def z291 : W := mkw 0x2213419312d44c52 0x42213419312d44c5 0x7ffbc3b33efcccff 0xf7ffbc3b33efcccf

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x7dcac030069cc0fe 0xe7dcac030069cc0f

def z293 : W := mkw 0x102c16400800a000 0x8102c16400800a00 0xe7bc1fc03800f009 0xde7bc1fc03800f00

def z294 : W := mkw 0x623fe19237ce4812 0xe623fe19237ce481 0x5fffe3b03fffc037 0xc5fffe3b03fffc03

def z295 : W := mkw 0x2413082810c00024 0x52413082810c0002 0x0002003000800030 0x0000200300080003

def z296 : W := mkw 0x822cf3d382144c52 0xa822cf3d382144c5 0x7dcee3f3c69cccfe 0xf7dcee3f3c69cccf

def z297 : W := mkw 0x343f1e6c18e0b0a4 0xd343f1e6c18e0b0a 0xefbf1ffc38e0f0fd 0xfefbf1ffc38e0f0f

def z298 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe2353fffc0000000 0x3e2353fffc000000

def z299 : W := mkw 0x0400082c002010a4 0x10400082c002010a 0x0000003c000000f0 0x20000003c000000f

def z300 : W := mkw 0x0000008002004800 0x0000000800200480 0x410803800600c000 0x8410803800600c00

def z301 : W := mkw 0x482c124025000208 0x8482c12402500020 0x0004004001000300 0x0000400400100030

def z302 : W := mkw 0x583f1ee82f00ea08 0xd583f1ee82f00ea0 0xefbf1ffc3f00ff0b 0xfefbf1ffc3f00ff0

def z303 : W := mkw 0x002c124000000000 0x8002c12400000000 0x41381f8000000000 0x041381f800000000

def z304 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x000000003e8c0000 0x8000000003e8c000

def z305 : W := mkw 0x003fe11200000000 0xe003fe1120000000 0x7fbfe3b300000000 0x37fbfe3b30000000

def z306 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c3c38603001 0x2ebb31c3c3860300

def z307 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xc3331c3c38e0f031 0x8c3331c3c38e0f03

def z308 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x41381f803f00ff0b 0xc41381f803f00ff0

def z309 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffedfc03f9cff0f 0xdfffedfc03f9cff0

def z310 : W := mkw 0x0000a000000a0000 0x20000a000000a000 0x1040e000001f0000 0x01040e000001f000

def z311 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x554ac3b3069ccc32 0x9554ac3b3069ccc3

def z312 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x197be0003eff0004 0x8197be0003eff000

def z313 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x863c1fc03f003f03 0x1863c1fc03f003f0

def z314 : W := mkw 0x602ca00035ca0000 0xa602ca00035ca000 0x144ce0003fff0007 0xc144ce0003fff000

def z315 : W := mkw 0x0100000140110540 0x0010000014011054 0xbec5204fc1130f02 0x3bec5204fc1130f0

def z316 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x47bc1f803f00c003 0xc47bc1f803f00c00

def z317 : W := mkw 0xb43fff7e98e0b0a4 0xfb43fff7e98e0b0a 0xebbbdfbc38e0f0fd 0xeebbbdfbc38e0f0f

def z318 : W := mkw 0x3400040418e0b0a4 0x03400040418e0b0a 0x6982003038e0f0fd 0xe6982003038e0f0f

def z319 : W := mkw 0x022c53d302144c52 0x8022c53d302144c5 0xfffedff3069cccfe 0xffffedff3069cccf

def z320 : W := mkw 0x743fa4043deab0a4 0xe743fa4043deab0a 0x1fffe0003ffff0ff 0xc1fffe0003ffff0f

def z321 : W := mkw 0x783fb6403dcaa208 0xe783fb6403dcaa20 0x9ffffc403fff3307 0xc9ffffc403fff330

def z322 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe2311c3c3860f0f9 0x2e2311c3c3860f0f

def z323 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x1dcac0003fff0007 0xc1dcac0003fff000

def z324 : W := mkw 0x5a2c57d32f14ee5a 0x85a2c57d32f14ee5 0x7dfadfb33e9cccfe 0xf7dfadfb33e9cccf

def z325 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x610ac3b3068cccf8 0xb610ac3b3068cccf

def z326 : W := mkw 0x2013000410e01080 0x42013000410e0108 0xabb3000c38e030cd 0xeabb3000c38e030c

def z327 : W := mkw 0x8213e93b80140452 0x78213e93b8014045 0x1843e03fc09c00f4 0x21843e03fc09c00f

def z328 : W := mkw 0x0000000400201080 0x0000000040020108 0xbec5200c017330cf 0x6bec5200c017330c

def z329 : W := mkw 0x94005f7e8820b0a4 0x194005f7e8820b0a 0xe0001fffc000f0f8 0x3e0001fffc000f0f

def z330 : W := mkw 0x8000493a80000000 0x18000493a8000000 0x0000003fc0000000 0x20000003fc000000

def z331 : W := mkw 0x0000000400201080 0x0000000040020108 0x8201000c00603001 0x08201000c0060300

def z332 : W := mkw 0x6013a00035ca0000 0x66013a00035ca000 0x1843e0003fff0007 0xc1843e0003fff000

def z333 : W := mkw 0x2000000010c00000 0x02000000010c0000 0x0000000038e00005 0xc0000000038e0000

def z334 : W := mkw 0x180004800a00ea08 0x0180004800a00ea0 0x000000000000ff08 0x0000000000000ff0

def z335 : W := mkw 0xc02cf352a50a0000 0xac02cf352a50a000 0x144ce3c3c71f0002 0x1144ce3c3c71f000

def z336 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x0bbbc0003eec0005 0xc0bbbc0003eec000

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x0982000000800004 0xc098200000080000

def z338 : W := mkw 0x623fe19337de4c52 0xe623fe19337de4c5 0x1fffe3833fff0c07 0xd1fffe3833fff0c0

def z339 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x0235200000000000 0x0023520000000000

def z340 : W := mkw 0x190016c54a31ffc8 0x0190016c54a31ffc 0xe0001fcfc000ffc8 0x3e0001fcfc000ffc

def z341 : W := mkw 0xb43fff7e98e0b0a4 0xfb43fff7e98e0b0a 0xffbffffff8603001 0x3ffbffffff860300

def z342 : W := mkw 0x803ffbfa82004800 0xf803ffbfa8200480 0xffbfffffc600cc0a 0xfffbfffffc600cc0

def z343 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffd3fc03f73ff0f 0xdfffd3fc03f73ff0

def z344 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe40c1fc00700ff0a 0x1e40c1fc00700ff0

def z345 : W := mkw 0x803fba6880000000 0xf803fba688000000 0xebb73c7cc0000000 0x2ebb73c7cc000000

def z346 : W := mkw 0x01000005403115c0 0x001000005403115c 0x1ec5200fc17300c7 0x61ec5200fc17300c

def z347 : W := mkw 0x0000082800000000 0x1000008280000000 0xe0001c3c00000000 0x2e0001c3c0000000

def z348 : W := mkw 0x803ffb7b80100440 0xf803ffb7b8010044 0xffffffffc0100cce 0x7ffffffffc0100cc

def z349 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc080c0fc 0xfffbfffffc080c0f

def z350 : W := mkw 0x0000000100100440 0x0000000010010044 0xbec4004301103fcf 0x7bec4004301103fc

def z351 : W := mkw 0x4000000025000000 0x0400000002500000 0x000000003f000003 0xc000000003f00000

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0x410200300080c030 0x8410200300080c03

def z353 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec5204fc07300c4 0x3bec5204fc07300c

def z354 : W := mkw 0x36134dbe1ae4f8b6 0x536134dbe1ae4f8b 0xebbbdfbc3eecf0fd 0xeebbbdfbc3eecf0f

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0xa280000000003009 0x4a28000000000300

def z356 : W := mkw 0x783f16c03fc0ea08 0xc783f16c03fc0ea0 0xefbf1fc03fe0ff0f 0xdefbf1fc03fe0ff0

def z357 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe3b11c0c3860f009 0xce3b11c0c3860f00

def z358 : W := mkw 0x7c3f1ee83fc0ea2c 0xd7c3f1ee83fc0ea2 0x413a1fb03e80c030 0x8413a1fb03e80c03

def z359 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7842c3b3009cccfc 0x37842c3b3009cccf

def z360 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b81f803e00f009 0xce3b81f803e00f00

def z361 : W := mkw 0x36134dbb1ad4ec76 0x536134dbb1ad4ec7 0x7dfadfb33e9cccfe 0xf7dfadfb33e9cccf

def z362 : W := mkw 0x592c16456d31b7c8 0x8592c16456d31b7c 0xbef53c4ff9733fcf 0x7bef53c4ff9733fc

def z363 : W := mkw 0x03004117403515d2 0x003004117403515d 0x1843e03fc0ff00f4 0x21843e03fc0ff00f

def z364 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x553efff3c0000000 0x1553efff3c000000

def z365 : W := mkw 0x140004040820b0a4 0x0140004040820b0a 0x000000000000f0f8 0x0000000000000f0f

def z366 : W := mkw 0x0100000440211180 0x0010000044021118 0x0000000001633301 0x0000000000163330

def z367 : W := mkw 0x592c16c56f31ffc8 0x8592c16c56f31ffc 0xe7bc1fcfff00ffcb 0xfe7bc1fcfff00ffc

def z368 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0x413adf803e8cc000 0x8413adf803e8cc00

def z369 : W := mkw 0x0000000400201080 0x0000000040020108 0xa000000c000030c8 0x2a000000c000030c

def z370 : W := mkw 0x7c3f1ee83fc0ea2c 0xd7c3f1ee83fc0ea2 0xe7be1ff03f80ff3b 0xde7be1ff03f80ff3

def z371 : W := mkw 0xb413ed3e98e0b0a4 0x7b413ed3e98e0b0a 0xfbb3fc3ff8e0f0fd 0xefbb3fc3ff8e0f0f

def z372 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xffb73c7ff8e0f0fd 0xfffb73c7ff8e0f0f

def z373 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0xfec523ffc173ffff 0x7fec523ffc173fff

def z374 : W := mkw 0xa413e93e90e010a4 0x7a413e93e90e010a 0x1803e03fc0e000f4 0x21803e03fc0e000f

def z375 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa684004fc1003fcb 0x7a684004fc1003fc

def z376 : W := mkw 0x482c12c027004a08 0x8482c12c027004a0 0x658c03c00700cf0a 0xd658c03c00700cf0

def z377 : W := mkw 0x8013a82880000000 0x78013a8288000000 0x0001200cc0000000 0x00001200cc000000

def z378 : W := mkw 0xe03fe93ab5ca0000 0xfe03fe93ab5ca000 0x1fffe03fffff0007 0xe1fffe03fffff000

def z379 : W := mkw 0x36134dba1ac4e836 0x536134dba1ac4e83 0x413adfb03e8cc030 0x8413adfb03e8cc03

def z380 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc1730007 0x7ffffffffc173000

def z381 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xea811c3c0060f0fd 0x6ea811c3c0060f0f

def z382 : W := mkw 0x412c0005653115c0 0x8412c0005653115c 0xbffd204fff733fcf 0xfbffd204fff733fc

def z383 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffbfffffff000003 0xfffbfffffff00000

def z384 : W := mkw 0x203fa00010ca0000 0xe203fa00010ca000 0x1fffe00000ff0004 0x01fffe00000ff000

def z385 : W := mkw 0x34130cac1ae0f8a4 0x534130cac1ae0f8a 0xefbb1fbc3ee0fcff 0xfefbb1fbc3ee0fcf

def z386 : W := mkw 0x36134dbf1af4fcf6 0x536134dbf1af4fcf 0xebb31fbf38e0fcfd 0xfebb31fbf38e0fcf

def z387 : W := mkw 0x2113a00550fb15c0 0x62113a00550fb15c 0x1843e00fc0ff00c4 0x21843e00fc0ff00c

def z388 : W := mkw 0xc03ffb7aa50a0000 0xfc03ffb7aa50a000 0xffffffffc71f0002 0x3ffffffffc71f000

def z389 : W := mkw 0x3413040418e0b0a4 0x43413040418e0b0a 0x0bb3000038e0f0fd 0xc0bb3000038e0f0f

def z390 : W := mkw 0x5a2c16c12f14ee5a 0x85a2c16c12f14ee5 0xe7fc1fc03f9cffff 0xde7fc1fc03f9cfff

def z391 : W := mkw 0x603f000035c00000 0xc603f000035c0000 0x0fbf00003fe00007 0xc0fbf00003fe0000

def z392 : W := mkw 0x4800008027004a08 0x04800008027004a0 0x0000000007000f02 0x00000000007000f0

def z393 : W := mkw 0xb4135f7e98e0b0a4 0x5b4135f7e98e0b0a 0xebb31ffff8e0f0fd 0xfebb31ffff8e0f0f

def z394 : W := mkw 0x01000005403115c0 0x001000005403115c 0x0000000fc00000c0 0x20000000fc00000c

def z395 : W := mkw 0x16004dbf0a34fcf6 0x116004dbf0a34fcf 0xe0001fbf0000fcf8 0x3e0001fbf0000fcf

def z396 : W := mkw 0x7a3ff7d33fdeee5a 0xe7a3ff7d33fdeee5 0xfffffff33fffffff 0xffffffff33ffffff

def z397 : W := mkw 0xb43fbe6c98e0b0a4 0xfb43fbe6c98e0b0a 0xebb73c7cf8e0f0fd 0xeebb73c7cf8e0f0f

def z398 : W := mkw 0xe23ffbfbb7de4c52 0xfe23ffbfbb7de4c5 0xffffffffffffccff 0xfffffffffffffccf

def z399 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x3cc8c383061c0cce 0x73cc8c383061c0cc

def z400 : W := mkw 0x01000005403115c0 0x001000005403115c 0x9a45204fc17333c5 0x29a45204fc17333c

def z401 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe000069c0006 0xc1fffe000069c000

def z402 : W := mkw 0xf83ffffabfcaea08 0xff83ffffabfcaea0 0xffffffffffffff0f 0xfffffffffffffff0

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c80000300000000 0x33c8000030000000

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x0205200001630001 0x0020520000163000

def z405 : W := mkw 0x482c12c027004a08 0x8482c12c027004a0 0x0008038006000000 0x0000803800600000

def z406 : W := mkw 0x753fac2d7dfbb5e4 0xf753fac2d7dfbb5e 0xfffffc7fffffffff 0xffffffc7ffffffff

def z407 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbcc0004fc0103fce 0x7bcc0004fc0103fc

def z408 : W := mkw 0x01000005403115c0 0x001000005403115c 0x8245204cc1733fcf 0x48245204cc1733fc

def z409 : W := mkw 0x2213e19312de4c52 0x62213e19312de4c5 0x7dcbe3b306ffccfe 0xf7dcbe3b306ffccf

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x2480000000000c0a 0x52480000000000c0

def z411 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x040c03c03f00ff0b 0xd040c03c03f00ff0

def z412 : W := mkw 0x823ffbfb82144c52 0xf823ffbfb82144c5 0xffbfffffc000ccf8 0x3ffbfffffc000ccf

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0xbec5204001733f0f 0x5bec5204001733f0

def z414 : W := mkw 0x803fe93a80000000 0xf803fe93a8000000 0x1fbfe03fc0000000 0x21fbfe03fc000000

def z415 : W := mkw 0x743fac2c3deab0a4 0xf743fac2c3deab0a 0x9ffffc0c3fff3007 0xc9ffffc0c3fff300

def z416 : W := mkw 0x803fba6880000000 0xf803fba688000000 0xe7bd3fccc0000000 0x1e7bd3fccc000000

def z417 : W := mkw 0x983ffffa8a00ea08 0xf983ffffa8a00ea0 0xffbfffffc000ff08 0x3ffbfffffc000ff0

def z418 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03e00c000 0x9e7bc1fc03e00c00

def z419 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0xbecde3cfc77f3fcf 0x7becde3cfc77f3fc

def z420 : W := mkw 0x783fb6403dcaa208 0xe783fb6403dcaa20 0x82353c4039633301 0x082353c403963330

def z421 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa040004fc1733fcf 0x7a040004fc1733fc

def z422 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xebbbdfbc00000000 0x2ebbbdfbc0000000

def z423 : W := mkw 0x813fba6cc0211180 0xf813fba6cc021118 0x82353c4cc1633301 0x082353c4cc163330

def z424 : W := mkw 0xd83fff7aad00a208 0xfd83fff7aad00a20 0xffbffffff9003301 0x3ffbffffff900330

def z425 : W := mkw 0xa013e93a90ca0000 0x7a013e93a90ca000 0x1843e03fc0ff0004 0x21843e03fc0ff000

def z426 : W := mkw 0x2513082d50f115e4 0x52513082d50f115e 0x1843203fc0f300f4 0x21843203fc0f300f

def z427 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0xf803ffffc0000000 0x3f803ffffc000000

def z428 : W := mkw 0x5b2c57d76f35ffda 0x85b2c57d76f35ffd 0xffffffffffffffff 0xffffffffffffffff

def z429 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0x7dcac3b307ffffff 0xf7dcac3b307fffff

def z430 : W := mkw 0x0013493a00000000 0x50013493a0000000 0xffbbdfbf00000000 0x3ffbbdfbf0000000

def z431 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0xe3b41c403900f309 0xce3b41c403900f30

def z432 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0xe7bc1fc039003301 0x1e7bc1fc03900330

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x1841200000730004 0x0184120000073000

def z434 : W := mkw 0x683fb2c037ca4a08 0xe683fb2c037ca4a0 0x1fffe3c03fff0f07 0xd1fffe3c03fff0f0

def z435 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0xaa83003c00e030fd 0x6aa83003c00e030f

def z436 : W := mkw 0x0100000140110540 0x0010000014011054 0x1ec52043c1730f07 0x51ec52043c1730f0

def z437 : W := mkw 0x6200008137de4c52 0x06200008137de4c5 0x004000003fffccff 0xc004000003fffccf

def z438 : W := mkw 0x0000000100100440 0x0000000010010044 0xbec5204fc0100cce 0x7bec5204fc0100cc

def z439 : W := mkw 0x643fa82c35ea10a4 0xf643fa82c35ea10a 0x1fffe03c3fff00f7 0xe1fffe03c3fff00f

def z440 : W := mkw 0x5a0045932f14ee5a 0x05a0045932f14ee5 0x7dcac3b33f9cffff 0xf7dcac3b33f9cfff

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x08020030008000f4 0x208020030008000f

def z442 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x1dcee000079f0006 0xc1dcee000079f000

def z443 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x0000000039630001 0x0000000003963000

def z444 : W := mkw 0x0200411300140452 0x0020041130014045 0x1dcac033069c00f6 0xe1dcac033069c00f

def z445 : W := mkw 0x0300419342154d52 0x00300419342154d5 0x144ce3c3c71f0f02 0x1144ce3c3c71f0f0

def z446 : W := mkw 0x5a2c57d22f04ea1a 0x85a2c57d22f04ea1 0xe7bedff03f8cff3b 0xde7bedff03f8cff3

def z447 : W := mkw 0x0200008002044812 0x0020000800204481 0x00000000068cc030 0x800000000068cc03

def z448 : W := mkw 0x592c16c56f31ffc8 0x8592c16c56f31ffc 0xe7fc1fc03f73ffcf 0xde7fc1fc03f73ffc

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x1842c000009c0004 0x01842c000009c000

def z450 : W := mkw 0x01000005403115c0 0x001000005403115c 0x1c45204fc1730fc6 0x31c45204fc1730fc

def z451 : W := mkw 0x013fa005403115c0 0xe013fa005403115c 0xbfffe04fc1733fcf 0x7bfffe04fc1733fc

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001003f0b 0x40000000001003f0

def z453 : W := mkw 0x35130c2d58f1b5e4 0x535130c2d58f1b5e 0xebf31c3c39f3ffff 0xeebf31c3c39f3fff

def z454 : W := mkw 0x482cb2c0270a4a08 0xa482cb2c0270a4a0 0x144ce3c0071f0f02 0x1144ce3c0071f0f0

def z455 : W := mkw 0x0100000440211180 0x0010000044021118 0x0001200cc0630000 0x00001200cc063000

def z456 : W := mkw 0x813ffb7fc03115c0 0xf813ffb7fc03115c 0xffffffffc07300c4 0x3ffffffffc07300c

def z457 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1bf3e00038ff0005 0xc1bf3e00038ff000

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000004000003f08 0x1a000004000003f0

def z459 : W := mkw 0x80135b7a80000000 0x580135b7a8000000 0xebb31fffc0000000 0x3ebb31fffc000000

def z460 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x0803003c38e0f0fd 0xe0803003c38e0f0f

def z461 : W := mkw 0x0000411200000000 0x0000041120000000 0x600003b300000000 0x3600003b30000000

def z462 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xe3b01c3c3800f0f9 0xee3b01c3c3800f0f

def z463 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0xebb31c3c00e000f4 0x2ebb31c3c00e000f

def z464 : W := mkw 0x0000411200000000 0x0000041120000000 0x410ac3b000000000 0x0410ac3b00000000

def z465 : W := mkw 0x412ca001651b0540 0xa412ca001651b054 0x144ce043c71f0f02 0x1144ce043c71f0f0

def z466 : W := mkw 0x100004000800a000 0x0100004000800a00 0xebb21c303880f0fd 0xeebb21c303880f0f

def z467 : W := mkw 0x3500040558f1b5e4 0x03500040558f1b5e 0x0040000039f3ffff 0xc0040000039f3fff

def z468 : W := mkw 0x7c130cac3fe0faac 0x57c130cac3fe0faa 0xebb31c3c3fe0ffff 0xeebb31c3c3fe0fff

def z469 : W := mkw 0x402c000025000000 0x8402c00002500000 0x0234000039000001 0x0023400003900000

def z470 : W := mkw 0x2213e11310de0452 0x62213e11310de045 0x1843e03300ff00f4 0x21843e03300ff00f

def z471 : W := mkw 0x003f1a6800000000 0xd003f1a680000000 0xefbf1ffc00000000 0x3efbf1ffc0000000

def z472 : W := mkw 0x582c16c12f10ee48 0x8582c16c12f10ee4 0xfffc1fc33f10ffcf 0xffffc1fc33f10ffc

def z473 : W := mkw 0x0000000400201080 0x0000000040020108 0xeb83003c00e0f0fd 0xeeb83003c00e0f0f

def z474 : W := mkw 0x823ffbfb82144c52 0xf823ffbfb82144c5 0x7dfadfb3069cccfe 0xf7dfadfb3069cccf

def z475 : W := mkw 0x261349bf12f45cf6 0x5261349bf12f45cf 0x7dcbc3bf06fcccfe 0xf7dcbc3bf06fcccf

def z476 : W := mkw 0x402c000025000000 0x8402c00002500000 0x013800003e000000 0x8013800003e00000

def z477 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x00400000061c0c02 0x000400000061c0c0

def z478 : W := mkw 0x0013082800000000 0x5001308280000000 0x82311c0c00000000 0x082311c0c0000000

def z479 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1dfac0003e9c0006 0xc1dfac0003e9c000

def z480 : W := mkw 0x35130c2d58f1b5e4 0x535130c2d58f1b5e 0xbef53c4ff9733fcf 0x7bef53c4ff9733fc

def z481 : W := mkw 0x0100000140110540 0x0010000014011054 0x3cc42043c1130fce 0x73cc42043c1130fc

def z482 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbffffff9630001 0x3ffbffffff963000

def z483 : W := mkw 0x1a0057d30a14ee5a 0x01a0057d30a14ee5 0xfdcadff3069cfffe 0xffdcadff3069cfff

def z484 : W := mkw 0x0100000140110540 0x0010000014011054 0x00000043c0000f00 0x100000043c0000f0

def z485 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x1fffe00001730007 0x41fffe0000173000

def z486 : W := mkw 0x100004000800a000 0x0100004000800a00 0x82301c0038003001 0x082301c003800300

def z487 : W := mkw 0x763fedbf3ffefcf6 0xf763fedbf3ffefcf 0xffffffbf3ffffcff 0xfffffffbf3ffffcf

def z488 : W := mkw 0x780004803fcaea08 0x0780004803fcaea0 0x004000003fffff0f 0xc004000003fffff0

def z489 : W := mkw 0x402c000025000000 0x8402c00002500000 0xa7bc00403f003f0b 0xda7bc00403f003f0

def z490 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x0bb3003c38e000f5 0xe0bb3003c38e000f

def z491 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0x82353c4cf9633301 0x082353c4cf963330

def z492 : W := mkw 0x0000000400201080 0x0000000040020108 0x00000000006030cd 0x400000000006030c

def z493 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0x80001c0c00003000 0x080001c0c0000300

def z494 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0xfbb3fc3fc0000000 0x2fbb3fc3fc000000

def z495 : W := mkw 0x422ce193271e4c52 0xa422ce193271e4c5 0x7dcee3b3079fccfe 0xf7dcee3b3079fccf

def z496 : W := mkw 0xda3ffffbaf14ee5a 0xfda3ffffbaf14ee5 0xffffffffff9cffff 0xfffffffffff9cfff

def z497 : W := mkw 0x15000c2d4831b5e4 0x115000c2d4831b5e 0xe0001c7fc000fff8 0x3e0001c7fc000fff

def z498 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1dcbe00006ff0006 0xc1dcbe00006ff000

def z499 : W := mkw 0x743fac2c3deab0a4 0xf743fac2c3deab0a 0x82353c0c39633001 0x082353c0c3963300

def z500 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x658803b30600ccfa 0xf658803b30600ccf

def z501 : W := mkw 0x7d3f1eed7ff1ffec 0xd7d3f1eed7ff1ffe 0xffff3ffffff3ffff 0xfffff3ffffff3fff

def z502 : W := mkw 0x7c3f1e6c3de0b2ac 0xd7c3f1e6c3de0b2a 0x82351c4c39603301 0x082351c4c3960330

def z503 : W := mkw 0x590004856f31ffc8 0x0590004856f31ffc 0xbec5204fff73ffcf 0xfbec5204fff73ffc

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x010ac000068c0000 0x8010ac000068c000

def z505 : W := mkw 0x613fa00475eb1180 0xe613fa00475eb118 0x9fffe04cffff3307 0xc9fffe04cffff330

def z506 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0xa6b41c4039003f0b 0x5a6b41c4039003f0

def z507 : W := mkw 0x793fb6c57ffbffc8 0xe793fb6c57ffbffc 0xffffffcfffffffcf 0xfffffffcfffffffc

def z508 : W := mkw 0x182c16c00a00ea08 0x8182c16c00a00ea0 0xe7bc1fc00000ff08 0x1e7bc1fc00000ff0

def z509 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1ec7e00001ff0007 0x41ec7e00001ff000

def z510 : W := mkw 0x613fa00575fb15c0 0xe613fa00575fb15c 0x1fffe0003fff3fcf 0xc1fffe0003fff3fc

def z511 : W := mkw 0x100004000800a000 0x0100004000800a00 0xe7b41c403900ff0b 0xde7b41c403900ff0

def z512 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0x5fffffb03fff0007 0xc5fffffb03fff000

def z513 : W := mkw 0x582c57d22f00ea08 0x8582c57d22f00ea0 0xffbedff33f00ff0b 0xfffbedff33f00ff0

def z514 : W := mkw 0x623fa08137de4c52 0xe623fa08137de4c5 0x1fffe0003fffccff 0xc1fffe0003fffccf

def z515 : W := mkw 0x782c16c03fcaea08 0x8782c16c03fcaea0 0xe7fc1fc03fffff0f 0xde7fc1fc03fffff0

def z516 : W := mkw 0x802cf35280000000 0xa802cf3528000000 0x0008c38000000000 0x00008c3800000000

def z517 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0x7d8be3bfc0000000 0x37d8be3bfc000000

def z518 : W := mkw 0x822cf3d382144c52 0xa822cf3d382144c5 0x144ce3c3c61c0c02 0x1144ce3c3c61c0c0

def z519 : W := mkw 0x7c3f1eec3fe0faac 0xd7c3f1eec3fe0faa 0xebbb1fbc3ee0f0fd 0xeebbb1fbc3ee0f0f

def z520 : W := mkw 0x003fa00000000000 0xe003fa0000000000 0x013ac00000000000 0x0013ac0000000000

def z521 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0xe3b01c003f00ff0b 0xce3b01c003f00ff0

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x1801200fc0000000 0x21801200fc000000

def z523 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fbfe0003e8c0000 0x81fbfe0003e8c000

def z524 : W := mkw 0x36130cad1af4fcf6 0x536130cad1af4fcf 0xebf31c3c3efcfcff 0xeebf31c3c3efcfcf

def z525 : W := mkw 0x0200411300140452 0x0020041130014045 0x00000033000000f0 0x200000033000000f

def z526 : W := mkw 0x003fa82800000000 0xf003fa8280000000 0xffbffc3c00000000 0x2ffbffc3c0000000

def z527 : W := mkw 0x01000005403115c0 0x001000005403115c 0x9645204fc1733f03 0x19645204fc1733f0

def z528 : W := mkw 0xe03fba68b5ca0000 0xfe03fba68b5ca000 0x9ffffc4cffff0007 0xc9ffffc4cffff000

def z529 : W := mkw 0xb43fff7a98c0a024 0xfb43fff7a98c0a02 0x413adfb03880c030 0x8413adfb03880c03

def z530 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x69c20030069cccfe 0xe69c20030069cccf

def z531 : W := mkw 0x603fb24035ca0000 0xe603fb24035ca000 0xffffffc03fff0007 0xdffffffc03fff000

def z532 : W := mkw 0x743f0c2c3de0b0a4 0xd743f0c2c3de0b0a 0xefbf1c3c3fe0f0ff 0xeefbf1c3c3fe0f0f

def z533 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcac3b3061c0c02 0x37dcac3b3061c0c0

def z534 : W := mkw 0x0000419202004800 0x0000041920200480 0x7d8ac3b30600cc0a 0xf7d8ac3b30600cc0

def z535 : W := mkw 0x360004851af4fcf6 0x0360004851af4fcf 0x004000003efcfcff 0xc004000003efcfcf

def z536 : W := mkw 0x0013000000000000 0x4001300000000000 0x0bb3000000000000 0x00bb300000000000

def z537 : W := mkw 0x803fba6880000000 0xf803fba688000000 0x00301c0000000000 0x000301c000000000

def z538 : W := mkw 0x402c008027004800 0x8402c00802700480 0x67bc03803f00cc0b 0xd67bc03803f00cc0

def z539 : W := mkw 0x613fa00575fb15c0 0xe613fa00575fb15c 0xbef5204ff9733fcf 0x7bef5204ff9733fc

def z540 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfffbdc3c3efcf0ff 0xefffbdc3c3efcf0f

def z541 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xe9821c3c0080f0fc 0xee9821c3c0080f0f

def z542 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1ffbc0003efc0007 0xc1ffbc0003efc000

def z543 : W := mkw 0x82005bfb82144c52 0x182005bfb82144c5 0xe0001fffc000ccf8 0x3e0001fffc000ccf

def z544 : W := mkw 0x703fa4003dcaa000 0xe703fa4003dcaa00 0xfffffc003ffff00f 0xcfffffc003ffff00

def z545 : W := mkw 0x35130c2d58f1b5e4 0x535130c2d58f1b5e 0xfbf33c3ff8f3f0fd 0xefbf33c3ff8f3f0f

def z546 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x07bd20003f630003 0xc07bd20003f63000

def z547 : W := mkw 0x98005ffa8a00ea08 0x198005ffa8a00ea0 0xe0001fffc000ff08 0x3e0001fffc000ff0

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000069c0006 0xc00400000069c000

def z549 : W := mkw 0x003fb24000000000 0xe003fb2400000000 0xffbfffc000000000 0x1ffbfffc00000000

def z550 : W := mkw 0x623fe19337de4c52 0xe623fe19337de4c5 0x7dfac3b33e9cccfe 0xf7dfac3b33e9cccf

def z551 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x1ec520003fff0007 0xc1ec520003fff000

def z552 : W := mkw 0x0013a00000000000 0x60013a0000000000 0x1803e00000000000 0x01803e0000000000

def z553 : W := mkw 0x783fa4803fcaea08 0xe783fa4803fcaea0 0x1fffe0003fffff0f 0xc1fffe0003fffff0

def z554 : W := mkw 0x603fa00435ea1080 0xe603fa00435ea108 0xbfffe00c3fff30cf 0xebfffe00c3fff30c

def z555 : W := mkw 0x603fe11235ca0000 0xe603fe11235ca000 0x7fffe3b33fff0007 0xf7fffe3b33fff000

def z556 : W := mkw 0x023fe19302144c52 0xe023fe19302144c5 0x7fffe3b3069cccfe 0xf7fffe3b3069cccf

def z557 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xc33ffffcc0000000 0x0c33ffffcc000000

def z558 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcec3f3079cffff 0xfffcec3f3079cfff

def z559 : W := mkw 0x0000000100100440 0x0000000010010044 0x1440000300100c02 0x11440000300100c0

def z560 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x65b81f803e00cc0a 0xd65b81f803e00cc0

def z561 : W := mkw 0x0000008002004800 0x0000000800200480 0x0408038006000c02 0x10408038006000c0

def z562 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d8ac00000000000 0x01d8ac0000000000

def z563 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0x0002c03000000000 0x00002c0300000000

def z564 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe13adfffc0000000 0x3e13adfffc000000

def z565 : W := mkw 0x002c12c002004800 0x8002c12c00200480 0xe7bc1fc00600cc0a 0xde7bc1fc00600cc0

def z566 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x604003b3069cccfe 0xf604003b3069cccf

def z567 : W := mkw 0x6200419337de4c52 0x06200419337de4c5 0x7dcac3b33fffccff 0xf7dcac3b33fffccf

def z568 : W := mkw 0x0000008002004800 0x0000000800200480 0x000000000600cc0a 0xc000000000600cc0

def z569 : W := mkw 0x602c000035ca0000 0x8602c000035ca000 0x07fc00003fff0007 0xc07fc00003fff000

def z570 : W := mkw 0x903fff7a8800a000 0xf903fff7a8800a00 0xffbffffff800f009 0xfffbffffff800f00

def z571 : W := mkw 0x2400000410e010a4 0x02400000410e010a 0x0000000000e000f4 0x00000000000e000f

def z572 : W := mkw 0x743fac283dcaa024 0xf743fac283dcaa02 0x5ffffc303fffc037 0xc5ffffc303fffc03

def z573 : W := mkw 0x1a0057d30a14ee5a 0x01a0057d30a14ee5 0xe0001ff30000fff8 0x3e0001ff30000fff

def z574 : W := mkw 0x01000005403115c0 0x001000005403115c 0xaa81004fc0603fcd 0x7aa81004fc0603fc

def z575 : W := mkw 0xb63fffff9af4fcf6 0xfb63fffff9af4fcf 0xfffffffffefcfcff 0xffffffffffefcfcf

def z576 : W := mkw 0x34134d3e18e0b0a4 0x534134d3e18e0b0a 0xffbbdfbf38e0f0fd 0xfffbbdfbf38e0f0f

def z577 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe8031c3c00e0f0fc 0x2e8031c3c00e0f0f

def z578 : W := mkw 0x582c16c42f20fa88 0x8582c16c42f20fa8 0xefbd1fcc3f60ffcf 0xfefbd1fcc3f60ffc

def z579 : W := mkw 0x0100000440211180 0x0010000044021118 0xbe85204fc1633301 0x3be85204fc163330

def z580 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x0030000038000000 0x0003000003800000

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x0684000001000003 0x4068400000100000

def z582 : W := mkw 0x613fa00475eb1180 0xe613fa00475eb118 0x8235204cf9633301 0x08235204cf963330

def z583 : W := mkw 0x0100000440211180 0x0010000044021118 0xa685204cc1633f0b 0x5a685204cc1633f0

def z584 : W := mkw 0x190016c54a31ffc8 0x0190016c54a31ffc 0xfec53fcfc173ffcf 0x7fec53fcfc173ffc

def z585 : W := mkw 0x0200419202044812 0x0020041920204481 0x658ac3b0068ccc3a 0xd658ac3b0068ccc3

def z586 : W := mkw 0x6100000575fb15c0 0x06100000575fb15c 0x004000003fff3fcf 0xc004000003fff3fc

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0xa684004000000000 0x1a68400400000000

def z588 : W := mkw 0xd82c5ffaaf00ea08 0x9d82c5ffaaf00ea0 0xe7bc1fffff00ff0b 0xfe7bc1fffff00ff0

def z589 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x75c8c383061ccc0a 0xd75c8c383061ccc0

def z590 : W := mkw 0xe03ff352b5ca0000 0xee03ff352b5ca000 0x1fffe3c3ffff0007 0xd1fffe3c3ffff000

def z591 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1ff7200039f30007 0xc1ff7200039f3000

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x14042043c0000000 0x114042043c000000

def z593 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe7bedff000000000 0x1e7bedff00000000

def z594 : W := mkw 0x0013082800000000 0x5001308280000000 0xebb31c3c0080c0fc 0xeebb31c3c0080c0f

def z595 : W := mkw 0x412ca005653b15c0 0xa412ca005653b15c 0xbecde04fc77f3fcf 0x7becde04fc77f3fc

def z596 : W := mkw 0xb43fff7a98c0a024 0xfb43fff7a98c0a02 0xffbffffff880c030 0xbffbffffff880c03

def z597 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x0001200000630000 0x0000120000063000

def z598 : W := mkw 0x623fe19237ce4812 0xe623fe19237ce481 0x413ac3b03e8cc030 0x8413ac3b03e8cc03

def z599 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x65c80380069cccfe 0xd65c80380069cccf

def z600 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xc33c1fc03f00f301 0x8c33c1fc03f00f30

def z601 : W := mkw 0x3400040018c0a024 0x03400040018c0a02 0x000000003880c030 0x8000000003880c03

def z602 : W := mkw 0x0200008102144c52 0x00200008102144c5 0x3cc00003069cccfe 0xf3cc00003069cccf

def z603 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0xe3b21c303880f039 0xce3b21c303880f03

def z604 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe5881fc00600ff0a 0xde5881fc00600ff0

def z605 : W := mkw 0x823ffbfa82044812 0xf823ffbfa8204481 0x413adfb0068cc030 0x8413adfb0068cc03

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cc0000000100006 0x41cc000000010000

def z607 : W := mkw 0x802cb24080000000 0xa802cb2408000000 0x00042040c0000000 0x000042040c000000

def z608 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0xa68400403f00ff0b 0xda68400403f00ff0

def z609 : W := mkw 0x0100000140110540 0x0010000014011054 0xb6c42043c1133f0b 0x5b6c42043c1133f0

def z610 : W := mkw 0xb43fbe6c98e0b0a4 0xfb43fbe6c98e0b0a 0x82353c4cf8603001 0x082353c4cf860300

def z611 : W := mkw 0x10130c280800a000 0x510130c280800a00 0xebb31c3c3800f009 0xeebb31c3c3800f00

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x1fcfe00007ff0007 0xc1fcfe00007ff000

def z613 : W := mkw 0x0200411200040012 0x0020041120004001 0x0002c030008c0030 0x00002c030008c003

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000001730007 0x4004000000173000

def z615 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe6841fc00100ff0b 0x5e6841fc00100ff0

def z616 : W := mkw 0x0200411300140452 0x0020041130014045 0x1040c003001c0000 0x01040c003001c000

def z617 : W := mkw 0x0200411300140452 0x0020041130014045 0x3cc2c033009c0cfe 0x73cc2c033009c0cf

def z618 : W := mkw 0x0013082800000000 0x5001308280000000 0x0803003c00000000 0x20803003c0000000

def z619 : W := mkw 0x81005b7fc03115c0 0x181005b7fc03115c 0xfec53fffc1733fcf 0x7fec53fffc1733fc

def z620 : W := mkw 0xd82cf7d2af00ea08 0xad82cf7d2af00ea0 0xf7bcffc3ff00ff0b 0xdf7bcffc3ff00ff0

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a81000000600005 0x40a8100000060000

def z622 : W := mkw 0x0200000100140452 0x0020000010014045 0x00400000009c00f4 0x000400000009c00f

def z623 : W := mkw 0xc82cf3d2a7004a08 0xac82cf3d2a7004a0 0x140ce3c3c7000f02 0x1140ce3c3c7000f0

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x8204004001003301 0x0820400400100330

def z625 : W := mkw 0x110004054831b5c0 0x0110004054831b5c 0xfff53c4ff973ffcf 0xffff53c4ff973ffc

def z626 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0x413adfb03e00c000 0x8413adfb03e00c00

def z627 : W := mkw 0x5a2c57d22f04ea1a 0x85a2c57d22f04ea1 0x413adfb03e8cc030 0x8413adfb03e8cc03

def z628 : W := mkw 0x0100000440211180 0x0010000044021118 0x9ec5204cc1733307 0x49ec5204cc173330

def z629 : W := mkw 0x812cf357c03115c0 0xa812cf357c03115c 0xbecde3cfc1733fcf 0x7becde3cfc1733fc

def z630 : W := mkw 0x0100000140110540 0x0010000014011054 0x10402003c0130000 0x010402003c013000

def z631 : W := mkw 0x0000008102104c40 0x00000008102104c4 0x7dc803830610ccce 0xf7dc803830610ccc

def z632 : W := mkw 0x0000000400201080 0x0000000040020108 0x0801000c006000c4 0x20801000c006000c

def z633 : W := mkw 0x402c000025000000 0x8402c00002500000 0x1ffd20003f730007 0xc1ffd20003f73000

def z634 : W := mkw 0x0300419742355dd2 0x00300419742355dd 0xfdcac3ffc69cfffe 0xffdcac3ffc69cfff

def z635 : W := mkw 0x7e3f5fff3ff4fefe 0xd7e3f5fff3ff4fef 0xffffdfff3ffcffff 0xfffffdfff3ffcfff

def z636 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0xebb31c3c3880c030 0xaebb31c3c3880c03

def z637 : W := mkw 0x603fa08037ca4800 0xe603fa08037ca480 0x7fffe3803fffcc0f 0xd7fffe3803fffcc0

def z638 : W := mkw 0xd83fbee8af00ea08 0xfd83fbee8af00ea0 0xe7bd3fccff00ff0b 0xde7bd3fccff00ff0

def z639 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0x00301c0038000000 0x000301c003800000

def z640 : W := mkw 0x0100008542315dc0 0x00100008542315dc 0xffcd23cfc773ffcf 0xfffcd23cfc773ffc

def z641 : W := mkw 0x0000008002004800 0x0000000800200480 0x600003800000cc08 0x1600003800000cc0

def z642 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x0231000038600001 0x0023100003860000

def z643 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fbfe00039630001 0x01fbfe0003963000

def z644 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0xe7bd3fc03f63ff0b 0xde7bd3fc03f63ff0

def z645 : W := mkw 0x482c12c027004a08 0x8482c12c027004a0 0xe7bc1fc007000f02 0x1e7bc1fc007000f0

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe85204fc1003f0b 0x7be85204fc1003f0

def z647 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7448c3b3061cccfa 0x37448c3b3061cccf

def z648 : W := mkw 0x0300008542355dd2 0x00300008542355dd 0x0040000007ffffff 0xc0040000007fffff

def z649 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x0001000c00600000 0x00001000c0060000

def z650 : W := mkw 0x0200419202044812 0x0020041920204481 0x7d8ac3b3068cc030 0xb7d8ac3b3068cc03

def z651 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x1dcac383069c0c06 0xd1dcac383069c0c0

def z652 : W := mkw 0x583fb6c02f00ea08 0xe583fb6c02f00ea0 0xffbfffc03f00ff0b 0xdffbfffc03f00ff0

def z653 : W := mkw 0x0000411200000000 0x0000041120000000 0xff8fe3ffc0000000 0x3ff8fe3ffc000000

def z654 : W := mkw 0x592c16446d21b388 0x8592c16446d21b38 0x82353c4cf9633301 0x082353c4cf963330

def z655 : W := mkw 0x00000005003014c0 0x000000005003014c 0xbec1000f00703ccf 0x7bec1000f00703cc

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0x0588000006000002 0xc058800000600000

def z657 : W := mkw 0x180016400800a208 0x0180016400800a20 0x80001c4000003300 0x080001c400000330

def z658 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x8bb31c0c38e03005 0xc8bb31c0c38e0300

def z659 : W := mkw 0x021349bb02144c52 0x5021349bb02144c5 0xfffbdfbf069cccfe 0xffffbdfbf069cccf

def z660 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x7dbadfb300000000 0x37dbadfb30000000

def z661 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1ef5200039730007 0x41ef520003973000

def z662 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa81000c00000000 0x2aa81000c0000000

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x0404004001000f02 0x10404004001000f0

def z664 : W := mkw 0x0100000440211180 0x0010000044021118 0x8000004cc0003300 0x08000004cc000330

def z665 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x0008c000060c0000 0x00008c000060c000

def z666 : W := mkw 0x783fb6c03fcaea08 0xe783fb6c03fcaea0 0x5fffff803fffc007 0xc5fffff803fffc00

def z667 : W := mkw 0x812cf353c0110540 0xa812cf353c011054 0x144ce3c3c1130f02 0x1144ce3c3c1130f0

def z668 : W := mkw 0x0200411300140452 0x0020041130014045 0x79c2c033009cc0fc 0xe79c2c033009cc0f

def z669 : W := mkw 0x2113000550f115c0 0x42113000550f115c 0xbff7204ff9f33fcf 0xfbff7204ff9f33fc

def z670 : W := mkw 0x0200419202044812 0x0020041920204481 0x5dcac3b0069cc036 0xc5dcac3b0069cc03

def z671 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x82341c403f00ff0b 0xc82341c403f00ff0

def z672 : W := mkw 0x2613493f10f414f6 0x52613493f10f414f 0x1843c03f00fc00f4 0x21843c03f00fc00f

def z673 : W := mkw 0xd83fbe68ad00a208 0xfd83fbe68ad00a20 0x82353c4cf9003301 0x082353c4cf900330

def z674 : W := mkw 0x823ffbfa82044812 0xf823ffbfa8204481 0xffbfffffc68cc030 0xbffbfffffc68cc03

def z675 : W := mkw 0x823ffbfb82144c52 0xf823ffbfb82144c5 0xffffffffc61c0c02 0x3ffffffffc61c0c0

def z676 : W := mkw 0x0013082800000000 0x5001308280000000 0x41321c3000000000 0x041321c300000000

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000300000c0f8 0x2600000300000c0f

def z678 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x1ecde000077f0007 0x41ecde000077f000

def z679 : W := mkw 0x8113e93fc03115c0 0x78113e93fc03115c 0x1843e03fc07300c4 0x21843e03fc07300c

def z680 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1c4fe00007ff0006 0x01c4fe00007ff000

def z681 : W := mkw 0x0200411300140452 0x0020041130014045 0x7dcac3b3009c00f4 0x37dcac3b3009c00f

def z682 : W := mkw 0x343fac2c18e0b0a4 0xf343fac2c18e0b0a 0xffbffc3c38e0f0fd 0xeffbffc3c38e0f0f

def z683 : W := mkw 0x0000000100100440 0x0000000010010044 0x7dc200330090ccfe 0xf7dc200330090ccf

def z684 : W := mkw 0x823ffb7b80140452 0xf823ffb7b8014045 0xffffffffc09c00f4 0x3ffffffffc09c00f

def z685 : W := mkw 0xfc3ffffebfe0faac 0xffc3ffffebfe0faa 0xffbfffffffe0ffff 0xfffbfffffffe0fff

def z686 : W := mkw 0x2000000010ca0000 0x02000000010ca000 0x0040000000ff0004 0x00040000000ff000

def z687 : W := mkw 0x502c04002d00a000 0x8502c04002d00a00 0xe7bc1c003f00f00b 0xce7bc1c003f00f00

def z688 : W := mkw 0x0000000400201080 0x0000000040020108 0xbe85204fc06030cd 0x7be85204fc06030c

def z689 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x6bb3003038e0c0fd 0xe6bb3003038e0c0f

def z690 : W := mkw 0x0000008002004800 0x0000000800200480 0x7dcac380069ccc0e 0xd7dcac380069ccc0

def z691 : W := mkw 0x1c001eec0a20faac 0x11c001eec0a20faa 0xe0001ffc0000fff8 0x3e0001ffc0000fff

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x8205204cc0000000 0x08205204cc000000

def z693 : W := mkw 0xd83ffffaaf00ea08 0xfd83ffffaaf00ea0 0xffbffffffe00c000 0xbffbffffffe00c00

def z694 : W := mkw 0x01000005403115c0 0x001000005403115c 0x3cc0000301733fcf 0x73cc0000301733fc

def z695 : W := mkw 0x100004000800a000 0x0100004000800a00 0xe0001c000000f008 0x0e0001c000000f00

def z696 : W := mkw 0x482c12c027004a08 0x8482c12c027004a0 0x07bc03c03f000f03 0xd07bc03c03f000f0

def z697 : W := mkw 0x36134d3f18f4b4f6 0x536134d3f18f4b4f 0xfbf3dc3f38fcf0fd 0xefbf3dc3f38fcf0f

def z698 : W := mkw 0x613fa00175db0540 0xe613fa00175db054 0x1fffe043ffff0f07 0xd1fffe043ffff0f0

def z699 : W := mkw 0x0100000140110540 0x0010000014011054 0x0040000001130f02 0x00040000001130f0

def z700 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0x40001f800000c000 0x040001f800000c00

def z701 : W := mkw 0x2413082c10e010a4 0x52413082c10e010a 0x6983003c00e0c0fc 0xe6983003c00e0c0f

def z702 : W := mkw 0x743fac2c3deab0a4 0xf743fac2c3deab0a 0xebb73c3c39e3f0fd 0xeebb73c3c39e3f0f

def z703 : W := mkw 0x7c0004843fe0faac 0x07c0004843fe0faa 0x000000003fe0ffff 0xc000000003fe0fff

def z704 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x1842c033069cccfe 0xe1842c033069cccf

def z705 : W := mkw 0x002c535200000000 0x8002c53520000000 0xffbedff300000000 0x3ffbedff30000000

def z706 : W := mkw 0x422ce193271e4c52 0xa422ce193271e4c5 0x144ce383071f0c02 0x1144ce383071f0c0

def z707 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbffffff8000000 0x3ffbffffff800000

def z708 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c7ff8e0f0fd 0xfebb31c7ff8e0f0f

def z709 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x3fffe0033fff0007 0xf3fffe0033fff000

def z710 : W := mkw 0x0300419642255992 0x0030041964225599 0xc30fe3fcc7eff331 0x8c30fe3fcc7eff33

def z711 : W := mkw 0x582c16402d00a208 0x8582c16402d00a20 0xe7bc1fc039003f0b 0x5e7bc1fc039003f0

def z712 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x0bfbc0003fff0007 0xc0bfbc0003fff000

def z713 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe9821fffc0000000 0x3e9821fffc000000

def z714 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xfdcadfffc69c0006 0xffdcadfffc69c000

def z715 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0x940cffcfc0000000 0x1940cffcfc000000

def z716 : W := mkw 0x803fba6880000000 0xf803fba688000000 0xffbd3fcfc0000000 0x3ffbd3fcfc000000

def z717 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc1000003 0x7ffbfffffc100000

def z718 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03900ff09 0x1e7bc1fc03900ff0

def z719 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc0003f08 0x3ffbfffffc0003f0

def z720 : W := mkw 0x823fbae982144c52 0xf823fbae982144c5 0x82753c4cc69cccfe 0xc82753c4cc69cccf

def z721 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcbc3bf069cccfe 0xfffcbc3bf069cccf

def z722 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x65cac3b0069cccfe 0xd65cac3b0069cccf

def z723 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec7e04fc1ff3fcf 0x7bec7e04fc1ff3fc

def z724 : W := mkw 0x0100000440211180 0x0010000044021118 0xbe85204fc1633f0b 0x7be85204fc1633f0

def z725 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbff5204ff9733fcf 0xfbff5204ff9733fc

def z726 : W := mkw 0x7c3fbe6c3deab2ac 0xf7c3fbe6c3deab2a 0x82353c4c39633301 0x082353c4c3963330

def z727 : W := mkw 0x6000a00035ca0000 0x26000a00035ca000 0x1040e0003fff0007 0xc1040e0003fff000

def z728 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc0600005 0x7ffbfffffc060000

def z729 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xfffffc003fff0007 0xcfffffc003fff000

def z730 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x594ac3b3069cccfe 0xe594ac3b3069cccf

def z731 : W := mkw 0x603fb24035ca0000 0xe603fb24035ca000 0x5fffff803fff0007 0xc5fffff803fff000

def z732 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebf31c3c39f3f0ff 0xeebf31c3c39f3f0f

def z733 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xfc0fffffc0000000 0x3fc0fffffc000000

def z734 : W := mkw 0x802c5b7a80000000 0x9802c5b7a8000000 0xe40c1fffc0000000 0x3e40c1fffc000000

def z735 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xfffdffc03f7fff0f 0xdfffdffc03f7fff0

def z736 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x698ac3b3068cccfc 0xf698ac3b3068cccf

def z737 : W := mkw 0x3413ac2c18eab0a4 0x73413ac2c18eab0a 0xebb3dc3c38ecf0fd 0xeebb3dc3c38ecf0f

def z738 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcfe3ffc7ffccff 0xfffcfe3ffc7ffccf

def z739 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x5d4ac3b3069cccf6 0xb5d4ac3b3069cccf

def z740 : W := mkw 0x592c16c56f31ffc8 0x8592c16c56f31ffc 0x59793f8ffe73c0c4 0xa59793f8ffe73c0c

def z741 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b41fc03900ff09 0xde3b41fc03900ff0

def z742 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x410ac3b3068cc0f0 0xa410ac3b3068cc0f

def z743 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7d8ac3b3068cccf8 0xb7d8ac3b3068cccf

def z744 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xfec53fffc1730007 0x7fec53fffc173000

def z745 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x49321c303880c0f4 0xa49321c303880c0f

def z746 : W := mkw 0x623fe19337de4c52 0xe623fe19337de4c5 0x623523b33963ccf9 0x3623523b33963ccf

def z747 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7fc1fc03f73ff0f 0xde7fc1fc03f73ff0

def z748 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec7207fc1f33fff 0x7bec7207fc1f33ff

def z749 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc6000002 0xfffbfffffc600000

def z750 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe10adfffc0000000 0x3e10adfffc000000

def z751 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbfffffff8c0003 0xfffbfffffff8c000

def z752 : W := mkw 0x80135b7a80000000 0x580135b7a8000000 0xffbbdfffc0000000 0x3ffbbdfffc000000

def z753 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xebb21c3c3880f0fd 0xeebb21c3c3880f0f

def z754 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa245204fc1733fcf 0x7a245204fc1733fc

def z755 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffbfffffc7000002 0x3ffbfffffc700000

def z756 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbd1fcc3f00ff0b 0xfefbd1fcc3f00ff0

def z757 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1c4fe0003fff0007 0xc1c4fe0003fff000

def z758 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfffffc3c3ffff0ff 0xefffffc3c3ffff0f

def z759 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x863c1fc03f00ff0b 0xd863c1fc03f00ff0

def z760 : W := mkw 0x0200419202044812 0x0020041920204481 0x410ac3b0068cc0fc 0xc410ac3b0068cc0f

def z761 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7fcfe3b3069cccfe 0xf7fcfe3b3069cccf

def z762 : W := mkw 0x602c000035ca0000 0x8602c000035ca000 0x1ffec0003fff0007 0xc1ffec0003fff000

def z763 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x41381f803e00ff08 0x841381f803e00ff0

def z764 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcec3f3079ccffe 0xf7dcec3f3079ccff

def z765 : W := mkw 0x0300419342154d52 0x00300419342154d5 0x7dcac3b3079fcffe 0xf7dcac3b3079fcff

def z766 : W := mkw 0x5a2c57532d14a65a 0x85a2c57532d14a65 0x9a76dc73399c33f5 0x29a76dc73399c33f

def z767 : W := mkw 0xd82cb6c0af00ea08 0xad82cb6c0af00ea0 0xe7bc3fc0ff00ff0b 0xde7bc3fc0ff00ff0

def z768 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x5d3fffffc0000000 0x35d3fffffc000000

def z769 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebf31c3c3efcf0ff 0xeebf31c3c3efcf0f

def z770 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xf53effffc0000000 0x3f53effffc000000

def z771 : W := mkw 0x2013000010c00000 0x42013000010c0000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z772 : W := mkw 0x0013493a00000000 0x50013493a0000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z773 : W := mkw 0x6c3f1aec37e05aac 0xd6c3f1aec37e05aa 0x0c0f03fc07e00ff6 0x30c0f03fc07e00ff

def z774 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x014ac0003fff0007 0xc014ac0003fff000

def z775 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x658ac3b3068cccfa 0xf658ac3b3068cccf

def z776 : W := mkw 0x613fa00575fb15c0 0xe613fa00575fb15c 0xa13ac04ffe8c3fc8 0xba13ac04ffe8c3fc

def z777 : W := mkw 0x813ffb7fc03115c0 0xf813ffb7fc03115c 0x417adfb001733fcf 0x4417adfb001733fc

def z778 : W := mkw 0xf43fbe6cbdeab0a4 0xff43fbe6cbdeab0a 0x82353c4cf9633001 0x082353c4cf963300

def z779 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xebb31c3c39e3f3fd 0xeebb31c3c39e3f3f

def z780 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc0003009 0x7ffbfffffc000300

def z781 : W := mkw 0x35130c2958d1a564 0x535130c2958d1a56 0x55763c73f993cf32 0x955763c73f993cf3

def z782 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xfffeffc03f9fff0f 0xdfffeffc03f9fff0

def z783 : W := mkw 0x0000411200000000 0x0000041120000000 0x7dcac3b3069cc0fe 0xf7dcac3b3069cc0f

def z784 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x9fffe0403fff3307 0xc9fffe0403fff330

def z785 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfbf33c3c38f3f0fd 0xefbf33c3c38f3f0f

def z786 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe3331c3c38e0f0f9 0xae3331c3c38e0f0f

def z787 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0303fff00f7 0xe1fffe0303fff00f

def z788 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x177fe0003fff0003 0x8177fe0003fff000

def z789 : W := mkw 0xe03fba68b5ca0000 0xfe03fba68b5ca000 0xbffffc4fffff0007 0xfbffffc4fffff000

def z790 : W := mkw 0x0200419202044812 0x0020041920204481 0x7dcac3b0069cc0fe 0xe7dcac3b0069cc0f

def z791 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0x967dffcfff7f0003 0x1967dffcfff7f000

def z792 : W := mkw 0x8013e93a80000000 0x78013e93a8000000 0xffbbffbfc0000000 0x3ffbbffbfc000000

def z793 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xefb71c3c39e0f0ff 0xeefb71c3c39e0f0f

def z794 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec5204fc1733f03 0x3bec5204fc1733f0

def z795 : W := mkw 0x80135b7a80000000 0x580135b7a8000000 0xffb73fffc0000000 0x3ffb73fffc000000

def z796 : W := mkw 0x542cac2c2d2ab0a4 0xb542cac2c2d2ab0a 0xf44cfc3c071ff0fa 0x2f44cfc3c071ff0f

def z797 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebbbdc3c3eecf0fd 0xeebbbdc3c3eecf0f

def z798 : W := mkw 0xa113e93fd0fb15c0 0x7a113e93fd0fb15c 0x1843e03fc0ff00c4 0x21843e03fc0ff00c

def z799 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xfffffffffeff0004 0xbfffffffffeff000

def z800 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1a77e0003fff0007 0xc1a77e0003fff000

def z801 : W := mkw 0x0200419202044812 0x0020041920204481 0x490ac3b0068cc0f4 0xa490ac3b0068cc0f

def z802 : W := mkw 0x582cb6c02f00ea08 0xa582cb6c02f00ea0 0xf7bcffc03f00ff0b 0xdf7bcffc03f00ff0

def z803 : W := mkw 0x17004dbf4a35fdf6 0x117004dbf4a35fdf 0xe0001fffc000fff8 0x3e0001fffc000fff

def z804 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc68c0000 0xbffbfffffc68c000

def z805 : W := mkw 0xa43ffb7a90c00024 0xfa43ffb7a90c0002 0xffbfffffc0800030 0x3ffbfffffc080003

def z806 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcbe3bfc69cccfe 0xf7dcbe3bfc69cccf

def z807 : W := mkw 0x01000005403115c0 0x001000005403115c 0xb6c5204fc1733f0b 0x5b6c5204fc1733f0

def z808 : W := mkw 0xca2cf3d3a7144e5a 0xaca2cf3d3a7144e5 0x144ce3c3c71c0f02 0x1144ce3c3c71c0f0

def z809 : W := mkw 0x823ffb7a80040012 0xf823ffb7a8004001 0xffbfffffc08c0030 0x3ffbfffffc08c003

def z810 : W := mkw 0x01000005403115c0 0x001000005403115c 0xb645204fc1733fcb 0x3b645204fc1733fc

def z811 : W := mkw 0x01000005403115c0 0x001000005403115c 0xffcd23cfc1733fcf 0x7ffcd23cfc1733fc

def z812 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fcfff00ff0b 0xfe7bc1fcfff00ff0

def z813 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe0301c3c3800f0f8 0x2e0301c3c3800f0f

def z814 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xefbb1fbc38e0f0fd 0xfefbb1fbc38e0f0f

def z815 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7ffac3b33e9cccff 0xf7ffac3b33e9cccf

def z816 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x3fffe0003fff00cf 0xe3fffe0003fff00c

def z817 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x167de0003fff0007 0xc167de0003fff000

def z818 : W := mkw 0x0300419342154d52 0x00300419342154d5 0xffcee3f3c79fffff 0xfffcee3f3c79ffff

def z819 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffffffc03fffff0f 0xdffffffc03fffff0

def z820 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7fcec3b3079cccff 0xf7fcec3b3079cccf

def z821 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0003eff0004 0x81fffe0003eff000

def z822 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xfffffffff9f30007 0xffffffffff9f3000

def z823 : W := mkw 0x602ca00035ca0000 0xa602ca00035ca000 0x1dcee0003fff0007 0xc1dcee0003fff000

def z824 : W := mkw 0xc02c5b7aa5000000 0x9c02c5b7aa500000 0xe7bc1fffff000003 0xfe7bc1fffff00000

def z825 : W := mkw 0xa513e93fd0f115e4 0x7a513e93fd0f115e 0x1843e03fc0f300f4 0x21843e03fc0f300f

def z826 : W := mkw 0x603fa82835ca0000 0xf603fa82835ca000 0x1fffe03c3fff0007 0xe1fffe03c3fff000

def z827 : W := mkw 0x01000005403115c0 0x001000005403115c 0xffcfe07fc7ffffff 0xfffcfe07fc7fffff

def z828 : W := mkw 0x0300419342154d52 0x00300419342154d5 0x7fcfe3f3c7ffcfff 0xf7fcfe3f3c7ffcff

def z829 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x65b81f803f00ff0b 0xd65b81f803f00ff0

def z830 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe7b41fc03900ff0b 0xde7b41fc03900ff0

def z831 : W := mkw 0x01000005403115c0 0x001000005403115c 0x9a45204fc1733fcf 0x69a45204fc1733fc

def z832 : W := mkw 0xe0005b7ab5ca0000 0x1e0005b7ab5ca000 0xe0401fffffff0007 0xfe0401fffffff000

def z833 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xfdbadfffc0000000 0x3fdbadfffc000000

def z834 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0xfd8effffc0000000 0x3fd8effffc000000

def z835 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xe2353ffff9630001 0x3e2353ffff963000

def z836 : W := mkw 0xc02cfb7aa50a0000 0xbc02cfb7aa50a000 0xf44cffffc71f0002 0x3f44cffffc71f000

def z837 : W := mkw 0x012c1245403115c0 0x8012c1245403115c 0xe7fc1fc001733fcf 0x5e7fc1fc001733fc

def z838 : W := mkw 0x100004800a00e800 0x0100004800a00e80 0xe7bc1fc03f00ff0b 0xde7bc1fc03f00ff0

def z839 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe0301fffc0000000 0x3e0301fffc000000

def z840 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1e7fe0003fff0007 0x01e7fe0003fff000

def z841 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xefbb1c3c3ee0f0ff 0xeefbb1c3c3ee0f0f

def z842 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x554ac3b3069cccfe 0xd554ac3b3069cccf

def z843 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xf8013fffc0000000 0x3f8013fffc000000

def z844 : W := mkw 0x2013082810c00000 0x52013082810c0000 0xebb31c3c38e0c0fd 0xeebb31c3c38e0c0f

def z845 : W := mkw 0xd813edbaaf00ea08 0x7d813edbaaf00ea0 0x1803e03fff00ff0b 0xe1803e03fff00ff0

def z846 : W := mkw 0x402c124025000000 0x8402c12402500000 0xe7bc1fc03f003f0b 0xde7bc1fc03f003f0

def z847 : W := mkw 0xc03ffb7aa50a0000 0xfc03ffb7aa50a000 0xffbfffffc1030000 0x3ffbfffffc103000

def z848 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0xe0013fffc0000000 0x3e0013fffc000000

def z849 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0x597bffbffeff0004 0xa597bffbffeff000

def z850 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc000c0f8 0x3ffbfffffc000c0f

def z851 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe63c1fc03f00ff0b 0x1e63c1fc03f00ff0

def z852 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xc3331c3c38e0f0fd 0xcc3331c3c38e0f0f

def z853 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcac3b3069cc0f4 0xb7dcac3b3069cc0f

def z854 : W := mkw 0x34130c2c18eab0a4 0x534130c2c18eab0a 0xebf31c3c38fff0fd 0xeebf31c3c38fff0f

def z855 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc0800004 0xfffbfffffc080000

def z856 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0003fffc0ff 0xc1fffe0003fffc0f

def z857 : W := mkw 0x6013000035ca0000 0x46013000035ca000 0x1ffbc0003fff0007 0xc1ffbc0003fff000

def z858 : W := mkw 0x3813b6c01acaea08 0x63813b6c01acaea0 0xf843ffc000ffff0c 0x1f843ffc000ffff0

def z859 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1dfbe0003eff0006 0xc1dfbe0003eff000

def z860 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc1130002 0x3ffffffffc113000

def z861 : W := mkw 0x14130c2c0820b0a4 0x514130c2c0820b0a 0xebb31c3c3800f0f9 0xeebb31c3c3800f0f

def z862 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcee3b3079fccfe 0xf7dcee3b3079fccf

def z863 : W := mkw 0x590004856f31ffc8 0x0590004856f31ffc 0x000000003f00ffcb 0xc000000003f00ffc

def z864 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbfcfe04fc1733fcf 0x7bfcfe04fc1733fc

def z865 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbc1fc03f00ffcf 0xfefbc1fc03f00ffc

def z866 : W := mkw 0xe03fba68b5ca0000 0xfe03fba68b5ca000 0x1ffffc003fff0007 0xc1ffffc003fff000

def z867 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xeab11c3c3860f0fd 0x6eab11c3c3860f0f

def z868 : W := mkw 0xa0135b7a90c00000 0x5a0135b7a90c0000 0xebb31ffff8e00005 0xfebb31ffff8e0000

def z869 : W := mkw 0x36134dbf1af4fcf6 0x536134dbf1af4fcf 0x9679df8f3e7c3c03 0x19679df8f3e7c3c0

def z870 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x41321c303880f0f8 0x841321c303880f0f

def z871 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x7dbbffbfc0000000 0x37dbbffbfc000000

def z872 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x9fbfffcfc0000000 0x19fbfffcfc000000

def z873 : W := mkw 0xb413ac2c98e0b0a4 0x7b413ac2c98e0b0a 0xebb33c3cf8e0f0fd 0xeebb33c3cf8e0f0f

def z874 : W := mkw 0xc03ffb7aa50a0000 0xfc03ffb7aa50a000 0xffffffffff1f0003 0xfffffffffff1f000

def z875 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x410ac3b0068cccf8 0x8410ac3b0068cccf

def z876 : W := mkw 0x01000005403115c0 0x001000005403115c 0x8205204fc1633f01 0x18205204fc1633f0

def z877 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xebb33c3cf8e3f0fd 0xeebb33c3cf8e3f0f

def z878 : W := mkw 0x7d0004857ff1ffec 0x07d0004857ff1ffe 0x004000003ff3ffff 0xc004000003ff3fff

def z879 : W := mkw 0xa03ffb7a90ca0000 0xfa03ffb7a90ca000 0xffbfffffc0630000 0x3ffbfffffc063000

def z880 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe2341fc03f00ff0b 0xde2341fc03f00ff0

def z881 : W := mkw 0x793fa4857ffbffc8 0xe793fa4857ffbffc 0x1fffe0003fffffcf 0xc1fffe0003fffffc

def z882 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xe1301c3c3800f0f8 0xae1301c3c3800f0f

def z883 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe7b81fc03e00ff0b 0xde7b81fc03e00ff0

def z884 : W := mkw 0x602ca00035ca0000 0xa602ca00035ca000 0x17fce0003fff0007 0xc17fce0003fff000

def z885 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffffffffff9c0007 0xfffffffffff9c000

def z886 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xf7fc3fc03f13ff0b 0xdf7fc3fc03f13ff0

def z887 : W := mkw 0x402c124025000000 0x8402c12402500000 0xfffd3fcfff730007 0xffffd3fcfff73000

def z888 : W := mkw 0x802c5b7a80000000 0x9802c5b7a8000000 0xffbedfffc0000000 0x3ffbedfffc000000

def z889 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xffbfffffc0e00004 0x3ffbfffffc0e0000

def z890 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe7bedfffc0000000 0x3e7bedfffc000000

def z891 : W := mkw 0x3413ac2c18eab0a4 0x73413ac2c18eab0a 0xfffbfc3c3efff0ff 0xefffbfc3c3efff0f

def z892 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xff8fffffc0000000 0x3ff8fffffc000000

def z893 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffffffffff9f0002 0xbffffffffff9f000

def z894 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xfdcac3ffc69cccfe 0xffdcac3ffc69cccf

def z895 : W := mkw 0x01000005403115c0 0x001000005403115c 0xfec5207fc173ffff 0x7fec5207fc173fff

def z896 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe00fffff0007 0xe1fffe00fffff000

def z897 : W := mkw 0x683fb24035ca0208 0xe683fb24035ca020 0x1fffe0403fff0307 0xc1fffe0403fff030

def z898 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0xe7b81f803f00ff0b 0xde7b81f803f00ff0

def z899 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c3c39e0ffff 0xeebb31c3c39e0fff

def z900 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe2053fffc0000000 0x3e2053fffc000000

def z901 : W := mkw 0x80135b7a80000000 0x580135b7a8000000 0xe2311fffc0000000 0x3e2311fffc000000

def z902 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbffffffeec0005 0xfffbffffffeec000

def z903 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcac3b3079cffff 0xf7dcac3b3079cfff

def z904 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffffffffff7f0003 0x3ffffffffff7f000

def z905 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1d7fe0003fff0006 0x81d7fe0003fff000

def z906 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xf7bc3fc3ff00ff0b 0xdf7bc3fc3ff00ff0

def z907 : W := mkw 0x2013a00010ca0000 0x62013a00010ca000 0x1ffbe0003eff0007 0xc1ffbe0003eff000

def z908 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfff73c7c39f3ffff 0xffff73c7c39f3fff

def z909 : W := mkw 0x4b2c53d367154f5a 0x84b2c53d367154f5 0x144ce3c3c71f0f02 0x1144ce3c3c71f0f0

def z910 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x4bb31c3038e0f0fd 0xc4bb31c3038e0f0f

def z911 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xfffffffffefc0007 0xffffffffffefc000

def z912 : W := mkw 0x2713493f50f515f6 0x52713493f50f515f 0x1843e03fc0ff00f4 0x21843e03fc0ff00f

def z913 : W := mkw 0x0200419202044812 0x0020041920204481 0x7d8ac3b3068cc0fc 0xf7d8ac3b3068cc0f

def z914 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x49331c3c38e0f0fd 0xe49331c3c38e0f0f

def z915 : W := mkw 0x190004854a31ffc8 0x0190004854a31ffc 0x000000000000ffc8 0x0000000000000ffc

def z916 : W := mkw 0x580016c02f00ea08 0x0580016c02f00ea0 0xe3b01fc03f00ff0b 0xde3b01fc03f00ff0

def z917 : W := mkw 0x5b0004856f35ffda 0x05b0004856f35ffd 0x004000003fffffff 0xc004000003ffffff

def z918 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc1003301 0x3ffbfffffc100330

def z919 : W := mkw 0x603fa82835ca0000 0xf603fa82835ca000 0x9ffffc0c3fff0007 0xc9ffffc0c3fff000

def z920 : W := mkw 0x01000005403115c0 0x001000005403115c 0xba45204fc1733fcd 0x3ba45204fc1733fc

def z921 : W := mkw 0x3413ac2c18eab0a4 0x73413ac2c18eab0a 0xebb33c3c38e3f0fd 0xeebb33c3c38e3f0f

def z922 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcfe3f307ffffff 0xfffcfe3f307fffff

def z923 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcee3f3c69cccfe 0xf7dcee3f3c69cccf

def z924 : W := mkw 0x603fa82835ca0000 0xf603fa82835ca000 0xfffffc3c3fffc0ff 0xefffffc3c3fffc0f

def z925 : W := mkw 0x603fb24035ca0000 0xe603fb24035ca000 0xffffffcfffff0007 0xfffffffcfffff000

def z926 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec5204fc1f3ffff 0xfbec5204fc1f3fff

def z927 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb73c3c39e3f0fd 0xeebb73c3c39e3f0f

def z928 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xebb11c3c3860f0fd 0xeebb11c3c3860f0f

def z929 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xbfffe00c3fff0007 0xebfffe00c3fff000

def z930 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xfdcac3f3069cfffe 0xffdcac3f3069cfff

def z931 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0xe008dfffc0000000 0x3e008dfffc000000

def z932 : W := mkw 0x580004802f00ea08 0x0580004802f00ea0 0xbe85204fff00ff0b 0xfbe85204fff00ff0

def z933 : W := mkw 0x01000005403115c0 0x001000005403115c 0xffc7207fc1733fcf 0x7ffc7207fc1733fc

def z934 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe9821fffc080c0fc 0xfe9821fffc080c0f

def z935 : W := mkw 0xc03ffb7aa50a0000 0xfc03ffb7aa50a000 0xffbfffffc60c0000 0x3ffbfffffc60c000

def z936 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffd3fcfff73ff0f 0xffffd3fcfff73ff0

def z937 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x61321c303880c0f8 0xa61321c303880c0f

def z938 : W := mkw 0x0300419342154d52 0x00300419342154d5 0xffcfe3ffc79fcffe 0xfffcfe3ffc79fcff

def z939 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xdb3fffffc0000000 0x2db3fffffc000000

def z940 : W := mkw 0x100004040820b080 0x0100004040820b08 0xebb31c3c38e0f0fd 0xeebb31c3c38e0f0f

def z941 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffbfffffff003f0b 0xfffbfffffff003f0

def z942 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x5dcac3b0069cccfe 0xc5dcac3b0069cccf

def z943 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfff73c7ff9f3f0ff 0xffff73c7ff9f3f0f

def z944 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe9331c3c38e0f0fc 0xae9331c3c38e0f0f

def z945 : W := mkw 0x6013a00035ca0000 0x66013a00035ca000 0x0042c0003fff0007 0xc0042c0003fff000

def z946 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0x5803ffbfc0000000 0x25803ffbfc000000

def z947 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0x40001fbfc0000000 0x240001fbfc000000

def z948 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c7c38e0fffd 0xfebb31c7c38e0fff

def z949 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c3c3880f0f8 0xaebb31c3c3880f0f

def z950 : W := mkw 0xf83ffffabfcaea08 0xff83ffffabfcaea0 0x413adfb03e8cc000 0x8413adfb03e8cc00

def z951 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xfffffffff9730007 0x7fffffffff973000

def z952 : W := mkw 0x4a2c53d327144e5a 0x84a2c53d327144e5 0x1448c383061c0c02 0x11448c383061c0c0

def z953 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x8a331c3c38e0f0fd 0xe8a331c3c38e0f0f

def z954 : W := mkw 0x6013a00035ca0000 0x66013a00035ca000 0x1bf3e0003fff0007 0xc1bf3e0003fff000

def z955 : W := mkw 0xb42cf75698e0b0a4 0xab42cf75698e0b0a 0x140ce3c3f8e0f0fd 0xd140ce3c3f8e0f0f

def z956 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bedfc03f8cff0b 0xde7bedfc03f8cff0

def z957 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xea811fffc0000000 0x3ea811fffc000000

def z958 : W := mkw 0x003fb24000000000 0xe003fb2400000000 0xffbfffcfc0000000 0x3ffbfffcfc000000

def z959 : W := mkw 0x100004000800a000 0x0100004000800a00 0x69b21c303880c0fc 0xe69b21c303880c0f

def z960 : W := mkw 0xe03fba68b5ca0000 0xfe03fba68b5ca000 0xfffffc7cffff0007 0xefffffc7cffff000

def z961 : W := mkw 0x0200419202044812 0x0020041920204481 0x610ac3b0068cc0f8 0xa610ac3b0068cc0f

def z962 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe0001fffc000c0f8 0x3e0001fffc000c0f

def z963 : W := mkw 0x4a2cf3d3271e4e5a 0xa4a2cf3d3271e4e5 0x144ce3c3071f0f02 0x1144ce3c3071f0f0

def z964 : W := mkw 0x582c16c02f0aea08 0x8582c16c02f0aea0 0xe7fc1fc03f1fff0b 0xde7fc1fc03f1fff0

def z965 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xa6bc1fc03f003f0b 0x5a6bc1fc03f003f0

def z966 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc1733f0f 0x7ffffffffc1733f0

def z967 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x47bc1f803f00ff0b 0xc47bc1f803f00ff0

def z968 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03f80ffff 0xde7bc1fc03f80fff

def z969 : W := mkw 0x0300419342154d52 0x00300419342154d5 0x7dcac3f3c69ccffe 0xf7dcac3f3c69ccff

def z970 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbfc7204fc1f33fcf 0xfbfc7204fc1f33fc

def z971 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x17fde0003f7f0003 0xc17fde0003f7f000

def z972 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0x5fffffbfffff0007 0xe5fffffbfffff000

def z973 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xfeb53fffc0000000 0x3feb53fffc000000

def z974 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe0001fffc0003f08 0x3e0001fffc0003f0

def z975 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0xe0043fffc0000000 0x3e0043fffc000000

def z976 : W := mkw 0x0000000000000000 0x0000000000000000 0xbec5204fc1733f0f 0x7bec5204fc1733f0

def z977 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbd1fc03f60ff0f 0xdefbd1fc03f60ff0

def z978 : W := mkw 0x10130c280800a000 0x510130c280800a00 0xebb31c3c3880f0fd 0xeebb31c3c3880f0f

def z979 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x3fffe0003fff0c0f 0xd3fffe0003fff0c0

def z980 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe1301fc03800ff08 0x9e1301fc03800ff0

def z981 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcec3f3069cccfe 0xfffcec3f3069cccf

def z982 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfbb33c3ff8e0f0fd 0xefbb33c3ff8e0f0f

def z983 : W := mkw 0xa013fb7a90ca0000 0x7a013fb7a90ca000 0xf843ffffc0ff0004 0x3f843ffffc0ff000

def z984 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbedfc03f00ff0b 0xdffbedfc03f00ff0

def z985 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xd73fffffc0000000 0x1d73fffffc000000

def z986 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1bfbe0003eff0005 0xc1bfbe0003eff000

def z987 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffffffffffffc0ff 0xfffffffffffffc0f

def z988 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfbf3dc3c38fcf0fd 0xefbf3dc3c38fcf0f

def z989 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x6bb31c3038e0c0fd 0xe6bb31c3038e0c0f

def z990 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc080c030 0xbffbfffffc080c03

def z991 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x453c1fc03f00ff0b 0xd453c1fc03f00ff0

def z992 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xffb73c7ff9e3f3fd 0xfffb73c7ff9e3f3f

def z993 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x1842c0003fff0007 0xc1842c0003fff000

def z994 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0xfbb3ffffc0000000 0x3fbb3ffffc000000

def z995 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe3b01fffc0000000 0x3e3b01fffc000000

def z996 : W := mkw 0xc22cf3d3a71e4c52 0xac22cf3d3a71e4c5 0x144ce3c3c71f0c02 0x1144ce3c3c71f0c0

def z997 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe3b21c3038e0f0fd 0xce3b21c3038e0f0f

def z998 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0003f7f0003 0x01fffe0003f7f000

def z999 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xc73c1fc03f00ff03 0x9c73c1fc03f00ff0

def z1000 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe1321c3c38e0f0fd 0xee1321c3c38e0f0f

def z1001 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xefb73c7cf9e3ffff 0xfefb73c7cf9e3fff

def z1002 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffffffffffff3f0f 0xfffffffffffff3f0

def z1003 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc0730004 0x3ffffffffc073000

def z1004 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0x41321c303880c0fc 0xc41321c303880c0f

def z1005 : W := mkw 0xa03ffb7a90ca0000 0xfa03ffb7a90ca000 0xfffffffff8ff0005 0xffffffffff8ff000

def z1006 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe3b21c3c3880f0f9 0xee3b21c3c3880f0f

def z1007 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xfffffffff9ff0005 0x3fffffffff9ff000

def z1008 : W := mkw 0x1b0057d74a35ffda 0x01b0057d74a35ffd 0xe0001fffc000fff8 0x3e0001fffc000fff

def z1009 : W := mkw 0x5a2c16c02f04ea1a 0x85a2c16c02f04ea1 0xe7bc1fc03f8cff3b 0xde7bc1fc03f8cff3

def z1010 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x794ac3b3069cccfc 0xb794ac3b3069cccf

def z1011 : W := mkw 0x01000005403115c0 0x001000005403115c 0x9ec5204fc1733f07 0x59ec5204fc1733f0

def z1012 : W := mkw 0x602ca00035ca0000 0xa602ca00035ca000 0x0048c0003fff0007 0xc0048c0003fff000

def z1013 : W := mkw 0x01000005403115c0 0x001000005403115c 0x9e45204fc1733fc7 0x39e45204fc1733fc

def z1014 : W := mkw 0xc83ffb7aa5000208 0xfc83ffb7aa500020 0xffbfffffc1000300 0x3ffbfffffc100030

def z1015 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x1448c0003fff0007 0xc1448c0003fff000

def z1016 : W := mkw 0x100004000800a000 0x0100004000800a00 0xe3b01c303800f0f9 0xee3b01c303800f0f

def z1017 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x82353fcfc0000000 0x182353fcfc000000

def z1018 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xe7bcdfc03f0cff0b 0xde7bcdfc03f0cff0

def z1019 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xf63dffffc0000000 0x3f63dffffc000000

def z1020 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbe1fc03f80ff0f 0xdefbe1fc03f80ff0

def z1021 : W := mkw 0x603fb24035ca0000 0xe603fb24035ca000 0xffffffc03fff3f0f 0xdffffffc03fff3f0

def z1022 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0xebb21c303880f0fd 0xeebb21c303880f0f

def z1023 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1efde0003f7f0007 0x41efde0003f7f000

def z1024 : W := mkw 0x01000005403115c0 0x001000005403115c 0x9645204fc1733fcf 0x59645204fc1733fc

def z1025 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x157ee0003fff0007 0xc157ee0003fff000

def z1026 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xf4043fffc0000000 0x3f4043fffc000000

def z1027 : W := mkw 0x803f5b7a80000000 0xd803f5b7a8000000 0xefbf1fffc0000000 0x3efbf1fffc000000

def z1028 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xfa37ffffc0000000 0x3fa37ffffc000000

def z1029 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xfff31c3c38f0f0ff 0xefff31c3c38f0f0f

def z1030 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xffb31c3f38e0f0fd 0xfffb31c3f38e0f0f

def z1031 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xbebdffcfc0000000 0x3bebdffcfc000000

def z1032 : W := mkw 0x802c5b7a80000000 0x9802c5b7a8000000 0xe2341fffc0000000 0x3e2341fffc000000

def z1033 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xfffadfb3069cccfe 0xffffadfb3069cccf

def z1034 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xfbbbffbfc0000000 0x2fbbbffbfc000000

def z1035 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcbe3b306ffccfe 0xf7dcbe3b306ffccf

def z1036 : W := mkw 0x6000000035ca0000 0x06000000035ca000 0x1fcfe0003fff0007 0xc1fcfe0003fff000

def z1037 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe6841fffc0000000 0x3e6841fffc000000

def z1038 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x614ac3b3069cccfe 0xf614ac3b3069cccf

def z1039 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xefb31c3c38e0fcff 0xfefb31c3c38e0fcf

def z1040 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc0000c0a 0x7ffbfffffc0000c0

def z1041 : W := mkw 0x003f1a6800000000 0xd003f1a680000000 0xffbf3fffc0000000 0x3ffbf3fffc000000

def z1042 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1b7fe0003fff0005 0x81b7fe0003fff000

def z1043 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x754ac3b3069cccfa 0xb754ac3b3069cccf

def z1044 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc7ff0007 0xfffffffffc7ff000

def z1045 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc1000f02 0x3ffbfffffc1000f0

def z1046 : W := mkw 0x402ca000250a0000 0xa402ca000250a000 0x1ffde0003f7f0007 0xc1ffde0003f7f000

def z1047 : W := mkw 0x6013a00035ca0000 0x66013a00035ca000 0x1dcbe0003fff0007 0xc1dcbe0003fff000

def z1048 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7c4ac3b3069cccfe 0x37c4ac3b3069cccf

def z1049 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xbfffe04fffff3f0f 0xfbfffe04fffff3f0

def z1050 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe6b41fc03900ff0b 0x5e6b41fc03900ff0

def z1051 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b81f803f00ff0b 0xce3b81f803f00ff0

def z1052 : W := mkw 0x6013a00035ca0000 0x66013a00035ca000 0x1843e0003eff0004 0x81843e0003eff000

def z1053 : W := mkw 0x4a2c53d327144e5a 0x84a2c53d327144e5 0x040c03c307000f02 0x1040c03c307000f0

def z1054 : W := mkw 0x643fa82835ca0024 0xf643fa82835ca002 0x1fffe0303fff0037 0xc1fffe0303fff003

def z1055 : W := mkw 0xa03ffb7a90ca0000 0xfa03ffb7a90ca000 0xffbfffffc08c0000 0x3ffbfffffc08c000

def z1056 : W := mkw 0x01000005403115c0 0x001000005403115c 0xaa85204fc1633fcd 0x7aa85204fc1633fc

def z1057 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffc1fc03f10ff0f 0xdfffc1fc03f10ff0

def z1058 : W := mkw 0x14000c2c0820b0a4 0x114000c2c0820b0a 0xe2301c3c3800f0f9 0x2e2301c3c3800f0f

def z1059 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x69b21c3038e0f0fd 0xe69b21c3038e0f0f

def z1060 : W := mkw 0x0000008002004800 0x0000000800200480 0x7dcac3b0069cccfe 0xf7dcac3b0069cccf

def z1061 : W := mkw 0x0300419342154d52 0x00300419342154d5 0x7dcae3b3c69fccfe 0xf7dcae3b3c69fccf

def z1062 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe33c1fc03f00ff09 0x9e33c1fc03f00ff0

def z1063 : W := mkw 0x370004855af5fdf6 0x0370004855af5fdf 0x004000003fffffff 0xc004000003ffffff

def z1064 : W := mkw 0x002c535200000000 0x8002c53520000000 0xffbfffffc0000000 0x3ffbfffffc000000

def z1065 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbec5204fc7ff3fcf 0xfbec5204fc7ff3fc

def z1066 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0xfe8dffffc0000000 0x3fe8dffffc000000

def z1067 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe1381fc03f00ff0b 0xde1381fc03f00ff0

def z1068 : W := mkw 0x0000124000000000 0x0000012400000000 0xfe853fcfc0000000 0x3fe853fcfc000000

def z1069 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xc33c1fc03f00ff0b 0xcc33c1fc03f00ff0

def z1070 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe3b81fc03e00ff09 0xde3b81fc03e00ff0

def z1071 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc08000f4 0x3ffbfffffc08000f

def z1072 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x197be0003fff0007 0xc197be0003fff000

def z1073 : W := mkw 0x01000005403115c0 0x001000005403115c 0xa685204fc1633fcb 0x7a685204fc1633fc

def z1074 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbffffff8000001 0xfffbffffff800000

def z1075 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcfe3ffc79cffff 0xfffcfe3ffc79cfff

def z1076 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffbffffff9000001 0x3ffbffffff900000

def z1077 : W := mkw 0x34000c2c18e0b0a4 0x134000c2c18e0b0a 0xe3b01c3c38e0f0fd 0xee3b01c3c38e0f0f

def z1078 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x017ac0003eff0004 0x8017ac0003eff000

def z1079 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xfc801fffc0000000 0x3fc801fffc000000

def z1080 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe0301fc03800ff08 0x1e0301fc03800ff0

def z1081 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb71c7c39e0f3fd 0xeebb71c7c39e0f3f

def z1082 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc61c0002 0x3ffffffffc61c000

def z1083 : W := mkw 0x34130c2818c0a024 0x534130c2818c0a02 0xebb31c3c3880c0fc 0xeebb31c3c3880c0f

def z1084 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7dcac3b307ffccff 0xf7dcac3b307ffccf

def z1085 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe53c1fc03f00ff0a 0x9e53c1fc03f00ff0

def z1086 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbecde04fc77f3fcf 0x7becde04fc77f3fc

def z1087 : W := mkw 0xe03fa828b5ca0000 0xfe03fa828b5ca000 0x1fffe00cffff0007 0xc1fffe00cffff000

def z1088 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbfffffff630003 0xfffbfffffff63000

def z1089 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x5dcac3b3069cc0f6 0xe5dcac3b3069cc0f

def z1090 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x82341fc039003f01 0x182341fc039003f0

def z1091 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xffbffffff8800000 0xbffbffffff880000

def z1092 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03e00ff08 0x9e7bc1fc03e00ff0

def z1093 : W := mkw 0xe03fb240b5ca0000 0xee03fb240b5ca000 0x1fffe040ffff0007 0xc1fffe040ffff000

def z1094 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe5b81fc03e00ff0a 0xde5b81fc03e00ff0

def z1095 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe043ffff0007 0xd1fffe043ffff000

def z1096 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe6841fffc1003f0b 0x7e6841fffc1003f0

def z1097 : W := mkw 0xe03ffb7ab5c00000 0xfe03ffb7ab5c0000 0xffbfffffffe00007 0xfffbfffffffe0000

def z1098 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x037fe0003fff0007 0xc037fe0003fff000

def z1099 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xffb73c7ff9e0ffff 0xfffb73c7ff9e0fff

def z1100 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc1630001 0x3ffbfffffc163000

def z1101 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbd3fc03f00ff0b 0xdffbd3fc03f00ff0

def z1102 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x41321c3038e0c0f4 0x841321c3038e0c0f

def z1103 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xf93bffffc0000000 0x3f93bffffc000000

def z1104 : W := mkw 0x01000005403115c0 0x001000005403115c 0xffc5204fc173ffcf 0xfffc5204fc173ffc

def z1105 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbe85204fc1633fc9 0x3be85204fc1633fc

def z1106 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c3c3860f0f9 0x2ebb31c3c3860f0f

def z1107 : W := mkw 0x802cfb7a80000000 0xb802cfb7a8000000 0xf7bcffffc0000000 0x3f7bcffffc000000

def z1108 : W := mkw 0x802c5b7a80000000 0x9802c5b7a8000000 0xffbd3fffc0000000 0x3ffbd3fffc000000

def z1109 : W := mkw 0x802c5b7a80000000 0x9802c5b7a8000000 0xe1381fffc0000000 0x3e1381fffc000000

def z1110 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xffbffffff8600001 0x3ffbffffff860000

def z1111 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffbffffffe000000 0xbffbffffffe00000

def z1112 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe7bd3fffc0000000 0x3e7bd3fffc000000

def z1113 : W := mkw 0x01000005403115c0 0x001000005403115c 0xfff53c4fc1733fcf 0x7fff53c4fc1733fc

def z1114 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bd3fccff00ff0b 0xde7bd3fccff00ff0

def z1115 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0x87bc1fc03f003f03 0xd87bc1fc03f003f0

def z1116 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x41321c3c3880c0f0 0xa41321c3c3880c0f

def z1117 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xcb331c3c38e0f0f5 0xacb331c3c38e0f0f

def z1118 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xefbe1ff03f00ff0b 0xfefbe1ff03f00ff0

def z1119 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0x80001fcfc0000000 0x180001fcfc000000

def z1120 : W := mkw 0x0200419302144c52 0x00200419302144c5 0xffcac3b3069cfcff 0xfffcac3b3069cfcf

def z1121 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xf408dfffc0000000 0x3f408dfffc000000

def z1122 : W := mkw 0x3400040418e0b0a4 0x03400040418e0b0a 0xebb21c3038e0f0fd 0xeebb21c3038e0f0f

def z1123 : W := mkw 0x402c000025000000 0x8402c00002500000 0x1fffe0003fff0007 0xc1fffe0003fff000

def z1124 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xea331c3c38e0f0fd 0x2ea331c3c38e0f0f

def z1125 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xfff73c7cf9f3f3ff 0xefff73c7cf9f3f3f

def z1126 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x69b31c3c38e0c0fc 0xe69b31c3c38e0c0f

def z1127 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0403fff0f07 0xd1fffe0403fff0f0

def z1128 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xebb73fffc0000000 0x3ebb73fffc000000

def z1129 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x7fcbc3b306fcccff 0xf7fcbc3b306fcccf

def z1130 : W := mkw 0x602ca00035ca0000 0xa602ca00035ca000 0x1ecde0003fff0007 0xc1ecde0003fff000

def z1131 : W := mkw 0x790004857ffbffc8 0x0790004857ffbffc 0x004000003fffffcf 0xc004000003fffffc

def z1132 : W := mkw 0x01000005403115c0 0x001000005403115c 0x1c45204fc1733fcf 0x71c45204fc1733fc

def z1133 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc0100006 0x7ffffffffc010000

def z1134 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xf7fcdfc03f1cff0b 0xdf7fcdfc03f1cff0

def z1135 : W := mkw 0xe03fba68b5ca0000 0xfe03fba68b5ca000 0xffffffccffff0007 0xdffffffccffff000

def z1136 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x69cac3b0069cccfe 0xe69cac3b0069cccf

def z1137 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xf802dfffc0000000 0x3f802dfffc000000

def z1138 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0xe002dfffc0000000 0x3e002dfffc000000

def z1139 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0xfe87ffffc0000000 0x3fe87ffffc000000

def z1140 : W := mkw 0x603fa82835ca0000 0xf603fa82835ca000 0x5ffffc303fff0007 0xc5ffffc303fff000

def z1141 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xbfffe0403fff0007 0xdbfffe0403fff000

def z1142 : W := mkw 0x80135b7a80000000 0x580135b7a8000000 0xe8031fffc0000000 0x3e8031fffc000000

def z1143 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc000c008 0xfffbfffffc000c00

def z1144 : W := mkw 0x603fb24035ca0000 0xe603fb24035ca000 0x1fffe3c03fff0007 0xd1fffe3c03fff000

def z1145 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbfffffffef0001 0xbffbfffffffef000

def z1146 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1fffe0003fff3f0f 0xc1fffe0003fff3f0

def z1147 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0x9fffffcfffff0007 0xd9fffffcfffff000

def z1148 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x7fffe0303fff0007 0xe7fffe0303fff000

def z1149 : W := mkw 0x582cb6c02f0aea08 0xa582cb6c02f0aea0 0xe7bc3fc03f03ff0b 0xde7bc3fc03f03ff0

def z1150 : W := mkw 0x03000005403515d2 0x003000005403515d 0xbec5204fc1ff3fff 0x7bec5204fc1ff3ff

def z1151 : W := mkw 0x6013a00035ca0000 0x66013a00035ca000 0x1ec7e0003fff0007 0xc1ec7e0003fff000

def z1152 : W := mkw 0x602ca00035ca0000 0xa602ca00035ca000 0x144ce0003f7f0003 0x0144ce0003f7f000

def z1153 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x1dfac0003fff0007 0xc1dfac0003fff000

def z1154 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x1c4ac3b3069cccfe 0xf1c4ac3b3069cccf

def z1155 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0xbfffe0003fff300f 0xcbfffe0003fff300

def z1156 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe9b21c3c3880f0fc 0xee9b21c3c3880f0f

def z1157 : W := mkw 0xa03ffb7a90ca0000 0xfa03ffb7a90ca000 0xffffffffc1ff0007 0x7ffffffffc1ff000

def z1158 : W := mkw 0x180016c00a00ea08 0x0180016c00a00ea0 0xe2301fc03800ff09 0x1e2301fc03800ff0

def z1159 : W := mkw 0x35130c2c58e1b1a4 0x535130c2c58e1b1a 0xebb31c7cf8e0f3fd 0xeebb31c7cf8e0f3f

def z1160 : W := mkw 0xc03ffb7aa50a0000 0xfc03ffb7aa50a000 0xffffffffc79f0006 0xfffffffffc79f000

def z1161 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7fc1fc03f9cff0f 0xde7fc1fc03f9cff0

def z1162 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xe33fffffc0000000 0x3e33fffffc000000

def z1163 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0x4bb31c3c38e0c0f5 0xe4bb31c3c38e0c0f

def z1164 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc69cc0fe 0xfffffffffc69cc0f

def z1165 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xfffffffffe9c0006 0xffffffffffe9c000

def z1166 : W := mkw 0x592c04856f31ffc8 0x8592c04856f31ffc 0x1ffd20003f73ffcf 0xc1ffd20003f73ffc

def z1167 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xf7bdffcfc0000000 0x1f7bdffcfc000000

def z1168 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbc45204fc1733fce 0x3bc45204fc1733fc

def z1169 : W := mkw 0x803ffb7a800a0000 0xf803ffb7a800a000 0xffffffffc01f0000 0x3ffffffffc01f000

def z1170 : W := mkw 0x182c16c00a00ea08 0x8182c16c00a00ea0 0xe7bc1fc03800ff09 0xde7bc1fc03800ff0

def z1171 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb73c7cf8e0f0fd 0xeebb73c7cf8e0f0f

def z1172 : W := mkw 0x603fa82835ca0000 0xf603fa82835ca000 0xfffffc7fffff0007 0xffffffc7fffff000

def z1173 : W := mkw 0x002c124000000000 0x8002c12400000000 0xe7bc1fcfc0000000 0x3e7bc1fcfc000000

def z1174 : W := mkw 0xc03ffb7aa50a0000 0xfc03ffb7aa50a000 0xffffffffc77f0007 0x7ffffffffc77f000

def z1175 : W := mkw 0x80135b7a80000000 0x580135b7a8000000 0xe1321fffc0000000 0x3e1321fffc000000

def z1176 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x7fffe3803fff0007 0xd7fffe3803fff000

def z1177 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe3b11c3c3860f0f9 0xee3b11c3c3860f0f

def z1178 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x07fec0003fff0007 0xc07fec0003fff000

def z1179 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffffffffc09c0004 0x3ffffffffc09c000

def z1180 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bd3fc03f63ff0b 0xde7bd3fc03f63ff0

def z1181 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x9fffe04cffff0007 0xc9fffe04cffff000

def z1182 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x5fffe0303fffc037 0xc5fffe0303fffc03

def z1183 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xffbbdc3c38e0f0fd 0xeffbbdc3c38e0f0f

def z1184 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffbffffff9e30005 0xfffbffffff9e3000

def z1185 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xe2311c3c38e0f0fd 0xee2311c3c38e0f0f

def z1186 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xebb31c3c38e0c0f4 0xaebb31c3c38e0c0f

def z1187 : W := mkw 0x0000124000000000 0x0000012400000000 0xe0001fcfc0000000 0x3e0001fcfc000000

def z1188 : W := mkw 0xa03ffb7a90c00000 0xfa03ffb7a90c0000 0xffbffffff8e0c0fd 0xfffbffffff8e0c0f

def z1189 : W := mkw 0xa03ffb7a90ca0000 0xfa03ffb7a90ca000 0xffffffffc6ff0006 0xfffffffffc6ff000

def z1190 : W := mkw 0x3413ac2c18e0b0a4 0x73413ac2c18e0b0a 0xfbb3fc3c38e0f0fd 0xefbb3fc3c38e0f0f

def z1191 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xffffffffc7ff0006 0x3ffffffffc7ff000

def z1192 : W := mkw 0x01000005403115c0 0x001000005403115c 0xbfcd204fc7733fcf 0xfbfcd204fc7733fc

def z1193 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xffbc1fc33f00ff0b 0xfffbc1fc33f00ff0

def z1194 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1ff03f00fffb 0xfe7bc1ff03f00fff

def z1195 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7bc1fc03f003f03 0x1e7bc1fc03f003f0

def z1196 : W := mkw 0x3013040018c0a000 0x43013040018c0a00 0xebb31c3038e0f0fd 0xeebb31c3038e0f0f

def z1197 : W := mkw 0x603fa00035ca0000 0xe603fa00035ca000 0x7fffe0003fffc00f 0xc7fffe0003fffc00

def z1198 : W := mkw 0x603fb24035ca0000 0xe603fb24035ca000 0x9ffffc403fff0007 0xc9ffffc403fff000

def z1199 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x414ac3b0069cc0f4 0x8414ac3b0069cc0f

def z1200 : W := mkw 0x0200419202044812 0x0020041920204481 0x6d8ac3b0068cccfe 0xf6d8ac3b0068cccf

def z1201 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x5fbfffbfc0000000 0x25fbfffbfc000000

def z1202 : W := mkw 0x603fba6835ca0000 0xf603fba6835ca000 0xfffffffc3fff0007 0xffffffffc3fff000

def z1203 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x413adfbfc0000000 0x2413adfbfc000000

def z1204 : W := mkw 0x802cf35280000000 0xa802cf3528000000 0xffbdffcfc0000000 0x3ffbdffcfc000000

def z1205 : W := mkw 0x0200419302144c52 0x00200419302144c5 0x79cac3b3069cc0fc 0xe79cac3b3069cc0f

def z1206 : W := mkw 0xc03ffb7aa5000000 0xfc03ffb7aa500000 0xffffffffff730007 0xfffffffffff73000

def z1207 : W := mkw 0x8013fb7a80000000 0x78013fb7a8000000 0xfd8bffffc0000000 0x3fd8bffffc000000

def z1208 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xfffedff03f9cffff 0xffffedff03f9cfff

def z1209 : W := mkw 0x190004854a31ffc8 0x0190004854a31ffc 0x004000000173ffcf 0x4004000000173ffc

def z1210 : W := mkw 0x80005b7a80000000 0x180005b7a8000000 0xe5881fffc0000000 0x3e5881fffc000000

def z1211 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xebbbdfffc0000000 0x3ebbbdfffc000000

def z1212 : W := mkw 0x3413ac2c18eab0a4 0x73413ac2c18eab0a 0xfff7fc3c39fff0ff 0xefff7fc3c39fff0f

def z1213 : W := mkw 0x8000fb7a80000000 0x38000fb7a8000000 0xf000ffffc0000000 0x3f000ffffc000000

def z1214 : W := mkw 0x582c16c02f00ea08 0x8582c16c02f00ea0 0xe7be1ff03f80ff3b 0xde7be1ff03f80ff3

def z1215 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xefb71c7c38e0f0fd 0xfefb71c7c38e0f0f

def z1216 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0xffbfffffc00000cc 0x7ffbfffffc00000c

def z1217 : W := mkw 0x102c16400800a000 0x8102c16400800a00 0xe7bc1fc03900ff0b 0xde7bc1fc03900ff0

def z1218 : W := mkw 0x34130c2c18e0b0a4 0x534130c2c18e0b0a 0xffb73c3c38e0f0fd 0xeffb73c3c38e0f0f

def z1219 : W := mkw 0xe03ffb7ab5ca0000 0xfe03ffb7ab5ca000 0xe13adffffe8c0000 0xbe13adffffe8c000

def z1220 : W := mkw 0x803ffb7a80000000 0xf803ffb7a8000000 0x9e3fffffc0000000 0x39e3fffffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z9])],[(1,[z10,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z12,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z13,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z14,z6]),(0,[z0,z1,z3,z4,z15,z5,z6]),(0,[z0,z1,z16,z3,z4,z5,z6]),(0,[z0,z1,z17,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z19,z6]),(0,[z0,z1,z3,z20,z4,z5,z6]),(0,[z0,z1,z21,z3,z4,z5,z6])],[(1,[z0,z22,z3,z4,z5,z6]),(0,[z23,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z24,z5,z6]),(0,[z0,z1,z21,z3,z4,z5,z25]),(0,[z0,z1,z26,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z27,z5,z6]),(0,[z0,z1,z3,z4,z5,z28,z6]),(0,[z29,z0,z1,z30,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z31]),(0,[z32,z0,z1,z3,z4,z5,z6]),(0,[z33,z34,z1,z3,z4,z5,z6]),(0,[z0,z35,z1,z3,z4,z5,z6]),(0,[z0,z1,z36,z3,z4,z5,z6]),(0,[z0,z1,z37,z3,z4,z5,z38]),(0,[z0,z1,z39,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z3,z41,z4,z5,z6]),(0,[z0,z1,z3,z4,z42,z43,z6]),(0,[z0,z1,z3,z44,z4,z5,z6]),(0,[z0,z1,z3,z4,z45,z5,z6])],[(0,[z0,z1,z3,z46,z4,z5,z6]),(0,[z0,z11,z3,z4,z5,z6,z47]),(0,[z48,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z49,z5,z6]),(0,[z50,z0,z1,z3,z4,z5,z6]),(0,[z51,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z52,z3,z4,z5,z6]),(0,[z0,z1,z53,z3,z4,z5,z6]),(0,[z0,z54,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z6,z8]),(0,[z0,z1,z56,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z57]),(0,[z58,z0,z1,z3,z4,z5,z6]),(0,[z59,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z60,z4,z5,z6])],[(0,[z61,z0,z1,z62,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z64,z6]),(1,[z0,z1,z3,z4,z14,z6]),(1,[z0,z1,z3,z4,z5,z25]),(0,[z0,z1,z3,z4,z5,z6,z65])],[(0,[z66,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z67]),(0,[z29,z0,z1,z68,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z69,z6]),(0,[z70,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z71,z6])],[(0,[z0,z11,z3,z4,z5,z42,z6]),(0,[z0,z1,z72,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z73,z5,z6]),(0,[z0,z1,z3,z4,z5,z74,z6]),(0,[z0,z1,z75,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z76,z6]),(0,[z0,z1,z77,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z79,z4,z5,z6]),(0,[z0,z1,z36,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z81,z6]),(0,[z0,z82,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z83,z6]),(0,[z0,z1,z3,z4,z5,z6,z84]),(0,[z63,z85,z0,z1,z3,z4,z5]),(0,[z86,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z87,z5,z6]),(1,[z0,z1,z3,z4,z43,z8]),(1,[z85,z0,z1,z3,z5,z88])],[(0,[z0,z1,z3,z4,z5,z6,z89]),(0,[z90,z0,z1,z3,z4,z5,z6]),(0,[z29,z1,z3,z4,z5,z55,z6]),(0,[z0,z1,z17,z3,z4,z5,z8]),(0,[z0,z1,z37,z3,z4,z43,z6])]],
   [[(0,[z0,z1,z62,z4,z5,z43,z6]),(0,[z0,z1,z91,z3,z4,z5,z6]),(0,[z0,z1,z92,z3,z4,z5,z6]),(0,[z0,z1,z3,z93,z4,z5,z6]),(0,[z94,z0,z1,z3,z4,z5,z18]),(1,[z0,z1,z3,z4,z95,z8]),(0,[z96,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z97,z5,z98,z6]),(1,[z0,z99,z3,z100,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z18]),(0,[z102,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z103,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z104,z6])],[(0,[z0,z1,z11,z3,z4,z5,z18]),(0,[z0,z1,z3,z100,z5,z105,z6])],[(0,[z0,z106,z1,z3,z4,z5,z6]),(0,[z0,z107,z3,z4,z108,z5,z6]),(0,[z109,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z110])],[(0,[z0,z1,z3,z4,z5,z111,z6]),(0,[z112,z0,z1,z3,z4,z5,z113]),(0,[z48,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z114,z3,z5,z105,z6])],[(0,[z115,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z95,z5,z116]),(0,[z0,z1,z3,z4,z95,z5,z18]),(0,[z0,z1,z117,z4,z5,z43,z6]),(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z119,z4,z5,z6]),(0,[z0,z1,z120,z3,z4,z5,z121])],[(0,[z0,z1,z122,z3,z4,z5,z6]),(0,[z112,z0,z123,z3,z4,z5,z6]),(0,[z0,z124,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z125,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z126,z6])],[(0,[z0,z127,z3,z4,z5,z6,z47]),(0,[z0,z1,z3,z4,z128,z5,z6]),(0,[z0,z1,z36,z117,z4,z5,z6]),(0,[z0,z1,z17,z3,z5,z98,z6]),(0,[z0,z1,z3,z4,z5,z129,z6])]],
   [[(0,[z0,z1,z80,z3,z4,z5,z6]),(1,[z48,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z131]),(0,[z132,z0,z1,z3,z4,z5,z18]),(0,[z133,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z134,z3,z4,z5,z6])],[(0,[z135,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z136,z4,z5,z105,z6]),(0,[z0,z1,z36,z3,z137,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z138])],[(1,[z0,z1,z3,z4,z5,z84]),(0,[z63,z139,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z140,z4,z5,z6]),(1,[z0,z1,z3,z4,z141,z6]),(0,[z142,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z47]),(0,[z0,z1,z3,z4,z5,z143,z6])],[(0,[z0,z127,z3,z4,z5,z42,z6]),(0,[z0,z123,z1,z3,z4,z5,z6]),(1,[z0,z1,z144,z4,z5,z6]),(0,[z145,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z146,z3,z5,z6]),(0,[z0,z1,z3,z147,z4,z5,z8])],[(0,[z0,z1,z3,z4,z95,z6,z8]),(0,[z0,z1,z148,z3,z4,z5,z6])],[(0,[z0,z1,z3,z149,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z94,z0,z1,z3,z4,z5,z8]),(0,[z150,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z151,z4,z5,z6])],[(0,[z152,z0,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z130,z4,z5,z18]),(0,[z153,z0,z1,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z8]),(0,[z0,z155,z1,z3,z4,z5,z6]),(0,[z156,z0,z1,z3,z4,z5,z6])],[(0,[z0,z11,z3,z4,z157,z5,z6]),(0,[z0,z1,z11,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z158,z6]),(0,[z0,z1,z3,z159,z4,z5,z6]),(0,[z0,z1,z160,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z161])]],
   [[(0,[z162,z0,z1,z80,z4,z5,z6]),(0,[z48,z0,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z117,z4,z5,z6]),(0,[z0,z1,z163,z3,z4,z5,z6]),(1,[z0,z1,z164,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z165,z6]),(0,[z0,z1,z3,z4,z5,z6,z166]),(0,[z0,z1,z3,z4,z98,z6,z8])],[(0,[z0,z1,z3,z167,z4,z5,z6]),(0,[z115,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z95,z5,z8]),(0,[z0,z168,z169,z3,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z36,z4,z5,z6])],[(0,[z61,z170,z1,z3,z4,z5,z6]),(0,[z33,z171,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z172]),(0,[z0,z1,z3,z4,z173,z5,z18])],[(0,[z152,z0,z1,z174,z4,z5,z6]),(0,[z0,z1,z175,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z5,z176]),(0,[z0,z1,z3,z4,z173,z43,z6]),(0,[z0,z177,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z121,z8]),(0,[z0,z1,z3,z178,z4,z5,z6]),(0,[z179,z0,z1,z3,z4,z5,z6])],[(0,[z132,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z180,z6]),(0,[z0,z1,z3,z164,z4,z5,z6])],[(0,[z112,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z95,z6]),(0,[z132,z0,z1,z3,z157,z5,z6]),(0,[z33,z0,z1,z3,z4,z173,z6]),(1,[z0,z1,z3,z4,z5,z138])],[(0,[z0,z1,z3,z4,z5,z6,z181]),(0,[z33,z0,z1,z3,z4,z5,z182]),(0,[z0,z1,z3,z183,z4,z5,z88])]],
   [[(0,[z0,z1,z184,z3,z4,z98,z6])],[(0,[z0,z127,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z185,z6]),(0,[z186,z0,z1,z3,z4,z5,z6])],[(0,[z1,z11,z3,z4,z5,z55,z6]),(0,[z152,z1,z3,z4,z5,z55,z6]),(0,[z0,z1,z3,z4,z187,z5,z6]),(0,[z0,z1,z4,z5,z188,z6,z121]),(0,[z189,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z190,z3,z4,z5,z6])],[(0,[z0,z1,z3,z130,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z191,z131]),(0,[z0,z192,z1,z3,z4,z5,z6]),(1,[z0,z1,z21,z3,z4,z8]),(0,[z193,z0,z1,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z5,z6,z88])],[(0,[z0,z1,z3,z4,z5,z194,z6]),(0,[z195,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z180,z6])],[(0,[z196,z0,z1,z3,z4,z5,z6]),(0,[z197,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z198,z3,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z199]),(0,[z200,z0,z1,z3,z4,z5,z6])],[(0,[z201,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z202]),(0,[z0,z1,z184,z3,z97,z5,z6]),(0,[z0,z1,z3,z4,z5,z203,z6]),(0,[z0,z204,z1,z3,z4,z5,z6]),(0,[z205,z0,z1,z4,z5,z6,z121])],[(0,[z206,z0,z1,z3,z4,z5,z6]),(0,[z0,z127,z3,z4,z157,z5,z6]),(0,[z0,z1,z3,z207,z4,z5,z6]),(0,[z0,z1,z3,z208,z4,z5,z6]),(0,[z209,z0,z1,z3,z4,z5,z8]),(0,[z210,z0,z1,z3,z4,z5,z6]),(0,[z211,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z18,z212]),(0,[z213,z0,z1,z3,z4,z5,z18])]],
   [[(0,[z214,z0,z1,z3,z4,z5,z6]),(0,[z215,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z216]),(0,[z0,z1,z3,z4,z173,z5,z8])],[],[(0,[z0,z1,z3,z4,z157,z5,z6]),(0,[z0,z217,z1,z3,z4,z5,z8])],[(0,[z0,z218,z1,z3,z4,z5,z6]),(0,[z219,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z220,z5,z6]),(0,[z0,z1,z3,z4,z221,z5,z6]),(0,[z0,z1,z3,z4,z5,z222,z18])],[(0,[z0,z1,z3,z223,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z42,z6]),(0,[z0,z1,z114,z136,z4,z5,z6])],[],[(0,[z0,z127,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z224]),(0,[z0,z1,z3,z225,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z226,z8]),(0,[z61,z0,z1,z117,z4,z5,z6]),(0,[z227,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z228,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z229]),(0,[z0,z1,z3,z230,z4,z5,z6]),(0,[z189,z0,z1,z3,z4,z5,z8])]],
   [[(0,[z152,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z231,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z131]),(0,[z0,z99,z1,z3,z4,z5,z18]),(0,[z232,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z233,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z234,z6]),(0,[z0,z1,z235,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z98,z6])],[(0,[z0,z1,z3,z4,z236,z5,z6]),(0,[z0,z1,z237,z3,z4,z5,z6]),(0,[z0,z1,z169,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z238,z5,z6]),(0,[z0,z1,z3,z4,z5,z239,z6]),(0,[z0,z1,z3,z4,z5,z8,z8])],[(0,[z63,z0,z240,z3,z4,z5,z6]),(0,[z0,z1,z3,z137,z4,z42,z6]),(0,[z0,z1,z241,z3,z4,z5,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z21,z3,z4,z5,z18])],[(0,[z0,z1,z3,z174,z4,z5,z6]),(0,[z0,z168,z1,z169,z4,z5,z6]),(0,[z0,z1,z144,z4,z157,z5,z6]),(0,[z0,z1,z120,z3,z4,z5,z188]),(0,[z0,z1,z3,z4,z243,z5,z6])],[(0,[z0,z1,z3,z4,z244,z5,z6]),(0,[z0,z1,z3,z245,z4,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z246]),(0,[z0,z1,z247,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z176]),(0,[z154,z0,z1,z3,z4,z5,z47])],[(0,[z154,z0,z101,z3,z4,z5,z6]),(0,[z0,z1,z37,z3,z4,z5,z248])],[(1,[z0,z1,z249,z4,z5,z6]),(0,[z0,z1,z3,z250,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z251]),(0,[z0,z1,z3,z4,z5,z252,z6]),(0,[z0,z1,z3,z4,z5,z253,z6]),(0,[z0,z1,z3,z4,z5,z254,z6])],[(0,[z0,z1,z255,z3,z4,z5,z6]),(0,[z256,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z257,z6]),(1,[z0,z1,z3,z223,z5,z6]),(0,[z0,z1,z3,z4,z5,z258,z6]),(0,[z0,z1,z120,z3,z4,z5,z6]),(0,[z0,z1,z3,z259,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z260])],[(0,[z0,z1,z184,z3,z130,z5,z6]),(0,[z0,z168,z1,z136,z4,z5,z6]),(0,[z0,z1,z261,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z262]),(0,[z0,z1,z3,z4,z5,z18,z191])],[(0,[z0,z1,z263,z3,z4,z5,z6]),(0,[z264,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z265,z6])],[(0,[z0,z266,z1,z3,z4,z5,z18])],[(0,[z115,z0,z267,z3,z4,z5,z6]),(1,[z0,z1,z268,z4,z5,z6]),(0,[z0,z1,z3,z4,z269,z5,z6]),(0,[z0,z99,z1,z3,z4,z5,z8]),(0,[z154,z0,z3,z4,z5,z6,z47]),(0,[z0,z1,z3,z270,z4,z5,z6])],[(0,[z162,z1,z3,z62,z4,z5,z6]),(0,[z0,z1,z80,z4,z5,z43,z6]),(0,[z0,z99,z1,z3,z157,z5,z6]),(0,[z33,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z271,z3,z4,z5,z6]),(0,[z0,z1,z272,z3,z4,z5,z6]),(0,[z0,z1,z3,z273,z4,z5,z6])],[(0,[z274,z0,z1,z3,z4,z5,z6]),(0,[z112,z1,z3,z4,z97,z5,z6]),(1,[z0,z1,z3,z4,z55,z8]),(0,[z0,z1,z3,z100,z4,z5,z18]),(0,[z0,z1,z275,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z276,z3,z4,z5,z6]),(0,[z0,z1,z277,z3,z4,z5,z6]),(0,[z278,z0,z1,z3,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z279]),(0,[z0,z1,z21,z3,z4,z5,z8])],[(0,[z0,z1,z120,z80,z4,z5,z6]),(0,[z280,z0,z1,z3,z4,z97,z5]),(0,[z281,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z114,z3,z4,z5,z18]),(0,[z282,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z9]),(0,[z0,z1,z3,z4,z5,z283,z6]),(0,[z0,z1,z3,z284,z4,z5,z6])],[(0,[z285,z0,z1,z3,z4,z5,z6]),(0,[z0,z286,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z279,z8]),(0,[z0,z1,z3,z4,z5,z18,z279]),(0,[z0,z1,z3,z4,z5,z287,z6]),(0,[z0,z1,z288,z3,z4,z5,z6])],[(0,[z61,z0,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z289,z6]),(0,[z139,z0,z1,z3,z4,z5,z226]),(0,[z290,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z291,z3,z4,z5,z6]),(0,[z292,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z293,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z294,z6]),(0,[z0,z1,z295,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z296]),(0,[z0,z1,z3,z297,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z298]),(0,[z0,z1,z299,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z212])]],
   [[(0,[z300,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z61,z0,z168,z3,z4,z5,z6]),(0,[z0,z1,z3,z301,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z302,z5,z6]),(0,[z0,z1,z21,z3,z5,z98,z6])],[(0,[z303,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z304,z5,z6]),(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z306,z3,z4,z5,z6])],[(0,[z0,z1,z307,z3,z4,z5,z6]),(0,[z0,z1,z3,z308,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z5,z191])],[(1,[z0,z1,z122,z4,z5,z6]),(1,[z0,z168,z169,z4,z5,z6]),(1,[z0,z1,z3,z309,z5,z6]),(0,[z310,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z184,z3,z284,z5,z6])],[(0,[z152,z0,z127,z3,z4,z5,z6]),(0,[z139,z1,z3,z4,z5,z226,z6]),(0,[z0,z1,z3,z100,z4,z5,z8])],[(0,[z0,z311,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z312,z5,z6]),(0,[z61,z0,z1,z3,z313,z5,z6]),(0,[z0,z1,z17,z184,z3,z5,z6]),(1,[z0,z1,z3,z4,z314,z6])],[(0,[z94,z0,z1,z3,z4,z95,z6]),(0,[z0,z1,z114,z3,z4,z5,z8]),(0,[z315,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z184,z21,z3,z5,z6])],[(0,[z0,z1,z3,z316,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z141,z6]),(0,[z0,z1,z3,z4,z5,z6,z317]),(0,[z0,z1,z3,z4,z5,z199,z6]),(0,[z0,z168,z1,z3,z4,z5,z18]),(0,[z154,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z137,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z18,z18])]],
   [[(1,[z0,z107,z3,z4,z108,z6]),(0,[z0,z1,z318,z3,z4,z5,z6]),(1,[z0,z1,z17,z5,z105,z6]),(0,[z0,z1,z184,z114,z3,z5,z6]),(0,[z0,z1,z120,z4,z5,z188,z6]),(0,[z0,z1,z319,z3,z4,z5,z6])],[(0,[z63,z0,z1,z3,z308,z5,z6]),(1,[z0,z1,z184,z21,z3,z6])],[(0,[z0,z1,z3,z4,z5,z116,z6]),(0,[z0,z1,z3,z4,z5,z320,z6])],[(0,[z162,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z321,z6]),(1,[z0,z1,z322,z4,z5,z6]),(0,[z0,z1,z3,z4,z323,z279,z6])],[(0,[z0,z1,z267,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z324,z5,z6]),(1,[z0,z325,z3,z4,z5,z6]),(1,[z0,z1,z3,z225,z5,z6]),(0,[z0,z1,z326,z3,z4,z5,z6]),(0,[z0,z1,z3,z100,z5,z98,z6]),(0,[z0,z1,z3,z4,z5,z6,z327]),(0,[z328,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z146,z3,z137,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z329]),(0,[z0,z1,z3,z4,z5,z330,z6]),(1,[z189,z0,z1,z3,z4,z8])],[(0,[z331,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z55,z6]),(1,[z0,z277,z3,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z5,z8]),(0,[z85,z0,z1,z3,z4,z332,z6])],[(0,[z0,z1,z114,z3,z5,z98,z6]),(0,[z0,z1,z333,z3,z4,z5,z6]),(0,[z0,z1,z3,z137,z4,z6,z8]),(0,[z0,z1,z334,z3,z4,z5,z6])],[(0,[z10,z0,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z335,z8])]],
   [[(0,[z0,z1,z3,z4,z336,z5,z6]),(1,[z115,z1,z80,z4,z5,z6]),(0,[z337,z0,z1,z3,z4,z5,z6]),(1,[z61,z0,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z338,z6]),(0,[z0,z1,z3,z4,z5,z110,z8])],[(0,[z0,z1,z62,z4,z5,z6,z121]),(0,[z0,z1,z3,z4,z5,z42,z6])],[(0,[z0,z1,z3,z4,z97,z5,z18]),(0,[z339,z0,z1,z3,z4,z5,z6])],[(0,[z152,z127,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z268,z4,z5,z6]),(0,[z0,z1,z340,z3,z4,z5,z6]),(1,[z0,z1,z3,z24,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z341]),(0,[z0,z1,z3,z4,z5,z6,z342]),(0,[z0,z1,z3,z144,z4,z5,z6])],[(0,[z112,z0,z1,z3,z97,z5,z6]),(0,[z0,z1,z3,z4,z343,z5,z6]),(0,[z139,z0,z1,z3,z183,z4,z5]),(0,[z0,z168,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z136,z100,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z344,z4,z5,z6]),(0,[z0,z1,z3,z137,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z18,z8]),(1,[z0,z1,z3,z4,z173,z18])],[(0,[z0,z1,z36,z169,z4,z5,z6])],[(0,[z1,z11,z3,z62,z4,z5,z6]),(0,[z152,z1,z3,z62,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z345,z6]),(0,[z0,z1,z3,z137,z221,z5,z6]),(0,[z346,z0,z1,z3,z4,z5,z6]),(0,[z347,z0,z1,z3,z4,z5,z18])],[(0,[z0,z1,z3,z4,z5,z6,z348]),(0,[z61,z0,z1,z3,z4,z14,z6]),(0,[z0,z1,z3,z4,z5,z6,z349]),(0,[z350,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z323,z6]),(0,[z205,z0,z1,z3,z4,z5,z188]),(0,[z0,z1,z3,z4,z5,z188,z6]),(0,[z0,z1,z3,z351,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z5,z18])]],
   [[(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z5,z226]),(0,[z0,z1,z169,z4,z5,z43,z6]),(0,[z0,z1,z17,z4,z5,z105,z6]),(0,[z353,z0,z1,z3,z4,z5,z6]),(0,[z206,z0,z1,z3,z4,z5,z18])],[(0,[z0,z1,z3,z354,z4,z5,z6]),(0,[z355,z0,z1,z3,z4,z5,z6]),(0,[z33,z0,z1,z3,z4,z108,z6]),(0,[z0,z1,z3,z4,z5,z356,z6]),(0,[z0,z1,z3,z4,z5,z6,z161]),(0,[z0,z1,z3,z4,z5,z25,z6])],[(0,[z0,z1,z357,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z358,z6]),(0,[z0,z359,z1,z3,z4,z5,z6])],[(1,[z162,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z360,z4,z5,z6]),(0,[z0,z1,z3,z361,z4,z5,z6]),(1,[z0,z1,z3,z4,z128,z5]),(0,[z0,z1,z3,z4,z362,z5,z6]),(0,[z0,z3,z4,z108,z5,z42,z6]),(0,[z0,z1,z3,z4,z108,z5,z18]),(0,[z0,z1,z3,z4,z5,z105,z18]),(0,[z0,z1,z36,z136,z4,z5,z6]),(1,[z0,z1,z3,z4,z18,z8])],[(0,[z0,z1,z363,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z364,z6]),(0,[z139,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z43,z6]),(0,[z0,z1,z365,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z314,z5,z6]),(0,[z0,z1,z184,z3,z4,z5,z18])],[(0,[z366,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z367,z5,z6]),(0,[z0,z1,z3,z4,z5,z131,z8]),(0,[z0,z1,z3,z4,z5,z368,z6])],[(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z1,z80,z3,z62,z4,z5,z6]),(0,[z61,z0,z1,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z370,z6]),(0,[z0,z1,z3,z4,z5,z6,z371])],[(0,[z0,z1,z3,z62,z4,z5,z18]),(0,[z0,z1,z3,z4,z97,z5,z8]),(0,[z29,z94,z1,z3,z4,z5,z6]),(1,[z0,z1,z372,z4,z5,z6]),(0,[z61,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z373,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z374]),(0,[z375,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z115,z0,z286,z3,z4,z5,z6]),(0,[z0,z1,z3,z376,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z377,z6]),(0,[z0,z1,z3,z4,z5,z6,z378])],[(0,[z29,z0,z325,z3,z4,z5,z6]),(0,[z29,z0,z1,z3,z225,z5,z6]),(0,[z0,z1,z3,z379,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z380]),(0,[z0,z1,z381,z3,z4,z5,z6])],[(0,[z33,z0,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z382,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z383]),(0,[z0,z1,z384,z3,z4,z5,z6])],[(0,[z0,z1,z3,z372,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z349]),(0,[z0,z1,z3,z385,z4,z5,z6]),(0,[z0,z1,z3,z386,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z5,z8]),(0,[z189,z0,z1,z3,z4,z6,z8])],[(0,[z0,z1,z387,z3,z4,z5,z6]),(0,[z0,z1,z3,z137,z4,z5,z388]),(0,[z206,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z389,z3,z4,z5,z6])],[(0,[z10,z152,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z130,z5,z98,z6]),(0,[z0,z1,z3,z4,z390,z5,z6]),(0,[z0,z1,z3,z4,z391,z5,z6]),(0,[z0,z1,z3,z392,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z393])],[(0,[z0,z1,z3,z4,z5,z191,z8])]],
   [[(0,[z112,z0,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z183,z97,z5,z6]),(0,[z394,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z395,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z396,z6]),(0,[z0,z1,z3,z4,z108,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z397]),(0,[z0,z1,z3,z4,z5,z105,z8]),(0,[z0,z1,z3,z4,z5,z8,z398])],[(0,[z0,z399,z1,z3,z4,z5,z6]),(0,[z400,z0,z1,z3,z4,z5,z6]),(0,[z401,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z184,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z8,z402])],[(0,[z403,z0,z1,z3,z4,z5,z6]),(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z405,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z406,z6]),(0,[z0,z1,z184,z3,z157,z5,z6]),(0,[z407,z0,z1,z3,z4,z5,z6]),(0,[z408,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z409,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z332,z6])],[(0,[z410,z0,z1,z3,z4,z5,z6]),(0,[z0,z101,z11,z3,z4,z5,z6]),(0,[z0,z1,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z411,z4,z5,z6])],[(0,[z0,z1,z3,z62,z4,z5,z8]),(1,[z29,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z298,z6]),(0,[z0,z1,z3,z4,z5,z6,z412]),(0,[z413,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z414,z6])],[(0,[z0,z1,z3,z4,z5,z415,z6]),(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z0,z1,z17,z3,z136,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z417]),(0,[z0,z1,z3,z183,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z18])],[(0,[z0,z168,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z418,z4,z5,z6]),(0,[z0,z1,z419,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z43,z6]),(0,[z0,z1,z3,z4,z5,z420,z6]),(0,[z421,z0,z1,z3,z4,z5,z6])],[(0,[z115,z0,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z422,z6]),(1,[z0,z1,z3,z4,z5,z380]),(0,[z0,z1,z3,z4,z5,z6,z423]),(0,[z33,z0,z1,z3,z223,z5,z6])]],
   [[(0,[z63,z0,z1,z3,z183,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z424]),(0,[z0,z1,z36,z37,z4,z5,z6]),(0,[z0,z1,z36,z3,z4,z5,z18]),(0,[z0,z1,z3,z183,z5,z191,z6]),(0,[z0,z1,z3,z4,z5,z6,z425])],[(0,[z0,z1,z62,z4,z5,z105,z6]),(0,[z0,z1,z21,z3,z4,z95,z6]),(0,[z0,z1,z114,z3,z136,z5,z6]),(0,[z0,z1,z36,z3,z4,z43,z6]),(0,[z0,z1,z3,z4,z5,z88,z8])],[(0,[z61,z0,z127,z3,z4,z5,z6]),(0,[z0,z1,z426,z3,z4,z5,z6]),(0,[z0,z170,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z284,z4,z5,z427]),(0,[z0,z1,z3,z284,z4,z98,z6])],[(0,[z152,z0,z1,z122,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z5,z121]),(1,[z0,z1,z3,z4,z5,z427]),(0,[z0,z1,z3,z284,z4,z5,z18])],[(0,[z0,z1,z3,z4,z428,z5,z6]),(1,[z0,z1,z3,z4,z5,z116]),(0,[z0,z1,z429,z3,z4,z5,z6]),(0,[z430,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z431,z4,z5,z6]),(0,[z0,z1,z3,z432,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z6,z8])],[(0,[z433,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z434,z6]),(0,[z0,z1,z21,z3,z4,z6,z8])],[(0,[z0,z1,z435,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z47]),(0,[z436,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z437,z6]),(0,[z438,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z439,z6]),(0,[z0,z1,z3,z4,z440,z5,z6])]],
   [[(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z441,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z442,z4,z5,z6]),(0,[z0,z1,z3,z4,z443,z5,z6]),(0,[z0,z1,z3,z4,z5,z47,z8]),(1,[z0,z1,z114,z136,z5,z6]),(0,[z0,z444,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z81,z18])],[(0,[z0,z1,z445,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z446,z5,z6]),(0,[z0,z1,z140,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z64,z6])],[(0,[z0,z447,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z8])],[(0,[z0,z1,z3,z4,z448,z5,z6]),(0,[z449,z0,z1,z3,z4,z5,z6]),(0,[z450,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z38,z6]),(0,[z0,z451,z1,z3,z4,z5,z6])],[(0,[z452,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z453,z4,z5,z6]),(0,[z132,z0,z1,z3,z100,z5,z6]),(0,[z0,z1,z3,z454,z4,z5,z6])],[(0,[z10,z1,z11,z3,z4,z5,z6]),(0,[z455,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z268,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z456]),(0,[z94,z0,z1,z3,z4,z55,z6]),(0,[z33,z0,z1,z3,z4,z5,z298]),(0,[z0,z1,z457,z3,z4,z5,z6]),(0,[z0,z1,z36,z3,z4,z5,z8])],[(0,[z458,z0,z1,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z279]),(0,[z0,z1,z3,z4,z5,z459,z6]),(0,[z0,z1,z460,z3,z4,z5,z6])],[(0,[z461,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z462,z3,z4,z5,z6]),(0,[z0,z1,z463,z3,z4,z5,z6])]],
   [[(0,[z464,z0,z1,z3,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z180,z6]),(0,[z0,z1,z3,z284,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z335])],[(0,[z0,z1,z3,z465,z4,z5,z6]),(0,[z61,z0,z1,z3,z220,z5,z6]),(0,[z0,z1,z466,z4,z157,z5,z6]),(0,[z33,z0,z1,z3,z309,z5,z6]),(1,[z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z467,z4,z5,z6]),(1,[z0,z1,z3,z4,z312,z6]),(0,[z0,z1,z37,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z468,z6])],[(0,[z61,z0,z3,z117,z4,z5,z6]),(0,[z0,z1,z3,z469,z4,z5,z6]),(0,[z0,z1,z470,z3,z4,z5,z6]),(0,[z471,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z221,z5,z6])],[(0,[z0,z1,z3,z4,z472,z5,z6]),(0,[z473,z0,z1,z3,z4,z5,z6]),(0,[z162,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z80,z3,z4,z5,z18]),(0,[z29,z0,z1,z3,z4,z5,z380]),(0,[z0,z1,z3,z4,z5,z6,z474]),(0,[z0,z1,z475,z3,z4,z5,z6])],[(0,[z10,z0,z127,z3,z4,z5,z6]),(0,[z0,z1,z3,z476,z4,z5,z6]),(0,[z0,z477,z1,z3,z4,z5,z6]),(0,[z478,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z17,z114,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z388]),(0,[z0,z1,z3,z4,z5,z330,z18])],[(0,[z0,z1,z3,z4,z479,z5,z6]),(0,[z115,z152,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z289,z6]),(0,[z29,z0,z1,z3,z343,z5,z6]),(0,[z0,z1,z3,z4,z5,z279,z121]),(0,[z0,z1,z3,z4,z5,z6,z393])],[(0,[z0,z1,z80,z4,z5,z6,z121]),(0,[z0,z1,z249,z3,z4,z5,z6]),(0,[z0,z1,z3,z480,z4,z5,z6]),(0,[z481,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z108,z5,z482]),(0,[z0,z1,z483,z3,z4,z5,z6])]],
   [[(0,[z484,z0,z1,z3,z4,z5,z6]),(1,[z112,z1,z3,z97,z5,z6]),(0,[z485,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z284,z5,z98,z6])],[(0,[z115,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z95,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z486,z3,z4,z5,z6]),(0,[z33,z0,z1,z322,z4,z5,z6]),(0,[z0,z1,z21,z3,z284,z4,z6]),(0,[z0,z1,z3,z151,z4,z5,z18])],[(0,[z63,z0,z277,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z226,z88]),(0,[z0,z1,z3,z4,z5,z487,z6]),(0,[z0,z1,z3,z4,z5,z42,z18]),(0,[z0,z107,z1,z3,z4,z6,z8]),(0,[z0,z1,z3,z4,z323,z5,z6]),(0,[z0,z1,z3,z4,z5,z488,z6])],[(0,[z0,z1,z3,z489,z4,z5,z6]),(0,[z0,z1,z490,z3,z4,z5,z6])],[(0,[z29,z0,z1,z3,z4,z95,z6]),(0,[z0,z1,z3,z117,z4,z5,z18]),(0,[z132,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z462,z21,z4,z5,z6])],[(0,[z0,z1,z3,z491,z4,z5,z6]),(0,[z0,z3,z100,z4,z157,z5,z6]),(0,[z0,z1,z3,z4,z5,z176,z6]),(0,[z0,z1,z3,z4,z5,z165,z18])],[(0,[z492,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z493,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z494,z6]),(0,[z0,z1,z3,z495,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z496])]],
   [[(0,[z0,z1,z497,z3,z4,z5,z6]),(0,[z0,z168,z1,z80,z4,z5,z6]),(0,[z112,z0,z1,z249,z4,z5,z6]),(0,[z63,z0,z1,z3,z24,z5,z6]),(0,[z0,z1,z498,z3,z4,z5,z6]),(0,[z0,z1,z322,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z499,z6]),(0,[z0,z500,z1,z3,z4,z5,z6])],[(0,[z162,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z501,z6]),(0,[z115,z0,z1,z80,z4,z5,z6]),(0,[z0,z1,z80,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z502,z6]),(0,[z0,z1,z3,z4,z503,z5,z6]),(0,[z0,z1,z3,z183,z4,z5,z191])],[(0,[z0,z99,z11,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z5,z18]),(0,[z0,z171,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z388]),(0,[z0,z1,z3,z137,z4,z5,z459])],[(0,[z504,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z482]),(1,[z0,z1,z3,z284,z98,z6])],[(0,[z0,z1,z3,z4,z5,z505,z6]),(0,[z0,z1,z3,z506,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z507,z6]),(0,[z0,z1,z334,z3,z4,z5,z8]),(0,[z0,z1,z508,z3,z4,z5,z6])],[(0,[z0,z1,z509,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z510,z6])],[(0,[z0,z1,z511,z3,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z8]),(0,[z33,z0,z1,z3,z4,z42,z6]),(1,[z0,z1,z3,z137,z4,z8]),(0,[z0,z1,z3,z4,z5,z425,z8]),(0,[z209,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z512]),(0,[z0,z1,z3,z4,z5,z42,z8]),(0,[z0,z1,z3,z4,z513,z5,z6]),(0,[z0,z1,z3,z4,z5,z514,z6]),(0,[z0,z101,z3,z4,z5,z279,z6]),(0,[z0,z1,z37,z3,z137,z4,z6]),(0,[z0,z1,z3,z4,z173,z5,z6]),(0,[z0,z1,z3,z4,z5,z216,z8]),(0,[z0,z1,z3,z4,z5,z515,z6])]],
   [[(0,[z94,z1,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z516,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(1,[z280,z0,z1,z3,z4,z5]),(0,[z0,z1,z136,z4,z5,z43,z6])],[(1,[z0,z1,z3,z4,z5,z158]),(0,[z139,z0,z1,z3,z4,z5,z131]),(0,[z0,z1,z3,z117,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z517,z6]),(0,[z0,z1,z3,z4,z5,z6,z518]),(0,[z0,z1,z3,z4,z5,z6,z383])],[(0,[z280,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z519,z6]),(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z521,z4,z5,z6])],[(0,[z162,z115,z1,z3,z4,z5,z6]),(0,[z522,z0,z1,z3,z4,z5,z6]),(0,[z48,z1,z3,z130,z4,z5,z6]),(0,[z0,z1,z22,z3,z4,z5,z6]),(0,[z94,z1,z3,z4,z95,z5,z6]),(0,[z0,z1,z3,z4,z95,z5,z84]),(0,[z0,z1,z3,z4,z523,z5,z6]),(0,[z0,z168,z1,z117,z4,z5,z6]),(0,[z0,z1,z3,z524,z4,z5,z6])],[(0,[z63,z0,z1,z372,z4,z5,z6]),(1,[z0,z1,z3,z4,z69,z6]),(0,[z0,z525,z1,z3,z4,z5,z6]),(0,[z0,z99,z1,z3,z100,z5,z6]),(0,[z526,z0,z1,z3,z4,z5,z6])],[(0,[z115,z1,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z226,z6]),(1,[z527,z1,z3,z4,z5,z6]),(0,[z0,z169,z3,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z528]),(0,[z0,z1,z3,z4,z5,z6,z529]),(0,[z0,z530,z1,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z531,z6])],[(0,[z0,z1,z3,z4,z157,z5,z18]),(0,[z0,z1,z137,z4,z5,z43,z6]),(0,[z0,z1,z3,z4,z5,z532,z6])],[(0,[z112,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z466,z3,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z121])]],
   [[(0,[z112,z0,z1,z3,z4,z312,z6]),(1,[z0,z1,z3,z4,z5,z482]),(0,[z0,z533,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z427,z6]),(0,[z534,z0,z1,z3,z4,z5,z6])],[(0,[z0,z101,z127,z3,z4,z5,z6]),(0,[z0,z325,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z535,z4,z5,z6]),(0,[z536,z0,z1,z3,z4,z5,z6])],[(1,[z154,z0,z3,z4,z5,z47]),(0,[z0,z1,z365,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z537,z6]),(0,[z0,z1,z114,z62,z4,z5,z6]),(1,[z132,z0,z3,z157,z5,z6]),(0,[z0,z1,z3,z538,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z539,z6]),(0,[z0,z1,z190,z3,z4,z5,z8]),(0,[z211,z0,z1,z3,z4,z5,z6])],[(0,[z152,z0,z1,z3,z4,z5,z18]),(1,[z0,z267,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z289,z6]),(1,[z0,z1,z540,z4,z5,z6]),(1,[z33,z0,z3,z4,z42,z6]),(0,[z33,z0,z3,z4,z5,z42,z6]),(0,[z0,z1,z541,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z6,z528])],[(0,[z0,z1,z542,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z543]),(0,[z0,z1,z3,z4,z5,z544,z6]),(0,[z205,z0,z1,z120,z4,z5,z6]),(0,[z0,z1,z3,z284,z4,z5,z383]),(0,[z0,z1,z3,z4,z5,z98,z18])],[(0,[z0,z1,z3,z545,z4,z5,z6]),(0,[z0,z1,z169,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z546,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z547]),(0,[z0,z1,z3,z183,z4,z5,z18])],[(0,[z0,z1,z3,z4,z5,z55,z6]),(0,[z548,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z136,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z43,z18])]],
   [[(0,[z0,z1,z21,z3,z4,z55,z6]),(0,[z549,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z191,z6,z88]),(0,[z210,z0,z1,z3,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z550,z6]),(0,[z0,z1,z3,z4,z551,z5,z6]),(1,[z0,z1,z36,z137,z4,z6]),(0,[z552,z0,z1,z3,z4,z5,z6])],[(0,[z0,z107,z11,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z183,z5,z6]),(0,[z0,z1,z3,z4,z5,z553,z6])],[(0,[z0,z1,z3,z4,z5,z554,z6]),(1,[z0,z240,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z157,z5,z8]),(0,[z0,z1,z3,z4,z5,z555,z6]),(0,[z0,z1,z3,z137,z4,z173,z6]),(0,[z0,z1,z556,z3,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z557,z6]),(0,[z0,z1,z558,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z55,z98,z6]),(1,[z139,z1,z3,z4,z5,z226]),(1,[z0,z1,z3,z4,z5,z38]),(0,[z0,z1,z120,z3,z4,z5,z18]),(0,[z256,z0,z1,z3,z4,z5,z18])],[(0,[z559,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z560,z4,z5,z6]),(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z562,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z37,z4,z43,z6])],[(0,[z0,z1,z3,z4,z5,z563,z6]),(0,[z0,z1,z3,z4,z5,z564,z6])]],
   [[(0,[z0,z1,z3,z97,z5,z6,z88]),(0,[z565,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z37,z4,z5,z43,z6]),(0,[z0,z566,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z567,z6])],[(0,[z152,z0,z1,z3,z4,z5,z8]),(0,[z63,z0,z1,z3,z4,z5,z18]),(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z569,z5,z6])],[(0,[z33,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z6,z398]),(0,[z0,z1,z3,z4,z5,z279,z6]),(0,[z0,z1,z3,z4,z5,z6,z570]),(0,[z0,z1,z3,z4,z5,z98,z8])],[(1,[z63,z1,z3,z4,z5,z131]),(0,[z0,z1,z169,z3,z4,z5,z8]),(0,[z0,z1,z571,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z402]),(0,[z0,z1,z3,z4,z5,z531,z6]),(0,[z0,z1,z3,z183,z4,z5,z8])],[(0,[z0,z1,z3,z4,z5,z572,z6]),(1,[z0,z1,z3,z343,z5,z6]),(0,[z0,z1,z3,z157,z5,z105,z6]),(0,[z0,z1,z573,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z43,z8]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z18,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z564]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z5,z131]),(1,[z170,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z575]),(0,[z0,z1,z3,z576,z4,z5,z6]),(0,[z0,z1,z577,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z578,z5,z6]),(1,[z34,z1,z3,z4,z5,z6]),(0,[z579,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z120,z4,z5,z188])],[(0,[z0,z1,z3,z4,z580,z5,z6]),(0,[z581,z0,z1,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z5,z158]),(0,[z0,z1,z3,z4,z5,z582,z6]),(0,[z527,z0,z1,z3,z4,z5,z6]),(0,[z61,z0,z1,z169,z4,z5,z6]),(0,[z583,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z584,z3,z4,z5,z6])]],
   [[(0,[z0,z585,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z586,z6]),(0,[z61,z527,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z88]),(0,[z461,z0,z1,z3,z4,z5,z18]),(0,[z0,z266,z1,z3,z4,z5,z6])],[(0,[z587,z0,z1,z3,z4,z5,z6]),(0,[z48,z0,z1,z3,z97,z5,z6]),(0,[z33,z0,z1,z3,z4,z6,z8]),(0,[z0,z1,z17,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z98,z8]),(0,[z0,z1,z3,z4,z5,z18,z588])],[(0,[z1,z3,z4,z5,z226,z6,z131]),(0,[z0,z589,z1,z3,z4,z5,z6]),(0,[z0,z1,z120,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z590]),(1,[z0,z1,z3,z4,z531,z6])],[(0,[z0,z1,z591,z3,z4,z5,z6]),(0,[z592,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z100,z4,z5,z6]),(0,[z0,z1,z3,z157,z5,z98,z6]),(0,[z0,z1,z37,z3,z4,z5,z18])],[(0,[z0,z1,z3,z4,z5,z593,z6]),(0,[z594,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z595,z4,z5,z6])],[(0,[z152,z94,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z596]),(0,[z61,z0,z1,z136,z4,z5,z6]),(0,[z0,z1,z597,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z598,z6]),(0,[z0,z1,z114,z3,z4,z5,z6]),(0,[z0,z1,z17,z3,z5,z105,z6]),(0,[z0,z1,z184,z21,z3,z4,z6]),(0,[z0,z599,z1,z3,z4,z5,z6])],[(0,[z48,z0,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z191,z226])],[(0,[z0,z1,z3,z600,z4,z5,z6]),(0,[z0,z1,z3,z183,z130,z5,z6]),(1,[z0,z1,z3,z4,z5,z199]),(0,[z33,z0,z1,z3,z4,z5,z8]),(1,[z0,z1,z3,z4,z5,z459]),(0,[z0,z1,z3,z4,z5,z6,z121])]],
   [[(0,[z0,z1,z601,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z141,z6]),(0,[z0,z602,z1,z3,z4,z5,z6])],[(1,[z0,z558,z3,z4,z5,z6]),(0,[z0,z1,z603,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z95,z98,z6]),(0,[z0,z1,z3,z4,z5,z131,z88]),(0,[z0,z1,z604,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z605]),(0,[z189,z0,z1,z3,z4,z173,z6])],[(0,[z606,z0,z1,z3,z4,z5,z6]),(0,[z127,z1,z11,z3,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z349]),(0,[z0,z1,z3,z4,z5,z607,z6]),(1,[z0,z107,z1,z3,z4,z8]),(0,[z0,z1,z36,z137,z4,z5,z6])],[(0,[z29,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z608,z4,z5,z6]),(0,[z0,z1,z3,z4,z220,z5,z6]),(0,[z0,z1,z3,z4,z5,z47,z121]),(0,[z609,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z610]),(0,[z0,z1,z611,z3,z4,z5,z6])],[(0,[z612,z0,z1,z3,z4,z5,z6]),(0,[z0,z613,z1,z3,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z5,z6])],[(0,[z0,z1,z114,z80,z4,z5,z6]),(0,[z29,z0,z22,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z279,z6,z528]),(0,[z0,z1,z3,z147,z4,z5,z6])],[(0,[z614,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z615,z3,z4,z5,z6]),(0,[z0,z616,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z188])],[(0,[z0,z617,z1,z3,z4,z5,z6]),(0,[z94,z0,z1,z3,z4,z5,z6]),(0,[z0,z99,z3,z100,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z279]),(0,[z618,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z21,z164,z4,z5,z6]),(0,[z0,z1,z3,z4,z18,z6,z8]),(0,[z0,z1,z3,z4,z5,z18,z619])]],
   [[(0,[z0,z99,z127,z3,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z6]),(0,[z0,z1,z37,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z620]),(0,[z85,z0,z1,z3,z4,z5,z88])],[(0,[z0,z1,z11,z3,z4,z5,z6]),(0,[z621,z0,z1,z3,z4,z5,z6]),(1,[z94,z1,z3,z4,z95,z6]),(1,[z0,z1,z3,z308,z5,z6]),(0,[z0,z622,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z623])],[(0,[z624,z0,z1,z3,z4,z5,z6]),(0,[z0,z127,z107,z3,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z564]),(0,[z0,z1,z625,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z626])],[(0,[z0,z168,z1,z3,z4,z5,z6]),(0,[z132,z0,z3,z4,z157,z5,z6]),(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z628,z0,z1,z3,z4,z5,z6]),(1,[z0,z101,z3,z4,z5,z279]),(0,[z0,z1,z3,z137,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z629]),(0,[z0,z1,z3,z4,z5,z18,z6])],[(0,[z630,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z182])],[(0,[z631,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z95,z5,z55,z6]),(1,[z0,z1,z140,z4,z5,z6]),(0,[z0,z1,z21,z3,z4,z5,z138])],[(1,[z152,z127,z3,z4,z5,z6]),(0,[z632,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z633,z4,z5,z6]),(0,[z0,z1,z634,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z635,z6]),(0,[z0,z1,z3,z4,z43,z6,z8])],[(1,[z0,z286,z3,z4,z5,z6]),(0,[z0,z1,z636,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z637,z6]),(0,[z0,z1,z3,z4,z173,z98,z6])]],
   [[(0,[z0,z1,z184,z3,z100,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z638])],[(0,[z0,z1,z3,z639,z4,z5,z6]),(0,[z0,z640,z1,z3,z4,z5,z6]),(0,[z641,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z130,z5,z6,z88]),(0,[z0,z1,z30,z3,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z642,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z643,z5,z6]),(0,[z0,z1,z21,z3,z4,z173,z6])],[],[(0,[z0,z11,z169,z3,z4,z5,z6]),(0,[z0,z1,z120,z62,z4,z5,z6]),(0,[z112,z48,z1,z3,z4,z5,z6]),(0,[z0,z168,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z644,z6]),(0,[z0,z1,z3,z645,z4,z5,z6])],[(0,[z0,z1,z3,z130,z4,z5,z6]),(0,[z1,z3,z130,z4,z97,z5,z6]),(1,[z171,z1,z3,z4,z5,z6]),(0,[z646,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z97,z5,z6]),(0,[z85,z139,z0,z1,z3,z4,z5]),(0,[z0,z647,z1,z3,z4,z5,z6])],[(0,[z0,z1,z648,z3,z4,z5,z6]),(0,[z0,z1,z649,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z332,z5,z6])]],
   [[(0,[z0,z650,z1,z3,z4,z5,z6]),(0,[z139,z0,z1,z3,z4,z5,z18]),(0,[z0,z3,z4,z5,z279,z6,z47]),(0,[z0,z651,z1,z3,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z5,z18]),(1,[z0,z1,z462,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z88]),(0,[z0,z1,z3,z4,z652,z5,z6])],[(0,[z653,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z113]),(1,[z0,z1,z3,z4,z5,z182]),(0,[z0,z1,z3,z4,z5,z6,z588])],[(0,[z0,z1,z36,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z654,z5,z6]),(0,[z655,z0,z1,z3,z4,z5,z6]),(0,[z656,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z657,z3,z4,z5,z6]),(0,[z0,z1,z658,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z248]),(0,[z347,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z659,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z660,z6]),(0,[z0,z1,z3,z4,z661,z5,z6]),(0,[z662,z0,z1,z3,z4,z5,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z115,z1,z80,z3,z4,z5,z6]),(0,[z0,z217,z1,z3,z4,z5,z6])],[(0,[z664,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z665,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z666,z6]),(0,[z0,z1,z3,z4,z5,z6,z667]),(0,[z0,z668,z1,z3,z4,z5,z6]),(0,[z0,z1,z669,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z191,z6])],[(0,[z112,z0,z558,z3,z4,z5,z6]),(1,[z0,z1,z30,z4,z5,z6]),(0,[z0,z670,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z5,z6]),(0,[z0,z1,z3,z313,z4,z5,z6]),(0,[z61,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z1,z3,z671,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z105,z6])]],
   [[(0,[z0,z127,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z55,z18]),(0,[z0,z1,z3,z4,z69,z5,z6]),(0,[z0,z1,z672,z3,z4,z5,z6]),(0,[z0,z1,z3,z136,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z188,z8]),(0,[z0,z1,z184,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z673])],[(0,[z0,z1,z3,z4,z5,z6,z674]),(0,[z0,z1,z3,z4,z5,z6,z675]),(1,[z33,z0,z1,z3,z4,z8]),(0,[z189,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z389,z3,z4,z5,z18])],[(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z677,z0,z1,z3,z4,z5,z6]),(0,[z33,z0,z1,z540,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z309,z5,z6])],[(1,[z0,z1,z174,z4,z5,z6]),(0,[z0,z127,z169,z3,z4,z5,z6]),(0,[z0,z1,z3,z678,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z0,z1,z3,z4,z680,z5,z6]),(0,[z0,z681,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z682,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z18]),(0,[z683,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z68,z4,z5,z6]),(0,[z139,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z6,z684]),(0,[z0,z1,z3,z4,z5,z6,z685]),(0,[z205,z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z686,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z113]),(0,[z213,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z313,z5,z6]),(1,[z0,z1,z466,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z108,z6]),(0,[z0,z107,z1,z3,z4,z173,z6]),(0,[z0,z101,z1,z3,z4,z5,z47]),(0,[z0,z1,z17,z4,z5,z43,z6]),(1,[z0,z1,z3,z4,z5,z248]),(0,[z0,z1,z3,z687,z4,z5,z6]),(0,[z688,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z619])]],
   [[(1,[z0,z123,z3,z4,z5,z6]),(0,[z132,z0,z99,z3,z4,z5,z6]),(0,[z0,z1,z689,z3,z4,z5,z6]),(0,[z690,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z128,z97,z5]),(0,[z0,z1,z691,z3,z4,z5,z6])],[(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z80,z4,z5,z105,z6]),(0,[z0,z1,z3,z4,z5,z6,z693]),(0,[z0,z1,z3,z4,z5,z18,z47]),(0,[z694,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z222,z6]),(1,[z205,z0,z1,z4,z5,z121])],[(0,[z0,z240,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z63,z1,z3,z4,z5,z6,z131]),(0,[z0,z1,z695,z3,z4,z5,z6]),(0,[z0,z1,z3,z696,z4,z5,z6]),(1,[z0,z1,z3,z183,z5,z191])],[(0,[z0,z1,z3,z697,z4,z5,z6]),(0,[z0,z1,z3,z540,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z314,z6])],[(0,[z0,z1,z3,z4,z5,z698,z6]),(0,[z699,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z700,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z55,z8]),(0,[z0,z1,z701,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z702,z6]),(0,[z0,z1,z3,z136,z4,z5,z8])],[(0,[z162,z0,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z18,z226]),(0,[z0,z1,z3,z136,z157,z5,z6]),(0,[z0,z1,z3,z137,z4,z108,z6]),(0,[z0,z1,z3,z4,z5,z703,z6]),(0,[z0,z704,z1,z3,z4,z5,z6])],[(0,[z0,z99,z1,z3,z4,z5,z6]),(0,[z705,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z706,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z4,z5,z707]),(0,[z0,z1,z3,z308,z5,z6]),(0,[z94,z1,z3,z4,z95,z6]),(0,[z0,z1,z117,z4,z14,z6]),(0,[z0,z1,z3,z221,z5,z8]),(0,[z195,z0,z1,z3,z4,z8]),(0,[z0,z1,z708,z4,z5,z18])],[(0,[z0,z1,z3,z4,z709,z6]),(0,[z10,z710,z3,z4,z5,z6]),(0,[z0,z1,z3,z711,z5,z6])],[(0,[z0,z1,z3,z4,z712,z6]),(0,[z63,z1,z3,z24,z5,z131]),(0,[z0,z1,z3,z4,z5,z713]),(0,[z171,z1,z3,z223,z5,z6]),(0,[z0,z1,z3,z4,z5,z714]),(0,[z0,z1,z3,z4,z5,z715]),(0,[z205,z0,z1,z4,z180,z121]),(0,[z0,z1,z3,z284,z98,z427])],[(0,[z0,z1,z3,z4,z5,z716]),(0,[z0,z1,z3,z4,z5,z717]),(0,[z0,z1,z3,z4,z289,z8]),(0,[z112,z280,z1,z3,z97,z5]),(0,[z0,z1,z3,z540,z4,z8]),(0,[z0,z1,z3,z718,z5,z6]),(0,[z0,z1,z3,z284,z98,z18])],[(0,[z612,z0,z3,z4,z42,z6]),(0,[z628,z127,z3,z4,z5,z6]),(0,[z0,z1,z3,z183,z4,z141]),(0,[z0,z1,z3,z4,z188,z528]),(0,[z0,z1,z164,z4,z5,z6])],[(0,[z152,z127,z3,z4,z5,z6]),(0,[z112,z1,z3,z97,z5,z8]),(0,[z0,z277,z3,z4,z64,z6]),(0,[z0,z1,z117,z4,z43,z8]),(0,[z0,z1,z395,z3,z4,z8]),(0,[z0,z1,z36,z4,z680,z6]),(0,[z0,z1,z3,z4,z314,z8]),(0,[z0,z1,z164,z4,z5,z25])],[(0,[z0,z286,z3,z4,z5,z6]),(1,[z710,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z719]),(0,[z413,z1,z3,z97,z5,z6]),(0,[z0,z1,z466,z220,z5,z6]),(0,[z0,z1,z3,z223,z5,z182]),(0,[z154,z0,z3,z4,z5,z720]),(0,[z0,z1,z462,z21,z4,z8])],[(0,[z0,z721,z3,z4,z5,z6]),(0,[z0,z1,z249,z4,z5,z158]),(0,[z0,z722,z3,z4,z5,z6]),(0,[z156,z1,z3,z4,z95,z6]),(0,[z723,z1,z3,z4,z5,z6]),(0,[z724,z1,z3,z4,z5,z6]),(0,[z725,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z726,z6]),(0,[z0,z1,z3,z4,z727,z6])]],
   [[(0,[z0,z1,z3,z4,z547,z8])],[(0,[z0,z127,z3,z4,z14,z6]),(0,[z0,z1,z3,z4,z5,z728]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z0,z1,z146,z3,z5,z459])],[(0,[z112,z1,z3,z97,z289,z6]),(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z731,z6]),(0,[z0,z1,z732,z4,z5,z6]),(0,[z461,z0,z1,z3,z4,z528]),(0,[z0,z1,z3,z4,z323,z18]),(0,[z0,z1,z3,z4,z5,z138]),(0,[z0,z1,z3,z682,z4,z8])],[(0,[z0,z1,z3,z24,z64,z6]),(0,[z61,z0,z117,z4,z5,z199]),(0,[z0,z1,z3,z4,z180,z188])],[(0,[z473,z1,z62,z4,z5,z6]),(0,[z171,z1,z3,z4,z5,z6]),(0,[z653,z0,z3,z4,z5,z47]),(0,[z0,z325,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z69,z18]),(0,[z0,z1,z3,z4,z5,z733]),(0,[z0,z1,z17,z5,z19,z6])],[(0,[z609,z1,z80,z4,z5,z6]),(0,[z210,z1,z3,z4,z55,z8]),(0,[z527,z1,z3,z4,z5,z18]),(0,[z0,z1,z318,z4,z5,z188]),(0,[z0,z1,z3,z4,z5,z734])],[(0,[z0,z1,z3,z735,z5,z6]),(0,[z63,z1,z372,z4,z5,z131])],[(0,[z0,z736,z3,z4,z5,z6]),(0,[z0,z1,z737,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z479,z8]),(0,[z0,z99,z3,z506,z5,z6]),(0,[z171,z1,z3,z4,z5,z298]),(0,[z0,z171,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z180,z6]),(0,[z0,z1,z3,z284,z98,z8]),(0,[z0,z1,z3,z4,z173,z25]),(0,[z0,z738,z3,z4,z5,z6])],[(0,[z0,z739,z3,z4,z5,z6]),(0,[z0,z1,z249,z4,z5,z113]),(0,[z112,z1,z3,z740,z5,z6]),(0,[z0,z1,z3,z4,z116,z8]),(0,[z0,z1,z3,z741,z5,z6]),(0,[z0,z1,z3,z4,z320,z8]),(0,[z0,z742,z3,z4,z5,z6])],[(0,[z0,z743,z3,z4,z5,z6]),(0,[z94,z1,z3,z4,z95,z84])],[(0,[z0,z1,z3,z4,z744,z8]),(0,[z132,z0,z3,z157,z5,z18]),(0,[z0,z1,z745,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z298]),(0,[z0,z3,z4,z746,z42,z6])],[(0,[z0,z267,z3,z4,z5,z18]),(0,[z0,z1,z3,z747,z5,z6]),(0,[z748,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z749]),(0,[z171,z1,z3,z309,z5,z6]),(0,[z0,z1,z540,z4,z5,z18]),(0,[z0,z1,z540,z223,z5,z6]),(0,[z33,z0,z3,z4,z42,z18])],[(0,[z0,z1,z3,z4,z5,z750]),(0,[z0,z1,z3,z4,z5,z751]),(0,[z170,z1,z3,z4,z5,z349]),(0,[z0,z1,z3,z4,z5,z752]),(0,[z0,z1,z753,z4,z5,z6]),(0,[z754,z1,z3,z4,z5,z6]),(0,[z0,z101,z1,z3,z4,z528]),(0,[z0,z1,z114,z3,z98,z8]),(0,[z0,z1,z3,z4,z5,z755]),(0,[z0,z1,z3,z4,z531,z191])],[(0,[z0,z1,z3,z756,z5,z6]),(0,[z0,z277,z140,z4,z5,z6]),(0,[z0,z1,z3,z4,z757,z6]),(0,[z0,z1,z233,z137,z4,z6]),(0,[z0,z1,z3,z4,z531,z330])],[(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z1,z268,z4,z5,z113]),(0,[z0,z1,z3,z759,z5,z6]),(0,[z0,z1,z3,z309,z173,z6]),(0,[z0,z1,z3,z4,z643,z8]),(0,[z0,z1,z3,z4,z323,z8]),(0,[z0,z760,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z505,z8]),(0,[z0,z1,z3,z97,z5,z113]),(0,[z0,z1,z3,z4,z507,z8]),(0,[z0,z761,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z762,z6]),(0,[z0,z1,z3,z309,z5,z182]),(0,[z0,z107,z1,z3,z4,z482]),(0,[z0,z1,z3,z763,z5,z8])],[(0,[z0,z1,z3,z4,z55,z380]),(0,[z0,z1,z3,z4,z69,z8]),(0,[z0,z1,z36,z137,z4,z18])],[(0,[z0,z764,z3,z4,z5,z6]),(0,[z527,z1,z3,z4,z5,z8])],[(0,[z0,z1,z174,z4,z5,z6]),(0,[z0,z765,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z289,z158]),(0,[z0,z3,z4,z766,z5,z6]),(0,[z0,z1,z3,z4,z514,z8])],[(0,[z1,z710,z3,z4,z5,z6]),(0,[z94,z1,z3,z4,z479,z6]),(0,[z0,z1,z68,z4,z5,z6]),(0,[z29,z1,z3,z343,z55,z6]),(0,[z0,z1,z140,z24,z5,z6])],[(0,[z0,z11,z122,z4,z5,z6]),(0,[z112,z1,z3,z97,z5,z158]),(0,[z29,z1,z3,z4,z55,z564]),(0,[z0,z1,z3,z5,z6,z767]),(0,[z0,z1,z3,z4,z332,z18])],[(0,[z0,z1,z3,z4,z5,z768]),(0,[z0,z1,z769,z4,z5,z6]),(0,[z0,z1,z37,z4,z43,z18])],[(0,[z0,z123,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z770]),(0,[z0,z1,z80,z220,z5,z6]),(0,[z0,z1,z3,z343,z5,z380]),(0,[z0,z1,z3,z103,z4,z8])]],
   [[(0,[z0,z1,z771,z3,z4,z6]),(0,[z772,z0,z1,z3,z4,z5]),(0,[z0,z1,z17,z220,z5,z6]),(0,[z132,z0,z3,z157,z5,z8]),(0,[z0,z1,z322,z4,z5,z182]),(0,[z0,z1,z136,z5,z773,z6]),(0,[z0,z1,z3,z4,z25,z8])],[(0,[z0,z1,z3,z4,z774,z6]),(0,[z0,z267,z3,z4,z5,z8]),(0,[z0,z775,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z776,z6]),(0,[z139,z1,z3,z4,z5,z777]),(0,[z0,z1,z3,z220,z5,z199]),(0,[z0,z1,z540,z4,z5,z8]),(0,[z33,z0,z3,z4,z42,z8]),(0,[z0,z3,z4,z5,z6,z778])],[(0,[z0,z1,z779,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z780]),(0,[z1,z3,z781,z4,z5,z6]),(0,[z1,z3,z740,z97,z5,z6]),(0,[z0,z1,z3,z4,z5,z744]),(0,[z0,z1,z3,z782,z5,z6]),(0,[z0,z1,z466,z5,z105,z6]),(0,[z0,z1,z540,z4,z5,z298]),(0,[z0,z1,z3,z4,z555,z18]),(0,[z0,z1,z160,z3,z4,z8]),(0,[z0,z1,z164,z4,z5,z138]),(0,[z0,z1,z3,z183,z5,z191]),(0,[z783,z0,z3,z4,z5,z8])],[(0,[z63,z1,z3,z4,z5,z619]),(0,[z0,z3,z766,z157,z5,z6]),(0,[z0,z1,z389,z4,z5,z188])],[(0,[z0,z1,z3,z4,z784,z6]),(0,[z0,z1,z785,z4,z5,z6]),(0,[z0,z1,z3,z343,z5,z18])],[(0,[z0,z1,z786,z4,z5,z6]),(0,[z170,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z787,z6]),(0,[z0,z1,z3,z223,z5,z6])],[(0,[z0,z1,z3,z4,z788,z6]),(0,[z0,z1,z3,z4,z6,z789]),(0,[z0,z790,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z791]),(0,[z0,z1,z3,z4,z5,z792]),(0,[z34,z1,z3,z223,z5,z6]),(0,[z0,z1,z36,z137,z4,z8])],[(0,[z0,z1,z793,z4,z5,z6]),(0,[z0,z325,z30,z4,z5,z6]),(0,[z0,z1,z30,z225,z5,z6]),(0,[z0,z1,z3,z343,z95,z6]),(0,[z794,z1,z3,z4,z5,z6]),(0,[z310,z0,z1,z3,z4,z8])]],
   [[(0,[z10,z11,z3,z4,z5,z6]),(0,[z11,z3,z4,z5,z111,z6]),(0,[z152,z1,z3,z4,z55,z8]),(0,[z63,z1,z3,z4,z64,z131]),(1,[z171,z1,z3,z4,z8])],[(0,[z0,z1,z3,z4,z5,z795]),(0,[z33,z34,z1,z3,z4,z8]),(0,[z0,z1,z75,z3,z4,z8]),(0,[z0,z1,z137,z796,z4,z6])],[(0,[z0,z1,z797,z4,z5,z6]),(0,[z227,z1,z62,z4,z5,z6]),(0,[z115,z1,z781,z4,z5,z6]),(0,[z0,z1,z542,z3,z4,z8]),(0,[z0,z651,z169,z4,z5,z6]),(0,[z33,z0,z1,z3,z309,z8]),(0,[z0,z1,z3,z4,z531,z18]),(0,[z0,z1,z3,z4,z332,z8]),(0,[z0,z1,z3,z5,z798,z8]),(0,[z209,z0,z3,z4,z5,z398])],[(0,[z0,z1,z3,z4,z312,z799]),(0,[z0,z1,z3,z4,z55,z8]),(0,[z0,z1,z3,z183,z448,z5]),(0,[z0,z1,z3,z4,z800,z6]),(0,[z0,z1,z3,z4,z187,z8]),(0,[z0,z801,z3,z4,z5,z6]),(0,[z0,z1,z3,z802,z5,z6]),(0,[z0,z1,z3,z454,z4,z8])],[(0,[z0,z1,z803,z3,z4,z6]),(0,[z0,z1,z3,z665,z4,z8]),(0,[z0,z1,z3,z130,z5,z113]),(0,[z0,z1,z184,z509,z3,z6]),(0,[z0,z1,z3,z4,z64,z116]),(0,[z401,z0,z1,z3,z4,z8])],[(0,[z0,z1,z3,z4,z5,z804]),(0,[z0,z1,z3,z4,z5,z805]),(0,[z0,z1,z68,z225,z5,z6]),(0,[z690,z0,z3,z157,z5,z6])],[(0,[z0,z806,z3,z4,z5,z6]),(0,[z807,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z808]),(0,[z0,z1,z3,z4,z553,z8])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z809]),(0,[z0,z1,z3,z4,z554,z8]),(0,[z0,z558,z249,z4,z5,z6]),(0,[z810,z1,z3,z4,z5,z6]),(0,[z811,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z812,z5,z18])]],
   [[(0,[z0,z1,z813,z4,z5,z6]),(0,[z0,z1,z3,z4,z14,z6]),(0,[z0,z1,z814,z4,z5,z6]),(0,[z0,z815,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z25])],[(0,[z0,z558,z3,z4,z5,z18]),(0,[z0,z1,z3,z343,z5,z8])],[(0,[z0,z1,z3,z4,z816,z6]),(0,[z0,z1,z3,z4,z236,z8]),(0,[z170,z1,z3,z4,z5,z8])],[(0,[z0,z127,z3,z220,z5,z6]),(0,[z61,z0,z117,z313,z5,z6]),(0,[z0,z1,z3,z4,z817,z6]),(0,[z61,z0,z272,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z298]),(0,[z0,z1,z3,z4,z298,z8]),(0,[z0,z818,z3,z4,z5,z6]),(0,[z0,z1,z462,z184,z5,z6])],[(0,[z0,z1,z3,z819,z5,z6]),(0,[z527,z1,z62,z4,z5,z6]),(0,[z0,z820,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z821,z6]),(0,[z1,z3,z4,z5,z226,z777]),(0,[z34,z1,z3,z4,z5,z298]),(0,[z0,z1,z21,z3,z4,z383])],[(0,[z0,z1,z3,z4,z5,z822]),(0,[z0,z1,z3,z4,z312,z18]),(0,[z527,z1,z3,z4,z69,z6]),(0,[z0,z1,z3,z4,z823,z6]),(0,[z0,z1,z3,z284,z98,z383]),(0,[z0,z1,z21,z3,z4,z824]),(0,[z85,z0,z1,z3,z5,z88])],[(0,[z0,z1,z3,z5,z6,z825]),(0,[z0,z1,z3,z4,z246,z8]),(0,[z0,z1,z3,z4,z826,z6]),(0,[z827,z1,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z5,z588])],[(0,[z0,z1,z122,z4,z5,z6]),(0,[z0,z1,z3,z309,z5,z6]),(0,[z0,z1,z3,z157,z98,z8]),(0,[z171,z3,z4,z5,z42,z6]),(0,[z0,z828,z3,z4,z5,z6]),(0,[z0,z1,z36,z137,z4,z388]),(0,[z0,z1,z3,z4,z531,z8])]],
   [[(0,[z0,z1,z3,z4,z572,z8]),(0,[z0,z1,z642,z4,z43,z6]),(0,[z0,z99,z3,z100,z5,z6]),(0,[z0,z1,z184,z3,z680,z6])],[(0,[z0,z1,z3,z829,z5,z6]),(0,[z94,z22,z3,z4,z5,z6])],[(0,[z0,z1,z830,z3,z5,z6]),(0,[z48,z1,z3,z740,z5,z6]),(0,[z831,z1,z3,z4,z5,z6]),(0,[z0,z1,z114,z454,z5,z6]),(0,[z0,z1,z36,z796,z4,z6]),(1,[z0,z1,z3,z4,z832])],[(0,[z0,z1,z3,z4,z5,z833]),(0,[z0,z22,z3,z225,z5,z6]),(0,[z0,z1,z3,z4,z141,z131]),(0,[z0,z1,z3,z4,z5,z834]),(0,[z0,z1,z540,z4,z42,z6]),(0,[z33,z0,z1,z3,z4,z835]),(0,[z0,z1,z3,z4,z5,z836])],[(0,[z0,z837,z1,z3,z4,z5]),(0,[z0,z107,z3,z4,z108,z6]),(0,[z0,z1,z17,z5,z105,z6]),(0,[z0,z1,z3,z151,z5,z191])],[(0,[z612,z1,z3,z4,z55,z6]),(0,[z0,z1,z838,z3,z5,z6]),(0,[z0,z240,z3,z24,z5,z6]),(0,[z0,z1,z140,z4,z5,z18]),(0,[z154,z0,z1,z3,z4,z528]),(0,[z0,z1,z3,z221,z6,z8]),(0,[z0,z1,z3,z151,z5,z330])],[(0,[z0,z11,z3,z4,z5,z349]),(0,[z152,z127,z3,z4,z5,z18]),(0,[z0,z1,z62,z4,z5,z349]),(0,[z0,z558,z3,z4,z5,z8]),(0,[z0,z3,z100,z766,z5,z6]),(0,[z0,z1,z3,z4,z439,z8])],[(0,[z1,z11,z3,z4,z55,z8]),(0,[z0,z1,z3,z4,z5,z839]),(0,[z0,z286,z3,z4,z5,z18]),(0,[z0,z558,z3,z4,z312,z6]),(0,[z0,z1,z3,z4,z840,z6]),(0,[z0,z1,z841,z4,z5,z6]),(0,[z213,z0,z1,z3,z5,z588])]],
   [[(0,[z0,z842,z3,z4,z5,z6]),(0,[z0,z1,z3,z225,z5,z6]),(0,[z0,z1,z3,z4,z5,z843]),(0,[z0,z325,z3,z4,z5,z564]),(0,[z0,z1,z3,z225,z5,z564]),(0,[z34,z1,z322,z4,z5,z6]),(0,[z0,z1,z844,z4,z5,z6]),(0,[z690,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z845]),(0,[z0,z1,z3,z846,z5,z8])],[(0,[z0,z277,z3,z4,z5,z6]),(0,[z612,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z84]),(0,[z0,z1,z3,z4,z5,z847]),(0,[z0,z1,z3,z4,z5,z848]),(0,[z0,z1,z3,z4,z309,z8])],[(0,[z0,z1,z3,z4,z312,z8]),(0,[z0,z1,z3,z4,z5,z849]),(0,[z0,z1,z3,z130,z98,z8]),(0,[z0,z1,z3,z4,z5,z850]),(0,[z0,z1,z144,z4,z5,z6]),(0,[z0,z1,z466,z184,z5,z6]),(0,[z0,z1,z146,z3,z5,z6])],[(0,[z0,z558,z3,z4,z289,z6]),(0,[z0,z1,z3,z633,z98,z6]),(0,[z0,z1,z3,z851,z5,z6]),(0,[z0,z1,z3,z4,z314,z459])],[(0,[z0,z1,z852,z4,z5,z6]),(0,[z274,z0,z3,z157,z5,z6]),(0,[z0,z853,z3,z4,z5,z6]),(0,[z61,z0,z117,z4,z5,z6]),(0,[z33,z0,z540,z4,z42,z6]),(0,[z0,z1,z854,z4,z5,z6])],[(0,[z112,z558,z3,z97,z5,z6]),(0,[z0,z1,z3,z4,z5,z855]),(0,[z61,z0,z117,z4,z14,z6]),(0,[z0,z1,z3,z4,z856,z6]),(0,[z0,z1,z3,z4,z857,z6]),(0,[z171,z1,z3,z4,z5,z18]),(0,[z0,z1,z36,z146,z137,z6]),(0,[z0,z1,z3,z4,z459,z8]),(0,[z0,z1,z3,z858,z284,z6])],[(0,[z0,z1,z3,z4,z859,z6]),(0,[z0,z1,z3,z4,z5,z860]),(0,[z0,z1,z861,z4,z5,z6])],[(0,[z29,z1,z30,z4,z55,z6]),(0,[z0,z1,z3,z313,z5,z349]),(0,[z0,z1,z184,z498,z3,z6])]],
   [[(0,[z0,z862,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z863,z5]),(0,[z864,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z835,z8]),(0,[z0,z1,z462,z4,z5,z18]),(0,[z0,z1,z3,z4,z173,z18]),(0,[z0,z1,z3,z4,z832,z8])],[(0,[z0,z1,z3,z865,z5,z6]),(0,[z0,z1,z3,z4,z6,z866]),(0,[z0,z1,z867,z4,z5,z6]),(0,[z112,z1,z3,z97,z312,z6]),(0,[z0,z240,z372,z4,z5,z6]),(0,[z0,z1,z3,z4,z868,z8]),(0,[z0,z1,z3,z858,z5,z6]),(0,[z552,z0,z1,z3,z4,z8])],[(0,[z22,z3,z4,z5,z55,z6]),(0,[z0,z1,z30,z4,z5,z380]),(0,[z0,z1,z140,z4,z5,z8]),(0,[z0,z168,z869,z4,z5,z6]),(0,[z0,z1,z541,z137,z4,z6]),(0,[z0,z1,z870,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z871]),(0,[z152,z127,z3,z4,z5,z8]),(0,[z285,z0,z1,z4,z5,z121])],[(0,[z0,z127,z107,z3,z4,z8]),(0,[z0,z286,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z777]),(0,[z449,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z259,z4,z8])],[(0,[z29,z1,z68,z4,z55,z6]),(0,[z170,z1,z3,z4,z69,z6]),(0,[z0,z1,z3,z4,z5,z872]),(0,[z33,z0,z1,z3,z223,z8])],[(0,[z133,z1,z62,z4,z5,z6]),(0,[z210,z1,z3,z4,z5,z131]),(0,[z0,z1,z4,z5,z6,z873]),(0,[z0,z1,z3,z4,z5,z874]),(0,[z0,z875,z3,z4,z5,z8])],[(0,[z162,z1,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z128,z5]),(0,[z353,z1,z3,z130,z5,z6]),(0,[z0,z1,z30,z4,z5,z18]),(0,[z876,z1,z3,z4,z5,z6]),(0,[z78,z1,z3,z4,z5,z216])]],
   [[(0,[z152,z127,z122,z4,z5,z6]),(0,[z0,z1,z877,z4,z5,z6]),(0,[z280,z0,z1,z3,z5,z88]),(0,[z0,z1,z68,z4,z5,z380]),(0,[z0,z82,z1,z3,z4,z8]),(0,[z0,z1,z184,z21,z164,z6])],[(0,[z0,z1,z3,z4,z5,z878]),(0,[z0,z1,z3,z678,z4,z8]),(0,[z0,z1,z3,z608,z5,z191]),(0,[z0,z1,z3,z4,z5,z879]),(0,[z0,z1,z3,z880,z5,z6])],[(0,[z0,z1,z3,z4,z5,z881]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z1,z3,z4,z55,z216,z8]),(0,[z0,z1,z883,z3,z5,z6]),(0,[z171,z1,z3,z4,z5,z8]),(0,[z0,z1,z17,z3,z98,z8]),(0,[z0,z1,z3,z4,z884,z6]),(0,[z0,z1,z21,z3,z4,z8])],[(0,[z0,z127,z122,z4,z5,z6]),(0,[z0,z1,z372,z4,z5,z6]),(0,[z0,z1,z387,z3,z4,z8]),(0,[z0,z277,z3,z4,z141,z6]),(0,[z0,z1,z169,z4,z43,z8]),(0,[z0,z1,z3,z4,z5,z885]),(0,[z0,z1,z17,z45,z5,z6]),(0,[z0,z1,z3,z147,z5,z88])],[(0,[z0,z1,z3,z886,z5,z6]),(0,[z0,z1,z3,z4,z43,z482]),(0,[z0,z1,z4,z5,z773,z6]),(0,[z0,z1,z3,z221,z5,z388])],[(0,[z0,z1,z3,z887,z4,z5]),(0,[z0,z1,z68,z4,z5,z18]),(0,[z0,z277,z3,z308,z5,z6]),(0,[z0,z1,z3,z159,z98,z6]),(0,[z0,z1,z462,z4,z5,z8]),(1,[z0,z1,z3,z5,z845])],[(0,[z0,z558,z3,z4,z5,z158]),(0,[z0,z123,z249,z4,z5,z6]),(0,[z0,z1,z3,z183,z24,z5]),(0,[z292,z0,z117,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z888]),(1,[z0,z1,z3,z309,z8]),(0,[z0,z1,z3,z4,z5,z889]),(0,[z0,z1,z21,z3,z98,z8])],[(0,[z162,z1,z781,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z890]),(0,[z0,z1,z3,z313,z5,z18]),(0,[z0,z1,z3,z4,z69,z199]),(0,[z0,z1,z466,z4,z5,z18]),(0,[z0,z1,z3,z208,z4,z8]),(0,[z0,z1,z891,z4,z5,z6])]],
   [[(0,[z286,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z892]),(0,[z0,z107,z3,z4,z661,z6]),(0,[z0,z1,z3,z4,z5,z893]),(0,[z0,z894,z3,z4,z5,z6]),(0,[z527,z1,z3,z4,z5,z199]),(0,[z0,z1,z3,z4,z5,z349]),(0,[z0,z1,z3,z4,z43,z248])],[(0,[z0,z101,z3,z4,z5,z12]),(0,[z0,z1,z3,z24,z141,z6]),(0,[z895,z1,z3,z4,z5,z6]),(0,[z0,z1,z136,z4,z43,z8]),(0,[z0,z1,z77,z3,z4,z8]),(0,[z0,z1,z365,z4,z5,z335])],[(0,[z0,z1,z3,z4,z312,z158]),(0,[z0,z1,z3,z4,z896,z6]),(0,[z63,z240,z3,z4,z5,z131]),(0,[z0,z1,z3,z220,z5,z6]),(0,[z0,z1,z3,z4,z897,z6]),(0,[z0,z1,z3,z898,z5,z6]),(1,[z0,z1,z796,z4,z6])],[(0,[z438,z11,z3,z4,z5,z6]),(0,[z0,z1,z899,z4,z5,z6]),(0,[z29,z22,z3,z4,z55,z6]),(0,[z0,z1,z3,z220,z14,z6]),(0,[z0,z1,z184,z21,z3,z138])],[(0,[z0,z1,z3,z4,z5,z900]),(0,[z0,z123,z268,z4,z5,z6]),(0,[z0,z1,z30,z4,z5,z8]),(0,[z0,z1,z3,z4,z510,z8]),(0,[z0,z1,z3,z4,z5,z901])],[(0,[z1,z3,z4,z5,z776,z6]),(0,[z0,z1,z462,z5,z98,z6])],[(0,[z115,z286,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z902]),(0,[z0,z22,z3,z4,z5,z380]),(0,[z0,z1,z3,z343,z55,z6]),(0,[z0,z1,z3,z4,z95,z744]),(0,[z0,z240,z3,z4,z5,z18]),(0,[z0,z1,z540,z4,z6,z8])],[(0,[z0,z903,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z904]),(0,[z171,z1,z322,z4,z5,z6]),(0,[z256,z1,z3,z4,z5,z619])]],
   [[(0,[z0,z1,z3,z4,z905,z6]),(0,[z0,z1,z3,z906,z5,z6]),(0,[z0,z1,z80,z4,z5,z349]),(0,[z29,z1,z3,z4,z55,z6]),(0,[z0,z1,z869,z4,z5,z6]),(0,[z0,z1,z907,z3,z4,z6]),(0,[z210,z1,z3,z4,z5,z9])],[(0,[z10,z11,z3,z4,z5,z18]),(0,[z0,z101,z3,z4,z323,z279]),(0,[z0,z1,z908,z4,z5,z6]),(0,[z0,z1,z462,z184,z21,z6])],[(0,[z0,z1,z3,z4,z666,z8]),(0,[z0,z1,z68,z4,z5,z8]),(0,[z0,z124,z1,z3,z4,z8])],[(0,[z0,z1,z909,z4,z5,z6]),(0,[z346,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z4,z5,z380]),(0,[z0,z22,z3,z4,z5,z18]),(0,[z0,z1,z910,z4,z5,z6]),(0,[z0,z240,z3,z4,z64,z6]),(0,[z0,z1,z3,z4,z69,z713]),(0,[z0,z1,z3,z4,z5,z911]),(0,[z0,z1,z508,z21,z3,z6])],[(0,[z0,z1,z912,z3,z5,z6]),(0,[z0,z913,z3,z4,z5,z6]),(0,[z0,z1,z36,z678,z4,z6]),(0,[z0,z1,z3,z4,z312,z113]),(0,[z0,z1,z914,z4,z5,z6]),(1,[z1,z3,z4,z5,z777]),(0,[z0,z1,z3,z313,z5,z8]),(0,[z0,z1,z466,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z176]),(0,[z594,z0,z1,z4,z5,z121]),(0,[z0,z1,z36,z137,z4,z459]),(0,[z0,z1,z184,z3,z858,z6]),(0,[z0,z1,z3,z4,z824,z8])],[(0,[z0,z1,z915,z3,z4,z5]),(0,[z0,z1,z3,z343,z5,z564]),(0,[z0,z1,z372,z4,z141,z6]),(0,[z347,z0,z1,z4,z5,z393])],[(0,[z0,z1,z249,z4,z5,z6]),(0,[z0,z168,z491,z4,z5,z6]),(0,[z0,z1,z3,z766,z5,z6]),(0,[z0,z177,z1,z3,z4,z8]),(0,[z0,z1,z3,z916,z5,z6])],[(0,[z0,z1,z3,z4,z917,z5]),(0,[z375,z1,z3,z4,z95,z6]),(0,[z0,z1,z372,z308,z5,z6]),(0,[z278,z0,z1,z3,z5,z88]),(0,[z0,z101,z3,z4,z5,z110]),(0,[z0,z1,z3,z4,z5,z427]),(0,[z211,z1,z3,z4,z5,z81])]],
   [[(0,[z0,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z5,z918]),(0,[z527,z286,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z289,z113]),(0,[z0,z1,z3,z4,z919,z6]),(0,[z920,z1,z3,z4,z5,z6]),(0,[z0,z1,z573,z3,z4,z8]),(0,[z0,z1,z921,z4,z5,z6]),(0,[z0,z1,z701,z136,z5,z6]),(0,[z0,z668,z3,z100,z5,z6]),(0,[z0,z922,z3,z4,z5,z6])],[(0,[z0,z923,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z14,z18]),(0,[z34,z1,z3,z4,z5,z18]),(0,[z0,z1,z3,z4,z924,z6])],[(0,[z0,z123,z3,z4,z289,z6]),(0,[z112,z1,z3,z97,z5,z113]),(1,[z0,z1,z3,z4,z925]),(0,[z0,z1,z3,z4,z269,z8]),(0,[z0,z1,z3,z24,z5,z226]),(0,[z926,z1,z3,z4,z5,z6]),(0,[z526,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z147,z98,z8])],[(0,[z0,z1,z927,z4,z5,z6]),(0,[z0,z1,z928,z4,z5,z6]),(0,[z0,z240,z3,z4,z5,z8]),(0,[z0,z3,z4,z108,z746,z6]),(0,[z0,z1,z3,z4,z528,z8])],[(0,[z0,z1,z3,z4,z929,z6]),(0,[z0,z1,z268,z4,z5,z6]),(0,[z0,z1,z466,z5,z98,z6]),(0,[z0,z1,z3,z223,z5,z298]),(0,[z0,z1,z3,z4,z544,z8])],[(0,[z0,z930,z3,z4,z5,z6])],[(0,[z10,z11,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z931]),(0,[z0,z1,z3,z932,z4,z5]),(0,[z933,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z934]),(0,[z0,z107,z3,z4,z6,z110]),(0,[z0,z1,z37,z4,z43,z8]),(0,[z0,z1,z3,z4,z222,z8]),(0,[z205,z0,z1,z4,z314,z121])],[(0,[z0,z1,z3,z4,z5,z935]),(0,[z61,z0,z117,z220,z5,z6]),(0,[z0,z1,z3,z4,z746,z6]),(0,[z0,z1,z3,z936,z5,z6])]],
   [[(0,[z0,z22,z3,z4,z5,z8]),(0,[z0,z325,z68,z4,z5,z6]),(0,[z170,z1,z3,z4,z5,z199]),(0,[z0,z1,z937,z4,z5,z6]),(0,[z0,z938,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z939]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z941]),(0,[z0,z942,z3,z4,z5,z6]),(0,[z0,z107,z3,z4,z108,z176]),(0,[z0,z1,z3,z147,z5,z402]),(0,[z0,z1,z943,z4,z5,z6])],[(0,[z0,z1,z944,z4,z5,z6]),(0,[z280,z0,z1,z3,z4,z945]),(0,[z139,z1,z3,z4,z503,z5])],[(0,[z61,z0,z79,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z946]),(0,[z0,z1,z3,z4,z523,z8])],[(0,[z0,z127,z3,z4,z5,z349]),(0,[z0,z1,z3,z4,z5,z947]),(0,[z0,z1,z948,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z8]),(0,[z0,z1,z949,z4,z5,z6]),(1,[z0,z1,z5,z773,z6]),(0,[z1,z3,z4,z5,z8,z950])],[(0,[z63,z1,z3,z4,z141,z131]),(0,[z0,z1,z3,z4,z14,z8]),(0,[z34,z1,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z19,z8])],[(0,[z527,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z951]),(0,[z0,z1,z952,z4,z5,z6]),(0,[z0,z1,z953,z4,z5,z6]),(0,[z0,z1,z17,z691,z5,z6]),(0,[z0,z1,z3,z4,z954,z6]),(1,[z0,z1,z4,z5,z955]),(0,[z0,z1,z4,z5,z955,z121])]],
   [[(0,[z0,z1,z3,z956,z5,z6]),(0,[z0,z1,z3,z4,z5,z957]),(0,[z958,z0,z1,z3,z4,z5]),(0,[z48,z1,z3,z130,z5,z18]),(0,[z63,z1,z3,z308,z5,z131]),(0,[z0,z1,z322,z223,z5,z6])],[(0,[z0,z1,z511,z5,z105,z6]),(0,[z688,z1,z62,z4,z5,z6]),(0,[z0,z1,z959,z4,z5,z6]),(0,[z0,z1,z3,z4,z98,z84]),(0,[z0,z1,z540,z4,z5,z182]),(0,[z33,z0,z3,z4,z42,z182])],[(0,[z0,z1,z3,z4,z336,z8]),(0,[z0,z1,z3,z4,z289,z6]),(0,[z0,z1,z3,z4,z141,z18]),(0,[z0,z168,z169,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z960]),(0,[z0,z961,z3,z4,z5,z6])],[(0,[z0,z1,z255,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z962]),(0,[z0,z1,z144,z4,z5,z18]),(0,[z0,z1,z963,z4,z5,z6]),(0,[z0,z1,z3,z4,z121,z528]),(0,[z0,z1,z146,z3,z5,z18]),(0,[z0,z1,z3,z964,z5,z6])],[(0,[z0,z1,z3,z740,z5,z6]),(1,[z1,z3,z4,z776,z6]),(0,[z94,z1,z3,z4,z95,z116]),(0,[z94,z1,z3,z4,z95,z18]),(0,[z520,z0,z1,z3,z4,z8]),(0,[z63,z1,z140,z4,z5,z131]),(0,[z0,z1,z3,z308,z5,z18]),(0,[z33,z0,z107,z3,z4,z8]),(0,[z0,z1,z3,z4,z314,z6]),(0,[z0,z1,z146,z5,z43,z6])],[(0,[z0,z1,z3,z965,z5,z6]),(0,[z0,z3,z4,z5,z746,z6]),(0,[z0,z1,z3,z858,z4,z6]),(0,[z0,z1,z3,z4,z5,z966])],[(0,[z0,z106,z1,z3,z4,z8]),(0,[z413,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z967,z5,z6]),(0,[z0,z1,z136,z220,z5,z6]),(0,[z0,z1,z3,z968,z5,z6]),(0,[z0,z1,z3,z309,z5,z298]),(0,[z0,z1,z3,z4,z18,z378]),(0,[z0,z1,z3,z4,z652,z8])],[(0,[z0,z969,z3,z4,z5,z6]),(0,[z280,z0,z1,z3,z183,z5]),(0,[z0,z1,z3,z313,z69,z6]),(0,[z970,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z81,z8]),(0,[z527,z1,z3,z313,z5,z6]),(0,[z0,z1,z3,z4,z971,z6]),(0,[z0,z1,z184,z21,z3,z6]),(0,[z0,z1,z164,z4,z5,z18])],[(0,[z0,z1,z3,z4,z5,z972]),(0,[z0,z1,z3,z183,z5,z83]),(0,[z0,z1,z3,z308,z64,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z0,z1,z3,z221,z5,z459]),(0,[z0,z1,z3,z858,z98,z6]),(0,[z0,z1,z184,z21,z3,z25])],[(0,[z0,z1,z3,z4,z5,z973]),(0,[z0,z1,z3,z4,z5,z974]),(0,[z1,z3,z4,z5,z6,z777]),(0,[z0,z1,z322,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z975]),(0,[z209,z0,z3,z4,z5,z47]),(0,[z976,z1,z3,z4,z5,z8])],[(0,[z0,z325,z3,z4,z5,z6]),(0,[z0,z1,z3,z977,z5,z6]),(0,[z0,z1,z3,z220,z5,z349]),(0,[z0,z1,z978,z4,z5,z6]),(0,[z189,z0,z1,z3,z4,z8])],[(0,[z0,z1,z708,z4,z5,z6]),(0,[z0,z1,z75,z136,z5,z6])],[(0,[z0,z1,z3,z4,z979,z6]),(0,[z0,z1,z980,z3,z5,z6]),(0,[z0,z981,z3,z4,z5,z6]),(0,[z0,z1,z982,z4,z5,z6]),(0,[z48,z1,z3,z130,z5,z8]),(0,[z0,z1,z140,z4,z64,z6]),(0,[z0,z1,z3,z4,z5,z983])],[(0,[z0,z1,z72,z3,z4,z8]),(0,[z0,z1,z322,z4,z5,z298]),(0,[z0,z1,z3,z5,z191,z845])],[(0,[z115,z1,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z141,z8]),(0,[z63,z1,z3,z4,z5,z777]),(0,[z132,z0,z3,z766,z5,z6]),(0,[z0,z1,z3,z984,z5,z6]),(0,[z0,z1,z120,z4,z5,z335]),(0,[z0,z1,z164,z4,z6,z8])]],
   [[(0,[z0,z1,z3,z4,z5,z985]),(0,[z0,z1,z3,z4,z111,z8]),(0,[z0,z1,z3,z4,z986,z6]),(0,[z315,z1,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z987]),(0,[z0,z1,z144,z4,z5,z8]),(0,[z0,z1,z988,z4,z5,z6]),(0,[z0,z1,z146,z3,z5,z8])],[(0,[z0,z1,z989,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z990]),(0,[z0,z1,z3,z991,z5,z6]),(0,[z280,z0,z1,z3,z4,z925]),(0,[z0,z1,z3,z489,z98,z6]),(0,[z94,z1,z3,z4,z95,z8]),(0,[z0,z1,z3,z4,z95,z138]),(0,[z0,z1,z3,z308,z5,z8]),(0,[z61,z527,z117,z4,z5,z6]),(0,[z0,z1,z992,z4,z5,z6]),(0,[z0,z1,z5,z773,z105,z6])],[(0,[z0,z1,z3,z24,z5,z6]),(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z1,z322,z309,z5,z6]),(0,[z0,z1,z3,z4,z5,z994]),(0,[z0,z1,z3,z137,z4,z8])],[(0,[z0,z1,z3,z4,z173,z116]),(0,[z0,z1,z3,z4,z5,z995]),(0,[z0,z1,z4,z5,z996,z8])],[(0,[z0,z1,z997,z4,z5,z6]),(0,[z0,z1,z3,z4,z998,z6]),(0,[z0,z1,z373,z3,z4,z8]),(0,[z0,z1,z3,z4,z180,z18]),(1,[z0,z1,z164,z4,z8])],[(0,[z0,z1,z3,z999,z5,z6]),(0,[z61,z0,z354,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z158]),(0,[z0,z1,z1000,z4,z5,z6]),(0,[z0,z1,z1001,z4,z5,z6]),(0,[z0,z3,z4,z5,z279,z720]),(0,[z0,z1,z164,z4,z5,z8]),(0,[z0,z217,z3,z4,z5,z110])],[(0,[z0,z1,z3,z4,z323,z6])],[(0,[z61,z0,z361,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1002]),(0,[z0,z1,z3,z4,z5,z1003]),(0,[z0,z1,z30,z343,z5,z6]),(0,[z0,z1,z466,z136,z5,z6]),(0,[z171,z1,z3,z4,z6,z8]),(0,[z0,z1,z1004,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1005]),(0,[z0,z1,z3,z763,z5,z6])]],
   [[(0,[z0,z1,z1006,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z6]),(0,[z0,z1,z3,z4,z5,z1007]),(0,[z0,z566,z1,z3,z4,z8])],[(0,[z527,z1,z3,z4,z5,z6]),(0,[z0,z1,z1008,z3,z4,z6]),(0,[z0,z1,z3,z1009,z5,z6]),(0,[z0,z1010,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z141]),(0,[z0,z1,z169,z4,z14,z6]),(0,[z1011,z1,z3,z4,z5,z6]),(0,[z0,z1,z542,z4,z43,z6]),(0,[z0,z1,z37,z4,z43,z248]),(0,[z0,z894,z3,z4,z5,z18])],[(0,[z350,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1012,z6]),(0,[z527,z1,z3,z4,z14,z6]),(0,[z1013,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1014]),(0,[z0,z1,z3,z4,z1015,z6]),(0,[z0,z1,z1016,z4,z5,z6]),(0,[z0,z1,z3,z4,z18,z8])],[(0,[z504,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z220,z5,z18]),(0,[z33,z0,z1,z540,z4,z8]),(0,[z0,z1,z3,z5,z6,z845])],[(0,[z50,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1017])],[(0,[z0,z1,z62,z4,z43,z8]),(0,[z0,z1,z3,z1018,z5,z6]),(0,[z0,z1,z120,z4,z5,z234]),(0,[z0,z1,z68,z343,z5,z6]),(0,[z0,z1,z3,z4,z5,z1019]),(1,[z0,z869,z4,z5,z6]),(0,[z61,z0,z379,z4,z5,z6]),(0,[z0,z1,z3,z4,z18,z590])],[(0,[z0,z1,z3,z4,z637,z8]),(0,[z154,z0,z3,z4,z5,z47]),(0,[z0,z1,z457,z3,z4,z8])],[(0,[z0,z1,z174,z4,z5,z18]),(0,[z0,z1,z781,z4,z5,z6]),(0,[z0,z1,z3,z1020,z5,z6]),(0,[z0,z1,z136,z4,z14,z6]),(0,[z0,z1,z3,z159,z4,z8]),(0,[z0,z500,z1,z3,z4,z8])]],
   [[(0,[z0,z267,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1021,z6]),(0,[z170,z1,z3,z313,z5,z6]),(0,[z33,z0,z3,z4,z42,z6]),(0,[z0,z1,z4,z43,z335,z8]),(0,[z549,z0,z1,z3,z4,z8]),(0,[z461,z0,z3,z4,z5,z212])],[(0,[z0,z1,z1022,z4,z5,z6]),(0,[z0,z1,z3,z4,z1023,z6]),(0,[z527,z1,z80,z4,z5,z6]),(0,[z1024,z1,z3,z4,z5,z6]),(0,[z34,z1,z540,z4,z5,z6]),(0,[z0,z1,z3,z4,z180,z8]),(0,[z0,z738,z3,z4,z5,z8])],[(0,[z0,z107,z11,z3,z4,z8]),(0,[z0,z1,z3,z4,z1025,z6]),(0,[z0,z1,z4,z5,z6,z996]),(0,[z0,z1,z37,z4,z43,z38]),(0,[z0,z1,z3,z221,z173,z6]),(0,[z0,z1,z3,z4,z5,z383]),(0,[z0,z1,z190,z4,z5,z161])],[(0,[z0,z1,z3,z4,z5,z1026]),(0,[z0,z123,z3,z4,z5,z18]),(1,[z0,z3,z766,z5,z6]),(0,[z0,z1,z3,z4,z5,z1027]),(0,[z0,z1,z3,z4,z5,z824]),(0,[z0,z1,z3,z4,z531,z88])],[(0,[z0,z1,z3,z4,z27,z8]),(0,[z1,z3,z130,z740,z5,z6]),(0,[z0,z277,z3,z24,z5,z6]),(0,[z0,z1,z3,z4,z14,z349]),(0,[z0,z1,z3,z4,z5,z1028]),(0,[z0,z107,z3,z4,z746,z6]),(0,[z85,z0,z1,z3,z5,z845])],[(0,[z0,z1,z1029,z4,z5,z6]),(0,[z0,z1,z1030,z4,z5,z6]),(0,[z61,z11,z62,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1031]),(0,[z436,z1,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z945,z6]),(0,[z0,z1,z3,z4,z141,z81]),(0,[z0,z1,z3,z4,z5,z1032]),(0,[z0,z1,z3,z100,z98,z8]),(0,[z0,z1033,z3,z4,z5,z6]),(0,[z0,z1,z36,z137,z4,z6]),(0,[z0,z1,z3,z137,z221,z8])],[(0,[z0,z1,z3,z4,z5,z1034]),(0,[z63,z40,z1,z3,z4,z5]),(0,[z0,z1,z3,z796,z4,z6])],[(0,[z0,z1035,z3,z4,z5,z6]),(0,[z61,z170,z117,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z1036,z6]),(0,[z0,z1,z3,z4,z312,z1037]),(0,[z0,z1038,z3,z4,z5,z6]),(0,[z0,z1,z3,z220,z5,z8])],[(0,[z0,z1,z1039,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1040]),(0,[z1041,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z799]),(0,[z139,z1,z3,z4,z5,z226]),(0,[z0,z1,z3,z223,z5,z18]),(0,[z0,z1,z3,z4,z5,z38]),(0,[z0,z1,z3,z4,z332,z6]),(0,[z0,z40,z1,z3,z5,z88])],[(0,[z0,z1,z3,z4,z1042,z6]),(0,[z683,z11,z3,z4,z5,z6]),(0,[z1,z3,z4,z740,z5,z6]),(0,[z0,z1,z3,z4,z203,z8]),(0,[z0,z1,z3,z313,z5,z199]),(0,[z0,z1,z3,z386,z4,z8]),(0,[z0,z1,z3,z4,z5,z868]),(0,[z0,z1,z3,z4,z332,z25]),(0,[z0,z1,z3,z4,z393,z8])],[(0,[z0,z1043,z3,z4,z5,z6]),(0,[z0,z558,z3,z4,z5,z113]),(0,[z0,z22,z3,z343,z5,z6]),(0,[z292,z0,z3,z4,z42,z6])],[(0,[z0,z1,z3,z4,z5,z1044]),(0,[z0,z1,z174,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1045]),(0,[z0,z22,z3,z4,z5,z564]),(0,[z63,z0,z1,z3,z4,z531])],[(0,[z0,z1,z3,z1046,z4,z6]),(0,[z0,z1,z268,z4,z5,z18]),(0,[z61,z0,z869,z4,z5,z6]),(0,[z0,z1,z3,z4,z1047,z6]),(0,[z0,z1048,z3,z4,z5,z6]),(0,[z205,z0,z1,z4,z5,z393]),(0,[z0,z1,z3,z4,z1049,z6])],[(0,[z0,z1,z3,z1050,z5,z6]),(0,[z0,z1,z3,z1051,z5,z6]),(0,[z0,z1,z3,z4,z1052,z6]),(0,[z0,z1,z1053,z4,z5,z6])],[(0,[z710,z11,z3,z4,z5,z6]),(0,[z23,z0,z1,z3,z4,z8]),(0,[z63,z1,z3,z4,z5,z131]),(0,[z0,z169,z869,z4,z5,z6]),(0,[z209,z0,z107,z3,z4,z8]),(0,[z85,z0,z1,z3,z332,z88])]],
   [[(0,[z152,z710,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1054,z6]),(0,[z0,z123,z3,z4,z5,z8]),(0,[z0,z1,z3,z343,z5,z6]),(0,[z0,z277,z372,z4,z5,z6]),(0,[z211,z1,z3,z4,z5,z226])],[(0,[z170,z1,z3,z4,z5,z6]),(0,[z0,z286,z62,z4,z5,z6]),(0,[z0,z123,z3,z4,z312,z6]),(0,[z0,z1,z190,z4,z43,z6]),(0,[z0,z1,z4,z5,z6,z955])],[(0,[z0,z1,z3,z4,z5,z1055]),(0,[z170,z1,z3,z4,z14,z6]),(0,[z1056,z1,z3,z4,z5,z6]),(0,[z171,z1,z3,z4,z5,z182]),(1,[z0,z1,z3,z858,z6])],[(0,[z0,z1,z3,z1057,z5,z6]),(0,[z0,z1,z3,z4,z5,z116]),(0,[z0,z1,z1058,z4,z5,z6])],[(0,[z0,z1,z1059,z4,z5,z6]),(0,[z1060,z0,z3,z4,z5,z6])],[(0,[z527,z127,z3,z4,z5,z6]),(0,[z0,z1061,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1062,z5,z6]),(0,[z0,z1,z3,z1063,z4,z5]),(0,[z0,z1,z372,z24,z5,z6]),(0,[z0,z1,z3,z223,z5,z8]),(0,[z0,z1,z3,z4,z531,z6])],[(0,[z1064,z0,z1,z3,z4,z5]),(0,[z112,z123,z3,z97,z5,z6]),(0,[z0,z1,z114,z136,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z64,z6]),(0,[z61,z0,z117,z4,z5,z349]),(0,[z0,z525,z1,z3,z4,z8]),(0,[z1065,z1,z3,z4,z5,z6]),(0,[z0,z1,z36,z137,z221,z6])],[(0,[z152,z670,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1066]),(0,[z0,z1,z249,z4,z289,z6]),(0,[z0,z1,z3,z1067,z5,z6]),(0,[z0,z240,z3,z4,z141,z6])],[(0,[z0,z1,z268,z4,z5,z8]),(0,[z0,z1,z136,z49,z5,z6]),(0,[z1068,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z1069,z5,z6]),(0,[z0,z1,z122,z4,z5,z18]),(0,[z0,z1,z3,z1070,z5,z6]),(0,[z0,z1,z3,z5,z6,z798]),(0,[z0,z1,z3,z812,z5,z6]),(0,[z0,z240,z3,z308,z5,z6]),(0,[z0,z1,z3,z4,z5,z1071]),(0,[z0,z1,z3,z309,z5,z18])],[(0,[z0,z1,z3,z4,z698,z8]),(0,[z0,z1,z3,z4,z1072,z6]),(0,[z29,z325,z3,z4,z55,z6]),(0,[z29,z1,z3,z225,z55,z6]),(0,[z1073,z1,z3,z4,z5,z6]),(0,[z0,z99,z3,z100,z5,z18]),(0,[z0,z1,z3,z4,z5,z1074]),(0,[z85,z0,z1,z3,z531,z88]),(0,[z0,z1075,z3,z4,z5,z6])],[(0,[z0,z558,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z18,z512]),(0,[z0,z1,z3,z4,z5,z1076]),(0,[z0,z1,z1077,z4,z5,z6]),(0,[z0,z1,z3,z4,z1078,z6]),(0,[z0,z1,z3,z936,z5,z8]),(0,[z0,z1,z334,z3,z5,z425])],[(0,[z94,z1,z3,z4,z776,z6]),(0,[z0,z107,z1,z3,z4,z8])],[(0,[z0,z1,z3,z4,z5,z1079]),(0,[z0,z1,z3,z1080,z5,z6]),(0,[z0,z1,z1081,z4,z5,z6]),(0,[z1,z781,z62,z4,z5,z6]),(0,[z0,z1,z268,z4,z289,z6]),(0,[z0,z325,z3,z4,z5,z380]),(0,[z0,z1,z3,z225,z5,z380]),(0,[z0,z240,z140,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1082]),(0,[z0,z1,z3,z4,z265,z8]),(0,[z0,z1,z3,z137,z4,z868]),(0,[z0,z1,z3,z4,z619,z8]),(0,[z0,z1,z3,z967,z5,z18])]],
   [[(0,[z0,z1,z3,z97,z289,z6]),(0,[z171,z1,z540,z4,z5,z6]),(0,[z0,z107,z3,z4,z108,z18]),(0,[z0,z266,z3,z4,z5,z279]),(0,[z0,z1,z17,z5,z105,z18])],[(0,[z0,z1,z3,z4,z312,z6]),(0,[z0,z1,z3,z5,z773,z6]),(0,[z0,z1,z184,z21,z3,z18])],[(0,[z0,z1,z1083,z4,z5,z6]),(0,[z0,z1,z3,z309,z6,z8]),(0,[z0,z1,z3,z221,z5,z6]),(0,[z0,z1,z457,z4,z43,z6])],[(0,[z0,z1084,z3,z4,z5,z6]),(0,[z0,z1,z3,z220,z69,z6]),(0,[z0,z1,z540,z4,z173,z6]),(0,[z0,z1,z322,z4,z5,z18]),(0,[z33,z0,z3,z4,z746,z6]),(0,[z0,z107,z3,z4,z110,z8]),(0,[z0,z1,z3,z4,z18,z528]),(0,[z0,z1,z3,z4,z5,z955])],[(0,[z0,z1,z3,z1085,z5,z6]),(0,[z0,z325,z3,z4,z5,z18]),(0,[z0,z1,z3,z225,z5,z18]),(0,[z527,z1,z3,z220,z5,z6]),(0,[z1086,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z1087]),(0,[z0,z1,z3,z4,z5,z1088]),(0,[z0,z1,z3,z4,z221,z8]),(0,[z189,z0,z1,z3,z4,z832])],[(0,[z0,z1089,z3,z4,z5,z6]),(0,[z0,z277,z3,z4,z5,z18]),(0,[z0,z3,z869,z4,z5,z6]),(0,[z0,z1,z3,z1090,z5,z6]),(0,[z0,z1,z190,z4,z5,z121])],[(0,[z0,z1,z3,z4,z5,z1091]),(0,[z0,z1,z3,z1092,z5,z6]),(0,[z0,z1,z3,z4,z5,z720])],[(0,[z112,z1,z3,z97,z5,z6]),(0,[z0,z1,z3,z4,z289,z947]),(0,[z33,z171,z3,z4,z42,z6]),(1,[z0,z1,z540,z4,z8]),(0,[z0,z101,z3,z4,z5,z279]),(0,[z1,z3,z4,z5,z6,z950])]],
   [[(0,[z481,z11,z3,z4,z5,z6]),(0,[z0,z1,z122,z4,z5,z8]),(0,[z152,z286,z3,z4,z5,z6]),(0,[z115,z1,z80,z4,z5,z18]),(0,[z0,z123,z3,z4,z5,z158]),(0,[z0,z1,z3,z4,z55,z138]),(0,[z0,z1,z3,z4,z69,z904]),(0,[z61,z0,z117,z4,z5,z18]),(0,[z0,z1,z3,z4,z6,z1093]),(0,[z232,z0,z3,z157,z5,z6]),(0,[z0,z1,z3,z309,z5,z8]),(0,[z0,z1,z137,z4,z43,z8])],[(0,[z0,z11,z466,z4,z5,z6]),(0,[z0,z1,z3,z1094,z5,z6]),(0,[z0,z1,z140,z4,z5,z6]),(0,[z0,z1,z3,z4,z1095,z6]),(0,[z0,z1,z3,z4,z5,z1096]),(0,[z0,z99,z3,z100,z5,z8]),(0,[z0,z1,z3,z4,z5,z1097]),(0,[z0,z1,z120,z4,z5,z955])],[(0,[z0,z1,z3,z4,z1098,z6]),(0,[z215,z11,z3,z4,z5,z6]),(0,[z0,z99,z3,z766,z5,z6]),(0,[z0,z101,z3,z4,z279,z528]),(0,[z0,z1,z17,z5,z773,z6]),(0,[z0,z1,z1099,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1100]),(0,[z0,z1,z3,z1101,z5,z6]),(0,[z0,z1,z3,z24,z5,z18]),(0,[z0,z1,z1102,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1103]),(0,[z0,z1,z509,z3,z4,z8]),(0,[z1104,z1,z3,z4,z5,z6]),(0,[z33,z0,z1,z322,z4,z8]),(0,[z1105,z1,z3,z4,z5,z6]),(0,[z0,z1,z1106,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1107])],[(0,[z0,z1,z3,z4,z5,z1108]),(0,[z0,z1,z3,z4,z5,z1109]),(0,[z0,z1,z3,z4,z5,z1110]),(0,[z0,z107,z3,z4,z108,z8]),(0,[z0,z1,z17,z5,z105,z8]),(0,[z0,z875,z3,z4,z5,z6])],[(0,[z0,z1,z114,z245,z5,z6]),(0,[z0,z1,z3,z4,z5,z1111]),(0,[z0,z1,z3,z4,z5,z1112]),(0,[z0,z1,z498,z3,z4,z8]),(0,[z0,z3,z4,z5,z6,z720]),(0,[z1113,z1,z3,z4,z5,z6]),(0,[z0,z1,z184,z21,z3,z8])],[(0,[z0,z1,z3,z1114,z5,z6]),(0,[z210,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z24,z5,z131]),(0,[z0,z1,z3,z4,z551,z18]),(0,[z0,z1,z3,z1115,z5,z6]),(0,[z0,z1,z3,z382,z98,z6]),(0,[z0,z1,z1116,z4,z5,z6])]],
   [[(0,[z0,z1,z1117,z4,z5,z6]),(0,[z0,z1,z3,z1118,z5,z6]),(0,[z118,z0,z1,z3,z4,z8]),(0,[z0,z1,z322,z4,z5,z8]),(0,[z0,z1,z114,z5,z773,z6])],[(0,[z0,z1,z3,z225,z5,z8]),(0,[z0,z1,z3,z4,z5,z1119]),(0,[z132,z0,z466,z157,z5,z6]),(0,[z0,z1,z3,z4,z5,z388]),(0,[z0,z1,z844,z4,z5,z8])],[(0,[z115,z1,z122,z4,z5,z6]),(0,[z0,z1120,z3,z4,z5,z6]),(0,[z0,z123,z3,z4,z5,z113]),(0,[z0,z1,z268,z4,z5,z158]),(0,[z0,z277,z3,z4,z5,z8]),(0,[z0,z1,z3,z4,z14,z1119]),(0,[z0,z1,z3,z4,z5,z1121]),(0,[z0,z1,z1122,z4,z5,z6]),(0,[z0,z1,z3,z284,z98,z6]),(0,[z0,z1,z3,z98,z425,z8])],[(0,[z0,z1,z3,z1123,z4,z6]),(0,[z162,z1,z62,z4,z5,z18]),(0,[z0,z286,z80,z4,z5,z6]),(0,[z0,z1,z3,z4,z97,z925]),(0,[z0,z168,z20,z4,z5,z6]),(0,[z0,z1,z1124,z4,z5,z6]),(0,[z154,z0,z3,z4,z5,z212]),(0,[z0,z1,z3,z4,z18,z832])],[(0,[z0,z1,z3,z130,z289,z6]),(0,[z0,z1,z3,z4,z14,z987]),(0,[z0,z1,z1125,z4,z5,z6]),(0,[z0,z1,z462,z4,z5,z6]),(0,[z0,z1,z3,z183,z5,z845])],[(0,[z0,z1,z1126,z4,z5,z6]),(0,[z0,z1,z3,z4,z1127,z6]),(0,[z115,z1,z80,z4,z5,z8]),(0,[z61,z0,z117,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1128]),(0,[z0,z1,z3,z4,z5,z182]),(0,[z0,z1,z462,z4,z5,z25])],[(0,[z0,z1129,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1130,z6]),(0,[z0,z1,z3,z4,z5,z1131]),(0,[z0,z22,z30,z4,z5,z6]),(0,[z34,z1,z3,z4,z5,z182]),(0,[z1132,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1133]),(0,[z280,z0,z1,z3,z4,z5]),(0,[z0,z1,z372,z4,z5,z18]),(0,[z0,z1,z3,z308,z141,z6]),(0,[z0,z1,z3,z1134,z5,z6]),(0,[z0,z1,z3,z4,z321,z8])]],
   [[(0,[z0,z1,z3,z24,z5,z8]),(0,[z0,z1,z3,z4,z6,z1135]),(0,[z0,z1,z3,z4,z330,z8]),(0,[z0,z1,z3,z164,z4,z8])],[(0,[z0,z1136,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1137]),(0,[z33,z0,z3,z223,z42,z6]),(1,[z0,z1,z3,z221,z8]),(0,[z0,z1,z146,z3,z137,z8]),(0,[z0,z1,z3,z4,z173,z832])],[(0,[z0,z1,z591,z4,z43,z6]),(0,[z112,z1,z3,z128,z97,z5]),(0,[z0,z1,z3,z4,z5,z1138]),(0,[z0,z1,z3,z4,z5,z1139]),(0,[z0,z1,z3,z208,z98,z6]),(0,[z0,z1,z3,z4,z180,z222]),(0,[z0,z1,z4,z5,z188,z955]),(0,[z0,z1,z3,z4,z98,z383])],[(0,[z0,z11,z3,z4,z14,z6]),(0,[z0,z1,z30,z4,z5,z6]),(0,[z0,z1,z62,z4,z14,z6]),(0,[z0,z1,z3,z4,z1140,z6]),(0,[z0,z1,z3,z4,z5,z1037]),(0,[z0,z1,z3,z4,z1141,z6]),(0,[z0,z1,z30,z4,z5,z564]),(0,[z0,z1,z140,z4,z141,z6]),(0,[z0,z1,z3,z4,z5,z1142]),(0,[z0,z1,z870,z4,z5,z8])],[(0,[z0,z22,z68,z4,z5,z6]),(0,[z0,z1,z372,z4,z64,z6]),(0,[z170,z1,z3,z220,z5,z6]),(0,[z0,z1,z3,z4,z5,z1143]),(0,[z0,z1,z3,z4,z1144,z6])],[(0,[z0,z1,z3,z4,z5,z1145]),(0,[z0,z1,z140,z308,z5,z6]),(0,[z33,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z323,z298]),(0,[z0,z1,z3,z595,z4,z8])],[(0,[z127,z710,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1146,z6]),(0,[z0,z1,z3,z4,z5,z1147]),(0,[z0,z444,z3,z100,z5,z6]),(0,[z0,z530,z3,z4,z5,z279]),(0,[z0,z1,z3,z4,z173,z459]),(0,[z0,z1,z3,z4,z569,z18])],[(1,[z1,z3,z740,z5,z6]),(0,[z0,z325,z3,z225,z5,z6]),(0,[z29,z1,z3,z4,z55,z380]),(0,[z0,z1,z3,z4,z1148,z6]),(0,[z0,z1,z3,z1149,z5,z6]),(0,[z0,z1,z3,z4,z5,z482]),(0,[z0,z1,z689,z4,z43,z6]),(0,[z0,z1,z37,z796,z4,z6]),(0,[z0,z3,z4,z5,z8,z778])]],
   [[(0,[z162,z1,z62,z4,z5,z8]),(0,[z1,z1150,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z925,z6]),(0,[z0,z1,z3,z4,z1151,z6]),(0,[z0,z1,z68,z4,z5,z564]),(0,[z215,z0,z1,z3,z4,z8]),(0,[z646,z1,z3,z4,z5,z131]),(0,[z242,z0,z3,z4,z5,z47]),(0,[z0,z1,z3,z4,z1152,z6]),(0,[z205,z0,z1,z4,z5,z955]),(0,[z0,z1,z3,z5,z845,z88])],[(0,[z0,z1,z3,z4,z1153,z6]),(0,[z0,z1,z3,z4,z5,z113]),(0,[z0,z1,z3,z4,z289,z1002]),(0,[z646,z1,z3,z97,z5,z6]),(0,[z132,z0,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z588,z8])],[(0,[z0,z1,z3,z476,z98,z6]),(0,[z0,z1,z21,z3,z4,z84]),(0,[z0,z1,z3,z313,z5,z6]),(0,[z0,z1,z466,z4,z5,z6]),(0,[z0,z1,z540,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z835]),(0,[z0,z1,z3,z4,z6,z528]),(0,[z0,z1154,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z248])],[(0,[z527,z1,z122,z4,z5,z6]),(0,[z0,z1,z3,z4,z1155,z6]),(0,[z29,z1,z3,z4,z55,z18]),(0,[z0,z1,z372,z4,z5,z8]),(0,[z0,z1,z3,z313,z14,z6]),(0,[z783,z0,z3,z4,z5,z6]),(0,[z0,z1,z146,z3,z5,z388])],[(0,[z0,z1,z1156,z4,z5,z6]),(0,[z583,z127,z3,z4,z5,z6]),(0,[z0,z869,z117,z4,z5,z6]),(0,[z0,z1,z21,z164,z4,z8])],[(0,[z0,z1,z3,z4,z5,z925]),(0,[z0,z1,z3,z4,z5,z1157]),(0,[z0,z1,z3,z4,z141,z226]),(0,[z0,z1,z1158,z3,z5,z6]),(0,[z0,z1,z3,z442,z4,z8]),(0,[z0,z3,z4,z5,z720,z47]),(0,[z0,z101,z3,z4,z5,z720]),(0,[z205,z0,z1,z4,z5,z121])],[(0,[z0,z1,z1159,z4,z5,z6]),(0,[z29,z1,z3,z4,z776,z6]),(0,[z0,z1,z3,z4,z5,z1160]),(0,[z0,z1,z3,z1161,z5,z6]),(0,[z33,z0,z3,z4,z42,z298]),(0,[z0,z1,z910,z4,z5,z18])]],
   [[(0,[z0,z1,z3,z4,z5,z1162]),(0,[z1,z122,z62,z4,z5,z6]),(0,[z0,z1,z1163,z4,z5,z6]),(0,[z0,z1,z3,z4,z185,z8]),(0,[z0,z1,z3,z4,z5,z1164]),(0,[z292,z0,z1,z3,z4,z8])],[(0,[z0,z1,z3,z4,z5,z1165]),(0,[z0,z1,z3,z4,z1166,z5]),(0,[z461,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z368,z8]),(0,[z0,z1,z3,z147,z98,z6])],[(0,[z0,z240,z3,z4,z5,z6]),(0,[z0,z1,z249,z4,z5,z18]),(0,[z303,z0,z1,z3,z5,z88]),(0,[z0,z1,z3,z4,z95,z380])],[(0,[z0,z445,z169,z4,z5,z6]),(0,[z0,z1,z3,z465,z4,z8]),(0,[z85,z0,z1,z3,z24,z5]),(0,[z0,z1,z3,z4,z5,z1167]),(0,[z0,z1,z540,z309,z5,z6]),(0,[z33,z0,z3,z309,z42,z6]),(0,[z1168,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1169]),(0,[z0,z1,z1170,z3,z5,z6])],[(0,[z0,z107,z3,z4,z108,z482]),(0,[z0,z1,z3,z4,z180,z121]),(0,[z0,z1,z164,z4,z173,z6])],[(0,[z0,z1,z1171,z4,z5,z6]),(0,[z0,z1,z3,z4,z1172,z6]),(0,[z1173,z0,z1,z3,z4,z5]),(0,[z0,z1,z37,z4,z43,z6]),(0,[z0,z266,z1,z3,z4,z8])],[(0,[z135,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1174]),(0,[z0,z1,z3,z4,z5,z1175]),(0,[z0,z1,z3,z4,z1176,z6]),(0,[z0,z1,z1177,z4,z5,z6])],[(0,[z0,z22,z3,z4,z5,z6]),(0,[z328,z1,z62,z4,z5,z6]),(0,[z485,z0,z1,z3,z4,z8]),(1,[z0,z3,z4,z746,z6])]],
   [[(0,[z0,z1,z3,z4,z1178,z6]),(0,[z61,z0,z117,z4,z69,z6]),(0,[z0,z1,z3,z4,z5,z1179]),(0,[z0,z1,z114,z136,z5,z18])],[(0,[z0,z1,z3,z1180,z5,z6]),(0,[z0,z1,z3,z4,z1181,z6]),(0,[z29,z1,z3,z4,z55,z8]),(0,[z0,z1,z3,z4,z64,z18]),(0,[z562,z0,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z87,z18])],[(0,[z0,z1,z3,z4,z1182,z6]),(0,[z1,z80,z781,z4,z5,z6]),(0,[z0,z1,z291,z4,z43,z6]),(0,[z0,z1,z462,z4,z5,z138]),(0,[z0,z1,z389,z4,z5,z222])],[(0,[z0,z1,z3,z97,z98,z8]),(0,[z33,z0,z322,z4,z42,z6]),(0,[z0,z1,z3,z4,z329,z8]),(0,[z0,z1,z3,z4,z6,z832])],[(0,[z0,z1,z3,z4,z5,z564]),(0,[z171,z1,z3,z4,z173,z6]),(0,[z33,z34,z3,z4,z42,z6]),(0,[z0,z1,z1183,z4,z5,z6]),(0,[z0,z177,z3,z4,z108,z6]),(0,[z0,z1,z3,z137,z4,z482])],[(0,[z34,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1184]),(0,[z0,z1,z3,z4,z238,z8]),(0,[z132,z0,z144,z157,z5,z6]),(0,[z0,z1,z1185,z4,z5,z6]),(0,[z0,z1,z120,z4,z5,z188]),(0,[z0,z942,z3,z4,z5,z18]),(0,[z0,z266,z3,z4,z5,z165])],[(0,[z0,z710,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z406,z8]),(0,[z0,z1,z1186,z4,z5,z6]),(0,[z1187,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1188])],[(0,[z0,z1,z249,z4,z5,z8]),(0,[z0,z1,z3,z4,z5,z1189]),(0,[z0,z1,z17,z13,z5,z6]),(0,[z0,z1,z190,z4,z43,z8]),(0,[z0,z1,z1190,z4,z5,z6]),(0,[z0,z451,z1,z3,z4,z8])]],
   [[(0,[z115,z267,z80,z4,z5,z6]),(0,[z0,z1,z249,z4,z312,z6]),(0,[z0,z1,z3,z4,z5,z1191]),(0,[z0,z1,z3,z137,z4,z248]),(0,[z0,z1,z3,z4,z98,z8])],[(0,[z152,z127,z174,z4,z5,z6]),(0,[z0,z1,z3,z4,z415,z8]),(0,[z0,z1,z36,z442,z4,z6]),(0,[z1192,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z832])],[(0,[z0,z1,z3,z1193,z5,z6]),(1,[z1,z781,z4,z5,z6]),(0,[z0,z558,z268,z4,z5,z6]),(0,[z0,z1,z615,z21,z3,z6]),(0,[z0,z1,z3,z1194,z5,z6]),(0,[z0,z1,z3,z4,z680,z8]),(0,[z0,z1,z3,z4,z43,z8]),(0,[z0,z1,z384,z3,z4,z8])],[(0,[z0,z1,z3,z1195,z5,z6]),(1,[z0,z3,z4,z5,z720]),(0,[z0,z1,z3,z221,z5,z18])],[(0,[z0,z1,z3,z4,z95,z8]),(0,[z282,z1,z3,z4,z5,z226]),(0,[z33,z0,z1,z3,z4,z482])],[(0,[z0,z1,z80,z4,z14,z6]),(0,[z1,z3,z4,z95,z776,z6]),(0,[z0,z1,z1196,z4,z5,z6]),(0,[z34,z1,z3,z309,z5,z6]),(0,[z0,z1,z3,z4,z543,z8]),(0,[z0,z1,z114,z136,z5,z8])],[(0,[z0,z1,z268,z4,z312,z6]),(0,[z112,z1,z249,z97,z5,z6]),(0,[z0,z1,z3,z4,z289,z18]),(0,[z0,z1,z3,z4,z64,z8]),(0,[z139,z1,z3,z4,z5,z216]),(0,[z0,z1,z3,z4,z5,z199]),(0,[z0,z1,z17,z4,z14,z6]),(0,[z171,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z459])],[(0,[z0,z127,z466,z4,z5,z6]),(0,[z0,z1,z3,z4,z252,z8]),(0,[z0,z1,z3,z4,z1197,z6]),(0,[z0,z1,z3,z4,z14,z199]),(0,[z0,z1,z3,z4,z1198,z6]),(0,[z33,z0,z3,z4,z567,z6]),(0,[z0,z1199,z3,z4,z5,z6])]],
   [[(0,[z0,z1200,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1201]),(0,[z112,z1,z3,z97,z5,z18]),(0,[z0,z1,z3,z4,z258,z8]),(0,[z0,z1,z3,z4,z1202,z6]),(0,[z0,z1,z3,z4,z314,z18]),(0,[z0,z1,z3,z4,z5,z1203])],[(0,[z0,z1,z3,z4,z5,z1204]),(0,[z0,z1,z3,z4,z434,z8]),(0,[z976,z1,z3,z4,z5,z6])],[(0,[z0,z1205,z3,z4,z5,z6]),(0,[z0,z1,z80,z4,z43,z8]),(0,[z0,z1,z3,z4,z5,z1206]),(0,[z1,z3,z4,z776,z55,z6]),(0,[z0,z1,z3,z846,z5,z6]),(0,[z1,z3,z4,z5,z777,z131]),(0,[z0,z1,z3,z4,z5,z1207]),(0,[z0,z1,z3,z1208,z5,z6]),(0,[z0,z1,z1209,z3,z4,z5]),(0,[z0,z1,z943,z4,z5,z8])],[(0,[z139,z0,z1,z3,z4,z531]),(0,[z0,z1,z3,z4,z5,z1210]),(0,[z0,z1,z17,z4,z43,z8]),(0,[z0,z1,z3,z4,z243,z18]),(0,[z0,z1,z21,z3,z858,z6])],[(0,[z0,z1,z3,z4,z5,z1211]),(0,[z48,z1,z3,z130,z5,z6]),(0,[z112,z1,z268,z97,z5,z6]),(0,[z0,z1,z1212,z4,z5,z6]),(0,[z0,z325,z3,z343,z5,z6]),(0,[z63,z277,z3,z4,z5,z131]),(0,[z0,z1,z3,z4,z69,z349]),(0,[z33,z171,z1,z3,z4,z8]),(0,[z0,z1,z3,z4,z5,z1213]),(0,[z0,z1,z36,z146,z5,z6])],[(0,[z0,z11,z3,z220,z5,z6]),(0,[z0,z1,z3,z1214,z5,z6]),(0,[z579,z127,z3,z4,z5,z6]),(0,[z0,z1,z62,z220,z5,z6]),(0,[z0,z1,z1215,z4,z5,z6]),(0,[z527,z1,z3,z4,z5,z349]),(0,[z0,z1,z3,z183,z5,z425])],[(0,[z0,z1,z3,z4,z5,z1216]),(0,[z0,z1,z1217,z3,z5,z6]),(0,[z280,z0,z1,z3,z24,z5]),(0,[z0,z1,z1218,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1219]),(0,[z0,z1,z3,z4,z141,z6]),(0,[z0,z1,z540,z4,z108,z6]),(0,[z0,z1,z796,z4,z43,z6])],[(0,[z1,z3,z4,z95,z55,z8]),(0,[z0,z1,z3,z4,z5,z1220])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1019).take 249) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1268)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 510, 249] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 82).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 165).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 247).take 9).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [82, 83, 82, 9] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_38031

theorem PEqualNP.Outside.L_meta_38031 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277070528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38031.solve