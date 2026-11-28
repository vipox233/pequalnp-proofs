import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37775

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4209044096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2001100c4161855a#64 ++ 0x84002201882c30ab#64 ++ 0xd80b349cc3e38fff#64 ++ 0xfb016693987c71ff#64 : BitVec 256),
   (0x40114125232c332b#64 ++ 0x28022824a4658665#64 ++ 0xbe35cb67233c733b#64 ++ 0xf7c6b96ce4678e67#64 : BitVec 256),
   (0x82c60c780c16dc30#64 ++ 0x7058c18f0182db86#64 ++ 0x7bc60c783c3ffc3f#64 ++ 0x6f78c18f0787ff87#64 : BitVec 256),
   (0x01780f8036806a84#64 ++ 0x402f01f006d00d50#64 ++ 0xf9f80f803fc07fc6#64 ++ 0xdf3f01f007f80ff8#64 : BitVec 256),
   (0x05bff0003bfb0007#64 ++ 0x80b7fe00077f6000#64 ++ 0xf5fff0003fff8006#64 ++ 0x3ebffe0007fff000#64 : BitVec 256),
   (0x01eeaed280000000#64 ++ 0x003dd5da50000000#64 ++ 0xf7ffffffc0000001#64 ++ 0xfefffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f80f803fc07fc6 0xdf3f01f007f80ff8

def z1 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7ffffffc0000001 0xfefffffff8000000

def z2 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff0003fff8006 0x3ebffe0007fff000

def z3 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd80b349cc3e38fff 0xfb016693987c71ff

def z4 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe35cb67233c733b 0xf7c6b96ce4678e67

def z5 : W := mkw 0x8286005808128410 0x1050c00b01025082 0x0002001800038000 0x0000400300007000

def z6 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc60c783c3ffc3f 0x6f78c18f0787ff87

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0xb635cb6700000001 0xf6c6b96ce0000000

def z8 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x08000000233c733a 0x0100000004678e67

def z9 : W := mkw 0x0001100001610002 0x80002200002c2000 0xd00b300003e38006 0x3a016600007c7000

def z10 : W := mkw 0x0086000008120000 0x0010c00001024000 0x71c600003c3f8006 0x2e38c0000787f000

def z11 : W := mkw 0xa287107c4977957a 0xb450e20f892ef2af 0x0207307cc03f8039 0x2040e60f9807f007

def z12 : W := mkw 0xa2c71c7c4d77dd7a 0xf458e38f89aefbaf 0xfbcf3cfcffffffff 0xff79e79f9fffffff

def z13 : W := mkw 0x01bea00032800004 0x0037d40006500000 0xf5fff0003fc00006 0x3ebffe0007f80000

def z14 : W := mkw 0x0010010036806a84 0x4002002006d00d50 0x080000003fc07fc6 0x0100000007f80ff8

def z15 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0x0607f07fc0000001 0x20c0fe0ff8000000

def z16 : W := mkw 0x83eeaefa8c16dc30 0x707dd5df5182db86 0xfffffffffc3ffc3f 0xffffffffff87ff87

def z17 : W := mkw 0x0000000800008410 0x0000000100001082 0x5802041800238c3f 0x6b00408300047187

def z18 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0a000c7800007c39 0x4140018f00000f87

def z19 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x0a000b67233c733b 0xc140016ce4678e67

def z20 : W := mkw 0xa3efbefecd77dd7a 0xf47df7dfd9aefbaf 0xffffffffffffffff 0xffffffffffffffff

def z21 : W := mkw 0x61795fad77edffff 0xec2f2bf5aefdbfff 0xffffffffffffffff 0xffffffffffffffff

def z22 : W := mkw 0x6011512d636db77b 0xac022a25ac6db6ef 0xbe37fb7fe33ff33b 0xf7c6ff6ffc67fe67

def z23 : W := mkw 0x0010010022002200 0x0002002004400440 0xb8300b0023007302 0xd706016004600e60

def z24 : W := mkw 0x01680e8014804884 0x402d01d002900910 0x41c804801cc00cc4 0x0839009003980198

def z25 : W := mkw 0x0000002000041020 0x2000000400008204 0x3a040860203c703b 0x6740810c04078e07

def z26 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x41ca3498c0000000 0x0839469318000000

def z27 : W := mkw 0x40115125236d332b 0xa8022a24a46da665 0xfe3ffb6723fff33f 0xffc7ff6ce47ffe67

def z28 : W := mkw 0x200110044161014a 0x84002200882c2029 0x00013004c0000000 0x0000260098000000

def z29 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x41ca30003fff8006 0x0839460007fff000

def z30 : W := mkw 0xc2d74d7d2f3eff3b 0x785ae9afa5e7dfe7 0xfff7cf7f3f3fff3f 0xfffef9efe7e7ffe7

def z31 : W := mkw 0x2001102c4165957a 0xa4002205882cb2af 0xfa0f3cfce3ffffff 0xff41e79f9c7fffff

def z32 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x2bc40c783c1c7c39 0x4578818f07838f87

def z33 : W := mkw 0x0128a28280000000 0x0025145050000000 0x8439f387c0000000 0x90873e70f8000000

def z34 : W := mkw 0x01feaed2b2800004 0x003fd5da56500000 0xf7ffffffffc00007 0xfefffffffff80000

def z35 : W := mkw 0x0487f000097b0003 0x8090fe00012f6000 0x0407f000003f8000 0x2080fe000007f000

def z36 : W := mkw 0x05ffff803ffb6a87 0xc0bffff007ff6d50 0xfdffff803fffffc6 0xffbffff007fffff8

def z37 : W := mkw 0x0000000800008410 0x0000000100001082 0x0002001800238039 0x2000400300047007

def z38 : W := mkw 0x82c60c580c12cc10 0x5058c18b01825982 0x79c20c183c03fc06 0x4f38418307807f80

def z39 : W := mkw 0x41794fa537ac7baf 0x682f29f4a6f58f75 0xf9f80f803ffc7ffe 0xdf3f01f007ff8fff

def z40 : W := mkw 0x441151253bff332f 0xa8822a24a77fe665 0x080000003ffff33e 0x0100000007fffe67

def z41 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x0e05c067233c733b 0x21c0b80ce4678e67

def z42 : W := mkw 0x45fffff7bbff332f 0xa8bffffef77fe665 0xfffffffffffff33f 0xfffffffffffffe67

def z43 : W := mkw 0x0011400023280003 0x0002280004650000 0xb435c000233c0002 0x3686b80004678000

def z44 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0x41ca30001cc38004 0x0839460003987000

def z45 : W := mkw 0x87feec703e9e5825 0x70ffdd8e07d3cb04 0x27f4c8603c1c7000 0x04fe990c07838e00

def z46 : W := mkw 0x2000100840418450 0x840002010808308a 0x400a3498c0c38cc4 0x0801469318187198

def z47 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x0803301cc3e38fff 0x21006603987c71ff

def z48 : W := mkw 0x01aea00000000000 0x0035d40000000000 0xf5fff00000000000 0x3ebffe0000000000

def z49 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x29f00b003fc07fc6 0x053e016007f80ff8

def z50 : W := mkw 0x82c60c700c165820 0x7058c18e0182cb04 0x73c60c783c1c7001 0x6e78c18f07838e00

def z51 : W := mkw 0x01680e8004004800 0x402d01d000800900 0xf9f80f803c007c06 0xdf3f01f007800f80

def z52 : W := mkw 0x40104121220c3221 0x2802082424418644 0x2634cb63201c7000 0x04c6996c64038e00

def z53 : W := mkw 0x0401f00001690003 0x80803e00002d2000 0x0401f00000000000 0x00803e0000000000

def z54 : W := mkw 0x0139400033a80007 0x0027280006750000 0xf5fdc0003ffc0006 0x3ebfb80007ff8000

def z55 : W := mkw 0x01eeaed294804884 0x403dd5da52900910 0xf7ffffffdcc00cc5 0xfefffffffb980198

def z56 : W := mkw 0x00c60c5000000000 0x0018c18a00000000 0x73c60c7800000001 0x6e78c18f00000000

def z57 : W := mkw 0x820000280c16dc30 0x704000050182db86 0x080000003c3ffc3e 0x010000000787ff87

def z58 : W := mkw 0x05bff00033e90007 0x80b7fe00067d2000 0xf5fff00003c00000 0x3ebffe0000780000

def z59 : W := mkw 0x0539f00033e90007 0x80a73e00067d2000 0x8439f00003c00000 0x10873e0000780000

def z60 : W := mkw 0x0000000014804884 0x4000000002900910 0x000000001cc00cc4 0x0000000003980198

def z61 : W := mkw 0x0010012022043220 0x2002002404408644 0xba340b60233c733b 0xf746816c04678e67

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x02000b6700000001 0xc040016ce0000000

def z63 : W := mkw 0x0168aed280000000 0x002d15da50000000 0x8639ffffc0000001 0xd0c73ffff8000000

def z64 : W := mkw 0x0010010022002200 0x0002002004400440 0xbe35cb6723007303 0xf7c6b96ce4600e60

def z65 : W := mkw 0x41784fa1368c7aa5 0x682f09f426d18f54 0x27f4cb633c1c7000 0x04fe996c67838e00

def z66 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x5803341cc0238c3f 0x6b00668398047187

def z67 : W := mkw 0x00500d0036806a84 0x400a01a006d00d50 0x79c00c003fc07fc6 0x4f38018007f80ff8

def z68 : W := mkw 0x000100040120010a 0x0000200080240021 0xd809048403e00fff 0xfb012090807c01ff

def z69 : W := mkw 0x20411c0c4561cd5a 0xc408238188ac39ab 0xf9cb3c9cffe3ffff 0xff3967939ffc7fff

def z70 : W := mkw 0x200110044161014a 0x84002200882c2029 0xd00b3084c3e383c6 0xba016610987c7078

def z71 : W := mkw 0x200110044161014a 0x84002200882c2029 0x80093084c3c003c0 0x9001261098780078

def z72 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x21f00b003c007000 0x043e016007800e00

def z73 : W := mkw 0x0001000001200002 0x0000200000240000 0x9001000003200002 0x3200200000640000

def z74 : W := mkw 0x4000012500043328 0x28000024a0008665 0x0a000b6700007339 0xc140016ce0000e67

def z75 : W := mkw 0x21ffbfdef7e1efde 0xc43ff7fbdefc3dfb 0xffffffffffe3ffff 0xfffffffffffc7fff

def z76 : W := mkw 0x05ffff803ffb6a87 0xc0bffff007ff6d50 0xf5fffb003ffff006 0x3ebfff6007fffe00

def z77 : W := mkw 0x83fe0ff83e96feb4 0x707fc1ff07d2dfd6 0xfbfe0ff83fffffff 0xff7fc1ff07ffffff

def z78 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0x25f4c0003c1c0000 0x04be980007838000

def z79 : W := mkw 0x05fffed2bbfb0007 0x80bfffda577f6000 0xf7ffffffffff8007 0xfefffffffffff000

def z80 : W := mkw 0x00400ed280000000 0x000801da50000000 0x02000fffc0000001 0xc04001fff8000000

def z81 : W := mkw 0x828600280c16dc30 0x7050c0050182db86 0x79c600003c3ffc3e 0x2f38c0000787ff87

def z82 : W := mkw 0x40104121220c3221 0x2802082424418644 0x00000000201c7000 0x0000000004038e00

def z83 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x98010004233c733b 0xf300200084678e67

def z84 : W := mkw 0x82400efa8404dc30 0x704801df50809b86 0x0a000fffc0007c39 0xc14001fff8000f87

def z85 : W := mkw 0xc2d74d752f3e7b2b 0x785ae9aea5e7cf65 0xbff5cb673f3c733b 0xf7feb96ce7e78e67

def z86 : W := mkw 0x0001000c0120851a 0x00002001802410a3 0xd803041c03238f3f 0xfb006083806471e7

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00b349cc0000001 0xfa01669398000000

def z88 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff49cffff8007 0xfebffe939ffff000

def z89 : W := mkw 0xc2c60d7d0c16ff38 0x7858c1afa182dfe7 0x7bc60f7f3c3fff3f 0xef78c1efe787ffe7

def z90 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff4803fff8fc6 0xffbffe9007fff1f8

def z91 : W := mkw 0x8286007008161020 0x3050c00e0102c204 0x02040060001c0000 0x0040800c00038000

def z92 : W := mkw 0x01be00003a920004 0x0037c00007524000 0xf1fe00003fff8006 0x3e3fc00007fff000

def z93 : W := mkw 0x45bff1253bff332f 0xa8b7fe24a77fe665 0xfffffb673ffff33f 0xffffff6ce7fffe67

def z94 : W := mkw 0x6011512d636db77b 0xac022a25ac6db6ef 0xfe3fffffe3ffffff 0xffc7fffffc7fffff

def z95 : W := mkw 0xa2c71c5c4d73cd5a 0xd458e38b89ae79ab 0xd9cb349cdfe38fff 0xfb3966939bfc71ff

def z96 : W := mkw 0x0139100033e10006 0x80272200067c2000 0xf1fb30003fe38006 0x3e3f660007fc7000

def z97 : W := mkw 0x8286007808169430 0x3050c00f0102d286 0x02060078003f8039 0x2040c00f0007f007

def z98 : W := mkw 0x87bff0283fffdc37 0xf0f7fe0507fffb86 0xfdfff0003ffffc3e 0x3fbffe0007ffff87

def z99 : W := mkw 0x25bff00c7bfb855f 0x84b7fe018f7f70ab 0xfdfff49cffff8fff 0xffbffe939ffff1ff

def z100 : W := mkw 0x41eeaff780043328 0x283dd5fef0008665 0xffffffffc0007339 0xfffffffff8000e67

def z101 : W := mkw 0x2000100840418450 0x840002010808308a 0xd80a3498c3c38fc6 0xdb014693187871f8

def z102 : W := mkw 0x21efbedec161855a 0x843df7dbd82c30ab 0xffffffffc3e38fff 0xfffffffff87c71ff

def z103 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x73ce3cf8c0000001 0x6e79c79f18000000

def z104 : W := mkw 0x45bff1053bfb230f 0x88b7fe20a77f6461 0xf5fff3073fff8306 0xbebffe60e7fff060

def z105 : W := mkw 0x01eeae8000000000 0x003dd5d000000000 0xf5ffff8000000000 0xfebffff000000000

def z106 : W := mkw 0x8200007800049430 0x3040000f00009286 0x0200007800000039 0x0040000f00000007

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0xd808048003c00fc6 0xdb010090007801f8

def z108 : W := mkw 0x00400c0004004800 0x4008018000800900 0x79c00c003c007c06 0x4f38018007800f80

def z109 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x0800000003e38ffe 0x01000000007c71ff

def z110 : W := mkw 0x0539f38033e92287 0x80a73e70067d2450 0x8439f38003c003c0 0x90873e7000780078

def z111 : W := mkw 0x401141052328230b 0x08022820a4650461 0x8431c30703000300 0x90863860e0600060

def z112 : W := mkw 0x05bff1003ffb6a87 0xc0b7fe2007ff6d50 0xfdfff0003fffffc6 0x3fbffe0007fffff8

def z113 : W := mkw 0x82c60c700c165820 0x7058c18e0182cb04 0x7bc40c603c1c7c06 0x4f78818c07838f80

def z114 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0xb637fb7fc0000001 0xf6c6ff6ff8000000

def z115 : W := mkw 0x41ffeff7a32c332b 0x283ffdfef4658665 0xffffffffe33c733b 0xfffffffffc678e67

def z116 : W := mkw 0x049750003bfb0007 0x8092ea00077f6000 0x71c600003fff8006 0x2e38c00007fff000

def z117 : W := mkw 0x82c60c580c12cc10 0x5058c18b01825982 0x41c204181c038c04 0x0838408303807180

def z118 : W := mkw 0x21eebedac0418450 0x843dd7db5808308a 0xf7ffffffc0c38cc5 0xfefffffff8187198

def z119 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x480a3498c3e38ffe 0x09014693187c71ff

def z120 : W := mkw 0x0128a28280000000 0x0025145050000000 0xb63dfbe7c0000001 0xf6c7bf7cf8000000

def z121 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x25f7f0003c3f8000 0x24befe000787f000

def z122 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x77f6cf7b00000001 0x6efed9ef60000000

def z123 : W := mkw 0x041150003bfb0007 0x80822a00077f6000 0x000000003fff8006 0x0000000007fff000

def z124 : W := mkw 0x8286a07a88169430 0x3050d40f5102d286 0x0607f07fc03f8039 0x20c0fe0ff807f007

def z125 : W := mkw 0x2087b05ec161855a 0x8410f60bd82c30ab 0xde0ff4ffc3e38fff 0xfbc1fe9ff87c71ff

def z126 : W := mkw 0x00c60c000c124800 0x4018c18001824900 0x79c60c003c3ffc06 0x6f38c1800787ff80

def z127 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x49c204183c3ffc3e 0x093840830787ff87

def z128 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xc00b349cc3c38fc4 0x98016693987871f8

def z129 : W := mkw 0x0000010000002200 0x0000002000000440 0x08000b0000007300 0xc100016000000e60

def z130 : W := mkw 0x2000000c40008558 0x04000001880010ab 0x0800049cc0000ff9 0xc1000093980001ff

def z131 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xfdfff0043fff833f 0xffbffe0087fff067

def z132 : W := mkw 0x45bff1213bff3227 0xa8b7fe24277fe644 0xf7fffb633ffff006 0x3effff6c67fffe00

def z133 : W := mkw 0x00400c0004004800 0x4008018000800900 0xf9c80c803fc07fc6 0xdf39019007f80ff8

def z134 : W := mkw 0xc2d64d712e1e7a21 0x785ac9ae25c3cf44 0x27f4cb633c1c7000 0x04fe996c67838e00

def z135 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0x71ce30003cff8006 0x2e39c600079ff000

def z136 : W := mkw 0x01feafd2b6806a84 0x403fd5fa56d00d50 0xffffffffffc07fc7 0xfffffffffff80ff8

def z137 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x27f7fb7fc0000001 0x24feff6ff8000000

def z138 : W := mkw 0x83ee0ef81c96dcb4 0x707dc1df0392db96 0x7bce0cf83cfffcff 0x6f79c19f079fff9f

def z139 : W := mkw 0x41bfe125232c332b 0x2837fc24a4658665 0xfffffb67233c733b 0xffffff6ce4678e67

def z140 : W := mkw 0xa2c61c584c53cc50 0xd458c38b098a798a 0x41ca3498dcc38cc4 0x083946931b987198

def z141 : W := mkw 0x01feafd2a2002200 0x003fd5fa54400440 0xffffffffe3007303 0xfffffffffc600e60

def z142 : W := mkw 0x0128028010800084 0x0025005002100010 0x0008008000c000c0 0x0001001000180018

def z143 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x25f4c0003fff8006 0x04be980007fff000

def z144 : W := mkw 0x40014025012c112b 0x28002804a0258225 0x0605c067003c0039 0x20c0b80ce0078007

def z145 : W := mkw 0x0539f282b3e90007 0x80a73e50567d2000 0x8439f387c3c00000 0x90873e70f8780000

def z146 : W := mkw 0x00400c0004004800 0x4008018000800900 0x08000c0000007c00 0x4100018000000f80

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0xf63fffffc0000001 0xfec7fffff8000000

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800048000000fc0 0xc1000090000001f8

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x5002000000238006 0x2a00400000047000

def z150 : W := mkw 0x0086002008161020 0x2010c0040102c204 0x7bc608603c3ff03f 0x6f78c10c0787fe07

def z151 : W := mkw 0x83780ff83684feb4 0x706f01ff06d09fd6 0xfbf80ff83fc07fff 0xdf7f01ff07f80fff

def z152 : W := mkw 0x2000100040410040 0x8400020008082008 0x00083080c0c000c0 0x0001061018180018

def z153 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xa635cb67231c7300 0x94c6b96ce4638e60

def z154 : W := mkw 0x0010010022002200 0x0002002004400440 0x0800000023007302 0x0100000004600e60

def z155 : W := mkw 0x82400c280c16dc30 0x704801850182db86 0x79c00c003c3ffc3e 0x4f3801800787ff87

def z156 : W := mkw 0x0010010022002200 0x0002002004400440 0x8030030003000300 0x9006006000600060

def z157 : W := mkw 0x00400ed280000000 0x000801da50000000 0xb635cfffc0000001 0xf6c6b9fff8000000

def z158 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x8e31cb6703007339 0xd1c6396ce0600e67

def z159 : W := mkw 0x000100040120010a 0x0000200080240021 0xbe35cb670320033b 0xf7c6b96ce0640067

def z160 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0xf5fff0001cc38004 0x3ebffe0003987000

def z161 : W := mkw 0x05bff282bbfb0007 0x80b7fe50577f6000 0xf5fff387ffff8006 0xbebffe70fffff000

def z162 : W := mkw 0xa2400c7c4404dd78 0x7448018f88809baf 0x0a000cfcc0007ff9 0xc140019f98000fff

def z163 : W := mkw 0x60115125636d336b 0xac022a24ac6da66d 0xbe3dfbe7e3fc73fb 0xf7c7bf7cfc7f8e7f

def z164 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x2635cb67203c7039 0x24c6b96ce4078e07

def z165 : W := mkw 0x0178af82b6806a84 0x402f15f056d00d50 0xfdf9ff87ffc07fc6 0xdfbf3ff0fff80ff8

def z166 : W := mkw 0x0087100009730002 0x8010e200012e6000 0xf1cf30003fff8006 0x3e39e60007fff000

def z167 : W := mkw 0x83ee0ef80c16dc30 0x707dc1df0182db86 0xfbfe0ff83c3ffc3f 0xff7fc1ff0787ff87

def z168 : W := mkw 0x05bff052bbfb0007 0x80b7fe0a577f6000 0xf7fff07fffff8007 0x3efffe0ffffff000

def z169 : W := mkw 0x0128a00000000000 0x0025140000000000 0x8439f00000000000 0x10873e0000000000

def z170 : W := mkw 0x40104125220c3329 0x28020824a4418665 0x2e34cb67201c7339 0xc5c6996ce4038e67

def z171 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf1fa3f98c0000000 0xde3f47f318000000

def z172 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x27f4cb6300000000 0x04fe996c60000000

def z173 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x49c804803fc07fc6 0x0939009007f80ff8

def z174 : W := mkw 0x83eeaef28c165820 0x707dd5de5182cb04 0x27f4cb633c1c7000 0x04fe996c67838e00

def z175 : W := mkw 0x01680e8000000000 0x002d01d000000000 0x21f00b0000000000 0x043e016000000000

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800000003000302 0xd300000000600060

def z177 : W := mkw 0x41794fa537ac7baf 0x682f29f4a6f58f75 0xfffdcfe73ffc7fff 0xffffb9fce7ff8fff

def z178 : W := mkw 0x8286007808169430 0x3050c00f0102d286 0x3a060878203ff03b 0x6740c10f0407fe07

def z179 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe3fffffe33c733b 0xffc7fffffc678e67

def z180 : W := mkw 0x82c60c700c165820 0x7058c18e0182cb04 0x23c408603c1c7000 0x0478810c07838e00

def z181 : W := mkw 0x82400c580400cc10 0x5048018b00801982 0x0000041800000c00 0x0000008300000180

def z182 : W := mkw 0x2000100840418450 0x840002010808308a 0x580a3498c0e38cff 0x6b014693181c719f

def z183 : W := mkw 0x83eeaeda8c12cc10 0x507dd5db51825982 0xf7ffffffdc038c05 0xfefffffffb807180

def z184 : W := mkw 0x21791f8c77e1efde 0xc42f23f18efc3dfb 0xf9fb3f9cffe3ffff 0xff3f67f39ffc7fff

def z185 : W := mkw 0x00400f8004006a80 0x400801f000800d50 0xd8080f8003c07fc6 0xdb0101f000780ff8

def z186 : W := mkw 0x0487f000097b0003 0x8090fe00012f6000 0x75c7f0003c3f8006 0x2eb8fe000787f000

def z187 : W := mkw 0x0168ae8280000000 0x002d15d050000000 0xf5f9ff87c0000000 0xdebf3ff0f8000000

def z188 : W := mkw 0x0001100001610002 0x80002200002c2000 0xd00b349cc3e38007 0xfa016693987c7000

def z189 : W := mkw 0x40114121232c3223 0x2802282424658644 0xb635cb63233c7002 0x36c6b96c64678e00

def z190 : W := mkw 0x0086000008120000 0x0010c00001024000 0x41c200001c038004 0x0838400003807000

def z191 : W := mkw 0x25bff0047bfb014f 0x84b7fe008f7f6029 0xf5fff084ffff83c6 0xbebffe109ffff078

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0xb435c00000000000 0x3686b80000000000

def z193 : W := mkw 0x2011500c6369855b 0x84022a018c6d30ab 0xfc3ff49ce3ff8fff 0xff87fe939c7ff1ff

def z194 : W := mkw 0x82c60ff80c16feb0 0x7058c1ff0182dfd6 0x7bc60ff83c3fffff 0xef78c1ff0787ffff

def z195 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x0003301cc0238039 0x2000660398047007

def z196 : W := mkw 0x01eeaed288120000 0x003dd5da51024000 0xf7fffffffc3f8007 0xfeffffffff87f000

def z197 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xa5fdf0003fdc0000 0x14bfbe0007fb8000

def z198 : W := mkw 0xc2400d7d0404ff38 0x784801afa0809fe7 0x0a000f7f00007f39 0xc14001efe0000fe7

def z199 : W := mkw 0x2001000c4120855a 0x04002001882410ab 0x9801049cc3200ffb 0xf3002093986401ff

def z200 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x8809349cc3c00ff9 0xd1012693987801ff

def z201 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0x00023018c0000000 0x0000460318000000

def z202 : W := mkw 0x0486b00008530000 0x8090d600010a6000 0x0002300000038000 0x0000460000007000

def z203 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xffffffffc3c00fc7 0xfffffffff87801f8

def z204 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008008003c003c0 0x9001001000780078

def z205 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x400b349cc0e38cfd 0x28016693981c719f

def z206 : W := mkw 0x01feaf8036806a84 0x403fd5f006d00d50 0xfdffff803fc07fc6 0xffbffff007f80ff8

def z207 : W := mkw 0x41ffeff7b7ac7baf 0x683ffdfef6f58f75 0xfffffffffffc7fff 0xffffffffffff8fff

def z208 : W := mkw 0x8200002808169430 0x304000050102d286 0x00000000003f8038 0x000000000007f007

def z209 : W := mkw 0x4097e177a32c332b 0x2812fc2ef4658665 0xbe37fb7fe33c733b 0xf7c6ff6ffc678e67

def z210 : W := mkw 0x00400f8004006a80 0x400801f000800d50 0x08000f8000007fc0 0xc10001f000000ff8

def z211 : W := mkw 0x0138000032800004 0x0027000006500000 0xf1f800003fc00006 0x1e3f000007f80000

def z212 : W := mkw 0x0000002000041020 0x2000000400008204 0xbe35cb67203c703b 0xf7c6b96ce4078e07

def z213 : W := mkw 0x82c6ac7a8c16dc30 0x7058d58f5182db86 0x7fc7fc7ffc3ffc3f 0x6ff8ff8fff87ff87

def z214 : W := mkw 0x0138038032802284 0x0027007006500450 0xf1f803803fc003c6 0x9e3f007007f80078

def z215 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x5a020c780023fc3f 0x6b40418f00047f87

def z216 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xb7f5cb6700000001 0xf6feb96ce0000000

def z217 : W := mkw 0xa2c61c784c57dc70 0xf458c38f098afb8e 0x7bce3cf8fcfffcff 0x6f79c79f1f9fff9f

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003301cc0000001 0x2000660398000000

def z219 : W := mkw 0x45ffffa53fff7baf 0xe8bffff4a7ffef75 0xffffffe73fffffff 0xfffffffce7ffffff

def z220 : W := mkw 0x4497f1252b7f332b 0xa892fe24a56fe665 0xbe37fb67233ff33b 0xf7c6ff6ce467fe67

def z221 : W := mkw 0x00400c080400cc10 0x4008018100801982 0x79c20c183c23fc3f 0x6f38418307847f87

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z223 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbce0cf83fffffff 0xff79c19f07ffffff

def z224 : W := mkw 0x0138038032802284 0x0027007006500450 0x8038038003c003c0 0x9007007000780078

def z225 : W := mkw 0x6011512d636db77b 0xac022a25ac6db6ef 0xd80b349ce3ffffff 0xfb0166939c7fffff

def z226 : W := mkw 0x00400ed280000000 0x000801da50000000 0xd20b3fffc0000001 0xfa4167fff8000000

def z227 : W := mkw 0x01680e8014804884 0x402d01d002900910 0x01c000001c000000 0x0038000003800000

def z228 : W := mkw 0x000100040120010a 0x0000200080240021 0x980100040320033b 0xf300200080640067

def z229 : W := mkw 0x00c60c5000000000 0x0018c18a00000000 0xf3cf3cfcc0000001 0xfe79e79f98000000

def z230 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0x75f6c0003c3f8006 0x2ebed8000787f000

def z231 : W := mkw 0x053950003bfb0007 0x80a72a00077f6000 0xf1f800003fff8006 0x1e3f000007fff000

def z232 : W := mkw 0x21efbedec161855a 0x843df7dbd82c30ab 0xd9cb349cc3e38fff 0xfb396693987c71ff

def z233 : W := mkw 0xc211412d2f3eff3b 0x78422825a5e7dfe7 0xbe35cb673f3fff3f 0xf7c6b96ce7e7ffe7

def z234 : W := mkw 0x0000002000041020 0x2000000400008204 0x22040860201c7000 0x0440810c04038e00

def z235 : W := mkw 0x01ee0ed000000000 0x003dc1da00000000 0xf3fe0ff800000001 0xfe7fc1ff00000000

def z236 : W := mkw 0x00400ed280000000 0x000801da50000000 0x00000498c0000000 0x0000009318000000

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x80093084c0000000 0x9001261098000000

def z238 : W := mkw 0x2129b286c161014a 0x84253650d82c2029 0x8439f387c3c003c0 0x90873e70f8780078

def z239 : W := mkw 0x0010010022002200 0x0002002004400440 0xf8380f8023c07fc6 0xdf0701f004780ff8

def z240 : W := mkw 0x4139412533ac332f 0x28272824a6758665 0xfffdcb673ffc733f 0xffffb96ce7ff8e67

def z241 : W := mkw 0x83eeaefa8404dc30 0x707dd5df50809b86 0xffffffffc0007c39 0xfffffffff8000f87

def z242 : W := mkw 0x4011412d232cb73b 0x28022825a46596e7 0xfe37cf7f233fff3f 0xffc6f9efe467ffe7

def z243 : W := mkw 0x87fffefabfffdc37 0xf0ffffdf57fffb86 0xfffffffffffffc3f 0xffffffffffffff87

def z244 : W := mkw 0x83eeaef28c165820 0x707dd5de5182cb04 0xf7fffffffc1c7001 0xfeffffffff838e00

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00b300000000000 0x3a01660000000000

def z246 : W := mkw 0x6011512d636db77b 0xac022a25ac6db6ef 0xbe35cb6723ffffff 0xf7c6b96ce47fffff

def z247 : W := mkw 0x41feeff3a20c3221 0x283fddfe74418644 0xf7ffffffe01c7001 0xfefffffffc038e00

def z248 : W := mkw 0x2011110c6361a75a 0x840222218c6c34eb 0xf83b3f9ce3e3ffff 0xff0767f39c7c7fff

def z249 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x0800049cc3e38fff 0xc1000093987c71ff

def z250 : W := mkw 0x40400ff780043328 0x280801fef0008665 0x0a000fffc0007339 0xc14001fff8000e67

def z251 : W := mkw 0x2087100c4973855a 0x8410e201892e70ab 0xf9cf349cffff8fff 0xff39e6939ffff1ff

def z252 : W := mkw 0x0579ff8037e96a87 0xc0af3ff006fd2d50 0xfdf9ff803fc07fc6 0xdfbf3ff007f80ff8

def z253 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x79f00f003c007c06 0x4f3e01e007800f80

def z254 : W := mkw 0x40104121220c3221 0x2802082424418644 0xbe34cb63231c7302 0xd7c6996c64638e60

def z255 : W := mkw 0x2087b05ec161855a 0x8410f60bd82c30ab 0x0607f07fc0238039 0x20c0fe0ff8047007

def z256 : W := mkw 0x2539f00473e9014f 0x84a73e008e7d2029 0x8439f084c3c003c0 0x90873e1098780078

def z257 : W := mkw 0x01aea00000000000 0x0035d40000000000 0x25f4c00000000000 0x04be980000000000

def z258 : W := mkw 0x2000100840418450 0x840002010808308a 0x0000000000c38cc4 0x0000000000187198

def z259 : W := mkw 0x40104121220c3221 0x2802082424418644 0x3e34cb63203c703b 0x67c6996c64078e07

def z260 : W := mkw 0x2539f00c73e9855f 0x84a73e018e7d30ab 0xdc3bf49cc3e38fff 0xfb877e93987c71ff

def z261 : W := mkw 0xa2411c7c4565dd7a 0xf448238f88acbbaf 0xda0b3cfcc3e3ffff 0xfb41679f987c7fff

def z262 : W := mkw 0x0138000032800004 0x0027000006500000 0x21f000003c000000 0x043e000007800000

def z263 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x23c608783c3ff039 0x2478c10f0787fe07

def z264 : W := mkw 0x25bff00c7bfb855f 0x84b7fe018f7f70ab 0xf5fff01cffff803f 0x3ebffe039ffff007

def z265 : W := mkw 0x001140042328010b 0x0002280084650021 0xbc35c004233c033b 0xf786b80084678067

def z266 : W := mkw 0x0010010036806a84 0x4002002006d00d50 0xd80804803fc07fc6 0xdb01009007f80ff8

def z267 : W := mkw 0x05febf803ed36a84 0xc0bfd7f007da6d50 0xf9fa3f803fc3ffc6 0xdf3f47f007f87ff8

def z268 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x61f80f803cc07cc4 0x0c3f01f007980f98

def z269 : W := mkw 0x83fe0ff03e967aa4 0x707fc1fe07d2cf54 0xfbfc0fe03fdc7fc6 0xdf7f81fc07fb8ff8

def z270 : W := mkw 0x0497f0002b7b0003 0x8092fe00056f6000 0xb437f000233f8002 0x3686fe000467f000

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x8431c30700000000 0x90863860e0000000

def z272 : W := mkw 0x01680e8000000000 0x002d01d000000000 0xf1f80f8000000000 0xde3f01f000000000

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x71c000003c000006 0x0e38000007800000

def z274 : W := mkw 0x4139438533a8238f 0x08272870a6750471 0x8439c38703c003c0 0x90873870e0780078

def z275 : W := mkw 0x04015000097b0003 0x80802a00012f6000 0x00000000003f8000 0x000000000007f000

def z276 : W := mkw 0x0000100000410000 0x8000020000082000 0x400a300000c38004 0x0801460000187000

def z277 : W := mkw 0x6001112d4165b77a 0xac002225a82cb6ef 0xda0b3fffc3e3ffff 0xfb4167fff87c7fff

def z278 : W := mkw 0x87fffc783fffdc37 0xf0ffff8f07fffb86 0xfffffc783ffffc3f 0x7fffff8f07ffff87

def z279 : W := mkw 0x01feafd2b6806a84 0x403fd5fa56d00d50 0x27f4cb633c007000 0x04fe996c67800e00

def z280 : W := mkw 0x0001400001280003 0x0000280000250000 0x0405c000003c0000 0x2080b80000078000

def z281 : W := mkw 0x01680e8014804884 0x402d01d002900910 0xf1f80f801cc00cc4 0xde3f01f003980198

def z282 : W := mkw 0x01680e8014804884 0x402d01d002900910 0x79c80c803cc07cc6 0x4f39019007980f98

def z283 : W := mkw 0x0000005280000000 0x0000000a50000000 0x0200007fc0000001 0x0040000ff8000000

def z284 : W := mkw 0x05aff00019fb0007 0x80b5fe00033f6000 0x45cff0001cff8004 0x28b9fe00039ff000

def z285 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf1f80b003fc07006 0x1e3f016007f80e00

def z286 : W := mkw 0x40014025012c112b 0x28002804a0258225 0xb635cb67003c0039 0xf6c6b96ce0078007

def z287 : W := mkw 0x82c60c7808169430 0x3058c18f0102d286 0x73c60c78003f8039 0x6e78c18f0007f007

def z288 : W := mkw 0x40d74d75232c332b 0x281ae9aea4658665 0xfff7cf7f233c733b 0xfffef9efe4678e67

def z289 : W := mkw 0xa201102c4d77dd7a 0xf440220589aefbaf 0xd80b349cffffffff 0xfb0166939fffffff

def z290 : W := mkw 0x01680ed280000000 0x002d01da50000000 0xf3f80fffc0000001 0xde7f01fff8000000

def z291 : W := mkw 0x441151253bff332f 0xa8822a24a77fe665 0xbe35cb673ffff33f 0xf7c6b96ce7fffe67

def z292 : W := mkw 0xa2c71c7c4d77dd7a 0xf458e38f89aefbaf 0x7bc60c783fffffff 0x6f78c18f07ffffff

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x30040000203c0002 0x2600800004078000

def z294 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x3a040c78203c7c3b 0x6740818f04078f87

def z295 : W := mkw 0x00500d0026006a00 0x400a01a004c00d40 0xf9f00f003f007f06 0xdf3e01e007e00fe0

def z296 : W := mkw 0x20400f8c4400efd8 0x440801f188801dfb 0x08000f9cc0007ff9 0xc10001f398000fff

def z297 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7fccfe300000000 0xdeff99fc60000000

def z298 : W := mkw 0x41794f8537a86b8f 0x482f29f0a6f50d71 0xfdf9cf873fc07fc6 0xdfbf39f0e7f80ff8

def z299 : W := mkw 0x00114020232c1023 0x2002280404658204 0xbe35c860233c703b 0x77c6b90c04678e07

def z300 : W := mkw 0x0128000010800004 0x0025000002100000 0x41c800001cc00004 0x0839000003980000

def z301 : W := mkw 0x0138038032802284 0x0027007006500450 0x0030030000000000 0x0006006000000000

def z302 : W := mkw 0x401141052328230b 0x08022820a4650461 0x0000000003000300 0x0000000000600060

def z303 : W := mkw 0x01780e8036804884 0x402f01d006d00910 0xf1f804803fc00cc6 0x1e3f009007f80198

def z304 : W := mkw 0x00c60c5008120000 0x0018c18a01024000 0x73c60c783c3f8007 0x6e78c18f0787f000

def z305 : W := mkw 0x83fe0ff83e96feb4 0x707fc1ff07d2dfd6 0x7bf60f783c3ffc3f 0x6f7ec1ef0787ff87

def z306 : W := mkw 0x820000280c16dc30 0x704000050182db86 0x580204183c3ffc3f 0x6b0040830787ff87

def z307 : W := mkw 0x2000000c40008558 0x04000001880010ab 0x0800000000000ff8 0x01000000000001ff

def z308 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x2bc408603c3ffc3e 0x0578810c0787ff87

def z309 : W := mkw 0x01aea05280000000 0x0035d40a50000000 0xf7fff07fc0000001 0x3efffe0ff8000000

def z310 : W := mkw 0x0001100001610002 0x80002200002c2000 0x0003300000238000 0x2000660000047000

def z311 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x43ca3fffc0000001 0xc87947fff8000000

def z312 : W := mkw 0x0000000008120000 0x0000000001024000 0x000000003c3f8006 0x000000000787f000

def z313 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0x65fef0003cdf8004 0x0cbfde00079bf000

def z314 : W := mkw 0x0086000008120000 0x0010c00001024000 0x21c400003c1c0000 0x0438800007838000

def z315 : W := mkw 0x82c60c700c165820 0x7058c18e0182cb04 0x73c608603c3ff006 0x2e78c10c0787fe00

def z316 : W := mkw 0x00400c5000000000 0x0008018a00000000 0x02000c7800000001 0x4040018f00000000

def z317 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd808048003e38ffe 0xdb010090007c71ff

def z318 : W := mkw 0x2000100840418450 0x840002010808308a 0xd00b349cc0c38cc5 0xfa01669398187198

def z319 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe3dcfe723fc7fff 0xffc7b9fce47f8fff

def z320 : W := mkw 0x820000080c12cc10 0x5040000101825982 0x000000001c038c04 0x0000000003807180

def z321 : W := mkw 0x6011412d632cb77b 0x2c022825ac6596ef 0xbe35cfffe33c7ffb 0xf7c6b9fffc678fff

def z322 : W := mkw 0x01eeaed294804884 0x403dd5da52900910 0x41ca3498dcc00cc4 0x083946931b980198

def z323 : W := mkw 0x2000100840418450 0x840002010808308a 0x00023018c0038000 0x0000460318007000

def z324 : W := mkw 0x20c71c5c4161855a 0x8418e38b882c30ab 0xfbcf3cfcc3e38fff 0xff79e79f987c71ff

def z325 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x67fefffbc0000000 0x0cffdfff78000000

def z326 : W := mkw 0x00c6aed280000000 0x0018d5da50000000 0x0607ffffc0000001 0xe0c0fffff8000000

def z327 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x0a060c78003ffc39 0x6140c18f0007ff87

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000049cc0000001 0xc000009398000000

def z329 : W := mkw 0x2411500c7bfb855f 0x84822a018f7f70ab 0xd80b349cffff8fff 0xfb0166939ffff1ff

def z330 : W := mkw 0x4139e387a328230b 0x08273c70f4650461 0x8439f387c3000300 0x90873e70f8600060

def z331 : W := mkw 0x01aea28280000000 0x0035d45050000000 0xf5fff387c0000000 0xbebffe70f8000000

def z332 : W := mkw 0x6011512d636db77b 0xac022a25ac6db6ef 0x0800000023fffffe 0x01000000047fffff

def z333 : W := mkw 0x40014025012c112b 0x28002804a0258225 0x3e05c867203c703b 0x67c0b90ce4078e07

def z334 : W := mkw 0x01afb00001610002 0x8035f600002c2000 0xf5fff00003e38006 0x3ebffe00007c7000

def z335 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xfe3fffffc3e38fff 0xffc7fffff87c71ff

def z336 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfff7cf7f3c3ffc3f 0xfffef9efe787ff87

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x5002041800000001 0x6a00408300000000

def z338 : W := mkw 0x41784fa1368c7aa5 0x682f09f426d18f54 0xfffccfe33fdc7fc6 0xdfff99fc67fb8ff8

def z339 : W := mkw 0x01eeafd284006a80 0x403dd5fa50800d50 0xffffffffc0007fc1 0xfffffffff8000ff8

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x9001000400000001 0xf200200080000000

def z341 : W := mkw 0x8286007808169430 0x3050c00f0102d286 0x73c600783c3f803f 0x2e78c00f0787f007

def z342 : W := mkw 0x05bff1003bfb2207 0x80b7fe20077f6440 0xfdfffb003ffff306 0xffbfff6007fffe60

def z343 : W := mkw 0x05bff3803bfb2287 0x80b7fe70077f6450 0xf5fff3803fff83c6 0xbebffe7007fff078

def z344 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd80b300003e38ffe 0x3b016600007c71ff

def z345 : W := mkw 0x01780f8022002200 0x002f01f004400440 0xf9f80f8023007302 0xdf3f01f004600e60

def z346 : W := mkw 0x0086a00000000000 0x0010d40000000000 0x0407f00000000000 0x2080fe0000000000

def z347 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0xf5fcc0003fdc0006 0x1ebf980007fb8000

def z348 : W := mkw 0xa2c60c7c4c16dd78 0x7458c18f8982dbaf 0x7bc60cfcfc3fffff 0xef78c19f9f87ffff

def z349 : W := mkw 0x0000000000000000 0x0000000000000000 0xd008048000000000 0xda01009000000000

def z350 : W := mkw 0x0010010032802284 0x0002002006500450 0x0000000003c003c0 0x0000000000780078

def z351 : W := mkw 0x01794f8037a86a87 0x402f29f006f50d50 0xfdfdcf803ffc7fc6 0xffbfb9f007ff8ff8

def z352 : W := mkw 0x6011510d6369a75b 0x8c022a21ac6d34eb 0xdc3bf79fc3e38fff 0xfb877ef3f87c71ff

def z353 : W := mkw 0x21afb00c4161855a 0x8435f601882c30ab 0xfdfff49cc3e38fff 0xffbffe93987c71ff

def z354 : W := mkw 0x83eeaeda8c12cc10 0x507dd5db51825982 0x41ca3498dc038c04 0x083946931b807180

def z355 : W := mkw 0x01780f8032802284 0x002f01f006500450 0xf1f80f8003c003c0 0xde3f01f000780078

def z356 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xfffdcfe73fc07fc7 0xffffb9fce7f80ff8

def z357 : W := mkw 0x40400fa504047ba8 0x680801f4a0808f75 0x0a000fe700007ff9 0xc14001fce0000fff

def z358 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x2e34cb63233c733a 0x05c6996c64678e67

def z359 : W := mkw 0x45bfe1253bbe332f 0x28b7fc24a777c665 0xbff5cb673f3c733b 0xf7feb96ce7e78e67

def z360 : W := mkw 0x0086000000000000 0x0010c00000000000 0x71c6000000000000 0x2e38c00000000000

def z361 : W := mkw 0xc297417d2b3eb73b 0x3852e82fa567d6e7 0xbe37cb7f233ff33b 0xf7c6f96fe467fe67

def z362 : W := mkw 0x0487f052897b0003 0x8090fe0a512f6000 0x0607f07fc03f8001 0x20c0fe0ff807f000

def z363 : W := mkw 0x2000000c40008558 0x04000001880010ab 0xd80b349cc0000ff9 0xfb016693980001ff

def z364 : W := mkw 0x83780fa83e96feb4 0x706f01f507d2dfd6 0xf9f80f803ffffffe 0xdf3f01f007ffffff

def z365 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x29f00f803c007fc0 0xc53e01f007800ff8

def z366 : W := mkw 0x45bee1213a9e3225 0x28b7dc242753c644 0x27f4cb633c1c7000 0x04fe996c67838e00

def z367 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x843ff00003ff8000 0x3087fe00007ff000

def z368 : W := mkw 0x0539f00033e90007 0x80a73e00067d2000 0xd43bf00003e38006 0x3a877e00007c7000

def z369 : W := mkw 0x0539f00033e90007 0x80a73e00067d2000 0xf5f9f0003fc00006 0x1ebf3e0007f80000

def z370 : W := mkw 0x82c60c500c124800 0x5058c18a01824900 0x01c000001c000000 0x0038000003800000

def z371 : W := mkw 0x0128a28280000000 0x0025145050000000 0x00083080c0000000 0x0001061018000000

def z372 : W := mkw 0x40004021000c1021 0x2800080420018204 0x0604c063001c0000 0x00c0980c60038000

def z373 : W := mkw 0x40014025012c112b 0x28002804a0258225 0x9e05c067033c033b 0xf3c0b80ce0678067

def z374 : W := mkw 0x20411edec161855a 0x840823dbd82c30ab 0xda0b3fffc3e38fff 0xfb4167fff87c71ff

def z375 : W := mkw 0x413943a533ac33af 0x28272874a6758675 0xbe3dcbe723fc73fb 0xf7c7b97ce47f8e7f

def z376 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9fb3f9cffc07fc7 0xff3f67f39ff80ff8

def z377 : W := mkw 0x01fe0f803e926a84 0x403fc1f007d24d50 0xf9fe0f803fffffc6 0xff3fc1f007fffff8

def z378 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xb9f00b003f007302 0xd73e016007e00e60

def z379 : W := mkw 0x828600780c16dc30 0x7050c00f0182db86 0x0a0600783c3ffc3f 0x2140c00f0787ff87

def z380 : W := mkw 0x00400fd284006a80 0x400801fa50800d50 0x0a000fffc0007fc1 0xc14001fff8000ff8

def z381 : W := mkw 0xc2c74c7d0d3edd3b 0x7858e98fa1a7dba7 0x7fc7cc7f3c3ffc3f 0x6ff8f98fe787ff87

def z382 : W := mkw 0x87bff0783bff9437 0xb0f7fe0f077ff286 0xf7fff0783fff803f 0x3efffe0f07fff007

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000003c00fc6 0x01000000007801f8

def z384 : W := mkw 0x01aea2d280000000 0x0035d45a50000000 0x863ff3ffc0000001 0xb0c7fe7ff8000000

def z385 : W := mkw 0x000100040120010a 0x0000200080240021 0x0001000400200039 0x2000200080040007

def z386 : W := mkw 0x01feafd2b2802284 0x003fd5fa56500450 0xf7ffffffc3c003c1 0xfefffffff8780078

def z387 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xa7fdfbe7c0000000 0x94ffbf7cf8000000

def z388 : W := mkw 0x01680e8000000000 0x002d01d000000000 0xf1fb3f9cc0000001 0xfe3f67f398000000

def z389 : W := mkw 0x82400c780c16dc30 0x7048018f0182db86 0x0a000c783c3ffc3f 0x4140018f0787ff87

def z390 : W := mkw 0x0011400023280003 0x0002280004650000 0xb635cb67233c0003 0xf6c6b96ce4678000

def z391 : W := mkw 0x0086000008120000 0x0010c00001024000 0x00060000003f8000 0x2000c0000007f000

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x400a3498c0000000 0x0801469318000000

def z393 : W := mkw 0x01eeaef280041020 0x203dd5de50008204 0xffffffffe03c703b 0xfffffffffc078e07

def z394 : W := mkw 0x4011412537ac7baf 0x68022824a6f58f75 0xbe35cb673ffc7fff 0xf7c6b96ce7ff8fff

def z395 : W := mkw 0xa2c71c7c4d77dd7a 0xf458e38f89aefbaf 0x7bc73c7cfc3ffc3f 0x6f78e78f9f87ff87

def z396 : W := mkw 0x0138010036806a84 0x4027002006d00d50 0xf9f800003fc07fc6 0x1f3f000007f80ff8

def z397 : W := mkw 0x82c60efa8c16dc30 0x7058c1df5182db86 0x7bc60ffffc3ffc3f 0xef78c1ffff87ff87

def z398 : W := mkw 0x21eebedac0418450 0x843dd7db5808308a 0x41ca3498c0c38cc4 0x0839469318187198

def z399 : W := mkw 0x82c60c580c12cc10 0x5058c18b01825982 0x73c60c781c038c05 0x6e78c18f03807180

def z400 : W := mkw 0x01791f8037e16a86 0xc02f23f006fc2d50 0xf9fb3f803fe3ffc6 0xff3f67f007fc7ff8

def z401 : W := mkw 0x4539f10533e9230f 0x88a73e20a67d2461 0x8439f30703c00300 0x90873e60e0780060

def z402 : W := mkw 0xc2514d7d272cff3b 0x784a29afa4e59fe7 0xbe35cf7f233c7f3b 0xf7c6b9efe4678fe7

def z403 : W := mkw 0x05fffc503bfb0007 0x80bfff8a077f6000 0xf7fffc783fff8007 0x7effff8f07fff000

def z404 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xa1f80b803fc073c0 0x943f017007f80e78

def z405 : W := mkw 0xa201102c4d77dd7a 0xf440220589aefbaf 0x080000003ffffffe 0x0100000007ffffff

def z406 : W := mkw 0x000100040120010a 0x0000200080240021 0x080000000320033a 0x0100000000640067

def z407 : W := mkw 0x41ffefd7a328230b 0x083ffdfaf4650461 0xf7ffffffc3000301 0xfefffffff8600060

def z408 : W := mkw 0x0000010004006a80 0x4000002000800d50 0x0800000000007fc0 0x0100000000000ff8

def z409 : W := mkw 0x8286007808169430 0x3050c00f0102d286 0x5a060478003f8c3f 0x6b40c08f0007f187

def z410 : W := mkw 0x2000100c40418558 0x84000201880830ab 0x480a349cc0c38ffd 0xc9014693981871ff

def z411 : W := mkw 0x82d74c782f3edc33 0x705ae98f05e7db86 0xfff7cc783f3ffc3f 0x7ffef98f07e7ff87

def z412 : W := mkw 0x25fffedefbfb855f 0x84bfffdbdf7f70ab 0xffffffffffff8fff 0xfffffffffffff1ff

def z413 : W := mkw 0x4000012500043328 0x28000024a0008665 0xbe35cb6700007339 0xf7c6b96ce0000e67

def z414 : W := mkw 0x2129b28ec161855a 0x84253651d82c30ab 0xdc3bf79fc3e38fff 0xfb877ef3f87c71ff

def z415 : W := mkw 0x0538e00032880005 0x00a71c0006510000 0x0430c00000000000 0x0086180000000000

def z416 : W := mkw 0x21eeaedec0008558 0x043dd5dbd80010ab 0xffffffffc0000ff9 0xfffffffff80001ff

def z417 : W := mkw 0x21781f8876c1eed4 0xc42f03f10ed83dda 0xf9fa3f98ffc3ffc6 0xdf3f47f31ff87ff8

def z418 : W := mkw 0x25bff00c7bfb855f 0x84b7fe018f7f70ab 0xfdfff0003fff8ffe 0x3fbffe0007fff1ff

def z419 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0x0604c06300000000 0x00c0980c60000000

def z420 : W := mkw 0x0128a28280000000 0x0025145050000000 0x0430c30300000000 0x0086186060000000

def z421 : W := mkw 0x25bff0087bfb8457 0x84b7fe010f7f708a 0xf5fff498ffff8cc6 0x3ebffe931ffff198

def z422 : W := mkw 0xc3ffefffaf3eff3b 0x787ffdfff5e7dfe7 0xffffffffff3fff3f 0xffffffffffe7ffe7

def z423 : W := mkw 0x01ffeed2a3280003 0x003ffdda54650000 0xf7ffffffe33c0003 0xfefffffffc678000

def z424 : W := mkw 0x409741252b3e332b 0x2812e824a567c665 0xfff7cb673f3ff33f 0xfffef96ce7e7fe67

def z425 : W := mkw 0x05bff0203bff1027 0xa0b7fe04077fe204 0xfffff8603ffff03f 0x7fffff0c07fffe07

def z426 : W := mkw 0x820000280c16dc30 0x704000050182db86 0x3a0408603c3ffc3f 0x6740810c0787ff87

def z427 : W := mkw 0x6001502d416d957b 0xac002a05a82db2af 0x0607f07fc03f8039 0x20c0fe0ff807f007

def z428 : W := mkw 0x0000038000002280 0x0000007000000450 0x00000380000003c0 0x8000007000000078

def z429 : W := mkw 0x0000002000041020 0x2000000400008204 0x02040060003c0039 0x2040800c00078007

def z430 : W := mkw 0x01680e8014804884 0x402d01d002900910 0xd9c804801fc00fc6 0xdb39009003f801f8

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0x0605c06700000001 0x20c0b80ce0000000

def z432 : W := mkw 0x05eebe801cd34884 0xc0bdd7d0039a6910 0x41ca34801cc38cc4 0x0839469003987198

def z433 : W := mkw 0x00400c0004004800 0x4008018000800900 0x21c008003c007000 0x0438010007800e00

def z434 : W := mkw 0x00c60c7000041020 0x2018c18e00008204 0x7bc60c78203c703b 0x6f78c18f04078e07

def z435 : W := mkw 0x4139e3a7a32c332b 0x28273c74f4658665 0xbe3dfbe7e33c733b 0xf7c7bf7cfc678e67

def z436 : W := mkw 0x4000012100043220 0x2800002420008644 0x02000b6300007000 0x0040016c60000e00

def z437 : W := mkw 0x400101250124332a 0x28002024a0248665 0x9a010b670320733b 0xf340216ce0640e67

def z438 : W := mkw 0xc7fffd7d3fffff3f 0xf8ffffafa7ffffe7 0xffffff7f3fffff3f 0xffffffefe7ffffe7

def z439 : W := mkw 0x00c60c5000000000 0x0018c18a00000000 0xf7f7cf7f00000001 0xfefef9efe0000000

def z440 : W := mkw 0x01680e8000000000 0x002d01d000000000 0xf7fdcfe700000001 0xfeffb9fce0000000

def z441 : W := mkw 0x0010010036806a84 0x4002002006d00d50 0xb8300b003fc07fc6 0xd706016007f80ff8

def z442 : W := mkw 0x0000002000041020 0x2000000400008204 0x08000000203c703a 0x0100000004078e07

def z443 : W := mkw 0x82400c7004045820 0x7048018e00808b04 0x0200086000007000 0x0040010c00000e00

def z444 : W := mkw 0x0011410023282203 0x0002282004650440 0xbc35cb00233c7302 0xf786b96004678e60

def z445 : W := mkw 0x86d75c783fffdc37 0xf0daeb8f07fffb86 0x7bc60c783ffffc3f 0x6f78c18f07ffff87

def z446 : W := mkw 0x01aea00008120000 0x0035d40001024000 0xf5fff0003c3f8006 0x3ebffe000787f000

def z447 : W := mkw 0x21780f8c7680efdc 0x442f01f18ed01dfb 0xf9f80f9cffc07fff 0xdf3f01f39ff80fff

def z448 : W := mkw 0x000100240124112a 0x2000200480248225 0xba050864233c733b 0xf740a10c84678e67

def z449 : W := mkw 0x01780fd2b6806a84 0x402f01fa56d00d50 0xfbf80fffffc07fc7 0xdf7f01fffff80ff8

def z450 : W := mkw 0x041150003bfb0007 0x80822a00077f6000 0xd00b30003fff8006 0x3a01660007fff000

def z451 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0xd60ff4ffc0000001 0xfac1fe9ff8000000

def z452 : W := mkw 0x05fffc003ffb4807 0xc0bfff8007ff6900 0xfdfffc003ffffc06 0x7fbfff8007ffff80

def z453 : W := mkw 0x00c60c5800008410 0x0018c18b00001082 0x7bc60c7800238c3f 0x6f78c18f00047187

def z454 : W := mkw 0x4000012500043328 0x28000024a0008665 0x3a040b67203c733b 0xe740816ce4078e67

def z455 : W := mkw 0xc2d74d7d2f3eff3b 0x785ae9afa5e7dfe7 0x7bc60c783f3fff3f 0x6f78c18f07e7ffe7

def z456 : W := mkw 0x01fe0fd036806a84 0x403fc1fa06d00d50 0xfbfe0ff83fc07fc7 0xff7fc1ff07f80ff8

def z457 : W := mkw 0x87feec783e9edc35 0x70ffdd8f07d3db86 0x7ff6cc783c3ffc3f 0x6ffed98f0787ff87

def z458 : W := mkw 0x00400f8004006a80 0x400801f000800d50 0x00000b0000007000 0x0000016000000e00

def z459 : W := mkw 0x821001283e96feb4 0x7042002507d2dfd6 0x080000003ffffffe 0x0100000007ffffff

def z460 : W := mkw 0x0000000800008410 0x0000000100001082 0x0800000000238c3e 0x0100000000047187

def z461 : W := mkw 0x45bff1253bff332f 0xa8b7fe24a77fe665 0xfdfff0003ffff33e 0x3fbffe0007fffe67

def z462 : W := mkw 0x05eebed298d30004 0x80bdd7da531a6000 0x41ca3498dcc38004 0x083946931b987000

def z463 : W := mkw 0xc287407d093e953b 0x3850e80fa127d2a7 0x0607c07f003f8039 0x20c0f80fe007f007

def z464 : W := mkw 0x05fffe803ffb4887 0xc0bfffd007ff6910 0xf5fff4803fff8cc6 0x3ebffe9007fff198

def z465 : W := mkw 0x05beb0003ad30004 0x80b7d600075a6000 0xf1fa30003fc38006 0x1e3f460007f87000

def z466 : W := mkw 0x0000000800008410 0x0000000100001082 0xd80a049803e38fff 0xfb014093007c71ff

def z467 : W := mkw 0x00400e8004004880 0x400801d000800910 0x0000048000000cc0 0x0000009000000198

def z468 : W := mkw 0x82c60c700c165820 0x7058c18e0182cb04 0x3bc408603c3c703b 0x6778810c07878e07

def z469 : W := mkw 0x009740002b3a0003 0x0012e80005674000 0xf5f7c0003f3f8006 0x3ebef80007e7f000

def z470 : W := mkw 0x200110044161014a 0x84002200882c2029 0x98093084c3e003fb 0xf3012610987c007f

def z471 : W := mkw 0x01eeaeda80008410 0x003dd5db50001082 0xffffffffc0238c3f 0xfffffffff8047187

def z472 : W := mkw 0x0128000000000000 0x0025000000000000 0xf1f8000000000000 0x1e3f000000000000

def z473 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x43c604781c3f8c3d 0x2878c08f0387f187

def z474 : W := mkw 0x820000280404dc30 0x7040000500809b86 0x0800000000007c38 0x0100000000000f87

def z475 : W := mkw 0x041040003a9a0005 0x0082080007534000 0x000000003c1c0000 0x0000000007838000

def z476 : W := mkw 0x25aeb00858d38454 0x84b5d6010b1a708a 0x41ca3498dcc38cc4 0x083946931b987198

def z477 : W := mkw 0x25afb00c59f3855e 0x84b5f6018b3e70ab 0xd9cb349cdfe38fff 0xfb3966939bfc71ff

def z478 : W := mkw 0x05aea00018920004 0x00b5d40003124000 0x01c000001c000000 0x0038000003800000

def z479 : W := mkw 0x8687f078097f9433 0xb0d0fe0f012ff286 0x0607f078003f8039 0x20c0fe0f0007f007

def z480 : W := mkw 0x82400ff80404feb0 0x704801ff00809fd6 0x0a000ff800007ff9 0xc14001ff00000fff

def z481 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf7fffb673fff8007 0xfeffff6ce7fff000

def z482 : W := mkw 0x2139138473e123ce 0x842722708e7c2479 0x80393384c3c003c0 0x9007267098780078

def z483 : W := mkw 0x00c60c5000000000 0x0018c18a00000000 0x41c2041800000000 0x0838408300000000

def z484 : W := mkw 0x000110040161010a 0x80002200802c2021 0xd80b300403e3833f 0xfb016600807c7067

def z485 : W := mkw 0x41780fa536847bac 0x682f01f4a6d08f75 0xfbf80fe73fc07fff 0xdf7f01fce7f80fff

def z486 : W := mkw 0x01790f8437a06b8e 0x402f21f086f40d71 0xf9f90f843fe07fff 0xff3f21f087fc0fff

def z487 : W := mkw 0x0138038032802284 0x0027007006500450 0xb8380b8023c073c2 0xd707017004780e78

def z488 : W := mkw 0x0539f00033e90007 0x80a73e00067d2000 0xb43df00023fc0002 0x3687be00047f8000

def z489 : W := mkw 0x0001100801618412 0x80002201002c3082 0xd80b341803e38c3f 0x7b016683007c7187

def z490 : W := mkw 0x0000002800049430 0x2000000500009286 0x7a060c78203ffc3f 0x6f40c18f0407ff87

def z491 : W := mkw 0x05aff000097b0003 0x80b5fe00012f6000 0xf5fff000003f8000 0x3ebffe000007f000

def z492 : W := mkw 0x2487f00c497b855b 0x8490fe01892f70ab 0xdc0ff49cc3ff8fff 0xfb81fe93987ff1ff

def z493 : W := mkw 0x21efbedec161855a 0x843df7dbd82c30ab 0xf7ffffffc0238039 0xfefffffff8047007

def z494 : W := mkw 0x4010012522043328 0x28020024a4408665 0xba300b672300733b 0xd746016ce4600e67

def z495 : W := mkw 0xa3ff1ffc7ff7fffe 0xf47fe3ff8ffeffff 0xfbff3ffcffffffff 0xff7fe7ff9fffffff

def z496 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbcf3cfcfc3ffc3f 0xff79e79f9f87ff87

def z497 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x5802041803e38fff 0x6b004083007c71ff

def z498 : W := mkw 0x0138038032802284 0x0027007006500450 0xd838078003c00fc6 0xdb0700f0007801f8

def z499 : W := mkw 0x87fffc583ffbcc17 0xd0ffff8b07ff7982 0xf5fff4183fff8c06 0x3ebffe8307fff180

def z500 : W := mkw 0x05fffe803bfb0007 0x80bfffd0077f6000 0xf5ffff803fff8006 0xfebffff007fff000

def z501 : W := mkw 0x0010010022002200 0x0002002004400440 0x20300b0020007000 0x0406016004000e00

def z502 : W := mkw 0x000100040120010a 0x0000200080240021 0x8001000403000300 0x9000200080600060

def z503 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x0000000000238038 0x0000000000047007

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x3204086000000001 0x6640810c00000000

def z505 : W := mkw 0xc2d64d792e1efe31 0x785ac9af25c3dfc6 0x7ff6cf7b3c3ffc3f 0x6ffed9ef6787ff87

def z506 : W := mkw 0x45bff0253bff112f 0xa8b7fe04a77fe225 0xf7fff0673fff803f 0x3efffe0ce7fff007

def z507 : W := mkw 0x40104121220c3221 0x2802082424418644 0xb635cb67201c7001 0xf6c6b96ce4038e00

def z508 : W := mkw 0x05fffed2bbfb0007 0x80bfffda577f6000 0xf5fff498ffff8006 0x3ebffe931ffff000

def z509 : W := mkw 0x65bff12d7bffb77f 0xacb7fe25af7ff6ef 0xffffffffffffffff 0xffffffffffffffff

def z510 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x88380f8003c07fc0 0xd10701f000780ff8

def z511 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xd1cb349cc0000001 0xfa39669398000000

def z512 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0300b0000000000 0xd606016000000000

def z513 : W := mkw 0x0010000032800004 0x0002000006500000 0x000000003fc00006 0x0000000007f80000

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800080020007002 0x4700010004000e00

def z515 : W := mkw 0x05eebed298d30004 0x80bdd7da531a6000 0xf7ffffffdcc38005 0xfefffffffb987000

def z516 : W := mkw 0x041151003ffb6a87 0xc0822a2007ff6d50 0x080000003fffffc6 0x0100000007fffff8

def z517 : W := mkw 0x40514d25272c7b2b 0x680a29a4a4e58f65 0xfff5cf673f3c7f3f 0xfffeb9ece7e78fe7

def z518 : W := mkw 0x01780e8032800004 0x002f01d006500000 0xf1f80f803fc00006 0xde3f01f007f80000

def z519 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7fffb6300000000 0x3effff6c60000000

def z520 : W := mkw 0x01eeaed284004800 0x403dd5da50800900 0xfffffffffc007c07 0xffffffffff800f80

def z521 : W := mkw 0x0011400023280003 0x0002280004650000 0x8431c00003000000 0x1086380000600000

def z522 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf5fff498c0000000 0x3ebffe9318000000

def z523 : W := mkw 0x87eebc581cd3cc14 0xd0fdd78b039a7982 0x41ca34181cc38c04 0x0839468303987180

def z524 : W := mkw 0x4010410122082201 0x0802082024410440 0x0430c30300000000 0x0086186060000000

def z525 : W := mkw 0x401141052328230b 0x08022820a4650461 0x9c31c3070320033b 0xf3863860e0640067

def z526 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0xf5fff0003c1c0000 0x3ebffe0007838000

def z527 : W := mkw 0x2000000c40008558 0x04000001880010ab 0x5802049cc0238fff 0xeb004093980471ff

def z528 : W := mkw 0x21791f8477e16bce 0xc42f23f08efc2d79 0xf9f93f84ffc07fc6 0xdf3f27f09ff80ff8

def z529 : W := mkw 0x0010000022000000 0x0002000004400000 0xb030000023000002 0x1606000004600000

def z530 : W := mkw 0x0411500033e90007 0x80822a00067d2000 0x0000000003c00000 0x0000000000780000

def z531 : W := mkw 0x82c71c780d77dc32 0xf058e38f01aefb86 0xfbcf3c783ffffc3f 0x7f79e78f07ffff87

def z532 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xc5fbf79fc0000000 0x98bf7ef3f8000000

def z533 : W := mkw 0x83eeaefa8c16dc30 0x707dd5df5182db86 0x7ff6cf7b3c3ffc3f 0x6ffed9ef6787ff87

def z534 : W := mkw 0x0010010036806a84 0x4002002006d00d50 0x000000003c007000 0x0000000007800e00

def z535 : W := mkw 0x21681e8854c1ccd4 0xc42d03d10a98399a 0x41ca3498dcc38cc4 0x083946931b987198

def z536 : W := mkw 0x21691e8c55e1cdde 0xc42d23d18abc39bb 0xd9cb349cdfe38fff 0xfb3966939bfc71ff

def z537 : W := mkw 0x01efbed281610002 0x803df7da502c2000 0xf7ffffffc3e38007 0xfefffffff87c7000

def z538 : W := mkw 0x2000000840008450 0x040000010800108a 0x00000498c0000cc0 0x0000009318000198

def z539 : W := mkw 0x01780fa036847aa4 0x602f01f406d08f54 0xfbfc0fe03ffc7fff 0xff7f81fc07ff8fff

def z540 : W := mkw 0x05ffffd2bffb6a87 0xc0bffffa57ff6d50 0xffffffffffffffc7 0xfffffffffffffff8

def z541 : W := mkw 0x40014025012c112b 0x28002804a0258225 0x00000000003c0038 0x0000000000078007

def z542 : W := mkw 0x01feafd2b6806a84 0x403fd5fa56d00d50 0xf7fffffffc007001 0xfeffffffff800e00

def z543 : W := mkw 0x4087e077812c112b 0x2810fc0ef0258225 0x0607f07fc03c0039 0x20c0fe0ff8078007

def z544 : W := mkw 0x05fffed2b3e90007 0x80bfffda567d2000 0xf7ffffffc3c00001 0xfefffffff8780000

def z545 : W := mkw 0x00400c2004045820 0x6008018400808b04 0x7bc40c603c3c7c3f 0x6f78818c07878f87

def z546 : W := mkw 0x00400f8004006a80 0x400801f000800d50 0x79c00f803c007fc6 0xcf3801f007800ff8

def z547 : W := mkw 0x83eeac780c16dc30 0x707dd58f0182db86 0xfffffc783c3ffc3f 0x7fffff8f0787ff87

def z548 : W := mkw 0x41ffeff7a32c332b 0x283ffdfef4658665 0xbff5cb67233c733b 0xf7feb96ce4678e67

def z549 : W := mkw 0x01bfe00023280003 0x0037fc0004650000 0xf5fff000233c0002 0x3ebffe0004678000

def z550 : W := mkw 0x0138038036806a84 0x4027007006d00d50 0x883803803fc07fc6 0x9107007007f80ff8

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008048000c00cc4 0x0801009000180198

def z552 : W := mkw 0x41feeff3a20c3221 0x283fddfe74418644 0x27f4cb63201c7000 0x04fe996c64038e00

def z553 : W := mkw 0x4487f025097f112b 0xa890fe04a12fe225 0x0607f067003f8039 0x20c0fe0ce007f007

def z554 : W := mkw 0x00400c0000000000 0x0008018000000000 0x71c00c0000000000 0x4e38018000000000

def z555 : W := mkw 0x861150283fffdc37 0xf0c22a0507fffb86 0x080000003ffffc3e 0x0100000007ffff87

def z556 : W := mkw 0x0138000032800004 0x0027000006500000 0x8038000003c00000 0x1007000000780000

def z557 : W := mkw 0x01aea00000000000 0x0035d40000000000 0x41ca300000000000 0x0839460000000000

def z558 : W := mkw 0x40514ff7a32c332b 0x280a29fef4658665 0xbe35cfffe33c733b 0xf7c6b9fffc678e67

def z559 : W := mkw 0x01eeac5000000000 0x003dd58a00000000 0xf7fffc7800000001 0x7effff8f00000000

def z560 : W := mkw 0x05bfe0003bba0007 0x00b7fc0007774000 0xb5f5c0003f3c0002 0x36beb80007e78000

def z561 : W := mkw 0x0000000800008410 0x0000000100001082 0x4002041800038c04 0x0800408300007180

def z562 : W := mkw 0x40114025232c112b 0x28022804a4658225 0xb635c067233c003b 0x36c6b80ce4678007

def z563 : W := mkw 0x01680e8000000000 0x002d01d000000000 0xf9f80f8003c00fc6 0xdf3f01f0007801f8

def z564 : W := mkw 0x01aea00000000000 0x0035d40000000000 0xf7fffb6700000001 0xfeffff6ce0000000

def z565 : W := mkw 0x82c60c780404dc30 0x7058c18f00809b86 0x7bc60c7800007c39 0x6f78c18f00000f87

def z566 : W := mkw 0x01feafd2b6806a84 0x403fd5fa56d00d50 0xf9fa3f98ffc07fc6 0xdf3f47f31ff80ff8

def z567 : W := mkw 0x82c60c580c12cc10 0x5058c18b01825982 0x71c604183c3f8c06 0x2e38c0830787f180

def z568 : W := mkw 0x00c60c5004004800 0x4018c18a00800900 0x7bc60c783c007c07 0x6f78c18f07800f80

def z569 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd00b349cc0238039 0xfa01669398047007

def z570 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x88093084c3e38ffe 0x91012610987c71ff

def z571 : W := mkw 0x01aea00000000000 0x0035d40000000000 0xf5fff49cc0000001 0xfebffe9398000000

def z572 : W := mkw 0x01680f8014806a84 0x402d01f002900d50 0x49c80f801cc07fc4 0xc93901f003980ff8

def z573 : W := mkw 0x0011500023690003 0x80022a00046d2000 0xf43ff00023ff8006 0x3e87fe00047ff000

def z574 : W := mkw 0xc211412d2f3eff3b 0x78422825a5e7dfe7 0x080000003f3fff3e 0x0100000007e7ffe7

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0xd008000003c00006 0x1a01000000780000

def z576 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x9801000403e38fff 0xf3002000807c71ff

def z577 : W := mkw 0x86c7fc780d7fdc33 0xf0d8ff8f01affb86 0x7fc7fc783c3ffc3f 0x6ff8ff8f0787ff87

def z578 : W := mkw 0x401141052328230b 0x08022820a4650461 0xb435c307233c0302 0xb686b860e4678060

def z579 : W := mkw 0x83feaffabe96feb4 0x707fd5ff57d2dfd6 0xffffffffffffffff 0xffffffffffffffff

def z580 : W := mkw 0x0000000004004800 0x4000000000800900 0x080000003c007c06 0x0100000007800f80

def z581 : W := mkw 0x83eeaefa8c16dc30 0x707dd5df5182db86 0x7bce3cf8fc3ffc3f 0x6f79c79f1f87ff87

def z582 : W := mkw 0x21691e8c4161855a 0x842d23d1882c30ab 0xf9fb3f9cc3e38fff 0xff3f67f3987c71ff

def z583 : W := mkw 0x0086000808128410 0x0010c00101025082 0x79c604183c3f8c3f 0x6f38c0830787f187

def z584 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x63c60c783c1ffc04 0x0c78c18f0783ff80

def z585 : W := mkw 0x01680f8004006a80 0x402d01f000800d50 0xf9f80f8000007fc0 0xdf3f01f000000ff8

def z586 : W := mkw 0x2001100841618452 0x84002201082c308a 0xd00b3498c3e38cc6 0x3a016693187c7198

def z587 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xc1f807801fc00fc4 0x983f00f003f801f8

def z588 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xb8300b00233c733a 0xd706016004678e67

def z589 : W := mkw 0x87eebc781cd7dc34 0xf0fdd78f039afb86 0x7bce3c783cfffc3f 0x6f79c78f079fff87

def z590 : W := mkw 0x41794fa537ac7baf 0x682f29f4a6f58f75 0xbff5cb673f3c733b 0xf7feb96ce7e78e67

def z591 : W := mkw 0x83ee0ed81c92cc94 0x507dc1db03925992 0x41ca04981cc38cc4 0x0839409303987198

def z592 : W := mkw 0x83fe0c783e96dc34 0x707fc18f07d2db86 0xfbfe0c783ffffc3f 0x7f7fc18f07ffff87

def z593 : W := mkw 0x87fffc703fff5827 0xf0ffff8e07ffeb04 0xf7fff8603ffff006 0x3effff0c07fffe00

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0xd80b349cc3c00fc7 0xfb016693987801f8

def z595 : W := mkw 0x05795f803ffb6a87 0xc0af2bf007ff6d50 0xf9f80f803fffffc6 0xdf3f01f007fffff8

def z596 : W := mkw 0x0000000800008410 0x0000000100001082 0x0800041800000c39 0x4100008300000187

def z597 : W := mkw 0x2487f00c497b855b 0x8490fe01892f70ab 0x0407f01cc03f8039 0x2080fe039807f007

def z598 : W := mkw 0x0528b00010c10004 0x80a5160002182000 0x0008300000c00000 0x0001060000180000

def z599 : W := mkw 0x83fe0ff03e967aa4 0x707fc1fe07d2cf54 0x23f40b603c1c7000 0x047e816c07838e00

def z600 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbc35c000233c733a 0x3786b80004678e67

def z601 : W := mkw 0x2011110c77e1efde 0xc40222218efc3dfb 0x080000003fe3fffe 0x0100000007fc7fff

def z602 : W := mkw 0x400140050128010b 0x08002800a0250021 0x0401c00700000000 0x00803800e0000000

def z603 : W := mkw 0x20411f8c4561efda 0xc40823f188ac3dfb 0xd80b3f9cc3e3ffff 0xfb0167f3987c7fff

def z604 : W := mkw 0x41efeef7812c112b 0x283dfddef0258225 0xf7ffffffc03c0039 0xfefffffff8078007

def z605 : W := mkw 0x0400100018d30004 0x80800200031a6000 0x000000001cc38004 0x0000000003987000

def z606 : W := mkw 0x82d60d783e96feb4 0x705ac1af07d2dfd6 0x7bc60c783fffffff 0x6f78c18f07ffffff

def z607 : W := mkw 0x00400c0004004800 0x4008018000800900 0x41c004001c000c04 0x0838008003800180

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0x2634cb6300000000 0x04c6996c60000000

def z609 : W := mkw 0x000100040120010a 0x0000200080240021 0xd80b349cc320033b 0xfb01669398640067

def z610 : W := mkw 0x0086005000000000 0x0010c00a00000000 0x0206007800000001 0x2040c00f00000000

def z611 : W := mkw 0x05afb00019f30006 0x80b5f600033e6000 0xd1cb30001fe38006 0x3a39660003fc7000

def z612 : W := mkw 0x01780f883680ee94 0x402f01f106d01dd2 0xf9fa0f983fe3ffff 0xff3f41f307fc7fff

def z613 : W := mkw 0x00500f8036806a84 0x400a01f006d00d50 0x08000f803fc07fc6 0xc10001f007f80ff8

def z614 : W := mkw 0x0000002000041020 0x2000000400008204 0x0a00086000007039 0x4140010c00000e07

def z615 : W := mkw 0x0128a28280000000 0x0025145050000000 0xd43bf79fc0000001 0xfa877ef3f8000000

def z616 : W := mkw 0x05feeed2ba9a0005 0x00bfddda57534000 0x27f4cb633c1c0000 0x04fe996c67838000

def z617 : W := mkw 0x0011400023280003 0x0002280004650000 0x00000000233c0002 0x0000000004678000

def z618 : W := mkw 0x2000000c40008558 0x04000001880010ab 0xd808049cc3c00fff 0xdb010093987801ff

def z619 : W := mkw 0x82d60d782e16fe30 0x705ac1af05c2dfc6 0xfbf60f783f3fff3f 0xff7ec1ef07e7ffe7

def z620 : W := mkw 0x0000000400000108 0x0000000080000021 0x0800000400000339 0xc100000080000067

def z621 : W := mkw 0x0138010032802204 0x0027002006500440 0xf9f80b003fc07306 0xdf3f016007f80e60

def z622 : W := mkw 0x00c60ed280000000 0x0018c1da50000000 0x73c60fffc0000001 0xee78c1fff8000000

def z623 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x0803349cc0238ff9 0xe1006693980471ff

def z624 : W := mkw 0x4000002500041128 0x28000004a0008225 0x0200006700000039 0x0040000ce0000007

def z625 : W := mkw 0x01feafd2b6806a84 0x403fd5fa56d00d50 0xfffccfe33fc07fc6 0xdfff99fc67f80ff8

def z626 : W := mkw 0x0128028000000000 0x0025005000000000 0x8038038000000000 0x9007007000000000

def z627 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x7bc00c783c007c3f 0x4f78018f07800f87

def z628 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x9803301cc323833b 0xf300660398647067

def z629 : W := mkw 0x25ffff8c7ffbefdf 0xc4bffff18fff7dfb 0xfdffff9cffffffff 0xffbffff39fffffff

def z630 : W := mkw 0xa287107c4977957a 0xb450e20f892ef2af 0xda0f34fcc3ff8fff 0xfb41e69f987ff1ff

def z631 : W := mkw 0x0001100001610002 0x80002200002c2000 0x0000000003e38006 0x00000000007c7000

def z632 : W := mkw 0x0539f0003bfb0007 0x80a73e00077f6000 0x8439f0003fff8006 0x10873e0007fff000

def z633 : W := mkw 0x00500f8026006a80 0x400a01f004c00d50 0xb8300f8023007fc2 0xd70601f004600ff8

def z634 : W := mkw 0x0138a382b2802284 0x0027147056500450 0x8439f387c3c003c0 0x90873e70f8780078

def z635 : W := mkw 0x0000028280000000 0x0000005050000000 0x00000387c0000000 0x80000070f8000000

def z636 : W := mkw 0x0138000032800004 0x0027000006500000 0xf9f804803fc00fc6 0xdf3f009007f801f8

def z637 : W := mkw 0x401141052328230b 0x08022820a4650461 0xbc31cb0723007302 0xd7863960e4600e60

def z638 : W := mkw 0x40014125012c332b 0x28002824a0258665 0x0e05cb67003c7339 0xe1c0b96ce0078e67

def z639 : W := mkw 0x2000000c40008558 0x04000001880010ab 0x0000001cc0000039 0x0000000398000007

def z640 : W := mkw 0x83fe0fd83e92ee94 0x507fc1fb07d25dd2 0xf9fa0f983fc3ffc6 0xdf3f41f307f87ff8

def z641 : W := mkw 0x6001502d416d957b 0xac002a05a82db2af 0xde0ff4ffc3ff8fff 0xfbc1fe9ff87ff1ff

def z642 : W := mkw 0xa7fffc7c7fffdd7f 0xf4ffff8f8ffffbaf 0xfffffcfcffffffff 0xffffff9f9fffffff

def z643 : W := mkw 0x82c60c580c12cc10 0x5058c18b01825982 0x59c204181c238c3f 0x6b38408303847187

def z644 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x47cff4ffc0000001 0x28f9fe9ff8000000

def z645 : W := mkw 0xc3ff4ffd3fbeffbf 0x787fe9ffa7f7dff7 0xffffcfff3fffffff 0xfffff9ffe7ffffff

def z646 : W := mkw 0x00c6ac5280000000 0x0018d58a50000000 0x77c7fc7fc0000001 0x6ef8ff8ff8000000

def z647 : W := mkw 0x200110044161014a 0x84002200882c2029 0x0000000003c003c0 0x0000000000780078

def z648 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x8c31c307233c733a 0x91863860e4678e67

def z649 : W := mkw 0x6000012d4004b778 0x2c000025a80096ef 0x0a000fffc0007ff9 0xc14001fff8000fff

def z650 : W := mkw 0x2139100c73e1855e 0x842722018e7c30ab 0xf9fb349cffe38fff 0xff3f66939ffc71ff

def z651 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x27f4cfffc0000001 0xc4fe99fff8000000

def z652 : W := mkw 0x05bff0083bfb8417 0x80b7fe01077f7082 0xfdfff4183fff8c3f 0x7fbffe8307fff187

def z653 : W := mkw 0x00400ed280000000 0x000801da50000000 0x02000b6300000000 0x0040016c60000000

def z654 : W := mkw 0x01680e8000000000 0x002d01d000000000 0x41c8048000000000 0x0839009000000000

def z655 : W := mkw 0x0000a00280000000 0x0000140050000000 0x0401f007c0000000 0x00803e00f8000000

def z656 : W := mkw 0x4000012500043328 0x28000024a0008665 0x0800000000007338 0x0100000000000e67

def z657 : W := mkw 0x05fffed2bbfb0007 0x80bfffda577f6000 0xf7fffb633fff8006 0x3effff6c67fff000

def z658 : W := mkw 0x00c60c5000000000 0x0018c18a00000000 0x23c4086000000000 0x0478810c00000000

def z659 : W := mkw 0x05effed2897b0003 0x80bdffda512f6000 0xf7ffffffc03f8001 0xfefffffff807f000

def z660 : W := mkw 0x0000000800008410 0x0000000100001082 0xd80b349cc0238c3f 0xfb01669398047187

def z661 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x4bc20c781c03fc3d 0x4978418f03807f87

def z662 : W := mkw 0x2139138c73e1a7de 0x842722718e7c34fb 0xd83b379cc3e38fff 0xfb0766f3987c71ff

def z663 : W := mkw 0x82c70c7c0d36dd3a 0x7058e18f81a6dba7 0xfbc70c7c3f3fff3f 0xff78e18f87e7ffe7

def z664 : W := mkw 0x87fffff83ffffeb7 0xf0ffffff07ffffd6 0xfffffff83fffffff 0xffffffff07ffffff

def z665 : W := mkw 0x40514fa5272c7bab 0x680a29f4a4e58f75 0xbe35cfe7233c7ffb 0xf7c6b9fce4678fff

def z666 : W := mkw 0x820000200c165820 0x704000040182cb04 0x000000003c1c7000 0x0000000007838e00

def z667 : W := mkw 0x041150003bfb0007 0x80822a00077f6000 0xb435c0003fff8006 0x3686b80007fff000

def z668 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x3a040860233c733b 0x6740810c04678e67

def z669 : W := mkw 0x01780c0036804804 0x402f018006d00900 0xf9f80c003fc07c06 0x5f3f018007f80f80

def z670 : W := mkw 0x41794fa5232c332b 0x282f29f4a4658665 0xfffdcfe7233c733b 0xffffb9fce4678e67

def z671 : W := mkw 0x21791f8c77e1efde 0xc42f23f18efc3dfb 0xf9f80f803fe3fffe 0xdf3f01f007fc7fff

def z672 : W := mkw 0x4539f12533ed332f 0xa8a73e24a67da665 0xbe3dfb6723fc733b 0xf7c7bf6ce47f8e67

def z673 : W := mkw 0x0001100001610002 0x80002200002c2000 0xd80b348003e38fc6 0xfb016690007c71f8

def z674 : W := mkw 0x83eeaefa88169430 0x307dd5df5102d286 0xf7ffffffc03f8039 0xfefffffff807f007

def z675 : W := mkw 0x05feeed2ba9a0005 0x00bfddda57534000 0xf7fffffffc1c0001 0xfeffffffff838000

def z676 : W := mkw 0x2011110c77e1efde 0xc40222218efc3dfb 0xd80b349cffe3ffff 0xfb0166939ffc7fff

def z677 : W := mkw 0x4011412537ac7baf 0x68022824a6f58f75 0x080000003ffc7ffe 0x0100000007ff8fff

def z678 : W := mkw 0x2000000440000148 0x0400000088000029 0x00000084c00003c0 0x8000001098000078

def z679 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd00b301cc3e3803f 0x3a016603987c7007

def z680 : W := mkw 0x0487f000097b0003 0x8090fe00012f6000 0xd40ff00003ff8006 0x3a81fe00007ff000

def z681 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x01c0000000000000 0x0038000000000000

def z682 : W := mkw 0x01efaed68120010a 0x003df5dad0240021 0xffffffffc320033b 0xfffffffff8640067

def z683 : W := mkw 0x401141052328230b 0x08022820a4650461 0xb635cb6703000301 0xf6c6b96ce0600060

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x5800040000000c06 0x4b00008000000180

def z685 : W := mkw 0x61ffffffe36db77b 0xac3ffffffc6db6ef 0xffffffffe3ffffff 0xfffffffffc7fffff

def z686 : W := mkw 0x0010400022080001 0x0002080004410000 0x2434c000201c0000 0x0486980004038000

def z687 : W := mkw 0x00400e8000000000 0x000801d000000000 0x00000f8000000000 0xc00001f000000000

def z688 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x8635c367033c0339 0xb0c6b86ce0678067

def z689 : W := mkw 0x0497f0003bfb0007 0x8092fe00077f6000 0x0407f0003fff8006 0x2080fe0007fff000

def z690 : W := mkw 0x0001100001610002 0x80002200002c2000 0x8009300003c00000 0x1001260000780000

def z691 : W := mkw 0x05feef803e9a6a85 0x40bfddf007d34d50 0xfdfccf803fdc7fc6 0xdfbf99f007fb8ff8

def z692 : W := mkw 0xe2d75d7d6f7fff7b 0xfc5aebafadefffef 0xffffffffffffffff 0xffffffffffffffff

def z693 : W := mkw 0x200110044161014a 0x84002200882c2029 0xd00b349cc3c003c1 0xfa01669398780078

def z694 : W := mkw 0x20400edec0008558 0x040801dbd80010ab 0x0a000fffc0000ff9 0xc14001fff80001ff

def z695 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf1f80f803c007000 0xde3f01f007800e00

def z696 : W := mkw 0x001101042320230a 0x0002202084640461 0xb8310b042320733b 0xf706216084640e67

def z697 : W := mkw 0x2411500c7bfb855f 0x84822a018f7f70ab 0x080000003fff8ffe 0x0100000007fff1ff

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000020003b 0x6300000000040007

def z699 : W := mkw 0x200110044161014a 0x84002200882c2029 0xd8093484c3c00fc6 0xdb012690987801f8

def z700 : W := mkw 0x601151056369234b 0x8c022a20ac6d2469 0x8439f387c3c003c0 0x90873e70f8780078

def z701 : W := mkw 0x21efbed6c161014a 0x843df7dad82c2029 0xf7ffffffc3c003c1 0xfefffffff8780078

def z702 : W := mkw 0x4000010500002308 0x08000020a0000461 0x0000030700000300 0x80000060e0000060

def z703 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xc5fbf0001fc38004 0x18bf7e0003f87000

def z704 : W := mkw 0x05feef803e9a6a85 0x40bfddf007d34d50 0x25f4cb003c1c7000 0x04be996007838e00

def z705 : W := mkw 0x0486e000081a0001 0x0090dc0001034000 0x0404c000001c0000 0x0080980000038000

def z706 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x800b309cc3e383f9 0xb0016613987c707f

def z707 : W := mkw 0x40104121220c3221 0x2802082424418644 0xbe34cb63233c733b 0xf7c6996c64678e67

def z708 : W := mkw 0x01aea2d280000000 0x0035d45a50000000 0x0637f37fc0000001 0x20c6fe6ff8000000

def z709 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf7fff0673fff8007 0x3efffe0ce7fff000

def z710 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe35cb6723fc7fff 0xf7c6b96ce47f8fff

def z711 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff0003fff8306 0xffbffe0007fff060

def z712 : W := mkw 0x8368aefa8404dc30 0x706d15df50809b86 0x8e39ffffc0007c39 0xd1c73ffff8000f87

def z713 : W := mkw 0xc2d74d5d2f3aef1b 0x585ae9aba5e75de3 0xc5f3c71f1f038f04 0x98be78e3e3e071e0

def z714 : W := mkw 0x2000100c40418558 0x84000201880830ab 0xd80a349cc3c38fff 0xdb014693987871ff

def z715 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x59c204183c3ffc3f 0x6b3840830787ff87

def z716 : W := mkw 0x41694ea515ac59af 0x682d29d4a2b58b35 0x47cdc4e71cfc0cfd 0x28f9b89ce39f819f

def z717 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0a000cfcc0007c39 0xc140019f98000f87

def z718 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7ffffffc0238007 0xfefffffff8047000

def z719 : W := mkw 0x25bee00c7a9a855d 0x04b7dc018f5350ab 0x2df4c49cfc1c0ff9 0xc5be98939f8381ff

def z720 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0x61ce30003cdf8004 0x0c39c600079bf000

def z721 : W := mkw 0x0096a152b6806a84 0x4012d42a56d00d50 0x0e07f07fffc07fc7 0x21c0fe0ffff80ff8

def z722 : W := mkw 0x05afb00019f30006 0x80b5f600033e6000 0xf1cf30003fff8006 0x3e39e60007fff000

def z723 : W := mkw 0x25bff3847bfb23cf 0x84b7fe708f7f6479 0xf5fff384ffff83c6 0xbebffe709ffff078

def z724 : W := mkw 0x05bff282bbfb0007 0x80b7fe50577f6000 0xf5fff080ffff8006 0x3ebffe101ffff000

def z725 : W := mkw 0x05bff1003bfb2207 0x80b7fe20077f6440 0xfffffb673ffff307 0xffffff6ce7fffe60

def z726 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xb7f7fb7fc0000001 0xf6feff6ff8000000

def z727 : W := mkw 0x40104125220c3329 0x28020824a4418665 0x3e34cb67203c733b 0xe7c6996ce4078e67

def z728 : W := mkw 0x0168aed280000000 0x002d15da50000000 0xd63bffffc0000001 0xfac77ffff8000000

def z729 : W := mkw 0x45aeb12518d7332c 0xa8b5d624a31ae665 0x4bca3b671cc3f33d 0xc979476ce3987e67

def z730 : W := mkw 0x21791f8c77e1efde 0xc42f23f18efc3dfb 0x21f33b1cfc23f039 0x243e67639f847e07

def z731 : W := mkw 0x01afb00009730002 0x8035f600012e6000 0xf5fff0003fff8006 0x3ebffe0007fff000

def z732 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xffffffffe0007003 0xfffffffffc000e00

def z733 : W := mkw 0x0086000008120000 0x0010c00001024000 0x79c608003c3ff006 0x6f38c1000787fe00

def z734 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x2bc40c783c3ffc3f 0x4578818f0787ff87

def z735 : W := mkw 0x00400c0004004800 0x4008018000800900 0x79c00c003fc07fc6 0x4f38018007f80ff8

def z736 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0a000cf800007ff9 0xc140019f00000fff

def z737 : W := mkw 0x01bf10003bf30006 0x8037e200077e6000 0xf1ff30003fff8006 0x3e3fe60007fff000

def z738 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0a000f7f00007c39 0xc14001efe0000f87

def z739 : W := mkw 0x82c60c280c16dc30 0x7058c1850182db86 0x79c60c003c3ffc3e 0x6f38c1800787ff87

def z740 : W := mkw 0x40115125236d332b 0xa8022a24a46da665 0xbe37fb67233ff33b 0xf7c6ff6ce467fe67

def z741 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x3a000c7820007c3b 0x4740018f04000f87

def z742 : W := mkw 0x83be03f83a96b6b4 0x3077c07f0752d6d6 0x823e03f803ff83f9 0xb047c07f007ff07f

def z743 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f804803fc07fc6 0x1f3f009007f80ff8

def z744 : W := mkw 0x05bff3803bfb2287 0x80b7fe70077f6450 0xfdfff7803fff8fc6 0xffbffef007fff1f8

def z745 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xf83b3f9cc3e38fff 0xff0767f3987c71ff

def z746 : W := mkw 0x04c7ff800d7b6a83 0xc098fff001af6d50 0x0c07ff80003fffc0 0xe180fff00007fff8

def z747 : W := mkw 0x0010010036806a84 0x4002002006d00d50 0x79c000003fc07fc6 0x0f38000007f80ff8

def z748 : W := mkw 0x82400c280404dc30 0x7048018500809b86 0x08000c0000007c38 0x4100018000000f87

def z749 : W := mkw 0x00c6ac5280000000 0x0018d58a50000000 0xf7f7ff7fc0000001 0xfefeffeff8000000

def z750 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff0003fff803f 0x7fbffe0007fff007

def z751 : W := mkw 0x82400d780404feb0 0x704801af00809fd6 0x0a000c7800007ff9 0x4140018f00000fff

def z752 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc608603c3ffc3e 0x2f78c10c0787ff87

def z753 : W := mkw 0x41ffeff7a32c332b 0x283ffdfef4658665 0x49ca3498e33c733a 0x093946931c678e67

def z754 : W := mkw 0x40104121220c3221 0x2802082424418644 0x2e34cb63201c7039 0x45c6996c64038e07

def z755 : W := mkw 0xa2c71c744d77596a 0xf458e38e89aeeb2d 0xa3cd38e4ffdc73c0 0x9479a71c9ffb8e78

def z756 : W := mkw 0x820000280c16dc30 0x704000050182db86 0x79c000003c3ffc3e 0x0f3800000787ff87

def z757 : W := mkw 0x60115125636d336b 0xac022a24ac6da66d 0xbe35fb67e33c733b 0xf7c6bf6cfc678e67

def z758 : W := mkw 0x0486b00008530000 0x8090d600010a6000 0x71c630003c3f8006 0x2e38c6000787f000

def z759 : W := mkw 0x40104121220c3221 0x2802082424418644 0x2634cb63203c7039 0x24c6996c64078e07

def z760 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x09c000003c3ffc3e 0x013800000787ff87

def z761 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xfdfff4843fff8fff 0xffbffe9087fff1ff

def z762 : W := mkw 0x409741052b3a230b 0x0812e820a5674461 0xf5f7c3073f3f8306 0xbebef860e7e7f060

def z763 : W := mkw 0x053950003bfb0007 0x80a72a00077f6000 0x41c800003fff8006 0x0839000007fff000

def z764 : W := mkw 0x049640003a9a0005 0x0092c80007534000 0x71c600003c3f8006 0x2e38c0000787f000

def z765 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9fc0f803ffc7fc6 0xff3f81f007ff8ff8

def z766 : W := mkw 0x82c6ac7a8c16dc30 0x7058d58f5182db86 0xfff7ff7ffc3ffc3f 0xfffeffefff87ff87

def z767 : W := mkw 0x82400c280c16dc30 0x704801850182db86 0x49c004003c3ffc3e 0x093800800787ff87

def z768 : W := mkw 0x0086000008120000 0x0010c00001024000 0xf7f7cb673c3f8007 0xfefef96ce787f000

def z769 : W := mkw 0x4000012500043328 0x28000024a0008665 0xbe35cb67203c733b 0xf7c6b96ce4078e67

def z770 : W := mkw 0x8328a2aa8c16dc30 0x706514555182db86 0x8c39f387fc3ffc3e 0x91873e70ff87ff87

def z771 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0x2637fb7fc0000001 0x24c6ff6ff8000000

def z772 : W := mkw 0x01eeaed284004800 0x403dd5da50800900 0xffffffffffc07fc7 0xfffffffffff80ff8

def z773 : W := mkw 0x0086005008120000 0x0010c00a01024000 0x73c600783c3f8007 0x2e78c00f0787f000

def z774 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf1fa30003fff8006 0x1e3f460007fff000

def z775 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x49c80f803fc07fc6 0xc93901f007f80ff8

def z776 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd80b3498c3e38ffe 0x3b016693187c71ff

def z777 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xffffffffc020003b 0xfffffffff8040007

def z778 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0x65f6c0003c1f8004 0x0cbed8000783f000

def z779 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x2bc60c783c3ffc39 0x6578c18f0787ff87

def z780 : W := mkw 0x40104121220c3221 0x2802082424418644 0x2e34cb63203c703a 0x05c6996c64078e07

def z781 : W := mkw 0x05bfe0003bba0007 0x00b7fc0007774000 0xf5f7c0003f3f8006 0x3ebef80007e7f000

def z782 : W := mkw 0x053950003bfb0007 0x80a72a00077f6000 0x21f000003fff8006 0x043e000007fff000

def z783 : W := mkw 0x049750003bfb0007 0x8092ea00077f6000 0x41c200003fff8006 0x0838400007fff000

def z784 : W := mkw 0xa2400c7c4404dd78 0x7448018f88809baf 0x0a000c7cc0007c39 0x4140018f98000f87

def z785 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff084ffff8006 0xbebffe109ffff000

def z786 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0200087800007039 0x0040010f00000e07

def z787 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xc5fff0001fff8004 0x38bffe0003fff000

def z788 : W := mkw 0x0000002000041020 0x2000000400008204 0x3e34cb63203c703b 0x67c6996c64078e07

def z789 : W := mkw 0x05aff00019fb0007 0x80b5fe00033f6000 0xf5fff0001cff8004 0x3ebffe00039ff000

def z790 : W := mkw 0x00c60c080c12cc10 0x4018c18101825982 0x79c60c183c3ffc3f 0x6f38c1830787ff87

def z791 : W := mkw 0x01bea0003a920004 0x0037d40007524000 0xf5fff0003fff8006 0x3ebffe0007fff000

def z792 : W := mkw 0x0000000008120000 0x0000000001024000 0x71c000003c3f8006 0x0e3800000787f000

def z793 : W := mkw 0x01680e8004004800 0x402d01d000800900 0xf9f80f803fc07fc6 0xdf3f01f007f80ff8

def z794 : W := mkw 0x00400c280404dc30 0x6008018500809b86 0x7bc60c783c3ffc3f 0x6f78c18f0787ff87

def z795 : W := mkw 0x208710044973014a 0x8410e200892e6029 0xf1cf3084ffff83c6 0xbe39e6109ffff078

def z796 : W := mkw 0x0086000008120000 0x0010c00001024000 0x73c608603c3f8007 0x6e78c10c0787f000

def z797 : W := mkw 0x01eeaed288120000 0x003dd5da51024000 0xf7ffffffdc038005 0xfefffffffb807000

def z798 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xffffffffc0000fc1 0xfffffffff80001f8

def z799 : W := mkw 0x4411512533ed332f 0xa8822a24a67da665 0xbe35cb6723fc733b 0xf7c6b96ce47f8e67

def z800 : W := mkw 0x40104125220c3329 0x28020824a4418665 0xbe35cb67201c7339 0xf7c6b96ce4038e67

def z801 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xf80f349ce3ff8fff 0xff01e6939c7ff1ff

def z802 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x79c20c183c3ffc3e 0x4f3841830787ff87

def z803 : W := mkw 0x0178afd2b6806a84 0x402f15fa56d00d50 0xfff9ffffffc07fc7 0xdfff3ffffff80ff8

def z804 : W := mkw 0x0086a05288120000 0x0010d40a51024000 0x77c7f07ffc3f8007 0x2ef8fe0fff87f000

def z805 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x67ffffffc0000001 0x2cfffffff8000000

def z806 : W := mkw 0x82400c280c16dc30 0x704801850182db86 0x29c008003c3ffc3e 0x053801000787ff87

def z807 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbf60f783c3ffc3f 0xff7ec1ef0787ff87

def z808 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x2e35cb67203c7339 0xe5c6b96ce4078e67

def z809 : W := mkw 0x82400ff80404feb0 0x704801ff00809fd6 0x0a000f7800007c39 0x414001ef00000f87

def z810 : W := mkw 0x0086000008120000 0x0010c00001024000 0x21c400003c3f8006 0x043880000787f000

def z811 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe35cb63233c733a 0x37c6b96c64678e67

def z812 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0x41ca30003cdf8004 0x08394600079bf000

def z813 : W := mkw 0x0086000008120000 0x0010c00001024000 0x41c200003c3f8006 0x083840000787f000

def z814 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xc9f80f801fc07fc4 0xd93f01f003f80ff8

def z815 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7ffffffc3c003c1 0xfefffffff8780078

def z816 : W := mkw 0x45bff1053bfb230f 0x88b7fe20a77f6461 0xfdfffb073ffff306 0xffbfff60e7fffe60

def z817 : W := mkw 0x25bff0047bfb014f 0x84b7fe008f7f6029 0xf5fff0003fff83c6 0x3ebffe0007fff078

def z818 : W := mkw 0x8779fc7837eddc37 0xf0ef3f8f06fdbb86 0x8e39fc7803c07c39 0x51c73f8f00780f87

def z819 : W := mkw 0x82410c7c0524dd3a 0x7048218f80a49ba7 0x9a010c7c03207f3b 0xf340218f80640fe7

def z820 : W := mkw 0x00500d0036806a84 0x400a01a006d00d50 0x49c004003fc07fc6 0x0938008007f80ff8

def z821 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff4803fff8006 0xfebffe9007fff000

def z822 : W := mkw 0x21efbedec161855a 0x843df7dbd82c30ab 0x2ff4cb6303e38ffe 0x05fe996c607c71ff

def z823 : W := mkw 0x25bff286fbfb014f 0x84b7fe50df7f6029 0xf5fff387ffff83c6 0xbebffe70fffff078

def z824 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x02000c7800007c00 0x0040018f00000f80

def z825 : W := mkw 0x04515ed2bbfb0007 0x808a2bda577f6000 0x02000fffffff8007 0xc04001fffffff000

def z826 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0xda0b3cfcc0007c39 0xfb41679f98000f87

def z827 : W := mkw 0x01eeaed284004800 0x403dd5da50800900 0xf7ffffffdc000c05 0xfefffffffb800180

def z828 : W := mkw 0x82400c7a8404dc30 0x7048018f50809b86 0x0a000c7fc0007c39 0x4140018ff8000f87

def z829 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x8e35cb67033c7339 0xf1c6b96ce0678e67

def z830 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe3fffffe3fc7fff 0xffc7fffffc7f8fff

def z831 : W := mkw 0x40014125012c332b 0x28002824a0258665 0xbe35cb67003c7339 0xf7c6b96ce0078e67

def z832 : W := mkw 0x0486e000081a0001 0x0090dc0001034000 0x75c6c0003c3f8006 0x2eb8d8000787f000

def z833 : W := mkw 0x013800003a920004 0x0027000007524000 0xf1f800003fff8006 0x1e3f000007fff000

def z834 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0x25f6f0003c1f8000 0x04bede000783f000

def z835 : W := mkw 0x01eeaed284004800 0x403dd5da50800900 0xffffffffc0007c01 0xfffffffff8000f80

def z836 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xb635cb67233c703b 0x36c6b96ce4678e07

def z837 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xb5f7f0003f3f8002 0x36befe0007e7f000

def z838 : W := mkw 0x05beb0003ad30004 0x80b7d600075a6000 0xf1fe30003fff8006 0x3e3fc60007fff000

def z839 : W := mkw 0x40115125236d332b 0xa8022a24a46da665 0xfe3fffe723ffffff 0xffc7fffce47fffff

def z840 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff01cffff8007 0x3ebffe039ffff000

def z841 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x29f00f803fc07fc6 0xc53e01f007f80ff8

def z842 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe3dfbe7e33c733b 0xf7c7bf7cfc678e67

def z843 : W := mkw 0x0086a00008120000 0x0010d40001024000 0x75c7f0003c3f8006 0x2eb8fe000787f000

def z844 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0xda080cf803c07fff 0xdb41019f00780fff

def z845 : W := mkw 0x6011512d636db77b 0xac022a25ac6db6ef 0x08000000233ff33a 0x010000000467fe67

def z846 : W := mkw 0x01be03803a922284 0x0037c07007524450 0xf1fe03803fff83c6 0xbe3fc07007fff078

def z847 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x5a020c7800007c39 0x6b40418f00000f87

def z848 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0xf5fff0003c3f8006 0x3ebffe000787f000

def z849 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7fc7cc7f3c3ffc3f 0x6ff8f98fe787ff87

def z850 : W := mkw 0x0486100018d30004 0x8090c200031a6000 0x71c600003cff8006 0x2e38c000079ff000

def z851 : W := mkw 0x05aff00019fb0007 0x80b5fe00033f6000 0x05c7f0001c3f8000 0x20b8fe000387f000

def z852 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbcf3cfcffffffff 0xff79e79f9fffffff

def z853 : W := mkw 0x0138038036806a84 0x4027007006d00d50 0xf9f803803fc07fc6 0x9f3f007007f80ff8

def z854 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0x25f4c0003c3f8006 0x04be98000787f000

def z855 : W := mkw 0x05eeaed298920004 0x00bdd5da53124000 0xf7ffffffdc000001 0xfefffffffb800000

def z856 : W := mkw 0x0128a28280000000 0x0025145050000000 0xf63fffffc0000001 0xfec7fffff8000000

def z857 : W := mkw 0x01680e8014804884 0x402d01d002900910 0xf9c80c803fc07fc6 0xdf39019007f80ff8

def z858 : W := mkw 0x01aea2d280000000 0x0035d45a50000000 0xf7fff3ffc0000001 0xbefffe7ff8000000

def z859 : W := mkw 0x82c60c700c165820 0x7058c18e0182cb04 0x7bc608603c3ff03f 0x6f78c10c0787fe07

def z860 : W := mkw 0x82500d782604fe30 0x704a01af04c09fc6 0xba300f7823007f3b 0xd74601ef04600fe7

def z861 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x3e34cb63233c733b 0x67c6996c64678e67

def z862 : W := mkw 0x6487f02d497f957b 0xac90fe05a92ff2af 0x0607f07fc03f8039 0x20c0fe0ff807f007

def z863 : W := mkw 0x4539f38533e9238f 0x88a73e70a67d2471 0x8439f38703c003c0 0x90873e70e0780078

def z864 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xc5fbf0003fff8006 0x18bf7e0007fff000

def z865 : W := mkw 0x05bff052bbfb0007 0x80b7fe0a577f6000 0xf7fff4ffffff8007 0xfefffe9ffffff000

def z866 : W := mkw 0x01eeaed288120000 0x003dd5da51024000 0xf7ffffffc03f8001 0xfefffffff807f000

def z867 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x63c60c783c3ffc3d 0x2c78c18f0787ff87

def z868 : W := mkw 0x828600280c16dc30 0x7050c0050182db86 0x7bc608603c3ffc3f 0x6f78c10c0787ff87

def z869 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff4183fff8007 0x7ebffe8307fff000

def z870 : W := mkw 0x01bf40003bba0007 0x0037e80007774000 0xf5ffc0003fff8006 0x3ebff80007fff000

def z871 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xc9f807803fc07fc6 0x993f00f007f80ff8

def z872 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfff5cb673f3c733f 0xfffeb96ce7e78e67

def z873 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7ffffffc0c00cc5 0xfefffffff8180198

def z874 : W := mkw 0x60115125636d336b 0xac022a24ac6da66d 0xbe35cb6723fc73fb 0xf7c6b96ce47f8e7f

def z875 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe35cf67233c7f3f 0xffc6b9ece4678fe7

def z876 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xd9c804803fc07fc6 0xdb39009007f80ff8

def z877 : W := mkw 0x01780fd2b6806a84 0x402f01fa56d00d50 0xfbfb3fffffc07fc7 0xff7f67fffff80ff8

def z878 : W := mkw 0x00400f8004006a80 0x400801f000800d50 0xf9c80f803fc07fc6 0xdf3901f007f80ff8

def z879 : W := mkw 0x01eeaed294804884 0x403dd5da52900910 0xf7ffffffdc000001 0xfefffffffb800000

def z880 : W := mkw 0x01aea00008120000 0x0035d40001024000 0x75f6c0003c3f8006 0x2ebed8000787f000

def z881 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x71ce30003fff8006 0x2e39c60007fff000

def z882 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xf9cb349cffe38fff 0xff3966939ffc71ff

def z883 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0800041800007c38 0x0100008300000f87

def z884 : W := mkw 0x2001500c4169855b 0x84002a01882d30ab 0xdc0ff49cc3ff8fff 0xfb81fe93987ff1ff

def z885 : W := mkw 0x01be00003a920004 0x0037c00007524000 0x71f600003c3f8006 0x2e3ec0000787f000

def z886 : W := mkw 0x01eeaed284004880 0x403dd5da50800910 0xf7ffffffc0000cc1 0xfefffffff8000198

def z887 : W := mkw 0x01aea2d280000000 0x0035d45a50000000 0xb63ffbffc0000001 0xf6c7ff7ff8000000

def z888 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f80b003fc07fc6 0x1f3f016007f80ff8

def z889 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x3a040c7800007c39 0x6740818f00000f87

def z890 : W := mkw 0x01eeaed294804884 0x403dd5da52900910 0xfffffffffcc07cc7 0xffffffffff980f98

def z891 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc40c603c3ffc3e 0x4f78818c0787ff87

def z892 : W := mkw 0x05bff002bbfb0007 0x80b7fe00577f6000 0xf5fff007ffff8006 0x3ebffe00fffff000

def z893 : W := mkw 0x0138010036806a84 0x4027002006d00d50 0xf9f804803fc07fc6 0xdf3f009007f80ff8

def z894 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc60cf83c3fffff 0xef78c19f0787ffff

def z895 : W := mkw 0xa287b07ec977957a 0xb450f60fd92ef2af 0x0607f07fc03f8039 0x20c0fe0ff807f007

def z896 : W := mkw 0x00500d0036806a84 0x400a01a006d00d50 0xf9f00f003fc07fc6 0xdf3e01e007f80ff8

def z897 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe3dcb6723fc733f 0xffc7b96ce47f8e67

def z898 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7fffb7fc0000001 0x3effff6ff8000000

def z899 : W := mkw 0x0168aed280000000 0x002d15da50000000 0xf7f9ffffc0000001 0xdeff3ffff8000000

def z900 : W := mkw 0x01680e8000000000 0x002d01d000000000 0xf7ffffffc0000001 0xfefffffff8000000

def z901 : W := mkw 0x05bff1003bfb2207 0x80b7fe20077f6440 0xf5fffb003ffff006 0x3ebfff6007fffe00

def z902 : W := mkw 0x0087100009730002 0x8010e200012e6000 0x71c600003fff8006 0x2e38c00007fff000

def z903 : W := mkw 0x0168aed280000000 0x002d15da50000000 0xb63dffffc0000001 0xf6c7bffff8000000

def z904 : W := mkw 0x05bff0503bfb0007 0x80b7fe0a077f6000 0xf7fff0783fff8007 0x3efffe0f07fff000

def z905 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xa7fdffffc0000001 0xd4ffbffff8000000

def z906 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe34cb63233c733a 0xd7c6996c64678e67

def z907 : W := mkw 0x0010012022043220 0x2002002404408644 0xbe35cb67233c733b 0xf7c6b96ce4678e67

def z908 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fcc0003fff8006 0x1ebf980007fff000

def z909 : W := mkw 0x45bff0053bfb010f 0x88b7fe00a77f6021 0xf5fff0073fff8006 0x3ebffe00e7fff000

def z910 : W := mkw 0x053950003bfb0007 0x80a72a00077f6000 0xf5fdc0003fff8006 0x3ebfb80007fff000

def z911 : W := mkw 0x0086002008161020 0x2010c0040102c204 0x79c600003c3ff03e 0x2f38c0000787fe07

def z912 : W := mkw 0x0487f000097b0003 0x8090fe00012f6000 0x25c7f0003c3f8000 0x24b8fe000787f000

def z913 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9fb3f803fc07fc6 0xff3f67f007f80ff8

def z914 : W := mkw 0x009600002a120000 0x0012c00005424000 0xf1f600003f3f8006 0x3e3ec00007e7f000

def z915 : W := mkw 0x87eebeda9cd3cc14 0xd0fdd7db539a7982 0x41ca3498dcc38c04 0x083946931b987180

def z916 : W := mkw 0x05bff282bbfb0007 0x80b7fe50577f6000 0xf7fffbe7ffff8007 0xfeffff7cfffff000

def z917 : W := mkw 0x82400c280c16dc30 0x704801850182db86 0x79c20c183c3ffc3f 0x6f3841830787ff87

def z918 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0xf5fff0003cff8006 0x3ebffe00079ff000

def z919 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe37cb67233ff33f 0xffc6f96ce467fe67

def z920 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fffb003fff8006 0xfebfff6007fff000

def z921 : W := mkw 0x05bff382bbfb2287 0x80b7fe70577f6450 0xf5fff387ffff83c6 0xbebffe70fffff078

def z922 : W := mkw 0x60400fad4404fff8 0x6c0801f5a8809fff 0x0a000fffc0007ff9 0xc14001fff8000fff

def z923 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xc80b349cc3e38ffe 0x99016693987c71ff

def z924 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xc7fbffffc0000001 0xd8ff7ffff8000000

def z925 : W := mkw 0x83eeaed28c124800 0x507dd5da51824900 0xf7ffffffdc000001 0xfefffffffb800000

def z926 : W := mkw 0x45bff1013bfb2207 0x88b7fe20277f6440 0xf5fff3033fff8006 0x3ebffe6067fff000

def z927 : W := mkw 0x053950003bfb0007 0x80a72a00077f6000 0xf1fb30003fff8006 0x3e3f660007fff000

def z928 : W := mkw 0x82c6ac7a8c16dc30 0x7058d58f5182db86 0xffcffcfffc3ffc3f 0xfff9ff9fff87ff87

def z929 : W := mkw 0xa2c60c784c16dc70 0x7458c18f0982db8e 0x7bc60cf8fc3ffcff 0x6f78c19f1f87ff9f

def z930 : W := mkw 0x65bff1057bfb234f 0x8cb7fe20af7f6469 0xf5fff387ffff83c6 0xbebffe70fffff078

def z931 : W := mkw 0x049750003bfb0007 0x8092ea00077f6000 0x21c400003fff8006 0x0438800007fff000

def z932 : W := mkw 0x0497f0003bfb0007 0x8092fe00077f6000 0x75c7f0003fff8006 0x2eb8fe0007fff000

def z933 : W := mkw 0x05bff052bbfb0007 0x80b7fe0a577f6000 0xf5fff018ffff8006 0x3ebffe031ffff000

def z934 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xfbf80fe73fc07fc7 0xdf7f01fce7f80ff8

def z935 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x880b349cc3e38ff9 0xf1016693987c71ff

def z936 : W := mkw 0x04875000097b0003 0x8090ea00012f6000 0x71c600003c3f8006 0x2e38c0000787f000

def z937 : W := mkw 0x01eeaed290800084 0x003dd5da52100010 0xf7ffffffc0c000c1 0xfefffffff8180018

def z938 : W := mkw 0x0086000008120000 0x0010c00001024000 0xf1cf30003c3f8006 0x3e39e6000787f000

def z939 : W := mkw 0x01aea00008120000 0x0035d40001024000 0x71ce30003c3f8006 0x2e39c6000787f000

def z940 : W := mkw 0x05aff00019fb0007 0x80b5fe00033f6000 0x41ca30001cff8004 0x08394600039ff000

def z941 : W := mkw 0x009740002b3a0003 0x0012e80005674000 0x71c600003f3f8006 0x2e38c00007e7f000

def z942 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf7fffb633fff8006 0x3effff6c67fff000

def z943 : W := mkw 0x0087000009320002 0x0010e00001264000 0xf1c700003f3f8006 0x3e38e00007e7f000

def z944 : W := mkw 0x0178af82b6806a84 0x402f15f056d00d50 0xfffdffe7ffc07fc7 0xffffbffcfff80ff8

def z945 : W := mkw 0x82c60ef80c16dcb0 0x7058c1df0182db96 0x7bc60cf83c3ffcff 0x6f78c19f0787ff9f

def z946 : W := mkw 0x01780d0036806a84 0x402f01a006d00d50 0xf9f80c003fc07fc6 0x5f3f018007f80ff8

def z947 : W := mkw 0x40115125236d332b 0xa8022a24a46da665 0xbe35cb6723fff33f 0xf7c6b96ce47ffe67

def z948 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe35cfe7233c7ffb 0xf7c6b9fce4678fff

def z949 : W := mkw 0x0086000008120000 0x0010c00001024000 0x61c600003c1f8004 0x0c38c0000783f000

def z950 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x2634cb63203c7038 0x04c6996c64078e07

def z951 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x73c608783c3ff03f 0x2e78c10f0787fe07

def z952 : W := mkw 0xc2400fff8404ff38 0x784801fff0809fe7 0x0a000fffc0007f39 0xc14001fff8000fe7

def z953 : W := mkw 0xc2400d790404fe30 0x784801af20809fc6 0x0a000f7b00007c39 0x414001ef60000f87

def z954 : W := mkw 0x82c60c7a8c16dc30 0x7058c18f5182db86 0x7bc60c7ffc3ffc3f 0x6f78c18fff87ff87

def z955 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x75f7f0003c3f8006 0x2ebefe000787f000

def z956 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff498ffff8006 0x3ebffe931ffff000

def z957 : W := mkw 0x05bff052bbfb0007 0x80b7fe0a577f6000 0xf7fff0633fff8006 0x3efffe0c67fff000

def z958 : W := mkw 0x0086100008530000 0x8010c200010a6000 0x71ce30003cff8006 0x2e39c600079ff000

def z959 : W := mkw 0x82400ef80404dc30 0x704801df00809b86 0x0a000ff800007c39 0xc14001ff00000f87

def z960 : W := mkw 0x40014025012c112b 0x28002804a0258225 0xbe35cb67203c703b 0xf7c6b96ce4078e07

def z961 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7fffffffc000007 0xfeffffffff800000

def z962 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe3dcbe723fc73fb 0xf7c7b97ce47f8e7f

def z963 : W := mkw 0x01780c0036804804 0x402f018006d00900 0xf9f80c803fc07fc6 0xdf3f019007f80ff8

def z964 : W := mkw 0x0138010036806a84 0x4027002006d00d50 0x49c800003fc07fc6 0x0939000007f80ff8

def z965 : W := mkw 0x01680f8014806a84 0x402d01f002900d50 0xd9c80f801fc07fc6 0xdb3901f003f80ff8

def z966 : W := mkw 0x00400ed280000000 0x000801da50000000 0xf63fffffc0000001 0xfec7fffff8000000

def z967 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x45cff0003fff8006 0x28b9fe0007fff000

def z968 : W := mkw 0x83780ff83684feb4 0x706f01ff06d09fd6 0x8a380ff803c07ff9 0xd14701ff00780fff

def z969 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbc60c783f3fff3f 0xff78c18f07e7ffe7

def z970 : W := mkw 0x05aff00019fb0007 0x80b5fe00033f6000 0x75cff0003cff8006 0x2eb9fe00079ff000

def z971 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xc80b349cc3c38ffd 0xd9016693987871ff

def z972 : W := mkw 0x40104121220c3221 0x2802082424418644 0xbe35cb67203c703b 0xf7c6b96ce4078e07

def z973 : W := mkw 0x82c6aefa8c16dc30 0x7058d5df5182db86 0x7fc7fffffc3ffc3f 0xeff8ffffff87ff87

def z974 : W := mkw 0x00114020232c1023 0x2002280404658204 0xbe35cb67233c703b 0xf7c6b96ce4678e07

def z975 : W := mkw 0x25bff0007bfb0047 0x84b7fe000f7f6008 0xf5fff080ffff80c6 0x3ebffe101ffff018

def z976 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0a00086000007c38 0x0140010c00000f87

def z977 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x580a3498c3e38fff 0x6b014693187c71ff

def z978 : W := mkw 0x45bff387bbfb230f 0x88b7fe70f77f6461 0xf5fff387ffff8306 0xbebffe70fffff060

def z979 : W := mkw 0x05aea00018920004 0x00b5d40003124000 0x71c600003c3f8006 0x2e38c0000787f000

def z980 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xb635cb67203c7039 0xf6c6b96ce4078e07

def z981 : W := mkw 0xa3eebedacc53cc50 0xd47dd7db598a798a 0x41ca3498dcc38cc4 0x083946931b987198

def z982 : W := mkw 0x60115125636d336b 0xac022a24ac6da66d 0xfe3fffffe3fc73fb 0xffc7fffffc7f8e7f

def z983 : W := mkw 0x01aea00000000000 0x0035d40000000000 0xf7ffffffc0000001 0xfefffffff8000000

def z984 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xae35cb67231c7339 0xd5c6b96ce4638e67

def z985 : W := mkw 0x60115125636d336b 0xac022a24ac6da66d 0xfe3ffbe7e3fff3ff 0xffc7ff7cfc7ffe7f

def z986 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xa5fff0003fff8000 0x34bffe0007fff000

def z987 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0x41ce30001cff8004 0x2839c600039ff000

def z988 : W := mkw 0x008700040932010a 0x0010e00081264021 0xf9c700043f3f833f 0xff38e00087e7f067

def z989 : W := mkw 0x00500d0026006a00 0x400a01a004c00d40 0xf9f80f803fc07fc6 0xdf3f01f007f80ff8

def z990 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x4bc604783c3ffc3f 0x2978c08f0787ff87

def z991 : W := mkw 0x05bff2803bfb0007 0x80b7fe50077f6000 0xf5fff3803fff8006 0xbebffe7007fff000

def z992 : W := mkw 0x82c6ac7a8c16dc30 0x7058d58f5182db86 0x7fc6cc7b3c3ffc3f 0x6ff8d98f6787ff87

def z993 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf7ffffffffff8007 0xfefffffffffff000

def z994 : W := mkw 0x25bff0047bfb014f 0x84b7fe008f7f6029 0xfdfff084ffff83ff 0xffbffe109ffff07f

def z995 : W := mkw 0x0086000008120000 0x0010c00001024000 0x21c600003c3f8000 0x2438c0000787f000

def z996 : W := mkw 0x60115125636d336b 0xac022a24ac6da66d 0xfe3dffe7e3fc7fff 0xffc7bffcfc7f8fff

def z997 : W := mkw 0x01780fd036806a84 0x402f01fa06d00d50 0xfbf80ff83fc07fc7 0xdf7f01ff07f80ff8

def z998 : W := mkw 0x4011412533ac33af 0x28022824a6758675 0xbe35cb6723fc73fb 0xf7c6b96ce47f8e7f

def z999 : W := mkw 0x0086000008120000 0x0010c00001024000 0xf5f7c0003c3f8006 0x3ebef8000787f000

def z1000 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7ffffffe03c0003 0xfefffffffc078000

def z1001 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0x8637f37fc0000001 0xb0c6fe6ff8000000

def z1002 : W := mkw 0x2539f38473e923cf 0x84a73e708e7d2479 0x8439f384c3c003c0 0x90873e7098780078

def z1003 : W := mkw 0x0128a2d280000000 0x0025145a50000000 0x8639f3ffc0000001 0x90c73e7ff8000000

def z1004 : W := mkw 0x6011512d77edffff 0xec022a25aefdbfff 0x080000003ffffffe 0x0100000007ffffff

def z1005 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc73c7cfc3ffc3f 0x6f78e78f9f87ff87

def z1006 : W := mkw 0x82400c280c16dc30 0x704801850182db86 0x7bc40c603c3ffc3f 0x6f78818c0787ff87

def z1007 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x3bc608783c3ff03b 0x6778c10f0787fe07

def z1008 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x09c000003fc07fc6 0x0138000007f80ff8

def z1009 : W := mkw 0x0178af82b6806a84 0x402f15f056d00d50 0xfdfbff9fffc07fc7 0xffbf7ff3fff80ff8

def z1010 : W := mkw 0x05aff000097b0003 0x80b5fe00012f6000 0xf5fff0003c3f8006 0x3ebffe000787f000

def z1011 : W := mkw 0x05bff1003bfb2207 0x80b7fe20077f6440 0xf5fff3003fff8306 0xbebffe6007fff060

def z1012 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xda0b3fffc3e38fff 0xfb4167fff87c71ff

def z1013 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f90f843fc07fc7 0xff3f21f087f80ff8

def z1014 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff49cffff8fc7 0xffbffe939ffff1f8

def z1015 : W := mkw 0x01eeaed290800004 0x003dd5da52100000 0xf7ffffffdcc00005 0xfefffffffb980000

def z1016 : W := mkw 0x0178af82b6806a84 0x402f15f056d00d50 0xf9f83f80ffc07fc6 0xdf3f07f01ff80ff8

def z1017 : W := mkw 0x41784f8136886a85 0x482f09f026d10d50 0xfdf8cf833fc07fc6 0xdfbf19f067f80ff8

def z1018 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x75f6c0003fff8006 0x2ebed80007fff000

def z1019 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe37cf7f233c733b 0xffc6f9efe4678e67

def z1020 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f93f84ffc07fc6 0xdf3f27f09ff80ff8

def z1021 : W := mkw 0xc2400d7d0404ff38 0x784801afa0809fe7 0x0a000c7800007f39 0x4140018f00000fe7

def z1022 : W := mkw 0x0138010036806a84 0x4027002006d00d50 0x29f000003fc07fc6 0x053e000007f80ff8

def z1023 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff8003ffff006 0x7fbfff0007fffe00

def z1024 : W := mkw 0x01aea05280000000 0x0035d40a50000000 0xf7fffb7fc0000001 0xfeffff6ff8000000

def z1025 : W := mkw 0x041150003bfb0007 0x80822a00077f6000 0x71c000003fff8006 0x0e38000007fff000

def z1026 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xc00b349cc3e38ffd 0xb8016693987c71ff

def z1027 : W := mkw 0x6001500d4169855b 0x8c002a01a82d30ab 0xdc0bf49fc3e38fff 0xfb817e93f87c71ff

def z1028 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc60f7f3c3ffc3f 0xef78c1efe787ff87

def z1029 : W := mkw 0x40115125236d332b 0xa8022a24a46da665 0xbe3dfb6723fc733b 0xf7c7bf6ce47f8e67

def z1030 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xa9f80f803fc07fc0 0xd53f01f007f80ff8

def z1031 : W := mkw 0x0138010036806a84 0x4027002006d00d50 0xf9f80b003fc07fc6 0xdf3f016007f80ff8

def z1032 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x1a000c7800207c3b 0x6340018f00040f87

def z1033 : W := mkw 0x82c6ac780c16dc30 0x7058d58f0182db86 0x7fc7fc783c3ffc3f 0x6ff8ff8f0787ff87

def z1034 : W := mkw 0xa687f07c497f957b 0xb4d0fe0f892ff2af 0x0607f07cc03f8039 0x20c0fe0f9807f007

def z1035 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbc70c7c3c3ffc3f 0xff78e18f8787ff87

def z1036 : W := mkw 0x00500d0036806a84 0x400a01a006d00d50 0xf9c80c803fc07fc6 0xdf39019007f80ff8

def z1037 : W := mkw 0x40115125236d332b 0xa8022a24a46da665 0xfe3fffffe3fff33f 0xffc7fffffc7ffe67

def z1038 : W := mkw 0x01780fd2b6806a84 0x402f01fa56d00d50 0xfbf80fe33fc07fc6 0xdf7f01fc67f80ff8

def z1039 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x863fffffc0000001 0xf0c7fffff8000000

def z1040 : W := mkw 0xa2411c7c4565dd7a 0xf448238f88acbbaf 0x8a093cfcc3c07ff9 0xd141279f98780fff

def z1041 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0xf5fec0003fff8006 0x3ebfd80007fff000

def z1042 : W := mkw 0x05bff2d2bbfb0007 0x80b7fe5a577f6000 0xf7fff3ffffff8007 0xbefffe7ffffff000

def z1043 : W := mkw 0x01aea28288120000 0x0035d45051024000 0xf5fff387fc3f8006 0xbebffe70ff87f000

def z1044 : W := mkw 0x25bff0047bfb014f 0x84b7fe008f7f6029 0xf5fff004ffff8006 0x3ebffe009ffff000

def z1045 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xfbfc0fe03fc07fc7 0xff7f81fc07f80ff8

def z1046 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc60c783fffffff 0x6f78c18f07ffffff

def z1047 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff4803fff8cc6 0x3ebffe9007fff198

def z1048 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0xf5fef0003fdf8006 0x1ebfde0007fbf000

def z1049 : W := mkw 0x82400d780404fe30 0x704801af00809fc6 0x0a000f7800007f39 0xc14001ef00000fe7

def z1050 : W := mkw 0x05bff3803bfb2287 0x80b7fe70077f6450 0xfdfffb803ffff3c6 0xffbfff7007fffe78

def z1051 : W := mkw 0x05bff1003bfb2287 0x80b7fe20077f6450 0xf5fff0003fff83c6 0x3ebffe0007fff078

def z1052 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xffffffffffc07fc7 0xfffffffffff80ff8

def z1053 : W := mkw 0x83eeaeda9c92cc94 0x507dd5db53925992 0x41ca3498dcc38cc4 0x083946931b987198

def z1054 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x79f00f003fc07fc6 0x4f3e01e007f80ff8

def z1055 : W := mkw 0x05aeb00018d30004 0x80b5d600031a6000 0x41ca30003cff8006 0x08394600079ff000

def z1056 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff0803fff83c6 0xbebffe1007fff078

def z1057 : W := mkw 0xa287107c4977957a 0xb450e20f892ef2af 0x02060078003f8039 0x2040c00f0007f007

def z1058 : W := mkw 0x828600280c16dc30 0x7050c0050182db86 0x49c200003c3ffc3e 0x093840000787ff87

def z1059 : W := mkw 0x05aff00019fb0007 0x80b5fe00033f6000 0xd5cff0001fff8006 0x3ab9fe0003fff000

def z1060 : W := mkw 0x82400c780c16dc30 0x7048018f0182db86 0x7bc00c783c3ffc3f 0x4f78018f0787ff87

def z1061 : W := mkw 0x82c60c780404dc30 0x7058c18f00809b86 0x0a060c7800007c39 0x6140c18f00000f87

def z1062 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bc60cfcfc3ffc3f 0xef78c19f9f87ff87

def z1063 : W := mkw 0x049750003bfb0007 0x8092ea00077f6000 0xf1cf30003fff8006 0x3e39e60007fff000

def z1064 : W := mkw 0x05bff1003bfb2207 0x80b7fe20077f6440 0xfdffff803fffffc6 0xffbffff007fffff8

def z1065 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x6bc60c783c3ffc3e 0x0d78c18f0787ff87

def z1066 : W := mkw 0x45bff1053bfb230f 0x88b7fe20a77f6461 0xf7fffb673fff8307 0xfeffff6ce7fff060

def z1067 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xa7fffbffc0000001 0xb4ffff7ff8000000

def z1068 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x65fef0003fff8006 0x0cbfde0007fff000

def z1069 : W := mkw 0x45bff3853bfb238f 0x88b7fe70a77f6471 0xf5fff3873fff83c6 0xbebffe70e7fff078

def z1070 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xfffccfe33fc07fc6 0xdfff99fc67f80ff8

def z1071 : W := mkw 0x60105129624db671 0xac020a252c49b6ce 0x663efffbe0dffcc4 0x0cc7dfff7c1bff98

def z1072 : W := mkw 0x0139500033e90007 0x80272a00067d2000 0xf5fff0003fff8006 0x3ebffe0007fff000

def z1073 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f80f9cffc07fc7 0xdf3f01f39ff80ff8

def z1074 : W := mkw 0x82400efa8404dc30 0x704801df50809b86 0x0a000f7b00007c39 0x414001ef60000f87

def z1075 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xde0ff4ffc3e38fff 0xfbc1fe9ff87c71ff

def z1076 : W := mkw 0x0086000008120000 0x0010c00001024000 0x79c604003c3f8c06 0x6f38c0800787f180

def z1077 : W := mkw 0xc2400c7d0404dd38 0x7848018fa0809ba7 0x0a000c7f00007c39 0x4140018fe0000f87

def z1078 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xb9f00b003fc07fc6 0xd73e016007f80ff8

def z1079 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0x25f4c0003cdf8004 0x04be9800079bf000

def z1080 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xe5fff0003fdf8004 0x1cbffe0007fbf000

def z1081 : W := mkw 0xa2400ffc4404fff8 0x744801ff88809fff 0x0a000ffcc0007ff9 0xc14001ff98000fff

def z1082 : W := mkw 0x0178af8036806a84 0x402f15f006d00d50 0xfdf9ff803fc07fc6 0xdfbf3ff007f80ff8

def z1083 : W := mkw 0x00c60c7008161020 0x2018c18e0102c204 0x7bc60c783c3ff03f 0x6f78c18f0787fe07

def z1084 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xb5f5c0003fff8006 0x36beb80007fff000

def z1085 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xa635cb67233c7339 0xb4c6b96ce4678e67

def z1086 : W := mkw 0x4011412533ac332f 0x28022824a6758665 0xbe35cb673ffc733f 0xf7c6b96ce7ff8e67

def z1087 : W := mkw 0x01eeaed284004800 0x403dd5da50800900 0xf7fffffffc007001 0xfeffffffff800e00

def z1088 : W := mkw 0x40114121232c3223 0x2802282424658644 0xbe35cb63233c703b 0x77c6b96c64678e07

def z1089 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbce0cf83c3ffc3f 0xff79c19f0787ff87

def z1090 : W := mkw 0x05bff282bbfb0007 0x80b7fe50577f6000 0xf5fff3033fff8006 0x3ebffe6067fff000

def z1091 : W := mkw 0x60114125632c336b 0x2c022824ac65866d 0xbe35cbe7e33c73fb 0xf7c6b97cfc678e7f

def z1092 : W := mkw 0x01aea2d280000000 0x0035d45a50000000 0xd63ff7ffc0000001 0xfac7fefff8000000

def z1093 : W := mkw 0x828600280c16dc30 0x7050c0050182db86 0x79c604183c3ffc3f 0x6f38c0830787ff87

def z1094 : W := mkw 0x009600003a920004 0x0012c00007524000 0x71c600003fff8006 0x2e38c00007fff000

def z1095 : W := mkw 0xa2400efec404dd78 0x744801dfd8809baf 0x0a000fffc0007ff9 0xc14001fff8000fff

def z1096 : W := mkw 0x01ae000008120000 0x0035c00001024000 0xf1fe00003c3f8006 0x3e3fc0000787f000

def z1097 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff0003fff8fc6 0x3fbffe0007fff1f8

def z1098 : W := mkw 0x2000100840418450 0x840002010808308a 0xd80a3498c3e38fff 0xfb014693187c71ff

def z1099 : W := mkw 0x01780f82b6806a84 0x402f01f056d00d50 0xf9f80f87ffc07fc6 0xdf3f01f0fff80ff8

def z1100 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xfa0f3cfcc3e38fff 0xff41e79f987c71ff

def z1101 : W := mkw 0x82c60efa8c16dc30 0x7058c1df5182db86 0xfbcf3ffffc3ffc3f 0xff79e7ffff87ff87

def z1102 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfffffffffc3ffc3f 0xffffffffff87ff87

def z1103 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x65fff0003cff8004 0x2cbffe00079ff000

def z1104 : W := mkw 0x05bff1003bfb2207 0x80b7fe20077f6440 0xfdfff0003ffff306 0x3fbffe0007fffe60

def z1105 : W := mkw 0x82c60efa8c16dc30 0x7058c1df5182db86 0xfff7cffffc3ffc3f 0xfffef9ffff87ff87

def z1106 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x3e35cb67203c703b 0x67c6b96ce4078e07

def z1107 : W := mkw 0x0578ef8036886a85 0x40af1df006d10d50 0xfdf8cf803fc07fc6 0xdfbf19f007f80ff8

def z1108 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xffffffffc3000303 0xfffffffff8600060

def z1109 : W := mkw 0x82400efa8404dc30 0x704801df50809b86 0x0a000cf8c0007c39 0x4140019f18000f87

def z1110 : W := mkw 0x05bff052bbfb0007 0x80b7fe0a577f6000 0xf7fffb7fffff8007 0xfeffff6ffffff000

def z1111 : W := mkw 0x0497f0002b7b0003 0x8092fe00056f6000 0xf5f7f0003f3f8006 0x3ebefe0007e7f000

def z1112 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe3dcfe7233c733b 0xffc7b9fce4678e67

def z1113 : W := mkw 0x0086000008120000 0x0010c00001024000 0x41c600001c3f8004 0x2838c0000387f000

def z1114 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x3bc408603c3ffc3f 0x6778810c0787ff87

def z1115 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9fa0f983fc07fc7 0xff3f41f307f80ff8

def z1116 : W := mkw 0x45bff1053bfb230f 0x88b7fe20a77f6461 0xf5fff0003fff8306 0x3ebffe0007fff060

def z1117 : W := mkw 0xe211512d6f7fff7b 0xfc422a25adefffef 0x080000003ffffffe 0x0100000007ffffff

def z1118 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x480a349cc3e38fff 0xc9014693987c71ff

def z1119 : W := mkw 0x4539f387b3e9230f 0x88a73e70f67d2461 0x8439f387c3c00300 0x90873e70f8780060

def z1120 : W := mkw 0x01780fd2b6806a84 0x402f01fa56d00d50 0xfffdcfffffc07fc7 0xffffb9fffff80ff8

def z1121 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x79c604183c3ffc3e 0x2f38c0830787ff87

def z1122 : W := mkw 0x0487f000097b0003 0x8090fe00012f6000 0x45c7f0001c3f8004 0x28b8fe000387f000

def z1123 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x73c60c783c3ff039 0x6e78c18f0787fe07

def z1124 : W := mkw 0x05bff3803bfb2287 0x80b7fe70077f6450 0xf5fff3003fff8006 0x3ebffe6007fff000

def z1125 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9fa3f98ffc07fc6 0xdf3f47f31ff80ff8

def z1126 : W := mkw 0x0487f000097b0003 0x8090fe00012f6000 0xf5cff0003fff8006 0x3eb9fe0007fff000

def z1127 : W := mkw 0x828600280c16dc30 0x7050c0050182db86 0x29c400003c3ffc3e 0x053880000787ff87

def z1128 : W := mkw 0x82c6ac7a8404dc30 0x7058d58f50809b86 0x0e07fc7fc0007c39 0x61c0ff8ff8000f87

def z1129 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x5a000c7800007c3f 0x4b40018f00000f87

def z1130 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xc7fff7ffc0000001 0xb8fffefff8000000

def z1131 : W := mkw 0xa2400c784404dc70 0x7448018f08809b8e 0x0a000cf8c0007cf9 0x4140019f18000f9f

def z1132 : W := mkw 0x82c60ef80c16dc30 0x7058c1df0182db86 0x7bc60ff83c3ffc3f 0xef78c1ff0787ff87

def z1133 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xdc3bf79fc3e38fff 0xfb877ef3f87c71ff

def z1134 : W := mkw 0x0086000008120000 0x0010c00001024000 0x79c600003c3f803f 0x6f38c0000787f007

def z1135 : W := mkw 0x009640002a1a0001 0x0012c80005434000 0x75f6c0003c3f8006 0x2ebed8000787f000

def z1136 : W := mkw 0x45bff1053bfb230f 0x88b7fe20a77f6461 0xfdfff3073fff833f 0xffbffe60e7fff067

def z1137 : W := mkw 0x0000000800008410 0x0000000100001082 0xd80b349cc3e38fff 0xfb016693987c71ff

def z1138 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xf5fff0043fff803f 0x3ebffe0087fff007

def z1139 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0x0200047800000c39 0x0040008f00000187

def z1140 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9fa0f803fe3ffc6 0xff3f41f007fc7ff8

def z1141 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe37fb7fe33c733b 0xf7c6ff6ffc678e67

def z1142 : W := mkw 0x82c6ac7a8c16dc30 0x7058d58f5182db86 0x7bc63c78fc3ffc3f 0x6f78c78f1f87ff87

def z1143 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xa5fdf0003fff8006 0x14bfbe0007fff000

def z1144 : W := mkw 0x05bff282bbfb0007 0x80b7fe50577f6000 0xf5fff79fffff8007 0xfebffef3fffff000

def z1145 : W := mkw 0x83feaff2be967aa4 0x707fd5fe57d2cf54 0x27f4cb633c1c7000 0x04fe996c67838e00

def z1146 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff3073fff8006 0xbebffe60e7fff000

def z1147 : W := mkw 0x05bf50003bfb0007 0x80b7ea00077f6000 0xf1fe00003fff8006 0x3e3fc00007fff000

def z1148 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xbe35cfffe33c733b 0xf7c6b9fffc678e67

def z1149 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x2bc608783c3ffc3f 0x2578c10f0787ff87

def z1150 : W := mkw 0x40104125220c3329 0x28020824a4418665 0xbe34cb67231c733b 0xd7c6996ce4638e67

def z1151 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xfdfdcf803fc07fc6 0xffbfb9f007f80ff8

def z1152 : W := mkw 0xc2514d7d272cff3b 0x784a29afa4e59fe7 0x8e31cf7f03007f39 0xd1c639efe0600fe7

def z1153 : W := mkw 0x0138010032802204 0x0027002006500440 0xf9f80f803fc07fc6 0xdf3f01f007f80ff8

def z1154 : W := mkw 0x05bff1043bfb230f 0x80b7fe20877f6461 0xfdfffb043ffff33f 0xffbfff6087fffe67

def z1155 : W := mkw 0x00874000093a0003 0x0010e80001274000 0x75c7c0003c3f8006 0x2eb8f8000787f000

def z1156 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xfdfff0003fff833e 0x3fbffe0007fff067

def z1157 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x2e34cb67233c733b 0xc5c6996ce4678e67

def z1158 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x23c408603c3ff038 0x0478810c0787fe07

def z1159 : W := mkw 0x82400ffa8404feb0 0x704801ff50809fd6 0x0a000fffc0007ff9 0xc14001fff8000fff

def z1160 : W := mkw 0x82c60efa8c16dc30 0x7058c1df5182db86 0x7bc60f7b3c3ffc3f 0x6f78c1ef6787ff87

def z1161 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7ff6cf7b3c3ffc3f 0x6ffed9ef6787ff87

def z1162 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xf80b3c9ce3e3ffff 0xff0167939c7c7fff

def z1163 : W := mkw 0x00500f8036806a84 0x400a01f006d00d50 0x79c00f803fc07fc6 0xcf3801f007f80ff8

def z1164 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xe7ffffffc0000000 0x9cfffffff8000000

def z1165 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x77f7ff7fc0000001 0x6efeffeff8000000

def z1166 : W := mkw 0x0000000000000000 0x0000000000000000 0xb637fb7fc0000001 0xf6c6ff6ff8000000

def z1167 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x01c000003fff8006 0x0038000007fff000

def z1168 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xffffffffc0000c07 0xfffffffff8000180

def z1169 : W := mkw 0xa2400c7c4404dd78 0x7448018f88809baf 0x0a000c7800007ff9 0x4140018f00000fff

def z1170 : W := mkw 0x00500d0036806a84 0x400a01a006d00d50 0x29c008003fc07fc6 0x0538010007f80ff8

def z1171 : W := mkw 0x01ae000018920004 0x0035c00003124000 0x71ce00003cff8006 0x2e39c000079ff000

def z1172 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbcf3c783c3ffc3f 0x7f79e78f0787ff87

def z1173 : W := mkw 0x0178af82b6806a84 0x402f15f056d00d50 0xfdf8cf833fc07fc6 0xdfbf19f067f80ff8

def z1174 : W := mkw 0x40104125220c3329 0x28020824a4418665 0x2e34cb63201c7338 0x05c6996c64038e67

def z1175 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfff7cc783c3ffc3f 0x7ffef98f0787ff87

def z1176 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xfdf9cf873fc07fc6 0xdfbf39f0e7f80ff8

def z1177 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xe1f80f803fc07fc4 0x9c3f01f007f80ff8

def z1178 : W := mkw 0x82400c7c0404dd38 0x7048018f80809ba7 0x0a000c7c00007f39 0xc140018f80000fe7

def z1179 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bce0cf83cfffcff 0x6f79c19f079fff9f

def z1180 : W := mkw 0xe287507d497f957b 0xbc50ea0fa92ff2af 0x0607f07fc03f8039 0x20c0fe0ff807f007

def z1181 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0xf7ffffffc3c00007 0xfefffffff8780000

def z1182 : W := mkw 0x05bff2803bfb0087 0x80b7fe50077f6010 0xf5fff0803fff80c6 0x3ebffe1007fff018

def z1183 : W := mkw 0x0086000008120000 0x0010c00001024000 0xf1cf349cfc3f8007 0xfe39e6939f87f000

def z1184 : W := mkw 0x01bfe0002b3a0003 0x0037fc0005674000 0xf5fff0003f3f8006 0x3ebffe0007e7f000

def z1185 : W := mkw 0x01eeaed288120000 0x003dd5da51024000 0xf7fffffffc1c0001 0xfeffffffff838000

def z1186 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf7fff8603fff8007 0x7effff0c07fff000

def z1187 : W := mkw 0x4539f10533e9230f 0x88a73e20a67d2461 0x8439f00003c00300 0x10873e0000780060

def z1188 : W := mkw 0x40104125220c3329 0x28020824a4418665 0x2634cb67201c7039 0x04c6996ce4038e07

def z1189 : W := mkw 0x01780fd2b6806a84 0x402f01fa56d00d50 0xf9f80f98ffc07fc6 0xdf3f01f31ff80ff8

def z1190 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x7bce3cf8fc3ffc3f 0x6f79c79f1f87ff87

def z1191 : W := mkw 0x000100240124112a 0x2000200480248225 0xbe35cb67233c733b 0xf7c6b96ce4678e67

def z1192 : W := mkw 0x82400c780404dc30 0x7048018f00809b86 0xbe35cf7f00007c39 0xf7c6b9efe0000f87

def z1193 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xfffffb673fff833f 0xffffff6ce7fff067

def z1194 : W := mkw 0x01eeaed280000000 0x003dd5da50000000 0x27f7ffffc0000001 0xe4fefffff8000000

def z1195 : W := mkw 0x01eeaed28c124800 0x403dd5da51824900 0xfffffffffc3ffc07 0xffffffffff87ff80

def z1196 : W := mkw 0x0086a05280000000 0x0010d40a50000000 0xf63fffffc0000001 0xfec7fffff8000000

def z1197 : W := mkw 0x25bff0047bfb014f 0x84b7fe008f7f6029 0xfdfff484ffff8fc6 0xffbffe909ffff1f8

def z1198 : W := mkw 0x82c60efa8c16dc30 0x7058c1df5182db86 0x7bc60cf8fc3ffc3f 0x6f78c19f1f87ff87

def z1199 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x69f80f803fc07fc6 0x0d3f01f007f80ff8

def z1200 : W := mkw 0x049750003bfb0007 0x8092ea00077f6000 0xf5f7c0003fff8006 0x3ebef80007fff000

def z1201 : W := mkw 0x009601002a122200 0x0012c02005424440 0xf9f60b003f3ff306 0xff3ec16007e7fe60

def z1202 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0x480b349cc3e38fff 0x29016693987c71ff

def z1203 : W := mkw 0x05aef00018db0005 0x80b5de00031b6000 0x45cef0001cdf8004 0x08b9de00039bf000

def z1204 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0x79c80c803fc07fc6 0x4f39019007f80ff8

def z1205 : W := mkw 0x0086000008120000 0x0010c00001024000 0xf1ce00003fff8006 0x3e39c00007fff000

def z1206 : W := mkw 0x82400ef80404dcb0 0x704801df00809b96 0x0a000cf800007cf9 0x4140019f00000f9f

def z1207 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xfdfff49cffff833f 0xffbffe939ffff067

def z1208 : W := mkw 0x40114125232c332b 0x28022824a4658665 0x2e35cb67233c733b 0x25c6b96ce4678e67

def z1209 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0x75fef0003cff8006 0x2ebfde00079ff000

def z1210 : W := mkw 0x009750002b7b0003 0x8012ea00056f6000 0xf5fff0003fff8006 0x3ebffe0007fff000

def z1211 : W := mkw 0x8286007808169430 0x3050c00f0102d286 0x7bc608783c3ff03f 0x6f78c10f0787fe07

def z1212 : W := mkw 0x0087100009730002 0x8010e200012e6000 0x71c730003c3f8006 0x2e38e6000787f000

def z1213 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xa9f80b803fc07fc6 0x953f017007f80ff8

def z1214 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xd1cb30003fff8006 0x3a39660007fff000

def z1215 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0x4bc20c783c3ffc3f 0x4978418f0787ff87

def z1216 : W := mkw 0x0086000008120000 0x0010c00001024000 0x71c604183c3f8007 0x6e38c0830787f000

def z1217 : W := mkw 0x83eeaeda8c12cc10 0x507dd5db51825982 0x41c204181c038c04 0x0838408303807180

def z1218 : W := mkw 0x05bef0003adb0005 0x80b7de00075b6000 0xf5fff0003cdf8004 0x3ebffe00079bf000

def z1219 : W := mkw 0xe2400d7d4404ff78 0x7c4801afa8809fef 0x0a000fffc0007ff9 0xc14001fff8000fff

def z1220 : W := mkw 0x01780f8036806a84 0x402f01f006d00d50 0xf9f80f803fe07fff 0xff3f01f007fc0fff

def z1221 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xfc3ff49cc3e38fff 0xff87fe93987c71ff

def z1222 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff0003c3f8000 0x3ebffe000787f000

def z1223 : W := mkw 0x0539f0003bfb0007 0x80a73e00077f6000 0xf5f9f0003fff8006 0x1ebf3e0007fff000

def z1224 : W := mkw 0xc2400ffd0404ffb8 0x784801ffa0809ff7 0x0a000fff00007ff9 0xc14001ffe0000fff

def z1225 : W := mkw 0x05bee0003a9a0005 0x00b7dc0007534000 0x25f6c0003c3f8000 0x24bed8000787f000

def z1226 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x25f4c0003c3f8000 0x04be98000787f000

def z1227 : W := mkw 0x6411512d7bffb77f 0xac822a25af7ff6ef 0x080000003ffffffe 0x0100000007ffffff

def z1228 : W := mkw 0x00c6aed280000000 0x0018d5da50000000 0xb637ffffc0000001 0xf6c6fffff8000000

def z1229 : W := mkw 0x25bff0047bfb014f 0x84b7fe008f7f6029 0xf5fff49cffff83c7 0xfebffe939ffff078

def z1230 : W := mkw 0x828600780c16dc30 0x7050c00f0182db86 0x7bc600783c3ffc3f 0x2f78c00f0787ff87

def z1231 : W := mkw 0x2001100c4161855a 0x84002201882c30ab 0xd80a3498c3e38ffe 0xdb014693187c71ff

def z1232 : W := mkw 0x82c60c780c16dc30 0x7058c18f0182db86 0xfbce0c783ffffc3f 0x7f79c18f07ffff87

def z1233 : W := mkw 0x0086000008120000 0x0010c00001024000 0xf9ce04803fff8fc6 0xff39c09007fff1f8

def z1234 : W := mkw 0x0086002808169430 0x2010c0050102d286 0x7bc60c783c3ffc3f 0x6f78c18f0787ff87

def z1235 : W := mkw 0x01784f8036886a85 0x402f09f006d10d50 0xfdfccf803fdc7fc6 0xdfbf99f007fb8ff8

def z1236 : W := mkw 0x00c60c5000000000 0x0018c18a00000000 0xf7ffffffc0000001 0xfefffffff8000000

def z1237 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0x25f7f0003fff8006 0x24befe0007fff000

def z1238 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xfe3ffb67233c733b 0xffc7ff6ce4678e67

def z1239 : W := mkw 0x00c60c200c165820 0x6018c1840182cb04 0x7bc60c603c3ffc3f 0x6f78c18c0787ff87

def z1240 : W := mkw 0x6139538573e923cf 0x8c272a70ae7d2479 0x8439f387c3c003c0 0x90873e70f8780078

def z1241 : W := mkw 0x6539f10573e9234f 0x8ca73e20ae7d2469 0x8439f387c3c003c0 0x90873e70f8780078

def z1242 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xf5fff0043fff8007 0xfebffe0087fff000

def z1243 : W := mkw 0x40114125232c332b 0x28022824a4658665 0xae35cb67233c733a 0x95c6b96ce4678e67

def z1244 : W := mkw 0x05bff0043bfb010f 0x80b7fe00877f6021 0xf5fff0043fff8306 0xbebffe0087fff060

def z1245 : W := mkw 0x01eeaed294804884 0x403dd5da52900910 0xffffffffdfc00fc7 0xfffffffffbf801f8

def z1246 : W := mkw 0x05bff0003bfb0007 0x80b7fe00077f6000 0xfdfff4003fff8c06 0x7fbffe8007fff180

def z1247 : W := mkw 0x82400fa80404feb0 0x704801f500809fd6 0x08000f8000007ff8 0xc10001f000000fff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z8,z6]),(0,[z9,z10,z0,z1,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z11,z12])],[(0,[z0,z13,z1,z2,z3,z4,z6]),(1,[z14,z15,z2,z3,z4,z6]),(1,[z10,z0,z1,z3,z4,z16]),(0,[z17,z0,z1,z3,z4,z18,z6])],[(0,[z0,z1,z2,z3,z19,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z20])],[(0,[z0,z1,z2,z3,z4,z21,z6]),(0,[z0,z1,z2,z3,z4,z22,z6]),(0,[z23,z24,z1,z2,z3,z4,z6]),(0,[z25,z0,z26,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z27,z6])],[(0,[z0,z1,z2,z28,z3,z4,z6]),(0,[z0,z26,z1,z2,z3,z4,z6]),(1,[z0,z1,z29,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z6,z30]),(0,[z0,z1,z2,z3,z31,z4,z6]),(0,[z25,z0,z1,z2,z3,z6,z30])],[(0,[z0,z1,z2,z3,z4,z32,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z15,z33,z0,z2,z3,z4,z6]),(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z1,z35,z2,z36,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z38,z6]),(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z0,z1,z2,z3,z4,z40,z6])],[(0,[z0,z1,z2,z3,z41,z4,z6]),(0,[z10,z24,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z42,z6]),(0,[z43,z0,z1,z44,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z45]),(0,[z0,z1,z2,z46,z3,z4,z6]),(0,[z17,z0,z1,z2,z4,z6,z12])]],
   [[(0,[z0,z1,z2,z47,z3,z4,z6]),(0,[z10,z0,z48,z1,z3,z4,z6]),(0,[z49,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z50,z6]),(0,[z51,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z46,z3,z52,z6])],[(0,[z0,z1,z53,z2,z3,z4,z6]),(0,[z54,z0,z1,z2,z3,z4,z6]),(1,[z0,z55,z2,z3,z4,z6]),(0,[z0,z1,z29,z2,z3,z4,z6]),(1,[z56,z0,z2,z3,z4,z16]),(0,[z0,z2,z3,z4,z57,z6,z16]),(0,[z33,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z58,z2,z3,z4,z6]),(0,[z43,z0,z1,z3,z4,z18,z6]),(0,[z25,z0,z1,z59,z2,z3,z4])],[(0,[z60,z0,z1,z2,z3,z4,z6]),(0,[z61,z0,z1,z2,z3,z4,z6]),(0,[z62,z0,z1,z2,z3,z4,z6]),(1,[z63,z0,z2,z3,z4,z6])],[(0,[z64,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z65,z6]),(0,[z0,z1,z2,z66,z3,z4,z6]),(0,[z67,z33,z1,z2,z3,z4,z6])],[],[(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z69,z4,z6]),(0,[z0,z1,z70,z3,z4,z18,z6]),(0,[z17,z0,z1,z2,z71,z4,z6])],[(0,[z14,z72,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z2,z3,z74,z6])],[(0,[z0,z1,z2,z3,z75,z4,z6]),(0,[z0,z1,z2,z76,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z77]),(0,[z0,z1,z78,z79,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z82,z4,z6]),(0,[z0,z1,z2,z3,z83,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z84,z6]),(0,[z0,z1,z2,z3,z4,z6,z85]),(0,[z86,z0,z1,z2,z3,z4,z6])],[(0,[z33,z0,z2,z79,z3,z4,z6]),(0,[z87,z0,z1,z88,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z89])],[(0,[z15,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z90,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z91,z6]),(0,[z0,z92,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z93,z94,z6]),(0,[z0,z1,z2,z3,z4,z6,z95])],[(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z97,z6]),(0,[z0,z1,z2,z3,z4,z6,z98]),(1,[z9,z0,z1,z99,z4,z6]),(0,[z0,z1,z2,z3,z4,z100,z6])],[(0,[z14,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z101,z3,z4,z6]),(0,[z0,z1,z3,z102,z4,z18,z6]),(0,[z0,z103,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z104,z6])],[(0,[z0,z105,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z57,z18,z6])],[(0,[z0,z1,z2,z3,z4,z106,z6]),(0,[z0,z1,z35,z3,z4,z93,z6]),(0,[z107,z108,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z109,z4,z94,z6]),(0,[z0,z1,z2,z3,z4,z57,z12])],[(0,[z0,z1,z110,z2,z3,z4,z6]),(0,[z0,z1,z3,z111,z4,z104,z6])]],
   [[(0,[z0,z1,z2,z112,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z113,z6]),(0,[z114,z0,z1,z2,z3,z4,z6]),(0,[z7,z87,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z8,z4,z115,z6]),(0,[z0,z1,z2,z3,z115,z94,z6]),(0,[z33,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z116,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z117,z6]),(0,[z0,z1,z2,z3,z118,z4,z6])],[(0,[z87,z0,z1,z2,z102,z4,z6]),(0,[z7,z0,z1,z2,z119,z4,z6]),(0,[z10,z0,z1,z3,z4,z6,z6]),(0,[z0,z1,z59,z2,z3,z4,z18]),(0,[z120,z0,z1,z2,z3,z4,z6])],[(0,[z14,z15,z1,z2,z3,z4,z6]),(1,[z0,z1,z121,z3,z4,z6]),(0,[z23,z0,z1,z3,z4,z18,z6]),(0,[z108,z1,z2,z3,z4,z6,z77]),(0,[z0,z122,z1,z2,z3,z4,z6])],[(0,[z10,z0,z1,z123,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z115,z6]),(0,[z0,z1,z2,z3,z4,z124,z6])],[(0,[z0,z1,z2,z3,z125,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z127]),(0,[z25,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z128,z3,z4,z6])],[(0,[z129,z0,z1,z2,z3,z4,z6]),(0,[z7,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z130,z3,z99,z4,z6]),(0,[z10,z63,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z131,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z132,z6]),(0,[z133,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z134])],[(1,[z0,z1,z135,z3,z4,z6])],[(0,[z0,z136,z2,z3,z4,z6,z16]),(0,[z107,z0,z137,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z138]),(0,[z0,z1,z2,z3,z4,z139,z6]),(0,[z0,z1,z2,z3,z4,z6,z140])]],
   [[(0,[z0,z1,z141,z2,z3,z4,z6]),(0,[z142,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z143,z2,z3,z4,z6])],[(0,[z0,z136,z2,z3,z8,z4,z6]),(1,[z24,z1,z2,z3,z144,z6]),(0,[z0,z1,z145,z2,z3,z4,z6]),(0,[z146,z0,z1,z3,z4,z18,z6]),(0,[z147,z0,z1,z2,z3,z4,z6])],[(0,[z148,z0,z1,z2,z3,z4,z6]),(0,[z149,z0,z1,z2,z3,z4,z6]),(1,[z150,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z151]),(0,[z0,z1,z2,z152,z3,z4,z6]),(0,[z0,z1,z2,z3,z153,z4,z6])],[(0,[z154,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z155]),(0,[z156,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z79,z3,z4,z93,z6]),(0,[z157,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z158,z4,z6])],[(0,[z0,z1,z2,z3,z144,z4,z6]),(0,[z159,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z160,z2,z3,z4,z6])],[(0,[z0,z1,z2,z161,z3,z4,z6]),(0,[z0,z1,z130,z3,z4,z18,z6]),(0,[z0,z1,z3,z4,z6,z162,z12]),(0,[z0,z1,z2,z3,z4,z163,z6])],[(0,[z0,z1,z2,z3,z164,z4,z6]),(0,[z0,z1,z3,z144,z4,z18,z6]),(0,[z33,z165,z1,z2,z3,z4,z6]),(0,[z166,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z167]),(0,[z15,z0,z1,z168,z3,z4,z6]),(0,[z169,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z79,z3,z4,z6]),(0,[z0,z1,z2,z109,z3,z4,z6]),(1,[z0,z1,z2,z3,z170,z6])]],
   [[(0,[z72,z0,z1,z3,z4,z18,z6]),(0,[z0,z171,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z46,z102,z4,z6]),(0,[z0,z172,z1,z2,z109,z4,z6]),(0,[z7,z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z174]),(0,[z0,z1,z59,z2,z3,z4,z57])],[(0,[z175,z0,z1,z2,z3,z4,z6]),(0,[z176,z0,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z177,z6]),(0,[z0,z1,z2,z3,z4,z178,z6]),(0,[z87,z0,z1,z2,z3,z179,z6]),(0,[z0,z1,z2,z3,z4,z180,z16]),(0,[z0,z1,z2,z3,z4,z181,z6]),(0,[z0,z1,z2,z182,z3,z4,z6]),(0,[z0,z1,z2,z3,z111,z117,z6]),(0,[z0,z1,z2,z3,z4,z6,z183])],[(0,[z0,z136,z2,z3,z102,z4,z6]),(0,[z72,z0,z1,z2,z184,z4,z6]),(0,[z0,z1,z123,z3,z4,z93,z6]),(0,[z185,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z135,z3,z111,z4,z6])],[(0,[z0,z1,z186,z2,z3,z4,z6]),(0,[z187,z0,z1,z2,z3,z4,z6]),(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z189,z4,z6]),(0,[z190,z0,z1,z2,z3,z4,z6]),(1,[z10,z0,z1,z3,z4,z18]),(0,[z0,z1,z2,z3,z191,z4,z6])],[(0,[z107,z0,z1,z3,z4,z18,z6]),(0,[z192,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z79,z3,z4,z6,z16]),(0,[z80,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z193,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z6,z194]),(0,[z107,z0,z1,z2,z184,z4,z6]),(1,[z72,z1,z2,z195,z4,z6]),(0,[z0,z1,z2,z130,z3,z4,z6]),(0,[z10,z0,z196,z2,z3,z4,z6]),(0,[z0,z1,z197,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z198])],[(0,[z14,z1,z2,z3,z184,z4,z6]),(0,[z15,z0,z1,z2,z3,z4,z155]),(0,[z80,z0,z2,z3,z4,z6,z16]),(1,[z0,z1,z3,z4,z84,z6]),(0,[z0,z1,z2,z199,z3,z4,z6]),(0,[z10,z0,z1,z200,z3,z4,z6])]],
   [[(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z202,z2,z3,z4,z6]),(1,[z0,z203,z2,z3,z4,z6]),(0,[z0,z1,z79,z3,z99,z4,z6])],[(0,[z204,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z205,z3,z4,z6]),(0,[z114,z24,z0,z2,z3,z4,z6]),(0,[z0,z1,z206,z2,z3,z4,z6]),(0,[z10,z0,z1,z79,z3,z4,z6]),(0,[z0,z1,z3,z99,z4,z93,z6])],[(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z0,z1,z2,z3,z4,z208,z6]),(0,[z0,z1,z2,z3,z4,z209,z6]),(0,[z210,z211,z1,z2,z3,z4,z6]),(0,[z87,z49,z1,z2,z3,z4,z6]),(0,[z212,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z213]),(0,[z214,z0,z1,z3,z4,z18,z6]),(1,[z25,z0,z1,z2,z3,z30])],[(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z4,z177,z6]),(0,[z0,z1,z2,z3,z52,z177,z6]),(1,[z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z4,z81,z6]),(0,[z56,z0,z2,z3,z4,z6,z16]),(0,[z0,z1,z2,z3,z4,z215,z6]),(1,[z43,z0,z1,z3,z93,z6]),(0,[z0,z1,z2,z3,z52,z4,z6]),(0,[z0,z216,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z217])],[(0,[z218,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z219,z6]),(0,[z0,z1,z2,z3,z4,z220,z6]),(0,[z221,z0,z1,z2,z3,z4,z6]),(0,[z10,z63,z0,z1,z3,z4,z6]),(0,[z222,z10,z0,z1,z3,z4,z6]),(0,[z25,z10,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z12])],[(0,[z107,z0,z1,z2,z3,z4,z223]),(0,[z224,z0,z1,z186,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z225,z6]),(0,[z0,z1,z3,z4,z84,z6,z16]),(0,[z226,z0,z1,z2,z3,z4,z6])],[(0,[z211,z1,z2,z36,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z6]),(0,[z227,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z123,z3,z99,z4,z6]),(0,[z43,z0,z1,z3,z4,z93,z6]),(1,[z0,z1,z44,z3,z74,z6]),(0,[z228,z0,z1,z2,z3,z94,z6]),(0,[z229,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z230,z3,z4,z6])]],
   [[(0,[z0,z1,z79,z3,z4,z18,z6]),(1,[z0,z1,z78,z130,z4,z6])],[(0,[z15,z0,z1,z231,z3,z4,z6]),(0,[z0,z1,z78,z2,z130,z4,z6]),(0,[z10,z0,z1,z46,z3,z4,z6])],[(0,[z24,z0,z1,z3,z4,z18,z6]),(1,[z0,z92,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z232,z4,z6]),(1,[z10,z0,z1,z3,z4,z57]),(0,[z0,z1,z2,z3,z4,z6,z233]),(0,[z234,z0,z1,z2,z3,z4,z6])],[(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z235,z1,z2,z3,z4,z6]),(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z237,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z238,z4,z6]),(0,[z0,z172,z1,z3,z4,z18,z6]),(0,[z239,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z240,z6]),(0,[z7,z25,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z57,z180]),(0,[z0,z1,z2,z3,z4,z6,z241]),(1,[z0,z1,z131,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z242,z6])],[(0,[z210,z1,z35,z2,z3,z4,z6]),(0,[z0,z1,z123,z44,z3,z4,z6]),(0,[z0,z1,z2,z3,z170,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z243]),(0,[z0,z1,z123,z78,z3,z4,z6]),(0,[z0,z1,z78,z130,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z244])],[(0,[z211,z1,z136,z2,z3,z4,z6]),(0,[z245,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z123,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z246,z6]),(0,[z0,z1,z59,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z247,z6])]],
   [[(0,[z0,z137,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z248,z4,z6]),(0,[z0,z1,z2,z249,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z250,z6])],[(0,[z10,z0,z1,z3,z4,z6,z77]),(0,[z0,z1,z2,z3,z251,z4,z6]),(0,[z0,z1,z252,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z6,z6]),(0,[z253,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z254,z4,z6]),(0,[z0,z1,z2,z3,z255,z4,z6]),(0,[z214,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z111,z117])],[(0,[z1,z2,z3,z144,z4,z177,z6]),(0,[z0,z1,z2,z46,z3,z94,z6])],[(0,[z10,z0,z172,z1,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z115,z6]),(1,[z0,z1,z161,z3,z4,z6]),(0,[z33,z0,z1,z2,z3,z4,z57]),(0,[z0,z1,z2,z3,z256,z4,z6])],[],[(0,[z0,z257,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z258,z3,z4,z6]),(0,[z0,z1,z3,z99,z4,z18,z6]),(0,[z0,z1,z2,z3,z259,z4,z6])],[(0,[z0,z1,z2,z3,z260,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z261]),(0,[z0,z1,z2,z3,z111,z4,z117])]],
   [[(0,[z1,z136,z2,z3,z4,z177,z6]),(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z263,z6]),(0,[z0,z1,z2,z3,z264,z4,z6]),(0,[z265,z0,z1,z2,z3,z4,z6])],[(0,[z24,z0,z1,z2,z3,z4,z6]),(0,[z24,z0,z1,z2,z3,z177,z6]),(0,[z266,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z267,z3,z4,z6]),(0,[z268,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z269])],[(0,[z0,z1,z2,z3,z99,z4,z6]),(1,[z0,z1,z3,z191,z4,z6])],[(0,[z0,z1,z270,z2,z3,z4,z6]),(0,[z271,z0,z1,z2,z3,z4,z6]),(0,[z0,z26,z1,z2,z3,z117,z6])],[(0,[z272,z0,z136,z2,z3,z4,z6]),(0,[z0,z1,z55,z2,z3,z4,z6]),(0,[z224,z0,z1,z2,z3,z4,z16]),(0,[z80,z0,z1,z3,z4,z18,z6]),(1,[z25,z10,z0,z1,z3,z4])],[(0,[z273,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z274,z6]),(1,[z0,z1,z2,z119,z4,z6]),(1,[z0,z1,z3,z4,z6,z198])],[(0,[z1,z136,z35,z2,z3,z4,z6]),(0,[z0,z1,z275,z2,z3,z4,z6]),(0,[z0,z1,z36,z3,z4,z93,z6]),(0,[z107,z0,z1,z2,z3,z164,z6]),(0,[z0,z1,z123,z2,z3,z4,z6]),(0,[z276,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z277,z6]),(0,[z10,z0,z1,z2,z3,z4,z278])],[(0,[z0,z1,z279,z2,z3,z4,z6]),(0,[z280,z0,z1,z2,z3,z4,z6]),(0,[z281,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z74,z4,z6]),(0,[z282,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z283,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z284,z2,z3,z4,z6]),(0,[z285,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z286,z4,z6]),(0,[z0,z1,z2,z3,z4,z287,z6]),(0,[z0,z1,z2,z3,z4,z288,z6]),(0,[z0,z1,z2,z3,z4,z6,z289]),(1,[z10,z0,z1,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z4,z30])],[(0,[z211,z0,z1,z3,z4,z18,z6]),(0,[z290,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z291,z6]),(0,[z0,z1,z2,z3,z4,z6,z292]),(0,[z293,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z294,z6]),(0,[z0,z1,z2,z3,z4,z18,z6]),(0,[z295,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z296,z4,z6]),(0,[z0,z297,z1,z2,z3,z4,z6]),(0,[z56,z0,z1,z2,z3,z4,z16]),(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z298,z6])],[(0,[z0,z26,z2,z3,z8,z4,z6]),(0,[z299,z0,z1,z2,z3,z4,z6]),(1,[z1,z2,z3,z4,z6,z11])],[(0,[z300,z0,z1,z2,z3,z4,z6]),(0,[z301,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z97,z180]),(0,[z0,z1,z2,z3,z302,z4,z6]),(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z111,z4,z18,z6])],[(0,[z210,z0,z1,z123,z3,z4,z6]),(0,[z1,z2,z195,z3,z4,z97,z6]),(0,[z10,z0,z1,z3,z144,z4,z6]),(0,[z304,z0,z1,z2,z3,z4,z6]),(0,[z67,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z136,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z6,z213]),(0,[z0,z1,z3,z184,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z6,z305]),(0,[z0,z1,z2,z3,z4,z306,z6]),(1,[z10,z0,z196,z3,z4,z6])]],
   [[(1,[z272,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z307,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z308,z6])],[(0,[z0,z309,z1,z2,z3,z4,z6]),(0,[z310,z0,z1,z2,z3,z4,z6]),(0,[z0,z48,z1,z3,z4,z18,z6]),(0,[z10,z0,z1,z109,z3,z4,z6]),(0,[z0,z311,z1,z2,z3,z4,z6])],[(0,[z312,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z16,z12]),(0,[z0,z1,z313,z2,z3,z4,z6])],[(0,[z0,z1,z36,z3,z99,z4,z6]),(0,[z9,z0,z1,z3,z99,z4,z6]),(0,[z314,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z315,z6]),(0,[z43,z0,z1,z2,z3,z4,z6]),(0,[z316,z0,z1,z3,z4,z18,z6])],[(0,[z210,z10,z0,z1,z3,z4,z6]),(1,[z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z11])],[(0,[z0,z1,z2,z317,z3,z4,z6]),(0,[z72,z0,z1,z2,z195,z4,z6]),(1,[z0,z1,z186,z3,z4,z6]),(0,[z0,z1,z2,z318,z3,z4,z6])],[(0,[z211,z0,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z319,z6]),(0,[z0,z1,z2,z3,z4,z320,z6]),(0,[z0,z1,z2,z3,z4,z321,z6]),(1,[z0,z196,z2,z3,z4,z6])],[(0,[z0,z1,z322,z2,z3,z4,z6]),(0,[z0,z1,z2,z323,z3,z4,z6]),(0,[z0,z1,z2,z3,z102,z4,z6]),(0,[z0,z1,z2,z3,z324,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z278]),(0,[z0,z325,z1,z2,z3,z4,z6])]],
   [[(0,[z14,z24,z1,z2,z3,z4,z6]),(0,[z326,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z327,z6]),(0,[z0,z1,z2,z3,z144,z94,z6]),(0,[z328,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z329,z4,z6]),(0,[z0,z1,z2,z3,z4,z330,z6])],[(0,[z14,z108,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z107,z0,z1,z2,z195,z4,z6]),(0,[z0,z48,z2,z79,z3,z4,z6]),(0,[z0,z331,z1,z3,z4,z18,z6]),(0,[z0,z2,z3,z4,z332,z94,z6])],[(0,[z10,z272,z0,z1,z3,z4,z6]),(0,[z7,z15,z0,z2,z3,z4,z6]),(0,[z15,z0,z2,z3,z8,z4,z6]),(0,[z0,z1,z2,z3,z333,z4,z6]),(0,[z0,z334,z1,z2,z3,z4,z6]),(1,[z212,z0,z1,z2,z3,z6]),(0,[z9,z0,z1,z78,z3,z4,z6]),(0,[z0,z1,z78,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z111,z4,z30])],[(0,[z0,z1,z36,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z335,z4,z6]),(0,[z7,z0,z1,z2,z3,z4,z336]),(0,[z9,z0,z1,z3,z4,z18,z6])],[(0,[z108,z10,z0,z1,z3,z4,z6]),(0,[z337,z0,z1,z2,z3,z4,z6]),(0,[z43,z0,z1,z2,z3,z93,z6]),(0,[z10,z10,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z179,z6]),(0,[z0,z1,z2,z3,z4,z338,z6]),(0,[z25,z0,z1,z2,z3,z111,z6])],[(0,[z0,z1,z136,z2,z3,z4,z6]),(0,[z0,z1,z339,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z177,z6]),(0,[z340,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z52,z4,z6])],[(0,[z211,z0,z1,z35,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z6,z12])]],
   [[(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z0,z1,z2,z342,z3,z4,z6]),(0,[z0,z1,z2,z3,z144,z52,z6]),(0,[z224,z0,z1,z343,z3,z4,z6]),(0,[z0,z48,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z344,z3,z4,z6]),(0,[z345,z0,z1,z2,z3,z4,z6])],[(0,[z346,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z347,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z348])],[(0,[z349,z0,z1,z2,z3,z4,z6]),(0,[z350,z0,z1,z2,z3,z4,z6]),(0,[z316,z0,z1,z2,z3,z4,z6]),(0,[z0,z351,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z352,z6])],[(0,[z15,z0,z2,z3,z102,z4,z6]),(0,[z0,z1,z2,z3,z353,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z354]),(0,[z0,z1,z2,z71,z3,z163,z6])],[(0,[z210,z0,z1,z79,z3,z4,z6]),(0,[z355,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z52,z4,z18,z6])],[(1,[z87,z0,z2,z102,z4,z6]),(0,[z7,z356,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z332,z6])],[(0,[z0,z1,z78,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z357,z6]),(1,[z0,z1,z2,z3,z358,z6]),(0,[z0,z1,z2,z3,z4,z117,z16]),(0,[z0,z1,z2,z3,z4,z359,z6]),(0,[z360,z10,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z361]),(0,[z0,z1,z362,z2,z3,z4,z6]),(0,[z0,z1,z2,z363,z3,z4,z6]),(0,[z0,z1,z2,z102,z4,z94,z6]),(0,[z0,z1,z2,z3,z4,z6,z364]),(0,[z365,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z366,z6])]],
   [[(0,[z23,z0,z1,z284,z3,z4,z6]),(0,[z0,z1,z2,z3,z177,z94,z6]),(0,[z0,z1,z367,z2,z3,z4,z6]),(0,[z0,z1,z2,z343,z3,z4,z6]),(0,[z0,z331,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z94,z6])],[(0,[z108,z1,z136,z2,z3,z4,z6]),(0,[z0,z1,z78,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z18,z6])],[(0,[z0,z1,z2,z3,z4,z97,z12]),(0,[z7,z0,z2,z3,z4,z115,z6]),(0,[z9,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z3,z99,z4,z6]),(0,[z0,z1,z2,z71,z4,z180,z6]),(0,[z0,z1,z368,z2,z3,z4,z6])],[(0,[z0,z1,z369,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z251,z4,z6]),(0,[z0,z1,z2,z3,z4,z370,z6])],[(0,[z0,z1,z2,z3,z184,z4,z6]),(0,[z371,z0,z1,z2,z3,z4,z6]),(0,[z228,z0,z1,z131,z3,z4,z6])],[(0,[z107,z0,z1,z2,z3,z4,z263]),(0,[z0,z1,z2,z3,z372,z4,z6]),(0,[z0,z1,z2,z3,z373,z4,z6]),(0,[z0,z1,z2,z3,z374,z4,z6]),(0,[z0,z26,z1,z2,z3,z8,z6])],[(0,[z0,z1,z2,z3,z4,z375,z6]),(1,[z376,z1,z2,z3,z4,z6]),(0,[z0,z1,z377,z2,z3,z4,z6]),(0,[z378,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z104,z6])],[(0,[z0,z1,z2,z3,z4,z379,z6]),(0,[z380,z0,z1,z2,z3,z4,z6]),(0,[z14,z0,z1,z3,z4,z18,z6]),(1,[z23,z1,z2,z3,z177,z6]),(0,[z0,z1,z2,z3,z4,z6,z381]),(0,[z0,z1,z2,z3,z4,z6,z382]),(0,[z0,z1,z44,z3,z74,z4,z6]),(1,[z166,z0,z1,z3,z4,z6])]],
   [[(0,[z33,z0,z136,z2,z3,z4,z6]),(0,[z383,z0,z1,z2,z3,z4,z6]),(0,[z0,z384,z1,z2,z3,z4,z6])],[(0,[z385,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z386,z2,z3,z4,z6]),(0,[z0,z1,z44,z78,z3,z4,z6]),(0,[z0,z387,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z180,z6]),(0,[z25,z0,z1,z2,z3,z4,z117])],[(0,[z388,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z88,z3,z4,z6]),(0,[z0,z1,z44,z3,z4,z18,z6]),(0,[z0,z1,z2,z71,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z223]),(0,[z1,z2,z3,z4,z97,z6,z77]),(0,[z0,z1,z2,z3,z4,z389,z6]),(1,[z0,z48,z79,z3,z4,z6]),(0,[z390,z0,z1,z2,z3,z4,z6]),(0,[z391,z10,z0,z1,z3,z4,z6])],[(0,[z392,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z99,z4,z6]),(0,[z10,z0,z1,z2,z3,z111,z4]),(0,[z0,z1,z3,z4,z18,z6,z151]),(0,[z0,z1,z393,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z394,z6]),(0,[z0,z1,z2,z3,z4,z6,z395]),(0,[z0,z92,z1,z3,z4,z6,z77]),(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z397]),(0,[z0,z1,z2,z3,z398,z4,z6]),(0,[z0,z1,z2,z3,z4,z399,z6]),(0,[z0,z400,z1,z2,z3,z4,z6]),(0,[z0,z1,z78,z2,z99,z4,z6]),(0,[z0,z1,z2,z3,z4,z401,z93]),(0,[z0,z1,z3,z4,z18,z6,z402])],[(0,[z0,z1,z3,z4,z18,z97,z6]),(0,[z0,z376,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z403,z3,z4,z6]),(0,[z9,z0,z1,z2,z99,z4,z6]),(0,[z404,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z405])],[(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z407,z6])]],
   [[(0,[z408,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z409,z6]),(0,[z7,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z410,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z411]),(0,[z0,z1,z2,z3,z4,z93,z6]),(0,[z0,z1,z2,z3,z52,z93,z6])],[(0,[z0,z1,z2,z3,z412,z4,z6]),(0,[z0,z1,z2,z3,z413,z4,z6]),(0,[z0,z1,z2,z3,z414,z4,z6]),(0,[z10,z0,z1,z3,z74,z4,z6])],[(0,[z15,z0,z1,z2,z3,z4,z213]),(1,[z0,z1,z143,z3,z4,z6]),(0,[z0,z1,z415,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z416,z4,z6]),(0,[z10,z0,z1,z44,z3,z4,z6]),(0,[z0,z1,z2,z3,z417,z4,z6])],[(0,[z0,z1,z2,z3,z418,z4,z6])],[(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z420,z0,z1,z2,z3,z4,z6]),(0,[z10,z56,z0,z1,z3,z4,z6]),(0,[z9,z0,z1,z2,z3,z27,z6]),(0,[z10,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z52,z4,z94,z6]),(0,[z0,z1,z2,z3,z421,z4,z6])],[(0,[z224,z0,z1,z2,z3,z4,z57])],[(0,[z14,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z44,z36,z3,z4,z6]),(1,[z0,z384,z2,z3,z4,z6]),(0,[z108,z0,z1,z2,z3,z4,z16]),(0,[z87,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z422]),(0,[z10,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z423,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z424,z6]),(0,[z0,z1,z2,z3,z4,z6,z162]),(0,[z0,z1,z2,z425,z3,z4,z6])],[(0,[z272,z1,z136,z2,z3,z4,z6]),(1,[z0,z1,z342,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z426,z6]),(0,[z0,z1,z3,z4,z106,z18,z6]),(0,[z0,z1,z2,z3,z4,z427,z6])]],
   [[(0,[z1,z136,z2,z3,z184,z4,z6]),(0,[z428,z0,z1,z2,z3,z4,z6]),(0,[z429,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z93,z18,z6]),(0,[z430,z0,z1,z2,z3,z4,z6])],[(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z432,z3,z4,z6]),(0,[z0,z1,z2,z195,z3,z4,z6]),(0,[z433,z0,z1,z2,z3,z4,z6]),(0,[z108,z224,z1,z2,z3,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z435,z6]),(0,[z0,z1,z2,z3,z436,z4,z6]),(0,[z0,z1,z2,z3,z437,z4,z6]),(0,[z0,z1,z44,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z438]),(0,[z228,z10,z0,z1,z3,z4,z6])],[(0,[z107,z0,z1,z90,z3,z4,z6]),(1,[z7,z0,z2,z3,z115,z6]),(0,[z150,z0,z1,z2,z3,z4,z93]),(0,[z439,z0,z1,z2,z3,z4,z6])],[(0,[z440,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z2,z3,z8,z4,z6]),(0,[z0,z1,z2,z3,z4,z57,z30]),(0,[z0,z1,z2,z3,z74,z94,z6]),(1,[z228,z0,z1,z2,z94,z6]),(0,[z147,z0,z2,z3,z4,z94,z6])],[(0,[z0,z1,z195,z3,z4,z18,z6]),(0,[z441,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z16,z30])],[(0,[z224,z0,z1,z3,z4,z18,z6]),(0,[z0,z172,z1,z2,z3,z4,z6]),(0,[z442,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z443,z18,z6])],[(0,[z444,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z445]),(0,[z0,z1,z3,z4,z115,z18,z6]),(0,[z0,z446,z1,z3,z4,z6,z16]),(1,[z165,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z447,z4,z6]),(0,[z448,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z4,z6])],[(0,[z24,z0,z55,z2,z3,z4,z6]),(1,[z0,z1,z343,z3,z4,z6]),(0,[z80,z449,z1,z2,z3,z4,z6]),(0,[z0,z1,z450,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z52,z6])]],
   [[(0,[z10,z0,z1,z36,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z308]),(1,[z0,z446,z1,z3,z4,z6]),(0,[z0,z1,z78,z3,z4,z93,z6])],[(0,[z10,z211,z0,z1,z3,z4,z6]),(0,[z87,z0,z172,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z6,z278])],[(0,[z451,z0,z1,z2,z3,z4,z6]),(0,[z23,z1,z2,z3,z4,z177,z6]),(0,[z0,z1,z2,z452,z3,z4,z6]),(0,[z80,z33,z0,z2,z3,z4,z6]),(0,[z453,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z454,z4,z6])],[(1,[z0,z1,z2,z3,z164,z6]),(0,[z0,z1,z2,z3,z4,z6,z455]),(0,[z0,z1,z456,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z457]),(0,[z0,z1,z2,z3,z74,z52,z6])],[(0,[z107,z1,z2,z3,z4,z97,z6]),(0,[z108,z1,z2,z195,z3,z4,z6]),(0,[z87,z0,z2,z3,z102,z4,z6]),(0,[z56,z0,z1,z3,z4,z18,z6])],[(0,[z212,z0,z1,z2,z3,z6,z16])],[(0,[z458,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z459,z6]),(0,[z460,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z461,z6]),(0,[z0,z165,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z377,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z6,z241])],[(1,[z0,z1,z2,z3,z4,z336]),(0,[z56,z33,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z16])]],
   [[(0,[z222,z0,z1,z3,z4,z18,z6])],[(0,[z10,z0,z1,z35,z3,z4,z6]),(0,[z108,z0,z384,z2,z3,z4,z6]),(0,[z0,z1,z2,z462,z3,z4,z6]),(1,[z0,z1,z88,z3,z4,z6]),(0,[z0,z1,z2,z3,z8,z4,z6]),(0,[z33,z0,z1,z161,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z463])],[(0,[z0,z1,z2,z464,z3,z4,z6]),(0,[z0,z1,z465,z2,z3,z4,z6]),(0,[z466,z0,z1,z2,z3,z4,z6])],[(0,[z467,z0,z1,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z4,z6])],[(0,[z14,z15,z0,z2,z3,z4,z6]),(0,[z224,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z468,z6]),(0,[z469,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z470,z3,z4,z6])],[(0,[z0,z1,z3,z4,z181,z18,z6]),(0,[z0,z1,z471,z2,z3,z4,z6])],[(0,[z472,z0,z1,z2,z3,z4,z6]),(0,[z80,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z71,z3,z259,z6])],[(0,[z0,z1,z2,z3,z4,z6,z223]),(0,[z0,z1,z2,z3,z4,z473,z6]),(0,[z0,z1,z2,z3,z4,z474,z6]),(0,[z0,z1,z475,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z476,z4,z6]),(1,[z0,z1,z2,z3,z4,z401]),(0,[z0,z1,z2,z3,z477,z4,z6]),(0,[z0,z1,z2,z3,z111,z4,z6])]],
   [[(1,[z0,z1,z116,z3,z4,z6]),(1,[z33,z0,z2,z3,z4,z57]),(0,[z0,z1,z478,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z479])],[(0,[z0,z1,z2,z3,z4,z480,z6]),(0,[z0,z1,z2,z3,z4,z180,z77]),(1,[z356,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z481,z3,z4,z6]),(0,[z0,z1,z196,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z6,z261]),(0,[z17,z0,z1,z2,z3,z4,z12])],[(0,[z0,z1,z2,z3,z482,z4,z6]),(1,[z0,z1,z2,z3,z4,z397]),(0,[z0,z1,z2,z46,z109,z4,z6]),(0,[z7,z0,z26,z2,z3,z4,z6]),(0,[z483,z0,z1,z2,z3,z4,z6]),(0,[z484,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z485,z6]),(0,[z10,z0,z1,z3,z4,z94,z6]),(0,[z0,z486,z1,z2,z3,z4,z6]),(0,[z469,z0,z1,z3,z4,z6,z30]),(0,[z487,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z488,z2,z3,z4,z6])],[(0,[z15,z0,z2,z3,z4,z6,z16]),(0,[z80,z0,z123,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z358,z6]),(0,[z56,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z130,z3,z4,z6]),(0,[z489,z0,z1,z2,z3,z4,z6]),(0,[z490,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z491,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z492,z4,z6]),(0,[z0,z1,z2,z3,z493,z4,z6]),(0,[z0,z2,z109,z3,z8,z4,z6]),(0,[z0,z1,z230,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z494,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z495]),(0,[z0,z1,z2,z3,z52,z8,z6]),(1,[z0,z1,z3,z4,z6,z162])],[(0,[z10,z0,z1,z3,z184,z4,z6]),(1,[z0,z1,z2,z3,z4,z496]),(0,[z0,z1,z2,z497,z3,z4,z6]),(0,[z498,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z499])],[(0,[z222,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z500,z3,z4,z6]),(1,[z0,z137,z2,z3,z4,z6]),(0,[z501,z0,z1,z2,z3,z4,z6]),(0,[z502,z0,z1,z2,z3,z4,z6]),(1,[z147,z0,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z503,z3,z4,z6]),(0,[z107,z0,z1,z2,z3,z319,z6]),(0,[z504,z0,z1,z2,z3,z4,z6])],[(0,[z0,z356,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z505])],[(0,[z0,z172,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z506,z6]),(0,[z0,z1,z2,z3,z507,z4,z6]),(0,[z0,z1,z2,z508,z3,z4,z6]),(1,[z67,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z509,z6]),(0,[z10,z510,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z30])],[(0,[z15,z0,z172,z2,z3,z4,z6]),(0,[z87,z376,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z180,z6]),(0,[z0,z511,z1,z2,z3,z4,z6])],[(0,[z7,z0,z136,z2,z3,z4,z6]),(0,[z0,z1,z121,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z6,z77]),(0,[z10,z0,z1,z71,z3,z4,z6])],[(0,[z512,z0,z1,z2,z3,z4,z6]),(0,[z15,z1,z136,z2,z3,z4,z6]),(0,[z513,z0,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z144,z6]),(0,[z514,z0,z1,z2,z3,z4,z6]),(0,[z0,z48,z1,z123,z3,z4,z6]),(0,[z0,z2,z109,z3,z102,z4,z6]),(0,[z0,z1,z2,z515,z3,z4,z6])],[(0,[z0,z1,z516,z2,z3,z4,z6]),(0,[z80,z396,z1,z2,z3,z4,z6]),(0,[z0,z172,z1,z2,z102,z4,z6]),(0,[z0,z172,z2,z109,z3,z4,z6]),(0,[z0,z1,z109,z3,z4,z18,z6])],[(0,[z0,z1,z2,z3,z4,z517,z6]),(0,[z518,z0,z1,z2,z3,z4,z6]),(0,[z0,z519,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z520,z2,z3,z4,z6]),(0,[z7,z0,z2,z109,z3,z4,z6]),(0,[z521,z0,z1,z2,z3,z4,z6]),(0,[z149,z10,z0,z1,z3,z4,z6]),(0,[z10,z0,z1,z2,z3,z4,z18]),(0,[z0,z1,z2,z3,z4,z332,z6]),(0,[z0,z1,z2,z4,z180,z6,z12])],[(0,[z0,z522,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z523]),(0,[z0,z1,z2,z3,z524,z4,z6]),(0,[z0,z1,z2,z3,z525,z4,z6])],[(0,[z0,z1,z526,z2,z3,z4,z6]),(0,[z0,z26,z1,z3,z4,z18,z6]),(0,[z10,z0,z1,z3,z4,z93,z6]),(0,[z0,z1,z2,z527,z3,z4,z6]),(0,[z0,z1,z2,z3,z528,z4,z6])],[(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z530,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z354,z16]),(0,[z0,z1,z2,z3,z4,z57,z117]),(0,[z0,z1,z2,z3,z4,z6,z531]),(0,[z0,z1,z2,z3,z94,z117,z6]),(0,[z0,z1,z71,z3,z191,z4,z6]),(0,[z0,z532,z1,z2,z3,z4,z6])],[(1,[z449,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z533]),(0,[z7,z0,z1,z2,z335,z4,z6]),(1,[z0,z1,z2,z3,z163,z6])],[(0,[z534,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z535,z4,z6]),(0,[z10,z72,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z536,z4,z6]),(0,[z108,z0,z1,z2,z3,z4,z97]),(0,[z0,z1,z537,z2,z3,z4,z6]),(0,[z0,z1,z2,z538,z3,z4,z6]),(0,[z0,z539,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z540,z3,z4,z6]),(0,[z0,z1,z2,z3,z541,z4,z6]),(0,[z0,z1,z203,z2,z3,z4,z6]),(0,[z0,z1,z542,z2,z3,z4,z6]),(1,[z80,z0,z123,z3,z4,z6]),(0,[z0,z1,z2,z481,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z543,z6]),(0,[z0,z1,z2,z544,z3,z4,z6])],[(0,[z23,z10,z0,z1,z3,z4,z6]),(0,[z545,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z143,z3,z4,z6]),(0,[z0,z1,z59,z2,z3,z4,z278]),(0,[z546,z0,z1,z2,z3,z4,z6]),(0,[z166,z0,z1,z3,z4,z6,z12])]],
   [[(0,[z0,z1,z231,z2,z3,z4,z6]),(0,[z80,z0,z48,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z547]),(0,[z0,z1,z2,z3,z4,z548,z6]),(0,[z0,z549,z1,z2,z3,z4,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z424,z6])],[(0,[z0,z1,z2,z168,z3,z4,z6]),(0,[z551,z0,z1,z2,z3,z4,z6]),(0,[z0,z26,z1,z2,z3,z115,z6]),(0,[z0,z1,z2,z3,z4,z552,z6]),(0,[z0,z1,z2,z3,z4,z553,z6]),(0,[z190,z10,z0,z1,z3,z4,z6]),(1,[z17,z0,z1,z2,z4,z12])],[(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z555]),(0,[z0,z1,z2,z46,z52,z4,z6])],[(0,[z556,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z195,z3,z4,z6]),(0,[z0,z557,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z558,z6]),(0,[z0,z1,z2,z3,z4,z6,z336]),(0,[z0,z559,z1,z2,z3,z4,z6]),(0,[z0,z1,z560,z2,z3,z4,z6])],[(0,[z0,z449,z1,z2,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6])],[(0,[z10,z0,z1,z136,z3,z4,z6]),(0,[z0,z1,z2,z3,z562,z4,z6]),(0,[z563,z0,z1,z2,z3,z4,z6]),(0,[z0,z564,z1,z2,z3,z4,z6]),(0,[z0,z1,z230,z71,z3,z4,z6])],[(0,[z224,z0,z1,z2,z3,z4,z97]),(0,[z0,z1,z2,z3,z4,z565,z6]),(0,[z0,z1,z2,z3,z358,z4,z6]),(0,[z0,z1,z566,z2,z3,z4,z6]),(0,[z10,z0,z26,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z567,z6]),(0,[z0,z1,z2,z3,z52,z117,z6]),(0,[z0,z1,z2,z3,z4,z117,z6])],[(0,[z568,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z569,z3,z4,z6]),(0,[z210,z0,z1,z3,z4,z18,z6]),(0,[z108,z0,z1,z2,z3,z4,z57]),(0,[z0,z1,z2,z570,z3,z4,z6]),(0,[z10,z0,z1,z2,z3,z4,z57]),(0,[z0,z571,z1,z2,z3,z4,z6]),(0,[z572,z0,z1,z2,z3,z4,z6]),(0,[z573,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z574])]],
   [[(0,[z15,z0,z1,z3,z4,z18,z6]),(0,[z575,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z480,z6]),(0,[z0,z1,z2,z576,z3,z4,z6]),(0,[z0,z1,z3,z74,z4,z93,z6])],[(0,[z10,z15,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z577]),(0,[z0,z1,z3,z578,z4,z18,z6])],[(0,[z0,z1,z2,z3,z4,z6,z579]),(0,[z0,z1,z2,z3,z4,z401,z6]),(1,[z0,z1,z313,z3,z4,z6]),(0,[z0,z1,z2,z3,z117,z6,z30])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z580,z0,z1,z2,z3,z4,z6]),(0,[z107,z72,z1,z2,z3,z4,z6]),(0,[z108,z0,z520,z2,z3,z4,z6]),(0,[z0,z48,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z581])],[(0,[z0,z1,z2,z3,z582,z4,z6]),(0,[z224,z0,z1,z2,z3,z4,z77]),(0,[z583,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z584,z6]),(1,[z0,z1,z2,z46,z52,z6])],[(0,[z585,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z4,z308]),(0,[z173,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z586,z3,z4,z6]),(0,[z587,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z588,z4,z6]),(1,[z108,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z3,z4,z6,z397]),(0,[z0,z1,z2,z3,z4,z443,z6]),(0,[z10,z0,z1,z78,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z589])],[(0,[z0,z1,z2,z3,z4,z590,z6]),(1,[z0,z1,z284,z3,z4,z6]),(0,[z108,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z6,z591]),(0,[z17,z0,z1,z2,z3,z4,z180])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z592]),(0,[z0,z1,z2,z3,z4,z57,z6]),(0,[z33,z0,z1,z2,z3,z4,z16]),(0,[z0,z1,z2,z71,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z6,z593])],[(0,[z15,z272,z0,z2,z3,z4,z6]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z107,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z595,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z6,z16]),(1,[z10,z0,z1,z3,z4,z278]),(0,[z596,z0,z1,z3,z4,z18,z6])],[(0,[z0,z1,z2,z3,z4,z6,z496]),(0,[z0,z1,z2,z3,z597,z4,z6]),(0,[z0,z1,z598,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z94,z6]),(0,[z133,z1,z2,z3,z4,z6,z12])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z210,z0,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z599]),(0,[z0,z1,z2,z3,z600,z4,z6]),(0,[z10,z0,z1,z3,z8,z4,z6]),(1,[z469,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z601,z4,z6])],[(0,[z24,z0,z1,z2,z3,z144,z6]),(0,[z0,z1,z2,z3,z602,z4,z6])],[(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z603,z4,z6]),(0,[z0,z1,z2,z3,z4,z604,z6]),(0,[z0,z1,z605,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z606]),(0,[z56,z0,z1,z2,z3,z4,z57]),(0,[z150,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z607,z0,z1,z2,z3,z4,z6]),(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z7,z0,z1,z29,z3,z4,z6]),(0,[z609,z0,z1,z2,z3,z4,z6])],[(0,[z10,z0,z1,z3,z111,z4,z6])],[(0,[z72,z1,z136,z2,z3,z4,z6]),(0,[z0,z1,z3,z8,z4,z18,z6]),(0,[z0,z1,z3,z4,z18,z6,z12])],[(0,[z610,z0,z1,z2,z3,z4,z6]),(1,[z396,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z180,z6]),(0,[z0,z1,z611,z2,z3,z4,z6]),(0,[z0,z612,z1,z2,z3,z4,z6])],[(0,[z210,z0,z1,z35,z3,z4,z6]),(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z102,z4,z6]),(0,[z614,z0,z1,z3,z4,z18,z6])],[(0,[z107,z0,z1,z121,z3,z4,z6]),(1,[z0,z1,z481,z3,z4,z6]),(0,[z0,z1,z2,z3,z8,z94,z6]),(0,[z0,z1,z44,z2,z3,z93,z6]),(0,[z0,z1,z3,z74,z4,z18,z6]),(0,[z615,z0,z1,z2,z3,z4,z6])],[(0,[z108,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z480,z6,z77]),(0,[z0,z1,z2,z616,z3,z4,z6]),(0,[z617,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z109,z4,z6]),(0,[z7,z0,z1,z2,z3,z117,z6]),(0,[z9,z0,z1,z2,z3,z170,z6]),(0,[z10,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z618,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z619]),(0,[z620,z0,z1,z2,z3,z4,z6]),(0,[z621,z0,z1,z2,z3,z4,z6]),(0,[z622,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z168,z3,z4,z6]),(0,[z0,z1,z2,z623,z3,z4,z6]),(0,[z0,z1,z2,z3,z624,z4,z6]),(0,[z0,z1,z625,z2,z3,z4,z6]),(0,[z596,z0,z1,z2,z3,z4,z6])],[(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z627,z6]),(0,[z0,z1,z2,z628,z3,z4,z6])],[(0,[z0,z1,z2,z3,z629,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z630]),(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z632,z2,z3,z4,z6]),(0,[z33,z0,z2,z3,z4,z57,z6]),(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z71,z3,z4,z18,z6])],[(0,[z634,z0,z1,z2,z3,z4,z6]),(0,[z635,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z3,z4,z496]),(0,[z273,z10,z0,z1,z3,z4,z6]),(0,[z63,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z94,z18,z6])],[(0,[z636,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z6,z30])],[(0,[z272,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z637,z4,z6])],[(0,[z0,z1,z2,z3,z638,z4,z6])],[(0,[z14,z1,z2,z3,z4,z97,z6]),(0,[z0,z1,z2,z639,z3,z4,z6])]],
   [[(0,[z0,z1,z35,z3,z99,z4,z6]),(0,[z10,z224,z0,z1,z3,z4,z6]),(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z43,z0,z1,z2,z3,z74,z6]),(0,[z293,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z402]),(0,[z0,z1,z2,z3,z4,z6,z640])],[(1,[z211,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z641,z6]),(0,[z0,z1,z2,z3,z4,z97,z6]),(0,[z0,z1,z2,z3,z4,z6,z642]),(0,[z17,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z46,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z643,z6])],[(0,[z0,z644,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z645]),(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z123,z2,z79,z3,z4,z6]),(0,[z0,z1,z2,z647,z3,z4,z6]),(0,[z10,z33,z0,z1,z3,z4,z6]),(0,[z510,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z578,z4,z6])],[(0,[z80,z0,z1,z123,z3,z4,z6]),(0,[z0,z1,z2,z3,z648,z4,z6]),(0,[z614,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z649,z6])],[(0,[z24,z1,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z650,z4,z6]),(0,[z107,z1,z2,z3,z184,z4,z6]),(0,[z0,z651,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z652,z3,z4,z6])],[(0,[z24,z1,z2,z3,z144,z4,z6]),(0,[z653,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z127,z6]),(0,[z0,z1,z59,z2,z3,z111,z4])],[(0,[z654,z0,z1,z2,z3,z4,z6]),(0,[z14,z0,z136,z2,z3,z4,z6]),(0,[z655,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z35,z44,z3,z4,z6]),(0,[z0,z1,z3,z4,z177,z18,z6]),(0,[z0,z1,z2,z3,z656,z4,z6]),(0,[z0,z1,z2,z657,z3,z4,z6]),(0,[z658,z0,z1,z2,z3,z4,z6]),(1,[z10,z63,z0,z3,z4,z6])],[(0,[z0,z1,z2,z659,z3,z4,z6]),(0,[z0,z1,z35,z78,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z660,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z661,z6]),(1,[z0,z1,z2,z3,z259,z6])]],
   [[(0,[z0,z1,z35,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z662,z4,z6]),(1,[z0,z1,z2,z335,z4,z6]),(0,[z0,z1,z2,z119,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z4,z127]),(0,[z312,z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z663])],[(0,[z211,z0,z1,z123,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z664]),(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z1,z2,z195,z3,z184,z4,z6]),(0,[z87,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z666,z6]),(0,[z0,z1,z2,z3,z4,z115,z6]),(0,[z0,z1,z2,z3,z52,z115,z6]),(0,[z0,z1,z667,z2,z3,z4,z6]),(0,[z43,z10,z0,z1,z3,z4,z6]),(0,[z314,z10,z0,z1,z3,z4,z6])],[(0,[z14,z211,z1,z2,z3,z4,z6]),(1,[z0,z1,z231,z3,z4,z6]),(0,[z0,z1,z2,z3,z668,z4,z6]),(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z228,z0,z1,z2,z4,z94,z6])],[(0,[z0,z1,z2,z3,z4,z670,z6]),(0,[z107,z0,z203,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z671,z4,z6]),(0,[z0,z1,z2,z3,z4,z672,z6])],[(0,[z272,z0,z1,z2,z3,z4,z6]),(0,[z228,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z135,z2,z3,z4,z6])],[(0,[z673,z0,z1,z2,z3,z4,z6]),(0,[z391,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z319,z6]),(0,[z23,z0,z1,z342,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z674]),(0,[z0,z1,z2,z675,z3,z4,z6]),(0,[z0,z1,z59,z3,z4,z18,z6]),(1,[z133,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z676,z4,z6]),(0,[z0,z1,z2,z3,z4,z677,z6]),(0,[z0,z1,z2,z3,z4,z77,z12]),(0,[z0,z1,z2,z678,z3,z4,z6]),(0,[z0,z1,z2,z71,z3,z4,z180])],[(0,[z14,z1,z2,z3,z4,z177,z6]),(0,[z0,z1,z2,z679,z3,z4,z6]),(0,[z0,z1,z680,z2,z3,z4,z6]),(0,[z0,z681,z1,z2,z3,z4,z6]),(0,[z0,z1,z59,z2,z3,z4,z16]),(0,[z0,z1,z3,z4,z18,z18,z6]),(0,[z0,z1,z682,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z683,z4,z6]),(0,[z10,z0,z1,z3,z4,z117,z6])],[(0,[z0,z1,z3,z4,z18,z6,z16]),(0,[z0,z1,z2,z3,z158,z4,z6])],[(0,[z0,z1,z3,z4,z6,z198,z30])],[(1,[z210,z1,z35,z3,z4,z6]),(0,[z0,z1,z2,z90,z3,z4,z6]),(0,[z0,z1,z520,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z474,z18,z6])],[(0,[z684,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z179,z6]),(0,[z0,z1,z2,z3,z4,z685,z6]),(0,[z686,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z196,z3,z4,z6])],[(0,[z687,z0,z1,z2,z3,z4,z6]),(0,[z1,z136,z2,z3,z4,z97,z6]),(0,[z14,z1,z35,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z155,z6]),(0,[z72,z1,z2,z195,z3,z4,z6]),(0,[z224,z1,z2,z3,z4,z97,z6]),(0,[z33,z0,z1,z116,z3,z4,z6]),(0,[z10,z0,z1,z59,z3,z4,z6])],[(0,[z0,z1,z2,z3,z688,z4,z6])],[(0,[z0,z1,z689,z2,z3,z4,z6]),(0,[z0,z1,z35,z2,z3,z4,z6]),(1,[z0,z172,z2,z109,z4,z6]),(0,[z9,z0,z1,z2,z130,z4,z6]),(0,[z690,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z691,z3,z4,z6]),(1,[z10,z0,z1,z3,z111,z4]),(0,[z0,z1,z2,z3,z4,z6,z692])]],
   [[(0,[z87,z0,z1,z2,z3,z4,z6])],[(0,[z80,z0,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z693,z3,z4,z6])],[(0,[z0,z1,z2,z3,z694,z4,z6]),(0,[z695,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z6,z354]),(0,[z10,z0,z1,z3,z4,z57,z6]),(0,[z228,z0,z1,z313,z3,z4,z6])],[(0,[z696,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z697,z4,z6]),(0,[z228,z0,z1,z2,z3,z4,z6]),(0,[z228,z0,z1,z2,z46,z4,z6]),(0,[z698,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z699,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z6,z278]),(0,[z228,z0,z1,z2,z3,z52,z6]),(0,[z0,z1,z2,z3,z4,z700,z6]),(0,[z0,z1,z2,z3,z701,z4,z6])],[(1,[z0,z1,z2,z3,z4,z263]),(1,[z114,z0,z2,z3,z4,z6]),(1,[z49,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z702,z4,z6]),(0,[z0,z1,z2,z200,z3,z4,z6])],[(0,[z14,z272,z1,z2,z3,z4,z6]),(0,[z108,z0,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z70,z3,z4,z6]),(0,[z0,z1,z703,z2,z3,z4,z6])],[(0,[z211,z0,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z704,z3,z4,z6]),(0,[z0,z1,z705,z2,z3,z4,z6]),(1,[z107,z1,z2,z184,z4,z6]),(0,[z0,z1,z2,z706,z3,z4,z6]),(0,[z0,z1,z2,z79,z3,z4,z6]),(1,[z0,z1,z59,z3,z4,z18])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z6]),(0,[z0,z1,z2,z3,z4,z127]),(0,[z133,z708,z2,z3,z4,z6])],[(0,[z10,z0,z1,z3,z4,z379]),(0,[z14,z451,z2,z3,z4,z6]),(0,[z0,z1,z709,z3,z4,z6]),(0,[z10,z114,z0,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z531]),(0,[z0,z1,z3,z4,z18,z315])],[(0,[z114,z136,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z710,z6]),(0,[z203,z2,z3,z184,z4,z6]),(0,[z0,z1,z711,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z533]),(0,[z10,z0,z1,z3,z4,z712]),(0,[z0,z1,z135,z3,z4,z6]),(0,[z25,z0,z1,z2,z3,z713])],[(0,[z0,z1,z2,z714,z4,z6]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z212,z10,z0,z1,z3,z16])],[(0,[z0,z1,z44,z3,z494,z6]),(1,[z1,z2,z3,z716,z6]),(0,[z150,z0,z1,z79,z3,z4]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z0,z718,z2,z3,z4,z6])],[(0,[z673,z0,z1,z99,z4,z6]),(0,[z24,z1,z2,z3,z144,z6]),(0,[z24,z1,z2,z3,z716,z6]),(0,[z0,z1,z2,z119,z4,z336]),(0,[z0,z1,z2,z3,z117,z336]),(0,[z0,z1,z59,z3,z4,z84]),(0,[z0,z1,z130,z719,z4,z6]),(0,[z133,z1,z3,z4,z18,z6]),(0,[z0,z1,z720,z3,z4,z6])],[(0,[z721,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z547]),(0,[z0,z1,z722,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z155]),(0,[z211,z1,z516,z3,z4,z6]),(0,[z0,z1,z3,z723,z4,z6]),(0,[z0,z1,z724,z3,z4,z6]),(0,[z10,z0,z1,z3,z354,z16])]],
   [[(0,[z0,z1,z725,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z213]),(0,[z211,z1,z36,z3,z4,z6]),(0,[z0,z137,z2,z3,z4,z263]),(0,[z0,z726,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z426]),(0,[z10,z165,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z727,z6]),(0,[z728,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z360,z0,z196,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z555]),(0,[z0,z1,z2,z3,z6,z713])],[(0,[z0,z1,z90,z3,z164,z6]),(0,[z107,z1,z2,z730,z4,z6]),(0,[z449,z1,z2,z3,z4,z81]),(0,[z0,z1,z3,z4,z18,z81]),(0,[z0,z731,z1,z3,z4,z6]),(0,[z212,z0,z1,z2,z3,z30]),(0,[z9,z0,z1,z99,z27,z6])],[(0,[z0,z732,z2,z3,z4,z6]),(0,[z108,z1,z2,z3,z4,z364]),(0,[z150,z0,z1,z3,z4,z18])],[(0,[z733,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z734]),(0,[z735,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z736,z223]),(0,[z0,z737,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z738,z336]),(0,[z10,z0,z196,z3,z4,z474]),(0,[z0,z1,z230,z3,z163,z6])],[(0,[z0,z1,z2,z3,z4,z739]),(0,[z0,z1,z2,z3,z740,z6]),(0,[z0,z1,z3,z4,z741,z6]),(0,[z1,z2,z3,z4,z6,z742]),(0,[z743,z1,z2,z3,z4,z6]),(0,[z159,z0,z1,z2,z94,z6]),(0,[z173,z1,z2,z119,z4,z6]),(0,[z0,z1,z29,z335,z4,z6]),(0,[z0,z1,z2,z3,z117,z581]),(0,[z0,z1,z70,z99,z4,z6]),(0,[z10,z63,z0,z3,z4,z6]),(0,[z0,z1,z744,z3,z4,z6])],[(0,[z0,z1,z2,z745,z4,z6]),(0,[z211,z1,z746,z3,z4,z6]),(0,[z63,z0,z116,z3,z4,z6]),(0,[z747,z10,z63,z3,z4,z6]),(0,[z0,z1,z2,z3,z259,z6])],[(0,[z0,z1,z3,z4,z748,z155]),(0,[z10,z0,z1,z3,z4,z577]),(0,[z0,z203,z2,z3,z4,z223]),(0,[z749,z0,z2,z3,z4,z6]),(0,[z356,z1,z2,z119,z4,z6]),(0,[z56,z0,z2,z3,z354,z16]),(0,[z67,z1,z161,z3,z4,z6]),(0,[z0,z1,z750,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z751,z6]),(0,[z0,z1,z2,z3,z4,z752]),(0,[z0,z1,z2,z3,z753,z6]),(0,[z212,z10,z0,z1,z3,z6])],[(0,[z0,z1,z231,z3,z4,z6]),(0,[z0,z1,z3,z4,z736,z6]),(0,[z10,z0,z1,z3,z4,z581]),(0,[z10,z0,z1,z3,z4,z401]),(0,[z0,z1,z2,z3,z754,z6]),(0,[z17,z0,z1,z2,z4,z755])],[(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z757,z6]),(0,[z49,z1,z2,z3,z179,z6]),(0,[z67,z10,z1,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z755])],[(0,[z0,z1,z758,z3,z4,z6]),(0,[z0,z1,z2,z3,z759,z6]),(0,[z0,z1,z335,z4,z18,z6]),(0,[z150,z0,z1,z3,z99,z4]),(0,[z150,z0,z1,z2,z3,z52]),(0,[z0,z1,z2,z3,z4,z760])],[(0,[z0,z1,z2,z3,z319,z6]),(0,[z133,z1,z2,z3,z4,z6]),(0,[z0,z1,z761,z3,z4,z6]),(0,[z0,z116,z79,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z397])],[(0,[z212,z0,z136,z2,z3,z6]),(0,[z0,z1,z3,z719,z4,z6]),(0,[z10,z0,z1,z3,z4,z762])],[(0,[z10,z0,z1,z3,z4,z592]),(0,[z636,z1,z36,z3,z4,z6]),(0,[z114,z0,z763,z3,z4,z6]),(0,[z0,z1,z764,z3,z4,z6]),(0,[z10,z765,z1,z3,z4,z6])],[(0,[z25,z10,z0,z1,z3,z158])]],
   [[(0,[z114,z0,z2,z3,z4,z766]),(0,[z114,z0,z2,z3,z4,z767]),(0,[z80,z0,z446,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z496]),(0,[z768,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z769,z6]),(0,[z56,z0,z2,z3,z4,z770]),(0,[z10,z56,z0,z3,z4,z16]),(0,[z771,z0,z2,z3,z4,z6])],[(0,[z0,z172,z109,z4,z18,z6]),(0,[z63,z0,z2,z3,z4,z57]),(0,[z120,z0,z2,z3,z4,z57]),(0,[z0,z1,z3,z4,z18,z348]),(0,[z0,z772,z2,z3,z4,z6])],[(0,[z212,z0,z1,z3,z84,z6]),(0,[z0,z1,z230,z3,z4,z6]),(0,[z0,z1,z44,z3,z74,z6]),(0,[z25,z10,z0,z1,z3,z111])],[(0,[z773,z0,z1,z3,z4,z6]),(0,[z0,z1,z168,z3,z4,z155]),(0,[z0,z2,z109,z8,z94,z6]),(0,[z229,z0,z2,z3,z4,z16]),(0,[z0,z1,z78,z130,z4,z6]),(0,[z0,z1,z3,z27,z18,z6]),(0,[z10,z0,z1,z3,z4,z661]),(0,[z0,z1,z611,z3,z74,z6])],[(0,[z211,z1,z540,z3,z4,z6]),(0,[z0,z1,z774,z3,z4,z6]),(0,[z0,z137,z90,z3,z4,z6]),(0,[z107,z1,z2,z184,z4,z263]),(0,[z775,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z776,z4,z6]),(0,[z0,z1,z3,z578,z181,z6]),(0,[z0,z777,z2,z3,z4,z6])],[(0,[z0,z172,z2,z109,z4,z6]),(0,[z0,z196,z3,z4,z93,z6]),(0,[z10,z0,z1,z3,z111,z4]),(0,[z10,z0,z1,z3,z578,z4]),(0,[z0,z1,z46,z52,z18,z6]),(0,[z0,z1,z778,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z779]),(0,[z0,z1,z2,z3,z780,z6]),(0,[z0,z1,z781,z3,z4,z6])]],
   [[(0,[z0,z1,z782,z3,z4,z6]),(0,[z87,z0,z102,z4,z18,z6]),(0,[z442,z10,z0,z1,z3,z4]),(0,[z0,z1,z131,z3,z4,z6]),(0,[z0,z1,z783,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z784]),(0,[z0,z1,z785,z3,z4,z6]),(0,[z0,z1,z481,z335,z4,z6]),(0,[z0,z1,z2,z3,z6,z354]),(0,[z56,z0,z3,z4,z18,z16])],[(0,[z0,z1,z3,z4,z18,z194]),(0,[z0,z1,z3,z4,z786,z6]),(0,[z0,z1,z787,z3,z4,z6]),(0,[z0,z48,z196,z3,z4,z6]),(0,[z0,z1,z3,z358,z18,z6]),(0,[z788,z0,z1,z2,z3,z6]),(0,[z7,z0,z2,z3,z753,z6]),(0,[z212,z10,z0,z1,z3,z4]),(0,[z439,z0,z2,z3,z4,z16]),(0,[z0,z196,z3,z251,z4,z6]),(0,[z63,z0,z3,z4,z18,z6]),(0,[z747,z1,z2,z3,z4,z6])],[(0,[z0,z1,z789,z3,z4,z6]),(0,[z790,z0,z1,z2,z3,z4])],[(0,[z0,z791,z1,z3,z4,z6]),(0,[z792,z0,z1,z3,z4,z6]),(0,[z793,z1,z2,z3,z4,z6]),(0,[z10,z0,z196,z3,z111,z4]),(0,[z25,z10,z0,z1,z3,z30]),(0,[z0,z331,z3,z4,z474,z6])],[(0,[z0,z137,z121,z3,z4,z6]),(0,[z794,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z335,z4,z127]),(0,[z0,z1,z3,z795,z4,z6])],[(0,[z796,z0,z1,z3,z4,z6]),(0,[z0,z797,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z163,z6]),(0,[z0,z1,z59,z3,z4,z18])],[(0,[z14,z1,z231,z3,z4,z6]),(0,[z1,z746,z2,z3,z4,z6]),(0,[z0,z798,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z274]),(0,[z0,z1,z2,z3,z799,z6])]],
   [[(0,[z721,z272,z2,z3,z4,z6]),(0,[z0,z1,z161,z3,z4,z6]),(0,[z0,z1,z2,z3,z800,z6]),(0,[z0,z1,z2,z3,z683,z117]),(0,[z0,z1,z78,z719,z4,z6]),(0,[z0,z1,z2,z801,z4,z6])],[(0,[z0,z1,z2,z3,z4,z802]),(0,[z10,z0,z384,z3,z4,z6]),(0,[z449,z2,z3,z4,z6,z16]),(0,[z7,z173,z2,z3,z115,z6]),(0,[z63,z803,z2,z3,z4,z6])],[(0,[z804,z0,z1,z3,z4,z6]),(0,[z510,z1,z35,z3,z4,z6]),(0,[z0,z805,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z806]),(0,[z212,z56,z0,z2,z3,z16]),(0,[z10,z63,z0,z3,z4,z18])],[(0,[z0,z1,z2,z3,z4,z807]),(0,[z0,z1,z2,z3,z808,z6]),(0,[z0,z1,z3,z4,z809,z6]),(0,[z0,z1,z2,z3,z716,z6]),(0,[z80,z10,z0,z3,z4,z16]),(0,[z810,z0,z1,z3,z4,z308]),(0,[z0,z196,z3,z99,z4,z6])],[(0,[z0,z136,z2,z335,z4,z6]),(0,[z545,z10,z0,z1,z3,z4]),(0,[z80,z396,z123,z3,z4,z6]),(0,[z0,z1,z2,z3,z811,z6]),(0,[z0,z1,z812,z3,z4,z6]),(0,[z813,z0,z1,z3,z4,z127]),(0,[z814,z1,z2,z3,z4,z6])],[(0,[z272,z136,z3,z4,z18,z6]),(0,[z290,z136,z2,z3,z4,z6]),(0,[z0,z815,z2,z3,z4,z6]),(0,[z10,z224,z1,z3,z4,z97]),(0,[z0,z1,z3,z4,z816,z6]),(0,[z0,z1,z3,z817,z4,z6]),(0,[z0,z1,z3,z4,z18,z818])],[(0,[z0,z1,z231,z3,z4,z155]),(0,[z108,z10,z1,z3,z4,z77]),(0,[z10,z0,z196,z3,z4,z16]),(0,[z0,z1,z3,z191,z4,z6]),(0,[z0,z1,z3,z4,z819,z6]),(0,[z25,z0,z1,z3,z18,z30]),(0,[z820,z1,z2,z3,z4,z6])],[(0,[z0,z1,z821,z3,z4,z6]),(0,[z211,z1,z595,z3,z4,z6]),(0,[z210,z1,z362,z3,z4,z6]),(0,[z466,z0,z1,z2,z4,z12]),(0,[z87,z0,z2,z822,z4,z6]),(0,[z0,z1,z3,z823,z4,z6]),(0,[z67,z33,z2,z3,z4,z57]),(0,[z0,z1,z3,z4,z824,z6])]],
   [[(0,[z10,z0,z1,z3,z4,z223]),(0,[z0,z825,z79,z3,z4,z6]),(0,[z0,z1,z3,z4,z826,z6]),(0,[z56,z0,z2,z3,z4,z16]),(0,[z150,z0,z1,z2,z3,z94]),(0,[z25,z0,z1,z2,z3,z424])],[(0,[z563,z136,z2,z3,z4,z6]),(0,[z72,z1,z2,z569,z4,z6]),(0,[z0,z827,z2,z3,z4,z6]),(0,[z63,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z119,z4,z6]),(0,[z10,z0,z1,z3,z4,z84]),(0,[z212,z0,z1,z2,z3,z117]),(0,[z0,z1,z3,z4,z6,z198]),(0,[z0,z196,z44,z3,z4,z6])],[(0,[z388,z136,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z828,z213]),(0,[z0,z1,z2,z3,z829,z6]),(0,[z108,z203,z2,z3,z4,z6]),(0,[z107,z1,z90,z184,z4,z6]),(0,[z80,z0,z116,z3,z4,z6]),(0,[z0,z196,z78,z3,z4,z6])],[(0,[z0,z1,z2,z3,z830,z6]),(0,[z0,z1,z2,z3,z831,z6]),(0,[z0,z1,z832,z3,z4,z6]),(0,[z0,z196,z3,z4,z18,z6]),(0,[z10,z0,z797,z3,z4,z6]),(0,[z614,z0,z1,z3,z6,z402])],[(0,[z0,z1,z186,z3,z4,z16]),(0,[z87,z0,z2,z102,z4,z496]),(0,[z0,z1,z116,z3,z4,z16]),(0,[z10,z0,z3,z4,z57,z16]),(0,[z833,z0,z1,z3,z4,z6])],[(0,[z10,z0,z1,z3,z4,z6]),(0,[z0,z1,z834,z3,z4,z6]),(0,[z0,z1,z3,z4,z84,z397]),(0,[z0,z1,z2,z3,z358,z496]),(0,[z10,z33,z0,z3,z4,z57]),(0,[z0,z835,z3,z4,z18,z6]),(0,[z0,z3,z4,z332,z18,z6])],[(0,[z0,z1,z2,z3,z836,z6]),(0,[z0,z1,z837,z3,z4,z6]),(0,[z0,z1,z838,z3,z4,z6]),(0,[z376,z172,z2,z3,z4,z6]),(0,[z165,z1,z161,z3,z4,z6])],[(0,[z0,z1,z2,z3,z839,z6]),(1,[z212,z10,z0,z1,z3])]],
   [[(0,[z0,z1,z840,z3,z4,z6]),(0,[z841,z1,z2,z3,z4,z6]),(0,[z80,z0,z825,z3,z4,z6]),(0,[z0,z1,z2,z3,z842,z6]),(0,[z0,z1,z3,z4,z738,z6]),(0,[z0,z1,z2,z719,z4,z6])],[(0,[z64,z1,z2,z3,z177,z6]),(0,[z843,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z844,z6]),(0,[z0,z2,z3,z4,z845,z6]),(0,[z0,z846,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z847,z6]),(0,[z0,z1,z848,z3,z4,z6]),(0,[z228,z10,z0,z1,z94,z6])],[(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z850,z3,z4,z6]),(0,[z0,z1,z851,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z852]),(0,[z853,z1,z2,z3,z4,z6]),(0,[z0,z1,z854,z3,z4,z6]),(0,[z0,z2,z855,z3,z4,z6]),(0,[z856,z0,z2,z3,z4,z6])],[(0,[z133,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z3,z4,z818])],[(0,[z14,z15,z168,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z178]),(0,[z376,z1,z2,z3,z4,z496]),(0,[z25,z10,z0,z1,z3,z52])],[(0,[z0,z2,z3,z4,z753,z6]),(0,[z0,z2,z3,z4,z770,z16]),(0,[z857,z1,z2,z3,z4,z6])],[(0,[z10,z0,z1,z3,z4,z327]),(0,[z396,z1,z123,z3,z4,z6]),(0,[z87,z0,z2,z102,z358,z6]),(0,[z0,z172,z2,z822,z4,z6]),(0,[z147,z0,z2,z3,z8,z6]),(0,[z0,z858,z3,z4,z18,z6])]],
   [[(1,[z1,z746,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z859])],[(0,[z0,z1,z121,z3,z4,z6]),(0,[z185,z1,z35,z3,z4,z6]),(0,[z0,z1,z3,z4,z860,z6]),(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z1,z29,z3,z4,z127]),(0,[z1,z2,z3,z4,z862,z6]),(0,[z0,z1,z3,z74,z6,z402])],[(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z196,z2,z3,z4,z6]),(0,[z0,z1,z119,z4,z18,z6])],[(0,[z1,z2,z3,z716,z177,z6]),(0,[z430,z1,z2,z3,z144,z6]),(0,[z0,z1,z481,z119,z4,z6]),(0,[z0,z1,z864,z3,z4,z6]),(0,[z10,z63,z803,z3,z4,z6])],[(0,[z0,z835,z2,z3,z4,z6]),(0,[z0,z1,z865,z3,z4,z6]),(0,[z1,z2,z195,z4,z6,z630]),(0,[z0,z1,z3,z179,z18,z6]),(0,[z10,z0,z866,z3,z4,z6])],[(0,[z721,z0,z2,z3,z4,z6]),(0,[z14,z721,z2,z3,z4,z6]),(0,[z14,z15,z2,z3,z4,z155]),(0,[z10,z0,z1,z3,z4,z308]),(0,[z0,z2,z3,z8,z246,z6]),(0,[z0,z2,z3,z4,z57,z770])],[(0,[z594,z0,z2,z102,z4,z6]),(0,[z0,z1,z2,z3,z4,z867]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z1,z869,z3,z4,z6]),(0,[z212,z0,z1,z2,z3,z6])],[(0,[z0,z870,z1,z3,z4,z6]),(0,[z7,z376,z2,z3,z4,z6]),(0,[z871,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z27,z6]),(0,[z10,z0,z1,z3,z4,z215]),(0,[z10,z0,z1,z3,z872,z6])]],
   [[(0,[z281,z136,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z627]),(0,[z0,z203,z3,z4,z18,z6]),(0,[z0,z873,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z164,z6]),(0,[z72,z1,z2,z730,z4,z6]),(0,[z376,z1,z2,z3,z358,z6]),(0,[z33,z0,z161,z3,z4,z57])],[(0,[z114,z24,z2,z3,z144,z6]),(0,[z0,z1,z143,z3,z4,z496]),(0,[z150,z0,z1,z2,z3,z4])],[(0,[z187,z136,z2,z3,z4,z6]),(0,[z221,z10,z0,z1,z3,z4]),(0,[z0,z1,z2,z3,z874,z6]),(0,[z490,z10,z0,z1,z3,z4])],[(0,[z0,z1,z2,z3,z875,z6]),(0,[z376,z1,z3,z4,z18,z6]),(0,[z876,z1,z2,z3,z4,z6]),(0,[z877,z1,z2,z3,z4,z6]),(0,[z878,z1,z2,z3,z4,z6])],[(0,[z0,z879,z2,z3,z4,z6]),(0,[z23,z1,z3,z177,z18,z6]),(0,[z0,z880,z1,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z336]),(0,[z0,z1,z881,z3,z4,z6])],[(0,[z10,z0,z1,z882,z4,z6])],[(0,[z0,z858,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z319,z263]),(0,[z80,z0,z123,z3,z4,z81]),(0,[z0,z1,z3,z4,z883,z6]),(0,[z166,z0,z1,z3,z4,z16]),(0,[z0,z1,z2,z3,z170,z6]),(0,[z147,z228,z0,z2,z94,z6])],[(0,[z14,z15,z231,z3,z4,z6]),(0,[z0,z1,z2,z884,z4,z6]),(0,[z0,z885,z1,z3,z4,z6]),(0,[z33,z0,z2,z3,z4,z81]),(0,[z165,z1,z116,z3,z4,z6]),(0,[z63,z0,z196,z3,z4,z6])]],
   [[(0,[z0,z886,z2,z3,z4,z6]),(0,[z107,z1,z2,z184,z319,z6]),(0,[z0,z887,z2,z3,z4,z6]),(0,[z888,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z889,z6]),(0,[z0,z890,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z891]),(0,[z0,z1,z892,z3,z4,z6]),(0,[z893,z1,z2,z3,z4,z6]),(0,[z87,z0,z2,z102,z4,z6]),(0,[z0,z2,z3,z4,z332,z6]),(0,[z10,z0,z1,z3,z4,z306])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z3,z358,z6]),(0,[z1,z2,z3,z4,z6,z895]),(0,[z896,z1,z2,z3,z4,z6]),(0,[z484,z0,z1,z99,z4,z6]),(0,[z25,z10,z0,z196,z3,z4]),(0,[z10,z0,z1,z3,z4,z18])],[(0,[z0,z1,z2,z3,z897,z6]),(0,[z0,z898,z2,z3,z4,z6]),(0,[z899,z0,z2,z3,z4,z6]),(0,[z900,z0,z2,z3,z4,z6]),(0,[z0,z1,z901,z3,z4,z6]),(0,[z87,z0,z143,z102,z4,z6]),(0,[z902,z0,z1,z3,z4,z6])],[(0,[z0,z1,z121,z3,z164,z6]),(0,[z0,z1,z143,z3,z358,z6]),(0,[z615,z0,z2,z3,z4,z57]),(0,[z43,z150,z0,z1,z3,z93]),(0,[z10,z903,z0,z3,z4,z6])],[(0,[z0,z1,z904,z3,z4,z6]),(0,[z72,z1,z2,z195,z4,z6]),(0,[z396,z1,z79,z3,z4,z6]),(0,[z87,z0,z2,z335,z4,z6]),(0,[z0,z1,z481,z3,z4,z127]),(0,[z10,z0,z905,z3,z4,z6]),(0,[z133,z166,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z713])],[(0,[z0,z1,z2,z3,z906,z6]),(0,[z0,z1,z3,z4,z84,z6]),(0,[z0,z1,z3,z4,z474,z81]),(0,[z0,z1,z2,z335,z117,z6]),(0,[z0,z1,z78,z199,z4,z6])],[(0,[z0,z203,z2,z3,z4,z6]),(0,[z907,z0,z1,z2,z3,z6]),(0,[z0,z1,z908,z3,z4,z6]),(0,[z0,z1,z3,z4,z909,z6]),(0,[z173,z1,z2,z3,z4,z336]),(0,[z7,z0,z393,z2,z3,z6]),(0,[z33,z165,z2,z3,z4,z57]),(0,[z10,z0,z1,z3,z4,z589])]],
   [[(0,[z0,z1,z910,z3,z4,z6]),(0,[z0,z1,z3,z4,z155,z18]),(0,[z911,z0,z1,z2,z3,z4]),(0,[z43,z0,z1,z3,z401,z93]),(0,[z273,z0,z196,z3,z4,z6]),(0,[z10,z0,z196,z3,z4,z18]),(0,[z747,z63,z2,z3,z4,z6]),(0,[z147,z0,z2,z3,z117,z6])],[(0,[z7,z356,z2,z3,z115,z6]),(0,[z25,z0,z1,z2,z3,z505]),(0,[z0,z1,z912,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z213]),(0,[z10,z24,z1,z3,z144,z6]),(0,[z913,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z335,z4,z6]),(0,[z0,z1,z3,z4,z104,z6]),(0,[z25,z10,z0,z1,z3,z94]),(0,[z0,z1,z2,z3,z700,z117]),(0,[z25,z0,z1,z2,z3,z30])],[(0,[z23,z1,z2,z3,z177,z6]),(0,[z914,z0,z1,z3,z4,z6]),(0,[z0,z384,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z81]),(0,[z43,z0,z1,z3,z93,z6])],[(0,[z14,z10,z15,z3,z4,z6]),(0,[z0,z1,z3,z4,z786,z263]),(0,[z0,z1,z2,z3,z6,z915]),(0,[z376,z1,z143,z3,z4,z6]),(0,[z10,z49,z1,z3,z4,z6]),(0,[z0,z1,z131,z3,z94,z6]),(0,[z0,z1,z916,z3,z4,z6])],[(0,[z440,z136,z2,z3,z4,z6]),(0,[z108,z1,z2,z3,z4,z579]),(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z384,z2,z3,z4,z16]),(0,[z212,z0,z1,z2,z3,z336]),(0,[z0,z1,z918,z3,z4,z6]),(0,[z212,z0,z1,z3,z18,z6]),(0,[z10,z0,z1,z3,z919,z6])],[(0,[z810,z0,z1,z3,z4,z6]),(0,[z686,z0,z1,z3,z93,z6])],[(0,[z0,z1,z920,z3,z4,z6]),(0,[z0,z48,z79,z3,z4,z6]),(0,[z469,z0,z1,z3,z4,z16])]],
   [[(0,[z0,z1,z921,z3,z4,z6]),(0,[z14,z1,z2,z3,z4,z155]),(0,[z0,z1,z3,z4,z922,z6]),(0,[z0,z1,z2,z923,z4,z6]),(0,[z0,z924,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z925]),(0,[z0,z1,z3,z4,z926,z6])],[(0,[z0,z1,z927,z3,z4,z6]),(0,[z0,z92,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z87,z0,z2,z102,z4,z308]),(0,[z0,z1,z2,z318,z52,z6]),(0,[z10,z0,z1,z3,z4,z57]),(0,[z10,z0,z1,z3,z4,z98]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z43,z0,z1,z3,z424,z6]),(0,[z0,z1,z3,z4,z930,z6]),(0,[z0,z1,z931,z3,z4,z6])],[(0,[z0,z1,z932,z3,z4,z6]),(0,[z0,z1,z933,z3,z4,z6]),(0,[z23,z1,z342,z3,z177,z6]),(0,[z934,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z358,z308]),(0,[z10,z0,z1,z935,z4,z6]),(0,[z17,z0,z1,z4,z18,z12]),(0,[z0,z1,z3,z191,z163,z6])],[(0,[z0,z1,z936,z3,z4,z6]),(0,[z0,z1,z90,z3,z319,z6]),(0,[z0,z937,z2,z3,z4,z6]),(0,[z304,z0,z2,z3,z4,z16]),(0,[z938,z0,z1,z3,z4,z496]),(0,[z0,z939,z1,z3,z4,z6]),(0,[z165,z1,z3,z4,z18,z6])],[(0,[z0,z1,z940,z3,z4,z6]),(0,[z0,z1,z3,z319,z18,z6]),(0,[z108,z92,z1,z3,z4,z77]),(0,[z941,z0,z1,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z770]),(0,[z0,z1,z3,z256,z4,z18]),(0,[z0,z1,z131,z3,z52,z6])],[(0,[z0,z1,z3,z4,z18,z308]),(0,[z0,z1,z942,z3,z4,z6]),(0,[z943,z0,z1,z3,z4,z6]),(0,[z944,z1,z2,z3,z4,z6])],[(0,[z721,z136,z2,z3,z4,z6]),(0,[z24,z1,z2,z3,z286,z6]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z946,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z179,z6]),(0,[z0,z1,z3,z74,z729,z6])],[(0,[z107,z10,z1,z184,z4,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z10,z0,z196,z3,z4,z57]),(0,[z0,z1,z44,z3,z729,z6]),(0,[z0,z196,z3,z4,z424,z6]),(0,[z17,z166,z0,z1,z4,z12])]],
   [[(0,[z0,z1,z2,z3,z948,z6]),(0,[z43,z150,z0,z1,z3,z4]),(0,[z949,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z950,z6]),(0,[z0,z1,z2,z3,z4,z951]),(0,[z147,z0,z2,z109,z4,z6]),(0,[z0,z216,z2,z109,z4,z6]),(0,[z0,z1,z3,z4,z6,z952]),(0,[z228,z0,z2,z332,z94,z6]),(0,[z0,z1,z3,z4,z6,z953]),(0,[z0,z1,z2,z3,z111,z117])],[(0,[z0,z384,z2,z3,z4,z6]),(0,[z0,z203,z2,z3,z164,z6]),(0,[z10,z449,z1,z3,z4,z6]),(0,[z376,z1,z2,z3,z4,z308]),(0,[z87,z0,z88,z102,z4,z6])],[(0,[z136,z2,z3,z582,z4,z6]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z342,z3,z4,z6]),(0,[z0,z1,z121,z3,z319,z6]),(0,[z72,z1,z195,z4,z18,z6]),(0,[z10,z0,z79,z3,z4,z16]),(0,[z396,z1,z2,z3,z4,z81]),(0,[z0,z1,z88,z3,z358,z6]),(0,[z0,z2,z3,z8,z179,z6]),(0,[z25,z0,z1,z2,z3,z336]),(0,[z67,z1,z116,z3,z4,z6]),(0,[z1,z3,z4,z6,z162,z11])],[(0,[z10,z15,z0,z3,z4,z16]),(0,[z0,z1,z955,z3,z4,z6]),(0,[z0,z1,z956,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z336]),(0,[z10,z0,z3,z4,z332,z6])],[(0,[z14,z114,z2,z3,z4,z6]),(0,[z0,z168,z3,z4,z6,z16]),(0,[z10,z0,z1,z3,z4,z138]),(0,[z0,z1,z186,z3,z4,z57]),(0,[z0,z1,z3,z4,z712,z16])],[(0,[z0,z1,z957,z3,z4,z6]),(0,[z7,z0,z2,z3,z115,z6]),(0,[z0,z1,z719,z99,z4,z6]),(0,[z0,z1,z682,z2,z94,z6]),(0,[z958,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z959,z6]),(0,[z0,z1,z2,z3,z960,z6]),(0,[z0,z1,z168,z3,z4,z213]),(0,[z10,z0,z1,z3,z4,z263]),(0,[z10,z0,z961,z3,z4,z6]),(0,[z190,z0,z1,z3,z158,z6]),(0,[z0,z1,z2,z3,z111,z672]),(0,[z228,z0,z1,z2,z94,z6]),(0,[z147,z25,z0,z2,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z962,z6]),(0,[z963,z1,z2,z3,z4,z6]),(0,[z964,z1,z2,z3,z4,z6]),(0,[z10,z803,z1,z3,z4,z6])],[(0,[z210,z0,z196,z3,z4,z6]),(0,[z965,z1,z2,z3,z4,z6]),(0,[z966,z0,z2,z3,z4,z6])],[(0,[z0,z1,z967,z3,z4,z6]),(0,[z0,z1,z2,z3,z164,z223]),(0,[z0,z1,z3,z4,z6,z968]),(0,[z0,z1,z29,z119,z4,z6])],[(0,[z0,z1,z90,z3,z4,z263]),(0,[z0,z1,z2,z3,z4,z969]),(0,[z0,z1,z970,z3,z4,z6]),(0,[z376,z1,z88,z3,z4,z6]),(0,[z265,z0,z1,z3,z93,z6]),(0,[z10,z0,z1,z971,z4,z6]),(0,[z25,z10,z0,z1,z3,z4])],[(0,[z10,z0,z55,z3,z4,z6]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z173,z1,z3,z4,z18,z6]),(0,[z0,z1,z3,z578,z93,z6])],[(0,[z10,z0,z1,z3,z4,z167]),(0,[z0,z1,z2,z3,z4,z973]),(0,[z974,z0,z1,z2,z3,z6]),(0,[z0,z1,z3,z975,z4,z6])],[(0,[z175,z136,z2,z3,z4,z6]),(0,[z1,z2,z3,z730,z4,z6]),(0,[z63,z0,z123,z3,z4,z6]),(0,[z0,z1,z143,z3,z4,z308]),(0,[z356,z1,z3,z4,z18,z6])],[(0,[z449,z1,z2,z3,z4,z397]),(0,[z0,z1,z3,z4,z18,z397]),(0,[z0,z1,z3,z4,z976,z308]),(0,[z87,z10,z0,z102,z4,z6]),(0,[z33,z0,z2,z3,z4,z770])]],
   [[(0,[z15,z173,z2,z3,z4,z6]),(0,[z633,z1,z35,z3,z4,z6]),(0,[z87,z49,z2,z102,z4,z6]),(0,[z0,z1,z2,z977,z4,z6]),(0,[z0,z1,z3,z4,z978,z6]),(0,[z0,z1,z2,z3,z729,z6]),(0,[z228,z0,z1,z131,z94,z6]),(0,[z228,z0,z1,z313,z94,z6])],[(0,[z80,z0,z123,z3,z4,z397]),(0,[z10,z0,z1,z46,z52,z6])],[(0,[z0,z1,z979,z3,z4,z6])],[(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z121,z3,z4,z263]),(0,[z1,z2,z3,z4,z6,z11]),(0,[z0,z1,z3,z4,z18,z496]),(0,[z0,z1,z2,z3,z6,z981]),(0,[z622,z0,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z983,z2,z3,z4,z6]),(0,[z0,z1,z3,z193,z93,z6]),(0,[z10,z0,z1,z3,z984,z6]),(0,[z0,z1,z3,z985,z18,z6])],[(0,[z0,z137,z3,z4,z18,z6]),(0,[z0,z1,z986,z3,z4,z6]),(0,[z107,z1,z2,z69,z4,z6])],[(0,[z107,z1,z121,z184,z4,z6]),(0,[z108,z1,z2,z3,z4,z223]),(0,[z0,z1,z987,z3,z4,z6]),(0,[z0,z1,z130,z4,z6,z261]),(0,[z988,z0,z1,z3,z4,z6]),(0,[z989,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z990]),(0,[z0,z1,z991,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z992]),(0,[z391,z510,z1,z3,z4,z6]),(0,[z10,z0,z196,z3,z4,z6]),(0,[z10,z63,z0,z3,z4,z81]),(0,[z0,z1,z993,z3,z4,z6]),(0,[z0,z1,z3,z994,z4,z6])],[(0,[z272,z136,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z828,z6]),(0,[z995,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z996,z6]),(0,[z67,z1,z3,z4,z18,z6]),(0,[z10,z0,z1,z3,z4,z700]),(0,[z997,z1,z3,z4,z18,z6])]],
   [[(0,[z0,z1,z2,z3,z998,z6]),(0,[z938,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z335,z8,z6]),(0,[z999,z0,z1,z3,z4,z6]),(0,[z10,z0,z1000,z3,z4,z6])],[(0,[z0,z1,z231,z3,z4,z213]),(0,[z0,z203,z2,z3,z319,z6]),(0,[z0,z1,z2,z335,z115,z6]),(0,[z67,z1,z2,z3,z4,z16]),(0,[z1001,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1002,z4]),(0,[z1003,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1004,z6]),(0,[z87,z0,z2,z102,z179,z6]),(0,[z0,z1,z3,z111,z4,z762]),(0,[z0,z1,z230,z3,z259,z6])],[(0,[z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1005]),(0,[z147,z0,z2,z3,z115,z6]),(0,[z0,z1,z2,z3,z4,z770]),(0,[z0,z1,z3,z729,z93,z6]),(0,[z0,z1,z2,z3,z4,z401])],[(0,[z792,z0,z1,z3,z4,z155]),(0,[z0,z1,z186,z3,z4,z6]),(0,[z0,z1,z116,z3,z4,z6]),(0,[z0,z331,z79,z3,z4,z6]),(0,[z609,z0,z1,z2,z94,z6]),(0,[z150,z0,z1,z3,z74,z4]),(0,[z25,z10,z63,z0,z3,z4])],[(0,[z356,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1006]),(0,[z0,z1,z2,z3,z4,z1007]),(0,[z0,z520,z3,z4,z18,z6]),(0,[z0,z571,z79,z3,z4,z6]),(0,[z0,z2,z3,z4,z81,z16]),(0,[z7,z0,z2,z3,z115,z336]),(0,[z10,z63,z0,z3,z4,z278]),(0,[z0,z1,z3,z4,z818,z278]),(0,[z1008,z1,z2,z3,z4,z6]),(0,[z1009,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1010,z3,z4,z6]),(0,[z0,z137,z2,z3,z4,z223]),(0,[z0,z1,z1011,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z397]),(0,[z0,z1,z2,z1012,z4,z6]),(0,[z1013,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1014,z3,z4,z6]),(0,[z0,z1015,z2,z3,z4,z6]),(0,[z1016,z1,z2,z3,z4,z6]),(0,[z166,z0,z1,z3,z4,z57]),(0,[z133,z772,z2,z3,z4,z6])]],
   [[(0,[z314,z0,z196,z3,z4,z6]),(0,[z1,z2,z3,z4,z1017,z6])],[(0,[z0,z2,z3,z4,z155,z16]),(0,[z449,z1,z3,z4,z18,z6]),(0,[z0,z1,z1018,z3,z4,z6]),(0,[z660,z0,z1,z2,z4,z12]),(0,[z0,z1,z3,z4,z6,z162]),(0,[z0,z1,z70,z4,z443,z6])],[(0,[z0,z1,z3,z164,z18,z6]),(0,[z0,z1,z825,z3,z4,z6]),(0,[z157,z0,z123,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z496]),(0,[z0,z1,z2,z3,z1019,z6]),(0,[z1020,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z119,z4,z127]),(0,[z0,z1,z3,z4,z6,z1021]),(0,[z10,z0,z1,z3,z4,z241])],[(0,[z1022,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1023,z3,z4,z6]),(0,[z63,z0,z79,z3,z4,z6]),(0,[z49,z1,z2,z3,z358,z6])],[(0,[z621,z1,z36,z3,z4,z6]),(0,[z0,z1024,z2,z3,z4,z6]),(0,[z0,z1,z88,z3,z4,z308]),(0,[z583,z0,z1,z3,z4,z18])],[(0,[z67,z1,z2,z3,z4,z6]),(0,[z24,z55,z2,z3,z144,z6]),(0,[z997,z1,z2,z3,z4,z6]),(0,[z25,z0,z1,z2,z335,z6]),(0,[z10,z0,z1,z3,z4,z127])],[(0,[z10,z0,z1,z3,z482,z4]),(0,[z0,z384,z1025,z3,z4,z6]),(0,[z0,z123,z825,z3,z4,z6])]],
   [[],[(0,[z15,z0,z2,z3,z4,z336]),(0,[z0,z203,z2,z3,z4,z263]),(0,[z0,z1,z2,z1026,z4,z6]),(0,[z0,z1,z2,z4,z1027,z6]),(0,[z188,z0,z1,z99,z4,z6]),(0,[z0,z1,z2,z3,z4,z1028]),(0,[z10,z0,z1,z3,z302,z4]),(0,[z0,z1,z2,z3,z1029,z6])],[(0,[z108,z136,z2,z3,z4,z16]),(0,[z210,z1,z3,z4,z6,z151]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z10,z1030,z1,z3,z4,z6]),(0,[z214,z1,z3,z4,z106,z6])],[(0,[z107,z203,z2,z184,z4,z6]),(0,[z0,z1,z3,z4,z18,z223]),(0,[z7,z0,z2,z335,z115,z6]),(0,[z903,z0,z2,z3,z4,z6]),(0,[z0,z708,z2,z3,z4,z6])],[(0,[z0,z520,z2,z3,z4,z6]),(0,[z0,z309,z79,z3,z4,z6]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z67,z384,z2,z3,z4,z6]),(0,[z1031,z1,z2,z3,z4,z6]),(0,[z7,z10,z0,z3,z115,z6])],[(0,[z10,z0,z1,z3,z4,z155]),(0,[z173,z1,z481,z3,z4,z6]),(0,[z7,z0,z3,z115,z18,z6]),(0,[z0,z1,z3,z4,z1032,z6]),(0,[z0,z1,z3,z191,z259,z6])],[(0,[z594,z1,z2,z184,z4,z6]),(0,[z14,z326,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z384,z2,z3,z4,z57]),(0,[z108,z1,z2,z3,z4,z459]),(0,[z1,z2,z3,z4,z6,z1034]),(0,[z0,z1,z44,z3,z158,z6])],[(0,[z0,z1,z2,z3,z4,z1035]),(0,[z1036,z1,z2,z3,z4,z6]),(0,[z999,z0,z1,z3,z4,z336]),(0,[z0,z2,z3,z753,z115,z6])]],
   [[(0,[z0,z1,z3,z4,z18,z6]),(0,[z449,z1,z2,z3,z4,z6]),(0,[z14,z15,z2,z3,z4,z213]),(0,[z0,z1,z2,z3,z1037,z6]),(0,[z1038,z1,z2,z3,z4,z6]),(0,[z10,z0,z1039,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1040]),(0,[z133,z10,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z163,z6]),(0,[z469,z0,z1,z3,z111,z4])],[(1,[z1,z2,z730,z4,z6]),(0,[z0,z1,z1041,z3,z4,z6]),(0,[z0,z1,z763,z3,z4,z6]),(0,[z0,z384,z1042,z3,z4,z6]),(0,[z0,z1043,z1,z3,z4,z6]),(0,[z25,z469,z0,z1,z3,z30])],[(0,[z0,z1,z3,z1044,z4,z6]),(0,[z80,z0,z123,z3,z4,z6]),(0,[z1045,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1046]),(0,[z0,z1,z1047,z3,z4,z6]),(0,[z0,z1,z1048,z3,z4,z6]),(0,[z0,z1,z3,z4,z1049,z6]),(0,[z108,z1,z3,z4,z18,z77]),(1,[z0,z2,z3,z4,z770]),(0,[z0,z1,z1050,z3,z4,z6])],[(0,[z0,z1,z1051,z3,z4,z6]),(0,[z114,z173,z2,z3,z4,z6]),(0,[z0,z1,z2,z699,z4,z180]),(0,[z356,z1,z2,z3,z4,z336]),(0,[z0,z1,z3,z4,z18,z567]),(0,[z10,z0,z1,z3,z259,z6]),(0,[z803,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z163,z18,z6]),(0,[z1052,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z117,z713])],[(0,[z376,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1053]),(0,[z17,z0,z1,z2,z4,z12])],[(0,[z0,z137,z2,z3,z164,z6]),(0,[z1054,z1,z2,z3,z4,z6]),(0,[z0,z1,z1055,z3,z4,z6]),(0,[z9,z0,z1,z99,z170,z6]),(0,[z166,z0,z1,z3,z4,z6]),(0,[z314,z0,z1,z200,z4,z6]),(0,[z0,z1,z59,z3,z4,z818])],[(0,[z0,z1,z1056,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1057]),(0,[z0,z1,z2,z3,z4,z1058])]],
   [[(0,[z0,z1,z1059,z3,z4,z6]),(0,[z0,z1,z123,z3,z4,z81]),(0,[z49,z1,z143,z3,z4,z6]),(0,[z25,z10,z0,z26,z1,z3])],[(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z1,z3,z4,z1061,z6]),(0,[z0,z1,z3,z170,z18,z6])],[(0,[z1,z136,z2,z3,z4,z155]),(0,[z0,z1,z2,z3,z4,z223]),(0,[z10,z0,z1,z3,z319,z6]),(0,[z23,z1,z284,z3,z177,z6]),(1,[z0,z825,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1062]),(0,[z63,z0,z2,z3,z4,z81]),(0,[z0,z1,z1063,z3,z4,z6]),(0,[z0,z1,z3,z99,z27,z6]),(0,[z0,z1,z1064,z3,z4,z6])],[(0,[z0,z1,z88,z3,z4,z496]),(0,[z10,z0,z1,z3,z702,z4]),(0,[z0,z1,z3,z4,z762,z6])],[(0,[z0,z48,z825,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z33,z0,z116,z3,z4,z57]),(0,[z0,z1,z3,z4,z1066,z6])],[(0,[z0,z1067,z2,z3,z4,z6]),(0,[z24,z1,z3,z144,z18,z6]),(0,[z498,z1,z2,z3,z4,z97]),(0,[z0,z1,z1068,z3,z4,z6]),(0,[z0,z1,z3,z754,z18,z6]),(0,[z147,z0,z993,z3,z4,z6])],[(0,[z0,z203,z90,z3,z4,z6]),(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z2,z822,z4,z6]),(0,[z1070,z1,z2,z3,z4,z6]),(0,[z0,z1,z313,z3,z4,z6]),(0,[z747,z10,z1,z3,z4,z6]),(0,[z10,z0,z1,z71,z4,z180]),(1,[z0,z1,z2,z1071,z6]),(0,[z17,z0,z1,z4,z162,z12])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z1072,z0,z1,z3,z4,z6]),(0,[z0,z1,z145,z3,z4,z18]),(0,[z1073,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1074,z6]),(0,[z0,z1,z3,z4,z883,z127]),(0,[z7,z25,z10,z0,z1,z3])]],
   [[(0,[z0,z1,z2,z1075,z4,z6]),(0,[z1076,z0,z1,z3,z4,z6]),(0,[z173,z1,z2,z335,z4,z6]),(1,[z0,z1,z3,z729,z6])],[(0,[z843,z0,z1,z3,z4,z213]),(0,[z68,z0,z1,z2,z94,z6]),(0,[z0,z1,z3,z4,z6,z1077]),(0,[z0,z1,z143,z3,z4,z6]),(0,[z1078,z1,z2,z3,z4,z6]),(0,[z0,z1,z78,z3,z27,z6])],[(0,[z0,z1,z746,z3,z4,z6]),(0,[z0,z1,z3,z4,z976,z6]),(0,[z356,z1,z2,z335,z4,z6]),(0,[z0,z1,z1079,z3,z4,z6]),(0,[z17,z10,z0,z1,z4,z12]),(0,[z0,z1,z3,z259,z18,z6]),(0,[z0,z1,z1080,z3,z4,z6])],[(0,[z266,z15,z2,z3,z4,z6]),(0,[z211,z0,z196,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1081]),(0,[z1082,z1,z2,z3,z4,z6]),(0,[z1083,z0,z1,z2,z3,z4]),(0,[z0,z1,z1084,z3,z4,z6]),(1,[z0,z1,z719,z4,z6])],[(0,[z1,z136,z231,z3,z4,z6]),(0,[z568,z0,z2,z3,z4,z16]),(0,[z0,z1,z2,z3,z1085,z6]),(0,[z17,z1,z2,z4,z11,z12]),(0,[z0,z1,z2,z3,z4,z755])],[(0,[z0,z1,z2,z3,z1086,z6]),(0,[z108,z1,z2,z3,z4,z606]),(0,[z0,z1087,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z389]),(0,[z0,z1,z2,z3,z1088,z6]),(0,[z614,z10,z0,z1,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1089]),(0,[z49,z1,z2,z3,z4,z308]),(0,[z0,z1,z1090,z3,z4,z6]),(0,[z0,z1,z2,z3,z1091,z6]),(0,[z10,z0,z1,z3,z4,z294])],[(0,[z0,z1,z3,z4,z748,z6]),(0,[z326,z0,z123,z3,z4,z6]),(0,[z0,z1092,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z10,z0,z1,z3,z6,z354]),(0,[z469,z0,z1,z3,z4,z6]),(1,[z0,z1,z3,z4,z818])]],
   [[(0,[z1094,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z18,z341]),(0,[z108,z384,z2,z3,z4,z77]),(0,[z390,z0,z1,z3,z93,z6]),(0,[z0,z1,z3,z4,z6,z1095]),(0,[z212,z10,z0,z1,z2,z3]),(0,[z0,z1,z116,z3,z4,z57]),(0,[z0,z1,z3,z111,z104,z117])],[(0,[z0,z1096,z1,z3,z4,z6]),(0,[z0,z1,z1097,z3,z4,z6]),(0,[z0,z1,z2,z1098,z4,z6]),(0,[z1099,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1100,z4,z6]),(0,[z0,z1,z2,z3,z4,z1101]),(0,[z147,z10,z0,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1102])],[(0,[z203,z2,z3,z4,z97,z6]),(0,[z0,z1,z1103,z3,z4,z6])],[(0,[z0,z1,z1104,z3,z4,z6]),(0,[z0,z1,z78,z200,z4,z6]),(0,[z0,z1,z2,z3,z4,z1105]),(0,[z10,z63,z0,z3,z111,z4]),(0,[z10,z814,z1,z3,z4,z6]),(0,[z228,z0,z1,z2,z1071,z6])],[(0,[z384,z136,z2,z3,z4,z6]),(0,[z10,z0,z203,z3,z4,z6])],[(0,[z165,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1106,z6]),(0,[z1,z1107,z2,z3,z4,z6])],[(0,[z67,z15,z2,z3,z4,z6]),(0,[z0,z1,z343,z3,z4,z6]),(0,[z0,z1108,z2,z3,z4,z6]),(0,[z0,z1,z79,z3,z4,z81]),(0,[z80,z0,z196,z3,z4,z6]),(0,[z0,z1,z2,z109,z179,z6]),(0,[z0,z1,z3,z4,z1109,z6]),(0,[z10,z0,z1,z801,z4,z6])],[(0,[z7,z0,z2,z3,z209,z6]),(0,[z0,z1,z1110,z3,z4,z6]),(0,[z0,z446,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z308]),(0,[z0,z1,z44,z3,z437,z6])]],
   [[(0,[z1,z2,z3,z4,z97,z223]),(0,[z0,z1,z1111,z3,z4,z6]),(0,[z190,z0,z196,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1112,z6]),(0,[z0,z1,z2,z3,z872,z6]),(0,[z10,z0,z172,z109,z4,z6]),(0,[z0,z1,z2,z3,z27,z6])],[(0,[z0,z1,z2,z3,z164,z6]),(0,[z1113,z0,z1,z3,z4,z6]),(0,[z0,z1,z78,z363,z4,z6]),(0,[z0,z1,z2,z3,z4,z1114]),(0,[z1115,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1116,z6]),(0,[z0,z1,z3,z18,z6,z354]),(0,[z67,z1,z2,z3,z4,z57]),(0,[z0,z2,z3,z4,z6,z1117])],[(0,[z0,z1,z2,z1118,z4,z6]),(0,[z0,z1,z2,z3,z4,z1119]),(0,[z0,z1,z2,z3,z179,z496]),(0,[z1120,z1,z2,z3,z4,z6]),(0,[z273,z1,z377,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1121]),(0,[z226,z0,z123,z3,z4,z6]),(0,[z0,z1,z3,z84,z6,z354]),(0,[z0,z1,z1122,z3,z4,z6])],[(0,[z10,z63,z0,z3,z4,z16]),(0,[z0,z446,z196,z3,z4,z6]),(0,[z573,z0,z1,z3,z93,z6])],[(0,[z0,z1,z2,z3,z4,z1123]),(0,[z0,z1,z1124,z3,z4,z6]),(0,[z1125,z1,z2,z3,z4,z6]),(1,[z0,z2,z822,z4,z6]),(0,[z0,z1,z2,z3,z4,z336])],[(0,[z0,z1,z2,z882,z4,z6]),(0,[z0,z1,z1126,z3,z4,z6]),(0,[z10,z0,z1,z119,z4,z6]),(0,[z9,z0,z1,z719,z4,z6]),(0,[z0,z1,z2,z3,z4,z1127]),(0,[z147,z0,z3,z4,z18,z6])]],
   [[(0,[z0,z1,z3,z4,z6,z1128]),(0,[z0,z1,z2,z730,z4,z6]),(0,[z0,z1,z88,z3,z4,z6]),(0,[z0,z1,z44,z3,z413,z6]),(0,[z0,z2,z109,z4,z225,z6]),(0,[z10,z0,z1,z3,z829,z6]),(0,[z146,z1,z3,z4,z6,z151]),(0,[z0,z1,z2,z3,z985,z6])],[(0,[z0,z1,z3,z4,z1129,z6]),(0,[z1,z2,z195,z730,z4,z6]),(0,[z0,z1130,z2,z3,z4,z6]),(0,[z150,z0,z1,z123,z3,z4]),(0,[z0,z1,z3,z4,z6,z1131])],[(0,[z0,z1,z2,z3,z4,z1132]),(0,[z211,z1,z112,z3,z4,z6]),(0,[z0,z1,z2,z1133,z4,z6]),(0,[z0,z1,z3,z4,z18,z89]),(0,[z0,z1,z3,z4,z6,z818]),(0,[z1134,z0,z1,z3,z4,z6]),(0,[z1135,z0,z1,z3,z4,z6])],[(0,[z15,z721,z2,z3,z4,z6]),(0,[z14,z384,z2,z3,z4,z6]),(0,[z0,z1039,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z474]),(0,[z10,z376,z1,z3,z4,z6]),(0,[z7,z0,z481,z3,z115,z6]),(0,[z0,z1000,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1136,z6])],[(0,[z1137,z0,z1,z2,z4,z6]),(0,[z49,z1,z2,z3,z4,z496]),(0,[z173,z1,z29,z3,z4,z6]),(0,[z133,z1,z2,z3,z4,z16]),(0,[z510,z0,z196,z3,z4,z6]),(0,[z0,z1,z135,z3,z111,z117])],[(1,[z721,z2,z3,z4,z6]),(0,[z0,z1,z1138,z3,z4,z6]),(0,[z0,z1,z3,z4,z1139,z6]),(0,[z10,z1140,z1,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z217])],[(0,[z0,z1,z2,z3,z1141,z6]),(0,[z356,z1,z29,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1142]),(0,[z107,z137,z2,z184,z4,z6]),(0,[z1,z2,z3,z144,z716,z6]),(0,[z10,z396,z1,z3,z4,z6]),(0,[z0,z1,z1143,z3,z4,z6]),(0,[z0,z2,z109,z822,z4,z6]),(0,[z7,z0,z2,z3,z115,z127]),(0,[z33,z0,z2,z3,z4,z57]),(0,[z0,z1,z3,z4,z401,z104]),(0,[z0,z1,z1144,z3,z4,z6])]],
   [[(0,[z380,z1,z35,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z1145]),(0,[z406,z0,z1,z2,z94,z6]),(0,[z0,z1,z1146,z3,z4,z6]),(0,[z149,z0,z1,z251,z4,z6]),(0,[z0,z1,z59,z3,z4,z104]),(0,[z0,z1,z2,z3,z713,z30])],[(0,[z0,z1,z1147,z3,z4,z6]),(0,[z0,z1,z2,z3,z1148,z6])],[(0,[z0,z1,z2,z3,z4,z1149]),(0,[z0,z384,z2,z3,z4,z155]),(0,[z0,z1,z2,z3,z1150,z6]),(0,[z1151,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1152]),(0,[z10,z0,z1,z3,z4,z818]),(0,[z25,z0,z1,z3,z198,z30])],[(0,[z211,z1,z377,z3,z4,z6]),(0,[z150,z0,z1,z35,z3,z4]),(0,[z10,z0,z1,z3,z4,z330]),(0,[z1153,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z319,z223]),(0,[z133,z1,z2,z3,z4,z223]),(0,[z0,z1,z1154,z3,z4,z6]),(0,[z1155,z0,z1,z3,z4,z6]),(0,[z0,z1,z1025,z3,z4,z6]),(0,[z108,z1,z2,z3,z4,z742]),(0,[z0,z1,z2,z335,z4,z6]),(0,[z0,z1,z1156,z3,z4,z6])],[(0,[z212,z15,z0,z2,z3,z6]),(0,[z0,z1,z2,z3,z1157,z6])],[(0,[z0,z137,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z1,z3,z4,z1159,z6]),(0,[z0,z1,z2,z3,z4,z1160]),(0,[z376,z1,z2,z3,z179,z6]),(0,[z147,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1161]),(0,[z150,z0,z1,z78,z3,z4]),(0,[z10,z0,z1,z3,z4,z411]),(0,[z0,z1,z2,z1071,z94,z6])],[(0,[z0,z1,z2,z1162,z4,z6]),(0,[z1163,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z243]),(0,[z80,z449,z123,z3,z4,z6]),(0,[z0,z1,z2,z3,z919,z6]),(0,[z0,z1164,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z713])]],
   [[(0,[z0,z1165,z2,z3,z4,z6]),(0,[z1166,z0,z2,z3,z4,z6]),(0,[z33,z449,z2,z3,z4,z6]),(0,[z0,z1,z481,z3,z4,z336]),(0,[z596,z0,z1,z4,z6,z261]),(0,[z147,z0,z1167,z3,z4,z6])],[(0,[z0,z1168,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1169]),(0,[z0,z905,z2,z3,z4,z6]),(0,[z10,z150,z0,z1,z3,z4]),(0,[z484,z0,z1,z2,z94,z6]),(0,[z10,z0,z924,z3,z4,z6]),(0,[z1170,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z4,z18,z263]),(0,[z10,z72,z1,z195,z4,z6]),(0,[z114,z0,z3,z4,z18,z6]),(0,[z0,z1171,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1172]),(0,[z49,z1,z3,z4,z18,z6]),(0,[z1173,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1174,z6]),(0,[z813,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z935,z4,z6]),(0,[z210,z1,z746,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1175]),(0,[z10,z0,z1,z393,z3,z4])],[(0,[z1176,z1,z2,z3,z4,z6]),(0,[z1,z3,z4,z18,z6,z11]),(0,[z1177,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1178,z6])],[(0,[z14,z15,z3,z4,z18,z6]),(0,[z1,z35,z746,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1179]),(0,[z0,z1,z1042,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1180])],[(0,[z210,z1,z35,z3,z4,z6]),(0,[z0,z1181,z2,z3,z4,z6]),(0,[z0,z1,z1182,z3,z4,z6]),(0,[z1183,z0,z1,z3,z4,z6])]],
   [[(0,[z239,z1,z2,z3,z177,z6]),(0,[z0,z1,z2,z3,z179,z6]),(0,[z0,z1184,z1,z3,z4,z6]),(0,[z147,z0,z2,z3,z4,z1102])],[(0,[z126,z0,z1,z3,z4,z18]),(0,[z396,z1,z2,z3,z4,z397]),(0,[z10,z0,z718,z3,z4,z6]),(0,[z10,z1,z3,z4,z6,z11]),(0,[z0,z1,z2,z128,z52,z6])],[(0,[z214,z1,z36,z3,z4,z6]),(0,[z108,z520,z2,z3,z4,z77]),(0,[z10,z0,z1,z3,z4,z565]),(0,[z0,z1,z143,z3,z179,z6]),(0,[z356,z1,z481,z3,z4,z6]),(0,[z312,z63,z0,z3,z4,z6]),(0,[z10,z0,z1185,z3,z4,z6]),(0,[z0,z1,z2,z4,z1071,z6]),(0,[z0,z1,z2,z52,z1071,z6])],[(0,[z0,z136,z2,z3,z4,z336]),(0,[z150,z0,z1,z36,z3,z4]),(0,[z0,z1,z1186,z3,z4,z6]),(0,[z469,z0,z1,z3,z4,z57])],[(0,[z10,z0,z1,z3,z4,z445]),(0,[z173,z1,z2,z3,z4,z127]),(0,[z0,z1,z2,z3,z4,z1187]),(0,[z33,z0,z3,z4,z57,z18]),(0,[z10,z0,z1,z3,z170,z6])],[(0,[z0,z1,z2,z3,z1188,z6]),(0,[z1,z2,z730,z184,z4,z6]),(0,[z1189,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z1191,z0,z1,z2,z3,z6]),(0,[z10,z356,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1192,z6]),(0,[z10,z0,z1,z3,z683,z4])],[(0,[z107,z1,z2,z184,z4,z223]),(0,[z0,z55,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z4,z766]),(0,[z0,z1,z2,z3,z4,z767]),(0,[z0,z2,z3,z822,z4,z6]),(0,[z0,z1,z1193,z3,z4,z6]),(0,[z356,z1,z2,z3,z4,z127]),(0,[z10,z0,z1,z3,z4,z468])],[(0,[z0,z1194,z2,z3,z4,z6]),(0,[z0,z1195,z2,z3,z4,z6]),(0,[z72,z203,z2,z3,z4,z6]),(0,[z1196,z0,z2,z3,z4,z6]),(0,[z23,z1,z2,z3,z716,z6]),(0,[z23,z10,z1,z3,z177,z6]),(0,[z0,z1,z3,z1197,z4,z6]),(0,[z0,z1,z2,z3,z4,z1198]),(0,[z87,z376,z2,z102,z4,z6]),(0,[z1199,z1,z2,z3,z4,z6]),(0,[z0,z1,z1200,z3,z4,z6]),(0,[z56,z0,z3,z4,z84,z16])]],
   [[(0,[z444,z0,z1,z3,z93,z6]),(0,[z107,z1,z184,z4,z18,z6]),(0,[z1201,z0,z1,z3,z4,z6]),(0,[z10,z0,z1,z3,z358,z6]),(0,[z43,z0,z1,z3,z729,z6]),(0,[z614,z150,z0,z1,z3,z4])],[(0,[z49,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1202,z4,z6]),(0,[z114,z0,z2,z3,z4,z6]),(0,[z1,z746,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z263]),(0,[z1,z2,z3,z4,z742,z77]),(0,[z63,z0,z2,z3,z4,z16]),(0,[z10,z0,z1,z3,z4,z457])],[(0,[z15,z0,z2,z335,z4,z6]),(0,[z0,z1,z1203,z3,z4,z6]),(0,[z0,z1,z3,z4,z401,z18]),(0,[z0,z1,z2,z586,z52,z6]),(0,[z10,z0,z1,z3,z4,z407])],[(0,[z173,z136,z2,z3,z4,z6]),(0,[z107,z1,z2,z184,z4,z6]),(0,[z0,z1,z2,z335,z4,z336]),(0,[z1204,z1,z2,z3,z4,z6]),(0,[z10,z728,z0,z3,z4,z6]),(0,[z10,z0,z1,z425,z3,z4])],[(0,[z1205,z0,z1,z3,z4,z223]),(0,[z0,z1,z3,z4,z1206,z6]),(0,[z0,z1,z2,z3,z1071,z6]),(0,[z0,z1,z2,z46,z1071,z6])],[(0,[z14,z15,z2,z3,z4,z6]),(0,[z0,z1,z1207,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z16]),(0,[z0,z1185,z2,z3,z4,z6]),(0,[z0,z1,z2,z971,z4,z6]),(0,[z316,z0,z3,z4,z6,z241])],[(0,[z0,z1,z2,z3,z1208,z6]),(0,[z0,z1,z1209,z3,z4,z6])],[(0,[z10,z272,z136,z3,z4,z6]),(0,[z0,z1,z3,z4,z480,z6]),(0,[z0,z1,z3,z4,z717,z496]),(0,[z1140,z1,z2,z3,z4,z6]),(0,[z293,z0,z1,z3,z424,z6])]],
   [[(0,[z10,z0,z1,z3,z4,z213]),(0,[z0,z1,z29,z3,z4,z6]),(0,[z304,z0,z1,z3,z4,z18]),(0,[z0,z1,z2,z3,z179,z308]),(0,[z0,z2,z822,z102,z4,z6]),(0,[z1210,z0,z1,z3,z4,z6]),(0,[z25,z469,z0,z1,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1211]),(0,[z1205,z0,z1,z3,z4,z6]),(0,[z10,z0,z1,z3,z4,z81]),(0,[z853,z1,z3,z4,z18,z6]),(0,[z0,z1,z2,z3,z111,z713])],[(0,[z1212,z0,z1,z3,z4,z6]),(0,[z108,z1,z3,z4,z480,z77]),(0,[z7,z0,z2,z3,z179,z6]),(0,[z1213,z1,z2,z3,z4,z6]),(0,[z0,z1,z1214,z3,z4,z6]),(0,[z147,z1008,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1215]),(0,[z396,z1,z3,z4,z18,z6]),(0,[z1216,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1217]),(0,[z0,z1,z1218,z3,z4,z6]),(0,[z0,z1,z2,z46,z52,z6]),(0,[z0,z1,z3,z4,z6,z1219])],[(0,[z1220,z1,z2,z3,z4,z6]),(0,[z0,z1,z1167,z3,z4,z6]),(0,[z17,z133,z1,z2,z4,z12])],[(0,[z0,z55,z2,z3,z4,z6]),(0,[z108,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z1221,z4,z6]),(0,[z80,z0,z3,z4,z6,z241]),(0,[z376,z2,z3,z8,z4,z6]),(0,[z0,z2,z109,z335,z4,z6]),(0,[z0,z1,z2,z3,z984,z6]),(0,[z299,z10,z0,z1,z3,z4]),(0,[z228,z0,z1,z94,z18,z6])],[(0,[z67,z136,z2,z3,z4,z6]),(0,[z0,z1,z284,z3,z4,z6]),(0,[z10,z0,z520,z3,z4,z6]),(0,[z0,z446,z1,z3,z6,z354]),(0,[z9,z0,z1,z251,z4,z6]),(0,[z0,z1,z3,z111,z18,z117])],[(0,[z0,z1,z1222,z3,z4,z6]),(0,[z0,z1,z1223,z3,z4,z6]),(0,[z147,z0,z2,z102,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z6,z1224]),(0,[z0,z1,z1225,z3,z4,z6]),(0,[z10,z173,z1,z3,z4,z6]),(0,[z212,z0,z446,z1,z3,z6]),(0,[z10,z0,z1,z3,z4,z278])],[(0,[z0,z1,z1226,z3,z4,z6]),(0,[z0,z203,z121,z3,z4,z6]),(0,[z0,z1,z90,z3,z4,z223]),(0,[z114,z0,z1110,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z0,z1,z88,z3,z179,z6]),(0,[z0,z1,z3,z4,z18,z127]),(0,[z1030,z1,z2,z3,z4,z6]),(0,[z10,z899,z0,z3,z4,z6])],[(0,[z0,z1,z110,z3,z4,z18]),(0,[z0,z866,z2,z3,z4,z6]),(0,[z7,z0,z29,z3,z115,z6]),(0,[z0,z2,z3,z4,z1227,z6]),(0,[z765,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z470,z94,z6])],[(0,[z33,z0,z168,z3,z4,z6]),(0,[z133,z1,z2,z3,z4,z97]),(0,[z147,z0,z2,z335,z4,z6]),(0,[z56,z0,z446,z3,z4,z16]),(0,[z147,z1052,z2,z3,z4,z6])],[(0,[z1228,z0,z2,z3,z4,z6]),(0,[z0,z1,z78,z618,z4,z6]),(0,[z0,z1,z2,z3,z164,z263]),(0,[z0,z564,z79,z3,z4,z6]),(0,[z0,z1,z3,z1229,z4,z6]),(0,[z10,z0,z1,z3,z4,z104])],[(0,[z0,z1,z2,z3,z4,z1230])],[(0,[z0,z1,z90,z3,z4,z6]),(0,[z107,z1,z2,z184,z164,z6]),(0,[z376,z2,z3,z102,z4,z6]),(0,[z10,z63,z0,z3,z4,z57]),(0,[z10,z0,z196,z3,z4,z278]),(0,[z133,z1,z3,z4,z6,z162])],[(0,[z10,z0,z136,z3,z4,z16]),(0,[z0,z1,z2,z1231,z4,z6]),(0,[z0,z1,z2,z3,z4,z1232]),(0,[z0,z961,z2,z3,z4,z6]),(0,[z1233,z0,z1,z3,z4,z6]),(0,[z10,z434,z0,z1,z3,z4]),(0,[z9,z0,z1,z99,z4,z6]),(0,[z1234,z0,z1,z2,z3,z4]),(0,[z1235,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z3,z111,z117]),(0,[z147,z0,z2,z3,z4,z760]),(0,[z1236,z0,z2,z3,z4,z6])]],
   [[(0,[z0,z137,z2,z3,z319,z6]),(0,[z7,z0,z2,z119,z115,z6])],[(0,[z0,z1,z1237,z3,z4,z6]),(0,[z0,z1,z121,z3,z4,z223]),(0,[z0,z1,z2,z101,z52,z6]),(0,[z0,z1,z2,z3,z1238,z6]),(0,[z0,z1,z2,z102,z179,z6])],[(0,[z396,z1,z2,z3,z4,z6]),(0,[z0,z172,z2,z317,z4,z6]),(0,[z1239,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1240]),(0,[z0,z446,z79,z3,z4,z6]),(0,[z49,z1,z88,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z712]),(0,[z0,z1,z2,z3,z4,z1241]),(0,[z25,z10,z0,z1,z3,z424])],[(0,[z51,z136,z2,z3,z4,z6]),(0,[z33,z0,z2,z3,z4,z155]),(0,[z646,z0,z2,z3,z4,z16]),(0,[z0,z1,z1242,z3,z4,z6]),(0,[z0,z1,z2,z3,z1243,z6]),(0,[z0,z1,z1244,z3,z4,z6])],[(0,[z995,z0,z1,z3,z4,z263]),(0,[z0,z1,z481,z3,z4,z6]),(0,[z0,z1245,z2,z3,z4,z6])],[(0,[z0,z1,z2,z46,z507,z6]),(0,[z133,z1,z2,z3,z4,z57]),(0,[z0,z1,z2,z4,z755,z12])],[(0,[z0,z1,z1246,z3,z4,z6]),(0,[z0,z1,z3,z4,z1247,z6])],[(0,[z0,z1,z168,z3,z4,z6]),(0,[z10,z0,z137,z3,z4,z6]),(0,[z147,z0,z2,z3,z179,z6]),(0,[z0,z1,z29,z3,z4,z336]),(0,[z212,z0,z1,z59,z2,z3]),(0,[z166,z1,z3,z4,z6,z11])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 516) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 516).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1040).take 231) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1271)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [516, 524, 231] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 93).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 193).take 63).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [93, 100, 63] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_37775

theorem PEqualNP.Outside.L_meta_37775 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4209044096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4209044096) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37775.solve