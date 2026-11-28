import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36338

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277071072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8090000428244e45#64 ++ 0x202400010a091391#64 ++ 0x7be8520cf86cde4f#64 ++ 0xdefa14833e1b3793#64 : BitVec 256),
   (0x08200411600502d0#64 ++ 0x42080104580140b4#64 ++ 0xf7dcac33609727f3#64 ++ 0xbdf72b0cd825c9fc#64 : BitVec 256),
   (0x204130c28318302a#64 ++ 0x88104c30a0c60c0a#64 ++ 0xeebf31c38718387f#64 ++ 0x7bafcc70e1c60e1f#64 : BitVec 256),
   (0x1282c16c05e03d01#64 ++ 0x04a0b05b01780f40#64 ++ 0xde7fc1fc07e03f82#64 ++ 0xf79ff07f01f80fe0#64 : BitVec 256),
   (0x2303fa0006da8002#64 ++ 0x08c0fe8001b6a000#64 ++ 0xc1fbfe0007ffc001#64 ++ 0xf07eff8001fff000#64 : BitVec 256),
   (0x3c03ffbbd0000000#64 ++ 0x0f00ffeef4000000#64 ++ 0x3ffbfffff8000000#64 ++ 0x0ffefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [11, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcac33609727f3 0xbdf72b0cd825c9fc

def z1 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fc1fc07e03f82 0xf79ff07f01f80fe0

def z2 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebf31c38718387f 0x7bafcc70e1c60e1f

def z3 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01a37e00077fc001 0x4068df8001dff000

def z4 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z5 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z6 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7be8520cf86cde4f 0xdefa14833e1b3793

def z7 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x0163de0007efc000 0xc058f78001fbf000

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1d8ac0000970001 0xb0762b000025c000

def z9 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x36040033600027f2 0x0d81000cd80009fc

def z10 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e0001fff8000000 0x0f80007ffe000000

def z11 : W := mkw 0x9292c16c2de47f45 0x24a4b05b0b791fd1 0xffffd3fcffecffcf 0xfffff4ff3ffb3ff3

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0x6aa810008008184f 0x5aaa040020020613

def z13 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x9554ac33609727b0 0xa5552b0cd825c9ec

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0xd65c803000802782 0xb597200c002009e0

def z15 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfffcd23cf8ecffcf 0xffff348f3e3b3ff3

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0xe69c200300102073 0x39a70800c004081c

def z17 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x082311c08708180c 0x4208c47021c20603

def z18 : W := mkw 0x3243f1ea87d8312a 0x8c90fc7aa1f60c4a 0x8417a1f3079021b0 0x2105e87cc1e4086c

def z19 : W := mkw 0x9292c12c2ce44f45 0x24a4b04b0b3913d1 0x1140c23c78e4c780 0x8450308f1e3931e0

def z20 : W := mkw 0x3c4135fbd318302a 0x8f104d7ef4c60c0a 0xfebf31ffff18387f 0x7fafcc7fffc60e1f

def z21 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xffffd3fcffe03f82 0xfffff4ff3ff80fe0

def z22 : W := mkw 0xa393fa042efece47 0x28e4fe810bbfb391 0xc1fbfe0007ffde4f 0xf07eff8001fff793

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x1604003000002782 0x0581000c000009e0

def z24 : W := mkw 0x12a2c16c25e53fd1 0x44a8b05b09794ff4 0xde7fc1fc07f73ff3 0xf79ff07f01fdcffc

def z25 : W := mkw 0x2303fa0026de8242 0x08c0fe8009b7a090 0xf3fbfe0067ffc643 0xfcfeff8019fff190

def z26 : W := mkw 0x3683fbee95e03d01 0x0da0fefba5780f40 0x082353cc9f601800 0x4208d4f327d80600

def z27 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x3f40cffff8000000 0x0fd033fffe000000

def z28 : W := mkw 0x3c23ffbbf00502d0 0x4f08ffeefc0140b4 0xfffffffff89727f3 0xbffffffffe25c9fc

def z29 : W := mkw 0x3c43fffbd318302a 0x8f10fffef4c60c0a 0xffffffffff18387f 0x7fffffffffc60e1f

def z30 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0x1e0401fc00003f82 0x0781007f00000fe0

def z31 : W := mkw 0x3383fb6c07fabd03 0x0ce0fedb01feaf40 0xdffffffc07ffff83 0xf7ffffff01ffffe0

def z32 : W := mkw 0x0280004405e03d01 0x00a0001101780f40 0xc004000007e03f82 0xf001000001f80fe0

def z33 : W := mkw 0x2c013e93d0000000 0x0b004fa4f4000000 0x21803e03f8000000 0x08600f80fe000000

def z34 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x21802c0360170071 0x08600b00d805c01c

def z35 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x082341cc07601800 0x4208d07301d80600

def z36 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x002352000768c000 0x4008d48001da3000

def z37 : W := mkw 0x8090000428244e45 0x202400010a091391 0x31c0520cf86cc64d 0x8c7014833e1b3193

def z38 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0x841781f007802180 0x2105e07c01e00860

def z39 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0x1040c03c00e00780 0x8410300f003801e0

def z40 : W := mkw 0x0080000400200c01 0x0020000100080300 0x5a68400c00601e02 0xd69a100300180780

def z41 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbffffffffc001 0xfffefffffffff000

def z42 : W := mkw 0x829000442de47f45 0x20a400110b791fd1 0xc004000007ecffcf 0xf001000001fb3ff3

def z43 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x8013ac0007930000 0x2004eb0001e4c000

def z44 : W := mkw 0x8090000428244e45 0x202400010a091391 0x29a0520cf86cd84d 0x4a6814833e1b3613

def z45 : W := mkw 0x0820041140010090 0x4208010450004024 0x8414ac33009321b0 0x21052b0cc024c86c

def z46 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x01803e00001fc001 0x00600f800007f000

def z47 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x37d8ac3360870780 0x8df62b0cd821c1e0

def z48 : W := mkw 0x1a22c57945c13190 0x4688b15e51704c64 0x8417adf3079321b0 0x2105eb7cc1e4c86c

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000970001 0xb00000000025c000

def z50 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0xde7fc1fc00802782 0xb79ff07f002009e0

def z51 : W := mkw 0x0c000493d0000000 0x03000124f4000000 0x20000003f8000000 0x08000000fe000000

def z52 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x0413adf300000000 0x0104eb7cc0000000

def z53 : W := mkw 0x3c43fffbd318302a 0x8f10fffef4c60c0a 0xbfffffffff102030 0x2fffffffffc4080c

def z54 : W := mkw 0x1aa2c57d65e53fd1 0x46a8b15f59794ff4 0xfe7fc1ff67e03ff2 0xff9ff07fd9f80ffc

def z55 : W := mkw 0xbc93ffbff8244e45 0x2f24ffeffe091391 0x7ffbfffff86cde4f 0xdffefffffe1b3793

def z56 : W := mkw 0x0280004405e03d01 0x00a0001101780f40 0x0000000007601800 0x4000000001d80600

def z57 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbf8fe0cf8ffde4f 0xfefe3f833e3ff793

def z58 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x000012000008c000 0x0000048000023000

def z59 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfffc720ff87cfe7f 0xffff1c83fe1f3f9f

def z60 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0xfffcfe3ff8ffffff 0xffff3f8ffe3fffff

def z61 : W := mkw 0xa393fa042efece47 0x28e4fe810bbfb391 0xfbfbfe0cffffde4f 0xfefeff833ffff793

def z62 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x841721c307102030 0x2105c870c1c4080c

def z63 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xc47fc1f007e02180 0xf11ff07c01f80860

def z64 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfeffe1ff07f03ff3 0xffbff87fc1fc0ffc

def z65 : W := mkw 0x2b23fe1166df82d2 0x4ac8ff8459b7e0b4 0xf7fffe3367ffe7f3 0xfdffff8cd9fff9fc

def z66 : W := mkw 0x0000004001003000 0x0000001000400c00 0xce3f01c007003802 0x738fc07001c00e00

def z67 : W := mkw 0x004000000218002a 0x801000000086000a 0x000000000018007d 0x000000000006001f

def z68 : W := mkw 0x3f83ffffd7fabd03 0x0fe0fffff5feaf40 0xffffffffffffff83 0xffffffffffffffe0

def z69 : W := mkw 0x00200000200502d0 0x40080000080140b4 0xf3cc0000609727f3 0xbcf300001825c9fc

def z70 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1863c1fc07e01f80 0xc618f07f01f807e0

def z71 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x1140ce3c78000000 0x0450338f1e000000

def z72 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x082353cc98000000 0x0208d4f326000000

def z73 : W := mkw 0x3c0135bbd0000000 0x0f004d6ef4000000 0x3ebb31fff8000000 0x0faecc7ffe000000

def z74 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0xc140ce0007ffc001 0xf050338001fff000

def z75 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x2ebb31c380000000 0x0baecc70e0000000

def z76 : W := mkw 0x1000012800000000 0x0400004a00000000 0x1e0001fc00000000 0x0780007f00000000

def z77 : W := mkw 0x8090000428244e45 0x202400010a091391 0x4820520c986cde4f 0xd2081483261b3793

def z78 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0xc07bc00007e00000 0xf01ef00001f80000

def z79 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0xc00400000718387f 0x7001000001c60e1f

def z80 : W := mkw 0x8090000428244e45 0x202400010a091391 0x40000000006cde4f 0xd0000000001b3793

def z81 : W := mkw 0x0000000020040240 0x0000000008010090 0xf3d8ac0060970643 0xbcf62b001825c190

def z82 : W := mkw 0x0000000020040240 0x0000000008010090 0x73c8000060040643 0x9cf2000018010190

def z83 : W := mkw 0x204130828218002a 0x88104c20a086000a 0x208030038018007d 0x08200c00e006001f

def z84 : W := mkw 0x3c03ff3950000000 0x0f00ffce54000000 0x11fbfe3c78000000 0x047eff8f1e000000

def z85 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0xbffffffff89321b0 0x2ffffffffe24c86c

def z86 : W := mkw 0x08200451610532d0 0x4208011458414cb4 0xffffadf367973ff3 0xffffeb7cd9e5cffc

def z87 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfeffd1fc87e83fcf 0xffbff47f21fa0ff3

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x41e85200006cc001 0xd07a1480001b3000

def z89 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xfeffb1f387983fff 0xffbfec7ce1e60fff

def z90 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x3ffbffffff68c000 0x4ffeffffffda3000

def z91 : W := mkw 0x1082c16c01203d01 0x0420b05b00480f40 0x1e7fc1fc00003f82 0x079ff07f00000fe0

def z92 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff8802782 0xbffffffffe2009e0

def z93 : W := mkw 0x0000000020040240 0x0000000008010090 0x2180000060040041 0x0860000018010010

def z94 : W := mkw 0x0380004407fabd03 0x00e0001101feaf40 0xc004000007ffff83 0xf001000001ffffe0

def z95 : W := mkw 0x8010000028044244 0x200400000a011091 0x21801200f80cc04d 0x086004803e033013

def z96 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xf7dcbe33f89fe7ff 0xbdf72f8cfe27f9ff

def z97 : W := mkw 0x286134d3e31d32fa 0xca184d34f8c74cbe 0xffffbdf3e79f3fff 0xffffef7cf9e7cfff

def z98 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x11408c3060870780 0x8450230c1821c1e0

def z99 : W := mkw 0x8090000428244e45 0x202400010a091391 0x1140420c7864c600 0x845010831e193180

def z100 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xb614ac33609327f2 0x2d852b0cd824c9fc

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x1658803000000000 0x0596200c00000000

def z102 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0x0140ce0000e7c000 0x805033800039f000

def z103 : W := mkw 0x0000000020040240 0x0000000008010090 0x3200000060000642 0x0c80000018000190

def z104 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0x7fec523ff86cffff 0xdffb148ffe1b3fff

def z105 : W := mkw 0x8090000408204c05 0x2024000102081301 0x0820520c9868d80c 0x42081483261a3603

def z106 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3a00000cf8001e4e 0x0e8000033e000793

def z107 : W := mkw 0x0000004001003000 0x0000001000400c00 0xc004000007003802 0x7001000001c00e00

def z108 : W := mkw 0x1a22c57965c533d0 0x4688b15e59714cf4 0xf7dfadf3679727f3 0xbdf7eb7cd9e5c9fc

def z109 : W := mkw 0x0800041140000000 0x0200010450000000 0x37d8ac3360000000 0x0df62b0cd8000000

def z110 : W := mkw 0x3243f1ea87d8312a 0x8c90fc7aa1f60c4a 0xeebfb1f3879839ff 0x7bafec7ce1e60e7f

def z111 : W := mkw 0x3f43fffbd7dab02a 0x8fd0fffef5f6ac0a 0xfffffffffffff87f 0xfffffffffffffe1f

def z112 : W := mkw 0x2001300002180002 0x08004c0000860000 0xe6bf300307182073 0x79afcc00c1c6081c

def z113 : W := mkw 0x3003f1aa80000000 0x0c00fc6aa0000000 0x3efbf1ff80000000 0x0fbefc7fe0000000

def z114 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0x2e0401c38000387e 0x0b810070e0000e1f

def z115 : W := mkw 0x2001300002180002 0x08004c0000860000 0x8013200007100000 0x2004c80001c40000

def z116 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x8193be00079fc001 0x2064ef8001e7f000

def z117 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc000000007ffc001 0xf000000001fff000

def z118 : W := mkw 0x3e83ffffd5e03d01 0x0fa0fffff5780f40 0xffffffffffe03f82 0xfffffffffff80fe0

def z119 : W := mkw 0x22c130c687f83d2b 0x88b04c31a1fe0f4a 0xeebf31c387f83fff 0xfbafcc70e1fe0fff

def z120 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x3ffbd3fcf8000000 0x0ffef4ff3e000000

def z121 : W := mkw 0x32c3f1ee87f83d2b 0x8cb0fc7ba1fe0f4a 0xfefff1ff87f83fff 0xffbffc7fe1fe0fff

def z122 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x1e7bc1fc00000000 0x079ef07f00000000

def z123 : W := mkw 0x23013a0006da8002 0x08c04e8001b6a000 0xc1803e0007ffc001 0xf0600f8001fff000

def z124 : W := mkw 0x08600451631d32fa 0xc218011458c74cbe 0xf7dcac33679f3fff 0xfdf72b0cd9e7cfff

def z125 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0xfbec520cf8ffffff 0xfefb14833e3fffff

def z126 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc07bec0007f30000 0xf01efb0001fcc000

def z127 : W := mkw 0x1382cb6c05e2bd01 0x04e0b2db0178af40 0xdf7fcffc07e7ff82 0xf7dff3ff01f9ffe0

def z128 : W := mkw 0x0820041140010090 0x4208010450004024 0xe69cac33009321f3 0x39a72b0cc024c87c

def z129 : W := mkw 0x204130828218002a 0x88104c20a086000a 0xe69c30038018207f 0x39a70c00e006081f

def z130 : W := mkw 0x0000004001003000 0x0000001000400c00 0xde7f81f007803f82 0xf79fe07c01e00fe0

def z131 : W := mkw 0x00200000200502d0 0x40080000080140b4 0xc0040000009727f3 0xb00100000025c9fc

def z132 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0xc9fbffcc9fffc001 0xf27efff327fff000

def z133 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x41eb5200076cc001 0xd07ad48001db3000

def z134 : W := mkw 0x30c131ee83383d2b 0x8c304c7ba0ce0f4a 0xfebf31ff87183fff 0x7fafcc7fe1c60fff

def z135 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0xde3f01fc07003f82 0x778fc07f01c00fe0

def z136 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefff73c3877cf87f 0xfbffdcf0e1df3e1f

def z137 : W := mkw 0x2003fa0002180002 0x0800fe8000860000 0xc1fbfe0007180001 0x707eff8001c60000

def z138 : W := mkw 0x2c013e93d0000000 0x0b004fa4f4000000 0x37d8be33f8000000 0x0df62f8cfe000000

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0x4068400000600000 0xd01a100000180000

def z140 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0x5a68c03c00e01f82 0xd69a300f003807e0

def z141 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0xffdcac3ff8973fff 0xbff72b0ffe25cfff

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x2080200300100071 0x08200800c004001c

def z143 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e2741fc07603f82 0x4789d07f01d80fe0

def z144 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffbfffff8970001 0xbffefffffe25c000

def z145 : W := mkw 0x0000000020040240 0x0000000008010090 0x7be8520cf8040643 0x9efa14833e010190

def z146 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc1d8ac0007ffc001 0xf0762b0001fff000

def z147 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x3f803ffff8000000 0x0fe00ffffe000000

def z148 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0x082353c08768d80c 0x4208d4f021da3603

def z149 : W := mkw 0x8090000428244e45 0x202400010a091391 0x0000000000001e4e 0x0000000000000793

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x1040803000800780 0x8410200c002001e0

def z151 : W := mkw 0x0800041140000000 0x0200010450000000 0x21802c0360000000 0x08600b00d8000000

def z152 : W := mkw 0x286134d3c31930ba 0xca184d34f0c64c2e 0xeebfbdf3879b39ff 0x7bafef7ce1e6ce7f

def z153 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0xee3f01c38700387e 0x7b8fc070e1c00e1f

def z154 : W := mkw 0x3303fb2806da8002 0x0cc0feca01b6a000 0xdffbfffc07ffc001 0xf7feffff01fff000

def z155 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf6040033609727f3 0xbd81000cd825c9fc

def z156 : W := mkw 0x286134d3e31d32fa 0xca184d34f8c74cbe 0xefbf3dc3e71f387f 0x7befcf70f9c7ce1f

def z157 : W := mkw 0x28613493e21d02fa 0xca184d24f88740be 0x21803c03e01f007d 0x08600f00f807c01f

def z158 : W := mkw 0x3383fb6c07fabd03 0x0ce0fedb01feaf40 0xde7fd3fc07e8ff82 0xf79ff4ff01fa3fe0

def z159 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01fbfe000768c000 0x407eff8001da3000

def z160 : W := mkw 0xac913e97f8244e45 0x2b244fa5fe091391 0x7be87e0ff86cde4f 0xdefa1f83fe1b3793

def z161 : W := mkw 0xa313fa002edec246 0x28c4fe800bb7b091 0xe1fbfe00ffffc04d 0xf87eff803ffff013

def z162 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1553efff78000000 0x0554fbffde000000

def z163 : W := mkw 0xac113e93f8044244 0x2b044fa4fe011091 0x21803e03f80cc04d 0x08600f80fe033013

def z164 : W := mkw 0x0080004401203d01 0x0020001100480f40 0x0004000000003f82 0x0001000000000fe0

def z165 : W := mkw 0x3c83ffbfd0200c01 0x0f20ffeff4080300 0x7ffbfffff8601e02 0xdffefffffe180780

def z166 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xae1721c38710387e 0x2b85c870e1c40e1f

def z167 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xbffbffffff930000 0x2ffeffffffe4c000

def z168 : W := mkw 0x18a0057d61253fd1 0x4628015f58494ff4 0x3e0401ff60003ff2 0x0f81007fd8000ffc

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e3b01c000000000 0x038ec07000000000

def z170 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0x41e8de0000efc001 0xd07a3780003bf000

def z171 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7fcfe3360ffe7f3 0xfdff3f8cd83ff9fc

def z172 : W := mkw 0x02a0004425e53fd1 0x40a8001109794ff4 0xc004000007f73ff3 0xf001000001fdcffc

def z173 : W := mkw 0x28013493c0000000 0x0a004d24f0000000 0x3ffbbdf3e0000000 0x0ffeef7cf8000000

def z174 : W := mkw 0xa0d130c6ab3c7e6f 0xa8344c31aacf1f9b 0xffff73cfff7cfe7f 0xffffdcf3ffdf3f9f

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x21801200f8000000 0x086004803e000000

def z176 : W := mkw 0x80d000442b3c7e6f 0xa03400110acf1f9b 0xc0040000077cfe7f 0xf001000001df3f9f

def z177 : W := mkw 0xbc93ffbff8244e45 0x2f24ffeffe091391 0x3ffbfffff864c600 0x8ffefffffe193180

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x3be8520cf8000000 0x0efa14833e000000

def z179 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xfbfbfe0cffffc001 0xfefeff833ffff000

def z180 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x1e7bd3fc98000000 0x079ef4ff26000000

def z181 : W := mkw 0x8010000028044244 0x200400000a011091 0x6ba81200f80cd84f 0x5aea04803e033613

def z182 : W := mkw 0x8010000028044244 0x200400000a011091 0x20000000f800004c 0x080000003e000013

def z183 : W := mkw 0x0800041140000000 0x0200010450000000 0x3600003360000000 0x0d80000cd8000000

def z184 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x05fbfff300000000 0x017efffcc0000000

def z185 : W := mkw 0x9292c16c2de47f45 0x24a4b05b0b791fd1 0xde7fc1fc07ecffcf 0xf79ff07f01fb3ff3

def z186 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0xefffffc387fff87f 0xfbfffff0e1fffe1f

def z187 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3e13adfff8000000 0x0f84eb7ffe000000

def z188 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xc4bf31c307182031 0x712fcc70c1c6080c

def z189 : W := mkw 0x2003fa8280000000 0x0800fea0a0000000 0x2ffbffc380000000 0x0bfefff0e0000000

def z190 : W := mkw 0x0000004001003000 0x0000001000400c00 0x841701c007002000 0x2105c07001c00800

def z191 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x41e87e00007fc001 0xd07a1f80001ff000

def z192 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefffbdc3879f387f 0xfbffef70e1e7ce1f

def z193 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e7bc1fc07601800 0x479ef07f01d80600

def z194 : W := mkw 0x1c2005bbf00502d0 0x4708016efc0140b4 0xffdcadfff89727f3 0xbff72b7ffe25c9fc

def z195 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0x00002c0000130000 0x00000b000004c000

def z196 : W := mkw 0x1f02cf3954c28000 0x07c0b3ce5530a000 0x1140ce3c78e7c000 0x8450338f1e39f000

def z197 : W := mkw 0x8090000428244e45 0x202400010a091391 0x41e85200006cde4f 0xd07a1480001b3793

def z198 : W := mkw 0x3c03fffbd1003000 0x0f00fffef4400c00 0xffffffffff003802 0x7fffffffffc00e00

def z199 : W := mkw 0x0002ca0000000000 0x0000b28000000000 0x0140ce0000000000 0x0050338000000000

def z200 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x3ffb73cff8000000 0x0ffedcf3fe000000

def z201 : W := mkw 0x1c00053950000000 0x0700014e54000000 0x1000003c78000000 0x0400000f1e000000

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x01d8ac0000000000 0x00762b0000000000

def z203 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xe79c2c0360172073 0x39e70b00d805c81c

def z204 : W := mkw 0x00200000200502d0 0x40080000080140b4 0xd65c8030009727f3 0xb597200c0025c9fc

def z205 : W := mkw 0x0280004405e03d01 0x00a0001101780f40 0xda6c400c07e03f82 0xf69b100301f80fe0

def z206 : W := mkw 0x24013a8290000000 0x09004ea0a4000000 0x0000120098000000 0x0000048026000000

def z207 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd75c8c3060872782 0xb5d7230c1821c9e0

def z208 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xd7fffe3007ffe783 0xf5ffff8c01fff9e0

def z209 : W := mkw 0x8090000428244e45 0x202400010a091391 0x5b68420c7864de02 0xd6da10831e193780

def z210 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc0bb300007180001 0x702ecc0001c60000

def z211 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x28a331c38718187d 0x4a28cc70e1c6061f

def z212 : W := mkw 0x0000000020040240 0x0000000008010090 0x7be81000e00c1e4f 0xdefa040038030793

def z213 : W := mkw 0x33c3fbee87fabd2b 0x8cf0fefba1feaf4a 0xffffffff87ffffff 0xffffffffe1ffffff

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x6be85200806cd84f 0xdafa1480201b3613

def z215 : W := mkw 0xabb3fe156effced7 0x6aecff855bbff3b5 0xfffffe3fffffffff 0xffffff8fffffffff

def z216 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0x8417adc307932030 0x2105eb70c1e4c80c

def z217 : W := mkw 0x21413ac2831ab02a 0x88504eb0a0c6ac0a 0xefbf3fc3871ff87f 0x7befcff0e1c7fe1f

def z218 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xffff73cfff18387f 0x7fffdcf3ffc60e1f

def z219 : W := mkw 0x3c23ffbbf00502d0 0x4f08ffeefc0140b4 0x3ffffffff80027f2 0x0ffffffffe0009fc

def z220 : W := mkw 0x3c43ffbbd218002a 0x8f10ffeef486000a 0x3ffbfffff818007d 0x0ffefffffe06001f

def z221 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff86cc001 0xdffefffffe1b3000

def z222 : W := mkw 0x286134d3e31d32fa 0xca184d34f8c74cbe 0xf7dfadf3679727f3 0xbdf7eb7cd9e5c9fc

def z223 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3e2353fff8000000 0x0f88d4fffe000000

def z224 : W := mkw 0x206130c2a31d32fa 0xc8184c30a8c74cbe 0xeebf31c3879f3fff 0xfbafcc70e1e7cfff

def z225 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcbc33e09f3fff 0xffff2f0cf827cfff

def z226 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0x1e7bc1fc00e00780 0x879ef07f003801e0

def z227 : W := mkw 0x80d000442b3c7e6f 0xa03400110acf1f9b 0xfbec520cff7cfe7f 0xfefb14833fdf3f9f

def z228 : W := mkw 0xa0d130c68b387c2f 0xa8344c31a2ce1f0b 0x082353cc9f68d80c 0x4208d4f327da3603

def z229 : W := mkw 0x0282c04405e03d01 0x00a0b01101780f40 0xc07fc00007e03f82 0xf01ff00001f80fe0

def z230 : W := mkw 0xa0d130c6ab3c7e6f 0xa8344c31aacf1f9b 0xfebf31cfff183e7f 0x7fafcc73ffc60f9f

def z231 : W := mkw 0x3c23ffbbf00502d0 0x4f08ffeefc0140b4 0x3ffbfffff8870780 0x8ffefffffe21c1e0

def z232 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2e2711c38708387e 0x4b89c470e1c20e1f

def z233 : W := mkw 0xa09130042a3c4e47 0x28244c010a8f1391 0xfbfb720cff7cde4f 0xfefedc833fdf3793

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a00000cf8000000 0x0e8000033e000000

def z235 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3fe853fff8000000 0x0ffa14fffe000000

def z236 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xe1842c03609727f3 0xb8610b00d825c9fc

def z237 : W := mkw 0x0820041140010090 0x4208010450004024 0xc5dcac33009721b1 0xb1772b0cc025c86c

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x41c8000000040001 0x9072000000010000

def z239 : W := mkw 0x204130828218002a 0x88104c20a086000a 0x0000200300100030 0x00000800c004000c

def z240 : W := mkw 0x1002c16801003000 0x0400b05a00400c00 0xde7fc1fc07003802 0x779ff07f01c00e00

def z241 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff8102073 0x3ffffffffe04081c

def z242 : W := mkw 0x0820041140010090 0x4208010450004024 0xd65cac33009327b2 0xb5972b0cc024c9ec

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x5248000000000602 0x9492000000000180

def z244 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0x7be87e0ff87fde7f 0xdefa1f83fe1ff79f

def z245 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0x21803e03f81fc07d 0x08600f80fe07f01f

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0xc03b000007000000 0x700ec00001c00000

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x7be8520cf808184f 0x5efa14833e020613

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x8414200300102030 0x21050800c004080c

def z249 : W := mkw 0x1aa2c53d64e50fd1 0x46a8b14f593943f4 0xf7dcec3f60f727f3 0xbdf73b0fd83dc9fc

def z250 : W := mkw 0xa1113a002a1ec246 0x28444e800a87b091 0x21803e00f81fc04d 0x08600f803e07f013

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z252 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdfffedfc07f73f83 0xf7fffb7f01fdcfe0

def z253 : W := mkw 0x0820041140010090 0x4208010450004024 0x04040033000021b0 0x0101000cc000086c

def z254 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xde7fd3fc9fe8ff8e 0xf79ff4ff27fa3fe3

def z255 : W := mkw 0xbc13ffbbf8044244 0x2f04ffeefe011091 0x3ffbfffff80cc04d 0x0ffefffffe033013

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x1140420c78000000 0x045010831e000000

def z257 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xe69f21c307102073 0x39a7c870c1c4081c

def z258 : W := mkw 0x3383fb6c07fabd03 0x0ce0fedb01feaf40 0x082353cc0768d800 0x4208d4f301da3600

def z259 : W := mkw 0x8090000428244e45 0x202400010a091391 0x61801200f86cde4f 0xd86004803e1b3793

def z260 : W := mkw 0x0040004001003028 0x8010001000400c0a 0x000400000000387e 0x0001000000000e1f

def z261 : W := mkw 0x0800041140000000 0x0200010450000000 0x0410ac3300000000 0x01042b0cc0000000

def z262 : W := mkw 0x2001308280000000 0x08004c20a0000000 0xeebf31c380102073 0x3bafcc70e004081c

def z263 : W := mkw 0x0b20041166df82d2 0x42c8010459b7e0b4 0xf7dcac3367ffe7f3 0xfdf72b0cd9fff9fc

def z264 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3b40420cf864de4e 0x8ed010833e193793

def z265 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xc41721c30718387f 0x7105c870c1c60e1f

def z266 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xe7fffe0307ffe073 0xf9ffff80c1fff81c

def z267 : W := mkw 0x1a82c57d45e03d01 0x06a0b15f51780f40 0xffffedff67e03f82 0xfffffb7fd9f80fe0

def z268 : W := mkw 0x8090000408204c05 0x2024000102081301 0x6aa8520c9868d84f 0x5aaa1483261a3613

def z269 : W := mkw 0x3c43fffbd318302a 0x8f10fffef4c60c0a 0x8417adf307102030 0x2105eb7cc1c4080c

def z270 : W := mkw 0xa393fa042efece47 0x28e4fe810bbfb391 0xd1fbfe0c7fffc601 0xf47eff831ffff180

def z271 : W := mkw 0xbf93ffbffefece47 0x2fe4ffefffbfb391 0xfffbffffffffde4f 0xfffefffffffff793

def z272 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0xeebfbdc3879b387f 0x7bafef70e1e6ce1f

def z273 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x29a37fcff8000000 0x0a68dff3fe000000

def z274 : W := mkw 0x8090000428244e45 0x202400010a091391 0x1960520cf86cde0c 0xc65814833e1b3783

def z275 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0xde5c81fc00803f82 0xb797207f00200fe0

def z276 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x37dcac33600027f2 0x0df72b0cd80009fc

def z277 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xc414ac33009727f3 0xb1052b0cc025c9fc

def z278 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004000000102073 0x300100000004081c

def z279 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdfffd3fc07ecff83 0xf7fff4ff01fb3fe0

def z280 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0xc004000000ffffff 0xf0010000003fffff

def z281 : W := mkw 0x2001300002180002 0x08004c0000860000 0xeabb30008718184f 0x7aaecc0021c60613

def z282 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1963dffcf8000000 0x0658f7ff3e000000

def z283 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xd65f81f007802782 0xb597e07c01e009e0

def z284 : W := mkw 0x00200000200502d0 0x40080000080140b4 0xc1dcac00009727f3 0xb0772b000025c9fc

def z285 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0xfffbffffffe00000 0xfffefffffff80000

def z286 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xe1d8ac0360970071 0xb8762b00d825c01c

def z287 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0xf7dcac3360ffffff 0xfdf72b0cd83fffff

def z288 : W := mkw 0x0080000400200c01 0x0020000100080300 0x5be8520c006cde03 0xd6fa1483001b3780

def z289 : W := mkw 0x1c02c5bbd0000000 0x0700b16ef4000000 0x3e7bc1fff8000000 0x0f9ef07ffe000000

def z290 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff808184f 0x5ffefffffe020613

def z291 : W := mkw 0x0000000000000000 0x0000000000000000 0x0820520c98000000 0x0208148326000000

def z292 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0xc1fbec0007f70001 0xf07efb0001fdc000

def z293 : W := mkw 0x2b23fe1166df82d2 0x4ac8ff8459b7e0b4 0xe1fbfe0367ffc071 0xf87eff80d9fff01c

def z294 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1dbac0007970001 0xb076eb0001e5c000

def z295 : W := mkw 0x3383fb6c07fabd03 0x0ce0fedb01feaf40 0xc9fbffcc07ffd801 0xf27efff301fff600

def z296 : W := mkw 0x286134d3c31930ba 0xca184d34f0c64c2e 0x8417adf3079321b0 0x2105eb7cc1e4c86c

def z297 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0xfffbffffff180001 0x7ffeffffffc60000

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0xc1f8fe0000ffc001 0xf07e3f80003ff000

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x4a28000000001802 0x528a000000000600

def z300 : W := mkw 0x0000000020040240 0x0000000008010090 0xf7dc200360142673 0xbdf70800d805099c

def z301 : W := mkw 0xb493fbae98204c05 0x2d24feeba6081301 0x082353cc9868d80c 0x4208d4f3261a3603

def z302 : W := mkw 0x00200000200502d0 0x40080000080140b4 0x0000000000870780 0x800000000021c1e0

def z303 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x1f7bcffc78000000 0x07def3ff1e000000

def z304 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9e1781fc07803f82 0x2785e07f01e00fe0

def z305 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x77cc0033600427f3 0x9df3000cd80109fc

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x2698200300000000 0x09a60800c0000000

def z307 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3fd8adfff8000000 0x0ff62b7ffe000000

def z308 : W := mkw 0xa0d13086aa3c4e6f 0xa8344c21aa8f139b 0x7be8720ff87cde7f 0xdefa1c83fe1f379f

def z309 : W := mkw 0x28213493e00502d0 0x4a084d24f80140b4 0xffffbdf3e09727f3 0xbfffef7cf825c9fc

def z310 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0x0023400007600000 0x4008d00001d80000

def z311 : W := mkw 0x0800041160040240 0x0200010458010090 0x77d8ac3360040643 0x9df62b0cd8010190

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x01408c0000870000 0x805023000021c000

def z313 : W := mkw 0x284134d3c318302a 0x8a104d34f0c60c0a 0xffffbdf3e718387f 0x7fffef7cf9c60e1f

def z314 : W := mkw 0x3303fb6807dab102 0x0cc0feda01f6ac40 0x8417adf007932180 0x2105eb7c01e4c860

def z315 : W := mkw 0x3f03ffbbd4c28000 0x0fc0ffeef530a000 0x3ffbfffff8e7c000 0x8ffefffffe39f000

def z316 : W := mkw 0x80d000c6a9247e6d 0xa0340031aa491f9b 0x3e0401cff8003e7e 0x0f810073fe000f9f

def z317 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0x8013800007800000 0x2004e00001e00000

def z318 : W := mkw 0x204130400318302a 0x88104c1000c60c0a 0xc0bf30000718387f 0x702fcc0001c60e1f

def z319 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc013ac0007ffc001 0xf004eb0001fff000

def z320 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x01fbfe0000000000 0x007eff8000000000

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x01802c0000170001 0x00600b000005c000

def z322 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xc8bb31c08718180d 0x722ecc7021c60603

def z323 : W := mkw 0x9090016c29247f45 0x2424005b0a491fd1 0x3e0401fcf8003fce 0x0f81007f3e000ff3

def z324 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x8413adf307930000 0x2104eb7cc1e4c000

def z325 : W := mkw 0x2001300002180002 0x08004c0000860000 0x0023100007080000 0x4008c40001c20000

def z326 : W := mkw 0x9092c12c28244e45 0x2424b04b0a091391 0x7ffbd3fcf86cde4f 0xdffef4ff3e1b3793

def z327 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcfe3ff89727f3 0xbfff3f8ffe25c9fc

def z328 : W := mkw 0x0040008280000028 0x80100020a000000a 0x200000038000007c 0x08000000e000001f

def z329 : W := mkw 0x1e82c5ffd5e03d01 0x07a0b17ff5780f40 0xfe7fc1ffffe03f82 0xff9ff07ffff80fe0

def z330 : W := mkw 0xa0d130c6ab3c7e6f 0xa8344c31aacf1f9b 0xeebf31c3877cfe7f 0xfbafcc70e1df3f9f

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x6288000000000043 0x18a2000000000010

def z332 : W := mkw 0xa0d130c6ab3c7e6f 0xa8344c31aacf1f9b 0x7beb53ccff6cde4f 0xdefad4f33fdb3793

def z333 : W := mkw 0x1c22cf39700502d0 0x4708b3ce5c0140b4 0x1140ce3c78870780 0x8450338f1e21c1e0

def z334 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0x8004000007102030 0x2001000001c4080c

def z335 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0x082353cc9f68c000 0x4208d4f327da3000

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x8414803000802180 0x2105200c00200860

def z337 : W := mkw 0x1aa2c57d65e53fd1 0x46a8b15f59794ff4 0xffffedff67f73ff3 0xfffffb7fd9fdcffc

def z338 : W := mkw 0x204130828218002a 0x88104c20a086000a 0x000010008008000c 0x0000040020020003

def z339 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x0003000007000000 0x0000c00001c00000

def z340 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x3beb53ccf8000000 0x0efad4f33e000000

def z341 : W := mkw 0x8010000028044244 0x200400000a011091 0x010002007804c000 0x004000801e013000

def z342 : W := mkw 0x0080000420240e41 0x0020000108090390 0x7be8400c60641e43 0xdefa100318190790

def z343 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0xc1d8ee0000f7c001 0xb0763b80003df000

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0x082010008008180c 0x4208040020020603

def z345 : W := mkw 0x32c3f1ee87f83d2b 0x8cb0fc7ba1fe0f4a 0xde7fd1fc87e83f8e 0xf79ff47f21fa0fe3

def z346 : W := mkw 0x02c0004407f83d2b 0x80b0001101fe0f4a 0xc004000007f83fff 0xf001000001fe0fff

def z347 : W := mkw 0x3f03ff3956da8002 0x0fc0ffce55b6a000 0xd1fbfe3c7fffc001 0xf47eff8f1ffff000

def z348 : W := mkw 0x1202c12804c00000 0x0480b04a01300000 0xde7bc1fc07e00000 0xf79ef07f01f80000

def z349 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0x0000400c00600000 0x0000100300180000

def z350 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7aa8100cf8081e4f 0x5eaa04033e020793

def z351 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x041321c300000000 0x0104c870c0000000

def z352 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xc82741cc07e03f82 0xf209d07301f80fe0

def z353 : W := mkw 0x8090000408204c05 0x2024000102081301 0x5a68520c9868de0e 0xd69a1483261a3783

def z354 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0x000042000060c000 0x0000108000183000

def z355 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0x000000000768c000 0x4000000001da3000

def z356 : W := mkw 0x3f23ffbbf6df82d2 0x4fc8ffeefdb7e0b4 0xffffffffffffe7f3 0xfffffffffffff9fc

def z357 : W := mkw 0x3d03ffbbd21a8002 0x0f40ffeef486a000 0x3ffbfffff81fc001 0x0ffefffffe07f000

def z358 : W := mkw 0x0000004001003000 0x0000001000400c00 0xeebf11c08708384f 0x7bafc47021c20e13

def z359 : W := mkw 0x286134d3e31d32fa 0xca184d34f8c74cbe 0xfebf31f3e7183fff 0x7fafcc7cf9c60fff

def z360 : W := mkw 0x2c013e93d0000000 0x0b004fa4f4000000 0x2fbb3fc3f8000000 0x0beecff0fe000000

def z361 : W := mkw 0x3443fbea9318302a 0x8d10fefaa4c60c0a 0x082353cc9f08180c 0x4208d4f327c20603

def z362 : W := mkw 0x0280004405e03d01 0x00a0001101780f40 0xd65c803007e03f82 0xf597200c01f80fe0

def z363 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xce3f21c307103832 0x738fc870c1c40e0c

def z364 : W := mkw 0x12c2c16c07f83d2b 0x84b0b05b01fe0f4a 0xde7fc1fc07f83fff 0xf79ff07f01fe0fff

def z365 : W := mkw 0x1202c12804c00100 0x0480b04a01300040 0x0000803000800180 0x0000200c00200060

def z366 : W := mkw 0x1e82cf3d54e00d01 0x07a0b3cf55380340 0x1140ce3c78e00780 0x8450338f1e3801e0

def z367 : W := mkw 0x2d013e93d21a8002 0x0b404fa4f486a000 0x21803e03f81fc001 0x08600f80fe07f000

def z368 : W := mkw 0x28213411621d02d2 0x4a084d04588740b4 0xf7ffbc33679f27f3 0xfdffef0cd9e7c9fc

def z369 : W := mkw 0x839000042efece47 0x20e400010bbfb391 0xc000000007ffde4f 0xf000000001fff793

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x208010008008004d 0x0820040020020013

def z371 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0x082353cc9f68d80c 0x4208d4f327da3603

def z372 : W := mkw 0x204130828218002a 0x88104c20a086000a 0x6aa830038018187f 0x5aaa0c00e006061f

def z373 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x37448c33608727f2 0x8dd1230cd821c9fc

def z374 : W := mkw 0x2301300006da8002 0x08c04c0001b6a000 0xc0bb300007ffc001 0xf02ecc0001fff000

def z375 : W := mkw 0x9292c16c2de47f45 0x24a4b05b0b791fd1 0xdf7fc3fc7fe4ff82 0xf7dff0ff1ff93fe0

def z376 : W := mkw 0x00200000200502d0 0x40080000080140b4 0xe69c2003009727f3 0xb9a70800c025c9fc

def z377 : W := mkw 0x8090000428244e45 0x202400010a091391 0x6aa81000806cde4f 0xdaaa0400201b3793

def z378 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc0bbbc00079b0001 0x702eef0001e6c000

def z379 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x37842c33601727f3 0x0de10b0cd805c9fc

def z380 : W := mkw 0x1aa2c57d45e13d91 0x46a8b15f51784f64 0xde7fedff07f33fb2 0xf79ffb7fc1fccfec

def z381 : W := mkw 0x0000000020040240 0x0000000008010090 0xf7dc8030608427c3 0xbdf7200c182109f0

def z382 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0xc1bb3e00071fc001 0x706ecf8001c7f000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0xe7dcac0300972073 0xb9f72b00c025c81c

def z384 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x0013ac0000000000 0x0004eb0000000000

def z385 : W := mkw 0xb393fb6c2ffeff47 0x2ce4fedb0bffbfd1 0xfffffffcffffffcf 0xffffffff3ffffff3

def z386 : W := mkw 0x2203fa0004c00000 0x0880fe8001300000 0xc1fbfe0007e00000 0xf07eff8001f80000

def z387 : W := mkw 0x0080000400200c01 0x0020000100080300 0x7be8520cf8601e02 0xdefa14833e180780

def z388 : W := mkw 0x0340004007dab02a 0x80d0001001f6ac0a 0xc004000007fff87f 0xf001000001fffe1f

def z389 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x81fbfe0007930000 0x207eff8001e4c000

def z390 : W := mkw 0x18a0057d61253fd1 0x4628015f58494ff4 0xffdcadff60973ff3 0xbff72b7fd825cffc

def z391 : W := mkw 0x2103fa00021a8002 0x0840fe800086a000 0x01fbfe00001fc001 0x007eff800007f000

def z392 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x0023520000000000 0x0008d48000000000

def z393 : W := mkw 0x8010000028044244 0x200400000a011091 0x61e85200f86cc04d 0xd87a14803e1b3013

def z394 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x3bfbfe0cf8000000 0x0efeff833e000000

def z395 : W := mkw 0x0080004401203c01 0x0020001100480f00 0xde7f41cc07603e02 0xf79fd07301d80f80

def z396 : W := mkw 0x8090004429247e45 0x202400110a491f91 0xffff53ccff6cfe4f 0xffffd4f33fdb3f93

def z397 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0xf7dcee3f78f7e7f3 0xbdf73b8fde3df9fc

def z398 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x2ebbbdf380000000 0x0baeef7ce0000000

def z399 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0x040401c300002030 0x01010070c000080c

def z400 : W := mkw 0x0280004405e03d01 0x00a0001101780f40 0xce3f01c007e03f82 0xf38fc07001f80fe0

def z401 : W := mkw 0xbc93ffbff8244e45 0x2f24ffeffe091391 0x3ffbfffff8001e4e 0x0ffefffffe000793

def z402 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x0c33ffff98000000 0x030cffffe6000000

def z403 : W := mkw 0x2b23fe1146db8092 0x4ac8ff8451b6e024 0xc5fffe3307ffe1b1 0xf17fff8cc1fff86c

def z404 : W := mkw 0x2243f0c287d8302a 0x8890fc30a1f60c0a 0xeefff1c387f8387f 0xfbbffc70e1fe0e1f

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0xc61c000000002002 0x3187000000000800

def z406 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3a20520cf868de4e 0x4e8814833e1a3793

def z407 : W := mkw 0x0002c00000000000 0x0000b00000000000 0x007bc00000000000 0x001ef00000000000

def z408 : W := mkw 0x1822c539600502d0 0x4608b14e580140b4 0xffffedff609727f3 0xbffffb7fd825c9fc

def z409 : W := mkw 0x204130828218002a 0x88104c20a086000a 0x2ebb31c38018007d 0x0baecc70e006001f

def z410 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9457c1fc07e02780 0xa515f07f01f809e0

def z411 : W := mkw 0x8090000408204c05 0x2024000102081301 0x3be8520cf868d80c 0x4efa14833e1a3603

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0xeebc30038018387f 0x7baf0c00e0060e1f

def z413 : W := mkw 0x9292c16c2de47f45 0x24a4b05b0b791fd1 0xfe7fc1fcffe03fce 0xff9ff07f3ff80ff3

def z414 : W := mkw 0x2b63fed3e7dfb2fa 0xcad8ffb4f9f7ecbe 0xfffffff3e7ffffff 0xfffffffcf9ffffff

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0xf6dca033009027f3 0xbdb7280cc02409fc

def z416 : W := mkw 0x0280000404e00d01 0x00a0000101380340 0x0000000000e00780 0x80000000003801e0

def z417 : W := mkw 0x3c63fffbf31d32fa 0xcf18fffefcc74cbe 0xffffffffff9f3fff 0xffffffffffe7cfff

def z418 : W := mkw 0xa8f134d7eb3d7eff 0xea3c4d35facf5fbf 0xffffffffffffffff 0xffffffffffffffff

def z419 : W := mkw 0x8090000408204c05 0x2024000102081301 0x0000420c1860c000 0x0000108306183000

def z420 : W := mkw 0x0800041140000000 0x0200010450000000 0xf7dcac3360802782 0xbdf72b0cd82009e0

def z421 : W := mkw 0x2c013e93d0000000 0x0b004fa4f4000000 0x3be87e0ff8000000 0x0efa1f83fe000000

def z422 : W := mkw 0x839000042efece47 0x20e400010bbfb391 0xfbe8520cffffde4f 0xfefa14833ffff793

def z423 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x37d8ac3360170071 0x0df62b0cd805c01c

def z424 : W := mkw 0x1aa2c53d64e50fd1 0x46a8b14f593943f4 0x1140cc3c60e70780 0x8450330f1839c1e0

def z425 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0x080001cc00001800 0x0200007300000600

def z426 : W := mkw 0x32c3f1ee87f83d2b 0x8cb0fc7ba1fe0f4a 0x082351cc8768180c 0x4208d47321da0603

def z427 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0xeebf73c38778f87f 0x7bafdcf0e1de3e1f

def z428 : W := mkw 0x2383fa4407fabd03 0x08e0fe9101feaf40 0xc1fffe0007ffff83 0xf07fff8001ffffe0

def z429 : W := mkw 0x3283f16c07f83d03 0x0ca0fc5b01fe0f40 0xdefff1fc07f83f83 0xf7bffc7f01fe0fe0

def z430 : W := mkw 0x8090000428244e45 0x202400010a091391 0x5140420c786cde4f 0xd45010831e1b3793

def z431 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0x9e7fc1fc07802180 0x279ff07f01e00860

def z432 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x000301c007000000 0x0000c07001c00000

def z433 : W := mkw 0x2c03fe93d0000000 0x0b00ffa4f4000000 0x21fbfe03f8000000 0x087eff80fe000000

def z434 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x082341cc00000000 0x0208d07300000000

def z435 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x082311c080000000 0x0208c47020000000

def z436 : W := mkw 0x20013a0000000000 0x08004e8000000000 0x01803e0000000000 0x00600f8000000000

def z437 : W := mkw 0x1280016c05e03d01 0x04a0005b01780f40 0xde0401fc07e03f82 0xf781007f01f80fe0

def z438 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0x5e6c41fc00603f82 0xd79b107f00180fe0

def z439 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xc82711c08718387f 0x7209c47021c60e1f

def z440 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01c0fe0000ffc001 0x80703f80003ff000

def z441 : W := mkw 0x12c2c1ee85e03d29 0x84b0b07ba1780f4a 0xfe7fc1ff87e03ffe 0xff9ff07fe1f80fff

def z442 : W := mkw 0x086004d3e10532f8 0xc2180134f8414cbe 0x3e0401f3e0003ffe 0x0f81007cf8000fff

def z443 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x37d8ee3f78000000 0x0df63b8fde000000

def z444 : W := mkw 0x3043f1ea8318302a 0x8c10fc7aa0c60c0a 0xfefff1ff8718387f 0x7fbffc7fe1c60e1f

def z445 : W := mkw 0x2803fe1140000000 0x0a00ff8450000000 0x37fbfe3360000000 0x0dfeff8cd8000000

def z446 : W := mkw 0x3c03ffbbf0040240 0x0f00ffeefc010090 0x7ffbfffff8040643 0x9ffefffffe010190

def z447 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x31c0ac33609707f1 0x8c702b0cd825c1fc

def z448 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xce3f11c08708380e 0x738fc47021c20e03

def z449 : W := mkw 0x2001300000000000 0x08004c0000000000 0x00bb300000000000 0x002ecc0000000000

def z450 : W := mkw 0x3ea3fffff5e53fd1 0x4fa8fffffd794ff4 0xfffffffffff73ff3 0xfffffffffffdcffc

def z451 : W := mkw 0x204130828218002a 0x88104c20a086000a 0xe0bb30038718007d 0x782ecc00e1c6001f

def z452 : W := mkw 0x2c213e93f00502d0 0x4b084fa4fc0140b4 0xf7dcbe33f89727f3 0xbdf72f8cfe25c9fc

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x7be8520cf86cc001 0xdefa14833e1b3000

def z454 : W := mkw 0x0080000400200c01 0x0020000100080300 0x0820400c00601800 0x4208100300180600

def z455 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd1d8ac3060970781 0xb4762b0c1825c1e0

def z456 : W := mkw 0x0300000004c28000 0x00c000000130a000 0x0000000000e7c000 0x800000000039f000

def z457 : W := mkw 0x1402cb2810000000 0x0500b2ca04000000 0x0000420c18000000 0x0000108306000000

def z458 : W := mkw 0x00200000200502d0 0x40080000080140b4 0x00040000000027f2 0x00010000000009fc

def z459 : W := mkw 0x1000016801003100 0x0400005a00400c40 0x040401f000002180 0x0101007c00000860

def z460 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x2000000360000070 0x08000000d800001c

def z461 : W := mkw 0x9292c16c2de47f45 0x24a4b05b0b791fd1 0x7beb53ccff6cde4f 0xdefad4f33fdb3793

def z462 : W := mkw 0x80d000c6a9247e6d 0xa0340031aa491f9b 0x7fec53cff86cfe7f 0xdffb14f3fe1b3f9f

def z463 : W := mkw 0x1382cb2c04e28d01 0x04e0b2cb0138a340 0x1140ce3c00e7c780 0x8450338f0039f1e0

def z464 : W := mkw 0xa0913086a8244e45 0x28244c21aa091391 0x7ffb73cff86cde4f 0xdffedcf3fe1b3793

def z465 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xc41781f007e03f82 0xf105e07c01f80fe0

def z466 : W := mkw 0xbc93ffbfd8204c05 0x2f24ffeff6081301 0x3ffbfffff868d80c 0x4ffefffffe1a3603

def z467 : W := mkw 0x8010000008004004 0x2004000002001001 0x000012009808c00c 0x0000048026023003

def z468 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xce3f41cc07603802 0x738fd07301d80e00

def z469 : W := mkw 0x9090016c29247f45 0x2424005b0a491fd1 0x7fec53fcf86cffcf 0xdffb14ff3e1b3ff3

def z470 : W := mkw 0xa0513082aa1c426e 0xa8144c20aa87109b 0x21803203f81cc07d 0x08600c80fe07301f

def z471 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0x080001c08000180c 0x0200007020000603

def z472 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x6ebb31c38008184f 0x5baecc70e0020613

def z473 : W := mkw 0xbe93fffffde47f45 0x2fa4ffffff791fd1 0xffffffffffecffcf 0xfffffffffffb3ff3

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x002052000068c000 0x40081480001a3000

def z475 : W := mkw 0x1e82cf7d55e03d01 0x07a0b3df55780f40 0xdf7fcffc7fe03f82 0xf7dff3ff1ff80fe0

def z476 : W := mkw 0xa093fa0428244e45 0x2824fe810a091391 0x7bfbfe0cf86cde4f 0xdefeff833e1b3793

def z477 : W := mkw 0x204130c281003028 0x88104c30a0400c0a 0x2ebf31c38000387e 0x0bafcc70e0000e1f

def z478 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x040001f300000000 0x0100007cc0000000

def z479 : W := mkw 0x2343fa8286da802a 0x88d0fea0a1b6a00a 0xe1fbfe0387ffc07d 0xf87eff80e1fff01f

def z480 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc1fb7200077cc001 0xf07edc8001df3000

def z481 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3be8520cf8001e4e 0x0efa14833e000793

def z482 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0x8417adf3009321b0 0x2105eb7cc024c86c

def z483 : W := mkw 0x3e03fffbd5c03100 0x0f80fffef5700c40 0xbfffffffff802180 0x2fffffffffe00860

def z484 : W := mkw 0x3c43fffbd1003028 0x8f10fffef4400c0a 0x3ffffffff800387e 0x0ffffffffe000e1f

def z485 : W := mkw 0x2001308282180002 0x08004c20a0860000 0xeebb31c387180001 0x7baecc70e1c60000

def z486 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x2ebb73cf98000000 0x0baedcf3e6000000

def z487 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xce3f81f007803982 0x738fe07c01e00e60

def z488 : W := mkw 0x8392ca042ce6ce45 0x20e4b2810b39b391 0x7be8de0cf8efde4f 0xdefa37833e3bf793

def z489 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0x8000000007930000 0x2000000001e4c000

def z490 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0xeaac10008718387f 0x7aab040021c60e1f

def z491 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xaebf31c387102030 0x2bafcc70e1c4080c

def z492 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x000301c000000000 0x0000c07000000000

def z493 : W := mkw 0x8090000428244e45 0x202400010a091391 0x1000000c78000600 0x040000031e000180

def z494 : W := mkw 0x0000000020040240 0x0000000008010090 0x4000000000040643 0x9000000000010190

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x40a8100000080001 0x502a040000020000

def z496 : W := mkw 0x0b22ce1164c782d0 0x42c8b3845931e0b4 0xf7dcee3360f7e7f3 0xbdf73b8cd83df9fc

def z497 : W := mkw 0x3ba3ff7d67ffbfd3 0x4ee8ffdf59ffeff4 0xffffffff67fffff3 0xffffffffd9fffffc

def z498 : W := mkw 0x140001aa90000000 0x0500006aa4000000 0x080001cc98000000 0x0200007326000000

def z499 : W := mkw 0x2383fa0406fa8c03 0x08e0fe8101bea300 0xdbfbfe0c07ffde03 0xf6feff8301fff780

def z500 : W := mkw 0x20c130c683383c2b 0x88304c31a0ce0f0a 0xfeff71cf87783e7f 0xffbfdc73e1de0f9f

def z501 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x2593bff3f8000000 0x0964effcfe000000

def z502 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd044c03c07e03f82 0xf411300f01f80fe0

def z503 : W := mkw 0x8010000028044244 0x200400000a011091 0x3be8520cf80cc04d 0x0efa14833e033013

def z504 : W := mkw 0x8392ca042ce6ce45 0x20e4b2810b39b391 0x1140ce0c78e7c600 0x845033831e39f180

def z505 : W := mkw 0x0282c00404e00c01 0x00a0b00101380300 0xda7bc00c07e01e02 0xf69ef00301f80780

def z506 : W := mkw 0xa393fa040efacc07 0x28e4fe8103beb301 0x0823520c9f68d80c 0x4208d48327da3603

def z507 : W := mkw 0x3383fb2c06fa8d03 0x0ce0fecb01bea340 0xd1fbfe3c07ffc781 0xf47eff8f01fff1e0

def z508 : W := mkw 0x3e83ffffd5e03d01 0x0fa0fffff5780f40 0xde7fedff07e03f82 0xf79ffb7fc1f80fe0

def z509 : W := mkw 0x1080012c00200d01 0x0420004b00080340 0x1000003c00000780 0x0400000f000001e0

def z510 : W := mkw 0x08a0041560250ed1 0x42280105580943b4 0xfffcec3f60f73ff3 0xffff3b0fd83dcffc

def z511 : W := mkw 0x8090000428244e45 0x202400010a091391 0x000000000064c600 0x8000000000193180

def z512 : W := mkw 0x1082c12c00200c01 0x0420b04b00080300 0x5e7bc1fc00601e02 0xd79ef07f00180780

def z513 : W := mkw 0x8090000428244e45 0x202400010a091391 0x73c8420c7864c643 0x9cf210831e193190

def z514 : W := mkw 0x29213e11621f82d2 0x4a484f845887e0b4 0x21803e03601fc071 0x08600f80d807f01c

def z515 : W := mkw 0x0202c04005c03000 0x0080b01001700c00 0xce7fc1c007e03802 0xf39ff07001f80e00

def z516 : W := mkw 0x2c413e93d218002a 0x8b104fa4f486000a 0x21803e03f818007d 0x08600f80fe06001f

def z517 : W := mkw 0x32c3f1ee87f83d2b 0x8cb0fc7ba1fe0f4a 0xde7fe1ff07f03fb2 0xf79ff87fc1fc0fec

def z518 : W := mkw 0x0820041140010090 0x4208010450004024 0xb7dcac33609321b0 0x2df72b0cd824c86c

def z519 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc1fbbc00079f0001 0xf07eef0001e7c000

def z520 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0x7be8de3cf8efdfcf 0xdefa378f3e3bf7f3

def z521 : W := mkw 0x0000000020040240 0x0000000008010090 0x73e85200606cc643 0xdcfa1480181b3190

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x33c8000060000000 0x0cf2000018000000

def z523 : W := mkw 0xa393fa040efacc07 0x28e4fe8103beb301 0xc9fbfe0c9fffd80d 0xf27eff8327fff603

def z524 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0xc1fbd20007ecc001 0xf07ef48001fb3000

def z525 : W := mkw 0x2323fa0026df82d2 0x48c8fe8009b7e0b4 0xc1fffe0007ffe7f3 0xf07fff8001fff9fc

def z526 : W := mkw 0x2001300002180002 0x08004c0000860000 0x0080300000180001 0x00200c0000060000

def z527 : W := mkw 0x8090000428244e45 0x202400010a091391 0x51e8520c786cc601 0xd47a14831e1b3180

def z528 : W := mkw 0x3c43fffbd318302a 0x8f10fffef4c60c0a 0x3ffbffffff08180c 0x4ffeffffffc20603

def z529 : W := mkw 0x0302c00006da8002 0x00c0b00001b6a000 0xc07bc00007ffc001 0xf01ef00001fff000

def z530 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3be8520cf864c600 0x8efa14833e193180

def z531 : W := mkw 0x2c213e93f00502d0 0x4b084fa4fc0140b4 0x21803e03f8170071 0x08600f80fe05c01c

def z532 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xc5fbfff307ffc001 0xf17efffcc1fff000

def z533 : W := mkw 0x1aa2c57d65e53fd1 0x46a8b15f59794ff4 0xdf7fcdfc67e73f82 0xf7dff37f19f9cfe0

def z534 : W := mkw 0x8090000408204c05 0x2024000102081301 0x0800000c9800180c 0x0200000326000603

def z535 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x09fbffcc98000000 0x027efff326000000

def z536 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3b80120cf80cde4f 0x0ee004833e033793

def z537 : W := mkw 0x2c013e93d0000000 0x0b004fa4f4000000 0x00002c0300000000 0x00000b00c0000000

def z538 : W := mkw 0x004000c28318302a 0x80100030a0c60c0a 0xee0401c38718387f 0x7b810070e1c60e1f

def z539 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0xc17bce0007e7c000 0xf05ef38001f9f000

def z540 : W := mkw 0x0200000004c00000 0x0080000001300000 0xc000000007e00000 0xf000000001f80000

def z541 : W := mkw 0x8090000428244e45 0x202400010a091391 0x5a68400c006cde4f 0xd69a1003001b3793

def z542 : W := mkw 0xa3d3fac6affefe6f 0xa8f4feb1abffbf9b 0xffffffcffffffe7f 0xfffffff3ffffff9f

def z543 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0x1140ce3c78e7c780 0x8450338f1e39f1e0

def z544 : W := mkw 0x9ab2c57d6de57fd5 0x66acb15f5b795ff5 0xffffffffffffffff 0xffffffffffffffff

def z545 : W := mkw 0x3003fb2800000000 0x0c00feca00000000 0x1ffbfffc00000000 0x07feffff00000000

def z546 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xeffbffc387ffc001 0xfbfefff0e1fff000

def z547 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xebfbfe0087ffd84f 0xfafeff8021fff613

def z548 : W := mkw 0x3283fb6c05e03d01 0x0ca0fedb01780f40 0xdffffffc07e03f82 0xf7ffffff01f80fe0

def z549 : W := mkw 0x10c001ee81203d29 0x8430007ba0480f4a 0x3e0401ff80003ffe 0x0f81007fe0000fff

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x01801200000cc001 0x0060048000033000

def z551 : W := mkw 0x0000004001003000 0x0000001000400c00 0x082301c007001800 0x4208c07001c00600

def z552 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x6aab11c08708184f 0x5aaac47021c20613

def z553 : W := mkw 0x200130c281003000 0x08004c30a0400c00 0xeebf31c387003802 0x7bafcc70e1c00e00

def z554 : W := mkw 0xb493fbaeb8244e45 0x2d24feebae091391 0x7beb53ccf86cde4f 0xdefad4f33e1b3793

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0xd7dcac3000972783 0xb5f72b0c0025c9e0

def z556 : W := mkw 0x01000000021a8002 0x004000000086a000 0x00000000001fc001 0x000000000007f000

def z557 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e44c1fc00e03f82 0x8791307f00380fe0

def z558 : W := mkw 0x2343fa4007dab02a 0x88d0fe9001f6ac0a 0xc1fffe0007fff87f 0xf07fff8001fffe1f

def z559 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0xc5ffffc307ffe031 0xf17ffff0c1fff80c

def z560 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0x6eac11c38008387f 0x5bab0470e0020e1f

def z561 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x31c0fe3ff8000000 0x0c703f8ffe000000

def z562 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2e8431c38018387f 0x0ba10c70e0060e1f

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x2aa8100080000000 0x0aaa040020000000

def z564 : W := mkw 0x0800041140000000 0x0200010450000000 0xf7d8ac3360970001 0xbdf62b0cd825c000

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0x2604000300002072 0x09810000c000081c

def z566 : W := mkw 0x8090000408204c05 0x2024000102081301 0x000000000068d80c 0x40000000001a3603

def z567 : W := mkw 0x0080000400200c01 0x0020000100080300 0x7ae8500c80681e4f 0xdeba1403201a0793

def z568 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x5a6b41cc07601e02 0xd69ad07301d80780

def z569 : W := mkw 0x3e83ffffd5e03d01 0x0fa0fffff5780f40 0x3ffbffffff601800 0x4ffeffffffd80600

def z570 : W := mkw 0x0800041140000000 0x0200010450000000 0x3ff8fe3ff8000000 0x0ffe3f8ffe000000

def z571 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x8153ee0007f7c000 0xa054fb8001fdf000

def z572 : W := mkw 0x8890041568244e45 0x222401055a091391 0x7ff8fe3ff86cde4f 0xdffe3f8ffe1b3793

def z573 : W := mkw 0x0080000400200c01 0x0020000100080300 0x1040400c00600600 0x8410100300180180

def z574 : W := mkw 0xa05130c2ab1c726e 0xa8144c30aac71c9b 0xefbf33c3ff1cf87f 0x7befccf0ffc73e1f

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x400000000008184f 0x5000000000020613

def z576 : W := mkw 0x8090000408204c05 0x2024000102081301 0x49e8520c986cd80d 0xd27a1483261b3603

def z577 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc0bb72000778c001 0x702edc8001de3000

def z578 : W := mkw 0x086004d3e10532f8 0xc2180134f8414cbe 0xffdcadf3e0973fff 0xbff72b7cf825cfff

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x01e8520000000000 0x007a148000000000

def z580 : W := mkw 0x8010000028044244 0x200400000a011091 0x73c81200f80cc64f 0x9cf204803e033193

def z581 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x8c3731c38718383c 0x630dcc70e1c60e0f

def z582 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0xce3f01c00718387f 0x738fc07001c60e1f

def z583 : W := mkw 0x0c000e1150000000 0x0300038454000000 0x01000e0078000000 0x004003801e000000

def z584 : W := mkw 0x2043fac28318302a 0x8810feb0a0c60c0a 0xefffffc38718387f 0x7bfffff0e1c60e1f

def z585 : W := mkw 0x0320000026df82d2 0x40c8000009b7e0b4 0xc004000007ffe7f3 0xf001000001fff9fc

def z586 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x1040c03c00000000 0x0410300f00000000

def z587 : W := mkw 0x3c43fffbd318302a 0x8f10fffef4c60c0a 0xeebfbdf38718387f 0x7bafef7ce1c60e1f

def z588 : W := mkw 0x204130c2a31c326a 0x88104c30a8c70c9a 0xffff31c3e71c3e7f 0xffffcc70f9c70f9f

def z589 : W := mkw 0x3c23ffbbf00502d0 0x4f08ffeefc0140b4 0xf7dfadf3609727f3 0xbdf7eb7cd825c9fc

def z590 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0x000301c007000000 0x0000c07001c00000

def z591 : W := mkw 0x01000a0000028000 0x004002800000a000 0x01000e000007c000 0x004003800001f000

def z592 : W := mkw 0x2303fa0004c28000 0x08c0fe800130a000 0x01fbfe0000e7c000 0x807eff800039f000

def z593 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0xc1fbfe0000970001 0xb07eff800025c000

def z594 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7a00000cf86cde4f 0xde8000033e1b3793

def z595 : W := mkw 0x2f03fe93d6da8002 0x0bc0ffa4f5b6a000 0xe1fbfe03ffffc001 0xf87eff80fffff000

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0xc004000000802782 0xb0010000002009e0

def z597 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0x00008c0000830000 0x000023000020c000

def z598 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x73c88c30608707c3 0x9cf2230c1821c1f0

def z599 : W := mkw 0x00200000200502d0 0x40080000080140b4 0x0000000000170071 0x000000000005c01c

def z600 : W := mkw 0xb2d3f1eeaffc7f6f 0xacb4fc7babff1fdb 0xfffff3fffffcffff 0xfffffcffffff3fff

def z601 : W := mkw 0x28613493e21d02fa 0xca184d24f88740be 0xf7dcbc33e09f27ff 0xbdf72f0cf827c9ff

def z602 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x2080300380000000 0x08200c00e0000000

def z603 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xa594ac33609721f1 0x29652b0cd825c87c

def z604 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x01000c0060070000 0x004003001801c000

def z605 : W := mkw 0xa393fa042efece47 0x28e4fe810bbfb391 0x7beb520cff6cde4f 0xdefad4833fdb3793

def z606 : W := mkw 0x29213e11621f82d2 0x4a484f845887e0b4 0xf7dcbe33609fe7f3 0xbdf72f8cd827f9fc

def z607 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xe08430038718387f 0x78210c00e1c60e1f

def z608 : W := mkw 0x3443fbea9318302a 0x8d10fefaa4c60c0a 0xeebf73cf9f18387f 0x7bafdcf3e7c60e1f

def z609 : W := mkw 0x2b03fe1146da8002 0x0ac0ff8451b6a000 0xf7fbfe3367ffc001 0xfdfeff8cd9fff000

def z610 : W := mkw 0x0000008280000000 0x00000020a0000000 0x2e0001c380000000 0x0b800070e0000000

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000006cc001 0xd0000000001b3000

def z612 : W := mkw 0x0b22ce1164c782d0 0x42c8b3845931e0b4 0x1140ce3060e7c780 0x8450338c1839f1e0

def z613 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x8c37c1fc07e03980 0x630df07f01f80e60

def z614 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x37dbadf360000000 0x0df6eb7cd8000000

def z615 : W := mkw 0x3283f1ee85e03d01 0x0ca0fc7ba1780f40 0xfefff1ff87e03f82 0xffbffc7fe1f80fe0

def z616 : W := mkw 0x3e83ffbfd4e00d01 0x0fa0ffeff5380340 0x3ffbfffff8e00780 0x8ffefffffe3801e0

def z617 : W := mkw 0x1282c16c25e43f41 0x04a0b05b09790fd0 0xffffc1fc67e43fc3 0xfffff07f19f90ff0

def z618 : W := mkw 0x88b0041568254ed5 0x622c01055a0953b5 0x3e04003ff8003ffe 0x0f81000ffe000fff

def z619 : W := mkw 0x0000004001003000 0x0000001000400c00 0xeebf21c307103873 0x7bafc870c1c40e1c

def z620 : W := mkw 0x1c2005bbf00502d0 0x4708016efc0140b4 0x3e0401fff80027f2 0x0f81007ffe0009fc

def z621 : W := mkw 0x2303fa4007dab002 0x08c0fe9001f6ac00 0xcfffffc007fff803 0xf3fffff001fffe00

def z622 : W := mkw 0x829000442de47f45 0x20a400110b791fd1 0xfbec520cffecffcf 0xfefb14833ffb3ff3

def z623 : W := mkw 0x1c22cf39700502d0 0x4708b3ce5c0140b4 0xf7dcee3f789727f3 0xbdf73b8fde25c9fc

def z624 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0x000000000708180c 0x4000000001c20603

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a68400c00000000 0x069a100300000000

def z626 : W := mkw 0x3ec3ffffd7f83d2b 0x8fb0fffff5fe0f4a 0xfffffffffff83fff 0xfffffffffffe0fff

def z627 : W := mkw 0x3c83ffffd1203d01 0x0f20fffff4480f40 0x3ffffffff8003f82 0x0ffffffffe000fe0

def z628 : W := mkw 0x2203f00006d80002 0x0880fc0001b60000 0xc0fbf00007f80001 0xf03efc0001fe0000

def z629 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x1000003060000780 0x0400000c180001e0

def z630 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc023520007ffc001 0xf008d48001fff000

def z631 : W := mkw 0x3e03fffbd5c03100 0x0f80fffef5700c40 0x8417adf307802180 0x2105eb7cc1e00860

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a0000008000184e 0x0a80000020000613

def z633 : W := mkw 0x0820041140010090 0x4208010450004024 0x00002c0300130030 0x00000b00c004c00c

def z634 : W := mkw 0x2b23fe1166df82d2 0x4ac8ff8459b7e0b4 0xf7dfac33679727f3 0xbdf7eb0cd9e5c9fc

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xc058800000800000 0xb016200000200000

def z636 : W := mkw 0xbcb3ffbff8254ed5 0x6f2cffeffe0953b5 0xfffffffff8ffffff 0xfffffffffe3fffff

def z637 : W := mkw 0x8292c0042ce44e45 0x20a4b0010b391391 0xfbfbd20cffecde4f 0xfefef4833ffb3793

def z638 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xa49731c38718207d 0x2925cc70e1c6081f

def z639 : W := mkw 0x3303fb6807dab102 0x0cc0feda01f6ac40 0xc5fffff007ffe181 0xf17ffffc01fff860

def z640 : W := mkw 0x0000000002180002 0x0000000000860000 0xc000000007180001 0x7000000001c60000

def z641 : W := mkw 0x21413a82821a802a 0x88504ea0a086a00a 0x21803e03801fc07d 0x08600f80e007f01f

def z642 : W := mkw 0x0800041140000000 0x0200010450000000 0x11408c3060000000 0x0450230c18000000

def z643 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7bc8000cf8041e4f 0x9ef200033e010793

def z644 : W := mkw 0x2001304003183002 0x08004c1000c60c00 0xcebf31c007183803 0x73afcc7001c60e00

def z645 : W := mkw 0x0200004005c03100 0x0080001001700c40 0x8004000007802180 0x2001000001e00860

def z646 : W := mkw 0x2c413ed3d318302a 0x8b104fb4f4c60c0a 0xefbf3fc3ff18387f 0x7befcff0ffc60e1f

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0xc098200000100001 0x3026080000040000

def z648 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x8033fe0007fbc000 0x600cff8001fef000

def z649 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0xd07bc03c07e00780 0xf41ef00f01f801e0

def z650 : W := mkw 0x9c9005bff8244e45 0x2724016ffe091391 0x7fe853fff86cde4f 0xdffa14fffe1b3793

def z651 : W := mkw 0x3683fbee95e03d01 0x0da0fefba5780f40 0xde7fd3fc9fe03f82 0xf79ff4ff27f80fe0

def z652 : W := mkw 0x3ae3f5ffe7fd3ffb 0xceb8fd7ff9ff4ffe 0xfffffdffe7ff3fff 0xffffff7ff9ffcfff

def z653 : W := mkw 0x8010000028044244 0x200400000a011091 0x00000000000cc04d 0x0000000000033013

def z654 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0xd65cc03c00e02782 0xb597300f003809e0

def z655 : W := mkw 0x9c92cf3d78244e45 0x2724b3cf5e091391 0x7be8de3cf86cde4f 0xdefa378f3e1b3793

def z656 : W := mkw 0x9c9005bff8244e45 0x2724016ffe091391 0x3e0001fff8001e4e 0x0f80007ffe000793

def z657 : W := mkw 0x8090000428244e45 0x202400010a091391 0x73c80000606cde4f 0xdcf20000181b3793

def z658 : W := mkw 0x32c3f1ee87f83d2b 0x8cb0fc7ba1fe0f4a 0xeebf71cf8778387f 0x7bafdc73e1de0e1f

def z659 : W := mkw 0x2343fac287dab02a 0x88d0feb0a1f6ac0a 0xc9fbffc087ffd80d 0xf27efff021fff603

def z660 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x00008c3000000000 0x0000230c00000000

def z661 : W := mkw 0x3c23ffbbf00502d0 0x4f08ffeefc0140b4 0x3ffbfffff8170071 0x0ffefffffe05c01c

def z662 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1e7bedff00000000 0x079efb7fc0000000

def z663 : W := mkw 0x1382c16c07fabd03 0x04e0b05b01feaf40 0xde7fc1fc07ffff83 0xf79ff07f01ffffe0

def z664 : W := mkw 0x0aa0045565e53fd1 0x42a8011559794ff4 0xf7dcac3367f73ff3 0xfdf72b0cd9fdcffc

def z665 : W := mkw 0x9c92cf3d78244e45 0x2724b3cf5e091391 0x1140ce3c7864c600 0x8450338f1e193180

def z666 : W := mkw 0x1802c53940000000 0x0600b14e50000000 0x3ffbedff60000000 0x0ffefb7fd8000000

def z667 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x73c82c0360170673 0x9cf20b00d805c19c

def z668 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x3be8de3cf8000000 0x0efa378f3e000000

def z669 : W := mkw 0x0000000020040240 0x0000000008010090 0x1140000060040600 0x8450000018010180

def z670 : W := mkw 0x0a22c41164c502d0 0x4288b104593140b4 0xf7ffec3367f727f3 0xfdfffb0cd9fdc9fc

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x014042000064c000 0x8050108000193000

def z672 : W := mkw 0x00600040231d32fa 0xc018001008c74cbe 0xc0040000079f3fff 0xf001000001e7cfff

def z673 : W := mkw 0x0080000400200c01 0x0020000100080300 0xde7cc03c00e03f82 0xf79f300f00380fe0

def z674 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2ebb31c38708180c 0x4baecc70e1c20603

def z675 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0xe69c20030718387f 0x79a70800c1c60e1f

def z676 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0x0040c00000e00000 0x8010300000380000

def z677 : W := mkw 0x0080000400200c01 0x0020000100080300 0x1a00000c00001e02 0x0680000300000780

def z678 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf65c8033608027f2 0xbd97200cd82009fc

def z679 : W := mkw 0x2b23fe1146db8092 0x4ac8ff8451b6e024 0x8417ac33079321b0 0x2105eb0cc1e4c86c

def z680 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7a68400cf8601e4e 0xde9a10033e180793

def z681 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc1e8520007ffc001 0xf07a148001fff000

def z682 : W := mkw 0x1c4005fbd1003028 0x8710017ef4400c0a 0x3e0401fff800387e 0x0f81007ffe000e1f

def z683 : W := mkw 0x0080000400200c01 0x0020000100080300 0x4000000000601e02 0xd000000000180780

def z684 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf69c2033601027f3 0x3da7080cd80409fc

def z685 : W := mkw 0x2b23fe1166df82d2 0x4ac8ff8459b7e0b4 0xd1fbfe3067ffc781 0xf47eff8c19fff1e0

def z686 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0xee9c21c38010387f 0x3ba70870e0040e1f

def z687 : W := mkw 0x0020000000010090 0x4008000000004024 0x80040000009321b0 0x200100000024c86c

def z688 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc07bd20007e8c000 0xf01ef48001fa3000

def z689 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0xd67fc03007e02782 0xf59ff00c01f809e0

def z690 : W := mkw 0x0000004001003000 0x0000001000400c00 0x0e0401c000003802 0x0381007000000e00

def z691 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x041381f000000000 0x0104e07c00000000

def z692 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd1448c30609727f3 0xb451230c1825c9fc

def z693 : W := mkw 0x2003fa0000000000 0x0800fe8000000000 0x41fbfe00006cc001 0xd07eff80001b3000

def z694 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0xc1d8be00009fc001 0xb0762f800027f000

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010ac0000930000 0x20042b000024c000

def z696 : W := mkw 0x9292c12c2ce44f45 0x24a4b04b0b3913d1 0x7be8d23cf8ecdfcf 0xdefa348f3e3b37f3

def z697 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xc87bc1cc07e01800 0xf21ef07301f80600

def z698 : W := mkw 0xa1913a042a3ece47 0x28644e810a8fb391 0x7be87e0cf87fde4f 0xdefa1f833e1ff793

def z699 : W := mkw 0x1c8005ffd1203d01 0x0720017ff4480f40 0x3e0401fff8003f82 0x0f81007ffe000fe0

def z700 : W := mkw 0x0800041140000000 0x0200010450000000 0xf7dcac3360102073 0x3df72b0cd804081c

def z701 : W := mkw 0xbcd3fffffb3c7e6f 0xaf34fffffecf1f9b 0xffffffffff7cfe7f 0xffffffffffdf3f9f

def z702 : W := mkw 0x234130c287dab02a 0x88d04c30a1f6ac0a 0xeebf31c387fff87f 0xfbafcc70e1fffe1f

def z703 : W := mkw 0x0820041140010090 0x4208010450004024 0x00008c3000830180 0x0000230c0020c060

def z704 : W := mkw 0xa0d130c68b387c2f 0xa8344c31a2ce1f0b 0xeebf73cf9f78f87f 0x7bafdcf3e7de3e1f

def z705 : W := mkw 0x2823fe11600502d0 0x4a08ff84580140b4 0xf7fffe33609727f3 0xbdffff8cd825c9fc

def z706 : W := mkw 0x3383fb6c07fabd03 0x0ce0fedb01feaf40 0xde7fedfc07f33f82 0xf79ffb7f01fccfe0

def z707 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1d73fffff8000000 0x075cfffffe000000

def z708 : W := mkw 0x3423fbaab00502d0 0x4d08feeaac0140b4 0xc82753cc989727f3 0xb209d4f32625c9fc

def z709 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x81d3fe0007ffc001 0xa074ff8001fff000

def z710 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebf73c38778f87f 0x7bafdcf0e1de3e1f

def z711 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdeffd1fc07e83f83 0xf7bff47f01fa0fe0

def z712 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xbffbfffffff7c000 0xaffefffffffdf000

def z713 : W := mkw 0x2001300002180002 0x08004c0000860000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z714 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfe7fc1fc87e03fce 0xff9ff07f21f80ff3

def z715 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x3beb53ccf8000000 0x0efad4f33e000000

def z716 : W := mkw 0x3d03ffbbd21a8002 0x0f40ffeef486a000 0xfffbffffff1fc001 0x7ffeffffffc7f000

def z717 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3f8013fff8000000 0x0fe004fffe000000

def z718 : W := mkw 0x1082c16c01203d01 0x0420b05b00480f40 0xde7fc1fc07003f82 0x779ff07f01c00fe0

def z719 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf614ac33609727f3 0xbd852b0cd825c9fc

def z720 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2ebb31c38718187d 0x4baecc70e1c6061f

def z721 : W := mkw 0x2e813ed7d5e03d01 0x0ba04fb5f5780f40 0xe1843e03ffe03f82 0xf8610f80fff80fe0

def z722 : W := mkw 0x32c3f1ae86f80d2b 0x8cb0fc6ba1be034a 0x30c0f03f80f807fd 0x8c303c0fe03e01ff

def z723 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xe69f21c30718387f 0x79a7c870c1c60e1f

def z724 : W := mkw 0x88b0041548214c95 0x622c010552085325 0x8c34fe3f98fbf9bc 0x630d3f8fe63efe6f

def z725 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xee2711c38718387f 0x7b89c470e1c60e1f

def z726 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fd3fc07e8ff82 0xf79ff4ff01fa3fe0

def z727 : W := mkw 0x2003fa8280000000 0x0800fea0a0000000 0x3ffbffcff8000000 0x0ffefff3fe000000

def z728 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xfffcbe33f89fffff 0xffff2f8cfe27ffff

def z729 : W := mkw 0x0342cac285c2b028 0x80d0b2b0a170ac0a 0x2f44cfc380e7f87e 0x8bd133f0e039fe1f

def z730 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x3fd8effff8000000 0x0ff63bfffe000000

def z731 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x09235fccf8000000 0x0248d7f33e000000

def z732 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd65cac33009727f3 0xb5972b0cc025c9fc

def z733 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfe7fc1fcffe03f82 0xff9ff07f3ff80fe0

def z734 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebf73cf9f18387f 0x7bafdcf3e7c60e1f

def z735 : W := mkw 0x1c000fbbd0000000 0x070003eef4000000 0x3f000ffff8000000 0x0fc003fffe000000

def z736 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3e7bedfff8000000 0x0f9efb7ffe000000

def z737 : W := mkw 0x1f02cf3954c28000 0x07c0b3ce5530a000 0xdf7bcffc7fe7c000 0xf7def3ff1ff9f000

def z738 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1fffe0007ffe783 0xf07fff8001fff9e0

def z739 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc5fffe0307ffe031 0xf17fff80c1fff80c

def z740 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x7fe853fff86cc001 0xdffa14fffe1b3000

def z741 : W := mkw 0x8090000408204c05 0x2024000102081301 0x3a20520cf868d80c 0x4e8814833e1a3603

def z742 : W := mkw 0xbc93ffbff8244e45 0x2f24ffeffe091391 0x4413adf3006cde4f 0xd104eb7cc01b3793

def z743 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0xfbfbffccffffc001 0xfefefff33ffff000

def z744 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeeff71c38778387f 0xfbbfdc70e1de0e1f

def z745 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xde7fc1fc07802782 0xb79ff07f01e009e0

def z746 : W := mkw 0x1382c16c05e2bd01 0x04e0b05b0178af40 0xde7fc1fc07e7ff82 0xf79ff07f01f9ffe0

def z747 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1dbee0007f7c001 0xb076fb8001fdf000

def z748 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xbe13adffff930000 0x2f84eb7fffe4c000

def z749 : W := mkw 0x82d000442ffc7f6f 0xa0b400110bff1fdb 0xc004000007fcffff 0xf001000001ff3fff

def z750 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x15fbffff78000000 0x057effffde000000

def z751 : W := mkw 0x1c42cf795318302a 0x8710b3de54c60c0a 0xd144ce3c7f18387f 0x7451338f1fc60e1f

def z752 : W := mkw 0xa393fa042efece47 0x28e4fe810bbfb391 0xba13ac0cff931e4e 0x2e84eb033fe4c793

def z753 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e10adfff8000000 0x0f842b7ffe000000

def z754 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3f53effff8000000 0x0fd4fbfffe000000

def z755 : W := mkw 0x1e02c5bbd4c00000 0x0780b16ef5300000 0xfe7bc1ffffe00000 0xff9ef07ffff80000

def z756 : W := mkw 0x3303fb2806da8002 0x0cc0feca01b6a000 0xfffbfffcffffc001 0xfffeffff3ffff000

def z757 : W := mkw 0x1382cb6c05e2bd01 0x04e0b2db0178af40 0xde7fc3fc07e0ff82 0xf79ff0ff01f83fe0

def z758 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdffffffc07ffff83 0xf7ffffff01ffffe0

def z759 : W := mkw 0x8090000428244e45 0x202400010a091391 0x6ba8520cf86cd84f 0x5aea14833e1b3613

def z760 : W := mkw 0x80d000442b3c7e6f 0xa03400110acf1f9b 0x40000000076cde4f 0xd000000001db3793

def z761 : W := mkw 0x3f03ffbbd4c28000 0x0fc0ffeef530a000 0xfffbffffffe7c000 0xfffefffffff9f000

def z762 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd75cac33609727b2 0xb5d72b0cd825c9ec

def z763 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefbf3dc3871f387f 0x7befcf70e1c7ce1f

def z764 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde1781fc07e03f82 0xf785e07f01f80fe0

def z765 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x5a6bc1fc07e01f82 0xd69af07f01f807e0

def z766 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefffbdc38718387f 0x7bffef70e1c60e1f

def z767 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde3f81fc07803f82 0x778fe07f01e00fe0

def z768 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9e7fc1fc07e02780 0xa79ff07f01f809e0

def z769 : W := mkw 0x1c02c5bbd0000000 0x0700b16ef4000000 0x3e40c1fff8000000 0x0f90307ffe000000

def z770 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff808004d 0x0ffefffffe020013

def z771 : W := mkw 0x1002c16801003000 0x0400b05a00400c00 0xde7fc1fc07803f82 0xf79ff07f01e00fe0

def z772 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3bc0520cf86cde4f 0x8ef014833e1b3793

def z773 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xde7fc1fc9fe03f8e 0xf79ff07f27f80fe3

def z774 : W := mkw 0x1c00053950000000 0x0700014e54000000 0x1e0001fc78000000 0x0780007f1e000000

def z775 : W := mkw 0x31813b6c033abd03 0x0c604edb00ceaf40 0x1f843ffc001fff83 0x07e10fff0007ffe0

def z776 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e6841fff8000000 0x0f9a107ffe000000

def z777 : W := mkw 0x21013a00021a8002 0x08404e800086a000 0xc1fb7e00077fc001 0xf07edf8001dff000

def z778 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xfffbffcfffffc001 0xfffefff3fffff000

def z779 : W := mkw 0x2b23fe1166df82d2 0x4ac8ff8459b7e0b4 0x362752336768e7f2 0x4d89d48cd9da39fc

def z780 : W := mkw 0x0820041140010090 0x4208010450004024 0xd7dcac33009727b3 0xb5f72b0cc025c9ec

def z781 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbfb520cff6cde4f 0xfefed4833fdb3793

def z782 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x9414ac33609327b0 0x25052b0cd824c9ec

def z783 : W := mkw 0x3c0135bbd0000000 0x0f004d6ef4000000 0x3e8031fff8000000 0x0fa00c7ffe000000

def z784 : W := mkw 0x1c02c5bbd0000000 0x0700b16ef4000000 0x3ffbd3fff8000000 0x0ffef4fffe000000

def z785 : W := mkw 0x3c0135bbd2180002 0x0f004d6ef4860000 0xfebb31ffff180001 0x7faecc7fffc60000

def z786 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xc9fbffc087ffc001 0xf27efff021fff000

def z787 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefff73c38718387f 0x7bffdcf0e1c60e1f

def z788 : W := mkw 0x3003f1aa80000000 0x0c00fc6aa0000000 0x3ffbf3fff8000000 0x0ffefcfffe000000

def z789 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc153ee0007ffc001 0xf054fb8001fff000

def z790 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc07bec0007ffc001 0xf01efb0001fff000

def z791 : W := mkw 0x2001308282180002 0x08004c20a0860000 0xfffb73cfff7cc001 0xfffedcf3ffdf3000

def z792 : W := mkw 0x1c02c5bbd0000000 0x0700b16ef4000000 0x3e2341fff8000000 0x0f88d07ffe000000

def z793 : W := mkw 0x1382cb6c05e2bd01 0x04e0b2db0178af40 0xdfffeffc07f7ff83 0xf7fffbff01fdffe0

def z794 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xf3fbfe0067ffc001 0xfcfeff8019fff000

def z795 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0xc1fbee0007f7c001 0xf07efb8001fdf000

def z796 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3e33fffff8000000 0x0f8cfffffe000000

def z797 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xae9731c38718387f 0x2ba5cc70e1c60e1f

def z798 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0xfffffffff89327b2 0xbffffffffe24c9ec

def z799 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0xfbfcfe0cf8ffffff 0xfeff3f833e3fffff

def z800 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7aa8520cf868de4f 0x5eaa14833e1a3793

def z801 : W := mkw 0x1aa2c57d65e53fd1 0x46a8b15f59794ff4 0x29a36dcf67771871 0x4a68db73d9ddc61c

def z802 : W := mkw 0x23013a0006da8002 0x08c04e8001b6a000 0xc0002c0007ffc001 0xf0000b0001fff000

def z803 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x37c4ac33609727f3 0x8df12b0cd825c9fc

def z804 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x3e002dfff8000000 0x0f800b7ffe000000

def z805 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3be8520cf86cd84d 0x4efa14833e1b3613

def z806 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x841781f007803f82 0x2105e07c01e00fe0

def z807 : W := mkw 0x8292c0442de47f45 0x20a4b0110b791fd1 0xc1ffd20007ecffcf 0xf07ff48001fb3ff3

def z808 : W := mkw 0xa3d3fa442ffefe6f 0xa8f4fe910bffbf9b 0xc1fffe0007fffe7f 0xf07fff8001ffff9f

def z809 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x3ebb31cff8000000 0x0faecc73fe000000

def z810 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xaebf31c38710387e 0x2bafcc70e1c40e1f

def z811 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e9821fff8000000 0x0fa6087ffe000000

def z812 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3f408dfff8000000 0x0fd0237ffe000000

def z813 : W := mkw 0x9212c1682dc47344 0x2484b05a0b711cd1 0xa59793f0ff8ce1cd 0x2965e4fc3fe33873

def z814 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc1408c0007ffc001 0xf050230001fff000

def z815 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0x2e2701c38700387e 0x4b89c070e1c00e1f

def z816 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0xfffcd23cf8ffffff 0xffff348f3e3fffff

def z817 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xd5fbffff7fffc001 0xf57effffdffff000

def z818 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xffffd3fcffecff83 0xfffff4ff3ffb3fe0

def z819 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3beb7fcff8000000 0x0efadff3fe000000

def z820 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff808180c 0x4ffefffffe020603

def z821 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0xc1d8ee0007ffc001 0xf0763b8001fff000

def z822 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x140001ff78000000 0x0500007fde000000

def z823 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0xc0008c0007ffc001 0xf000230001fff000

def z824 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x2db3fffff8000000 0x0b6cfffffe000000

def z825 : W := mkw 0x2301300006da8002 0x08c04c0001b6a000 0xc1fbbc0007ffc001 0xf07eef0001fff000

def z826 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0x3ffffffff80021b0 0x0ffffffffe00086c

def z827 : W := mkw 0x1c02c5bbd0000000 0x0700b16ef4000000 0x3ffbedfff8000000 0x0ffefb7ffe000000

def z828 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x41ebde0007efc001 0xd07af78001fbf000

def z829 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0xc1fbde0007efc001 0xf07ef78001fbf000

def z830 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3f4043fff8000000 0x0fd010fffe000000

def z831 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf65cac33609327f2 0xbd972b0cd824c9fc

def z832 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc17bde0007efc000 0xf05ef78001fbf000

def z833 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcfe3ff89f3fff 0xffff3f8ffe27cfff

def z834 : W := mkw 0x1f0005bbd6da8002 0x07c0016ef5b6a000 0xfe0001ffffffc001 0xff80007ffffff000

def z835 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x35d3fffff8000000 0x0d74fffffe000000

def z836 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3be8520cf868de4e 0x4efa14833e1a3793

def z837 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xe8bb31c38718187d 0x7a2ecc70e1c6061f

def z838 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd87bc1fc07e01f80 0xf61ef07f01f807e0

def z839 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xe1fbfe0087ffc04d 0xf87eff8021fff013

def z840 : W := mkw 0x0820041140010090 0x4208010450004024 0xf6dcac33009327f3 0xbdb72b0cc024c9fc

def z841 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x7ea811fff808184f 0x5faa047ffe020613

def z842 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e7fc1fc07603f82 0x479ff07f01d80fe0

def z843 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbe8520cf8ffde4f 0xfefa14833e3ff793

def z844 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xd67fc1f007e02782 0xf59ff07c01f809e0

def z845 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xc4bf31c30718387f 0x712fcc70c1c60e1f

def z846 : W := mkw 0x8090000428244e45 0x202400010a091391 0x5b68520cf86cde0e 0xd6da14833e1b3783

def z847 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x182341fc07601f80 0x4608d07f01d807e0

def z848 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xffffd3fc87ecffcf 0xfffff4ff21fb3ff3

def z849 : W := mkw 0x3c0135bbd0000000 0x0f004d6ef4000000 0x3e2311fff8000000 0x0f88c47ffe000000

def z850 : W := mkw 0x8090004429247f45 0x202400110a491fd1 0x40040000006cffcf 0xd0010000001b3ff3

def z851 : W := mkw 0x23013a0006da8002 0x08c04e8001b6a000 0xc1e87e0007ffc001 0xf07a1f8001fff000

def z852 : W := mkw 0x0000008280000000 0x00000020a0000000 0x3fe853cff8000000 0x0ffa14f3fe000000

def z853 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7ffac33679727f3 0xfdffeb0cd9e5c9fc

def z854 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x280001cff8000000 0x0a000073fe000000

def z855 : W := mkw 0x286134d3e31d32fa 0xca184d34f8c74cbe 0x19639df0e78f1f8c 0xc658e77c39e3c7e3

def z856 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xfbfbfe0cffffd84f 0xfefeff833ffff613

def z857 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7be87e0cf87fde4f 0xdefa1f833e1ff793

def z858 : W := mkw 0x839000442ffeff47 0x20e400110bffbfd1 0xc004000007ffffcf 0xf001000001fffff3

def z859 : W := mkw 0x8090000408204c05 0x2024000102081301 0x7be8520cf86cd80d 0xdefa14833e1b3603

def z860 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xffff73cfff7cf87f 0xffffdcf3ffdf3e1f

def z861 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x841721c30710387e 0x2105c870c1c40e1f

def z862 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xcffbffc007ffc001 0xf3fefff001fff000

def z863 : W := mkw 0x1202c12804c00000 0x0480b04a01300000 0xde7fc1fc07e02782 0xf79ff07f01f809e0

def z864 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcee3f789727f3 0xbdf73b8fde25c9fc

def z865 : W := mkw 0x3f43ffbbd6da802a 0x8fd0ffeef5b6a00a 0xfffbffffffffc07d 0xfffefffffffff01f

def z866 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff818387f 0x7ffffffffe060e1f

def z867 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xfebf31cfff18387f 0x7fafcc73ffc60e1f

def z868 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc010ac0007ffc001 0xf0042b0001fff000

def z869 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x8414ac33009327f2 0x21052b0cc024c9fc

def z870 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff8100071 0x0ffefffffe04001c

def z871 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbf8720cf87cde4f 0xfefe1c833e1f3793

def z872 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfeffc1fc07e03fc3 0xffbff07f01f80ff0

def z873 : W := mkw 0x3303fb2806da8002 0x0cc0feca01b6a000 0xc5fbfff007ffc001 0xf17efffc01fff000

def z874 : W := mkw 0x0820041140010090 0x4208010450004024 0xf7dcac33609327b2 0xbdf72b0cd824c9ec

def z875 : W := mkw 0xa0d130c6ab3c7e6f 0xa8344c31aacf1f9b 0x955763cf7f74e630 0xa555d8f3dfdd398c

def z876 : W := mkw 0x1c02c53950000000 0x0700b14e54000000 0x1e7bc1fc78000000 0x079ef07f1e000000

def z877 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x3ffbfffff8ffc001 0x8ffefffffe3ff000

def z878 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x37dbefff78000000 0x0df6fbffde000000

def z879 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7ff8720ff86cde4f 0xdffe1c83fe1b3793

def z880 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0x3ffbfffff8180001 0x0ffefffffe060000

def z881 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x3f7bcffff8000000 0x0fdef3fffe000000

def z882 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xe1fbfe0387ffc001 0xf87eff80e1fff000

def z883 : W := mkw 0x829000442de47f45 0x20a400110b791fd1 0x40000000076cde4f 0xd000000001db3793

def z884 : W := mkw 0x3e03ffbbd4c00100 0x0f80ffeef5300040 0x3ffbfffff8800180 0x0ffefffffe200060

def z885 : W := mkw 0x2c613e93f21d02fa 0xcb184fa4fc8740be 0x21803e03f81f007d 0x08600f80fe07c01f

def z886 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e5881fff8000000 0x0f96207ffe000000

def z887 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7a68520cf868de4e 0xde9a14833e1a3793

def z888 : W := mkw 0x8090000408204c05 0x2024000102081301 0x7be8520cf868de0e 0xdefa14833e1a3783

def z889 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2ea731c38718387f 0x4ba9cc70e1c60e1f

def z890 : W := mkw 0x8090000428244e45 0x202400010a091391 0x5960520cf86cde4f 0xd65814833e1b3793

def z891 : W := mkw 0x3c0135bbd0000000 0x0f004d6ef4000000 0x3e1321fff8000000 0x0f84c87ffe000000

def z892 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x282353cff8000000 0x0a08d4f3fe000000

def z893 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdf7fc3fc07e4ff82 0xf7dff0ff01f93fe0

def z894 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xcbfbfe0007ffd803 0xf2feff8001fff600

def z895 : W := mkw 0x2703fa8296da8002 0x09c0fea0a5b6a000 0xc1fbfe009fffc001 0xf07eff8027fff000

def z896 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xcc3731c38718387f 0x730dcc70e1c60e1f

def z897 : W := mkw 0x3f43fffbd7dab02a 0x8fd0fffef5f6ac0a 0x8417adf307932030 0x2105eb7cc1e4c80c

def z898 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xeffffe0387fff87f 0xfbffff80e1fffe1f

def z899 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc0bbbc0007ffc001 0xf02eef0001fff000

def z900 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xffff31c3e718387f 0x7fffcc70f9c60e1f

def z901 : W := mkw 0x2343fa0006da802a 0x88d0fe8001b6a00a 0xc1fbfe0007ffc07d 0xf07eff8001fff01f

def z902 : W := mkw 0x1802c53940000000 0x0600b14e50000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z903 : W := mkw 0x12c2c16c05e03d29 0x84b0b05b01780f4a 0xde7fc1fc07e03ffe 0xf79ff07f01f80fff

def z904 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcac3360ffe7f3 0xfdf72b0cd83ff9fc

def z905 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xd7fbfe3007ffc001 0xf5feff8c01fff000

def z906 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fc1fc07f03ff3 0xf79ff07f01fc0ffc

def z907 : W := mkw 0x0080004401203c01 0x0020001100480f00 0xde7fc1fc07e03f82 0xf79ff07f01f80fe0

def z908 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xf7fcfe33f8ffe7ff 0xfdff3f8cfe3ff9ff

def z909 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xffffd3fcffe8ff8e 0xfffff4ff3ffa3fe3

def z910 : W := mkw 0x21413ac2831ab02a 0x88504eb0a0c6ac0a 0xefffbfc3879ff87f 0xfbffeff0e1e7fe1f

def z911 : W := mkw 0x0000000000000000 0x0000000000000000 0x7be8520cf86cd84f 0xdefa14833e1b3613

def z912 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdeffe1fc07f03f83 0xf7bff87f01fc0fe0

def z913 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2e0701c38700387e 0x0b81c070e1c00e1f

def z914 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0x3ffbfffff8830180 0x0ffefffffe20c060

def z915 : W := mkw 0x3003fb2800000000 0x0c00feca00000000 0x3ffbfffcf8000000 0x0ffeffff3e000000

def z916 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcbc33e09727f3 0xbfff2f0cf825c9fc

def z917 : W := mkw 0x08200411600502d0 0x42080104580140b4 0x8414ac33009727b0 0xa1052b0cc025c9ec

def z918 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc5fffe3007ffe181 0xf17fff8c01fff860

def z919 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0x3ffbfffff8e00000 0x8ffefffffe380000

def z920 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc7fffe0007ffe003 0xf1ffff8001fff800

def z921 : W := mkw 0x3f03ffbbd4c28000 0x0fc0ffeef530a000 0x3ffbfffff860c000 0x0ffefffffe183000

def z922 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3ea811fff8000000 0x0faa047ffe000000

def z923 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebfb1f3879839ff 0x7bafec7ce1e60e7f

def z924 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3e7bd3fff8000000 0x0f9ef4fffe000000

def z925 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0xde7f41fc07603f82 0xf79fd07f01d80fe0

def z926 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xbffffffff8102030 0x2ffffffffe04080c

def z927 : W := mkw 0x24413ac29318302a 0x89104eb0a4c60c0a 0xeebf33c39f18387f 0x7bafccf0e7c60e1f

def z928 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x81fbfe0007f7c000 0xa07eff8001fdf000

def z929 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0x7bec520cf86cffff 0xdefb14833e1b3fff

def z930 : W := mkw 0x3c0135bbd0000000 0x0f004d6ef4000000 0x3ffbbdfff8000000 0x0ffeef7ffe000000

def z931 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xbffbfffff8930000 0x2ffefffffe24c000

def z932 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x1f7bc3fc78000000 0x07def0ff1e000000

def z933 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0xae1701c38700387e 0x2b85c070e1c00e1f

def z934 : W := mkw 0x3f03ffbbd4c28000 0x0fc0ffeef530a000 0x3ffbfffff8830000 0x0ffefffffe20c000

def z935 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3fc801fff8000000 0x0ff2007ffe000000

def z936 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01235e00076fc000 0x4048d78001dbf000

def z937 : W := mkw 0x3d03ffbbd21a8002 0x0f40ffeef486a000 0x3ffbfffff8130000 0x0ffefffffe04c000

def z938 : W := mkw 0x1f02cfbbd4c28000 0x07c0b3eef530a000 0x3f40cffff8e7c000 0x8fd033fffe39f000

def z939 : W := mkw 0x28613493e21d02fa 0xca184d24f88740be 0x20803003e018007d 0x08200c00f806001f

def z940 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x3e2353ffff68c000 0x4f88d4ffffda3000

def z941 : W := mkw 0x2343fa8286da802a 0x88d0fea0a1b6a00a 0xc1fbfe0307ffc031 0xf07eff80c1fff00c

def z942 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xbffbfffffffbc000 0x6ffefffffffef000

def z943 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01fbfe00077fc001 0x407eff8001dff000

def z944 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0xfffffffff89721b1 0xbffffffffe25c86c

def z945 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xe7fbfe0307ffc001 0xf9feff80c1fff000

def z946 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x3ffbffffffefc000 0xcffefffffffbf000

def z947 : W := mkw 0x29613e93e21f82fa 0xca584fa4f887e0be 0x21803e03e01fc07d 0x08600f80f807f01f

def z948 : W := mkw 0x1002c12800000000 0x0400b04a00000000 0x3e7bc1fcf8000000 0x0f9ef07f3e000000

def z949 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xdbfbfe0c07ffc001 0xf6feff8301fff000

def z950 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0x0163ce0007e7c000 0xc058f38001f9f000

def z951 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xee3f21c38710387e 0x7b8fc870e1c40e1f

def z952 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0xfffffffff89321f3 0x3ffffffffe24c87c

def z953 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x1963dffcffefc000 0xc658f7ff3ffbf000

def z954 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x8173fe0007ffc000 0xe05cff8001fff000

def z955 : W := mkw 0x1280016c05e03d01 0x04a0005b01780f40 0xde3f01fc07e03f82 0xf78fc07f01f80fe0

def z956 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0xfe5c81fff8802782 0xbf97207ffe2009e0

def z957 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdfffc1fc07e43f83 0xf7fff07f01f90fe0

def z958 : W := mkw 0x3f23ffbbd6db8092 0x4fc8ffeef5b6e024 0xffffffffffffe1b1 0xfffffffffffff86c

def z959 : W := mkw 0x3303fb2806da8002 0x0cc0feca01b6a000 0xd1fbfe3c07ffc001 0xf47eff8f01fff000

def z960 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fc1fc07e83fcf 0xf79ff07f01fa0ff3

def z961 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xde7fc1fc07e8ff8e 0xf79ff07f01fa3fe3

def z962 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7fcbc33609f27f3 0xfdff2f0cd827c9fc

def z963 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7fcec3360f727f3 0xfdff3b0cd83dc9fc

def z964 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfffcfe3cf8ffffcf 0xffff3f8f3e3ffff3

def z965 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffbfffff8100001 0x3ffefffffe040000

def z966 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xb5d4ac33609727f1 0xad752b0cd825c9fc

def z967 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x3e0013fff8000000 0x0f8004fffe000000

def z968 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3be8520cf86cde0c 0xcefa14833e1b3783

def z969 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd65fc1fc07e02782 0xb597f07f01f809e0

def z970 : W := mkw 0x1000012800000000 0x0400004a00000000 0x3fe853fcf8000000 0x0ffa14ff3e000000

def z971 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc193be0007ffc001 0xf064ef8001fff000

def z972 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xe1fbfe00ffffc001 0xf87eff803ffff000

def z973 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0x0140ce0007efc000 0xc050338001fbf000

def z974 : W := mkw 0x3e03ffbbd6d80002 0x0f80ffeef5b60000 0xfffbfffffff80001 0xfffefffffffe0000

def z975 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbffffff78c001 0x7ffeffffffde3000

def z976 : W := mkw 0x3303fb2806da8102 0x0cc0feca01b6a040 0xc1fbfe3007ffc181 0xf07eff8c01fff060

def z977 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x2fbb7fcff8000000 0x0beedff3fe000000

def z978 : W := mkw 0xa0d130442b3c7e6f 0xa8344c110acf1f9b 0xc1ff7200077cfe7f 0xf07fdc8001df3f9f

def z979 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0xfffbffffff18184f 0x7ffeffffffc60613

def z980 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x41eb7e00077fc001 0xd07adf8001dff000

def z981 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x182353fcf8000000 0x0608d4ff3e000000

def z982 : W := mkw 0x3303fb2806da8002 0x0cc0feca01b6a000 0xc9fbffcc07ffc001 0xf27efff301fff000

def z983 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc17bee0007f7c000 0xf05efb8001fdf000

def z984 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xe8a731c38718387f 0x7a29cc70e1c60e1f

def z985 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9e57c1fc07e03f82 0xa795f07f01f80fe0

def z986 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xfeff31c387183e7f 0xffbfcc70e1c60f9f

def z987 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7ffb53ccf86cde4f 0xdffed4f33e1b3793

def z988 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9e7fc1fc07803f82 0x279ff07f01e00fe0

def z989 : W := mkw 0x98b0057d69257fd5 0x662c015f5a495ff5 0x3e0401fff8003ffe 0x0f81007ffe000fff

def z990 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff800184e 0x0ffefffffe000613

def z991 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbffffff9b0001 0x7ffeffffffe6c000

def z992 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd47fc1fc07e02780 0xf51ff07f01f809e0

def z993 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x5e6f41fc07603f82 0xd79bd07f01d80fe0

def z994 : W := mkw 0x08200451610532d0 0x4208011458414cb4 0xefbf2dc367173873 0x7befcb70d9c5ce1c

def z995 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0x945781f007802780 0xa515e07c01e009e0

def z996 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x1940cffcf8000000 0x065033ff3e000000

def z997 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x3fe87ffff8000000 0x0ffa1ffffe000000

def z998 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xce3f21c30718387f 0x738fc870c1c60e1f

def z999 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff8170001 0x0ffefffffe05c000

def z1000 : W := mkw 0x1282c12c04e00d01 0x04a0b04b01380340 0xde7bc1fc07e00780 0xf79ef07f01f801e0

def z1001 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xb794ac33609727f3 0x2de52b0cd825c9fc

def z1002 : W := mkw 0x1c02c5bbd0000000 0x0700b16ef4000000 0x3e1381fff8000000 0x0f84e07ffe000000

def z1003 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xffffbdf3879f3fff 0xffffef7ce1e7cfff

def z1004 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xee1721c38718387f 0x7b85c870e1c60e1f

def z1005 : W := mkw 0x8090000428244e45 0x202400010a091391 0x39e0520cf86cde4d 0xce7814833e1b3793

def z1006 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0x961781f007802782 0x2585e07c01e009e0

def z1007 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfffc520cf86cfe4f 0xffff14833e1b3f93

def z1008 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e3b01fff8000000 0x0f8ec07ffe000000

def z1009 : W := mkw 0x0000004001003000 0x0000001000400c00 0xd65f81f007802782 0xb597e07c01e009e0

def z1010 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9c77c1fc07e03f80 0xe71df07f01f80fe0

def z1011 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x3ffbffffff7fc001 0x4ffeffffffdff000

def z1012 : W := mkw 0x3703fb2816da8002 0x0dc0feca05b6a000 0xc1fbfe0c1fffc001 0xf07eff8307fff000

def z1013 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xde7fc3fc1fe0ff82 0xf79ff0ff07f83fe0

def z1014 : W := mkw 0x3c0135bbd0000000 0x0f004d6ef4000000 0x3ffb73fff8000000 0x0ffedcfffe000000

def z1015 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xc41781f007802782 0xb105e07c01e009e0

def z1016 : W := mkw 0xa393fa442ffeff47 0x28e4fe910bffbfd1 0xc1fffe0007ffffcf 0xf07fff8001fffff3

def z1017 : W := mkw 0x80f000442b3d7eff 0xe03c00110acf5fbf 0xc004000007ffffff 0xf001000001ffffff

def z1018 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x0143ce0007e7c000 0x8050f38001f9f000

def z1019 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xc5fbffc307ffc001 0xf17efff0c1fff000

def z1020 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1fbfe0007ffd84f 0xf07eff8001fff613

def z1021 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01e3fe0007ffc001 0xc078ff8001fff000

def z1022 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1fffe0007ffe073 0xf07fff8001fff81c

def z1023 : W := mkw 0x0000008280000000 0x00000020a0000000 0x3e0001cff8000000 0x0f800073fe000000

def z1024 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff8800780 0x8ffefffffe2001e0

def z1025 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e67c1fc07e03f82 0xc799f07f01f80fe0

def z1026 : W := mkw 0x0000004001003000 0x0000001000400c00 0xeebf31c38718387f 0x7bafcc70e1c60e1f

def z1027 : W := mkw 0x140001aa90000000 0x0500006aa4000000 0x3be853ccf8000000 0x0efa14f33e000000

def z1028 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbfffffff30000 0xfffefffffffcc000

def z1029 : W := mkw 0x3f03ffbbd4c28000 0x0fc0ffeef530a000 0xfffbfffff8f7c001 0xbffefffffe3df000

def z1030 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0x8140ce0007f7c000 0xa050338001fdf000

def z1031 : W := mkw 0x0280004405e03d01 0x00a0001101780f40 0xde7f81f007e03f82 0xf79fe07c01f80fe0

def z1032 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x841781f007e02780 0xa105e07c01f809e0

def z1033 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0xbffbffffff100000 0x2ffeffffffc40000

def z1034 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x3ffbffffff000000 0x0ffeffffffc00000

def z1035 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd5dcac33609727b1 0xb5772b0cd825c9ec

def z1036 : W := mkw 0x2343fa8286da802a 0x88d0fea0a1b6a00a 0xeffbffc387ffc07d 0xfbfefff0e1fff01f

def z1037 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xee9f21c38710387f 0x3ba7c870e1c40e1f

def z1038 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xf7dcac33f89727ff 0xbdf72b0cfe25c9ff

def z1039 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc1802c0007ffc001 0xf0600b0001fff000

def z1040 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0x7beb53ccff6cc001 0xdefad4f33fdb3000

def z1041 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdfffedfc07e03f82 0xf7fffb7f01f80fe0

def z1042 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x3fd8bffff8000000 0x0ff62ffffe000000

def z1043 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x29fbffcff8000000 0x0a7efff3fe000000

def z1044 : W := mkw 0x3303fb2806da8002 0x0cc0feca01b6a000 0xdffffffc07ffe783 0xf7ffffff01fff9e0

def z1045 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x3fbb3ffff8000000 0x0feecffffe000000

def z1046 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbffffffffd84f 0xfffefffffffff613

def z1047 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x1963cffc78000000 0x0658f3ff1e000000

def z1048 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x196353ccf8000000 0x0658d4f33e000000

def z1049 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0xeebf21c30718387f 0x7bafc870c1c60e1f

def z1050 : W := mkw 0x82b000442de57fd5 0x60ac00110b795ff5 0xc004000007ffffff 0xf001000001ffffff

def z1051 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xe1fbfe0307ffc071 0xf87eff80c1fff01c

def z1052 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcbc33e09f27ff 0xbdf72f0cf827c9ff

def z1053 : W := mkw 0x8090000428244e45 0x202400010a091391 0x69a0520cf86cde4f 0xda6814833e1b3793

def z1054 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x3fe8dffff8000000 0x0ffa37fffe000000

def z1055 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0x3ffbffffff600000 0x4ffeffffffd80000

def z1056 : W := mkw 0x8090000408204c05 0x2024000102081301 0x1960520cf868d80c 0x465814833e1a3603

def z1057 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff868c000 0x4ffefffffe1a3000

def z1058 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc033fe0007ffc001 0xf00cff8001fff000

def z1059 : W := mkw 0x0820041140010090 0x4208010450004024 0x9454ac33009327b0 0xa5152b0cc024c9ec

def z1060 : W := mkw 0x80d0004429247e6d 0xa03400110a491f9b 0x0004000000003e7e 0x0001000000000f9f

def z1061 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0x8153ce0007e7c000 0xa054f38001f9f000

def z1062 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xee3f11c38708387e 0x7b8fc470e1c20e1f

def z1063 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff89027f3 0xbffffffffe2409fc

def z1064 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x29a37fcfff7fc001 0x4a68dff3ffdff000

def z1065 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e0001fff800184e 0x0f80007ffe000613

def z1066 : W := mkw 0x33c3fbee87fabd2b 0x8cf0fefba1feaf4a 0x082353cc8768d80c 0x4208d4f321da3603

def z1067 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcbe33f89727f3 0xbdf72f8cfe25c9fc

def z1068 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xbffbffffff9fc001 0x2ffeffffffe7f000

def z1069 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3ba0520cf86cde4f 0x4ee814833e1b3793

def z1070 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefffffc387fff87f 0xfbfffff0e1fffe1f

def z1071 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xc47fc1f007e03f82 0xf11ff07c01f80fe0

def z1072 : W := mkw 0x21413ac2831ab02a 0x88504eb0a0c6ac0a 0xefff7fc3877ff87f 0xfbffdff0e1dffe1f

def z1073 : W := mkw 0x80d000442b3c7e6f 0xa03400110acf1f9b 0xc004000007183e7f 0x7001000001c60f9f

def z1074 : W := mkw 0xa8713493ea1d42fe 0xea1c4d24fa8750bf 0x21803e03f81fc07d 0x08600f80fe07f01f

def z1075 : W := mkw 0x004000c28318302a 0x80100030a0c60c0a 0xee3f01c38718387f 0x7b8fc070e1c60e1f

def z1076 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfffcfe0ff8fffe7f 0xffff3f83fe3fff9f

def z1077 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcac3360973ff3 0xffff2b0cd825cffc

def z1078 : W := mkw 0x2343fa8286da802a 0x88d0fea0a1b6a00a 0xebfbfe0387ffd87f 0xfafeff80e1fff61f

def z1079 : W := mkw 0x829000442de47f45 0x20a400110b791fd1 0xc004000007e4ff82 0xf001000001f93fe0

def z1080 : W := mkw 0x1c2005bbd0010090 0x4708016ef4004024 0xbe14adfff89321b0 0x2f852b7ffe24c86c

def z1081 : W := mkw 0x1382cb6c05e2bd01 0x04e0b2db0178af40 0xde7fcdfc07e33f82 0xf79ff37f01f8cfe0

def z1082 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffffffff8002782 0x0ffffffffe0009e0

def z1083 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebf31c3879f387f 0xfbafcc70e1e7ce1f

def z1084 : W := mkw 0x2303fa0004c28000 0x08c0fe800130a000 0xc1fbfe0007e7c000 0xf07eff8001f9f000

def z1085 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3e0301fff8000000 0x0f80c07ffe000000

def z1086 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3fc0fffff8000000 0x0ff03ffffe000000

def z1087 : W := mkw 0x3d013fbbd21a8002 0x0f404feef486a000 0x3f803ffff81fc001 0x0fe00ffffe07f000

def z1088 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3fa37ffff8000000 0x0fe8dffffe000000

def z1089 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7fec523cf86cffcf 0xdffb148f3e1b3ff3

def z1090 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfe7fc1ff07e03ff2 0xff9ff07fc1f80ffc

def z1091 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x3ffbd3fcf8000000 0x0ffef4ff3e000000

def z1092 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc9fbfe0087ffd80d 0xf27eff8021fff603

def z1093 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x8013ac0007f7c000 0xa004eb0001fdf000

def z1094 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfeffe1ff07e03f82 0xffbff87fc1f80fe0

def z1095 : W := mkw 0x3c013fbbd0000000 0x0f004feef4000000 0x29803fcff8000000 0x0a600ff3fe000000

def z1096 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xb7dcac33609327f2 0x2df72b0cd824c9fc

def z1097 : W := mkw 0x2343fa8286da802a 0x88d0fea0a1b6a00a 0xe7fffe0387ffe07f 0xf9ffff80e1fff81f

def z1098 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x9e37c1fc07e03f82 0x678df07f01f80fe0

def z1099 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xffffffffffffe073 0xfffffffffffff81c

def z1100 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0xfffbfffffff70001 0xfffefffffffdc000

def z1101 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e0401fff8002072 0x0f81007ffe00081c

def z1102 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0xffd8adfff8970001 0xbff62b7ffe25c000

def z1103 : W := mkw 0x2001308280000000 0x08004c20a0000000 0x3beb53ccf8000000 0x0efad4f33e000000

def z1104 : W := mkw 0xa0913086a8244e45 0x28244c21aa091391 0x6ebb31c3806cde4f 0xdbaecc70e01b3793

def z1105 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x1540cfff78000000 0x055033ffde000000

def z1106 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xcc37c1fc07e03f82 0xf30df07f01f80fe0

def z1107 : W := mkw 0x03000a0006da8002 0x00c0028001b6a000 0xc1000e0007ffc001 0xf040038001fff000

def z1108 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xe9fbffcfffffc001 0xfa7efff3fffff000

def z1109 : W := mkw 0x0820041140010090 0x4208010450004024 0x9614ac33009327b2 0x25852b0cc024c9ec

def z1110 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e7bc1fc07e01f80 0xc79ef07f01f807e0

def z1111 : W := mkw 0x1202c16805c03100 0x0480b05a01700c40 0xde7f81f007803f82 0xf79fe07c01e00fe0

def z1112 : W := mkw 0x8090000428244e45 0x202400010a091391 0x0920520cf86cd80c 0x424814833e1b3603

def z1113 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefbf33c3ff18387f 0x7befccf0ffc60e1f

def z1114 : W := mkw 0x3f03ffbbd4c28000 0x0fc0ffeef530a000 0x7ffbfffff8efc001 0xdffefffffe3bf000

def z1115 : W := mkw 0x0202c00004c00000 0x0080b00001300000 0xc1fbfe0007ffc001 0xf07eff8001fff000

def z1116 : W := mkw 0x3d03ffbbd21a8002 0x0f40ffeef486a000 0x7ffbfffff87fc001 0xdffefffffe1ff000

def z1117 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0xbffbffffff800000 0x2ffeffffffe00000

def z1118 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff8080001 0x5ffefffffe020000

def z1119 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x9553efff7ff7c000 0xa554fbffdffdf000

def z1120 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xc5dcac33009727f3 0xb1772b0cc025c9fc

def z1121 : W := mkw 0x3c4135bbd218002a 0x8f104d6ef486000a 0x3e8031fff818007d 0x0fa00c7ffe06001f

def z1122 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xffffedff07f73ff3 0xfffffb7fc1fdcffc

def z1123 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7bf8fe0cf86cde4f 0xdefe3f833e1b3793

def z1124 : W := mkw 0x2d213e93f21f82d2 0x4b484fa4fc87e0b4 0x21803e03f81fc071 0x08600f80fe07f01c

def z1125 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x3a2353ccf8000000 0x0e88d4f33e000000

def z1126 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xf7fffe3307ffe7f3 0xfdffff8cc1fff9fc

def z1127 : W := mkw 0x214130c2831ab02a 0x88504c30a0c6ac0a 0xeebf31c3871ff87f 0x7bafcc70e1c7fe1f

def z1128 : W := mkw 0x3d03ffbbd21a8002 0x0f40ffeef486a000 0x3ffbfffff808c000 0x0ffefffffe023000

def z1129 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7a20520cf86cde4f 0xde8814833e1b3793

def z1130 : W := mkw 0x1c2005bbd0010090 0x4708016ef4004024 0x3e0401fff80021b0 0x0f81007ffe00086c

def z1131 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0xfffc720ff8ffffff 0xffff1c83fe3fffff

def z1132 : W := mkw 0x0000004001003000 0x0000001000400c00 0xde3f01f007003f82 0x778fc07c01c00fe0

def z1133 : W := mkw 0x3c43ffbbd218002a 0x8f10ffeef486000a 0x3ffbfffff808000c 0x0ffefffffe020003

def z1134 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0x1e2701fc07003f82 0x4789c07f01c00fe0

def z1135 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff8972783 0xbffffffffe25c9e0

def z1136 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xffdcac3ff89727f3 0xbff72b0ffe25c9fc

def z1137 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xfeffb1f38718387f 0x7fbfec7ce1c60e1f

def z1138 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3bebdffcf8000000 0x0efaf7ff3e000000

def z1139 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fc1fc07ecff83 0xf79ff07f01fb3fe0

def z1140 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x2ebf31c38708387e 0x4bafcc70e1c20e1f

def z1141 : W := mkw 0x8090004429247e45 0x202400110a491f91 0xc0040000076cfe4f 0xf001000001db3f93

def z1142 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbec520cf8ecffcf 0xfefb14833e3b3ff3

def z1143 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff8000602 0x9ffefffffe000180

def z1144 : W := mkw 0x21413ac2831ab02a 0x88504eb0a0c6ac0a 0xeebf33c38718f87f 0x7bafccf0e1c63e1f

def z1145 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7be8720ff87cde7f 0xdefa1c83fe1f379f

def z1146 : W := mkw 0x0202c04005c03000 0x0080b01001700c00 0xde7fc1f007e03f82 0xf79ff07c01f80fe0

def z1147 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xe49731c38718387f 0x7925cc70e1c60e1f

def z1148 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x180001fcf8000000 0x0600007f3e000000

def z1149 : W := mkw 0x8090000428244e45 0x202400010a091391 0x1820520cf868de0c 0x460814833e1a3783

def z1150 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x19fbfffcf8000000 0x067effff3e000000

def z1151 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0x7be8520cf8efdfcf 0xdefa14833e3bf7f3

def z1152 : W := mkw 0x8090000428244e45 0x202400010a091391 0x71c0520cf86cde4f 0xdc7014833e1b3793

def z1153 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7ff8d23cf86cde4f 0xdffe348f3e1b3793

def z1154 : W := mkw 0x204130828218002a 0x88104c20a086000a 0xf6dcb033809827ff 0xbdb72c0ce02609ff

def z1155 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf69cac33609327f3 0x3da72b0cd824c9fc

def z1156 : W := mkw 0x28613493e21d02fa 0xca184d24f88740be 0x21802c0360170071 0x08600b00d805c01c

def z1157 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xffffffffffffe783 0xfffffffffffff9e0

def z1158 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xce3f81f007e03f82 0xf38fe07c01f80fe0

def z1159 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xffffadf3609727f3 0xbfffeb7cd825c9fc

def z1160 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdfffd3fc07e03f82 0xf7fff4ff01f80fe0

def z1161 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde3f41fc07603f82 0x778fd07f01d80fe0

def z1162 : W := mkw 0x23013a0006da8002 0x08c04e8001b6a000 0xc1d8be0007ffc001 0xf0762f8001fff000

def z1163 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xb7dcac33609727b0 0xadf72b0cd825c9ec

def z1164 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x29a353ccf8000000 0x0a68d4f33e000000

def z1165 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xacb731c38718387d 0x6b2dcc70e1c60e1f

def z1166 : W := mkw 0x3d43ffbbd21a802a 0x8f50ffeef486a00a 0x3ffbfffff81fc07d 0x0ffefffffe07f01f

def z1167 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x6aab31c38718187f 0x5aaacc70e1c6061f

def z1168 : W := mkw 0x8090000428244e45 0x202400010a091391 0x2820520cf868d84c 0x4a0814833e1a3613

def z1169 : W := mkw 0x0302c00006da8002 0x00c0b00001b6a000 0xc1fbec0007ffc001 0xf07efb0001fff000

def z1170 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff8600000 0xdffefffffe180000

def z1171 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcbe33609fe7f3 0xbdf72f8cd827f9fc

def z1172 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcfe3ff8ffe7f3 0xffff3f8ffe3ff9fc

def z1173 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x3ffbdffcf8000000 0x0ffef7ff3e000000

def z1174 : W := mkw 0x3c43ffbbd218002a 0x8f10ffeef486000a 0x7ffbfffff818187f 0x5ffefffffe06061f

def z1175 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcee3360f7e7f3 0xbdf73b8cd83df9fc

def z1176 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xbffffffff8802180 0x2ffffffffe200860

def z1177 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc163de0007ffc001 0xf058f78001fff000

def z1178 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfefff1ff87f83fff 0xffbffc7fe1fe0fff

def z1179 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xfeffd1fc87e03f82 0xffbff47f21f80fe0

def z1180 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeeffb1c38798387f 0xfbbfec70e1e60e1f

def z1181 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbffffff970001 0xbffeffffffe5c000

def z1182 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e2053fff8000000 0x0f8814fffe000000

def z1183 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x39e3fffff8000000 0x0e78fffffe000000

def z1184 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0x9e1701fc07003f82 0x2785c07f01c00fe0

def z1185 : W := mkw 0x2c013e93d0000000 0x0b004fa4f4000000 0x3ffb7fcff8000000 0x0ffedff3fe000000

def z1186 : W := mkw 0x3d03ffbbd21a8002 0x0f40ffeef486a000 0xfffbfffff89fc001 0xbffefffffe27f000

def z1187 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xd554ac33609727f3 0xb5552b0cd825c9fc

def z1188 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffffffff8002072 0x0ffffffffe00081c

def z1189 : W := mkw 0x3c03f5bbd0000000 0x0f00fd6ef4000000 0x3efbf1fff8000000 0x0fbefc7ffe000000

def z1190 : W := mkw 0x3c43ffbbd218002a 0x8f10ffeef486000a 0xfffffffff818207f 0x3ffffffffe06081f

def z1191 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3fdbadfff8000000 0x0ff6eb7ffe000000

def z1192 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7be8de0cf8efde4f 0xdefa37833e3bf793

def z1193 : W := mkw 0x0302ca0004c28000 0x00c0b2800130a000 0xc140ce0007e7c000 0xf050338001f9f000

def z1194 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff86cd84f 0xdffefffffe1b3613

def z1195 : W := mkw 0x3303fbaa86da8002 0x0cc0feeaa1b6a000 0xfffbffff87ffc001 0xfffeffffe1fff000

def z1196 : W := mkw 0x1000012800000000 0x0400004a00000000 0x3e0001fcf8000000 0x0f80007f3e000000

def z1197 : W := mkw 0x004000400318302a 0x8010001000c60c0a 0xfbec520cff18387f 0x7efb14833fc60e1f

def z1198 : W := mkw 0x9ab2c53d6ce54fd5 0x66acb14f5b3953f5 0x1140ce3c78e7c780 0x8450338f1e39f1e0

def z1199 : W := mkw 0x3c43ffbbd218002a 0x8f10ffeef486000a 0xfffbffffff18007d 0x7ffeffffffc6001f

def z1200 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xffdcac33e0973fff 0xbff72b0cf825cfff

def z1201 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffbfffff8ffc001 0xfffefffffe3ff000

def z1202 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ffb53ccf8000000 0x0ffed4f33e000000

def z1203 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbf8d20cf8ecde4f 0xfefe34833e3b3793

def z1204 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xe594ac33609727f3 0xb9652b0cd825c9fc

def z1205 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0xffffffffffe02782 0xfffffffffff809e0

def z1206 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0x3ffbffffff080000 0x4ffeffffffc20000

def z1207 : W := mkw 0x3c43ffbbd0000028 0x8f10ffeef400000a 0x3ffbfffff800007c 0x0ffefffffe00001f

def z1208 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xfeff71cf8718387f 0x7fbfdc73e1c60e1f

def z1209 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0xdffbfffc9fffc001 0xf7feffff27fff000

def z1210 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3ff8fffff8000000 0x0ffe3ffffe000000

def z1211 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff80cc001 0x0ffefffffe033000

def z1212 : W := mkw 0x1382cb6c05e2bd01 0x04e0b2db0178af40 0xdfffdffc07efff83 0xf7fff7ff01fbffe0

def z1213 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x01fbfe0007efc000 0xc07eff8001fbf000

def z1214 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0xeebf11c38708387f 0x7bafc470e1c20e1f

def z1215 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1c0fe0007ffc001 0xf0703f8001fff000

def z1216 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefbf33c3871cf87f 0x7befccf0e1c73e1f

def z1217 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xd9fbfffcffffc001 0xf67effff3ffff000

def z1218 : W := mkw 0x1080016c01203d01 0x0420005b00480f40 0xde7f81fc07803f82 0xf79fe07f01e00fe0

def z1219 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x282311c38708187c 0x4a08c470e1c2061f

def z1220 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfbec520cf87cfe7f 0xfefb14833e1f3f9f

def z1221 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc9fbfe0c9fffc001 0xf27eff8327fff000

def z1222 : W := mkw 0x23013a0006da8002 0x08c04e8001b6a000 0xc1bb3e0007ffc001 0xf06ecf8001fff000

def z1223 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcfe33e0ffffff 0xffff3f8cf83fffff

def z1224 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ebbbdfff8000000 0x0faeef7ffe000000

def z1225 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xdfffd3fc9fecff8f 0xf7fff4ff27fb3fe3

def z1226 : W := mkw 0x8090004429247f45 0x202400110a491fd1 0x0004000000003fce 0x0001000000000ff3

def z1227 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x1553cffc78000000 0x0554f3ff1e000000

def z1228 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7dcac33009727f3 0xbdf72b0cc025c9fc

def z1229 : W := mkw 0x0820041140010090 0x4208010450004024 0xc414ac33009327b2 0xb1052b0cc024c9ec

def z1230 : W := mkw 0x80b0000428254ed5 0x602c00010a0953b5 0x7be8520cf87fde7f 0xdefa14833e1ff79f

def z1231 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd457c1fc07e03f82 0xf515f07f01f80fe0

def z1232 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffbfffff8800000 0xbffefffffe200000

def z1233 : W := mkw 0x80d0004429247e6d 0xa03400110a491f9b 0x40040000006cfe7f 0xd0010000001b3f9f

def z1234 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xd1fbfe0c7fffc001 0xf47eff831ffff000

def z1235 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7fec520ff86cfe7f 0xdffb1483fe1b3f9f

def z1236 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fe1ff07f03fb2 0xf79ff87fc1fc0fec

def z1237 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1413adff78000000 0x0504eb7fde000000

def z1238 : W := mkw 0x83d000442ffefe6f 0xa0f400110bffbf9b 0xc004000007fffe7f 0xf001000001ffff9f

def z1239 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0x81b3fe0007ffc001 0x606cff8001fff000

def z1240 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xe3fbfe0007ffc043 0xf8feff8001fff010

def z1241 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0xc17bce0007ffc001 0xf05ef38001fff000

def z1242 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebfbdc3879b387f 0x7bafef70e1e6ce1f

def z1243 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fd3fc9fe03f82 0xf79ff4ff27f80fe0

def z1244 : W := mkw 0x3c43ffbbd218002a 0x8f10ffeef486000a 0x3ffbfffff8100030 0x0ffefffffe04000c

def z1245 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3f93bffff8000000 0x0fe4effffe000000

def z1246 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7fcfe33609727f3 0xbdff3f8cd825c9fc

def z1247 : W := mkw 0x21413ac2831ab02a 0x88504eb0a0c6ac0a 0xeebf3dc3871b387f 0x7bafcf70e1c6ce1f

def z1248 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3feb53fff8000000 0x0ffad4fffe000000

def z1249 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xffffc1fc67e03f82 0xfffff07f19f80fe0

def z1250 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1143cffc78000000 0x0450f3ff1e000000

def z1251 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xffffd3fcffe83fcf 0xfffff4ff3ffa0ff3

def z1252 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xf7dcac33609fe7ff 0xbdf72b0cd827f9ff

def z1253 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0xfffbffffffe8c000 0xfffefffffffa3000

def z1254 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fc1fc07f73f83 0xf79ff07f01fdcfe0

def z1255 : W := mkw 0x3c03ff3950000000 0x0f00ffce54000000 0x1ffbfffc78000000 0x07feffff1e000000

def z1256 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf7dcac33609f3fff 0xfdf72b0cd827cfff

def z1257 : W := mkw 0x8090000408204c05 0x2024000102081301 0x29a0520cf868d80c 0x4a6814833e1a3603

def z1258 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff864c000 0x8ffefffffe193000

def z1259 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0xffffffffff182073 0x7fffffffffc6081c

def z1260 : W := mkw 0x8090000428244e45 0x202400010a091391 0x3b60520cf86cde4e 0xced814833e1b3793

def z1261 : W := mkw 0x88f004d7e9257efd 0xe23c0135fa495fbf 0x3e0401fff8003ffe 0x0f81007ffe000fff

def z1262 : W := mkw 0x829000442de47f45 0x20a400110b791fd1 0xc004000007e03fce 0xf001000001f80ff3

def z1263 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0xeffbffcf9fffc001 0xfbfefff3e7fff000

def z1264 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0xfffbffffff9f0001 0xfffeffffffe7c000

def z1265 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fedfc07f33f82 0xf79ffb7f01fccfe0

def z1266 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde5f81fc07803f82 0xb797e07f01e00fe0

def z1267 : W := mkw 0x004000c281003028 0x80100030a0400c0a 0xeebf21c38710387f 0x7bafc870e1c40e1f

def z1268 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebf31c3877cf87f 0xfbafcc70e1df3e1f

def z1269 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0xfe9c21fff8102073 0x3fa7087ffe04081c

def z1270 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xfffcfe3ff89fe7ff 0xbfff3f8ffe27f9ff

def z1271 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xeffbffc387ffd84f 0xfbfefff0e1fff613

def z1272 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xfebf31f387183fff 0x7fafcc7ce1c60fff

def z1273 : W := mkw 0x2303fa8286da8002 0x08c0fea0a1b6a000 0xefffffc387ffe073 0xfbfffff0e1fff81c

def z1274 : W := mkw 0x3c23ffbbd0010090 0x4f08ffeef4004024 0x3ffbfffff8130030 0x0ffefffffe04c00c

def z1275 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1043c1fc07e00780 0x8410f07f01f801e0

def z1276 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x941781fc07802780 0x2505e07f01e009e0

def z1277 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xd1fbfe3007ffc781 0xf47eff8c01fff1e0

def z1278 : W := mkw 0x9292c16c0de07d05 0x24a4b05b03781f41 0xfeffd3fc9fe8ffcf 0xffbff4ff27fa3ff3

def z1279 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd65f81f007e03f82 0xf597e07c01f80fe0

def z1280 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0x1e0701fc07003f82 0x0781c07f01c00fe0

def z1281 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xd3fbfe0007ffc603 0xf4feff8001fff180

def z1282 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1bb7e00077fc001 0x706edf8001dff000

def z1283 : W := mkw 0x28013493c0000000 0x0a004d24f0000000 0x3ffbfffff8000000 0x0ffefffffe000000

def z1284 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ffbfffff8870000 0x8ffefffffe21c000

def z1285 : W := mkw 0x8090000428244e45 0x202400010a091391 0xfffcf23ff8fcffff 0xffff3c8ffe3f3fff

def z1286 : W := mkw 0x3d03ffbbd0028000 0x0f40ffeef400a000 0x3ffbfffff807c000 0x0ffefffffe01f000

def z1287 : W := mkw 0x23013a0006da8002 0x08c04e8001b6a000 0x01803e00077fc001 0x40600f8001dff000

def z1288 : W := mkw 0x140001aa90000000 0x0500006aa4000000 0x3a0001ccf8000000 0x0e8000733e000000

def z1289 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1a37e0007ffc001 0xf068df8001fff000

def z1290 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde7fd1fc87e83f8e 0xf79ff47f21fa0fe3

def z1291 : W := mkw 0x1202c12804c00000 0x0480b04a01300000 0xfffbd3fcffecc001 0xfffef4ff3ffb3000

def z1292 : W := mkw 0x3703fbaa96da8002 0x0dc0feeaa5b6a000 0xc1fbffc007ffc001 0xf07efff001fff000

def z1293 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0x6eaf11c38708387f 0x5babc470e1c20e1f

def z1294 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff8001802 0x5ffefffffe000600

def z1295 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3e0401fff8002782 0x0f81007ffe0009e0

def z1296 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xde2741fc07e03f82 0xf789d07f01f80fe0

def z1297 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x1f40cffc78000000 0x07d033ff1e000000

def z1298 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xd867c1fc07e03f82 0xf619f07f01f80fe0

def z1299 : W := mkw 0x8090000428244e45 0x202400010a091391 0x7be8d23cf8ecdfcf 0xdefa348f3e3b37f3

def z1300 : W := mkw 0x0300000006da8002 0x00c0000001b6a000 0xc1f8fe0007ffc001 0xf07e3f8001fff000

def z1301 : W := mkw 0x204130c281003028 0x88104c30a0400c0a 0xeebf31c38700387e 0x7bafcc70e1c00e1f

def z1302 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xe69cac33009727f3 0xb9a72b0cc025c9fc

def z1303 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff8002002 0x3ffffffffe000800

def z1304 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1f7befff78000000 0x07defbffde000000

def z1305 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdf7fc3fc7fe03f82 0xf7dff0ff1ff80fe0

def z1306 : W := mkw 0x1682cb6c15e03d01 0x05a0b2db05780f40 0xde7fc3fc1fe03f82 0xf79ff0ff07f80fe0

def z1307 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x1f7bdffcf8000000 0x07def7ff3e000000

def z1308 : W := mkw 0x1c4005bbd0000028 0x8710016ef400000a 0x3e0001fff800007c 0x0f80007ffe00001f

def z1309 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xb754ac33609727f2 0xadd52b0cd825c9fc

def z1310 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xeebf31c387983fff 0xfbafcc70e1e60fff

def z1311 : W := mkw 0x1c0005bbd0000000 0x0700016ef4000000 0x3f802dfff8000000 0x0fe00b7ffe000000

def z1312 : W := mkw 0x8090000428244e45 0x202400010a091391 0x59e8520cf86cde0d 0xd67a14833e1b3783

def z1313 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xae3731c38718387e 0x6b8dcc70e1c60e1f

def z1314 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xfffcec3f609727f3 0xbfff3b0fd825c9fc

def z1315 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x3bfbffccf8000000 0x0efefff33e000000

def z1316 : W := mkw 0x3f23ffbbd6db8092 0x4fc8ffeef5b6e024 0xbfffffffff9321b0 0x2fffffffffe4c86c

def z1317 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffbffffff000000 0x7ffeffffffc00000

def z1318 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x3e008dfff8000000 0x0f80237ffe000000

def z1319 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xc1dbac0007ffc001 0xf076eb0001fff000

def z1320 : W := mkw 0x88300411680542d4 0x620c01045a0150b5 0xf7dcae337897e7f3 0xbdf72b8cde25f9fc

def z1321 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff8040001 0x9ffefffffe010000

def z1322 : W := mkw 0x08200411600502d0 0x42080104580140b4 0xf1c4ac33609727f3 0xbc712b0cd825c9fc

def z1323 : W := mkw 0x1282c16c05e03d01 0x04a0b05b01780f40 0xdf7fcdfc07e73f82 0xf7dff37f01f9cfe0

def z1324 : W := mkw 0x3403fbaa90000000 0x0d00feeaa4000000 0x3ffb73cff8000000 0x0ffedcf3fe000000

def z1325 : W := mkw 0x3f03ff3956da8002 0x0fc0ffce55b6a000 0xdffbfffc7fffc001 0xf7feffff1ffff000

def z1326 : W := mkw 0x8090000428244e45 0x202400010a091391 0x69e8520cf86cd84d 0xda7a14833e1b3613

def z1327 : W := mkw 0x2303fa0006da8002 0x08c0fe8001b6a000 0xebfbfe0087ffc001 0xfafeff8021fff000

def z1328 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0xfffffffff8972073 0xbffffffffe25c81c

def z1329 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x7ffbfffff8000043 0x1ffefffffe000010

def z1330 : W := mkw 0x20413ac28318302a 0x88104eb0a0c60c0a 0xefbf3fc38718387f 0x7befcff0e1c60e1f

def z1331 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3ebb73fff8000000 0x0faedcfffe000000

def z1332 : W := mkw 0x3e03ffbbd4c00000 0x0f80ffeef5300000 0xfffbffffffecc001 0xfffefffffffb3000

def z1333 : W := mkw 0x1c02cfbbd0000000 0x0700b3eef4000000 0x3e0043fff8000000 0x0f8010fffe000000

def z1334 : W := mkw 0x3c03ffbbd2180002 0x0f00ffeef4860000 0xfffbffffff7cc001 0xfffeffffffdf3000

def z1335 : W := mkw 0x1282cb6c05e03d01 0x04a0b2db01780f40 0xdf7fcffc07e03f82 0xf7dff3ff01f80fe0

def z1336 : W := mkw 0x3c03ffbbd0000000 0x0f00ffeef4000000 0x3f63dffff8000000 0x0fd8f7fffe000000

def z1337 : W := mkw 0x8090000408204c05 0x2024000102081301 0x7be8520cf868d84f 0x5efa14833e1a3613

def z1338 : W := mkw 0x3f03ffbbd6da8002 0x0fc0ffeef5b6a000 0x7ffbffffff6cc001 0xdffeffffffdb3000

def z1339 : W := mkw 0x1c02cf3950000000 0x0700b3ce54000000 0x3ffbefff78000000 0x0ffefbffde000000

def z1340 : W := mkw 0x0302ca0006da8002 0x00c0b28001b6a000 0xc1e8de0007ffc001 0xf07a378001fff000

def z1341 : W := mkw 0x204130c28318302a 0x88104c30a0c60c0a 0xefff31c3871c387f 0xfbffcc70e1c70e1f

def z1342 : W := mkw 0x2343fa8286da802a 0x88d0fea0a1b6a00a 0xc1fbfe0087ffc00d 0xf07eff8021fff003

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z2,z7,z5,z6]),(0,[z8,z9,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z6,z11]),(0,[z12,z13,z1,z2,z4,z5,z6])],[(0,[z14,z0,z1,z2,z4,z5,z15]),(0,[z16,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z2,z4,z18,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z19]),(0,[z0,z1,z2,z4,z5,z20,z6]),(1,[z0,z21,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z22])],[(0,[z23,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z24,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z25,z5,z6]),(0,[z0,z1,z2,z4,z26,z5,z6]),(1,[z0,z1,z27,z2,z4,z6])],[(0,[z0,z1,z2,z4,z28,z29,z6]),(0,[z0,z30,z1,z2,z31,z5,z6]),(0,[z32,z0,z2,z4,z33,z5,z6])],[(0,[z34,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z37,z6]),(0,[z0,z38,z39,z2,z4,z5,z6]),(0,[z40,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z42]),(0,[z0,z1,z2,z4,z41,z41,z6]),(0,[z0,z1,z2,z43,z5,z41,z6])],[(1,[z0,z1,z2,z4,z5,z44]),(0,[z45,z9,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z46,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z48,z2,z4,z5,z6]),(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z0,z50,z1,z2,z4,z5,z6]),(0,[z0,z51,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z52,z29,z6]),(0,[z0,z1,z2,z4,z5,z53,z6]),(1,[z0,z1,z2,z43,z41,z6])],[(0,[z0,z1,z54,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z6,z55])]],
   [[(0,[z56,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z57]),(0,[z0,z1,z2,z31,z5,z41,z6])],[(0,[z0,z1,z2,z58,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z59]),(0,[z0,z1,z2,z4,z5,z60,z61]),(0,[z0,z1,z62,z2,z4,z5,z6]),(0,[z0,z63,z1,z2,z4,z5,z6])],[(0,[z16,z0,z64,z2,z4,z5,z6]),(1,[z8,z1,z2,z65,z5,z6]),(0,[z66,z0,z39,z2,z4,z5,z6]),(0,[z67,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z68,z6]),(0,[z69,z0,z1,z2,z4,z5,z6])],[(1,[z0,z70,z2,z4,z5,z6]),(0,[z0,z1,z71,z2,z4,z72,z6]),(0,[z0,z1,z2,z4,z73,z5,z6]),(0,[z74,z0,z1,z75,z2,z5,z6]),(0,[z0,z76,z1,z10,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z77,z6]),(0,[z78,z0,z30,z2,z4,z5,z6]),(0,[z79,z0,z1,z2,z4,z80,z6]),(0,[z0,z1,z10,z2,z4,z20,z6]),(0,[z81,z0,z1,z2,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z82,z45,z1,z2,z4,z5,z6]),(0,[z0,z1,z83,z2,z4,z5,z6]),(0,[z0,z30,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z4,z84,z5,z6])],[(0,[z82,z0,z1,z2,z4,z5,z6]),(0,[z45,z0,z1,z2,z4,z85,z6]),(0,[z0,z86,z1,z2,z4,z5,z6]),(0,[z12,z0,z87,z2,z4,z5,z6]),(0,[z88,z0,z1,z2,z43,z5,z6])],[(0,[z0,z1,z2,z89,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z90,z6]),(0,[z0,z91,z1,z2,z4,z5,z6])]],
   [[(0,[z14,z0,z1,z2,z4,z92,z6]),(0,[z93,z0,z1,z2,z4,z5,z6]),(0,[z94,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z95,z6,z96])],[(0,[z14,z66,z0,z2,z4,z5,z6]),(0,[z1,z17,z2,z4,z97,z5,z6]),(0,[z98,z0,z1,z10,z2,z4,z6]),(0,[z79,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z62,z2,z4,z5,z99]),(0,[z100,z0,z1,z2,z4,z5,z6])],[(0,[z101,z0,z1,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z65,z5,z6]),(0,[z103,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z104]),(0,[z0,z1,z2,z4,z5,z105,z106]),(0,[z107,z0,z1,z2,z4,z5,z6]),(0,[z78,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z108,z2,z4,z5,z6]),(0,[z0,z1,z21,z2,z4,z5,z6])],[(1,[z9,z1,z2,z36,z5,z6]),(0,[z109,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z46,z5,z41,z6]),(0,[z0,z1,z2,z4,z110,z5,z6]),(0,[z0,z1,z2,z4,z41,z111,z6])],[(0,[z98,z0,z1,z4,z97,z5,z6]),(0,[z0,z1,z112,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z113,z5,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z115,z2,z4,z5,z6])],[(0,[z0,z1,z2,z116,z4,z5,z6])],[(0,[z8,z0,z1,z10,z2,z4,z6]),(0,[z117,z9,z0,z1,z2,z5,z6]),(0,[z0,z1,z10,z2,z46,z4,z6]),(0,[z0,z2,z4,z5,z118,z6,z11]),(0,[z0,z1,z2,z119,z4,z5,z6]),(1,[z0,z120,z1,z2,z4,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z97,z121,z5,z6]),(0,[z0,z122,z1,z2,z123,z5,z6]),(0,[z0,z1,z71,z2,z4,z5,z6]),(0,[z0,z124,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z125]),(0,[z0,z1,z10,z2,z4,z105,z6]),(0,[z0,z1,z2,z126,z4,z5,z6]),(0,[z102,z0,z127,z2,z4,z5,z6]),(0,[z128,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z129,z2,z4,z5,z6]),(0,[z130,z0,z1,z2,z4,z5,z6]),(0,[z131,z109,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z132,z5,z6]),(0,[z0,z1,z2,z133,z4,z5,z6])],[(0,[z0,z1,z2,z4,z134,z5,z6]),(0,[z102,z0,z135,z2,z4,z5,z6]),(0,[z88,z0,z1,z136,z4,z5,z6])],[(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z137,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z138,z5,z6]),(0,[z139,z0,z1,z2,z4,z5,z6]),(0,[z0,z140,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z141])],[(0,[z142,z0,z1,z2,z4,z5,z6]),(1,[z0,z143,z2,z4,z5,z6]),(0,[z8,z0,z1,z2,z4,z144,z6]),(0,[z145,z0,z1,z2,z4,z5,z6]),(0,[z146,z0,z1,z2,z4,z5,z6]),(0,[z78,z0,z1,z2,z4,z147,z6]),(0,[z0,z1,z2,z4,z148,z5,z6]),(0,[z0,z1,z2,z4,z41,z149,z6])],[(0,[z150,z0,z1,z2,z4,z5,z6]),(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z152,z5,z6]),(0,[z153,z0,z1,z46,z4,z5,z6]),(1,[z0,z1,z2,z154,z5,z6]),(0,[z155,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z156,z5,z6]),(1,[z0,z2,z4,z157,z5,z6]),(0,[z0,z1,z2,z4,z158,z5,z6]),(0,[z0,z1,z2,z159,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z160]),(0,[z0,z1,z2,z4,z5,z6,z161]),(1,[z0,z1,z2,z4,z162,z6]),(0,[z0,z1,z2,z4,z5,z6,z163])]],
   [[(0,[z164,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z165,z6]),(0,[z0,z1,z166,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z167,z6])],[(0,[z98,z1,z17,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z5,z41,z6])],[(0,[z0,z1,z168,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z90,z6]),(0,[z169,z0,z1,z2,z4,z5,z6]),(1,[z78,z0,z2,z31,z5,z6]),(0,[z0,z1,z2,z4,z6,z42,z11]),(1,[z114,z102,z0,z1,z5,z6]),(0,[z170,z0,z1,z2,z4,z5,z6]),(0,[z0,z171,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z44,z6]),(0,[z172,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z173,z5,z6]),(0,[z98,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z105,z174]),(0,[z175,z0,z1,z2,z4,z5,z6]),(0,[z40,z0,z38,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z176]),(0,[z0,z1,z2,z4,z5,z6,z177]),(0,[z178,z0,z1,z2,z179,z5,z6])],[(0,[z0,z1,z2,z4,z180,z5,z6]),(0,[z0,z1,z2,z4,z5,z181,z6]),(0,[z0,z1,z2,z4,z5,z182,z6]),(0,[z183,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z184,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z185])],[(0,[z109,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z10,z2,z4,z186,z6]),(0,[z102,z0,z1,z2,z5,z6,z61]),(0,[z79,z0,z1,z2,z4,z29,z6]),(0,[z88,z0,z1,z2,z4,z187,z6]),(0,[z0,z1,z188,z2,z4,z5,z6])],[(0,[z66,z0,z1,z4,z121,z5,z6]),(0,[z0,z1,z189,z2,z4,z5,z6]),(0,[z0,z1,z75,z2,z4,z80,z6]),(0,[z0,z1,z2,z5,z106,z6,z61])],[(0,[z190,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z191,z4,z5,z6]),(0,[z0,z1,z4,z186,z5,z6,z174]),(0,[z114,z0,z1,z4,z5,z6,z174]),(0,[z0,z1,z2,z4,z4,z41,z6]),(0,[z0,z51,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z187,z5,z6])]],
   [[(0,[z8,z0,z1,z192,z4,z5,z6]),(0,[z8,z0,z1,z2,z4,z41,z6]),(0,[z0,z193,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z123,z5,z6]),(0,[z0,z1,z194,z2,z4,z5,z6])],[(0,[z131,z0,z1,z2,z4,z28,z6]),(0,[z0,z1,z2,z4,z121,z5,z6]),(0,[z0,z1,z2,z195,z4,z5,z6])],[(0,[z45,z98,z1,z2,z4,z5,z6]),(0,[z32,z0,z38,z2,z4,z5,z6]),(0,[z0,z1,z196,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z197,z6]),(0,[z0,z1,z2,z4,z5,z106,z6])],[(0,[z0,z1,z2,z4,z5,z198,z6]),(0,[z199,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z200,z2,z4,z6,z174]),(0,[z178,z0,z1,z2,z4,z6,z55])],[(0,[z0,z1,z2,z186,z65,z5,z6]),(0,[z0,z2,z4,z121,z5,z6,z11]),(0,[z0,z1,z201,z2,z4,z5,z6]),(1,[z171,z1,z2,z4,z5,z6])],[(1,[z0,z1,z89,z4,z5,z6]),(0,[z202,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z105,z61]),(0,[z203,z0,z1,z2,z4,z5,z6]),(0,[z204,z0,z1,z2,z4,z5,z6]),(0,[z205,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z206,z5,z6]),(0,[z207,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z208,z5,z6]),(0,[z1,z2,z36,z4,z65,z5,z6]),(0,[z82,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z209,z6]),(0,[z0,z1,z2,z4,z5,z118,z6]),(0,[z0,z1,z27,z210,z2,z4,z6])]],
   [[(0,[z0,z1,z211,z2,z4,z5,z6]),(0,[z14,z1,z2,z4,z5,z6,z60]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z213,z5,z6]),(0,[z0,z1,z210,z2,z4,z5,z6]),(0,[z214,z0,z1,z2,z4,z5,z6])],[(1,[z88,z0,z1,z2,z5,z61])],[(0,[z0,z1,z2,z4,z5,z6,z215]),(1,[z9,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z28,z41,z6]),(0,[z0,z1,z2,z4,z216,z5,z6]),(0,[z0,z1,z10,z2,z43,z4,z6])],[(1,[z0,z1,z217,z4,z5,z6]),(0,[z0,z38,z1,z2,z4,z5,z6]),(0,[z0,z38,z1,z2,z4,z5,z95]),(0,[z178,z0,z1,z218,z4,z5,z6])],[(0,[z14,z0,z38,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z219,z6]),(0,[z0,z38,z2,z4,z121,z5,z6]),(0,[z0,z1,z2,z4,z5,z220,z6]),(0,[z0,z122,z1,z2,z4,z80,z6]),(0,[z0,z1,z2,z4,z29,z41,z6]),(0,[z79,z0,z1,z4,z5,z6,z174]),(0,[z88,z0,z1,z2,z4,z221,z6])],[(0,[z66,z0,z1,z4,z186,z5,z6]),(0,[z114,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z222,z5,z6]),(0,[z0,z1,z2,z4,z52,z41,z6]),(0,[z0,z1,z10,z2,z4,z106,z6]),(1,[z100,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z223,z5,z6]),(0,[z0,z1,z2,z224,z4,z5,z6]),(0,[z0,z225,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z41,z6]),(0,[z0,z39,z1,z83,z4,z5,z6]),(0,[z0,z226,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z227]),(0,[z0,z1,z2,z4,z5,z6,z228]),(0,[z229,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z230])]],
   [[(0,[z0,z1,z4,z186,z97,z5,z6]),(0,[z114,z0,z1,z4,z97,z5,z6]),(0,[z0,z1,z2,z4,z5,z231,z6]),(0,[z8,z0,z1,z232,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z46,z4,z41,z6]),(0,[z32,z0,z1,z2,z4,z118,z6]),(0,[z0,z1,z2,z4,z5,z6,z233]),(0,[z79,z0,z1,z71,z2,z4,z6]),(1,[z0,z1,z10,z2,z4,z6]),(0,[z234,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z235,z2,z43,z4,z6])],[(0,[z0,z1,z2,z46,z36,z5,z6]),(0,[z66,z0,z1,z2,z4,z5,z6]),(0,[z236,z0,z1,z2,z4,z5,z6]),(0,[z102,z0,z1,z2,z43,z5,z6]),(0,[z0,z1,z2,z43,z4,z5,z6]),(0,[z237,z0,z1,z2,z4,z5,z6])],[(0,[z238,z0,z1,z2,z4,z5,z6]),(0,[z66,z0,z2,z4,z121,z5,z6]),(0,[z0,z1,z239,z2,z4,z5,z6]),(0,[z0,z38,z2,z4,z5,z118,z6]),(0,[z0,z1,z10,z2,z4,z118,z6]),(0,[z0,z1,z2,z4,z41,z6,z11]),(0,[z0,z240,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z241,z6]),(0,[z242,z0,z1,z2,z4,z5,z6])],[(0,[z243,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z244]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z245]),(0,[z246,z0,z1,z2,z4,z5,z6]),(0,[z247,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z62,z2,z4,z41,z6])],[(0,[z248,z0,z1,z2,z4,z5,z6]),(0,[z45,z0,z1,z2,z4,z5,z6]),(0,[z45,z1,z2,z4,z5,z105,z6]),(0,[z0,z1,z249,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z250])],[(0,[z251,z0,z1,z2,z4,z5,z6]),(0,[z98,z1,z2,z4,z5,z6,z60]),(0,[z0,z1,z252,z2,z4,z5,z6])],[(0,[z253,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z105,z6,z254]),(0,[z0,z1,z2,z4,z5,z6,z255]),(0,[z0,z1,z2,z186,z5,z6,z61]),(0,[z0,z1,z75,z2,z4,z29,z6]),(0,[z256,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z0,z1,z257,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z258,z5,z6]),(0,[z0,z1,z2,z4,z5,z259,z6]),(0,[z260,z0,z1,z2,z4,z5,z6]),(1,[z225,z1,z2,z4,z5,z6])],[(0,[z34,z0,z38,z2,z4,z5,z6]),(0,[z261,z0,z1,z2,z4,z5,z6]),(0,[z109,z1,z2,z4,z5,z28,z6]),(0,[z0,z1,z262,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z72,z118,z6]),(0,[z0,z1,z2,z4,z41,z6,z55]),(0,[z0,z263,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z264,z6]),(0,[z79,z0,z1,z62,z4,z5,z6]),(1,[z0,z1,z265,z4,z5,z6])],[(0,[z0,z1,z2,z4,z266,z5,z6]),(0,[z0,z1,z267,z2,z4,z5,z6]),(1,[z146,z0,z1,z2,z5,z6]),(1,[z0,z1,z2,z4,z147,z6])],[(0,[z16,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z4,z5,z268,z6]),(0,[z0,z1,z10,z210,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z269,z6]),(0,[z0,z1,z2,z4,z5,z6,z270]),(0,[z0,z1,z2,z4,z41,z6,z271]),(0,[z0,z1,z2,z4,z272,z5,z6])],[(1,[z0,z1,z2,z4,z273,z6]),(1,[z0,z1,z2,z4,z5,z274]),(0,[z0,z1,z2,z4,z5,z274,z6]),(0,[z0,z275,z1,z2,z4,z5,z6]),(0,[z0,z30,z38,z2,z4,z5,z6]),(0,[z276,z0,z1,z2,z4,z5,z6]),(1,[z277,z1,z2,z4,z5,z6])],[(0,[z278,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z279,z2,z4,z5,z6])],[(0,[z9,z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z280]),(0,[z114,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z281,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z282,z6]),(0,[z0,z283,z1,z2,z4,z5,z6]),(0,[z78,z102,z0,z1,z2,z5,z6]),(0,[z0,z1,z62,z4,z186,z5,z6]),(0,[z284,z0,z1,z2,z4,z5,z6])],[(0,[z78,z0,z1,z2,z4,z285,z6]),(0,[z286,z0,z1,z2,z4,z5,z6]),(0,[z0,z122,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z287])],[(1,[z0,z1,z192,z4,z5,z6]),(0,[z288,z0,z1,z2,z4,z5,z6]),(1,[z32,z0,z2,z4,z33,z6]),(0,[z40,z0,z1,z2,z4,z5,z11]),(0,[z0,z1,z71,z2,z4,z41,z6])],[(0,[z0,z1,z289,z2,z46,z4,z6]),(0,[z102,z0,z1,z210,z2,z5,z6]),(0,[z12,z0,z1,z2,z4,z290,z6]),(0,[z0,z1,z10,z62,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z106,z60])],[(0,[z66,z34,z0,z2,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z59]),(0,[z45,z1,z2,z4,z97,z5,z6]),(0,[z9,z1,z2,z36,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z72,z6]),(0,[z291,z0,z1,z2,z4,z5,z6]),(0,[z0,z122,z1,z2,z4,z29,z6]),(0,[z0,z1,z10,z194,z2,z4,z6]),(0,[z0,z1,z201,z10,z2,z4,z6])],[(0,[z292,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z293,z5,z6]),(0,[z8,z0,z252,z2,z4,z5,z6]),(0,[z0,z1,z2,z294,z4,z5,z6])],[(0,[z0,z1,z2,z4,z295,z5,z6]),(0,[z16,z0,z70,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z296,z5,z6]),(1,[z0,z1,z2,z4,z297,z6]),(0,[z0,z1,z2,z4,z5,z6,z174]),(0,[z0,z1,z2,z4,z41,z68,z6]),(0,[z117,z0,z1,z10,z2,z4,z6])]],
   [[(0,[z1,z2,z4,z97,z5,z6,z60]),(0,[z0,z143,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z105,z6]),(0,[z298,z0,z1,z2,z4,z5,z6]),(0,[z299,z0,z1,z2,z4,z5,z6]),(0,[z0,z122,z1,z2,z154,z5,z6]),(0,[z300,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z301])],[(0,[z130,z0,z2,z4,z97,z5,z6]),(0,[z302,z0,z1,z2,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z5,z174])],[(1,[z0,z1,z2,z208,z5,z6]),(0,[z45,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z105,z6]),(1,[z0,z1,z303,z2,z4,z6]),(0,[z0,z304,z1,z2,z4,z5,z6]),(0,[z305,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z80,z6,z55])],[(0,[z306,z0,z1,z2,z4,z5,z6]),(0,[z98,z0,z1,z17,z4,z5,z6]),(1,[z0,z1,z307,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z308]),(0,[z0,z1,z2,z4,z309,z5,z6]),(0,[z164,z0,z1,z2,z4,z41,z6])],[(0,[z310,z0,z1,z2,z4,z5,z6]),(0,[z66,z0,z30,z2,z4,z5,z6]),(0,[z0,z38,z1,z10,z2,z4,z6]),(0,[z311,z0,z1,z2,z4,z5,z6])],[(0,[z312,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z313,z5,z6]),(0,[z0,z1,z2,z4,z314,z5,z6]),(0,[z153,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z315,z6]),(0,[z0,z1,z71,z2,z4,z52,z6]),(0,[z0,z1,z2,z4,z5,z6,z316])],[(0,[z9,z0,z1,z2,z4,z5,z6]),(0,[z0,z83,z2,z4,z31,z5,z6]),(0,[z317,z0,z1,z2,z4,z5,z6]),(1,[z74,z0,z1,z2,z5,z6]),(1,[z117,z0,z1,z10,z2,z6]),(0,[z0,z1,z10,z318,z2,z4,z6]),(0,[z178,z0,z1,z2,z319,z5,z6])],[(0,[z117,z0,z1,z320,z2,z5,z6]),(0,[z88,z0,z1,z2,z4,z5,z106])]],
   [[(0,[z321,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z322,z2,z4,z5,z6]),(0,[z131,z45,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z105,z99]),(0,[z0,z1,z2,z217,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z323]),(0,[z114,z0,z1,z2,z186,z5,z6]),(0,[z0,z1,z2,z4,z324,z41,z6])],[(0,[z14,z0,z1,z211,z4,z5,z6]),(0,[z0,z1,z325,z2,z4,z5,z6]),(0,[z131,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z326]),(0,[z0,z1,z2,z4,z5,z290,z6]),(0,[z234,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z43,z4,z5,z61]),(0,[z0,z1,z2,z4,z5,z6,z61]),(0,[z178,z327,z1,z2,z4,z5,z6])],[(1,[z0,z1,z232,z4,z5,z6]),(0,[z66,z0,z1,z10,z2,z4,z6]),(0,[z328,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z303,z83,z2,z4,z6]),(0,[z0,z1,z10,z2,z4,z6,z174]),(0,[z0,z1,z10,z329,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z330])],[(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z72,z5,z6])],[(0,[z331,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z28,z6]),(0,[z0,z1,z2,z4,z121,z41,z6]),(0,[z0,z1,z2,z4,z179,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z332]),(0,[z0,z1,z333,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z85,z6]),(0,[z0,z122,z1,z2,z4,z33,z6]),(0,[z334,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z335,z41,z6]),(0,[z0,z1,z196,z2,z4,z41,z6])],[(0,[z336,z0,z1,z2,z4,z5,z6]),(0,[z0,z337,z2,z4,z31,z5,z6]),(0,[z0,z1,z338,z2,z4,z5,z6]),(0,[z0,z1,z2,z339,z4,z5,z6]),(0,[z45,z0,z1,z2,z4,z340,z6]),(0,[z45,z0,z1,z10,z2,z4,z6]),(1,[z0,z1,z200,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z324,z6])],[(0,[z45,z0,z1,z2,z4,z5,z60]),(0,[z0,z1,z2,z4,z5,z341,z6]),(0,[z251,z0,z1,z10,z2,z4,z6]),(0,[z88,z0,z1,z166,z4,z5,z6])]],
   [[(0,[z0,z1,z337,z2,z4,z5,z6]),(0,[z342,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z97,z5,z6]),(0,[z343,z0,z1,z2,z4,z5,z6]),(0,[z344,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z345,z5,z6]),(0,[z346,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z347,z6]),(0,[z0,z348,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z5,z41,z6])],[(0,[z0,z1,z210,z2,z4,z41,z6])],[(0,[z0,z349,z1,z2,z4,z5,z6]),(0,[z8,z117,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z350,z6]),(0,[z0,z1,z351,z2,z4,z5,z6]),(0,[z12,z225,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z6,z61])],[(0,[z0,z35,z1,z2,z4,z5,z6]),(0,[z0,z1,z232,z2,z4,z5,z6]),(0,[z0,z352,z1,z2,z4,z5,z6]),(0,[z0,z1,z46,z217,z4,z5,z6]),(0,[z0,z1,z265,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z353,z6]),(0,[z0,z35,z2,z4,z121,z5,z6]),(1,[z0,z1,z2,z266,z5,z6]),(0,[z354,z0,z1,z2,z4,z5,z6]),(0,[z355,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z33,z28,z6]),(0,[z0,z1,z10,z2,z4,z6,z60]),(0,[z0,z38,z1,z2,z4,z41,z6]),(0,[z0,z1,z10,z75,z2,z4,z6]),(1,[z12,z0,z1,z4,z5,z174])],[(0,[z0,z1,z2,z4,z5,z356,z6]),(0,[z0,z1,z10,z2,z4,z28,z6]),(0,[z78,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z357,z6]),(0,[z358,z0,z1,z2,z4,z5,z6]),(0,[z88,z171,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z359,z5,z6]),(0,[z0,z1,z2,z4,z360,z5,z6]),(1,[z153,z0,z1,z4,z5,z6]),(0,[z0,z120,z1,z2,z4,z5,z6]),(0,[z0,z1,z210,z2,z4,z297,z6]),(0,[z0,z1,z2,z4,z361,z5,z6]),(0,[z0,z1,z200,z2,z4,z5,z6])],[(0,[z362,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z363,z2,z4,z5,z6]),(0,[z0,z1,z364,z2,z4,z5,z6])],[(0,[z0,z365,z1,z2,z4,z5,z6]),(0,[z0,z122,z1,z10,z2,z4,z6]),(0,[z0,z1,z366,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z367,z5,z6])],[(0,[z0,z1,z10,z83,z2,z4,z6]),(0,[z0,z1,z2,z4,z368,z5,z6]),(0,[z114,z102,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z369])],[(0,[z14,z0,z2,z4,z5,z6,z11]),(0,[z0,z1,z2,z4,z340,z5,z6]),(0,[z66,z0,z1,z2,z4,z41,z6]),(0,[z370,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z43,z4,z41,z6])],[(0,[z0,z1,z2,z4,z5,z6,z371]),(0,[z0,z1,z372,z2,z4,z5,z6]),(0,[z373,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z374,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z375])],[(0,[z0,z1,z2,z4,z5,z6,z59]),(0,[z0,z1,z17,z4,z121,z5,z6]),(1,[z242,z1,z2,z4,z5,z6]),(0,[z0,z1,z75,z2,z4,z41,z6]),(0,[z376,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z221,z6])],[(0,[z0,z1,z2,z192,z4,z5,z6]),(1,[z0,z1,z2,z4,z285,z6]),(0,[z0,z1,z210,z4,z186,z5,z6]),(0,[z0,z1,z2,z4,z5,z377,z6]),(0,[z0,z1,z2,z378,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z106,z6]),(0,[z0,z1,z2,z43,z5,z106,z6]),(1,[z178,z0,z1,z2,z4,z55])]],
   [[(1,[z0,z252,z2,z4,z5,z6]),(0,[z45,z0,z1,z2,z4,z41,z6]),(0,[z0,z283,z2,z4,z5,z105,z6]),(0,[z379,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z10,z2,z5,z6]),(0,[z88,z0,z304,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z65,z5,z6]),(0,[z0,z1,z380,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z121,z6]),(0,[z0,z2,z4,z31,z5,z6,z11]),(0,[z381,z0,z1,z2,z4,z5,z6]),(0,[z114,z0,z1,z210,z4,z5,z6]),(0,[z0,z1,z2,z4,z29,z6,z55]),(0,[z251,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z218,z4,z5,z6])],[(0,[z14,z0,z1,z89,z4,z5,z6]),(0,[z0,z1,z2,z382,z4,z5,z6]),(0,[z383,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z384,z2,z4,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z82,z0,z1,z2,z4,z5,z60]),(0,[z0,z1,z2,z4,z5,z6,z385]),(0,[z0,z1,z2,z386,z4,z5,z6]),(0,[z387,z0,z1,z2,z4,z5,z6]),(0,[z388,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z320,z2,z41,z6])],[(0,[z0,z1,z83,z4,z97,z5,z6]),(0,[z0,z1,z10,z2,z4,z95,z6]),(0,[z0,z1,z210,z2,z186,z5,z6]),(0,[z0,z1,z2,z389,z4,z5,z6])],[(0,[z0,z1,z390,z2,z4,z5,z6]),(0,[z0,z1,z2,z391,z4,z5,z6])],[(0,[z45,z1,z2,z4,z65,z5,z6]),(0,[z0,z1,z392,z2,z4,z5,z6]),(1,[z66,z0,z4,z121,z5,z6]),(0,[z0,z1,z2,z4,z5,z393,z6]),(0,[z0,z1,z10,z2,z4,z4,z6]),(0,[z0,z1,z394,z2,z4,z5,z6])],[(0,[z9,z0,z1,z10,z2,z4,z6]),(0,[z395,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z396]),(0,[z78,z0,z1,z2,z186,z5,z6]),(0,[z114,z0,z1,z62,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z397]),(0,[z0,z1,z2,z4,z398,z5,z6]),(1,[z0,z279,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z15]),(0,[z399,z0,z1,z2,z4,z5,z6]),(0,[z400,z0,z1,z2,z4,z5,z6])],[(0,[z131,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z401])],[(1,[z14,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z402,z5,z6]),(0,[z0,z1,z2,z4,z403,z5,z6]),(1,[z0,z1,z2,z4,z340,z6]),(0,[z0,z1,z2,z404,z4,z5,z6]),(0,[z0,z1,z2,z4,z186,z5,z6])],[(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z16,z0,z1,z10,z2,z4,z6]),(0,[z8,z0,z1,z2,z4,z5,z406]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z407,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z408,z2,z4,z5,z6]),(0,[z0,z122,z1,z2,z4,z41,z6]),(0,[z0,z1,z409,z2,z4,z5,z6]),(0,[z178,z32,z0,z1,z2,z4,z6]),(0,[z0,z410,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z411,z6]),(0,[z412,z0,z1,z2,z4,z5,z6]),(0,[z0,z30,z2,z4,z5,z6,z11]),(0,[z102,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z43,z186,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z413])],[(0,[z0,z1,z2,z4,z414,z5,z6]),(0,[z415,z0,z1,z2,z4,z5,z6]),(0,[z416,z0,z1,z2,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z178,z0,z1,z2,z4,z5,z55])],[(0,[z16,z0,z1,z2,z4,z241,z6]),(0,[z0,z1,z2,z4,z5,z417,z6]),(0,[z0,z1,z2,z4,z5,z6,z418]),(0,[z0,z1,z2,z4,z5,z419,z6]),(0,[z420,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z421,z5,z6]),(0,[z0,z1,z10,z2,z4,z99,z6]),(0,[z0,z1,z2,z4,z5,z6,z422]),(1,[z0,z1,z2,z179,z5,z6])]],
   [[(0,[z0,z39,z2,z4,z5,z6,z11]),(0,[z423,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z127,z2,z4,z5,z6])],[(0,[z0,z1,z337,z10,z2,z4,z6]),(0,[z0,z1,z17,z2,z4,z5,z6]),(0,[z8,z0,z1,z2,z4,z5,z57])],[(0,[z35,z1,z337,z2,z4,z5,z6]),(0,[z0,z1,z424,z2,z4,z5,z6]),(0,[z0,z425,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z144,z6]),(0,[z0,z1,z2,z4,z426,z5,z6]),(0,[z32,z0,z122,z2,z4,z5,z6]),(0,[z0,z1,z27,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z80,z6]),(0,[z0,z1,z2,z4,z52,z5,z55])],[(0,[z0,z1,z2,z4,z427,z5,z6]),(0,[z0,z1,z83,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z428,z5,z6]),(0,[z0,z1,z2,z4,z429,z5,z6]),(0,[z0,z1,z4,z5,z99,z6,z174]),(1,[z0,z1,z62,z4,z5,z99])],[(0,[z82,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z123,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z430,z6]),(0,[z0,z1,z62,z4,z5,z99,z6]),(1,[z0,z1,z2,z4,z52,z80]),(0,[z0,z431,z1,z2,z4,z5,z6])],[(0,[z0,z1,z432,z2,z4,z5,z6]),(1,[z8,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z433,z5,z6]),(0,[z117,z102,z0,z1,z2,z5,z6])],[(0,[z0,z434,z1,z2,z4,z5,z6]),(0,[z0,z35,z1,z10,z2,z4,z6]),(0,[z0,z1,z435,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z95,z105]),(0,[z0,z1,z303,z2,z4,z5,z6]),(0,[z0,z1,z436,z2,z4,z5,z6]),(0,[z12,z0,z1,z2,z4,z162,z6]),(0,[z12,z0,z1,z2,z4,z5,z99]),(0,[z0,z437,z1,z2,z4,z5,z6]),(0,[z0,z1,z320,z2,z5,z41,z6]),(0,[z0,z438,z1,z2,z4,z5,z6])],[(0,[z0,z1,z439,z2,z4,z5,z6]),(0,[z0,z1,z2,z440,z4,z5,z6]),(0,[z78,z0,z1,z2,z31,z5,z6]),(0,[z0,z1,z441,z2,z4,z5,z6]),(0,[z0,z1,z71,z2,z4,z6,z55])]],
   [[(1,[z0,z1,z2,z4,z73,z6])],[(0,[z16,z0,z1,z2,z4,z5,z274]),(0,[z0,z442,z1,z2,z4,z5,z6]),(0,[z0,z1,z443,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z65,z5,z6]),(0,[z9,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z72,z80,z6]),(0,[z0,z1,z2,z4,z444,z5,z6])],[(0,[z8,z0,z1,z2,z65,z5,z6]),(0,[z0,z1,z2,z4,z445,z5,z6]),(0,[z0,z1,z2,z4,z33,z72,z6]),(0,[z0,z1,z2,z4,z31,z5,z6]),(0,[z178,z0,z1,z75,z2,z4,z6])],[(1,[z34,z35,z2,z4,z5,z6]),(0,[z16,z98,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z186,z5,z6]),(0,[z178,z0,z1,z2,z4,z28,z6]),(0,[z0,z1,z10,z2,z4,z72,z6]),(0,[z0,z1,z2,z4,z5,z446,z6]),(0,[z102,z0,z1,z2,z5,z41,z6])],[(0,[z16,z0,z1,z2,z4,z282,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z45,z1,z2,z4,z5,z28,z6]),(0,[z447,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z10,z2,z41,z6])],[(0,[z14,z0,z1,z2,z4,z5,z44]),(0,[z0,z1,z448,z2,z4,z5,z6]),(0,[z0,z1,z10,z17,z2,z4,z6]),(0,[z0,z30,z2,z46,z4,z5,z6]),(0,[z178,z0,z122,z1,z2,z4,z6]),(0,[z0,z1,z449,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z41,z6])],[(0,[z0,z1,z2,z4,z5,z450,z6]),(0,[z0,z1,z2,z4,z282,z5,z6]),(0,[z40,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z451,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z452,z5,z6]),(0,[z0,z2,z4,z5,z95,z6,z11]),(1,[z0,z1,z2,z4,z6,z42]),(0,[z0,z1,z75,z4,z5,z29,z6]),(0,[z453,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z218,z4,z5,z6])]],
   [[(0,[z454,z0,z1,z2,z4,z5,z6]),(0,[z455,z0,z1,z2,z4,z5,z6]),(0,[z456,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z457,z2,z4,z5,z6]),(0,[z458,z0,z1,z2,z4,z5,z6]),(0,[z78,z0,z1,z2,z46,z5,z6]),(0,[z0,z459,z1,z2,z4,z5,z6]),(0,[z12,z0,z1,z4,z5,z6,z174])],[(0,[z460,z0,z1,z2,z4,z5,z6])],[(0,[z14,z0,z35,z2,z4,z5,z6]),(0,[z0,z1,z337,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z461]),(0,[z0,z1,z2,z4,z97,z41,z6]),(0,[z0,z1,z2,z72,z132,z5,z6]),(0,[z0,z122,z2,z4,z5,z118,z6]),(0,[z0,z1,z2,z4,z5,z6,z462])],[(0,[z0,z1,z64,z2,z4,z5,z6]),(0,[z0,z1,z463,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z464]),(0,[z0,z1,z2,z4,z41,z6,z174]),(0,[z0,z465,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z466]),(0,[z178,z0,z1,z2,z4,z5,z105]),(0,[z0,z38,z2,z4,z31,z5,z6]),(0,[z32,z0,z1,z2,z4,z5,z6]),(0,[z0,z348,z1,z2,z4,z41,z6]),(0,[z88,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z43,z5,z106])],[(0,[z0,z1,z2,z4,z5,z467,z6]),(0,[z0,z468,z1,z2,z4,z5,z6]),(0,[z78,z0,z2,z4,z31,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z469]),(0,[z0,z1,z2,z4,z33,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z470])],[(0,[z471,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z90,z6]),(0,[z0,z1,z10,z2,z4,z5,z6]),(0,[z0,z1,z472,z2,z4,z5,z6])]],
   [[(0,[z0,z35,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z473])],[(0,[z0,z1,z307,z2,z4,z5,z6]),(0,[z474,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z52,z5,z105]),(0,[z0,z1,z475,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z476]),(0,[z0,z1,z477,z2,z4,z5,z6]),(0,[z0,z1,z478,z2,z4,z5,z6])],[(0,[z0,z1,z2,z46,z65,z5,z6]),(0,[z0,z1,z2,z36,z31,z5,z6]),(0,[z0,z1,z2,z4,z479,z5,z6]),(0,[z0,z1,z480,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z481,z6])],[(0,[z0,z1,z2,z4,z5,z482,z6]),(0,[z66,z0,z2,z4,z31,z5,z6]),(0,[z0,z1,z2,z4,z5,z483,z6]),(0,[z0,z1,z2,z4,z5,z484,z6]),(0,[z0,z1,z10,z2,z4,z29,z6]),(0,[z0,z1,z485,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z486,z5,z6]),(0,[z0,z487,z1,z2,z4,z5,z6]),(1,[z0,z1,z136,z4,z5,z6])],[(0,[z0,z1,z2,z4,z147,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z488]),(0,[z178,z79,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z367,z41,z6]),(0,[z489,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z235,z2,z4,z5,z6]),(0,[z490,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z491,z2,z4,z5,z6])],[(0,[z14,z45,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z406]),(0,[z0,z1,z2,z4,z5,z6,z60]),(0,[z102,z0,z30,z1,z2,z5,z6]),(0,[z40,z0,z2,z4,z5,z6,z11]),(0,[z102,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z41,z6,z61])],[(0,[z14,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z492,z5,z6]),(0,[z82,z1,z2,z4,z5,z6,z60]),(0,[z0,z1,z2,z4,z5,z493,z6]),(0,[z12,z0,z1,z62,z4,z5,z6]),(0,[z12,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z10,z320,z2,z4,z6]),(0,[z277,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z34,z0,z35,z2,z4,z5,z6]),(0,[z494,z0,z1,z2,z4,z5,z6]),(0,[z0,z39,z1,z4,z121,z5,z6]),(0,[z495,z0,z1,z2,z4,z5,z6]),(0,[z0,z496,z1,z2,z4,z5,z6]),(0,[z79,z0,z1,z75,z4,z5,z6]),(0,[z0,z1,z62,z4,z5,z29,z6])],[(0,[z0,z1,z2,z4,z497,z5,z6]),(0,[z0,z1,z498,z2,z4,z5,z6]),(0,[z178,z0,z465,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z28,z118,z6]),(0,[z0,z1,z2,z4,z72,z29,z6]),(0,[z0,z1,z2,z4,z499,z5,z6])],[(1,[z0,z1,z2,z4,z5,z57]),(1,[z82,z1,z2,z4,z5,z60]),(0,[z0,z122,z1,z71,z2,z4,z6]),(0,[z0,z1,z2,z500,z4,z5,z6]),(0,[z0,z1,z2,z4,z501,z5,z6])],[(0,[z0,z30,z35,z2,z4,z5,z6]),(0,[z0,z502,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z4,z41,z6])],[(0,[z0,z1,z2,z4,z5,z60,z11]),(0,[z0,z1,z2,z4,z5,z503,z6]),(0,[z32,z0,z2,z4,z5,z6,z11]),(0,[z0,z1,z2,z186,z5,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z504]),(0,[z178,z0,z21,z2,z4,z5,z6])],[(0,[z505,z0,z1,z2,z4,z5,z6])],[(0,[z0,z39,z35,z2,z4,z5,z6]),(1,[z109,z1,z2,z4,z28,z6]),(1,[z0,z122,z2,z4,z118,z6]),(1,[z0,z1,z2,z4,z187,z6]),(0,[z0,z1,z2,z4,z5,z6,z506]),(0,[z178,z0,z1,z2,z4,z5,z80])]],
   [[(0,[z9,z0,z1,z2,z65,z5,z6]),(0,[z0,z1,z2,z65,z31,z5,z6]),(1,[z0,z1,z289,z2,z4,z6])],[(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z32,z0,z1,z2,z4,z33,z6]),(0,[z0,z1,z2,z4,z5,z508,z6])],[(0,[z16,z0,z1,z2,z266,z5,z6]),(0,[z0,z1,z10,z2,z36,z4,z6]),(0,[z0,z509,z1,z2,z4,z5,z6]),(0,[z0,z510,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z511,z6]),(0,[z0,z512,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z513,z6]),(0,[z0,z1,z2,z4,z514,z5,z6]),(0,[z0,z1,z10,z2,z4,z33,z6]),(0,[z515,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z516,z5,z6]),(0,[z0,z1,z2,z4,z517,z5,z6]),(1,[z0,z1,z2,z4,z167,z6]),(0,[z518,z0,z1,z2,z4,z5,z6])],[(0,[z34,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z519,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z520]),(0,[z521,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z307,z2,z36,z4,z6]),(0,[z522,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z523]),(0,[z0,z1,z2,z4,z5,z95,z6]),(0,[z0,z38,z1,z2,z4,z5,z11]),(0,[z0,z1,z2,z4,z41,z356,z6]),(0,[z284,z0,z1,z10,z2,z4,z6])],[(0,[z8,z0,z1,z2,z4,z223,z6]),(0,[z524,z0,z1,z2,z4,z5,z6])],[(0,[z16,z1,z2,z4,z97,z5,z6]),(0,[z0,z1,z2,z4,z525,z5,z6]),(0,[z0,z1,z526,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z41,z95,z6]),(0,[z0,z1,z2,z4,z186,z41,z6]),(0,[z0,z1,z2,z4,z5,z527,z6]),(0,[z0,z1,z71,z4,z5,z29,z6]),(1,[z0,z1,z2,z4,z6,z176])],[(0,[z14,z1,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z528,z6]),(0,[z178,z0,z1,z2,z4,z72,z6]),(1,[z0,z39,z83,z4,z5,z6]),(0,[z529,z0,z1,z2,z4,z5,z6]),(0,[z40,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z530,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z241,z6]),(0,[z0,z1,z2,z4,z531,z5,z6]),(1,[z0,z1,z2,z4,z5,z411]),(0,[z0,z30,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z96]),(0,[z102,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z532,z6])],[(0,[z0,z1,z533,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z534,z6]),(0,[z0,z1,z2,z4,z535,z5,z6]),(0,[z102,z0,z1,z2,z36,z5,z6]),(0,[z12,z0,z1,z2,z4,z41,z6])],[(0,[z0,z1,z2,z4,z5,z536,z6]),(0,[z0,z1,z2,z4,z537,z5,z6]),(1,[z0,z127,z2,z4,z5,z6]),(0,[z538,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z319,z5,z6])],[(0,[z0,z1,z83,z17,z4,z5,z6]),(0,[z0,z39,z1,z2,z4,z5,z6]),(0,[z0,z1,z83,z2,z479,z5,z6]),(0,[z539,z0,z1,z83,z2,z5,z6]),(0,[z540,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z541,z6]),(0,[z0,z1,z2,z4,z5,z6,z542]),(0,[z88,z100,z1,z2,z4,z5,z6])],[(0,[z0,z70,z1,z2,z4,z5,z6]),(0,[z0,z1,z17,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z543]),(1,[z0,z135,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z544]),(0,[z1,z2,z4,z65,z5,z6,z60]),(0,[z0,z1,z83,z2,z4,z220,z6]),(0,[z117,z0,z1,z2,z186,z5,z6]),(0,[z88,z0,z1,z2,z4,z5,z61])],[(0,[z0,z1,z2,z4,z545,z5,z6]),(0,[z32,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z546,z5,z6]),(0,[z0,z1,z2,z4,z547,z5,z6]),(0,[z0,z1,z2,z4,z548,z5,z6]),(0,[z260,z0,z1,z2,z4,z41,z6]),(0,[z88,z0,z1,z10,z2,z4,z6]),(1,[z0,z1,z235,z2,z4,z6])],[(1,[z16,z1,z4,z97,z5,z6]),(0,[z0,z549,z1,z2,z4,z5,z6]),(0,[z550,z0,z1,z2,z4,z5,z6]),(0,[z0,z38,z2,z4,z5,z95,z6]),(1,[z0,z410,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z99,z6])]],
   [[(0,[z551,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z552,z2,z4,z5,z6]),(0,[z0,z1,z553,z2,z4,z5,z6]),(0,[z0,z1,z87,z2,z4,z5,z6]),(0,[z0,z1,z10,z10,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z6,z554]),(0,[z555,z0,z1,z2,z4,z5,z6]),(0,[z556,z0,z1,z2,z4,z5,z6]),(0,[z0,z557,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z558,z5,z6]),(0,[z0,z1,z2,z4,z559,z5,z6]),(0,[z560,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z319,z4,z5,z6])],[(0,[z114,z0,z1,z17,z4,z5,z6]),(0,[z0,z1,z2,z4,z561,z5,z6]),(0,[z0,z1,z562,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z96]),(0,[z0,z1,z75,z2,z546,z5,z6]),(0,[z563,z0,z1,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z80,z6])],[(0,[z565,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z566,z6]),(0,[z102,z0,z1,z2,z4,z315,z6]),(0,[z0,z1,z320,z2,z4,z5,z6]),(0,[z178,z0,z1,z2,z4,z5,z6])],[(0,[z34,z0,z2,z4,z5,z6,z11]),(0,[z0,z1,z2,z4,z65,z41,z6]),(0,[z567,z0,z1,z2,z4,z5,z6]),(0,[z102,z0,z1,z4,z186,z5,z6]),(0,[z0,z1,z2,z4,z41,z80,z6])],[(0,[z0,z568,z1,z2,z4,z5,z6]),(0,[z66,z0,z1,z83,z4,z5,z6]),(0,[z114,z0,z39,z1,z4,z5,z6]),(1,[z0,z1,z2,z479,z5,z6]),(0,[z0,z1,z2,z4,z31,z41,z6])],[(0,[z0,z1,z2,z4,z5,z569,z6]),(0,[z570,z0,z1,z2,z4,z5,z6]),(0,[z539,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z571,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z572]),(0,[z573,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z220,z6]),(0,[z0,z1,z2,z4,z118,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z574]),(0,[z575,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z41,z6]),(0,[z0,z1,z2,z4,z52,z5,z6])]],
   [[(0,[z14,z0,z1,z10,z2,z4,z6]),(0,[z35,z1,z2,z4,z5,z6,z60]),(0,[z0,z1,z17,z4,z186,z5,z6]),(0,[z8,z0,z1,z2,z5,z41,z6]),(0,[z183,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z576,z6])],[(0,[z0,z1,z2,z577,z4,z5,z6]),(0,[z0,z578,z1,z2,z4,z5,z6]),(0,[z579,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z41,z6,z61]),(0,[z0,z1,z2,z136,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z580,z6]),(0,[z16,z0,z1,z4,z97,z5,z6]),(0,[z109,z0,z1,z2,z4,z28,z6]),(0,[z0,z1,z581,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z105,z6,z60]),(0,[z582,z0,z1,z2,z4,z5,z6]),(0,[z453,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z498,z10,z2,z4,z6])],[(0,[z0,z1,z2,z4,z273,z5,z6]),(0,[z0,z583,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z80,z6]),(0,[z0,z1,z2,z584,z4,z5,z6])],[(0,[z585,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z31,z5,z6]),(0,[z0,z1,z2,z4,z5,z297,z6]),(0,[z458,z0,z1,z2,z4,z41,z6])],[(0,[z0,z586,z1,z2,z4,z5,z6]),(1,[z40,z0,z2,z4,z5,z11])],[(1,[z0,z64,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z587,z6])],[(0,[z14,z0,z83,z2,z4,z5,z6]),(0,[z0,z35,z2,z4,z31,z5,z6]),(0,[z146,z0,z1,z2,z72,z5,z6]),(0,[z0,z1,z2,z588,z4,z5,z6]),(1,[z79,z0,z1,z71,z4,z6]),(1,[z0,z1,z2,z571,z5,z6]),(0,[z0,z1,z2,z4,z5,z589,z6])]],
   [[(0,[z0,z590,z1,z2,z4,z5,z6]),(0,[z591,z0,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z592,z4,z5,z6]),(0,[z88,z0,z1,z2,z4,z41,z6])],[(0,[z0,z1,z2,z4,z5,z406,z6]),(0,[z0,z1,z593,z2,z4,z5,z6]),(1,[z0,z283,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z105,z11]),(0,[z0,z1,z2,z4,z33,z41,z6]),(0,[z0,z1,z2,z4,z5,z594,z6])],[(0,[z0,z1,z2,z4,z595,z5,z6]),(0,[z0,z1,z2,z4,z5,z315,z6]),(0,[z0,z1,z10,z2,z4,z41,z6])],[(1,[z0,z1,z2,z4,z92,z6]),(0,[z596,z0,z1,z2,z4,z5,z6]),(0,[z597,z0,z1,z2,z4,z5,z6]),(0,[z598,z0,z1,z2,z4,z5,z6])],[(0,[z599,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z600]),(0,[z0,z1,z2,z4,z601,z5,z6]),(0,[z0,z1,z602,z2,z4,z5,z6]),(0,[z0,z1,z289,z2,z4,z5,z6]),(0,[z603,z0,z1,z2,z4,z5,z6])],[(0,[z14,z0,z1,z2,z4,z273,z6]),(0,[z604,z0,z1,z2,z4,z5,z6]),(0,[z34,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z605]),(0,[z0,z1,z2,z4,z606,z5,z6]),(0,[z0,z1,z607,z2,z4,z5,z6]),(0,[z0,z1,z2,z43,z4,z167,z6])],[(0,[z0,z1,z2,z4,z608,z5,z6]),(0,[z0,z1,z2,z4,z5,z95,z60]),(0,[z117,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z4,z5,z111,z6]),(0,[z0,z1,z485,z2,z4,z41,z6])],[(1,[z0,z1,z2,z4,z223,z6]),(0,[z0,z1,z2,z4,z609,z5,z6]),(0,[z131,z0,z1,z2,z4,z41,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z41,z6,z61]),(0,[z611,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z612,z1,z2,z4,z5,z6]),(0,[z0,z613,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z254]),(0,[z0,z1,z2,z4,z614,z5,z6]),(0,[z0,z2,z4,z33,z5,z118,z6])],[(1,[z0,z1,z211,z4,z5,z6]),(0,[z16,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z72,z41,z6]),(0,[z0,z30,z1,z10,z2,z4,z6]),(0,[z40,z0,z1,z2,z4,z5,z95]),(0,[z0,z120,z1,z2,z4,z6,z11]),(1,[z0,z1,z2,z186,z41,z6]),(0,[z0,z1,z2,z4,z615,z5,z6]),(0,[z0,z1,z318,z2,z4,z5,z6])],[(0,[z14,z0,z1,z2,z4,z41,z6]),(1,[z0,z30,z2,z46,z5,z6])],[(0,[z0,z1,z2,z4,z5,z616,z6]),(0,[z0,z1,z2,z4,z5,z29,z6]),(0,[z0,z1,z2,z4,z162,z5,z6]),(0,[z229,z0,z1,z2,z4,z5,z6])],[(0,[z34,z0,z83,z2,z4,z5,z6]),(0,[z0,z1,z617,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z618]),(0,[z45,z0,z1,z2,z4,z5,z105]),(0,[z0,z39,z1,z10,z2,z4,z6])],[(0,[z619,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z620,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z621,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z622]),(0,[z0,z1,z623,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z52,z6])],[(0,[z624,z0,z1,z2,z4,z5,z6]),(0,[z625,z0,z1,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z5,z6,z61])],[(0,[z14,z0,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z626,z6]),(0,[z0,z1,z2,z4,z5,z627,z6])]],
   [[(1,[z130,z0,z2,z4,z5,z6]),(0,[z66,z114,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z628,z4,z5,z6]),(0,[z0,z30,z83,z2,z4,z5,z6]),(0,[z0,z2,z46,z4,z31,z5,z6]),(0,[z0,z1,z2,z4,z5,z149,z6])],[(0,[z629,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z630,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z99,z60]),(0,[z0,z1,z10,z2,z4,z31,z6]),(0,[z0,z1,z2,z4,z5,z631,z6]),(0,[z632,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z546,z5,z6]),(1,[z0,z1,z2,z547,z5,z6])],[(0,[z14,z0,z1,z2,z208,z5,z6]),(0,[z633,z0,z1,z2,z4,z5,z6]),(0,[z242,z1,z2,z4,z5,z95,z6]),(0,[z0,z1,z2,z4,z634,z5,z6])],[(0,[z635,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z636]),(0,[z0,z39,z83,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z637]),(0,[z12,z0,z410,z2,z4,z5,z6])],[(0,[z14,z34,z1,z2,z4,z5,z6]),(0,[z32,z0,z1,z2,z4,z29,z6]),(0,[z0,z1,z638,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z639,z5,z6]),(0,[z640,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z641,z4,z5,z6]),(0,[z0,z135,z1,z2,z4,z5,z6]),(1,[z13,z1,z2,z4,z5,z6]),(0,[z0,z1,z62,z2,z4,z5,z174]),(0,[z178,z0,z1,z10,z2,z4,z6])],[(0,[z642,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z643,z6]),(0,[z178,z0,z1,z2,z4,z5,z60]),(1,[z539,z0,z1,z2,z5,z6]),(0,[z0,z1,z644,z2,z4,z5,z6]),(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z646,z5,z6]),(1,[z0,z1,z75,z4,z29,z6])],[(0,[z0,z1,z2,z4,z5,z6,z15]),(0,[z647,z0,z1,z2,z4,z5,z6]),(0,[z79,z0,z1,z2,z4,z5,z6])],[(0,[z34,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z648,z4,z5,z6]),(0,[z0,z649,z1,z2,z4,z5,z6]),(0,[z0,z1,z329,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z650])]],
   [[(1,[z0,z1,z2,z31,z41,z6]),(0,[z0,z1,z2,z46,z4,z357,z6])],[(0,[z0,z1,z2,z4,z651,z5,z6]),(0,[z0,z1,z2,z4,z52,z5,z60]),(0,[z0,z1,z2,z4,z5,z6,z254]),(1,[z0,z1,z166,z4,z5,z6])],[(0,[z0,z1,z10,z2,z4,z65,z6])],[(0,[z0,z1,z2,z4,z652,z5,z6]),(0,[z0,z1,z2,z4,z41,z6,z60]),(0,[z0,z30,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z653,z6])],[(0,[z34,z0,z337,z2,z4,z5,z6]),(0,[z0,z654,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z285,z6]),(1,[z102,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z5,z6,z655]),(1,[z0,z1,z2,z4,z290,z6]),(0,[z0,z1,z2,z4,z5,z6,z656])],[(0,[z0,z1,z1,z2,z4,z5,z6])],[(0,[z8,z0,z1,z2,z36,z5,z6]),(0,[z109,z0,z1,z2,z4,z72,z6]),(0,[z0,z39,z1,z2,z4,z41,z6]),(0,[z0,z1,z71,z75,z2,z4,z6]),(0,[z178,z0,z1,z265,z4,z5,z6])],[(0,[z9,z1,z2,z4,z5,z6,z60]),(0,[z0,z1,z71,z2,z4,z28,z6]),(0,[z0,z1,z2,z4,z5,z657,z6]),(0,[z0,z1,z4,z5,z29,z6,z174]),(0,[z0,z1,z2,z4,z6,z176,z174]),(0,[z0,z1,z2,z4,z335,z5,z6])]],
   [[(0,[z0,z30,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z658,z5,z6]),(0,[z82,z0,z1,z2,z4,z5,z105]),(1,[z0,z1,z2,z4,z85,z6]),(0,[z79,z0,z1,z71,z4,z5,z6])],[(0,[z0,z1,z2,z4,z659,z5,z6]),(0,[z178,z277,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z28,z80,z6]),(0,[z131,z1,z2,z4,z72,z5,z6]),(0,[z131,z1,z2,z4,z5,z6,z60]),(0,[z0,z76,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z46,z41,z6]),(0,[z0,z1,z660,z2,z4,z5,z6]),(1,[z0,z87,z2,z4,z5,z6]),(0,[z117,z0,z1,z2,z43,z5,z6]),(0,[z0,z1,z10,z2,z4,z6,z650])],[(0,[z0,z39,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z661,z6]),(0,[z0,z1,z2,z4,z662,z5,z6]),(0,[z12,z0,z1,z2,z571,z5,z6]),(0,[z0,z1,z663,z2,z4,z5,z6])],[(0,[z0,z122,z1,z2,z4,z118,z6]),(0,[z0,z664,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z665])],[(0,[z0,z1,z666,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z157,z5,z6]),(1,[z98,z1,z17,z4,z5,z6]),(0,[z667,z0,z1,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z52,z80,z6])],[(0,[z102,z0,z1,z2,z4,z73,z6]),(0,[z0,z1,z668,z2,z4,z5,z6]),(0,[z0,z1,z320,z2,z4,z41,z6]),(0,[z178,z0,z1,z2,z4,z41,z6]),(0,[z0,z327,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z52,z5,z80])],[(0,[z32,z0,z1,z71,z2,z4,z6]),(1,[z0,z38,z2,z4,z5,z95]),(0,[z13,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z98,z0,z1,z2,z4,z5,z6]),(0,[z669,z0,z1,z2,z4,z5,z6]),(0,[z0,z670,z1,z2,z4,z5,z6]),(0,[z671,z0,z1,z2,z4,z5,z6]),(0,[z610,z0,z1,z10,z2,z4,z6])],[(0,[z672,z0,z1,z2,z4,z5,z6]),(0,[z673,z0,z1,z2,z4,z5,z6]),(0,[z78,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z71,z2,z4,z6])],[(0,[z109,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z72,z5,z28,z6]),(0,[z131,z0,z1,z2,z4,z5,z411]),(0,[z0,z39,z1,z4,z186,z5,z6]),(1,[z0,z1,z2,z4,z357,z6]),(0,[z0,z1,z10,z2,z4,z197,z6]),(1,[z0,z304,z2,z4,z5,z6])],[(0,[z0,z1,z674,z2,z4,z5,z6]),(0,[z675,z0,z1,z2,z4,z5,z6]),(0,[z676,z0,z1,z2,z4,z5,z6]),(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z678,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z679,z5,z6]),(0,[z0,z30,z1,z2,z186,z5,z6]),(0,[z0,z1,z2,z4,z5,z680,z6]),(0,[z681,z0,z1,z2,z4,z5,z6])],[(0,[z8,z0,z1,z2,z4,z5,z6]),(0,[z0,z83,z2,z4,z121,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z11]),(0,[z0,z1,z682,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z125]),(0,[z0,z1,z2,z4,z132,z5,z6]),(0,[z683,z0,z1,z2,z4,z5,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z88,z0,z279,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z685,z5,z6]),(0,[z0,z1,z2,z4,z5,z144,z6]),(0,[z686,z0,z1,z2,z4,z5,z6]),(0,[z687,z0,z1,z2,z4,z5,z6]),(1,[z131,z1,z2,z4,z72,z6])]],
   [[(0,[z0,z1,z2,z688,z4,z5,z6]),(0,[z689,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z28,z6,z60]),(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z691,z1,z2,z4,z5,z6]),(0,[z692,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z75,z2,z4,z5,z6]),(1,[z327,z1,z2,z4,z5,z6]),(0,[z0,z1,z693,z2,z4,z5,z6])],[(0,[z0,z1,z2,z694,z4,z5,z6]),(0,[z695,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z696]),(1,[z0,z1,z2,z4,z221,z6]),(0,[z178,z0,z1,z2,z4,z52,z6])],[(0,[z0,z697,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z698]),(0,[z0,z1,z699,z2,z4,z5,z6]),(0,[z114,z102,z0,z1,z4,z5,z6]),(0,[z700,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z701]),(0,[z0,z1,z2,z4,z702,z5,z6]),(0,[z88,z0,z1,z2,z5,z6,z61])],[(0,[z14,z0,z1,z2,z3,z5,z6]),(0,[z703,z0,z1,z2,z4,z5,z6]),(0,[z8,z0,z143,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z704]),(0,[z0,z1,z2,z4,z154,z5,z6]),(1,[z0,z1,z210,z186,z5,z6]),(0,[z0,z1,z2,z43,z4,z5,z106])],[(0,[z0,z1,z2,z4,z41,z99,z6]),(0,[z0,z1,z2,z4,z5,z6,z55])],[(0,[z0,z337,z2,z4,z121,z5,z6]),(0,[z0,z2,z4,z157,z97,z5,z6]),(0,[z12,z0,z1,z2,z547,z5,z6]),(0,[z0,z1,z2,z4,z705,z5,z6]),(0,[z0,z1,z478,z10,z2,z4,z6]),(1,[z0,z465,z2,z4,z5,z6])],[(0,[z0,z1,z10,z2,z4,z97,z6])],[(0,[z0,z1,z2,z4,z5,z60,z174]),(0,[z79,z0,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z271]),(0,[z0,z1,z2,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z131,z1,z2,z72,z132,z6]),(0,[z0,z1,z2,z428,z41,z6])],[(0,[z0,z1,z2,z4,z707,z6])],[(0,[z207,z1,z17,z4,z5,z6]),(0,[z0,z1,z2,z4,z708,z6]),(0,[z0,z1,z2,z41,z6,z385])],[(0,[z34,z2,z4,z5,z6,z371]),(0,[z298,z1,z2,z65,z5,z6]),(0,[z0,z1,z2,z709,z5,z6])],[(0,[z98,z1,z17,z4,z41,z6]),(0,[z0,z1,z710,z4,z5,z6]),(0,[z0,z711,z2,z4,z5,z6]),(0,[z0,z1,z75,z4,z29,z6]),(0,[z0,z1,z2,z546,z29,z6]),(0,[z0,z1,z2,z571,z712,z6]),(0,[z0,z1,z265,z319,z5,z6])],[(0,[z0,z1,z713,z2,z5,z6]),(0,[z0,z2,z367,z31,z41,z6])],[],[(0,[z327,z1,z265,z4,z5,z6])],[(0,[z0,z1,z232,z4,z5,z406]),(0,[z0,z1,z166,z4,z5,z6]),(0,[z0,z714,z2,z4,z5,z6]),(0,[z0,z1,z2,z547,z162,z6]),(0,[z88,z0,z1,z166,z5,z61])],[(0,[z0,z715,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z716,z6]),(0,[z0,z39,z83,z4,z41,z6]),(0,[z0,z135,z2,z4,z73,z6])],[(0,[z0,z1,z2,z4,z41,z411]),(0,[z490,z0,z1,z71,z4,z6])],[(0,[z0,z1,z2,z3,z92,z6]),(0,[z387,z0,z2,z4,z5,z11]),(0,[z0,z1,z717,z2,z4,z6]),(0,[z0,z718,z2,z4,z5,z6]),(0,[z719,z1,z2,z4,z5,z6])],[(0,[z0,z1,z720,z4,z5,z6]),(0,[z0,z1,z2,z123,z5,z6]),(0,[z0,z2,z4,z721,z118,z6]),(0,[z0,z1,z2,z319,z41,z6])],[(0,[z0,z1,z232,z4,z5,z57]),(0,[z0,z1,z2,z4,z41,z125]),(0,[z0,z2,z4,z722,z5,z6])],[(0,[z183,z0,z1,z2,z41,z6]),(0,[z0,z1,z27,z210,z186,z6]),(0,[z0,z135,z2,z4,z41,z6]),(0,[z0,z1,z218,z319,z5,z6])],[(0,[z0,z1,z2,z4,z85,z6]),(0,[z0,z1,z723,z4,z5,z6]),(0,[z0,z1,z2,z621,z41,z6]),(0,[z327,z1,z2,z4,z41,z6]),(0,[z0,z1,z10,z166,z4,z6])]],
   [[(0,[z1,z2,z4,z5,z724,z60]),(0,[z0,z1,z186,z368,z5,z6])],[(0,[z0,z1,z89,z4,z5,z6]),(0,[z0,z1,z211,z3,z5,z6]),(0,[z0,z1,z2,z4,z92,z15]),(0,[z16,z1,z4,z97,z41,z6]),(0,[z0,z1,z725,z4,z5,z6]),(0,[z0,z726,z2,z4,z5,z6]),(0,[z0,z1,z727,z2,z4,z6])],[(0,[z1,z2,z4,z5,z6,z728]),(0,[z0,z1,z210,z186,z41,z6]),(0,[z114,z729,z0,z1,z5,z6]),(0,[z0,z1,z10,z2,z43,z106])],[(0,[z14,z337,z2,z4,z92,z6]),(0,[z0,z1,z730,z2,z4,z6]),(0,[z0,z1,z2,z4,z731,z6]),(0,[z732,z1,z2,z4,z5,z6]),(0,[z0,z733,z10,z2,z4,z6])],[],[(0,[z130,z0,z89,z4,z5,z6]),(0,[z1,z2,z4,z5,z580,z60])],[(0,[z9,z0,z1,z2,z41,z6]),(0,[z0,z1,z734,z4,z5,z6]),(0,[z0,z38,z2,z4,z5,z503]),(0,[z0,z1,z2,z186,z167,z6])],[(0,[z0,z1,z735,z2,z4,z6]),(0,[z0,z1,z2,z479,z41,z6]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z0,z1,z210,z186,z297,z6])],[],[(0,[z14,z337,z211,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z59]),(0,[z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z737,z2,z4,z6]),(0,[z0,z1,z62,z186,z41,z6])],[(0,[z0,z1,z2,z738,z5,z6]),(0,[z0,z1,z2,z739,z5,z6]),(0,[z16,z130,z4,z97,z5,z6]),(0,[z0,z135,z4,z186,z5,z6]),(0,[z0,z1,z740,z2,z4,z6]),(0,[z0,z1,z10,z2,z4,z741]),(1,[z0,z1,z2,z4,z742])],[],[(0,[z0,z21,z2,z4,z72,z6]),(0,[z0,z1,z2,z4,z743,z6]),(0,[z66,z0,z441,z4,z5,z6]),(0,[z0,z1,z744,z4,z5,z6]),(0,[z38,z2,z4,z5,z95,z96]),(0,[z0,z1,z384,z2,z41,z6])],[(0,[z98,z1,z2,z4,z5,z59])],[(0,[z0,z1,z2,z4,z282,z59]),(0,[z0,z745,z2,z4,z5,z6]),(0,[z0,z746,z2,z4,z5,z6])],[(0,[z0,z1,z2,z747,z5,z6]),(0,[z0,z1,z2,z499,z41,z6]),(0,[z0,z1,z2,z4,z748,z6])]],
   [[(0,[z0,z1,z2,z4,z6,z749]),(0,[z0,z1,z2,z4,z750,z6]),(0,[z79,z0,z1,z751,z4,z6]),(0,[z0,z1,z2,z4,z5,z752])],[(0,[z0,z1,z753,z2,z4,z6]),(0,[z0,z83,z4,z722,z5,z6]),(0,[z0,z1,z2,z4,z754,z6]),(0,[z0,z1,z75,z218,z4,z6]),(0,[z0,z1,z2,z571,z41,z6])],[(0,[z0,z1,z755,z2,z46,z6]),(0,[z0,z1,z201,z2,z41,z6]),(0,[z0,z1,z2,z4,z742,z55])],[],[(0,[z0,z70,z2,z4,z5,z59]),(0,[z0,z465,z2,z4,z5,z6])],[(1,[z0,z1,z2,z756,z6]),(0,[z0,z1,z10,z2,z571,z6])],[(0,[z0,z757,z2,z4,z5,z6]),(0,[z0,z1,z2,z507,z41,z6]),(0,[z1,z2,z4,z41,z6,z96]),(0,[z0,z279,z166,z4,z5,z6]),(0,[z0,z1,z218,z4,z6,z55])],[(0,[z0,z1,z2,z7,z5,z6]),(0,[z0,z758,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z759]),(0,[z0,z1,z71,z2,z132,z6]),(0,[z0,z21,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z6,z760]),(0,[z0,z1,z192,z4,z223,z6]),(0,[z0,z1,z2,z4,z761,z6]),(0,[z0,z1,z2,z126,z41,z6])],[(0,[z762,z1,z2,z4,z5,z6]),(0,[z242,z38,z2,z4,z5,z95]),(0,[z0,z1,z235,z2,z319,z6])],[(0,[z0,z1,z211,z4,z41,z6]),(0,[z0,z1,z763,z4,z5,z6]),(0,[z0,z127,z2,z65,z5,z6]),(0,[z0,z1,z2,z132,z80,z6]),(0,[z0,z764,z2,z4,z5,z6]),(0,[z0,z1,z485,z4,z111,z6]),(0,[z0,z1,z2,z4,z52,z742])],[(0,[z0,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z282,z6]),(0,[z0,z765,z2,z4,z5,z6]),(0,[z0,z1,z766,z4,z5,z6]),(0,[z131,z146,z1,z2,z72,z6]),(0,[z242,z1,z2,z4,z5,z105]),(0,[z0,z767,z2,z4,z5,z6]),(0,[z0,z1,z2,z41,z6,z488])],[(0,[z0,z122,z21,z2,z4,z6]),(0,[z0,z768,z2,z4,z5,z6])],[(0,[z0,z1,z2,z535,z41,z6]),(0,[z0,z1,z769,z2,z4,z6]),(0,[z0,z348,z2,z31,z5,z6]),(0,[z0,z91,z2,z46,z5,z6])],[(0,[z0,z83,z2,z31,z41,z6]),(0,[z0,z1,z2,z4,z770,z6]),(0,[z0,z1,z351,z4,z29,z6])]],
   [[(0,[z0,z771,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z772]),(0,[z0,z1,z2,z154,z80,z6]),(0,[z0,z1,z485,z4,z29,z6]),(0,[z171,z1,z2,z4,z5,z61])],[(0,[z0,z2,z4,z5,z6,z773]),(0,[z0,z1,z774,z2,z479,z6]),(0,[z0,z1,z2,z775,z5,z6]),(0,[z0,z1,z776,z2,z4,z6])],[(0,[z0,z70,z2,z4,z5,z6]),(0,[z130,z114,z0,z4,z5,z6]),(0,[z0,z1,z75,z4,z20,z6])],[(0,[z0,z1,z211,z208,z5,z6]),(0,[z0,z1,z17,z266,z5,z6]),(0,[z0,z1,z2,z777,z5,z6]),(0,[z0,z1,z2,z545,z41,z6]),(0,[z0,z1,z2,z546,z41,z6]),(0,[z560,z102,z0,z1,z5,z6]),(0,[z0,z1,z2,z547,z41,z6]),(0,[z0,z1,z2,z778,z6,z174])],[(0,[z689,z0,z2,z31,z5,z6]),(0,[z88,z0,z279,z2,z5,z61]),(0,[z178,z277,z1,z2,z4,z55])],[(0,[z312,z0,z1,z2,z41,z6]),(1,[z1,z2,z779,z5,z6]),(0,[z381,z1,z2,z4,z5,z60]),(0,[z780,z1,z2,z4,z5,z6]),(0,[z0,z1,z217,z4,z357,z6])],[(0,[z0,z1,z2,z4,z5,z781]),(0,[z0,z1,z2,z558,z41,z6]),(0,[z0,z1,z2,z559,z41,z6])],[(0,[z782,z1,z2,z4,z5,z6])],[(0,[z0,z1,z186,z97,z41,z6]),(0,[z539,z0,z1,z2,z783,z6]),(0,[z0,z1,z784,z2,z4,z6]),(0,[z0,z1,z2,z785,z41,z6]),(0,[z178,z327,z1,z2,z4,z55])],[(0,[z0,z1,z2,z786,z5,z6]),(0,[z0,z1,z232,z4,z223,z6]),(0,[z117,z0,z1,z2,z5,z57]),(0,[z0,z1,z200,z4,z29,z6]),(0,[z0,z1,z787,z4,z5,z6])],[(0,[z9,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z4,z223,z406]),(0,[z253,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z5,z724]),(0,[z0,z1,z2,z4,z788,z6]),(0,[z0,z1,z2,z789,z5,z6]),(0,[z225,z1,z2,z4,z5,z174]),(0,[z0,z304,z10,z2,z4,z6])],[(0,[z0,z1,z2,z790,z5,z6]),(0,[z0,z1,z791,z2,z4,z6]),(0,[z0,z1,z166,z4,z41,z6])],[(0,[z0,z1,z792,z2,z4,z6]),(0,[z0,z64,z2,z266,z5,z6]),(0,[z0,z793,z2,z4,z5,z6]),(0,[z0,z1,z2,z794,z5,z6])],[(0,[z795,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z796,z6]),(0,[z0,z1,z797,z4,z5,z6]),(1,[z0,z2,z4,z721,z6]),(0,[z0,z1,z2,z4,z798,z6]),(0,[z0,z1,z2,z4,z5,z799])],[(0,[z0,z1,z168,z2,z41,z6]),(0,[z0,z279,z2,z4,z221,z6])],[(0,[z0,z1,z89,z4,z273,z6]),(0,[z0,z337,z2,z31,z41,z6]),(0,[z0,z1,z2,z123,z41,z6]),(1,[z0,z1,z2,z778,z6])]],
   [[(0,[z0,z1,z2,z132,z5,z6]),(0,[z0,z2,z4,z775,z5,z6])],[(0,[z415,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z800]),(1,[z0,z4,z722,z5,z6]),(0,[z0,z39,z10,z83,z4,z6])],[(0,[z1,z801,z2,z4,z5,z6]),(0,[z0,z51,z1,z2,z154,z6]),(0,[z0,z120,z1,z2,z802,z6])],[(0,[z0,z1,z218,z4,z28,z6]),(0,[z803,z1,z2,z4,z5,z6]),(0,[z0,z38,z2,z4,z5,z181]),(0,[z0,z1,z2,z391,z41,z6]),(0,[z0,z1,z2,z4,z804,z6])],[(0,[z0,z1,z2,z4,z5,z805]),(0,[z0,z1,z2,z132,z29,z6]),(0,[z199,z0,z1,z2,z41,z6])],[(0,[z9,z1,z2,z36,z90,z6]),(0,[z0,z1,z2,z154,z5,z6]),(0,[z0,z806,z2,z4,z41,z6]),(0,[z0,z465,z10,z2,z4,z6])],[(0,[z0,z1,z2,z4,z6,z807]),(0,[z0,z1,z2,z4,z6,z808])],[(0,[z8,z252,z2,z65,z5,z6]),(0,[z0,z1,z809,z2,z4,z6])],[(0,[z0,z1,z10,z232,z4,z6]),(0,[z0,z1,z810,z4,z5,z6])],[(0,[z0,z83,z4,z156,z5,z6]),(0,[z0,z1,z811,z2,z4,z6]),(0,[z0,z1,z2,z154,z29,z6]),(0,[z0,z38,z2,z4,z41,z95]),(0,[z0,z21,z10,z2,z4,z6])],[(0,[z183,z0,z1,z2,z132,z6]),(0,[z0,z21,z2,z4,z5,z60]),(0,[z12,z0,z1,z4,z5,z174])],[(0,[z0,z1,z2,z7,z241,z6]),(1,[z0,z1,z2,z41,z57])],[(0,[z0,z1,z89,z208,z5,z6]),(0,[z669,z1,z2,z4,z5,z60]),(0,[z0,z30,z2,z775,z5,z6]),(0,[z0,z304,z2,z4,z41,z6]),(0,[z284,z1,z498,z2,z4,z6])],[(0,[z0,z1,z10,z2,z4,z44]),(0,[z14,z337,z2,z4,z5,z44]),(0,[z0,z1,z812,z2,z4,z6]),(0,[z0,z1,z218,z4,z5,z105])],[(0,[z16,z4,z157,z97,z5,z6]),(0,[z0,z1,z755,z2,z4,z6]),(0,[z0,z2,z4,z5,z6,z813])],[(0,[z814,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z33,z132,z6]),(0,[z74,z0,z1,z75,z29,z6]),(0,[z0,z465,z265,z4,z5,z6])]],
   [[(0,[z0,z64,z17,z4,z5,z6]),(0,[z1,z2,z4,z72,z708,z6]),(1,[z729,z0,z1,z5,z6])],[(0,[z815,z0,z1,z4,z5,z6]),(0,[z0,z1,z774,z2,z4,z6]),(0,[z32,z0,z1,z2,z179,z6]),(0,[z0,z1,z2,z4,z5,z816])],[],[(0,[z14,z801,z2,z4,z5,z6]),(0,[z0,z70,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z817,z6]),(0,[z0,z818,z2,z4,z5,z6]),(0,[z0,z1,z136,z4,z187,z6]),(0,[z0,z21,z265,z4,z5,z6])],[(0,[z0,z1,z2,z4,z819,z6]),(0,[z0,z1,z2,z4,z820,z6]),(0,[z0,z1,z2,z41,z6,z57]),(0,[z327,z1,z218,z4,z5,z6])],[(0,[z821,z0,z1,z2,z5,z6]),(0,[z0,z1,z822,z2,z547,z6]),(0,[z823,z0,z1,z2,z5,z6]),(0,[z0,z1,z10,z62,z4,z99])],[(0,[z0,z1,z2,z4,z824,z6]),(0,[z0,z70,z2,z4,z241,z6]),(0,[z0,z1,z2,z825,z5,z6]),(0,[z0,z1,z2,z4,z826,z6]),(0,[z0,z1,z2,z43,z221,z6]),(0,[z0,z1,z2,z5,z106,z752])],[(0,[z0,z1,z827,z2,z4,z6]),(0,[z214,z0,z1,z4,z5,z174]),(0,[z0,z465,z2,z4,z41,z6])],[(0,[z0,z1,z2,z828,z5,z6]),(0,[z0,z1,z620,z2,z41,z6])],[(0,[z8,z1,z2,z65,z144,z6]),(0,[z829,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z639,z41,z6])],[(0,[z0,z1,z211,z4,z5,z15]),(0,[z0,z1,z2,z4,z273,z44]),(0,[z0,z1,z2,z7,z41,z6]),(0,[z0,z1,z217,z4,z5,z6]),(0,[z12,z0,z1,z4,z290,z174]),(0,[z0,z1,z830,z2,z4,z6])],[(0,[z0,z1,z17,z186,z41,z6]),(0,[z0,z39,z303,z83,z4,z6]),(0,[z831,z1,z2,z4,z5,z6]),(0,[z0,z21,z2,z4,z41,z6])],[(0,[z0,z1,z2,z832,z5,z6]),(0,[z383,z1,z4,z97,z5,z6]),(0,[z833,z1,z2,z4,z5,z6]),(0,[z12,z0,z87,z4,z5,z174])],[(0,[z153,z0,z30,z4,z5,z6])],[(1,[z0,z1,z834,z2,z6]),(0,[z0,z1,z10,z2,z4,z799])],[(0,[z0,z1,z2,z4,z41,z44]),(0,[z0,z1,z2,z4,z340,z6]),(0,[z0,z1,z200,z2,z4,z105]),(0,[z0,z1,z2,z4,z835,z6]),(0,[z32,z0,z21,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z836]),(0,[z277,z1,z2,z4,z72,z6]),(0,[z0,z39,z372,z4,z5,z6])],[],[(0,[z0,z252,z2,z5,z41,z6]),(0,[z0,z122,z1,z2,z179,z6])],[(0,[z0,z1,z837,z4,z5,z6]),(0,[z0,z838,z2,z4,z5,z6])],[(0,[z0,z2,z4,z92,z6,z11]),(0,[z8,z1,z2,z65,z41,z6]),(0,[z0,z1,z2,z839,z5,z6])],[(0,[z0,z70,z2,z4,z41,z6]),(0,[z117,z0,z1,z2,z223,z6]),(0,[z539,z0,z1,z303,z2,z6]),(0,[z114,z170,z0,z1,z5,z6])],[(0,[z1,z2,z4,z5,z6,z724]),(0,[z840,z1,z2,z4,z5,z6]),(0,[z0,z1,z699,z2,z41,z6]),(0,[z0,z1,z841,z2,z4,z6]),(0,[z178,z0,z465,z2,z4,z55])],[(0,[z0,z1,z2,z208,z5,z44]),(0,[z0,z842,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z843]),(0,[z0,z844,z2,z4,z5,z6]),(0,[z0,z1,z10,z845,z4,z6])],[(0,[z0,z1,z2,z4,z5,z846]),(0,[z145,z1,z2,z4,z5,z60]),(0,[z0,z1,z2,z4,z52,z80])],[(0,[z0,z1,z211,z4,z92,z6]),(0,[z0,z847,z2,z4,z5,z6]),(0,[z0,z848,z2,z4,z5,z6]),(0,[z0,z1,z394,z2,z41,z6])],[(0,[z524,z0,z2,z31,z5,z6]),(0,[z32,z0,z2,z4,z421,z6])],[(0,[z0,z1,z2,z4,z849,z6]),(0,[z298,z0,z1,z2,z5,z61])],[(0,[z551,z0,z4,z121,z5,z6]),(0,[z0,z1,z2,z4,z5,z274]),(0,[z277,z1,z2,z4,z5,z6])],[(0,[z0,z35,z2,z208,z5,z6]),(0,[z0,z1,z89,z3,z5,z6]),(0,[z9,z1,z2,z36,z41,z6]),(0,[z0,z1,z71,z2,z154,z6])],[(0,[z0,z1,z2,z4,z6,z850]),(0,[z0,z1,z2,z851,z5,z6]),(0,[z852,z0,z1,z2,z4,z6]),(0,[z0,z1,z201,z2,z546,z6]),(0,[z0,z1,z740,z2,z41,z6])],[(0,[z34,z35,z2,z4,z5,z6]),(0,[z853,z1,z2,z4,z5,z6]),(0,[z225,z1,z2,z4,z5,z99]),(0,[z0,z1,z62,z4,z290,z6])]],
   [[(0,[z0,z1,z854,z2,z4,z6]),(0,[z1,z17,z4,z855,z5,z6]),(0,[z0,z1,z2,z856,z5,z6]),(0,[z13,z1,z2,z571,z5,z6]),(0,[z0,z1,z2,z778,z5,z6])],[(0,[z0,z1,z2,z4,z5,z857]),(0,[z0,z1,z192,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z858])],[(0,[z0,z1,z2,z4,z5,z859]),(0,[z79,z0,z1,z2,z179,z6])],[(0,[z0,z1,z89,z4,z5,z15]),(0,[z0,z2,z208,z5,z6,z11]),(0,[z0,z1,z252,z2,z41,z6]),(0,[z0,z1,z2,z132,z41,z6]),(1,[z1,z2,z4,z708,z6]),(0,[z0,z1,z2,z4,z6,z42]),(0,[z0,z1,z860,z4,z41,z6]),(0,[z0,z1,z861,z4,z5,z6]),(0,[z0,z1,z10,z218,z4,z6])],[(0,[z202,z0,z1,z2,z41,z6]),(0,[z131,z1,z2,z4,z72,z411]),(0,[z0,z1,z2,z862,z5,z6])],[(0,[z14,z337,z89,z4,z5,z6])],[(0,[z1,z2,z4,z5,z44,z60]),(0,[z0,z863,z2,z4,z5,z6]),(0,[z864,z1,z2,z4,z5,z6])],[(0,[z0,z143,z192,z4,z5,z6]),(0,[z0,z1,z2,z479,z865,z6]),(0,[z0,z1,z10,z2,z154,z6]),(0,[z327,z1,z2,z319,z5,z6])],[(0,[z45,z1,z2,z208,z5,z6]),(0,[z0,z1,z2,z4,z866,z6]),(0,[z0,z1,z2,z154,z41,z6]),(0,[z0,z1,z867,z4,z5,z6])],[],[(0,[z868,z0,z1,z2,z5,z6]),(0,[z869,z1,z2,z4,z5,z6]),(0,[z100,z279,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z870,z6]),(0,[z0,z1,z2,z4,z5,z871]),(0,[z0,z872,z2,z4,z5,z6]),(0,[z0,z30,z127,z2,z5,z6]),(0,[z0,z1,z2,z873,z5,z6])],[(0,[z0,z39,z83,z479,z5,z6])],[(0,[z874,z1,z2,z4,z5,z6]),(0,[z0,z1,z62,z4,z5,z875]),(0,[z117,z0,z1,z10,z2,z6]),(0,[z100,z1,z10,z2,z4,z6])],[(0,[z0,z1,z876,z2,z4,z6])],[(0,[z0,z1,z2,z266,z5,z59]),(0,[z0,z1,z2,z25,z41,z6]),(0,[z0,z1,z2,z324,z41,z61])]],
   [[],[(0,[z0,z1,z232,z4,z5,z6]),(0,[z0,z1,z2,z4,z340,z60]),(0,[z0,z1,z2,z4,z877,z6])],[(0,[z0,z1,z2,z4,z223,z57]),(0,[z13,z1,z2,z547,z5,z6]),(0,[z178,z0,z1,z2,z4,z742])],[(0,[z66,z0,z89,z4,z5,z6]),(0,[z242,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z878,z6]),(0,[z0,z1,z71,z607,z4,z6]),(0,[z0,z1,z75,z546,z29,z6]),(0,[z79,z0,z1,z196,z4,z6])],[(0,[z0,z1,z2,z4,z5,z879])],[(0,[z0,z1,z10,z2,z7,z6])],[(0,[z0,z1,z2,z4,z880,z6]),(0,[z0,z818,z2,z4,z41,z6])],[(0,[z0,z1,z89,z4,z41,z6]),(0,[z0,z252,z192,z4,z5,z6]),(0,[z0,z143,z232,z4,z5,z6]),(0,[z695,z0,z1,z2,z41,z6]),(0,[z0,z1,z881,z2,z4,z6]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z0,z1,z10,z210,z186,z6])],[(0,[z0,z1,z2,z3,z5,z44]),(0,[z0,z1,z2,z4,z6,z883]),(0,[z0,z252,z2,z36,z5,z6]),(0,[z0,z143,z2,z4,z5,z406])],[(0,[z0,z1,z2,z41,z6,z250])],[(0,[z0,z1,z2,z4,z884,z6])],[(0,[z0,z2,z4,z885,z5,z6]),(0,[z109,z1,z2,z4,z28,z6])],[(0,[z0,z1,z886,z2,z3,z6]),(0,[z0,z1,z2,z4,z5,z887]),(0,[z114,z0,z1,z440,z5,z6])],[(0,[z0,z1,z2,z266,z5,z6]),(0,[z0,z1,z10,z2,z4,z274]),(0,[z0,z1,z2,z186,z90,z6]),(0,[z0,z39,z1,z479,z5,z6]),(0,[z0,z1,z217,z4,z41,z6]),(0,[z0,z1,z62,z4,z5,z527]),(0,[z277,z1,z10,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z888]),(0,[z277,z1,z2,z4,z5,z60]),(0,[z66,z0,z4,z134,z5,z6])],[(0,[z16,z70,z4,z97,z5,z6]),(0,[z0,z38,z2,z4,z5,z813]),(0,[z100,z1,z2,z4,z41,z6])]],
   [[(0,[z0,z1,z889,z4,z5,z6]),(0,[z0,z1,z854,z2,z208,z6]),(0,[z34,z35,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z890]),(0,[z0,z1,z2,z4,z241,z274])],[],[(0,[z0,z1,z2,z4,z891,z6])],[(0,[z0,z1,z127,z2,z41,z6])],[(0,[z0,z1,z2,z340,z743,z6]),(0,[z0,z1,z2,z294,z5,z106]),(0,[z0,z1,z2,z33,z154,z6]),(0,[z242,z1,z2,z4,z798,z6])],[(0,[z8,z0,z1,z232,z41,z6]),(0,[z0,z1,z2,z4,z892,z6]),(0,[z12,z0,z1,z4,z162,z174]),(0,[z171,z1,z136,z4,z5,z6])],[(0,[z0,z893,z2,z4,z5,z6]),(0,[z178,z0,z1,z2,z4,z55])],[(0,[z0,z252,z232,z4,z5,z6]),(0,[z0,z1,z2,z192,z41,z6]),(0,[z0,z1,z2,z894,z5,z6]),(0,[z555,z0,z1,z2,z41,z6]),(0,[z277,z1,z265,z4,z5,z6])],[(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z1,z896,z4,z5,z6]),(0,[z284,z1,z2,z4,z72,z6]),(0,[z0,z1,z2,z4,z5,z897])],[(0,[z0,z1,z192,z4,z144,z6]),(0,[z0,z1,z2,z648,z41,z6]),(0,[z0,z1,z2,z898,z5,z6]),(0,[z0,z38,z2,z4,z5,z393]),(0,[z0,z1,z200,z218,z4,z6]),(0,[z0,z1,z2,z43,z5,z752])],[(0,[z0,z1,z2,z179,z72,z6]),(0,[z0,z30,z46,z217,z5,z6]),(0,[z0,z1,z2,z899,z5,z6]),(0,[z0,z1,z235,z2,z4,z6])],[(0,[z0,z1,z900,z4,z5,z6]),(0,[z0,z1,z2,z901,z5,z6]),(0,[z0,z1,z10,z2,z595,z6]),(0,[z260,z0,z1,z196,z4,z6])],[(0,[z0,z1,z902,z2,z4,z6]),(0,[z0,z64,z2,z4,z5,z59]),(0,[z0,z1,z2,z31,z90,z6]),(0,[z0,z38,z2,z31,z41,z6]),(0,[z0,z903,z2,z4,z5,z6]),(0,[z904,z1,z2,z4,z5,z6]),(0,[z0,z465,z218,z4,z5,z6])],[(0,[z0,z1,z2,z905,z5,z6]),(0,[z0,z1,z2,z4,z92,z44]),(0,[z0,z30,z2,z694,z5,z6]),(0,[z0,z906,z2,z4,z5,z6]),(0,[z907,z0,z2,z4,z5,z6]),(0,[z66,z0,z4,z121,z5,z6]),(0,[z1,z2,z4,z5,z6,z908]),(0,[z0,z1,z2,z386,z41,z6])],[(0,[z0,z2,z4,z5,z6,z909]),(0,[z204,z1,z2,z4,z72,z6]),(0,[z114,z0,z135,z4,z5,z6])],[(0,[z0,z1,z2,z4,z41,z274]),(0,[z0,z2,z4,z5,z411,z909]),(0,[z0,z1,z2,z43,z5,z350]),(0,[z277,z1,z2,z4,z41,z6]),(0,[z0,z1,z478,z2,z179,z6])]],
   [[(0,[z0,z1,z910,z4,z5,z6]),(0,[z203,z35,z2,z4,z5,z6]),(0,[z911,z0,z1,z2,z4,z41]),(0,[z171,z1,z2,z4,z187,z6]),(0,[z0,z304,z166,z4,z5,z6]),(0,[z0,z21,z218,z4,z5,z6])],[(0,[z0,z83,z2,z208,z5,z6]),(0,[z0,z912,z2,z4,z5,z6]),(0,[z0,z1,z913,z4,z5,z6]),(0,[z0,z1,z478,z2,z41,z6]),(0,[z277,z1,z218,z4,z5,z6])],[(0,[z0,z1,z2,z4,z914,z6]),(0,[z0,z1,z755,z2,z41,z6]),(0,[z729,z0,z1,z2,z5,z6])],[],[(0,[z0,z1,z192,z4,z41,z6]),(0,[z82,z1,z2,z4,z5,z724]),(0,[z66,z0,z4,z213,z5,z6]),(0,[z0,z348,z2,z31,z41,z6]),(0,[z0,z1,z2,z4,z915,z6]),(0,[z916,z1,z2,z4,z5,z6]),(0,[z917,z1,z2,z4,z5,z6])],[(0,[z117,z0,z1,z192,z5,z6]),(0,[z1,z2,z779,z65,z5,z6]),(0,[z103,z1,z2,z4,z5,z60]),(0,[z0,z1,z2,z4,z41,z859])],[(0,[z0,z1,z2,z918,z5,z6]),(0,[z0,z1,z2,z46,z90,z6]),(0,[z0,z1,z2,z4,z919,z6]),(0,[z0,z1,z861,z4,z41,z6]),(0,[z0,z1,z2,z179,z5,z6])],[(0,[z0,z1,z2,z920,z5,z6]),(0,[z0,z1,z2,z4,z921,z6]),(0,[z0,z1,z2,z4,z28,z411]),(0,[z79,z0,z1,z668,z4,z6]),(0,[z0,z1,z166,z4,z221,z6])],[(0,[z8,z0,z252,z2,z41,z6]),(0,[z0,z1,z922,z2,z571,z6])],[(0,[z0,z1,z923,z4,z5,z6]),(0,[z292,z0,z2,z31,z5,z6]),(0,[z0,z1,z232,z4,z144,z6]),(0,[z40,z0,z2,z4,z5,z11]),(0,[z1,z10,z2,z4,z6,z96]),(0,[z0,z1,z115,z186,z5,z6]),(0,[z12,z0,z1,z10,z4,z174]),(0,[z0,z863,z2,z4,z41,z6])],[(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z925,z2,z4,z5,z6]),(0,[z0,z1,z4,z290,z6,z174])],[(0,[z0,z1,z2,z4,z926,z6]),(0,[z1,z2,z4,z779,z5,z6]),(0,[z131,z1,z2,z4,z708,z6]),(0,[z0,z410,z2,z4,z290,z6])],[(0,[z0,z1,z4,z927,z5,z6]),(0,[z539,z0,z1,z2,z761,z6])],[(0,[z869,z1,z2,z4,z41,z6])],[(0,[z45,z1,z2,z4,z92,z6]),(1,[z0,z1,z751,z4,z6]),(0,[z458,z1,z2,z4,z335,z6])],[(0,[z0,z1,z886,z2,z4,z6]),(0,[z0,z1,z2,z216,z41,z6]),(0,[z0,z1,z2,z928,z5,z6]),(0,[z12,z0,z1,z4,z176,z174])]],
   [[],[(0,[z0,z337,z2,z208,z5,z6]),(0,[z0,z1,z2,z266,z241,z6]),(0,[z0,z1,z2,z4,z5,z929]),(0,[z0,z1,z218,z4,z52,z6])],[(0,[z0,z1,z46,z217,z41,z6]),(0,[z170,z0,z1,z2,z41,z6])],[(0,[z0,z1,z2,z4,z930,z6]),(0,[z0,z1,z2,z4,z223,z6]),(0,[z0,z1,z2,z223,z41,z6]),(0,[z178,z0,z21,z2,z4,z55])],[(0,[z310,z0,z2,z31,z5,z6]),(0,[z0,z1,z232,z4,z41,z6]),(0,[z0,z1,z2,z4,z931,z6]),(0,[z109,z1,z194,z2,z4,z6]),(0,[z117,z0,z1,z217,z5,z6]),(0,[z0,z120,z1,z2,z756,z6])],[(0,[z0,z1,z2,z694,z41,z6]),(0,[z0,z1,z2,z186,z41,z6]),(0,[z0,z932,z1,z2,z4,z6])],[],[(1,[z0,z1,z192,z41,z6]),(0,[z9,z1,z10,z2,z36,z6]),(0,[z933,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z934,z6])],[(0,[z8,z0,z143,z2,z41,z6]),(0,[z0,z1,z935,z2,z4,z6]),(0,[z0,z1,z2,z936,z5,z6]),(0,[z0,z1,z2,z4,z937,z6]),(0,[z729,z0,z1,z186,z5,z6]),(0,[z0,z304,z2,z4,z221,z6])],[(0,[z0,z143,z2,z4,z223,z6]),(0,[z0,z4,z722,z121,z5,z6]),(0,[z0,z76,z329,z2,z4,z6])],[(0,[z131,z1,z2,z4,z72,z125]),(0,[z0,z1,z2,z186,z297,z6]),(0,[z0,z1,z938,z2,z4,z6])],[(0,[z1,z2,z36,z779,z5,z6])],[(0,[z0,z1,z2,z41,z105,z61])],[(0,[z629,z0,z1,z2,z41,z6]),(0,[z0,z2,z4,z939,z5,z6])],[(0,[z0,z1,z2,z4,z940,z6]),(0,[z0,z1,z2,z941,z5,z6])],[(0,[z555,z337,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z942,z6]),(0,[z0,z465,z2,z319,z5,z6])]],
   [[(0,[z0,z1,z2,z266,z41,z6]),(0,[z686,z102,z0,z1,z5,z6]),(0,[z12,z0,z1,z4,z41,z174]),(0,[z610,z0,z1,z4,z20,z6])],[(0,[z0,z1,z2,z943,z5,z6]),(0,[z0,z1,z2,z592,z41,z6]),(0,[z0,z1,z2,z272,z41,z6]),(0,[z0,z1,z2,z4,z944,z6])],[(0,[z35,z801,z2,z4,z5,z6]),(0,[z0,z1,z2,z945,z5,z6]),(0,[z109,z1,z2,z4,z708,z6]),(0,[z0,z1,z257,z4,z5,z99]),(0,[z117,z0,z1,z834,z2,z6]),(0,[z327,z465,z2,z4,z5,z6])],[(0,[z0,z1,z136,z4,z5,z6]),(0,[z0,z21,z2,z319,z5,z6])],[(0,[z0,z1,z2,z7,z946,z6]),(0,[z0,z2,z4,z947,z5,z6]),(0,[z225,z410,z2,z4,z5,z6]),(0,[z0,z948,z1,z2,z4,z6])],[(0,[z0,z1,z89,z4,z92,z6]),(0,[z0,z1,z2,z4,z5,z406]),(0,[z0,z30,z2,z440,z5,z6]),(0,[z0,z1,z2,z949,z5,z6]),(0,[z0,z1,z682,z2,z41,z6])],[(0,[z950,z0,z1,z2,z5,z6]),(1,[z0,z1,z217,z41,z6]),(0,[z0,z1,z951,z4,z5,z6]),(0,[z0,z1,z2,z4,z952,z6]),(0,[z327,z21,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z179,z5,z60])],[(0,[z16,z1,z4,z97,z5,z274]),(0,[z0,z1,z2,z4,z953,z6]),(0,[z0,z1,z62,z4,z5,z530])],[(0,[z0,z1,z2,z954,z5,z6]),(0,[z0,z1,z2,z4,z5,z57]),(0,[z40,z0,z10,z2,z4,z11])],[(0,[z0,z955,z2,z4,z5,z6]),(0,[z0,z1,z472,z4,z29,z6]),(0,[z0,z1,z2,z4,z41,z897])],[(0,[z0,z1,z956,z2,z4,z6]),(0,[z0,z1,z2,z295,z41,z6]),(0,[z16,z1,z4,z97,z282,z6]),(0,[z0,z957,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z958,z6]),(0,[z0,z1,z2,z959,z5,z6]),(0,[z0,z960,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z961])],[(0,[z0,z122,z2,z4,z118,z6]),(0,[z0,z1,z2,z4,z187,z6]),(0,[z0,z1,z834,z320,z2,z6])],[(0,[z678,z1,z2,z36,z5,z6]),(0,[z962,z1,z2,z4,z5,z6]),(0,[z0,z903,z2,z4,z41,z6])]],
   [[(0,[z0,z143,z2,z4,z5,z57]),(0,[z66,z0,z4,z121,z41,z6])],[(0,[z0,z1,z265,z179,z5,z6])],[(0,[z9,z1,z307,z2,z36,z6]),(0,[z539,z0,z30,z2,z5,z6]),(0,[z963,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z314,z41,z6]),(0,[z0,z1,z2,z4,z167,z6])],[(0,[z0,z1,z2,z4,z5,z964])],[(0,[z321,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z965,z6]),(0,[z966,z1,z2,z4,z5,z6]),(0,[z0,z30,z2,z46,z357,z6]),(0,[z0,z127,z2,z4,z315,z6])],[(0,[z9,z1,z2,z4,z5,z57]),(0,[z78,z0,z127,z2,z5,z6]),(0,[z0,z1,z2,z4,z6,z176])],[(0,[z0,z1,z2,z4,z967,z6]),(0,[z45,z1,z2,z4,z5,z411]),(0,[z32,z0,z2,z4,z516,z6]),(0,[z0,z1,z751,z2,z4,z6]),(0,[z0,z1,z71,z318,z4,z6])],[(0,[z0,z1,z2,z4,z5,z968]),(0,[z0,z1,z2,z4,z756,z6]),(0,[z0,z1,z693,z2,z41,z6])],[(0,[z0,z969,z2,z4,z5,z6]),(0,[z0,z970,z1,z2,z4,z6]),(0,[z0,z557,z1,z186,z5,z6]),(0,[z0,z1,z2,z4,z80,z742])],[(0,[z0,z127,z2,z4,z5,z6]),(0,[z0,z1,z2,z179,z41,z6])],[(0,[z0,z1,z2,z186,z285,z6])],[(0,[z0,z252,z2,z4,z5,z406]),(0,[z69,z1,z2,z4,z5,z60]),(0,[z117,z0,z1,z2,z73,z6]),(0,[z0,z1,z218,z179,z5,z6])],[(0,[z0,z1,z2,z971,z5,z6]),(0,[z529,z0,z1,z10,z2,z6]),(0,[z0,z1,z2,z972,z5,z6])],[(0,[z114,z343,z0,z1,z5,z6]),(0,[z81,z1,z2,z4,z5,z60]),(0,[z66,z0,z30,z186,z5,z6]),(0,[z539,z0,z127,z2,z5,z6]),(0,[z153,z0,z1,z289,z4,z6]),(0,[z178,z0,z1,z265,z4,z55])],[(0,[z8,z263,z1,z2,z5,z6]),(0,[z973,z0,z1,z2,z5,z6]),(0,[z0,z410,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z974,z6]),(0,[z247,z0,z1,z2,z4,z55]),(0,[z0,z87,z2,z4,z290,z6])],[(0,[z0,z1,z2,z4,z975,z6])]],
   [[(0,[z0,z252,z2,z4,z5,z57])],[(0,[z0,z1,z2,z976,z5,z6]),(0,[z247,z0,z1,z4,z5,z174])],[(0,[z0,z1,z2,z4,z977,z6]),(0,[z1,z4,z855,z97,z5,z6]),(0,[z0,z654,z83,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z978])],[(0,[z0,z1,z2,z132,z118,z6]),(0,[z100,z1,z166,z4,z5,z6]),(0,[z0,z1,z2,z4,z979,z6])],[(0,[z0,z1,z2,z980,z5,z6]),(0,[z102,z0,z127,z2,z41,z6]),(0,[z0,z1,z2,z4,z41,z929])],[(0,[z1,z2,z4,z92,z6,z60]),(0,[z801,z337,z2,z4,z5,z6]),(0,[z34,z35,z2,z4,z41,z6]),(0,[z0,z1,z2,z359,z41,z6]),(0,[z0,z1,z2,z4,z981,z6]),(0,[z102,z0,z1,z477,z5,z6])],[(0,[z0,z1,z211,z4,z5,z44]),(0,[z0,z1,z2,z982,z5,z6]),(0,[z0,z1,z10,z2,z4,z406]),(0,[z8,z1,z10,z2,z65,z6]),(0,[z0,z1,z2,z4,z220,z6]),(0,[z0,z1,z2,z983,z5,z6]),(0,[z0,z1,z27,z2,z4,z6]),(0,[z0,z410,z2,z4,z162,z6])],[(0,[z0,z1,z984,z4,z5,z6]),(0,[z242,z38,z2,z4,z5,z6])],[(0,[z1,z2,z4,z855,z5,z6]),(0,[z0,z1,z2,z154,z118,z6]),(0,[z0,z985,z2,z4,z5,z6]),(0,[z0,z1,z189,z2,z41,z6]),(0,[z88,z0,z1,z2,z187,z61]),(0,[z178,z0,z1,z2,z179,z55])],[(0,[z0,z1,z986,z4,z5,z6]),(0,[z98,z1,z552,z4,z5,z6]),(0,[z0,z252,z2,z65,z5,z6]),(0,[z0,z1,z2,z4,z5,z987]),(0,[z0,z1,z2,z31,z285,z6]),(0,[z78,z0,z2,z775,z5,z6]),(0,[z0,z1,z2,z217,z41,z6]),(0,[z0,z988,z2,z4,z5,z6])],[(0,[z32,z0,z120,z2,z4,z6])],[(0,[z0,z1,z10,z2,z4,z57]),(0,[z66,z0,z1,z479,z5,z6]),(0,[z178,z0,z1,z2,z4,z464])],[(0,[z0,z1,z2,z5,z6,z989]),(0,[z0,z279,z2,z4,z187,z6])],[(0,[z0,z64,z2,z4,z5,z6]),(0,[z35,z2,z4,z5,z6,z245]),(0,[z0,z1,z2,z4,z144,z406]),(0,[z0,z1,z2,z4,z5,z742])],[(0,[z678,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z990,z6]),(0,[z79,z0,z1,z71,z4,z6]),(0,[z0,z1,z235,z2,z41,z6])],[(0,[z0,z1,z2,z4,z991,z6]),(0,[z0,z1,z10,z2,z319,z6])]],
   [[(0,[z0,z283,z2,z4,z5,z6]),(0,[z8,z0,z1,z2,z41,z406])],[(0,[z0,z992,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z778,z6])],[(0,[z16,z1,z10,z4,z97,z6]),(0,[z0,z1,z2,z4,z144,z57]),(0,[z0,z993,z2,z4,z5,z6]),(0,[z0,z39,z641,z4,z5,z6])],[(0,[z0,z275,z2,z46,z5,z6]),(0,[z178,z0,z1,z2,z4,z326])],[(0,[z1,z2,z208,z5,z6,z60]),(0,[z100,z304,z2,z4,z5,z6])],[(0,[z0,z994,z2,z4,z5,z6]),(0,[z9,z1,z2,z41,z6,z60]),(0,[z0,z30,z2,z191,z5,z6]),(0,[z0,z1,z2,z4,z721,z6])],[(0,[z0,z1,z479,z97,z5,z6]),(0,[z0,z995,z2,z4,z5,z6]),(0,[z0,z1,z996,z2,z4,z6]),(0,[z0,z1,z2,z4,z997,z6]),(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z1,z136,z4,z41,z6])],[(0,[z0,z2,z4,z5,z6,z254]),(0,[z0,z1,z2,z4,z999,z6]),(0,[z225,z87,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z41,z406]),(0,[z0,z21,z2,z4,z28,z6]),(0,[z823,z0,z1,z200,z2,z6])],[(0,[z0,z1,z10,z2,z3,z6]),(0,[z8,z0,z1,z2,z940,z6]),(0,[z0,z1,z4,z722,z5,z6]),(0,[z0,z30,z2,z46,z5,z6])],[(0,[z45,z9,z1,z2,z41,z6]),(0,[z0,z120,z1,z2,z4,z6]),(0,[z0,z2,z4,z5,z813,z11]),(0,[z0,z1,z2,z4,z5,z813]),(0,[z0,z127,z10,z2,z4,z6]),(0,[z12,z0,z1,z571,z5,z174])],[(0,[z0,z1,z2,z743,z5,z6]),(0,[z0,z1,z382,z186,z5,z6]),(0,[z0,z1000,z2,z4,z5,z6]),(0,[z100,z1,z2,z4,z221,z6])],[(0,[z0,z1,z4,z855,z5,z6]),(0,[z1001,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z41,z57]),(0,[z0,z50,z2,z4,z118,z6]),(0,[z0,z1,z1002,z2,z4,z6]),(0,[z0,z1,z2,z20,z41,z6])],[(0,[z0,z1,z1003,z4,z5,z6]),(0,[z0,z1,z1004,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1005]),(0,[z130,z0,z2,z4,z5,z6]),(0,[z0,z1,z266,z97,z5,z6]),(0,[z0,z1006,z2,z4,z5,z6]),(0,[z1,z2,z4,z708,z5,z6]),(0,[z0,z1,z2,z41,z6,z542]),(0,[z0,z410,z10,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1007]),(0,[z0,z1,z1008,z2,z4,z6]),(0,[z1009,z0,z2,z4,z5,z6])],[(0,[z0,z1010,z2,z4,z5,z6]),(0,[z102,z0,z1,z562,z5,z6])],[(0,[z0,z1,z2,z4,z1011,z6]),(0,[z0,z1,z2,z1012,z5,z6]),(0,[z0,z2,z4,z5,z6,z1013]),(0,[z0,z21,z2,z4,z5,z105]),(0,[z0,z1,z2,z4,z1014,z6])],[(0,[z0,z2,z4,z157,z5,z6]),(0,[z1,z2,z4,z65,z5,z57])],[(0,[z286,z35,z2,z4,z5,z6]),(0,[z0,z1015,z2,z4,z5,z6])],[(0,[z0,z35,z89,z4,z5,z6]),(0,[z277,z1,z2,z4,z5,z411]),(0,[z0,z1,z2,z294,z41,z6]),(0,[z153,z0,z4,z31,z5,z6]),(0,[z383,z0,z1,z2,z41,z6])],[],[(0,[z0,z1,z2,z31,z41,z6]),(0,[z0,z1,z2,z4,z6,z1016]),(0,[z0,z127,z2,z4,z73,z6]),(0,[z277,z1,z2,z319,z5,z6])],[(0,[z0,z1,z2,z4,z6,z1017]),(0,[z131,z1,z2,z4,z340,z6]),(0,[z0,z1,z2,z1018,z5,z6]),(0,[z0,z1,z2,z1019,z5,z6]),(0,[z0,z1,z2,z1020,z5,z6])],[(0,[z0,z1,z2,z1021,z5,z6]),(0,[z0,z1,z2,z1022,z5,z6]),(0,[z178,z1,z2,z4,z28,z60]),(0,[z32,z0,z2,z4,z367,z6]),(0,[z0,z1,z2,z802,z5,z6])],[(0,[z1023,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z43,z41,z61])],[(0,[z0,z89,z4,z5,z6,z11]),(0,[z0,z1,z2,z4,z1024,z6]),(0,[z675,z0,z1,z71,z4,z6]),(0,[z0,z1,z4,z29,z6,z464]),(0,[z0,z1,z2,z4,z290,z6]),(0,[z0,z1,z740,z2,z43,z6])],[(0,[z0,z252,z2,z4,z223,z6]),(0,[z0,z127,z2,z4,z41,z6]),(0,[z12,z0,z1,z547,z5,z174])],[(0,[z0,z1025,z2,z4,z5,z6]),(0,[z0,z39,z4,z722,z5,z6]),(0,[z0,z1,z2,z191,z41,z6]),(0,[z0,z1,z2,z43,z167,z106])],[(0,[z0,z38,z2,z208,z5,z6]),(0,[z1026,z0,z1,z4,z5,z6]),(0,[z0,z64,z10,z2,z4,z6]),(0,[z0,z1,z1027,z2,z4,z6])],[]],
   [[(0,[z45,z1,z89,z4,z5,z6]),(0,[z171,z1,z2,z4,z5,z6]),(0,[z178,z0,z1,z2,z4,z554]),(0,[z0,z1,z2,z4,z1028,z6])],[(0,[z14,z108,z2,z4,z5,z6]),(0,[z0,z64,z4,z97,z5,z6]),(0,[z0,z64,z2,z4,z241,z6]),(0,[z0,z283,z10,z2,z4,z6]),(0,[z0,z87,z2,z4,z5,z6]),(0,[z0,z1,z2,z46,z41,z6]),(0,[z0,z410,z2,z4,z41,z6])],[(0,[z0,z1,z519,z186,z5,z6]),(0,[z0,z1,z2,z4,z1029,z6]),(0,[z9,z1,z2,z133,z5,z6]),(0,[z1030,z0,z1,z2,z5,z6])],[(0,[z1031,z0,z2,z4,z5,z6]),(0,[z32,z0,z1,z218,z4,z6]),(0,[z0,z1032,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z347,z6]),(0,[z12,z13,z1,z4,z5,z174])],[(0,[z673,z0,z2,z4,z5,z11])],[(0,[z0,z1,z2,z7,z282,z6]),(0,[z171,z1,z2,z4,z5,z106])],[(0,[z0,z1,z2,z4,z1033,z6]),(0,[z0,z1,z2,z179,z6,z55])],[(0,[z0,z1,z10,z2,z630,z6]),(0,[z0,z1,z463,z2,z41,z6]),(0,[z0,z120,z21,z2,z4,z6])],[],[(0,[z0,z1,z2,z4,z1034,z6]),(0,[z0,z1,z2,z4,z357,z6]),(0,[z1035,z1,z2,z4,z5,z6]),(0,[z0,z87,z2,z4,z162,z6]),(0,[z0,z1,z2,z4,z5,z875])],[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z88,z0,z1,z2,z5,z752])],[(0,[z0,z70,z2,z7,z5,z6]),(0,[z0,z1,z1037,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1038]),(0,[z729,z0,z1,z210,z5,z6])],[(0,[z1039,z0,z1,z2,z5,z6]),(0,[z0,z39,z129,z4,z5,z6]),(0,[z555,z1,z2,z65,z5,z6]),(0,[z0,z120,z1,z2,z4,z60]),(0,[z0,z1,z2,z4,z1040,z6])],[(0,[z0,z1041,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1042,z6])],[(0,[z153,z0,z1,z46,z41,z6]),(0,[z40,z0,z2,z4,z41,z11])]],
   [[(0,[z0,z1,z2,z4,z1043,z6]),(0,[z0,z64,z2,z4,z41,z6]),(0,[z0,z70,z2,z4,z282,z6]),(0,[z130,z0,z10,z2,z4,z6]),(0,[z0,z1,z2,z440,z41,z6]),(0,[z0,z1,z2,z584,z41,z6])],[(0,[z16,z1,z7,z97,z5,z6]),(0,[z8,z1,z192,z65,z5,z6]),(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z2,z4,z1045,z6]),(0,[z0,z1,z62,z547,z5,z6]),(0,[z0,z1,z2,z4,z1046,z6])],[(0,[z0,z1,z1047,z2,z4,z6]),(0,[z0,z1,z325,z186,z5,z6]),(0,[z146,z0,z1,z2,z223,z6]),(0,[z8,z1,z2,z779,z5,z6]),(0,[z0,z1,z2,z4,z1048,z6])],[(0,[z1049,z0,z1,z4,z5,z6]),(0,[z0,z1,z10,z2,z609,z6]),(0,[z0,z283,z2,z4,z41,z6])],[(0,[z0,z1,z2,z4,z6,z1050]),(0,[z0,z1,z2,z1051,z5,z6]),(0,[z0,z122,z1,z218,z4,z6]),(0,[z0,z279,z136,z4,z5,z6])],[(0,[z1052,z1,z2,z4,z5,z6]),(0,[z0,z1,z217,z5,z41,z6])],[(0,[z0,z1,z2,z4,z5,z1053]),(0,[z0,z1,z1054,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1055,z6]),(0,[z153,z0,z1,z4,z357,z6])],[(0,[z88,z0,z1,z10,z2,z61]),(0,[z0,z1,z136,z5,z6,z61])],[(0,[z0,z1,z2,z4,z273,z6]),(0,[z102,z0,z1,z2,z167,z6]),(0,[z0,z1,z2,z4,z5,z1056])],[(0,[z0,z1,z436,z2,z41,z6])],[(0,[z460,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z1057,z6]),(0,[z0,z1,z2,z1058,z5,z6]),(0,[z0,z1,z2,z525,z41,z6]),(0,[z1059,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z1060])],[(0,[z0,z30,z2,z46,z41,z6]),(0,[z1061,z0,z1,z2,z5,z6])],[(0,[z415,z1,z4,z97,z5,z6]),(0,[z0,z1,z54,z2,z41,z6]),(0,[z66,z0,z549,z4,z5,z6])],[(0,[z32,z0,z2,z4,z33,z6]),(0,[z0,z1000,z2,z4,z41,z6])],[(0,[z0,z1,z1062,z4,z5,z6]),(0,[z178,z0,z1,z2,z4,z466]),(0,[z0,z1,z2,z4,z1063,z6])]],
   [[(0,[z0,z1,z2,z4,z1064,z6]),(0,[z0,z1,z2,z4,z5,z59]),(0,[z0,z1,z1065,z2,z4,z6]),(0,[z0,z1,z2,z41,z6,z656])],[(0,[z8,z1,z232,z65,z5,z6]),(0,[z1,z2,z4,z1066,z5,z6]),(0,[z729,z0,z1,z4,z5,z6]),(0,[z171,z1,z10,z2,z4,z6])],[(0,[z130,z0,z2,z4,z41,z6]),(0,[z178,z0,z1,z2,z4,z636]),(0,[z1067,z1,z2,z4,z5,z6]),(0,[z0,z87,z10,z2,z4,z6])],[(0,[z131,z0,z1,z2,z132,z6]),(0,[z0,z1,z2,z4,z1068,z6]),(0,[z0,z1,z2,z4,z297,z6]),(0,[z164,z0,z2,z4,z367,z6])],[(0,[z0,z1,z2,z4,z5,z1069]),(0,[z79,z0,z1,z218,z4,z6]),(0,[z225,z1,z2,z4,z290,z6]),(0,[z0,z1,z2,z41,z6,z504])],[(0,[z16,z1,z4,z855,z5,z6]),(0,[z0,z1,z2,z43,z5,z481])],[(0,[z130,z45,z2,z4,z5,z6]),(0,[z0,z1,z2,z46,z285,z6]),(0,[z88,z0,z304,z2,z5,z61])],[(0,[z0,z1,z1070,z4,z5,z6]),(0,[z78,z0,z10,z2,z31,z6]),(0,[z0,z1071,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z353,z11]),(0,[z8,z0,z1,z2,z41,z57]),(0,[z0,z1,z1072,z4,z5,z6]),(0,[z0,z1,z2,z315,z6,z61])],[(0,[z0,z83,z89,z4,z5,z6]),(0,[z0,z1,z2,z4,z482,z80]),(0,[z0,z1,z2,z4,z340,z105]),(0,[z0,z1,z2,z4,z315,z6]),(0,[z0,z1,z186,z41,z6,z174]),(1,[z0,z1,z4,z5,z875]),(0,[z0,z1,z2,z4,z6,z1073])],[(0,[z146,z0,z1,z10,z2,z6]),(0,[z114,z102,z0,z135,z5,z6]),(0,[z0,z1,z2,z378,z41,z6])],[(0,[z0,z1,z2,z41,z6,z523]),(0,[z305,z0,z1,z2,z41,z6])],[(0,[z619,z0,z4,z121,z5,z6]),(0,[z0,z2,z4,z5,z6,z1074]),(0,[z0,z1,z192,z5,z41,z6]),(0,[z9,z1,z2,z335,z5,z6]),(0,[z277,z1,z2,z4,z28,z6]),(0,[z0,z2,z4,z41,z6,z254]),(0,[z1075,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1076]),(0,[z0,z1,z136,z43,z5,z6])],[(0,[z0,z1,z2,z179,z5,z105]),(0,[z1077,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1078,z5,z6]),(0,[z0,z1,z2,z4,z6,z1079])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z130,z0,z4,z186,z5,z6]),(0,[z0,z1,z1080,z2,z4,z6]),(0,[z0,z1081,z2,z4,z5,z6])],[(0,[z343,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z940,z41,z6]),(0,[z0,z1,z10,z2,z479,z6])]],
   [[(0,[z0,z1,z2,z4,z1082,z6]),(0,[z1,z2,z4,z97,z5,z59]),(0,[z0,z1,z1083,z4,z5,z6])],[(0,[z8,z0,z1,z2,z90,z6])],[(0,[z0,z1,z89,z4,z5,z44])],[(0,[z0,z1,z2,z1084,z5,z6]),(0,[z171,z1,z2,z4,z41,z6])],[(0,[z0,z143,z2,z4,z5,z6]),(0,[z0,z38,z2,z4,z92,z6]),(0,[z0,z1,z2,z4,z1085,z6]),(0,[z0,z1,z2,z4,z1086,z6]),(0,[z114,z102,z0,z1,z315,z6]),(0,[z0,z87,z2,z4,z41,z6]),(0,[z327,z1,z2,z179,z5,z6])],[(0,[z0,z1,z2,z4,z1087,z6]),(0,[z0,z1,z281,z186,z5,z6])],[(0,[z0,z1,z2,z41,z6,z698]),(0,[z102,z0,z135,z2,z41,z6]),(0,[z0,z1,z2,z4,z162,z6]),(0,[z12,z225,z1,z4,z5,z174])],[(0,[z0,z1,z2,z4,z1088,z6]),(0,[z0,z1,z2,z4,z5,z1089]),(0,[z0,z1090,z2,z4,z5,z6]),(0,[z0,z1,z17,z479,z5,z6]),(0,[z0,z1,z2,z4,z52,z280]),(0,[z229,z0,z51,z2,z4,z6])],[(0,[z14,z48,z2,z4,z5,z6]),(0,[z455,z1,z17,z4,z5,z6])],[(0,[z0,z337,z89,z4,z5,z6]),(0,[z0,z1,z2,z4,z1091,z6]),(0,[z0,z1,z2,z4,z90,z6]),(0,[z78,z0,z2,z31,z5,z6]),(0,[z114,z102,z0,z1,z5,z6])],[(0,[z16,z64,z4,z97,z5,z6]),(0,[z0,z1,z2,z1092,z5,z6]),(0,[z109,z0,z1,z2,z132,z6]),(0,[z0,z1,z2,z1093,z5,z6])],[(0,[z0,z1094,z2,z4,z5,z6]),(0,[z0,z1,z217,z36,z5,z6])],[(0,[z292,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z1095,z6]),(0,[z153,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z756,z6,z11]),(0,[z1096,z1,z2,z4,z5,z6]),(0,[z88,z0,z1,z136,z5,z61])],[(0,[z0,z1,z2,z1097,z5,z6]),(0,[z0,z1098,z2,z4,z5,z6]),(0,[z74,z0,z1,z10,z2,z6]),(0,[z0,z1,z2,z41,z6,z22]),(0,[z0,z1,z235,z2,z43,z106])],[(0,[z0,z1,z2,z266,z1099,z6]),(0,[z0,z30,z10,z2,z46,z6]),(0,[z155,z0,z1,z2,z41,z6])],[(0,[z0,z1,z2,z4,z1100,z6]),(0,[z0,z1,z1101,z2,z4,z6]),(0,[z0,z1,z1102,z2,z4,z6]),(0,[z0,z1,z2,z389,z41,z6]),(0,[z0,z1,z201,z318,z4,z6])]],
   [[(0,[z114,z102,z0,z127,z5,z6])],[(0,[z0,z1,z10,z2,z4,z59]),(0,[z0,z1,z1103,z2,z4,z6]),(0,[z539,z0,z2,z31,z5,z6]),(0,[z0,z2,z46,z775,z5,z6]),(0,[z0,z1,z2,z4,z6,z1104]),(0,[z0,z1,z1105,z2,z4,z6])],[(0,[z242,z1,z2,z4,z5,z6]),(0,[z0,z1106,z2,z4,z5,z6]),(0,[z1107,z0,z1,z2,z5,z6]),(0,[z0,z1,z10,z834,z2,z6]),(0,[z277,z465,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1108,z6]),(0,[z0,z670,z2,z31,z5,z6]),(0,[z1109,z1,z2,z4,z5,z6]),(0,[z0,z1,z10,z136,z4,z6])],[(0,[z0,z252,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z241,z59]),(0,[z0,z1110,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z712,z6])],[(0,[z0,z1,z2,z7,z5,z274]),(0,[z1,z2,z4,z25,z5,z60]),(0,[z0,z1,z329,z2,z41,z6]),(0,[z0,z1,z166,z4,z187,z6])],[(0,[z0,z1111,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1112]),(0,[z539,z0,z39,z83,z5,z6]),(0,[z0,z1,z1113,z4,z5,z6]),(0,[z0,z1,z2,z4,z1114,z6]),(0,[z277,z21,z2,z4,z5,z6])],[(0,[z1115,z0,z1,z2,z5,z6]),(0,[z0,z1,z10,z192,z4,z6]),(0,[z0,z1,z2,z4,z1116,z6]),(0,[z0,z1,z320,z2,z41,z6])],[(0,[z0,z1,z2,z4,z1117,z6]),(0,[z0,z1071,z10,z2,z4,z6]),(0,[z88,z0,z1,z2,z5,z61])],[(0,[z8,z9,z1,z2,z41,z6]),(0,[z0,z1,z303,z2,z479,z6]),(0,[z102,z729,z0,z1,z5,z6]),(0,[z0,z1,z4,z5,z6,z875]),(0,[z0,z1,z200,z2,z778,z6]),(0,[z0,z348,z2,z4,z68,z6])],[(0,[z0,z1,z2,z4,z282,z274])],[(0,[z66,z0,z10,z4,z121,z6]),(0,[z0,z1,z2,z4,z1118,z6])],[(0,[z0,z279,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1119,z6]),(0,[z1120,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z752,z61])],[(0,[z0,z1,z2,z4,z1121,z6]),(0,[z0,z1122,z2,z4,z5,z6]),(0,[z0,z410,z2,z547,z5,z6])],[(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z1,z2,z4,z5,z1123]),(0,[z0,z2,z4,z1124,z5,z6]),(0,[z0,z1,z2,z41,z6,z104]),(0,[z0,z39,z1,z186,z41,z6]),(0,[z0,z1,z2,z4,z1125,z6])],[(0,[z14,z337,z2,z4,z5,z6]),(0,[z0,z1,z10,z2,z4,z6]),(0,[z300,z1,z2,z4,z5,z60]),(0,[z0,z1,z2,z1126,z5,z6]),(0,[z0,z1,z1127,z4,z5,z6]),(0,[z0,z1,z75,z2,z179,z6]),(0,[z0,z1,z834,z2,z4,z6]),(0,[z88,z171,z1,z2,z5,z61])]],
   [[(0,[z0,z1,z2,z4,z1128,z6]),(0,[z0,z70,z2,z4,z5,z274]),(0,[z0,z1,z2,z4,z5,z1129]),(0,[z13,z410,z2,z4,z5,z6])],[(0,[z8,z0,z1,z192,z41,z6]),(0,[z0,z1,z10,z2,z532,z6])],[(0,[z34,z2,z4,z601,z5,z6]),(0,[z0,z1,z2,z4,z241,z6]),(0,[z0,z1,z192,z36,z5,z6]),(0,[z0,z1,z2,z382,z41,z6]),(0,[z242,z2,z4,z5,z6,z11]),(0,[z114,z102,z0,z1,z10,z6]),(0,[z0,z1,z136,z4,z221,z6])],[(0,[z0,z1,z2,z4,z41,z59]),(0,[z178,z0,z1,z2,z132,z6]),(0,[z0,z1,z2,z41,z6,z618]),(0,[z0,z1,z1130,z2,z4,z6]),(0,[z0,z2,z4,z33,z721,z6]),(0,[z0,z1,z2,z4,z5,z1131])],[(0,[z0,z1,z2,z208,z273,z6]),(0,[z0,z1,z480,z186,z5,z6]),(0,[z453,z0,z1,z2,z5,z61])],[(0,[z0,z143,z10,z2,z4,z6]),(0,[z1132,z0,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1133,z6]),(0,[z0,z1,z2,z659,z41,z6]),(0,[z0,z1,z2,z4,z144,z6]),(0,[z0,z30,z1,z217,z5,z6]),(0,[z0,z1,z10,z217,z4,z6]),(0,[z0,z304,z2,z4,z187,z6])],[(0,[z225,z1,z2,z4,z5,z6]),(0,[z0,z1134,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1135,z6]),(0,[z1136,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1137,z4,z5,z6]),(0,[z0,z1,z2,z4,z1138,z6]),(0,[z0,z283,z2,z4,z5,z11]),(0,[z539,z0,z1,z2,z220,z6]),(0,[z0,z2,z4,z721,z5,z6]),(0,[z0,z1,z265,z4,z5,z6]),(0,[z0,z1139,z2,z4,z5,z6])],[(0,[z0,z801,z2,z4,z5,z6]),(0,[z146,z0,z1,z2,z5,z6]),(1,[z0,z1,z2,z743,z6]),(0,[z0,z1,z2,z4,z147,z6])],[(0,[z0,z1,z1140,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z1141]),(0,[z66,z0,z4,z722,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1142]),(0,[z0,z1,z2,z4,z1143,z6]),(0,[z0,z143,z2,z4,z144,z6]),(0,[z570,z1,z2,z4,z28,z6]),(0,[z117,z0,z1,z289,z2,z6]),(0,[z0,z1,z2,z4,z73,z6])],[(0,[z0,z1,z1144,z4,z5,z6]),(1,[z1,z4,z855,z5,z6]),(0,[z1,z2,z4,z340,z28,z6])],[(0,[z0,z1,z2,z4,z5,z1145]),(0,[z1146,z0,z2,z4,z5,z6]),(0,[z0,z1,z1147,z4,z5,z6]),(0,[z0,z1,z2,z41,z6,z650]),(1,[z0,z1,z2,z5,z752])],[(0,[z0,z1,z1148,z2,z4,z6]),(0,[z9,z1,z2,z335,z41,z6]),(0,[z0,z1,z593,z2,z41,z6]),(0,[z0,z1,z2,z4,z5,z1149]),(0,[z225,z1,z2,z4,z162,z6])]],
   [[(0,[z0,z1,z2,z4,z1150,z6]),(0,[z0,z1,z485,z186,z5,z6])],[(0,[z0,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z5,z1151]),(0,[z0,z1,z2,z4,z5,z1152]),(0,[z0,z463,z83,z4,z5,z6]),(0,[z171,z279,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1153]),(0,[z0,z1154,z2,z4,z5,z6]),(0,[z0,z1,z519,z2,z41,z6]),(0,[z1155,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z1156,z5,z6])],[(0,[z0,z1,z2,z4,z1157,z6]),(0,[z178,z0,z1,z2,z546,z6]),(0,[z0,z1,z218,z4,z5,z6]),(0,[z0,z1158,z2,z4,z5,z6])],[(0,[z1159,z1,z2,z4,z5,z6]),(0,[z0,z1160,z2,z4,z5,z6])],[(0,[z0,z1161,z2,z4,z5,z6]),(0,[z0,z252,z10,z2,z4,z6]),(0,[z8,z1,z2,z65,z5,z406]),(0,[z78,z0,z2,z31,z147,z6]),(0,[z0,z1,z2,z116,z41,z6])],[(0,[z0,z1,z2,z1162,z5,z6]),(0,[z0,z1,z2,z179,z28,z6]),(0,[z1163,z1,z2,z4,z5,z6])],[(0,[z0,z143,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z1164,z6]),(0,[z114,z102,z0,z1,z73,z6])],[],[(0,[z0,z1,z2,z208,z5,z6]),(0,[z0,z1,z1165,z4,z5,z6]),(0,[z0,z2,z4,z157,z41,z6]),(0,[z0,z1,z303,z2,z4,z6]),(0,[z66,z0,z2,z31,z41,z6]),(1,[z0,z2,z775,z5,z6]),(0,[z40,z0,z120,z2,z4,z11]),(0,[z0,z1,z2,z4,z1166,z6]),(0,[z178,z0,z1,z2,z4,z650])],[(0,[z0,z1,z1167,z4,z5,z6]),(0,[z0,z1,z307,z2,z4,z6]),(0,[z8,z1,z2,z65,z5,z57]),(0,[z0,z1,z2,z4,z5,z1168]),(0,[z0,z1,z2,z4,z324,z149])],[(0,[z1169,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z266,z282,z6]),(0,[z16,z1,z266,z97,z5,z6]),(0,[z0,z30,z289,z2,z46,z6])],[(0,[z0,z1,z112,z186,z5,z6]),(0,[z0,z1,z2,z4,z1170,z6]),(0,[z78,z0,z2,z31,z41,z6]),(0,[z1171,z1,z2,z4,z5,z6]),(0,[z114,z102,z0,z1,z41,z6]),(0,[z12,z0,z1,z200,z4,z174]),(0,[z0,z1,z2,z706,z41,z6])],[(0,[z74,z0,z1,z2,z5,z6]),(0,[z1172,z1,z2,z4,z5,z6]),(0,[z1120,z1,z10,z2,z4,z6])],[(0,[z0,z1,z10,z211,z4,z6]),(0,[z298,z0,z1,z2,z41,z6]),(0,[z0,z39,z83,z4,z220,z6]),(0,[z0,z1,z1173,z2,z4,z6]),(0,[z0,z348,z2,z4,z118,z6]),(0,[z0,z2,z4,z5,z95,z813]),(0,[z0,z87,z2,z571,z5,z6])],[(0,[z0,z1,z10,z2,z208,z6]),(0,[z153,z0,z1,z4,z41,z6]),(0,[z0,z1,z2,z4,z1174,z6]),(0,[z1175,z1,z2,z4,z5,z6])]],
   [[(0,[z14,z337,z10,z2,z4,z6]),(0,[z0,z1,z834,z2,z5,z6])],[(0,[z0,z1,z2,z4,z1176,z6]),(0,[z0,z70,z2,z266,z5,z6]),(0,[z0,z1,z2,z1177,z5,z6]),(0,[z700,z1,z2,z4,z28,z6])],[],[(0,[z130,z0,z83,z4,z5,z6]),(0,[z0,z1178,z2,z4,z5,z6]),(0,[z0,z1179,z2,z4,z5,z6])],[(0,[z0,z1,z1180,z4,z5,z6]),(0,[z0,z1,z262,z4,z29,z6]),(0,[z0,z1,z2,z4,z1181,z6]),(0,[z0,z1,z1182,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1183,z6]),(0,[z0,z1,z2,z3,z273,z6]),(0,[z0,z1,z200,z2,z4,z6]),(0,[z0,z1184,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1185,z6]),(0,[z0,z1,z2,z195,z41,z6]),(0,[z0,z1,z751,z4,z5,z6])],[(0,[z0,z1,z2,z4,z52,z377])],[(0,[z0,z1,z2,z4,z1186,z6]),(0,[z0,z1,z2,z73,z41,z6]),(0,[z1187,z1,z2,z4,z5,z6]),(0,[z225,z1,z10,z2,z4,z6]),(0,[z81,z0,z1,z2,z41,z6])],[(0,[z0,z1,z2,z4,z1188,z6]),(0,[z0,z1,z2,z4,z1189,z6]),(0,[z1136,z1,z10,z2,z4,z6])],[(0,[z0,z1,z2,z4,z1190,z6]),(0,[z383,z1,z2,z65,z5,z6]),(0,[z102,z0,z1,z2,z297,z6])],[(0,[z420,z1,z2,z4,z28,z6]),(0,[z0,z1,z10,z2,z123,z6]),(0,[z88,z0,z1,z2,z41,z61])],[(0,[z9,z1,z2,z779,z5,z6]),(0,[z0,z1,z2,z4,z1191,z6]),(0,[z0,z1,z2,z479,z220,z6]),(0,[z0,z465,z2,z179,z5,z6])],[(0,[z14,z337,z2,z4,z273,z6]),(0,[z16,z1,z4,z97,z5,z59]),(0,[z0,z1,z2,z4,z5,z1192]),(0,[z277,z1,z2,z4,z340,z6]),(0,[z1193,z0,z1,z2,z5,z6]),(0,[z229,z0,z2,z4,z33,z6]),(0,[z0,z1,z2,z4,z1194,z6]),(0,[z684,z0,z1,z2,z41,z6]),(0,[z0,z1,z10,z2,z374,z6]),(0,[z13,z1,z2,z4,z290,z6])],[(0,[z0,z1,z2,z1195,z5,z6]),(0,[z0,z410,z2,z571,z5,z6])],[(0,[z0,z1196,z1,z2,z4,z6])]],
   [[(0,[z1197,z0,z1,z2,z4,z6]),(0,[z0,z87,z2,z547,z5,z6]),(0,[z0,z21,z2,z179,z5,z6])],[(0,[z539,z0,z1,z10,z2,z6]),(0,[z0,z2,z4,z1124,z41,z6])],[(0,[z14,z337,z2,z4,z41,z6])],[(0,[z0,z1,z4,z5,z6,z1198]),(0,[z0,z1,z2,z4,z1199,z6]),(0,[z1200,z1,z2,z4,z5,z6]),(0,[z13,z87,z2,z4,z5,z6])],[(0,[z0,z1,z4,z5,z99,z875])],[(0,[z0,z1,z2,z5,z41,z57]),(0,[z12,z0,z1,z4,z5,z875])],[(0,[z0,z1,z2,z4,z1201,z6]),(0,[z1202,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z285,z6])],[(0,[z0,z1,z2,z4,z5,z1203]),(0,[z1204,z1,z2,z4,z5,z6]),(0,[z453,z0,z1,z2,z41,z61])],[(0,[z0,z1,z2,z4,z946,z6]),(0,[z0,z1,z2,z4,z1205,z6]),(0,[z0,z1,z2,z41,z60,z61]),(0,[z358,z0,z4,z121,z5,z6]),(0,[z0,z1,z71,z751,z4,z6])],[(0,[z0,z2,z31,z41,z6,z11])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z14,z337,z2,z208,z5,z6]),(0,[z225,z1,z2,z4,z41,z6]),(0,[z0,z1,z2,z4,z6,z742])],[(0,[z16,z1,z4,z97,z5,z6]),(0,[z868,z0,z1,z2,z340,z6])],[(0,[z521,z1,z2,z4,z5,z60]),(0,[z0,z122,z2,z123,z118,z6]),(0,[z0,z1,z265,z4,z41,z6])],[(0,[z0,z1,z2,z4,z1206,z6]),(0,[z0,z1015,z2,z4,z5,z411]),(0,[z146,z0,z1,z2,z41,z6])],[(0,[z0,z1,z2,z4,z1207,z6]),(0,[z0,z1,z1208,z4,z5,z6]),(0,[z79,z0,z1,z4,z6,z330]),(0,[z0,z304,z136,z4,z5,z6])],[(0,[z0,z1,z2,z1209,z5,z6]),(0,[z0,z1,z1210,z2,z4,z6]),(0,[z0,z30,z2,z641,z5,z6]),(0,[z0,z1,z2,z4,z1211,z6]),(0,[z0,z1,z922,z2,z4,z6]),(0,[z0,z1212,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z15]),(0,[z0,z1,z10,z89,z4,z6]),(0,[z102,z0,z1,z2,z90,z6])],[(0,[z0,z1,z2,z1213,z5,z6]),(0,[z78,z0,z2,z31,z285,z6]),(0,[z1214,z0,z1,z4,z5,z6])],[(0,[z0,z1,z2,z1215,z5,z6]),(0,[z0,z1,z1216,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1217,z6]),(0,[z40,z0,z2,z4,z42,z11]),(0,[z0,z1,z485,z186,z41,z6])],[(0,[z14,z2,z4,z5,z60,z11]),(0,[z0,z1218,z2,z4,z5,z6]),(0,[z567,z0,z2,z4,z5,z11]),(0,[z0,z1,z2,z4,z785,z6]),(0,[z0,z127,z2,z5,z41,z6]),(0,[z0,z1,z751,z75,z4,z6])],[],[(0,[z0,z38,z89,z4,z5,z6]),(0,[z8,z1,z2,z65,z223,z6]),(0,[z0,z1,z1219,z4,z5,z6]),(0,[z0,z1,z10,z265,z4,z6])],[(0,[z34,z801,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1220]),(0,[z0,z1,z200,z2,z4,z60])],[(0,[z0,z1,z2,z1221,z5,z6]),(0,[z0,z1,z2,z1222,z5,z6]),(0,[z1223,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1224,z6]),(0,[z0,z1,z2,z5,z6,z752])],[(0,[z117,z0,z252,z2,z5,z6]),(0,[z0,z2,z4,z5,z6,z1225]),(0,[z0,z1,z2,z4,z6,z1226]),(0,[z0,z1,z1227,z2,z4,z6]),(0,[z0,z1,z845,z4,z5,z6]),(0,[z100,z1,z2,z4,z187,z6])],[(0,[z0,z1,z218,z4,z72,z6]),(0,[z1228,z1,z2,z4,z5,z6]),(0,[z0,z1,z62,z4,z5,z99]),(0,[z178,z0,z1,z218,z4,z55])],[(0,[z153,z0,z1,z10,z4,z6]),(0,[z1229,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z73,z6])],[(0,[z0,z1,z2,z208,z41,z6]),(0,[z0,z1,z2,z4,z5,z1230]),(0,[z8,z0,z1,z2,z41,z6]),(0,[z0,z1,z217,z65,z5,z6]),(0,[z0,z1231,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1232,z6]),(0,[z0,z1,z2,z213,z41,z6]),(0,[z0,z1,z2,z4,z6,z1233])],[(0,[z0,z1,z2,z208,z1157,z6]),(0,[z0,z1,z2,z41,z6,z161]),(0,[z0,z1,z2,z1234,z5,z6])],[(0,[z0,z1,z2,z4,z92,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1235]),(0,[z0,z1236,z2,z4,z5,z6]),(0,[z212,z1,z2,z4,z5,z60]),(0,[z0,z1,z2,z4,z1237,z6]),(0,[z0,z1,z2,z4,z6,z1238]),(0,[z74,z0,z1,z2,z41,z6]),(0,[z1172,z1,z2,z4,z41,z6])],[(0,[z0,z1,z2,z1239,z5,z6]),(0,[z0,z1,z2,z1240,z5,z6]),(0,[z684,z1,z2,z36,z5,z6]),(0,[z1241,z0,z1,z2,z5,z6]),(0,[z0,z1,z10,z2,z179,z6])],[(0,[z0,z1,z811,z2,z7,z6]),(0,[z0,z1,z1242,z4,z5,z6]),(0,[z0,z1243,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1244,z6]),(0,[z0,z1,z2,z4,z1245,z6]),(0,[z32,z0,z2,z4,z6,z185]),(0,[z1246,z1,z2,z4,z5,z6])],[(0,[z14,z380,z2,z4,z5,z6]),(0,[z0,z1,z1247,z4,z5,z6]),(0,[z0,z1,z10,z2,z41,z6]),(0,[z0,z1,z834,z2,z41,z6])],[(0,[z0,z1,z2,z4,z1248,z6]),(0,[z0,z1249,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1250,z6]),(0,[z284,z0,z1,z2,z41,z6]),(0,[z183,z1,z194,z2,z4,z6])],[(0,[z45,z0,z1,z2,z743,z6]),(0,[z0,z1,z2,z4,z783,z6])],[(0,[z0,z1,z451,z186,z5,z6]),(0,[z242,z1,z10,z2,z4,z6]),(0,[z0,z1251,z2,z4,z5,z6])],[(0,[z242,z1,z2,z4,z5,z60]),(0,[z1,z2,z4,z5,z6,z1252]),(0,[z0,z1,z2,z641,z41,z6]),(0,[z0,z1,z547,z5,z6,z174])],[(0,[z0,z1,z2,z4,z1253,z6]),(0,[z0,z10,z2,z4,z157,z6]),(0,[z0,z1254,z2,z4,z5,z6]),(0,[z0,z1,z2,z159,z41,z6]),(0,[z0,z120,z2,z4,z118,z6])],[],[],[(0,[z14,z337,z2,z3,z5,z6]),(0,[z0,z1,z2,z266,z5,z274]),(0,[z0,z1,z10,z2,z266,z6]),(1,[z0,z252,z2,z41,z6]),(0,[z597,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z571,z290,z6])],[(0,[z0,z1,z2,z43,z5,z106])],[(0,[z0,z1,z2,z546,z5,z6]),(0,[z0,z1,z2,z547,z5,z6])],[(0,[z0,z1,z2,z4,z1255,z6]),(0,[z1256,z1,z2,z4,z5,z6])],[(0,[z16,z1,z4,z97,z241,z6]),(0,[z0,z252,z2,z4,z144,z6]),(0,[z0,z10,z2,z4,z6,z254]),(0,[z591,z0,z1,z2,z41,z6]),(0,[z0,z1,z2,z4,z5,z1257]),(0,[z79,z0,z1,z200,z4,z6])]],
   [[(0,[z13,z1,z2,z4,z5,z6]),(0,[z78,z0,z1,z217,z5,z6]),(0,[z0,z1,z2,z4,z1258,z6]),(0,[z12,z0,z410,z4,z5,z174]),(0,[z0,z279,z10,z2,z4,z6])],[(0,[z0,z1,z10,z2,z4,z15]),(0,[z14,z337,z2,z4,z5,z15]),(0,[z0,z38,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z1259,z6]),(0,[z539,z0,z1,z2,z5,z6]),(0,[z0,z51,z1,z2,z41,z6])],[(0,[z0,z1,z2,z4,z5,z1260])],[(0,[z0,z1,z2,z5,z6,z1261]),(0,[z0,z1,z192,z65,z5,z6]),(0,[z564,z1,z2,z4,z28,z6]),(0,[z0,z1,z4,z5,z875,z174]),(0,[z0,z1,z2,z4,z6,z1262])],[(0,[z412,z1,z4,z97,z5,z6]),(0,[z0,z1,z2,z1263,z5,z6]),(0,[z0,z1,z2,z779,z5,z6])],[(0,[z0,z1,z2,z4,z1264,z6]),(0,[z0,z1,z2,z4,z80,z622]),(0,[z0,z1,z2,z221,z6,z61])],[(0,[z0,z1265,z2,z4,z5,z6]),(0,[z246,z0,z1,z186,z5,z6]),(0,[z0,z1,z137,z2,z41,z6])],[(0,[z0,z1266,z2,z4,z5,z6])],[(0,[z1267,z0,z1,z4,z5,z6]),(0,[z242,z1,z2,z4,z41,z6]),(0,[z102,z0,z1,z2,z41,z6]),(0,[z13,z1,z2,z4,z162,z6]),(0,[z0,z1,z1268,z4,z5,z6])],[(0,[z0,z1,z1269,z2,z4,z6]),(0,[z1,z2,z4,z5,z6,z1270]),(0,[z117,z0,z127,z2,z5,z6])],[(0,[z0,z252,z2,z4,z41,z6]),(0,[z0,z127,z2,z36,z5,z6]),(0,[z82,z1,z2,z4,z5,z60]),(0,[z288,z0,z2,z4,z5,z11]),(0,[z0,z1,z822,z2,z4,z6]),(0,[z0,z1,z2,z1271,z5,z6])],[(0,[z0,z1,z1272,z4,z5,z6]),(0,[z0,z1,z1148,z2,z266,z6]),(0,[z0,z1,z2,z1273,z5,z6]),(0,[z0,z1,z2,z4,z72,z411])],[(0,[z0,z1,z2,z4,z1274,z6]),(0,[z0,z1275,z2,z4,z5,z6]),(0,[z0,z1276,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1277,z5,z6]),(0,[z0,z1,z2,z3,z41,z6]),(0,[z0,z2,z4,z5,z6,z1278]),(0,[z0,z1279,z2,z4,z5,z6]),(0,[z0,z1280,z2,z4,z5,z6]),(0,[z0,z1,z751,z4,z29,z6]),(0,[z0,z1,z2,z547,z290,z6])],[(0,[z0,z1,z2,z4,z273,z15]),(0,[z0,z1,z2,z1281,z5,z6]),(0,[z242,z1,z2,z4,z1164,z6]),(0,[z564,z1,z2,z4,z356,z6])],[(0,[z1,z89,z4,z5,z6,z60]),(0,[z0,z1,z2,z1282,z5,z6]),(0,[z0,z1,z2,z4,z1283,z6]),(0,[z1,z2,z4,z708,z28,z6]),(0,[z0,z1,z289,z2,z4,z6]),(0,[z0,z806,z2,z4,z5,z6]),(0,[z0,z1,z10,z867,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z1284,z6]),(0,[z1,z2,z4,z5,z411,z60]),(0,[z0,z1,z2,z4,z5,z1285])],[(0,[z98,z1,z17,z4,z5,z6]),(0,[z0,z1,z2,z4,z1286,z6]),(0,[z0,z1,z2,z4,z865,z6]),(0,[z32,z0,z2,z4,z721,z6])],[(0,[z0,z1,z2,z1287,z5,z6]),(0,[z214,z0,z1,z2,z5,z61]),(0,[z0,z279,z2,z4,z41,z6]),(0,[z234,z0,z1,z2,z4,z650])],[(0,[z0,z1,z2,z4,z41,z15]),(0,[z0,z1,z1288,z2,z4,z6]),(0,[z0,z38,z2,z4,z5,z95]),(0,[z0,z1,z2,z41,z6,z270])],[(0,[z0,z1,z2,z1289,z5,z6]),(0,[z0,z1290,z2,z4,z5,z6]),(0,[z0,z120,z1,z2,z4,z105]),(0,[z225,z1,z2,z571,z5,z6]),(0,[z277,z1,z2,z179,z5,z6])],[(0,[z0,z122,z2,z154,z118,z6]),(0,[z0,z1291,z1,z2,z4,z6])],[(0,[z0,z64,z2,z7,z5,z6]),(0,[z0,z1,z2,z1292,z5,z6]),(0,[z0,z39,z83,z4,z5,z6]),(0,[z0,z304,z2,z4,z5,z6]),(0,[z0,z1,z289,z217,z4,z6]),(0,[z0,z1,z196,z186,z41,z6]),(0,[z0,z135,z2,z4,z315,z6])],[(0,[z0,z1,z1293,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z411]),(0,[z1,z2,z588,z4,z5,z60]),(0,[z0,z1,z2,z4,z1294,z6])],[(0,[z0,z1,z1295,z2,z4,z6]),(0,[z0,z64,z2,z4,z5,z274]),(0,[z0,z1296,z2,z4,z5,z6]),(0,[z0,z1,z218,z4,z5,z60]),(0,[z0,z1,z1297,z2,z4,z6]),(0,[z911,z0,z1,z2,z4,z5])],[(0,[z0,z1298,z2,z4,z5,z6]),(0,[z0,z1,z2,z319,z5,z6]),(0,[z88,z100,z1,z2,z5,z61])],[(0,[z0,z1,z2,z4,z5,z125]),(0,[z171,z1,z166,z4,z5,z6])],[(0,[z0,z1,z2,z208,z5,z15]),(1,[z801,z2,z4,z5,z6]),(0,[z0,z64,z2,z4,z282,z6]),(0,[z131,z1,z2,z4,z72,z6]),(0,[z0,z135,z2,z4,z5,z6]),(0,[z0,z122,z475,z2,z4,z6]),(1,[z0,z127,z2,z41,z6])],[(0,[z327,z1,z2,z4,z5,z6])],[(0,[z0,z1,z186,z5,z6,z233]),(0,[z0,z1,z62,z4,z41,z99]),(0,[z0,z1,z2,z4,z221,z6])],[(0,[z0,z1,z2,z4,z5,z1299]),(0,[z0,z283,z2,z4,z5,z44]),(0,[z14,z86,z2,z4,z5,z6]),(0,[z1300,z0,z1,z2,z5,z6]),(0,[z0,z1,z1301,z4,z5,z6]),(0,[z102,z0,z1,z186,z41,z6])],[(0,[z518,z1,z2,z4,z28,z6]),(0,[z412,z0,z1,z4,z5,z174]),(0,[z0,z1,z210,z186,z5,z6]),(0,[z1302,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z442,z1,z2,z41,z6]),(0,[z0,z1,z289,z2,z41,z6])],[(0,[z1,z2,z4,z5,z6,z96]),(0,[z130,z2,z4,z5,z6,z60]),(0,[z13,z1,z10,z2,z4,z6]),(0,[z0,z1,z2,z4,z52,z197]),(0,[z681,z0,z1,z10,z2,z6]),(0,[z100,z1,z136,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1303,z6]),(0,[z0,z86,z4,z121,z5,z6]),(0,[z0,z1,z2,z4,z1304,z6]),(0,[z0,z122,z2,z4,z721,z6]),(0,[z117,z0,z1,z235,z2,z6])],[(0,[z0,z1,z211,z4,z273,z6]),(0,[z0,z1,z2,z756,z5,z6]),(0,[z0,z1305,z2,z4,z5,z6]),(0,[z0,z1,z2,z547,z1046,z6]),(0,[z178,z0,z1,z2,z319,z55])],[(0,[z0,z1306,z2,z4,z5,z6]),(0,[z0,z1,z2,z479,z5,z6]),(0,[z0,z2,z46,z31,z41,z6]),(0,[z0,z1,z2,z4,z80,z227]),(0,[z0,z1,z2,z179,z52,z6])],[(0,[z0,z1,z2,z4,z1307,z6]),(0,[z0,z1,z1308,z2,z4,z6]),(0,[z1309,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z41,z6,z476])],[(0,[z0,z1,z1310,z4,z5,z6]),(0,[z98,z1,z10,z17,z4,z6]),(0,[z131,z1,z2,z4,z335,z6]),(0,[z225,z1,z2,z547,z5,z6]),(0,[z453,z0,z1,z2,z4,z55])],[(0,[z0,z1,z1311,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z1312]),(0,[z0,z1,z1313,z4,z5,z6]),(0,[z1314,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z41,z6,z61])],[(0,[z98,z1,z4,z855,z5,z6]),(0,[z0,z1,z2,z4,z1315,z6]),(0,[z453,z0,z1,z2,z4,z271]),(0,[z0,z1,z218,z4,z41,z6])],[(0,[z0,z1,z2,z208,z92,z6]),(0,[z0,z1,z2,z4,z1316,z6]),(0,[z0,z1,z409,z4,z29,z6]),(0,[z0,z1,z10,z2,z547,z6]),(0,[z0,z1,z2,z43,z41,z6]),(0,[z178,z0,z1,z2,z4,z301])],[(0,[z66,z0,z2,z208,z5,z6]),(0,[z82,z1,z10,z2,z4,z60]),(0,[z0,z1,z2,z4,z1317,z6]),(0,[z178,z0,z1,z2,z154,z6]),(0,[z0,z1,z2,z546,z80,z6]),(0,[z0,z1,z1318,z2,z4,z6]),(0,[z171,z304,z2,z4,z5,z6])],[(0,[z130,z0,z4,z121,z5,z6]),(0,[z0,z1,z2,z1319,z5,z6]),(0,[z1,z2,z4,z5,z6,z1320]),(0,[z40,z0,z2,z4,z5,z813])],[(0,[z102,z0,z1,z2,z285,z6])],[(0,[z8,z1,z2,z65,z5,z6]),(0,[z9,z0,z1,z2,z90,z6]),(0,[z0,z122,z329,z2,z4,z6]),(0,[z0,z1,z2,z571,z5,z6])],[(0,[z0,z1,z10,z2,z132,z6]),(0,[z283,z2,z4,z5,z6,z60]),(0,[z45,z283,z2,z4,z5,z6]),(0,[z0,z1,z2,z43,z41,z106])]],
   [[(0,[z0,z1,z2,z4,z1321,z6]),(0,[z0,z283,z2,z4,z5,z95]),(0,[z1322,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z548,z41,z6])],[(0,[z0,z1323,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1324,z6]),(0,[z362,z0,z2,z4,z33,z6]),(0,[z0,z1,z2,z4,z1325,z6])],[(0,[z0,z733,z2,z4,z5,z6]),(0,[z171,z1,z2,z4,z221,z6])],[(0,[z0,z1,z2,z4,z5,z1326]),(0,[z564,z9,z1,z2,z41,z6]),(0,[z0,z1,z2,z1327,z5,z6]),(0,[z13,z1,z2,z4,z41,z6])],[(0,[z8,z143,z2,z65,z5,z6]),(0,[z539,z0,z1,z2,z41,z6]),(0,[z0,z38,z10,z2,z4,z95]),(0,[z0,z1,z2,z4,z1328,z6])],[(0,[z0,z2,z4,z5,z44,z11]),(0,[z0,z1,z2,z4,z1329,z6]),(0,[z0,z1,z2,z43,z315,z6]),(0,[z0,z1,z71,z2,z546,z6]),(0,[z0,z1,z478,z2,z4,z197])],[(0,[z0,z1,z1330,z4,z5,z6]),(0,[z0,z1,z2,z571,z162,z6])],[(0,[z14,z2,z4,z5,z6,z544]),(0,[z0,z1,z2,z4,z1331,z6]),(0,[z0,z1,z2,z4,z1332,z6]),(0,[z88,z0,z1,z2,z221,z61])],[(0,[z0,z1,z211,z4,z5,z6]),(0,[z0,z1,z1333,z2,z4,z6]),(0,[z0,z1,z192,z4,z5,z406]),(0,[z0,z1,z10,z2,z4,z411]),(0,[z376,z1,z2,z4,z72,z6]),(0,[z0,z1,z2,z4,z1334,z6])],[(0,[z0,z1335,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z741])],[(0,[z0,z1,z2,z4,z1336,z6]),(0,[z0,z2,z775,z31,z5,z6])],[(0,[z0,z35,z2,z31,z41,z6]),(0,[z0,z1,z2,z4,z5,z1337]),(0,[z0,z1,z10,z2,z4,z125]),(0,[z0,z1,z2,z4,z1338,z6]),(0,[z0,z1,z289,z2,z123,z6]),(0,[z102,z0,z1,z2,z785,z6])],[(0,[z0,z1,z2,z3,z5,z15]),(0,[z0,z1,z1339,z2,z4,z6]),(0,[z0,z135,z10,z2,z4,z6]),(0,[z1340,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z324,z80])],[(0,[z0,z1,z192,z4,z5,z57]),(0,[z0,z1,z1341,z4,z5,z6]),(0,[z82,z1,z2,z4,z41,z60]),(0,[z153,z0,z30,z46,z5,z6]),(0,[z0,z1,z860,z4,z5,z6]),(0,[z327,z1,z10,z2,z4,z6])],[(0,[z0,z1,z2,z1342,z5,z6])],[(0,[z0,z1,z2,z4,z1099,z6]),(0,[z66,z0,z1,z186,z41,z6]),(1,[z0,z2,z4,z5,z813]),(0,[z0,z1,z10,z2,z546,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 500).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 999).take 340) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1339)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [500, 499, 340] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 143).take 138).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 281).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 402).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [143, 138, 121, 110] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36338

theorem PEqualNP.Outside.L_meta_36338 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277071072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277071072) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36338.solve