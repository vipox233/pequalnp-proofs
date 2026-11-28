import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38705

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4274571464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000198ce380e318a#64 ++ 0xa0003319c701c631#64 ++ 0x8813f9fe781e739f#64 ++ 0xd1027f3fcf03ce73#64 : BitVec 256),
   (0x00644220c060c634#64 ++ 0x400c8844180c18c6#64 ++ 0xf8ec4623e0e3ffff#64 ++ 0xbf1d88c47c1c7fff#64 : BitVec 256),
   (0x030b85c31b0318c0#64 ++ 0x806170b863606318#64 ++ 0xb70f87c39f039ce7#64 ++ 0x76e1f0f873e0739c#64 : BitVec 256),
   (0x0db007740db41f07#64 ++ 0x01b600ee81b683e0#64 ++ 0xfff007fc1ffc1f06#64 ++ 0xfffe00ff83ff83e0#64 : BitVec 256),
   (0x16dee80016dbe000#64 ++ 0x02dbdd0002db7c00#64 ++ 0xdffff8001fffe005#64 ++ 0xfbffff0003fffc00#64 : BitVec 256),
   (0x27ff77bbe0000000#64 ++ 0x04ffeef77c000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8813f9fe781e739f 0xd1027f3fcf03ce73

def z1 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8ec4623e0e3ffff 0xbf1d88c47c1c7fff

def z2 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70f87c39f039ce7 0x76e1f0f873e0739c

def z3 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007fc1ffc1f06 0xfffe00ff83ff83e0

def z4 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8001fffe005 0xfbffff0003fffc00

def z5 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z6 : W := mkw 0x27fffffff80e318a 0xa4ffffffff01c631 0xe7fffffff81c0003 0xfcffffffff038000

def z7 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0013b9dc181c0000 0x4002773b83038000

def z8 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x70ec060180e18c60 0x2e1d80c0301c318c

def z9 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013f9fe60000003 0xd0027f3fcc000000

def z10 : W := mkw 0x0001988a300a2088 0xa000331146014411 0x0003f80260026099 0x00007f004c004c13

def z11 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x48e0402060e06318 0x891c08040c1c0c63

def z12 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x0713b9dc00000000 0x40e2773b80000000

def z13 : W := mkw 0x0100054009001800 0x002000a801200300 0xb70c07c39f039ce7 0x76e180f873e0739c

def z14 : W := mkw 0x0020022000200604 0x00040044000400c0 0xf8ec062380e39fe7 0xbf1d80c4701c73fc

def z15 : W := mkw 0x224ff8cff80e318a 0xa449ff19ff01c631 0x881ff9fff81e739f 0xd103ff3fff03ce73

def z16 : W := mkw 0x020b988b320b20c8 0xa041731166416419 0x000ff803e003e0f9 0x0001ff007c007c1f

def z17 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xbf1fffffff1fffff 0xf7e3ffffffe3ffff

def z18 : W := mkw 0x37ffffbbf6fbe634 0x46fffff77edf7cc6 0xffffffffffffffff 0xffffffffffffffff

def z19 : W := mkw 0x0df44774cdb41f07 0x01be88ee99b683e0 0xfffc47fffffc1f07 0xffff88ffffff83e0

def z20 : W := mkw 0x0920077409241f07 0x012400ee812483e0 0x200007fc00001f02 0x040000ff800003e0

def z21 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z22 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xf7ffffffe0e18c63 0xfefffffffc1c318c

def z23 : W := mkw 0x000000000060c634 0x40000000000c18c6 0x1800000000e3fffc 0x03000000001c7fff

def z24 : W := mkw 0x030b058300000000 0x006160b060000000 0x070381c000000000 0x40e0703800000000

def z25 : W := mkw 0x14f46a20c4f8e634 0x429e8d44189f1cc6 0xf8fc7e23e0ffffff 0xbf1f8fc47c1fffff

def z26 : W := mkw 0x1ffeef741fffff07 0x03ffddee83ffffe0 0xfffffffc1fffff07 0xffffffff83ffffe0

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0x880040226002739f 0x910008044c004e73

def z28 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67ffbfdd80000000 0x6cfff7fbb0000000

def z29 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08000000181e739c 0x010000000303ce73

def z30 : W := mkw 0x27fe6731c0000000 0x04ffcce638000000 0x67ec060180000000 0x2cfd80c030000000

def z31 : W := mkw 0x14d4680004d8e000 0x029a8d00009b1c00 0x48f0780000fc6000 0x891e0f00001f8c00

def z32 : W := mkw 0x16feea20d6fbe634 0x42dfdd441adf7cc6 0xfffffe23ffffffff 0xffffffc47fffffff

def z33 : W := mkw 0x1490880016dbe000 0x0292110002db7c00 0xdff000001fffe004 0xfbfe000003fffc00

def z34 : W := mkw 0x0001108a20000000 0x0000221144000000 0x0013b9dc00000000 0x4002773b80000000

def z35 : W := mkw 0x06df708a20000000 0x00dbee1144000000 0xc7fff9fe60000003 0xf8ffff3fcc000000

def z36 : W := mkw 0x124ee800d24be030 0x4249dd001a497c06 0x000ff803e003e0f9 0x0001ff007c007c1f

def z37 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370f87c19f018c60 0x66e1f0f833e0318c

def z38 : W := mkw 0x27ff77ffe804118a 0xa4ffeefffd008231 0xe7ffffffe000139b 0xfcfffffffc000273

def z39 : W := mkw 0x010115cf290419ca 0xa02022b9e5208339 0x200007ffe0001ffa 0x040000fffc0003ff

def z40 : W := mkw 0x0fbb87f31fb31ec5 0x81f770fe63f663d8 0xf7ef87c39fe39ce7 0x7efdf0f873fc739c

def z41 : W := mkw 0x2fff77ffedf4df37 0x45ffeefffdbe9be6 0xffffffffffffffff 0xffffffffffffffff

def z42 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x080001fe781e739e 0x0100003fcf03ce73

def z43 : W := mkw 0x34f47a38e4d8e000 0x069e8f471c9b1c00 0x48f0783c60fc6000 0x891e0f078c1f8c00

def z44 : W := mkw 0x0000004408041102 0x0000000881008220 0x881001fc181c1306 0xd102003f83038260

def z45 : W := mkw 0x0db19ffe3dbe3f8f 0xa1b633ffc7b7c7f1 0xfff3fffe7ffe7f9f 0xfffe7fffcfffcff3

def z46 : W := mkw 0x030a050103010840 0x006140a020602108 0x370c060187018c60 0x26e180c030e0318c

def z47 : W := mkw 0x24f47238e0000000 0x049e8e471c000000 0x40f0783c60000000 0x881e0f078c000000

def z48 : W := mkw 0x0020022000200604 0x00040044000400c0 0xf8e0062000e01f06 0xbf1c00c4001c03e0

def z49 : W := mkw 0x0df44774cdf4df37 0x41be88ee99be9be6 0xfffc47ffffffffff 0xffff88ffffffffff

def z50 : W := mkw 0x000000440804118a 0xa000000881008231 0x0000000000001398 0x0000000000000273

def z51 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0x0713b8001f1c0000 0x40e2770003e38000

def z52 : W := mkw 0x236f77bbe0000000 0x046deef77c000000 0x200fffffe0000003 0x0401fffffc000000

def z53 : W := mkw 0x0065daeef86ef7be 0xe00cbb5ddf0ddef7 0xf8fffffff8ffffff 0xff1fffffff1fffff

def z54 : W := mkw 0x27fffffff80e318a 0xa4ffffffff01c631 0xeffffffff81e739f 0xfdffffffff03ce73

def z55 : W := mkw 0x0000180c200c210a 0x2000030184018421 0x0810783c601c6318 0x81020f078c038c63

def z56 : W := mkw 0x16de600006d1c000 0x02dbcc0000da3800 0x57ec000007e18000 0x2afd800000fc3000

def z57 : W := mkw 0x17dfe5c31fd3d8c0 0x82fbfcb863fa7b18 0xf7ef87c39fe39ce7 0x7efdf0f873fc739c

def z58 : W := mkw 0x000080401b0318c0 0x8000100803606318 0x100000001f039ce4 0x0200000003e0739c

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0xb00c060380039ce7 0x360180c07000739c

def z60 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x47f3f9fc60000000 0xc8fe7f3f8c000000

def z61 : W := mkw 0x000118ce280c318a 0xa0002319c5018631 0x081079fe601c739a 0x81020f3fcc038e73

def z62 : W := mkw 0x0db007700db01e05 0x01b600ee01b603c0 0xf7e007c01fe01c06 0x7efc00f803fc0380

def z63 : W := mkw 0x00008800100a2000 0x0000110002014400 0x8813f800181e6005 0xd1027f000303cc00

def z64 : W := mkw 0x16dff8ce3edff18a 0xa2dbff19c7dbfe31 0xdffff9fe7ffff39f 0xfbffff3fcffffe73

def z65 : W := mkw 0x0fbb87f71fb71fc7 0x81f770fee3f6e3f8 0xffff87ff9fff9fe7 0xfffff0fff3fff3fc

def z66 : W := mkw 0x0020022000000000 0x0004004400000000 0xe0e0062000000002 0xbc1c00c400000000

def z67 : W := mkw 0x1044c80016dbe000 0x0208990002db7c00 0xd8ec40001fffe005 0xbb1d880003fffc00

def z68 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf0ec060380e39ce7 0x3e1d80c0701c739c

def z69 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x57eff80007e3e001 0x2afdff0000fc7c00

def z70 : W := mkw 0x030a85411b0318c0 0x806150a823606318 0x370c06019f039ce4 0x26e180c033e0739c

def z71 : W := mkw 0x17dfedc31fdbf8c0 0x82fbfdb863fb7f18 0xdffff9c01fffe005 0xfbffff3803fffc00

def z72 : W := mkw 0x0d9005540db41f07 0x01b200aa81b683e0 0x1f1001dc1ffc1f04 0x43e2003b83ff83e0

def z73 : W := mkw 0x2fff77bfe4b40707 0x05ffeef7fc9680e0 0xefffffffe0fc0303 0xfdfffffffc1f8060

def z74 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0x071001dc1f1c0000 0x40e2003b83e38000

def z75 : W := mkw 0x27ff77bbe3010840 0x04ffeef77c602108 0xf7ffffffe7018c63 0xfefffffffce0318c

def z76 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8227ffff39f 0xfbffff044ffffe73

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0x300c060180018c60 0x260180c03000318c

def z78 : W := mkw 0x00008800100a2000 0x0000110002014400 0x0003f80000026001 0x00007f0000004c00

def z79 : W := mkw 0x104468000048e000 0x02088d0000091c00 0x0000780000006000 0x00000f0000000c00

def z80 : W := mkw 0x24f572bae0000000 0x049eae575c000000 0xc0f3f9fe60000003 0xd81e7f3fcc000000

def z81 : W := mkw 0x000110ce2804118a 0xa0002219c5008231 0x000001fe6000139a 0x0000003fcc000273

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000060380001ce2 0x040000c07000039c

def z83 : W := mkw 0x169bb8ce3e9f318a 0xa2d37719c7d3e631 0x8f13f9fe7f1e739f 0xd1e27f3fcfe3ce73

def z84 : W := mkw 0x092117fe29241f8f 0xa12422ffc52483f1 0x200007fe60001f9a 0x040000ffcc0003f3

def z85 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x270387c39f001ce2 0x44e070f873e0039c

def z86 : W := mkw 0x036fc7e3db63def4 0xc06df8fc7b6c7bde 0xffefc7e3ffe3ffff 0xfffdf8fc7ffc7fff

def z87 : W := mkw 0x26fe7238e0000000 0x04dfce471c000000 0xc7fff83c60000001 0xf8ffff078c000000

def z88 : W := mkw 0x080198ce3dbe3f8f 0xa1003319c7b7c7f1 0x9813f9fe7ffe7f9f 0xd3027f3fcfffcff3

def z89 : W := mkw 0x16dee8441edff102 0x02dbdd0883dbfe20 0xdffff9fc1ffff307 0xfbffff3f83fffe60

def z90 : W := mkw 0x0490000004900000 0x0092000000920000 0xdff000001ffc0004 0xfbfe000003ff8000

def z91 : W := mkw 0x27ff77bbe040c000 0x04ffeef77c081800 0xffffffffe0e3e007 0xfffffffffc1c7c00

def z92 : W := mkw 0x2fff77ffedb41f07 0x05ffeefffdb683e0 0xfffffffffffc1f07 0xffffffffffff83e0

def z93 : W := mkw 0x37dffd9b36dbe000 0x06fbffb366db7c00 0xdffff9dc1fffe005 0xfbffff3b83fffc00

def z94 : W := mkw 0x279bb5db3b0318c0 0x84f376bb67606318 0xb71fbfdf9f039ce7 0x76e3f7fbf3e0739c

def z95 : W := mkw 0x00200220c0200634 0x40040044180400c6 0xb00c0623e0039fff 0x360180c47c0073ff

def z96 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xb71fbfdf9f1f9ce7 0x76e3f7fbf3e3f39c

def z97 : W := mkw 0x00444000c040c030 0x4008880018081806 0x000c4003e003e0f9 0x000188007c007c1f

def z98 : W := mkw 0x05b0073004900000 0x00b600e600920000 0xfff007fc1ffc0006 0xfffe00ff83ff8000

def z99 : W := mkw 0x37ffffbbf6dbe000 0x06fffff77edb7c00 0xffffffffffffe007 0xfffffffffffffc00

def z100 : W := mkw 0x0df5dffefdfeffbf 0xe1bebbffdfbfdff7 0xffffffffffffffff 0xffffffffffffffff

def z101 : W := mkw 0x0db0073005b00e05 0x01b600e600b601c0 0x77e0060007e00c00 0x2efc00c000fc0180

def z102 : W := mkw 0x0100054009001800 0x002000a801200300 0xb70007c01f001c06 0x76e000f803e00380

def z103 : W := mkw 0x020b8083120300c0 0x8041701062406018 0x000f8003800380e1 0x0001f0007000701c

def z104 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xbf0fc7e3ff03ffff 0xf7e1f8fc7fe07fff

def z105 : W := mkw 0x020a800012030000 0x0041500002406000 0x970f80001f038005 0x72e1f00003e07000

def z106 : W := mkw 0x004440000040c000 0x0008880000081800 0xd8ec400000e3e005 0xbb1d8800001c7c00

def z107 : W := mkw 0x1f9aad541f9f3903 0x03f355aa83f3e720 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z108 : W := mkw 0x0db19ffe3dbe3f8f 0xa1b633ffc7b7c7f1 0xfff3bffc1ffc1f06 0xfffe77ff83ff83e0

def z109 : W := mkw 0x06de60000040c000 0x00dbcc0000081800 0xdffff80000e3e005 0xfbffff00001c7c00

def z110 : W := mkw 0x030b8dc71b0f39ca 0xa06171b8e361e739 0xbf0f87c39f1fffff 0x77e1f0f873e3ffff

def z111 : W := mkw 0x0db0073005b00e05 0x01b600e600b601c0 0xf7f007fc07e00c02 0xfefe00ff80fc0180

def z112 : W := mkw 0x124ff88a324be088 0xa249ff1146497c11 0x000ff8026003e099 0x0001ff004c007c13

def z113 : W := mkw 0x27ff67b3c0000000 0x04ffecf678000000 0xe7ef87c380000003 0x7cfdf0f870000000

def z114 : W := mkw 0x00444000c0000000 0x0008880018000000 0x000c4003e0000001 0x000188007c000000

def z115 : W := mkw 0x000100c208001080 0x8000201841000210 0x000001c200001082 0x0000003840000210

def z116 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0013f9de781e6099 0x40027f3bcf03cc13

def z117 : W := mkw 0x0000004009001800 0x0000000801200300 0x100000001f001c04 0x0200000003e00380

def z118 : W := mkw 0x00000804000c210a 0x2000010080018421 0x08000000001c6318 0x0100000000038c63

def z119 : W := mkw 0x1fffeff71fffffc7 0x83fffdfee3fffff8 0xffffffff9fffffe7 0xfffffffff3fffffc

def z120 : W := mkw 0x06de600000000000 0x00dbcc0000000000 0xc7fff80000000001 0xf8ffff0000000000

def z121 : W := mkw 0x27ff7fbfe00c210a 0x24ffeff7fc018421 0xefffffffe01c631b 0xfdfffffffc038c63

def z122 : W := mkw 0x1efeea3416ffe707 0x03dfdd4682dffce0 0xdffff83c1fffe305 0xfbffff0783fffc60

def z123 : W := mkw 0x10008800124be000 0x0200110002497c00 0x000000000003e000 0x0000000000007c00

def z124 : W := mkw 0x27ffffbbf00a2088 0xa4fffff77e014411 0xe7ffffffe002609b 0xfcfffffffc004c13

def z125 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0xb81ffffff81fffff 0xf703ffffff03ffff

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000039ce4 0x020000000000739c

def z127 : W := mkw 0x24f47238e060c634 0x449e8e471c0c18c6 0x48f0783c60e06318 0x891e0f078c1c0c63

def z128 : W := mkw 0x020a8800120b2000 0x0041510002416400 0x9f1ff8001f1fe005 0xf3e3ff0003e3fc00

def z129 : W := mkw 0x036e4721c361ce74 0x406dc8e4386c39ce 0xffec4623e7e3ffff 0xbffd88c47cfc7fff

def z130 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x4ff3f8001ffc6000 0xc9fe7f0003ff8c00

def z131 : W := mkw 0x2df4777cedb41f07 0x05be8eef9db683e0 0xfff07ffc7ffc1f06 0xfffe0fff8fff83e0

def z132 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x881001fc181e739e 0xd102003f8303ce73

def z133 : W := mkw 0x00644220c0200634 0x400c8844180400c6 0xe0ec4623e0001ffb 0xbc1d88c47c0003ff

def z134 : W := mkw 0x05b0073000000000 0x00b600e600000000 0xe7f007fc00000002 0xfcfe00ff80000000

def z135 : W := mkw 0x124fe883124be0c0 0x8249fd1062497c18 0x000ff8038003e0e1 0x0001ff0070007c1c

def z136 : W := mkw 0x292117ffe9241f07 0x052422fffd2483e0 0x200007ffe0001f02 0x040000fffc0003e0

def z137 : W := mkw 0x030b8dc31b0b38c0 0x806171b863616718 0xbf1fffc39f1ffce7 0xf7e3fff873e3ff9c

def z138 : W := mkw 0x124ee800124be000 0x0249dd0002497c00 0x000ff8000003e001 0x0001ff0000007c00

def z139 : W := mkw 0x0100054409041902 0x002000a881208320 0xbf1007fc1f1c1f06 0xf7e200ff83e383e0

def z140 : W := mkw 0x09200774c9241f37 0x412400ee992483e6 0x200007ffe0001ffa 0x040000fffc0003ff

def z141 : W := mkw 0x16dee800d6dbe030 0x42dbdd001adb7c06 0xdffff803ffffe0fd 0xfbffff007ffffc1f

def z142 : W := mkw 0x1000880016dbe000 0x0200110002db7c00 0x180000001fffe004 0x0300000003fffc00

def z143 : W := mkw 0x21200731c0000000 0x042400e638000000 0x2000060180000000 0x040000c030000000

def z144 : W := mkw 0x0db08f741dbe3f8f 0xa1b611ee83b7c7f1 0xfff007fc1ffe7f9e 0xfffe00ff83ffcff3

def z145 : W := mkw 0x00010083000000c0 0x8000201060000018 0x00000003800000e0 0x000000007000001c

def z146 : W := mkw 0x06de600004900000 0x00dbcc0000920000 0xdffff8001ffc0005 0xfbffff0003ff8000

def z147 : W := mkw 0x14d4600004d0c000 0x029a8c00009a1800 0x40e0000000e00000 0x081c0000001c0000

def z148 : W := mkw 0x2fff77bbe5b00e05 0x05ffeef77cb601c0 0xf7ffffffe7e00c03 0xfefffffffcfc0180

def z149 : W := mkw 0x212117bbe0000000 0x042422f77c000000 0xa013ffffe0000003 0xd4027ffffc000000

def z150 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8813f9fe6002739f 0xd1027f3fcc004e73

def z151 : W := mkw 0x120a880016dbe000 0x0241510002db7c00 0x9f0f80001fffe005 0x73e1f00003fffc00

def z152 : W := mkw 0x000088441b0f39ca 0xa00011088361e739 0x180000001f1ffffc 0x0300000003e3ffff

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013f80000000001 0xd0027f0000000000

def z154 : W := mkw 0x0cb002740db41f07 0x0196004e81b683e0 0x58f0003c1ffc1f04 0x8b1e000783ff83e0

def z155 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf0ec4623e0e18c63 0xbe1d88c47c1c318c

def z156 : W := mkw 0x17dfedc31fdbf8c0 0x82fbfdb863fb7f18 0xffffffc39ffffce7 0xfffffff873ffff9c

def z157 : W := mkw 0x0db0073405b40f07 0x01b600e680b681e0 0x7ff0063c07fc0f00 0xaffe00c780ff81e0

def z158 : W := mkw 0x00219aee382e378e 0xa004335dc705c6f1 0xf8f3fffe78fe7f9f 0xff1e7fffcf1fcff3

def z159 : W := mkw 0x212117bbe0000000 0x042422f77c000000 0x200007ffe0000002 0x040000fffc000000

def z160 : W := mkw 0x092107f709241fc7 0x812420fee12483f8 0x200007ff80001fe2 0x040000fff00003fc

def z161 : W := mkw 0x24f47238e060c634 0x449e8e471c0c18c6 0xf8fc7e3fe0e3ffff 0xbf1f8fc7fc1c7fff

def z162 : W := mkw 0x27fe7739e0000000 0x04ffcee73c000000 0x67fc7e3de0000000 0xacff8fc7bc000000

def z163 : W := mkw 0x000180c218021080 0x8000301843004210 0x800381c218021087 0x5000703843004210

def z164 : W := mkw 0x0cb0023404b40707 0x01960046809680e0 0x48f0003c00fc0300 0x891e0007801f8060

def z165 : W := mkw 0x032b87e3db231ef4 0xc06570fc7b6463de 0xb70f87e3ff039fff 0x76e1f0fc7fe073ff

def z166 : W := mkw 0x016547e3c960def4 0xc02ca8fc792c1bde 0xf8ec47e3e0e3ffff 0xbf1d88fc7c1c7fff

def z167 : W := mkw 0x000080401b0318c0 0x8000100803606318 0xb00c06039f039ce7 0x360180c073e0739c

def z168 : W := mkw 0x224f708be0000000 0x0449ee117c000000 0x000ff803e0000001 0x0001ff007c000000

def z169 : W := mkw 0x06de600000000000 0x00dbcc0000000000 0x47ec000000000000 0x28fd800000000000

def z170 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x071ff8001f1fe001 0x40e3ff0003e3fc00

def z171 : W := mkw 0x0000100c2004010a 0x2000020184008021 0x0000003c60000318 0x000000078c000063

def z172 : W := mkw 0x100088441edff18a 0xa200110883dbfe31 0x180000001ffff39c 0x0300000003fffe73

def z173 : W := mkw 0x216557bbe0000000 0x042caaf77c000000 0xe0ec47ffe0000003 0xbc1d88fffc000000

def z174 : W := mkw 0x0001988a300a2088 0xa000331146014411 0x8813f802781e609d 0xd1027f004f03cc13

def z175 : W := mkw 0x0100050001000800 0x002000a000200100 0x3700060007000c00 0x26e000c000e00180

def z176 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x40e0000000e00000 0x081c0000001c0000

def z177 : W := mkw 0x10008800169b2000 0x0200110002d36400 0x000000001f1c0000 0x0000000003e38000

def z178 : W := mkw 0x234ff5cbfb0318c0 0x8469feb97f606318 0xb70fffc3ff039ce7 0x76e1fff87fe0739c

def z179 : W := mkw 0x030b158b20000000 0x006162b164000000 0xa71fffffe0000003 0xf4e3fffffc000000

def z180 : W := mkw 0x0490000004900000 0x0092000000920000 0x57e0000007e00000 0x2afc000000fc0000

def z181 : W := mkw 0x0065daeef86ef7be 0xe00cbb5ddf0ddef7 0xc8f3f9fe78fe739f 0xd91e7f3fcf1fce73

def z182 : W := mkw 0x0020026408241706 0x0004004c810482e0 0xf8f007fc18fc1f06 0xff1e00ff831f83e0

def z183 : W := mkw 0x220b308b20000000 0x0441661164000000 0x0003b80000000000 0x0000770000000000

def z184 : W := mkw 0x024ec0001243c000 0x0049d80002487800 0xdfefc0001fe3e005 0xfbfdf80003fc7c00

def z185 : W := mkw 0x030b058300000000 0x006160b060000000 0xb70f87c380039ce7 0x76e1f0f87000739c

def z186 : W := mkw 0x0100050000000000 0x002000a000000000 0xa70007c000000002 0x74e000f800000000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0xb80c4623e003ffff 0xb70188c47c007fff

def z188 : W := mkw 0x030a050100000000 0x006140a020000000 0x270c060180000000 0x24e180c030000000

def z189 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0813f9fc781c6318 0xc1027f3f8f038c63

def z190 : W := mkw 0x00000040090018c0 0x8000000801200318 0x0000000000001ce0 0x000000000000039c

def z191 : W := mkw 0x14d4e80016dbe000 0x029a9d0002db7c00 0x58f078001fffe004 0x8b1e0f0003fffc00

def z192 : W := mkw 0x036fc7e3db63def4 0xc06df8fc7b6c7bde 0xf7ef87c39fe39ce7 0x7efdf0f873fc739c

def z193 : W := mkw 0x0db117fe2db41f07 0x01b622ffc5b683e0 0xfff3fffe7ffc1f07 0xfffe7fffcfff83e0

def z194 : W := mkw 0x06fe6220c0000000 0x00dfcc4418000000 0xe7fffe23e0000003 0xfcffffc47c000000

def z195 : W := mkw 0x0cf44234c4f4c737 0x419e8846989e98e6 0x48f0403c60fc6318 0x891e08078c1f8c63

def z196 : W := mkw 0x020a000102010040 0x0041400020402008 0x000c000180018060 0x000180003000300c

def z197 : W := mkw 0x0000004408041102 0x0000000881008220 0x001001dc181c0000 0x4002003b83038000

def z198 : W := mkw 0x0fbb9fff3fbf3fcf 0xa1f773ffe7f7e7f9 0xffffffffffffffff 0xffffffffffffffff

def z199 : W := mkw 0x37ff77bbe6d1c000 0x06ffeef77cda3800 0xf7ffffffe7e18003 0xfefffffffcfc3000

def z200 : W := mkw 0x2f9b35df2d941903 0x05f366bbe5b28320 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z201 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xefffffffe002739f 0xfdfffffffc004e73

def z202 : W := mkw 0x000180c218021080 0x8000301843004210 0xb00f87c398039ce7 0x7601f0f87300739c

def z203 : W := mkw 0x07fe673000000000 0x00ffcce600000000 0xe7fffffc00000003 0xfcffffff80000000

def z204 : W := mkw 0x0001108a20000000 0x0000221144000000 0x0003f80260000001 0x00007f004c000000

def z205 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x58e0402060e3fffc 0x8b1c08040c1c7fff

def z206 : W := mkw 0x0000800012030000 0x0000100002406000 0x100000001f038004 0x0200000003e07000

def z207 : W := mkw 0x00008800100a2000 0x0000110002014400 0x0013b800181c0000 0x4002770003038000

def z208 : W := mkw 0x0001988a300a2088 0xa000331146014411 0x8013f9fe6002609b 0xd0027f3fcc004c13

def z209 : W := mkw 0x0cb0023004b00605 0x01960046009600c0 0x40e0000000e00000 0x081c0000001c0000

def z210 : W := mkw 0x030b058300000000 0x006160b060000000 0xa70f87c380000003 0x74e1f0f870000000

def z211 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0xdff3b8001ffc0004 0xfbfe770003ff8000

def z212 : W := mkw 0x080088441dbe3f8f 0xa100110883b7c7f1 0x180000001ffe7f9c 0x0300000003ffcff3

def z213 : W := mkw 0x000198ce386ef7be 0xe0003319c70ddef7 0x9813f9fe78ffffff 0xd3027f3fcf1fffff

def z214 : W := mkw 0x0044c800104ae000 0x0008990002095c00 0xd8fff80018ffe005 0xfb1fff00031ffc00

def z215 : W := mkw 0x030b85c71b0719c2 0x806170b8e360e338 0xbf1f87ff9f1f9fe7 0xf7e3f0fff3e3f3fc

def z216 : W := mkw 0x0cb0023404b40707 0x01960046809680e0 0xdff0003c1ffc0304 0xfbfe000783ff8060

def z217 : W := mkw 0x2490301820000000 0x0492060304000000 0x0010381c00000000 0x0002070380000000

def z218 : W := mkw 0x0064c260db63def4 0xc00c984c1b6c7bde 0xf8ec4623ffe3ffff 0xbf1d88c47ffc7fff

def z219 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x68e04623e0e07ffa 0x8d1c08c47c1c0fff

def z220 : W := mkw 0x0000000000200604 0x00000000000400c0 0x1800000000e01f04 0x03000000001c03e0

def z221 : W := mkw 0x00200220c0200634 0x40040044180400c6 0x20000623e0001ffa 0x040000c47c0003ff

def z222 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0xdff001dc1ffc0004 0xfbfe003b83ff8000

def z223 : W := mkw 0x0490000004900000 0x0092000000920000 0x48f0000000fc0000 0x891e0000001f8000

def z224 : W := mkw 0x0101058300000000 0x002020b060000000 0x200007c380000002 0x040000f870000000

def z225 : W := mkw 0x0065daaaf06ae6bc 0xe00cbb555e0d5cd7 0xf8effe23e0e3ffff 0xbf1dffc47c1c7fff

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8e0000000e00004 0xbb1c0000001c0000

def z227 : W := mkw 0x27fff7fbfb0318c0 0x84fffeff7f606318 0xf7ffffffff039ce7 0xfeffffffffe0739c

def z228 : W := mkw 0x0000000000200634 0x40000000000400c6 0x0000000000001ff8 0x00000000000003ff

def z229 : W := mkw 0x01019dce390e398a 0xa02033b9c721c731 0xbf13fffe7f1e7f9f 0xf7e27fffcfe3cff3

def z230 : W := mkw 0x0b2b87f71b271fc7 0x816570fee364e3f8 0xb70f87ff9f039fe7 0x76e1f0fff3e073fc

def z231 : W := mkw 0x3fffffffffffff07 0x07ffffffffffffe0 0xffffffffffffff07 0xffffffffffffffe0

def z232 : W := mkw 0x004440000040c000 0x0008880000081800 0x50ec000000e18000 0x2a1d8000001c3000

def z233 : W := mkw 0x080000440d941903 0x0100000881b28320 0x000000001f1c0000 0x0000000003e38000

def z234 : W := mkw 0x2db117ffedb41f07 0x05b622fffdb683e0 0xfff007fffffc1f06 0xfffe00ffffff83e0

def z235 : W := mkw 0x0000180820082008 0x2000030104010401 0x0000780060006018 0x00000f000c000c03

def z236 : W := mkw 0x0490000000000000 0x0092000000000000 0xc7f0000000000000 0xf8fe000000000000

def z237 : W := mkw 0x000000000060c634 0x40000000000c18c6 0x0800000000e06318 0x01000000001c0c63

def z238 : W := mkw 0x27df759be0000000 0x04fbeeb37c000000 0x071ff9dfe0000001 0x40e3ff3bfc000000

def z239 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8013f9fe781c0003 0xd0027f3fcf038000

def z240 : W := mkw 0x212117ffe804118a 0xa42422fffd008231 0x200007ffe000139a 0x040000fffc000273

def z241 : W := mkw 0x16dee8441edff18a 0xa2dbdd0883dbfe31 0xdffff8001ffff39d 0xfbffff0003fffe73

def z242 : W := mkw 0x020b98cf3a0f31ca 0xa0417319e741e639 0x881ff9fff81ff3ff 0xd103ff3fff03fe7f

def z243 : W := mkw 0x27fe6731c0000000 0x04ffcce638000000 0xe7ec4623e0000003 0xbcfd88c47c000000

def z244 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x88100000181c0004 0xd102000003038000

def z246 : W := mkw 0x16de600006d1c000 0x02dbcc0000da3800 0xdffc00001ffd8004 0xfbff800003ffb000

def z247 : W := mkw 0x012107e3c9201ef4 0xc02420fc792403de 0x200007e3e0001ffa 0x040000fc7c0003ff

def z248 : W := mkw 0x0000180c200c210a 0x2000030184018421 0x8810783e601e739f 0x91020f07cc03ce73

def z249 : W := mkw 0x27bb37bbe0000000 0x04f766f77c000000 0x2713bfffe0000002 0x44e277fffc000000

def z250 : W := mkw 0x169aa80016dbe000 0x02d3550002db7c00 0x1f13b8001fffe004 0x43e2770003fffc00

def z251 : W := mkw 0x224f708be040c030 0x4449ee117c081806 0x000ff803e003e0f9 0x0001ff007c007c1f

def z252 : W := mkw 0x279bbddf380e318a 0xa4f377bbe701c631 0x8f13f9fe781e739f 0xd1e27f3fcf03ce73

def z253 : W := mkw 0x0120073000000000 0x002400e600000000 0x200007fc00000002 0x040000ff80000000

def z254 : W := mkw 0x379bbd9b369b2000 0x06f377b366d36400 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z255 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67effe03e0000001 0x2cfdffc07c000000

def z256 : W := mkw 0x0db007740d941903 0x01b600ee81b28320 0xe7f007fc1f1c0002 0xfcfe00ff83e38000

def z257 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x70ec4603e0e3ecf9 0x2e1d88c07c1c7d9f

def z258 : W := mkw 0x010105c3090018c0 0x802020b861200318 0xb70007c39f001ce6 0x76e000f873e0039c

def z259 : W := mkw 0x1fbaaf741fbf3f07 0x03f755ee83f7e7e0 0xfff3bffc1ffc1f06 0xfffe77ff83ff83e0

def z260 : W := mkw 0x069a200000000000 0x00d3440000000000 0x0713b80000000000 0x40e2770000000000

def z261 : W := mkw 0x006552aae060c634 0x400caa555c0c18c6 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z262 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xfffffe039ffffce7 0xffffffc073ffff9c

def z263 : W := mkw 0x000080401b0318c0 0x8000100803606318 0x000000001f000000 0x0000000003e00000

def z264 : W := mkw 0x08644264cdf4df37 0x410c884c99be9be6 0xf8ec4623ffffffff 0xbf1d88c47fffffff

def z265 : W := mkw 0x0db117fe2db41f8f 0xa1b622ffc5b683f1 0xfff007fe7ffc1f9e 0xfffe00ffcfff83f3

def z266 : W := mkw 0x04d4600000000000 0x009a8c0000000000 0x40f0780000000000 0x881e0f0000000000

def z267 : W := mkw 0x24f5fafef80e318a 0xa49ebf5fdf01c631 0xc8f3f9fe781e739f 0xd91e7f3fcf03ce73

def z268 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0803f802781e739d 0x01007f004f03ce73

def z269 : W := mkw 0x04908800149a2000 0x0092110002934400 0xdff3f8001ffe6005 0xfbfe7f0003ffcc00

def z270 : W := mkw 0x00644220c0000000 0x000c884418000000 0xe0ec4623e0000003 0xbc1d88c47c000000

def z271 : W := mkw 0x00008800100a2088 0xa000110002014411 0x0000000000026098 0x0000000000004c13

def z272 : W := mkw 0x2ffe6731c5b00e05 0x05ffcce638b601c0 0x77ec060187e00c00 0x2efd80c030fc0180

def z273 : W := mkw 0x080000440db41f07 0x0100000881b683e0 0x180000001ffc1f04 0x0300000003ff83e0

def z274 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x77f007dc1ffc0c00 0x6efe00fb83ff8180

def z275 : W := mkw 0x020a800012030000 0x0041500002406000 0x070380001f000000 0x40e0700003e00000

def z276 : W := mkw 0x169bb8ce3e9f318a 0xa2d37719c7d3e631 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z277 : W := mkw 0x00008000120300c0 0x8000100002406018 0x00000000000380e0 0x000000000000701c

def z278 : W := mkw 0x010105c3090018c0 0x802020b861200318 0x200007c380001ce2 0x040000f87000039c

def z279 : W := mkw 0x224ff08bf20300c0 0x8449fe117e406018 0x000ff803e00380e1 0x0001ff007c00701c

def z280 : W := mkw 0x1000000006d1c000 0x0200000000da3800 0x1000000007e18000 0x0200000000fc3000

def z281 : W := mkw 0x124ee80016dbe000 0x0249dd0002db7c00 0x180ff8001fffe005 0x0301ff0003fffc00

def z282 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x970f81c01f038005 0x72e1f03803e07000

def z283 : W := mkw 0x17deed401fdbf800 0x02fbdda803fb7f00 0xffffffc01ffffc07 0xfffffff803ffff80

def z284 : W := mkw 0x006552aae0000000 0x000caa555c000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z285 : W := mkw 0x27fff7fbfb0318c0 0x84fffeff7f606318 0xe7ffffffff000003 0xfcffffffffe00000

def z286 : W := mkw 0x000110ce28041102 0x00002219c5008220 0x8813f9fe781c1307 0xd1027f3fcf038260

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x801001fc00000002 0xd002003f80000000

def z288 : W := mkw 0x27ff77bbe0200634 0x44ffeef77c0400c6 0xe7ffffffe0001ffb 0xfcfffffffc0003ff

def z289 : W := mkw 0x00645a2ce06ce73e 0x600c8b459c0d9ce7 0xf8fc7e3fe0ffffff 0xbf1f8fc7fc1fffff

def z290 : W := mkw 0x0fba07750fb51f47 0x01f740eea1f6a3e8 0xfffc07fd9ffd9f66 0xffff80ffb3ffb3ec

def z291 : W := mkw 0x0045d8cef84ef1ba 0xe008bb19df09de37 0x881ff9fff81ff3ff 0xd103ff3fff03fe7f

def z292 : W := mkw 0x2101159b20000000 0x042022b364000000 0x000001dc00000000 0x0000003b80000000

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000200021087 0x1000000040004210

def z294 : W := mkw 0x000180c218021080 0x8000301843004210 0x000381c018000000 0x4000703803000000

def z295 : W := mkw 0x05b0077408041102 0x00b600ee81008220 0xeff007fc181c1306 0xfdfe00ff83038260

def z296 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x070381c01f000000 0x40e0703803e00000

def z297 : W := mkw 0x069a800016930000 0x00d3500002d26000 0xdfff80001fff8005 0xfbfff00003fff000

def z298 : W := mkw 0x0cb0023404b40707 0x01960046809680e0 0xf8f0063c00fc1f06 0xbf1e00c7801f83e0

def z299 : W := mkw 0x324ff88bf24be000 0x0649ff117e497c00 0x000ff803e003e001 0x0001ff007c007c00

def z300 : W := mkw 0x00200220c060c634 0x40040044180c18c6 0x38000623e0e3fffe 0x070000c47c1c7fff

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000002739c 0x0100000000004e73

def z302 : W := mkw 0x1ffeef3017fbee05 0x03ffdde602ff7dc0 0xfffffe001fffec05 0xffffffc003fffd80

def z303 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x870381c21f021087 0x50e0703843e04210

def z304 : W := mkw 0x0db01f7c2dbc3f0f 0x21b603ef85b787e1 0xfff07ffc7ffc7f1e 0xfffe0fff8fff8fe3

def z305 : W := mkw 0x030a05410b011840 0x006140a821602308 0xb70c07c19f019c66 0x76e180f833e0338c

def z306 : W := mkw 0x17de650107d1c840 0x02fbcca020fa3908 0x77ec060187e18c60 0x2efd80c030fc318c

def z307 : W := mkw 0x0c9000440db41f07 0x0192000881b683e0 0xdff000001ffc1f04 0xfbfe000003ff83e0

def z308 : W := mkw 0x010105c3090018c0 0x802020b861200318 0xb00c07c380039ce7 0x360180f87000739c

def z309 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0x8f13f8001f1e6005 0xd1e27f0003e3cc00

def z310 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x48ec4023e0e3e3f9 0x891d88047c1c7c7f

def z311 : W := mkw 0x37fe6731c6d1c000 0x06ffcce638da3800 0x77ec060187e18000 0x2efd80c030fc3000

def z312 : W := mkw 0x124e60000241c000 0x0249cc0000483800 0x000c000000018000 0x0001800000003000

def z313 : W := mkw 0x020a800012030000 0x0041500002406000 0x000f800000038001 0x0001f00000007000

def z314 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x5fec00001fffe004 0x2bfd800003fffc00

def z315 : W := mkw 0x004440000040c000 0x0008880000081800 0xd8ec402260e3f39f 0xbb1d88044c1c7e73

def z316 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70387c01f001c06 0x76e070f803e00380

def z317 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z318 : W := mkw 0x030b05c30b0118c0 0x806160b861602318 0x370c07c387019ce2 0x26e180f870e0339c

def z319 : W := mkw 0x37fffffbffdbf8c0 0x86ffffff7ffb7f18 0xfffffffffffffce7 0xffffffffffffff9c

def z320 : W := mkw 0x16dee8401fdbf8c0 0x82dbdd0803fb7f18 0xdffff8001ffffce5 0xfbffff0003ffff9c

def z321 : W := mkw 0x180088441fffff07 0x0300110883ffffe0 0x180000001fffff04 0x0300000003ffffe0

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000226000139a 0x000000044c000273

def z323 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x4ff001fc1ffc0300 0xc9fe003f83ff8060

def z324 : W := mkw 0x0490000004900000 0x0092000000920000 0x071000001f1c0000 0x40e2000003e38000

def z325 : W := mkw 0x000000000060c634 0x40000000000c18c6 0x9800402260e3ffff 0x930008044c1c7fff

def z326 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x8813f800181e739d 0xd1027f000303ce73

def z327 : W := mkw 0x0001108a20000000 0x0000221144000000 0x000001fe60000002 0x0000003fcc000000

def z328 : W := mkw 0x27ff77bbe0200604 0x04ffeef77c0400c0 0xffffffffe0e01f07 0xfffffffffc1c03e0

def z329 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8813f9dc181e6005 0xd1027f3b8303cc00

def z330 : W := mkw 0x06dee00012030000 0x00dbdc0002406000 0xd7fff8001f038005 0xfaffff0003e07000

def z331 : W := mkw 0x27ff77bbe040c030 0x44ffeef77c081806 0xe7ffffffe003e0fb 0xfcfffffffc007c1f

def z332 : W := mkw 0x0d90051005900801 0x01b200a200b20100 0x0700000007000000 0x00e0000000e00000

def z333 : W := mkw 0x0000004408041102 0x0000000881008220 0x08000000181c1304 0x0100000003038260

def z334 : W := mkw 0x020a000002010000 0x0041400000402000 0x170c000007018000 0x22e1800000e03000

def z335 : W := mkw 0x0920077409241f07 0x012400ee812483e0 0xf8e007fc00e01f06 0xbf1c00ff801c03e0

def z336 : W := mkw 0x0001988a300a2088 0xa000331146014411 0x8803f8226002739f 0x91007f044c004e73

def z337 : W := mkw 0x232b97fbfb0318c0 0x846572ff7f606318 0xb70f87ffff039ce7 0x76e1f0ffffe0739c

def z338 : W := mkw 0x2fff77ffed941903 0x05ffeefffdb28320 0xe7ffffffff1c0003 0xfcffffffffe38000

def z339 : W := mkw 0x04f44220c4f0c634 0x409e8844189e18c6 0xfffc4623ffffffff 0xffff88c47fffffff

def z340 : W := mkw 0x216557bbe060c634 0x442caaf77c0c18c6 0xf8ec47ffe0e3ffff 0xbf1d88fffc1c7fff

def z341 : W := mkw 0x16fe6220c6f1c634 0x42dfcc4418de38c6 0x77ec060187e18c60 0x2efd80c030fc318c

def z342 : W := mkw 0x16de680004d8e000 0x02dbcd00009b1c00 0xcffff80000fc6001 0xf9ffff00001f8c00

def z343 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff047fe7ffe7f9f 0xfffe08ffcfffcff3

def z344 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8e0462060e07f1e 0xbf1c08c40c1c0fe3

def z345 : W := mkw 0x27fff7bbf2030000 0x04fffef77e406000 0xf7ffffffff038007 0xfeffffffffe07000

def z346 : W := mkw 0x00644220c040c000 0x000c884418081800 0xf8ec4623e0e3e007 0xbf1d88c47c1c7c00

def z347 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x78ec060180e3fffc 0x2f1d80c0301c7fff

def z348 : W := mkw 0x030b058303010840 0x006160b060602108 0xb70f87c387018c63 0x76e1f0f870e0318c

def z349 : W := mkw 0x000188c2180a3080 0x8000311843014610 0x8813f9c2181e7087 0xd1027f384303ce10

def z350 : W := mkw 0x036fdfeffb6ffffe 0xe06dfbfdff6dffff 0xffffffffffffffff 0xffffffffffffffff

def z351 : W := mkw 0x0100050101000840 0x002000a020200108 0x2000060180000c60 0x040000c03000018c

def z352 : W := mkw 0x179badc31f9b38c0 0x82f375b863f36718 0xb71fbfc39f1f9ce7 0x76e3f7f873e3f39c

def z353 : W := mkw 0x010185c219021880 0x802030b843204310 0xb70387c21f021c87 0x76e070f843e04390

def z354 : W := mkw 0x0800000005b00e05 0x0100000000b601c0 0x1000000007e00c00 0x0200000000fc0180

def z355 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfffc07ff9fff9fe7 0xffff80fff3fff3fc

def z356 : W := mkw 0x0db00774cdb41f37 0x41b600ee99b683e6 0xfff007fffffc1ffe 0xfffe00ffffff83ff

def z357 : W := mkw 0x224f708be0000000 0x0449ee117c000000 0x801ff9ffe0000003 0xd003ff3ffc000000

def z358 : W := mkw 0x00200220c0200634 0x40040044180400c6 0xa8004623e0027fff 0x950008c47c004fff

def z359 : W := mkw 0x2fbb37ff2db41f07 0x05f766ffe5b683e0 0xfff3bffc1ffc1f06 0xfffe77ff83ff83e0

def z360 : W := mkw 0x05b19ffe380e318a 0xa0b633ffc701c631 0xeff3fffe781e739f 0xfdfe7fffcf03ce73

def z361 : W := mkw 0x030b85c318021080 0x806170b863004210 0xa70f87c398021087 0x74e1f0f873004210

def z362 : W := mkw 0x17deed0117dbe840 0x02fbdda022fb7d08 0xfffffe019fffec65 0xffffffc033fffd8c

def z363 : W := mkw 0x1cf46a3404fce707 0x039e8d46809f9ce0 0x48f0783c00fc6300 0x891e0f07801f8c60

def z364 : W := mkw 0x0f9b85d71f9719c3 0x81f370bae3f2e338 0x071381dc1f1c0000 0x40e2703b83e38000

def z365 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x200c4623e003fffb 0x040188c47c007fff

def z366 : W := mkw 0x0db0073005b00e05 0x01b600e600b601c0 0xfff006001ffc0c04 0xfffe00c003ff8180

def z367 : W := mkw 0x020b80c31a0310c0 0x8041701863406218 0x800f81c3980390e7 0x5001f0387300721c

def z368 : W := mkw 0x1fdeed541fdff903 0x03fbddaa83fbff20 0xdffff9dc1fffe005 0xfbffff3b83fffc00

def z369 : W := mkw 0x030b9dcb3b0b38c8 0xa06173b967616719 0xb70fffc3ff03fcff 0x76e1fff87fe07f9f

def z370 : W := mkw 0x000180c21b0318c0 0x8000301843606318 0x900381c21f039ce7 0x5200703843e0739c

def z371 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70c060387039ce7 0x36e180c070e0739c

def z372 : W := mkw 0x2ffffffffdbe3f8f 0xa5ffffffffb7c7f1 0xfffffffffffe7f9f 0xffffffffffffcff3

def z373 : W := mkw 0x14d4680004d8e000 0x029a8d00009b1c00 0xd8fc780000ffe005 0xbb1f8f00001ffc00

def z374 : W := mkw 0x37ffffbbf69b2000 0x06fffff77ed36400 0xe7ffffffff1c0003 0xfcffffffffe38000

def z375 : W := mkw 0x124ee800124be000 0x0249dd0002497c00 0x970ff8001f03e005 0x72e1ff0003e07c00

def z376 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0003f9fe6002739b 0x00007f3fcc004e73

def z377 : W := mkw 0x0000000003010840 0x0000000000602108 0x1000000007018c60 0x0200000000e0318c

def z378 : W := mkw 0x27ff77ffe8041102 0x04ffeefffd008220 0xeffffffff81c1307 0xfdffffffff038260

def z379 : W := mkw 0x27fe6731c060c634 0x44ffcce6380c18c6 0x77ec060180e18c60 0x2efd80c0301c318c

def z380 : W := mkw 0x1df46f740dfcff07 0x03be8dee81bf9fe0 0xfff07ffc1ffc7f06 0xfffe0fff83ff8fe0

def z381 : W := mkw 0x00200220c0200634 0x40040044180400c6 0x2000060180000c60 0x040000c03000018c

def z382 : W := mkw 0x034fc5c3db43d8f0 0xc069f8b87b687b1e 0xb70fc7c3ff03fcff 0x76e1f8f87fe07f9f

def z383 : W := mkw 0x17dfed8316dbe000 0x02fbfdb062db7c00 0xffffffc39fffe007 0xfffffff873fffc00

def z384 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x00000000181c0000 0x0000000003038000

def z385 : W := mkw 0x27fff7fbf8021080 0x84fffeff7f004210 0xe7fffffff8021087 0xfcffffffff004210

def z386 : W := mkw 0x000180c618061182 0x80003018c300c230 0x881381fe181e1387 0xd102703fc303c270

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800002000001306 0x9100000400000260

def z388 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x57ffb8001ffd8000 0x6afff70003ffb000

def z389 : W := mkw 0x37ff7fbbe4d8e000 0x06ffeff77c9b1c00 0xefffffffe0fc6003 0xfdfffffffc1f8c00

def z390 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xc8e0402260e2739f 0x991c08044c1c4e73

def z391 : W := mkw 0x036fc7e3db0318c0 0x806df8fc7b606318 0xf7efc7e3ff039ce7 0xfefdf8fc7fe0739c

def z392 : W := mkw 0x030b95cb3b0318c0 0x806172b967606318 0xb71fffffff039ce7 0xf6e3ffffffe0739c

def z393 : W := mkw 0x27fe6731c060c634 0x44ffcce6380c18c6 0xffec4623e0e3ffff 0xbffd88c47c1c7fff

def z394 : W := mkw 0x049000440c941102 0x0092000881928220 0xdff001fc1ffc1306 0xfbfe003f83ff8260

def z395 : W := mkw 0x05b0073000200604 0x00b600e6000400c0 0xfff007fc00e01f06 0xfffe00ff801c03e0

def z396 : W := mkw 0x27df759b20000000 0x04fbeeb364000000 0xc7fff9dc00000001 0xf8ffff3b80000000

def z397 : W := mkw 0x06fe6220c060c634 0x40dfcc44180c18c6 0xfffffe23e0e3ffff 0xffffffc47c1c7fff

def z398 : W := mkw 0x0044400000000000 0x0008880000000000 0xc0ec400000000001 0xb81d880000000000

def z399 : W := mkw 0x026ec220d263c634 0x404dd8441a4c78c6 0xffefc623ffe3ffff 0xfffdf8c47ffc7fff

def z400 : W := mkw 0x224e6001c0000000 0x0449cc0038000000 0x000c000180000000 0x0001800030000000

def z401 : W := mkw 0x036f47a3c0000000 0x006de8f478000000 0xe7efc7e3e0000003 0xfcfdf8fc7c000000

def z402 : W := mkw 0x2001108be0000000 0x040022117c000000 0x00000003e0000000 0x000000007c000000

def z403 : W := mkw 0x20447008e0000000 0x04088e011c000000 0x0000780060000000 0x00000f000c000000

def z404 : W := mkw 0x27bb37bb20000000 0x04f766f764000000 0xe7f3bffc00000002 0xfcfe77ff80000000

def z405 : W := mkw 0x27ff77bbe4900000 0x04ffeef77c920000 0xfffffffffffc0007 0xffffffffffff8000

def z406 : W := mkw 0x0065c2e2d862d6b4 0xc00cb85c5b0c5ad6 0xf8efc7e3f8e3ffff 0xff1df8fc7f1c7fff

def z407 : W := mkw 0x37fffffffedff18a 0xa6ffffffffdbfe31 0xfffffffffffff39f 0xfffffffffffffe73

def z408 : W := mkw 0x000110ce2804118a 0xa0002219c5008231 0x880041fe6002739f 0x9100083fcc004e73

def z409 : W := mkw 0x100088401fdbf8c0 0x8200110803fb7f18 0x180000001ffffce4 0x0300000003ffff9c

def z410 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xd8ec402060e3e31d 0xbb1d88040c1c7c63

def z411 : W := mkw 0x0000800010020000 0x0000100002004000 0x8003800018020005 0x5000700003004000

def z412 : W := mkw 0x00644220c040c030 0x400c884418081806 0xe0ec4623e003e0fb 0xbc1d88c47c007c1f

def z413 : W := mkw 0x020a80401b0318c0 0x8041500803606318 0x970f80001f039ce5 0x72e1f00003e0739c

def z414 : W := mkw 0x16dff8ce3edff18a 0xa2dbff19c7dbfe31 0xdffff9dc1fffe005 0xfbffff3b83fffc00

def z415 : W := mkw 0x024e600000000000 0x0049cc0000000000 0x000ff80000000001 0x0001ff0000000000

def z416 : W := mkw 0x030b8583130308c0 0x806170b062606118 0x370f860387038ce1 0x26e1f0c070e0719c

def z417 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xe8ec4623e0e0631b 0xbd1d88c47c1c0c63

def z418 : W := mkw 0x27ffffbbf00a2000 0x04fffff77e014400 0xeffffffff81e6007 0xfdffffffff03cc00

def z419 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x7fe006001ffc1f04 0x2ffc00c003ff83e0

def z420 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x88004022781e739f 0x910008044f03ce73

def z421 : W := mkw 0x279a251100000000 0x04f344a220000000 0x0700000000000000 0x00e0000000000000

def z422 : W := mkw 0x27ff77fbe9001800 0x04ffeeff7d200300 0xf7ffffffff001c07 0xfeffffffffe00380

def z423 : W := mkw 0x130b8dc31fdbf8c0 0x826171b863fb7f18 0xbf0f87c39ffffce7 0x77e1f0f873ffff9c

def z424 : W := mkw 0x0b0b85c71fb71fc7 0x816170b8e3f6e3f8 0xbf0f87c39fff9fe7 0x77e1f0f873fff3fc

def z425 : W := mkw 0x17ffefe3dffbfef4 0xc2fffdfc7bff7fde 0xffffffe3ffffffff 0xfffffffc7fffffff

def z426 : W := mkw 0x24f47a3ce00c210a 0x249e8f479c018421 0x48f0783c601c6318 0x891e0f078c038c63

def z427 : W := mkw 0x080000440df4df37 0x4100000881be9be6 0x180000001ffffffc 0x0300000003ffffff

def z428 : W := mkw 0x030b8583120300c0 0x806170b062406018 0xa70f87c3800380e3 0x74e1f0f87000701c

def z429 : W := mkw 0x16dff88a36dbe000 0x02dbff1146db7c00 0xdffff9fe7fffe007 0xfbffff3fcffffc00

def z430 : W := mkw 0x27fffffff86ef7be 0xe4ffffffff0ddef7 0xfffffffff8ffffff 0xffffffffff1fffff

def z431 : W := mkw 0x0000004408041102 0x0000000881008220 0x000001fc00001302 0x0000003f80000260

def z432 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xefffffffe0e0631b 0xfdfffffffc1c0c63

def z433 : W := mkw 0x212117bbe0200634 0x442422f77c0400c6 0x200007ffe0001ffa 0x040000fffc0003ff

def z434 : W := mkw 0x24f46230c0000000 0x049e8c4618000000 0x40e0000000000000 0x081c000000000000

def z435 : W := mkw 0x0000100820000000 0x0000020104000000 0x0010783c60000000 0x80020f078c000000

def z436 : W := mkw 0x1490280004982000 0x0292050000930400 0x00103800001c0000 0x0002070000038000

def z437 : W := mkw 0x006442200060c604 0x000c8844000c18c0 0xf8ec462000e3ff07 0xbf1d88c4001c7fe0

def z438 : W := mkw 0x030b858312030000 0x006170b062406000 0xb70f87c39f038007 0x76e1f0f873e07000

def z439 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x8713f9fe60000003 0xd0e27f3fcc000000

def z440 : W := mkw 0x020b80c31b0318c0 0x8041701863606318 0x100f80039f039ce5 0x0201f00073e0739c

def z441 : W := mkw 0x00644264c864d736 0x400c884c990c9ae6 0xf8fc47fff8ffffff 0xff1f88ffff1fffff

def z442 : W := mkw 0x0df44730c5f0ce35 0x41be88e618be19c6 0xffec4623e7e3ffff 0xbffd88c47cfc7fff

def z443 : W := mkw 0x0cb002740cb41707 0x0196004e819682e0 0xc8f001fc18fc1306 0xd91e003f831f8260

def z444 : W := mkw 0x0db187f61db61f87 0x81b630fec3b6c3f0 0xfff387fe1ffe1f87 0xfffe70ffc3ffc3f0

def z445 : W := mkw 0x1ffffffe3fffff8f 0xa3ffffffc7fffff1 0xfffffffe7fffff9f 0xffffffffcffffff3

def z446 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x48fff80000ffe001 0x891fff00001ffc00

def z447 : W := mkw 0x27fe6731c0000000 0x04ffcce638000000 0xe7fffe0180000001 0xfcffffc030000000

def z448 : W := mkw 0x0100054009001800 0x002000a801200300 0x070001c01f000000 0x40e0003803e00000

def z449 : W := mkw 0x07bb87f31b0318c0 0x80f770fe63606318 0xf7ff87ff9f039ce7 0xfefff0fff3e0739c

def z450 : W := mkw 0x16de600006d1c000 0x02dbcc0000da3800 0xd7fff80007e18001 0xfaffff0000fc3000

def z451 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0013b9fe781c139a 0x4002773fcf038273

def z452 : W := mkw 0x0064ca64d86ef7be 0xe00c994c9b0ddef7 0xf8ec4623f8ffffff 0xbf1d88c47f1fffff

def z453 : W := mkw 0x14f46a20c4f8e634 0x429e8d44189f1cc6 0x48f0782060fc6318 0x891e0f040c1f8c63

def z454 : W := mkw 0x126eea20d26be634 0x424ddd441a4d7cc6 0xf8effe23e0e3ffff 0xbf1dffc47c1c7fff

def z455 : W := mkw 0x279bb5db3b0318c0 0x84f376bb67606318 0x0713b9dc1f000000 0x40e2773b83e00000

def z456 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0xb71007dc1f1c1c06 0x76e200fb83e38380

def z457 : W := mkw 0x07bb07b300000000 0x00f760f660000000 0xe7ff87ff80000003 0xfcfff0fff0000000

def z458 : W := mkw 0x000190ca38021080 0x8000321947004210 0x8013f9fe78021087 0xd0027f3fcf004210

def z459 : W := mkw 0x0000980c300e210a 0x200013018601c421 0x8813f83c781e631d 0xd1027f078f03cc63

def z460 : W := mkw 0x0cb01a3c24bc270f 0x21960347849784e1 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z461 : W := mkw 0x0001808210020080 0x8000301042004010 0x0003800200020081 0x0000700040004010

def z462 : W := mkw 0x092007740db41f07 0x012400ee81b683e0 0x380007fc1ffc1f06 0x070000ff83ff83e0

def z463 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xa70f87c39f000003 0x74e1f0f873e00000

def z464 : W := mkw 0x0db08f741dbe3f07 0x01b611ee83b7c7e0 0xfff3fffc1ffe7f07 0xfffe7fff83ffcfe0

def z465 : W := mkw 0x0001008200000000 0x0000201040000000 0x800381c200000003 0x5000703840000000

def z466 : W := mkw 0x00644220c0000000 0x000c884418000000 0x40e0402060000000 0x881c08040c000000

def z467 : W := mkw 0x05b117ba20000000 0x00b622f744000000 0xe7f3fffe60000003 0xfcfe7fffcc000000

def z468 : W := mkw 0x010085401b0318c0 0x802010a803606318 0xb70007c01f039ce6 0x76e000f803e0739c

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c000000038005 0x3201800000007000

def z470 : W := mkw 0x020a800012030000 0x0041500002406000 0xb70f86039f039ce7 0x76e1f0c073e0739c

def z471 : W := mkw 0x0920077409241f07 0x012400ee812483e0 0xb70007fc1f001f06 0x76e000ff83e003e0

def z472 : W := mkw 0x37feef31d6dbe000 0x06ffdde63adb7c00 0xfffffe019fffe005 0xffffffc033fffc00

def z473 : W := mkw 0x000110ce2804118a 0xa0002219c5008231 0x881001fe781c139e 0xd102003fcf038273

def z474 : W := mkw 0x0000004408041102 0x0000000881008220 0x881041fe781e739f 0xd102083fcf03ce73

def z475 : W := mkw 0x05f44730c0000000 0x00be88e618000000 0xe7fc47ffe0000003 0xfcff88fffc000000

def z476 : W := mkw 0x14d4780c24dce10a 0x229a8f01849b9c21 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z477 : W := mkw 0x00008800100a2000 0x0000110002014400 0x8813f822781e739f 0xd1027f044f03ce73

def z478 : W := mkw 0x100198ce3edff18a 0xa2003319c7dbfe31 0x9813f9fe7ffff39f 0xd3027f3fcffffe73

def z479 : W := mkw 0x16de600006d1c000 0x02dbcc0000da3800 0xdfec400007e3e005 0xbbfd880000fc7c00

def z480 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8ec062180e19f66 0xbf1d80c4301c33ec

def z481 : W := mkw 0x0001988a300a2000 0x0000331146014400 0x8813f9fe781e6007 0xd1027f3fcf03cc00

def z482 : W := mkw 0x0000000400040102 0x0000000080008020 0x0810003c001c0300 0x8102000780038060

def z483 : W := mkw 0x16dfe88316dbe0c0 0x82dbfd1062db7c18 0xdffff8039fffe0e5 0xfbffff0073fffc1c

def z484 : W := mkw 0x279bbddf380e318a 0xa4f377bbe701c631 0x0713b9dc181c0000 0x40e2773b83038000

def z485 : W := mkw 0x1000880016fbe634 0x4200110002df7cc6 0x180000001ffffffc 0x0300000003ffffff

def z486 : W := mkw 0x09219ffe392e3f8f 0xa12433ffc725c7f1 0xa813fffe781e7f9f 0xd5027fffcf03cff3

def z487 : W := mkw 0x17feef3016dbe000 0x02ffdde602db7c00 0xfffffffc1fffe007 0xffffffff83fffc00

def z488 : W := mkw 0x16feea20d6dbe000 0x02dfdd441adb7c00 0xfffffe23ffffe007 0xffffffc47ffffc00

def z489 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x170381c01f039ce4 0x42e0703803e0739c

def z490 : W := mkw 0x0000804018021080 0x8000100803004210 0x0000000018021084 0x0000000003004210

def z491 : W := mkw 0x010185c31b0318c0 0x802030b863606318 0x300007c39f039ce6 0x060000f873e0739c

def z492 : W := mkw 0x030a050103010840 0x006140a020602108 0x0700000007000000 0x00e0000000e00000

def z493 : W := mkw 0x16feea20d6fbe634 0x42dfdd441adf7cc6 0xdffff8207fffe31d 0xfbffff040ffffc63

def z494 : W := mkw 0x27fff7bbf20300c0 0x84fffef77e406018 0xe7ffffffe00380e3 0xfcfffffffc00701c

def z495 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8013b9de181e1087 0x5002773bc303c210

def z496 : W := mkw 0x082002640db41f07 0x0104004c81b683e0 0xf8e006201ffc1f06 0xbf1c00c403ff83e0

def z497 : W := mkw 0x0920077409241f07 0x012400ee812483e0 0xa81007fc181c1f06 0xd50200ff830383e0

def z498 : W := mkw 0x024fc083d243c0f0 0xc049f8107a48781e 0x000fc003e003e0f9 0x0001f8007c007c1f

def z499 : W := mkw 0x16de680006d9e000 0x02dbcd0000db3c00 0x5ffc780007fde000 0xabff8f0000ffbc00

def z500 : W := mkw 0x14d5f8ce3cdef18a 0xa29abf19c79bde31 0xc8f3f9fe78fe739f 0xd91e7f3fcf1fce73

def z501 : W := mkw 0x0d919dde3d9e398b 0xa1b233bbc7b3c731 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z502 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0813b9dc181e739c 0x4102773b8303ce73

def z503 : W := mkw 0x212117fbe90018c0 0x842422ff7d200318 0x200007ffe0001ce2 0x040000fffc00039c

def z504 : W := mkw 0x20201238e0000000 0x040402471c000000 0x0000003c60000000 0x000000078c000000

def z505 : W := mkw 0x16dee00016d3c000 0x02dbdc0002da7800 0xd7ef80001fe38005 0x7afdf00003fc7000

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000402260000003 0x900008044c000000

def z507 : W := mkw 0x0100054009001800 0x002000a801200300 0x200007c000001c02 0x040000f800000380

def z508 : W := mkw 0x002002200060c634 0x40040044000c18c6 0xf8e0062000e3fffe 0xbf1c00c4001c7fff

def z509 : W := mkw 0x14d4e80014dae000 0x029a9d00029b5c00 0xc8f3f80018fe6005 0xd91e7f00031fcc00

def z510 : W := mkw 0x279b359b20000000 0x04f366b364000000 0xa71fbfdf80000003 0x74e3f7fbf0000000

def z511 : W := mkw 0x124ff8ce3a4ff18a 0xa249ff19c749fe31 0x881ff9fe781ff39f 0xd103ff3fcf03fe73

def z512 : W := mkw 0x0001988e300e218a 0xa0003311c601c431 0x0813f83e601e6399 0x81027f07cc03cc73

def z513 : W := mkw 0x020b8083120300c0 0x8041701062406018 0x0003800000000000 0x0000700000000000

def z514 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xf7ffffffe0039ce7 0xfefffffffc00739c

def z515 : W := mkw 0x0045d8ce384ef18a 0xa008bb19c709de31 0xd8fff9fe78fff39f 0xfb1fff3fcf1ffe73

def z516 : W := mkw 0x004440000040c000 0x0008880000081800 0x48e0400000e06000 0x891c0800001c0c00

def z517 : W := mkw 0x00008800100a2000 0x0000110002014400 0x08000000181e6004 0x010000000303cc00

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00c060380000003 0x340180c070000000

def z519 : W := mkw 0x0590051000000000 0x00b200a200000000 0x071001dc00000000 0x40e2003b80000000

def z520 : W := mkw 0x16feea20d6fbe634 0x42dfdd441adf7cc6 0xfffffe019fffec65 0xffffffc033fffd8c

def z521 : W := mkw 0x16dee800124be000 0x02dbdd0002497c00 0xc7fff8000003e001 0xf8ffff0000007c00

def z522 : W := mkw 0x00444000c060c634 0x40088800180c18c6 0x180c4003e0e3fffd 0x030188007c1c7fff

def z523 : W := mkw 0x0000080000082000 0x0000010000010400 0x08107800001c6000 0x81020f0000038c00

def z524 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67ec07ffe0000002 0x2cfd80fffc000000

def z525 : W := mkw 0x079b85c31f9318c0 0x80f370b863f26318 0xffff87c39fff9ce7 0xfffff0f873fff39c

def z526 : W := mkw 0x21219ffff80e318a 0xa42433ffff01c631 0xa813fffff81e739f 0xd5027fffff03ce73

def z527 : W := mkw 0x0c90001404940103 0x0192000280928020 0x0010001c001c0000 0x0002000380038000

def z528 : W := mkw 0x000080401b63def4 0xc0001008036c7bde 0x180000001fe3fffc 0x0300000003fc7fff

def z529 : W := mkw 0x2ffe6775cdb41f07 0x05ffcceeb9b683e0 0xfffc07fd9ffc1f06 0xffff80ffb3ff83e0

def z530 : W := mkw 0x17dffdcf3fdff9ca 0xa2fbffb9e7fbff39 0xffffffffffffffff 0xffffffffffffffff

def z531 : W := mkw 0x16dee80016fbe634 0x42dbdd0002df7cc6 0xdffff8001ffffffd 0xfbffff0003ffffff

def z532 : W := mkw 0x000198ce3b0f39ca 0xa0003319c761e739 0x9813f9fe7f1fffff 0xd3027f3fcfe3ffff

def z533 : W := mkw 0x000180c218021080 0x8000301843004210 0x8803c1e27802739f 0xd100783c4f004e73

def z534 : W := mkw 0x020b98ce3a0f318a 0xa0417319c741e631 0x9f1ff9fe7f1ff39f 0xf3e3ff3fcfe3fe73

def z535 : W := mkw 0x05b0073000000000 0x00b600e600000000 0x67e0060000000000 0x2cfc00c000000000

def z536 : W := mkw 0x0000984c380e318a 0xa00013098701c631 0x0810783c781e739c 0x81020f078f03ce73

def z537 : W := mkw 0x169a200006910000 0x02d3440000d22000 0x0700000007000000 0x00e0000000e00000

def z538 : W := mkw 0x00444000c040c030 0x4008880018081806 0x0000400060006018 0x000008000c000c03

def z539 : W := mkw 0x030b85c31b63def4 0xc06170b8636c7bde 0xbf0f87c39fe3ffff 0x77e1f0f873fc7fff

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000001f000004 0x72e0000003e00000

def z541 : W := mkw 0x030a850113030840 0x006150a022606108 0xb70f86019f038c65 0x76e1f0c033e0718c

def z542 : W := mkw 0x0cf44234c4f4c737 0x419e8846989e98e6 0xf8fc463fe0ffffff 0xbf1f88c7fc1fffff

def z543 : W := mkw 0x226f72abe0000000 0x044dee557c000000 0xe0effe23e0000003 0xbc1dffc47c000000

def z544 : W := mkw 0x032b87e31b231ec4 0x806570fc636463d8 0xffef87e39fe39fe7 0xfffdf0fc73fc73fc

def z545 : W := mkw 0x179badc31f9b38c0 0x82f375b863f36718 0x0713b9c01f1c0000 0x40e2773803e38000

def z546 : W := mkw 0x0820023400240707 0x01040046800480e0 0x0000003c00000300 0x0000000780000060

def z547 : W := mkw 0x036f47a3c060c634 0x406de8f4780c18c6 0xffefc7e3e0e3ffff 0xfffdf8fc7c1c7fff

def z548 : W := mkw 0x1db08f741fffff07 0x03b611ee83ffffe0 0xfff007fc1fffff06 0xfffe00ff83ffffe0

def z549 : W := mkw 0x0001108a20000088 0xa000221144000011 0x0000000260000098 0x000000004c000013

def z550 : W := mkw 0x01644760c960de34 0x402c88ec192c1bc6 0xffec47e3ffe3ffff 0xfffd88fc7ffc7fff

def z551 : W := mkw 0x07dfe5c31b0318c0 0x80fbfcb863606318 0xf7ffffc39f039ce7 0xfefffff873e0739c

def z552 : W := mkw 0x030b05c3090018c0 0x806160b861200318 0xa70f87c380001ce3 0x74e1f0f87000039c

def z553 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0x971fb8001f1f8005 0x72e3f70003e3f000

def z554 : W := mkw 0x090005440db41f07 0x012000a881b683e0 0xbf0007c01ffc1f06 0x77e000f803ff83e0

def z555 : W := mkw 0x16dee800169b2000 0x02dbdd0002d36400 0xc7fff8001f1c0001 0xf8ffff0003e38000

def z556 : W := mkw 0x01019dcf390e39ca 0xa02033b9e721c739 0xa813fffff81e7fff 0xd5027fffff03cfff

def z557 : W := mkw 0x1edee8441fffff07 0x03dbdd0883ffffe0 0xdffff8001fffff05 0xfbffff0003ffffe0

def z558 : W := mkw 0x00008844186ef7be 0xe0001108830ddef7 0x1800000018fffffc 0x03000000031fffff

def z559 : W := mkw 0x27ff77fbe90018c0 0x84ffeeff7d200318 0xe7ffffffe0001ce3 0xfcfffffffc00039c

def z560 : W := mkw 0x030b05c309001800 0x006160b861200300 0xb70f87c39f001c07 0x76e1f0f873e00380

def z561 : W := mkw 0x0120076009201e04 0x002400ec012403c0 0xffe007e01fe01f06 0xfffc00fc03fc03e0

def z562 : W := mkw 0x27fe6731c3010840 0x04ffcce638602108 0x77ec060187018c60 0x2efd80c030e0318c

def z563 : W := mkw 0x030b95cf3b0719ca 0xa06172b9e760e339 0xb70f87ffff039fff 0x76e1f0ffffe073ff

def z564 : W := mkw 0x06dee800100a2000 0x00dbdd0002014400 0xcffff800181e6005 0xf9ffff000303cc00

def z565 : W := mkw 0x00444000c040c030 0x4008880018081806 0xd8ec4003e0e3e0fd 0xbb1d88007c1c7c1f

def z566 : W := mkw 0x00000000c0000030 0x4000000018000006 0x00000003e00000f8 0x000000007c00001f

def z567 : W := mkw 0x09644774c964df37 0x412c88ee992c9be6 0xf8ec47ffe0e3ffff 0xbf1d88fffc1c7fff

def z568 : W := mkw 0x0020022000200604 0x00040044000400c0 0xf8e0462260e27f9f 0xbf1c08c44c1c4ff3

def z569 : W := mkw 0x000188c6180e318a 0xa0003118c301c631 0x880381c2181e739f 0x510070384303ce73

def z570 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x77e007fc07e01f02 0x2efc00ff80fc03e0

def z571 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8813b9fc181c1306 0xd102773f83038260

def z572 : W := mkw 0x134fedc31b4bf8c0 0x8269fdb863697f18 0xb70fffc39f03fce7 0x76e1fff873e07f9c

def z573 : W := mkw 0x006552eee864d7be 0xe00caa5ddd0c9af7 0xf8ec47ffe0e3ffff 0xbf1d88fffc1c7fff

def z574 : W := mkw 0x2fff77ffe9241f07 0x05ffeefffd2483e0 0xe7ffffffe0001f03 0xfcfffffffc0003e0

def z575 : W := mkw 0x05b0077009001800 0x00b600ee01200300 0xf7f007fc1f001c06 0xfefe00ff83e00380

def z576 : W := mkw 0x00008844180e3102 0x000011088301c620 0x8813f9fc181e7307 0xd1027f3f8303ce60

def z577 : W := mkw 0x2cf4723ce4b40707 0x059e8e479c9680e0 0x48f0783c60fc0300 0x891e0f078c1f8060

def z578 : W := mkw 0x0ffe67740db41f07 0x01ffccee81b683e0 0xfffffffc1ffc1f07 0xffffffff83ff83e0

def z579 : W := mkw 0x030b9dcf380e318a 0xa06173b9e701c631 0xaf1ffffff81e739f 0xf5e3ffffff03ce73

def z580 : W := mkw 0x1064ca20d6fbe634 0x420c99441adf7cc6 0xf8ec4623ffffffff 0xbf1d88c47fffffff

def z581 : W := mkw 0x0f9b85d71f9719c3 0x81f370bae3f2e338 0xb71f87df9f1f9ce7 0x76e3f0fbf3e3f39c

def z582 : W := mkw 0x0000000004900000 0x0000000000920000 0x180000001ffc0004 0x0300000003ff8000

def z583 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x78ec4621e0e1ef78 0xaf1d88c43c1c3def

def z584 : W := mkw 0x124ee800124be000 0x0249dd0002497c00 0xd8eff80000e3e005 0xbb1dff00001c7c00

def z585 : W := mkw 0x0020022000200604 0x00040044000400c0 0x70e0060000e00c00 0x2e1c00c0001c0180

def z586 : W := mkw 0x27fffffffb0f39ca 0xa4ffffffff61e739 0xffffffffff1fffff 0xffffffffffe3ffff

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0xb000060000001c06 0x360000c000000380

def z588 : W := mkw 0x004440000040c000 0x0008880000081800 0xf8ec460380e3fce7 0xbf1d88c0701c7f9c

def z589 : W := mkw 0x0000180c200c210a 0x2000030184018421 0x0010381c001c0000 0x0002070380038000

def z590 : W := mkw 0x0db087741fb71fc7 0x81b610ee83f6e3f8 0xfff007fc1fff9fe6 0xfffe00ff83fff3fc

def z591 : W := mkw 0x36dff88bf6dbe000 0x06dbff117edb7c00 0xdffff803ffffe005 0xfbffff007ffffc00

def z592 : W := mkw 0x00200220c0000000 0x0004004418000000 0x20000623e0000002 0x040000c47c000000

def z593 : W := mkw 0x0fba87741fb71f07 0x01f750ee83f6e3e0 0xffff87fc1fff9f07 0xfffff0ff83fff3e0

def z594 : W := mkw 0x06dff8ce380e318a 0xa0dbff19c701c631 0xcffff9fe781e739f 0xf9ffff3fcf03ce73

def z595 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x68f007fc00fc1f02 0x8d1e00ff801f83e0

def z596 : W := mkw 0x0800004409241f07 0x01000008812483e0 0x0000000000001f00 0x00000000000003e0

def z597 : W := mkw 0x049198ce3c9e318a 0xa0923319c793c631 0xdff3f9fe7ffe739f 0xfbfe7f3fcfffce73

def z598 : W := mkw 0x000110ce2804118a 0xa0002219c5008231 0x8013f9fe6000139b 0xd0027f3fcc000273

def z599 : W := mkw 0x1000880016dbe000 0x0200110002db7c00 0x9813f8001fffe005 0xd3027f0003fffc00

def z600 : W := mkw 0x1ffeef74dfffff37 0x43ffddee9bffffe6 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x0db0077409241f07 0x01b600ee812483e0 0xe7f007fc00001f02 0xfcfe00ff800003e0

def z602 : W := mkw 0x026fc2a3d263c6f4 0xc04df8547a4c78de 0xf8efc623e0e3ffff 0xbf1df8c47c1c7fff

def z603 : W := mkw 0x0df44730c5f0ce35 0x41be88e618be19c6 0x77ec060187e18c60 0x2efd80c030fc318c

def z604 : W := mkw 0x00644220c0000000 0x000c884418000000 0xf0ec4623e0039ce7 0xbe1d88c47c00739c

def z605 : W := mkw 0x036e4721c361ce74 0x406dc8e4386c39ce 0x77ec060187e18c60 0x2efd80c030fc318c

def z606 : W := mkw 0x080080441fb71fc7 0x8100100883f6e3f8 0x180000001fff9fe4 0x0300000003fff3fc

def z607 : W := mkw 0x00444000c040c030 0x4008880018081806 0xb00c4603e003fcff 0x360188c07c007f9f

def z608 : W := mkw 0x004440000040c000 0x0008880000081800 0x000c40000003e001 0x0001880000007c00

def z609 : W := mkw 0x234f758be0000000 0x0469eeb17c000000 0xa70fffc3e0000003 0x74e1fff87c000000

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400260026099 0x000008004c004c13

def z611 : W := mkw 0x00644220c0200604 0x000c8844180400c0 0xf8ec4623e0e01f07 0xbf1d88c47c1c03e0

def z612 : W := mkw 0x020b80c21a031080 0x8041701843406210 0x970f81c21f039087 0x72e1f03843e07210

def z613 : W := mkw 0x00219aeef82e37be 0xe004335ddf05c6f7 0xa813fffff81e7fff 0xd5027fffff03cfff

def z614 : W := mkw 0x0cb19afe3cbe378f 0xa196335fc797c6f1 0xc8f3f9fe78fe739f 0xd91e7f3fcf1fce73

def z615 : W := mkw 0x00200220c0200634 0x40040044180400c6 0xf8e00623e0e01ffe 0xbf1c00c47c1c03ff

def z616 : W := mkw 0x0020022000200604 0x00040044000400c0 0x48e0002000e00300 0x891c0004001c0060

def z617 : W := mkw 0x0800000404b40707 0x01000000809680e0 0x0800000000fc0300 0x01000000001f8060

def z618 : W := mkw 0x27fff7fbfb63def4 0xc4fffeff7f6c7bde 0xffffffffffe3ffff 0xfffffffffffc7fff

def z619 : W := mkw 0x0900055409041903 0x012000aa81208320 0x000001dc00000000 0x0000003b80000000

def z620 : W := mkw 0x05f44730c060c634 0x40be88e6180c18c6 0xfffc47ffe0e3ffff 0xffff88fffc1c7fff

def z621 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x70ec0623e0e19ffa 0x2e1d80c47c1c33ff

def z622 : W := mkw 0x07df658300000000 0x00fbecb060000000 0xe7ffffc380000003 0xfcfffff870000000

def z623 : W := mkw 0x25f577bbe0000000 0x04beaef77c000000 0x60f07fffe0000002 0x8c1e0ffffc000000

def z624 : W := mkw 0x36fefa38f6dbe000 0x06dfdf471edb7c00 0xdffff83c7fffe005 0xfbffff078ffffc00

def z625 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0x8f13f9fe7f1e739f 0xd1e27f3fcfe3ce73

def z626 : W := mkw 0x124ee800124be000 0x0249dd0002497c00 0x881ff800181fe005 0xd103ff000303fc00

def z627 : W := mkw 0x0001188e200c210a 0x20002311c4018421 0x8813f9fe601c631b 0xd1027f3fcc038c63

def z628 : W := mkw 0x002112eee82417be 0xe004225ddd0482f7 0x200007ffe0001ffa 0x040000fffc0003ff

def z629 : W := mkw 0x0db0073404b40707 0x01b600e6809680e0 0xeff007fc00fc0302 0xfdfe00ff801f8060

def z630 : W := mkw 0x00644220c0000000 0x000c884418000000 0x60ec060180000000 0x2c1d80c030000000

def z631 : W := mkw 0x1000080004d8e000 0x02000100009b1c00 0x0800000000fc6000 0x01000000001f8c00

def z632 : W := mkw 0x020b8083120300c0 0x8041701062406018 0x970f80039f0380e5 0x72e1f00073e0701c

def z633 : W := mkw 0x000000000060c634 0x40000000000c18c6 0x1000000000e18c60 0x02000000001c318c

def z634 : W := mkw 0x120aa800120b2000 0x0241550002416400 0x0003b80000000000 0x0000770000000000

def z635 : W := mkw 0x37ffffbbf24be000 0x06fffff77e497c00 0xe7ffffffe003e003 0xfcfffffffc007c00

def z636 : W := mkw 0x0fffc7f7dff7dff7 0xc1fff8fefbfefbfe 0xffffc7ffffffffff 0xfffff8ffffffffff

def z637 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0x8f1001fc1f1c1306 0xd1e2003f83e38260

def z638 : W := mkw 0x000198ca380a3088 0xa000331947014611 0x8003f9c27802709f 0x50007f384f004e13

def z639 : W := mkw 0x010185c3190218c0 0x802030b863204318 0xa00387c398021ce7 0x540070f87300439c

def z640 : W := mkw 0x0fbb87f71fb71fc7 0x81f770fee3f6e3f8 0xfff387fc1ffc1f06 0xfffe70ff83ff83e0

def z641 : W := mkw 0x000110ce2804118a 0xa0002219c5008231 0x000001dc00000000 0x0000003b80000000

def z642 : W := mkw 0x04b0022004b00604 0x00960044009600c0 0xfff006201ffc1f06 0xfffe00c403ff83e0

def z643 : W := mkw 0x004440000060c634 0x40088800000c18c6 0xd8ec400000e3fffd 0xbb1d8800001c7fff

def z644 : W := mkw 0x16dff88a36dbe088 0xa2dbff1146db7c11 0xdffff8027fffe09d 0xfbffff004ffffc13

def z645 : W := mkw 0x00444000c040c030 0x4008880018081806 0x880c4023e003f3ff 0x910188047c007e7f

def z646 : W := mkw 0x00200220c0200634 0x40040044180400c6 0x0000002060000318 0x000000040c000063

def z647 : W := mkw 0x00645a2ce06ce73e 0x600c8b459c0d9ce7 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z648 : W := mkw 0x0001988a300a2088 0xa000331146014411 0x0003b80000000000 0x0000770000000000

def z649 : W := mkw 0x04b0023000000000 0x0096004600000000 0x40f0003c00000000 0x881e000780000000

def z650 : W := mkw 0x0db0073005b00e05 0x01b600e600b601c0 0xffe0062007e01f06 0xbffc00c400fc03e0

def z651 : W := mkw 0x020a000000000000 0x0041400000000000 0x870f800000000001 0x70e1f00000000000

def z652 : W := mkw 0x232b17bbe0000000 0x046562f77c000000 0xa70f87ffe0000003 0x74e1f0fffc000000

def z653 : W := mkw 0x226f72abe060c634 0x444dee557c0c18c6 0xf8effe23e0e3ffff 0xbf1dffc47c1c7fff

def z654 : W := mkw 0x16fffaeefefff7be 0xe2dfff5ddfdffef7 0xffffffffffffffff 0xffffffffffffffff

def z655 : W := mkw 0x0045d88af04ae0b8 0xe008bb115e095c17 0x000ff803e003e0f9 0x0001ff007c007c1f

def z656 : W := mkw 0x0920073001200e05 0x012400e6002401c0 0x2000060000000c00 0x040000c000000180

def z657 : W := mkw 0x059005400d901800 0x00b200a801b20300 0xfff007c01ffc1c06 0xfffe00f803ff8380

def z658 : W := mkw 0x24f47238e0000000 0x049e8e471c000000 0xe0fc7e3fe0000003 0xbc1f8fc7fc000000

def z659 : W := mkw 0x2ffff7ffffb71fc7 0x85fffefffff6e3f8 0xffffffffffff9fe7 0xfffffffffffff3fc

def z660 : W := mkw 0x010105c3090018c0 0x802020b861200318 0x000001c000000000 0x0000003800000000

def z661 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x271007fc1f1c1f02 0x44e200ff83e383e0

def z662 : W := mkw 0x0000184c280c310a 0x2000030985018621 0x881079fc781c731e 0xd1020f3f8f038e63

def z663 : W := mkw 0x0064ca20d06ae634 0x400c99441a0d5cc6 0xf8fffe23f8ffffff 0xff1fffc47f1fffff

def z664 : W := mkw 0x080000440db41f07 0x0100000881b683e0 0x981001fc1ffc1f06 0xd302003f83ff83e0

def z665 : W := mkw 0x16feea2016fbe604 0x02dfdd4402df7cc0 0xfffffe201fffff07 0xffffffc403ffffe0

def z666 : W := mkw 0x00444000c040c030 0x4008880018081806 0x000c000180018060 0x000180003000300c

def z667 : W := mkw 0x26ff72bbe0000000 0x04dfee577c000000 0x40fff83fe0000001 0x881fff07fc000000

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0003800380e1 0x000180007000701c

def z669 : W := mkw 0x000190ce3806118a 0xa0003219c700c231 0x800381fe7802139f 0x5000703fcf004273

def z670 : W := mkw 0x1ffe673007f1ce05 0x03ffcce600fe39c0 0x77ec060007e18c00 0x2efd80c000fc3180

def z671 : W := mkw 0x030a85401b031800 0x006150a803606300 0xb70f87c01f039c07 0x76e1f0f803e07380

def z672 : W := mkw 0x1ffe67740ff5df07 0x03ffccee81febbe0 0xfffc07fc1ffd9f06 0xffff80ff83ffb3e0

def z673 : W := mkw 0x0020022000200604 0x00040044000400c0 0x2000062000001f02 0x040000c4000003e0

def z674 : W := mkw 0x020b008300000000 0x0041601060000000 0x000f800380000001 0x0001f00070000000

def z675 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8ec460180e3ec65 0xbf1d88c0301c7d8c

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800400000026005 0x9100080000004c00

def z677 : W := mkw 0x16fe6220c6f1c634 0x42dfcc4418de38c6 0xffec4623e7e3ffff 0xbffd88c47cfc7fff

def z678 : W := mkw 0x0df447740df4df07 0x01be88ee81be9be0 0xfffc47fc1fffff07 0xffff88ff83ffffe0

def z679 : W := mkw 0x0db107f70db41fc7 0x81b620fee1b683f8 0xfff007ff9ffc1fe6 0xfffe00fff3ff83fc

def z680 : W := mkw 0x04d4400004d0c000 0x009a8800009a1800 0xdffc40001fffe005 0xfbff880003fffc00

def z681 : W := mkw 0x27ffe7f3db0318c0 0x84fffcfe7b606318 0xf7ef87c39f039ce7 0x7efdf0f873e0739c

def z682 : W := mkw 0x0df44774cdf4df37 0x41be88ee99be9be6 0xfff047fc7ffc7f1e 0xfffe08ff8fff8fe3

def z683 : W := mkw 0x16dfe8c21edbf080 0x82dbfd1843db7e10 0xdffff9c21ffff087 0xfbffff3843fffe10

def z684 : W := mkw 0x000000000040c000 0x0000000000081800 0x1800000000e3e004 0x03000000001c7c00

def z685 : W := mkw 0x0db007740df4df37 0x41b600ee81be9be6 0xfff007fc1ffffffe 0xfffe00ff83ffffff

def z686 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x200f87c380039ce3 0x0401f0f87000739c

def z687 : W := mkw 0x27fe6731c0000000 0x04ffcce638000000 0xe7fc07fd80000002 0xfcff80ffb0000000

def z688 : W := mkw 0x14d4680004d8e000 0x029a8d00009b1c00 0xdff078001ffc6004 0xfbfe0f0003ff8c00

def z689 : W := mkw 0x0fbb07f70db41f07 0x01f760fee1b683e0 0xffff87ff9ffc1f07 0xfffff0fff3ff83e0

def z690 : W := mkw 0x25b117bbe0000000 0x04b622f77c000000 0xe7f007ffe0000002 0xfcfe00fffc000000

def z691 : W := mkw 0x25f47738e0000000 0x04be8ee71c000000 0xe7f07ffc60000002 0xfcfe0fff8c000000

def z692 : W := mkw 0x000000000060c634 0x40000000000c18c6 0xb80c060380e3ffff 0x370180c0701c7fff

def z693 : W := mkw 0x0000004008001000 0x0000000801000200 0x800001c018001006 0x5000003803000200

def z694 : W := mkw 0x00644220c0000000 0x000c884418000000 0xe8ec4623e002739f 0xbd1d88c47c004e73

def z695 : W := mkw 0x000000000040c030 0x4000000000081806 0x000000000003e0f8 0x0000000000007c1f

def z696 : W := mkw 0x0fba073107b10e45 0x01f740e620f621c8 0x77ec060187e18c60 0x2efd80c030fc318c

def z697 : W := mkw 0x0df44774cdf4df37 0x41be88ee99be9be6 0xfffc07fd9ffd9f66 0xffff80ffb3ffb3ec

def z698 : W := mkw 0x16def80c36dfe10a 0x22dbdf0186dbfc21 0xdffff83c7fffe31d 0xfbffff078ffffc63

def z699 : W := mkw 0x26df708be0000000 0x04dbee117c000000 0xc7fff803e0000001 0xf8ffff007c000000

def z700 : W := mkw 0x034fc5c31b43d8c0 0x8069f8b863687b18 0xffefc7c39fe3fce7 0xfffdf8f873fc7f9c

def z701 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x070f81c39f0380e1 0x40e1f03873e0701c

def z702 : W := mkw 0x020b8083120300c0 0x8041701062406018 0xb00f860380039ce7 0x3601f0c07000739c

def z703 : W := mkw 0x0065daeef80e318a 0xa00cbb5ddf01c631 0xe8fffffff81e739f 0xfd1fffffff03ce73

def z704 : W := mkw 0x224ff88bf00a2088 0xa449ff117e014411 0x000ff803e0026099 0x0001ff007c004c13

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800402060006318 0x810008040c000c63

def z706 : W := mkw 0x0d919dde3d9e398b 0xa1b233bbc7b3c731 0x8f13f9fe7f1e739f 0xd1e27f3fcfe3ce73

def z707 : W := mkw 0x030b158b20000000 0x006162b164000000 0xbf1fffffe003ffff 0xf7e3fffffc007fff

def z708 : W := mkw 0x030b95cb3b0318c8 0xa06172b967606319 0xb70f87c3ff039cff 0x76e1f0f87fe0739f

def z709 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffffe00380e3 0xfcfffffffc00701c

def z710 : W := mkw 0x00008844190e39ca 0xa00011088321c739 0x08000000181e7ffc 0x010000000303cfff

def z711 : W := mkw 0x27ff77bbe040c030 0x44ffeef77c081806 0xffffffffe0e3e0ff 0xfffffffffc1c7c1f

def z712 : W := mkw 0x000088441b0f39ca 0xa00011088361e739 0xb80c4623ff1fffff 0xb70188c47fe3ffff

def z713 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xc7fff9fc60000001 0xf8ffff3f8c000000

def z714 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x88100000181e739c 0xd10200000303ce73

def z715 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xf7ffffffe0001c07 0xfefffffffc000380

def z716 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8813f9fe781c631b 0xd1027f3fcf038c63

def z717 : W := mkw 0x15b08f3016dbe000 0x02b611e602db7c00 0xfff007fc1fffe006 0xfffe00ff83fffc00

def z718 : W := mkw 0x100088441fdff9ca 0xa200110883fbff39 0x180000001ffffffc 0x0300000003ffffff

def z719 : W := mkw 0x0db19fba35ba2e8d 0xa1b633f746b745d1 0x77e3fe0267e26c99 0x2efc7fc04cfc4d93

def z720 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x4ffff8001fffe001 0xc9ffff0003fffc00

def z721 : W := mkw 0x0db00774cdb41f07 0x01b600ee99b683e0 0xfff007fffffc1f06 0xfffe00ffffff83e0

def z722 : W := mkw 0x25f577bbe0000000 0x04beaef77c000000 0xe0f3ffffe0000003 0xdc1e7ffffc000000

def z723 : W := mkw 0x00008844184ef18a 0xa00011088309de31 0x1800000018fff39c 0x03000000031ffe73

def z724 : W := mkw 0x036f57abe0000000 0x006deaf57c000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z725 : W := mkw 0x232b17bbe0000000 0x046562f77c000000 0xa71fffffe0000003 0xf4e3fffffc000000

def z726 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8fc4623f8ffffff 0xff1f88c47f1fffff

def z727 : W := mkw 0x226f72abe060c634 0x444dee557c0c18c6 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z728 : W := mkw 0x00008844180e3102 0x000011088301c620 0x08000000181e7304 0x010000000303ce60

def z729 : W := mkw 0x2ffe6731c5f0ce35 0x45ffcce638be19c6 0x77ec060187e18c60 0x2efd80c030fc318c

def z730 : W := mkw 0x16dee8441edff18a 0xa2dbdd0883dbfe31 0x5fec00001ffff39c 0x2bfd800003fffe73

def z731 : W := mkw 0x0001108a2060c634 0x40002211440c18c6 0x9813f9fe60e3ffff 0xd3027f3fcc1c7fff

def z732 : W := mkw 0x012117efe9241ffe 0xe02422fdfd2483ff 0x200007ffe0001ffa 0x040000fffc0003ff

def z733 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x7fe007fc1ffc1f06 0x2ffc00ff83ff83e0

def z734 : W := mkw 0x030b85c71b0719ca 0xa06170b8e360e339 0xb70f87c39f039fff 0x76e1f0f873e073ff

def z735 : W := mkw 0x0db007740db41fc7 0x81b600ee81b683f8 0xfff007fc1ffc1fe6 0xfffe00ff83ff83fc

def z736 : W := mkw 0x04908800149a2000 0x0092110002934400 0xdff3b8001ffc0004 0xfbfe770003ff8000

def z737 : W := mkw 0x030a8d451b0f39ca 0xa06151a8a361e739 0x3f0c06019f1ffffc 0x27e180c033e3ffff

def z738 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x5fffb8001fffe004 0x6bfff70003fffc00

def z739 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013b9fc00000002 0xd002773f80000000

def z740 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08000000181c6318 0x0100000003038c63

def z741 : W := mkw 0x092117ff29241fcf 0xa12422ffe52483f9 0x200007ffe0001ffa 0x040000fffc0003ff

def z742 : W := mkw 0x16baaa20d6bb2634 0x42d755441ad764c6 0x2713be23ff1c1ffa 0x44e277c47fe383ff

def z743 : W := mkw 0x036fc7e3db63def4 0xc06df8fc7b6c7bde 0x4fe3c1e07fe06318 0xc9fc783c0ffc0c63

def z744 : W := mkw 0x27ff77bbe0200604 0x04ffeef77c0400c0 0xffffffffe0e27f9f 0xfffffffffc1c4ff3

def z745 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfffc07ff9ffc1f07 0xffff80fff3ff83e0

def z746 : W := mkw 0x006552aae060c634 0x400caa555c0c18c6 0xf0ffffffe0e18c63 0xfe1ffffffc1c318c

def z747 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xbf1fbfdf9f1fffff 0x77e3f7fbf3e3ffff

def z748 : W := mkw 0x27df759be0000000 0x04fbeeb37c000000 0x071fb9dd80000000 0x40e3f73bb0000000

def z749 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x981ff9fe781ff39f 0xf303ff3fcf03fe73

def z750 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370f87c19f039ce4 0x66e1f0f833e0739c

def z751 : W := mkw 0x030b158b20000000 0x006162b164000000 0x0713b9dc00000000 0x40e2773b80000000

def z752 : W := mkw 0x0db00774cdb41f37 0x41b600ee99b683e6 0xfff007fc7ffc1f1e 0xfffe00ff8fff83e3

def z753 : W := mkw 0x030b95cb3b0318c0 0x806172b967606318 0xb71fbfdf9f039ce7 0x76e3f7fbf3e0739c

def z754 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370c07c39f039ce6 0x26e180f873e0739c

def z755 : W := mkw 0x07df758b20000000 0x00fbeeb164000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z756 : W := mkw 0x180088441f9f3903 0x0300110883f3e720 0x000000001f1c0000 0x0000000003e38000

def z757 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xf7ffffffe0e3ecfb 0xfefffffffc1c7d9f

def z758 : W := mkw 0x030b05c30b0118c0 0x806160b861602318 0xb70f87c387019ce3 0x76e1f0f870e0339c

def z759 : W := mkw 0x002112aa20000000 0x0004225544000000 0xe0f3fffe60000003 0xfc1e7fffcc000000

def z760 : W := mkw 0x030b058303010840 0x006160b060602108 0x370f87c187018c60 0x66e1f0f830e0318c

def z761 : W := mkw 0x0db0073005b00e05 0x01b600e600b601c0 0xfff007fc1ffc0c06 0xfffe00ff83ff8180

def z762 : W := mkw 0x030a1d0d230d294a 0x206143a1a461a529 0x3f1c7e3de71def78 0xa7e38fc7bce3bdef

def z763 : W := mkw 0x030b058303010840 0x006160b060602108 0x370c07c387018c62 0x26e180f870e0318c

def z764 : W := mkw 0x010185c219021880 0x802030b843204310 0xb70f87c39f039ce7 0x76e1f0f873e0739c

def z765 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffbfdf80000003 0x7cfff7fbf0000000

def z766 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfffc07fd9ffd9f66 0xffff80ffb3ffb3ec

def z767 : W := mkw 0x06de600004d0c000 0x00dbcc00009a1800 0xdffff8001fffe005 0xfbffff0003fffc00

def z768 : W := mkw 0x0db00774cdb41f37 0x41b600ee99b683e6 0xfffc07ffffff9fff 0xffff80fffffff3ff

def z769 : W := mkw 0x0064ca64d80e318a 0xa00c994c9b01c631 0xe8ec4623f81e739f 0xbd1d88c47f03ce73

def z770 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff047fe7ffc1f07 0xfffe08ffcfff83e0

def z771 : W := mkw 0x234f758be0000000 0x0469eeb17c000000 0xa71fffffe0000003 0xf4e3fffffc000000

def z772 : W := mkw 0x0001108a20000000 0x0000221144000000 0xb01fffffe0039ce7 0xf603fffffc00739c

def z773 : W := mkw 0x27ff77bbe0200634 0x44ffeef77c0400c6 0xffffffffe0e01fff 0xfffffffffc1c03ff

def z774 : W := mkw 0x27ff77bbe0200634 0x44ffeef77c0400c6 0xe7ffffffe0000c63 0xfcfffffffc00018c

def z775 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8fffe23e0e3ffff 0xff1fffc47c1c7fff

def z776 : W := mkw 0x27ff77bbe2010040 0x04ffeef77c402008 0xe7ffffffe0018063 0xfcfffffffc00300c

def z777 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70f87c39f018c63 0x76e1f0f873e0318c

def z778 : W := mkw 0x0045508ae0000000 0x0008aa115c000000 0x801ff9ffe0000003 0xd003ff3ffc000000

def z779 : W := mkw 0x000088441b6ffffe 0xe0001108836dffff 0x180000001ffffffc 0x0300000003ffffff

def z780 : W := mkw 0x15d56dc30dd8f8c0 0x82baadb861bb1f18 0x68f07fc380fc7ce2 0x8d1e0ff8701f8f9c

def z781 : W := mkw 0x1b6eef741b6fff07 0x036dddee836dffe0 0x200ffffc0003ff03 0x0401ffff80007fe0

def z782 : W := mkw 0x0065daeef86ef7be 0xe00cbb5ddf0ddef7 0x70ffbfdd98fd8c60 0x6e1ff7fbb31fb18c

def z783 : W := mkw 0x27ff77bbe2010000 0x04ffeef77c402000 0xf7ffffffe7018003 0xfefffffffce03000

def z784 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xf7ffffffe0e39ce7 0xfefffffffc1c739c

def z785 : W := mkw 0x030a050103010840 0x006140a020602108 0x370c060387019ce2 0x26e180c070e0339c

def z786 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x5ffff8001ffde000 0xebffff0003ffbc00

def z787 : W := mkw 0x030a85411b0318c0 0x806150a823606318 0x370c06019f018c60 0x26e180c033e0318c

def z788 : W := mkw 0x292117ffe9241fc7 0x852422fffd2483f8 0x200007ffe0001fe2 0x040000fffc0003fc

def z789 : W := mkw 0x279b359b23010840 0x04f366b364602108 0x0713b9dc07000000 0x40e2773b80e00000

def z790 : W := mkw 0x030b95cb3b0318c0 0x806172b967606318 0xb70fffc3ff039ce7 0x76e1fff87fe0739c

def z791 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffffe0001ce3 0xfcfffffffc00039c

def z792 : W := mkw 0x31219fbbf6dbe000 0x062433f77edb7c00 0x380007ffffffe006 0x070000fffffffc00

def z793 : W := mkw 0x030a8d01130b2840 0x006151a022616508 0xbf1ffe019f1fec65 0xf7e3ffc033e3fd8c

def z794 : W := mkw 0x030b8583130308c0 0x806170b062606118 0x370f860187018c60 0x26e1f0c030e0318c

def z795 : W := mkw 0x26ff72bae0000000 0x04dfee575c000000 0xc7fff9fe60000003 0xf8ffff3fcc000000

def z796 : W := mkw 0x030b95cf3b0719ca 0xa06172b9e760e339 0xbf0fc7ffff03ffff 0xf7e1f8ffffe07fff

def z797 : W := mkw 0x000118ce280c318a 0xa0002319c5018631 0x8813f9fe601c739b 0xd1027f3fcc038e73

def z798 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8027fffe09d 0xfbffff004ffffc13

def z799 : W := mkw 0x100088441a4ff18a 0xa20011088349fe31 0x08000000181ff39c 0x010000000303fe73

def z800 : W := mkw 0x030b858312030000 0x006170b062406000 0xb70f87c39f039ce7 0x76e1f0f873e0739c

def z801 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffdd80000001 0xfcfffffbb0000000

def z802 : W := mkw 0x092117fe29241f07 0x012422ffc52483e0 0x200007fe60001f02 0x040000ffcc0003e0

def z803 : W := mkw 0x030b8dc31b0b38c0 0x806171b863616718 0xb71fbfc39f1f9ce7 0x76e3f7f873e3f39c

def z804 : W := mkw 0x279b359b2060c634 0x44f366b3640c18c6 0x1f13b9dc00e3fffc 0x43e2773b801c7fff

def z805 : W := mkw 0x27ff77bb20000000 0x04ffeef764000000 0xe7fffffc00000003 0xfcffffff80000000

def z806 : W := mkw 0x24f572bae0000000 0x049eae575c000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z807 : W := mkw 0x030b0583030108c0 0x806160b060602118 0x370c060387018ce0 0x26e180c070e0319c

def z808 : W := mkw 0x0020022000200604 0x00040044000400c0 0xf8ec4623e0e3ffff 0xbf1d88c47c1c7fff

def z809 : W := mkw 0x0101158a20000000 0x002022b144000000 0xa713fffe60000003 0xf4e27fffcc000000

def z810 : W := mkw 0x030b158b23010840 0x006162b164602108 0xb71fffffe7018c63 0xf6e3fffffce0318c

def z811 : W := mkw 0x27df759b20000000 0x04fbeeb364000000 0x47f3f9dc00000000 0xc8fe7f3b80000000

def z812 : W := mkw 0x279b359b20000000 0x04f366b364000000 0xa71fffffe0000003 0xf4e3fffffc000000

def z813 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x78ec0623e0e3fffe 0x2f1d80c47c1c7fff

def z814 : W := mkw 0x16dee80016dbe088 0xa2dbdd0002db7c11 0xdffff8001fffe09d 0xfbffff0003fffc13

def z815 : W := mkw 0x04d4c80014dae000 0x009a9900029b5c00 0xdffff8001fffe005 0xfbffff0003fffc00

def z816 : W := mkw 0x0cf44234c4f4c737 0x419e8846989e98e6 0x48f0003c00fc0300 0x891e0007801f8060

def z817 : W := mkw 0x25f577bae0000000 0x04beaef75c000000 0xe7f3fffe60000003 0xfcfe7fffcc000000

def z818 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0xfff007dc1ffc1c06 0xfffe00fb83ff8380

def z819 : W := mkw 0x0045508a2040c000 0x0008aa1144081800 0xd8fff9fe60e3e007 0xfb1fff3fcc1c7c00

def z820 : W := mkw 0x07ba273000000000 0x00f744e600000000 0xe7f3bffc00000002 0xfcfe77ff80000000

def z821 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007fe7ffc1f9e 0xfffe00ffcfff83f3

def z822 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xfffffe039fffe007 0xffffffc073fffc00

def z823 : W := mkw 0x212117bbe0200634 0x442422f77c0400c6 0xa813ffffe0027fff 0xd5027ffffc004fff

def z824 : W := mkw 0x05b0073004b00604 0x00b600e6009600c0 0xfff007fc1ffc1f06 0xfffe00ff83ff83e0

def z825 : W := mkw 0x24f4f278fb0318c0 0x849e9e4f1f606318 0x50f0783c7f039ce4 0x8a1e0f078fe0739c

def z826 : W := mkw 0x030a850113030840 0x006150a022606108 0x370f86019f018c60 0x66e1f0c033e0318c

def z827 : W := mkw 0x1490880016dbe000 0x0292110002db7c00 0xdff3f8001fffe005 0xfbfe7f0003fffc00

def z828 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xe7ffffffe003fffb 0xfcfffffffc007fff

def z829 : W := mkw 0x000198ce3a0f318a 0xa0003319c741e631 0x9813f9fe7f1ff39f 0xd3027f3fcfe3fe73

def z830 : W := mkw 0x16dee800d6dbe030 0x42dbdd001adb7c06 0xdffff8019fffe065 0xfbffff0033fffc0c

def z831 : W := mkw 0x27ff77bbe1000800 0x04ffeef77c200100 0xf7ffffffe7000c03 0xfefffffffce00180

def z832 : W := mkw 0x0db007740db41f8f 0xa1b600ee81b683f1 0xfff007fc1ffc1f9e 0xfffe00ff83ff83f3

def z833 : W := mkw 0x00008844182e378e 0xa00011088305c6f1 0x1800000018fe7f9c 0x03000000031fcff3

def z834 : W := mkw 0x07fe6730c0000000 0x00ffcce618000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z835 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff9fc1fffe007 0xfbffff3f83fffc00

def z836 : W := mkw 0x1064ca64defff7be 0xe20c994c9bdffef7 0xf8ec4623ffffffff 0xbf1d88c47fffffff

def z837 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xffffffffe0e00007 0xfffffffffc1c0000

def z838 : W := mkw 0x292117ff29241f07 0x052422ffe52483e0 0x200007fc00001f02 0x040000ff800003e0

def z839 : W := mkw 0x030a85411b0318c0 0x806150a823606318 0xb70c06039f039ce7 0x36e180c073e0739c

def z840 : W := mkw 0x0ebb82b716b707c7 0x81d77056e2d6e0f8 0x48ff803f80ff83e1 0x891ff007f01ff07c

def z841 : W := mkw 0x27feef75d80e318a 0xa4ffddeebb01c631 0x6fec0601981e739c 0x2dfd80c03303ce73

def z842 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z843 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70fc7e3ff039ce7 0xf6e1f8fc7fe0739c

def z844 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfffc07fc1fff9f07 0xffff80ff83fff3e0

def z845 : W := mkw 0x292117ffe9241f37 0x452422fffd2483e6 0x200007ffe0001ffa 0x040000fffc0003ff

def z846 : W := mkw 0x224f708be040c030 0x4449ee117c081806 0x881ff9ffe003f3ff 0xd103ff3ffc007e7f

def z847 : W := mkw 0x236f77bbe0000000 0x046deef77c000000 0xa01fffffe0000003 0xd403fffffc000000

def z848 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffbffd80000002 0xfcfff7ffb0000000

def z849 : W := mkw 0x07bb17bb20000000 0x00f762f764000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z850 : W := mkw 0x2fff77bbe5900801 0x05ffeef77cb20100 0xe7ffffffe7000003 0xfcfffffffce00000

def z851 : W := mkw 0x030a05450b051942 0x006140a8a160a328 0xbf1c07fd9f1d9f66 0xf7e380ffb3e3b3ec

def z852 : W := mkw 0x030a85401b031800 0x006150a803606300 0xb70f87c39f039ce7 0x76e1f0f873e0739c

def z853 : W := mkw 0x2cf4723ce4f4c737 0x459e8e479c9e98e6 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z854 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67ffffdfe0000001 0x6cfffffbfc000000

def z855 : W := mkw 0x124ff88a324be088 0xa249ff1146497c11 0x000ff8000003e001 0x0001ff0000007c00

def z856 : W := mkw 0x030b8583130308c0 0x806170b062606118 0xb70f87c387038ce3 0x76e1f0f870e0719c

def z857 : W := mkw 0x2fff77bbe4b00605 0x05ffeef77c9600c0 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z858 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xbf0f87c39f03ffff 0x77e1f0f873e07fff

def z859 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xfffffe001ffffc07 0xffffffc003ffff80

def z860 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0813f9fe601e739b 0x81027f3fcc03ce73

def z861 : W := mkw 0x100088441e9f318a 0xa200110883d3e631 0x080000001f1e739c 0x0100000003e3ce73

def z862 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x08000002781e739c 0x010000004f03ce73

def z863 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67efffffe0000003 0x2cfdfffffc000000

def z864 : W := mkw 0x059005440d941902 0x00b200a881b28320 0xfff007fc1ffc1f06 0xfffe00ff83ff83e0

def z865 : W := mkw 0x0591159a20000000 0x00b222b344000000 0x0713b9dc00000000 0x40e2773b80000000

def z866 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70c060187019c66 0x36e180c030e0338c

def z867 : W := mkw 0x0120076409241f06 0x002400ec812483e0 0xfff007fc1ffc1f06 0xfffe00ff83ff83e0

def z868 : W := mkw 0x16de600006d1c000 0x02dbcc0000da3800 0xdffff8001ffd8005 0xfbffff0003ffb000

def z869 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8813f9fe60001307 0xd1027f3fcc000260

def z870 : W := mkw 0x00008844184ef1ba 0xe00011088309de37 0x08000000181ff3fc 0x010000000303fe7f

def z871 : W := mkw 0x124ff88af24be0b8 0xe249ff115e497c17 0x000ff803e003e0f9 0x0001ff007c007c1f

def z872 : W := mkw 0x049088441c9e318a 0xa09211088393c631 0xdff000001ffe739c 0xfbfe000003ffce73

def z873 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xffef87c39fe39ce7 0xfffdf0f873fc739c

def z874 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xbf0f87ffff1fffff 0x77e1f0ffffe3ffff

def z875 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013b9de00000003 0x5002773bc0000000

def z876 : W := mkw 0x1ffeef741fffff07 0x03ffddee83ffffe0 0x7fec06001fffff04 0x2ffd80c003ffffe0

def z877 : W := mkw 0x030b8dc71b0f39c2 0x806171b8e361e738 0xbf1fffff9f1fffe7 0xf7e3fffff3e3fffc

def z878 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xbf0fffc3ff1fffff 0x77e1fff87fe3ffff

def z879 : W := mkw 0x0001108a20000000 0x0000221144000000 0xa01fffffe0000003 0xf403fffffc000000

def z880 : W := mkw 0x27ff77bbe0200604 0x04ffeef77c0400c0 0xf7ffffffe0e00c03 0xfefffffffc1c0180

def z881 : W := mkw 0x124ff88b324be0c8 0xa249ff1166497c19 0x000ff803e003e0f9 0x0001ff007c007c1f

def z882 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x8713b9de00000003 0x50e2773bc0000000

def z883 : W := mkw 0x2045708ae0000000 0x0408ae115c000000 0x8013f9fe60000003 0xd0027f3fcc000000

def z884 : W := mkw 0x16df70ce2ed5d18a 0xa2dbee19c5daba31 0x57ec01fe67e1939a 0x2afd803fccfc3273

def z885 : W := mkw 0x27ff77bbe040c030 0x44ffeef77c081806 0xefffffffe003f3ff 0xfdfffffffc007e7f

def z886 : W := mkw 0x236f77bbe060c634 0x446deef77c0c18c6 0xf8efffffe0e3ffff 0xbf1dfffffc1c7fff

def z887 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xefffffffe000631b 0xfdfffffffc000c63

def z888 : W := mkw 0x030b95cf3b0719c2 0x806172b9e760e338 0xbf1fffffff1f9fe7 0xf7e3ffffffe3f3fc

def z889 : W := mkw 0x27df759be0000000 0x04fbeeb37c000000 0xa71fffdfe0000003 0x74e3fffbfc000000

def z890 : W := mkw 0x000110ce28041102 0x00002219c5008220 0x8813f9fe781e739f 0xd1027f3fcf03ce73

def z891 : W := mkw 0x0064ca64db6ffffe 0xe00c994c9b6dffff 0xf8ec4623ffffffff 0xbf1d88c47fffffff

def z892 : W := mkw 0x069b308a20000000 0x00d3661144000000 0x0713b9dc00000000 0x40e2773b80000000

def z893 : W := mkw 0x05b117ba20000000 0x00b622f744000000 0xe7f3bffc00000002 0xfcfe77ff80000000

def z894 : W := mkw 0x002112aa20200604 0x00042255440400c0 0xf8f3fffe60e01f07 0xff1e7fffcc1c03e0

def z895 : W := mkw 0x220b308b20000000 0x0441661164000000 0x0013b9dc00000000 0x4002773b80000000

def z896 : W := mkw 0x27ff77bbe040c000 0x04ffeef77c081800 0xffffffffe0e3f39f 0xfffffffffc1c7e73

def z897 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007fc1ffe7f9e 0xfffe00ff83ffcff3

def z898 : W := mkw 0x04b112ba20000000 0x0096225744000000 0xc0f3f9fe60000003 0xd81e7f3fcc000000

def z899 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb71fffc39f039ce7 0xf6e3fff873e0739c

def z900 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x88004000181e739d 0x910008000303ce73

def z901 : W := mkw 0x020b80c21a031080 0x8041701843406210 0xb70f87c39f039ce7 0x76e1f0f873e0739c

def z902 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370f87c387039ce3 0x26e1f0f870e0739c

def z903 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08000000181e6004 0x010000000303cc00

def z904 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0x77ffbfdd80e18c60 0x6efff7fbb01c318c

def z905 : W := mkw 0x216557bbe060c634 0x442caaf77c0c18c6 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z906 : W := mkw 0x0001988e300e210a 0x20003311c601c421 0x8813f9fe781e631f 0xd1027f3fcf03cc63

def z907 : W := mkw 0x05f557bae0000000 0x00beaaf75c000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z908 : W := mkw 0x2a4f70cfedb41f07 0x0549ee19fdb683e0 0x180ff803fffc1f05 0x0301ff007fff83e0

def z909 : W := mkw 0x0590051004900000 0x00b200a200920000 0xdff001dc1ffc0004 0xfbfe003b83ff8000

def z910 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013f9fe6000139b 0xd0027f3fcc000273

def z911 : W := mkw 0x0001108a20000000 0x0000221144000000 0x0013b9fe60000002 0x4002773fcc000000

def z912 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xefffffffe0001307 0xfdfffffffc000260

def z913 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67ffbfffe0000002 0x6cfff7fffc000000

def z914 : W := mkw 0x100088441e9f318a 0xa200110883d3e631 0x000000001f1c0000 0x0000000003e38000

def z915 : W := mkw 0x36dee801d6dbe000 0x06dbdd003adb7c00 0xdffff8019fffe005 0xfbffff0033fffc00

def z916 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xb71fffdfff1ffcff 0x76e3fffbffe3ff9f

def z917 : W := mkw 0x16de680004d8e000 0x02dbcd00009b1c00 0xdffff8001ffc6005 0xfbffff0003ff8c00

def z918 : W := mkw 0x27ff77bbe3010840 0x04ffeef77c602108 0xe7ffffffe7000003 0xfcfffffffce00000

def z919 : W := mkw 0x004440000040c000 0x0008880000081800 0xf8ec4623e0e3ffff 0xbf1d88c47c1c7fff

def z920 : W := mkw 0x000198ce3b0f39ca 0xa0003319c761e739 0x8813f9fe7f1e739f 0xd1027f3fcfe3ce73

def z921 : W := mkw 0x069a8800169b2000 0x00d3510002d36400 0xdffff8001fffe005 0xfbffff0003fffc00

def z922 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x8713f9dc00000001 0xd0e27f3b80000000

def z923 : W := mkw 0x0490000004900000 0x0092000000920000 0xdff3f8001ffc0005 0xfbfe7f0003ff8000

def z924 : W := mkw 0x224f708be0000000 0x0449ee117c000000 0x001ff9dfe0000001 0x4003ff3bfc000000

def z925 : W := mkw 0x080088441d9e398b 0xa100110883b3c731 0x000000001f1c0000 0x0000000003e38000

def z926 : W := mkw 0x2491309a20000000 0x0492261344000000 0x8013f9fe60000003 0xd0027f3fcc000000

def z927 : W := mkw 0x06ff72aae0000000 0x00dfee555c000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z928 : W := mkw 0x27ff77bbe040c030 0x44ffeef77c081806 0xe7ffffffe0018063 0xfcfffffffc00300c

def z929 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xf7ffffffe0018c63 0xfefffffffc00318c

def z930 : W := mkw 0x030b8dc71b0f39ca 0xa06171b8e361e739 0xb70f87c39f1f9ce7 0x76e1f0f873e3f39c

def z931 : W := mkw 0x0491108a20000000 0x0092221144000000 0xc7f3f9fe60000003 0xf8fe7f3fcc000000

def z932 : W := mkw 0x030a85411b031840 0x006150a823606308 0xb70f87c19f039c67 0x76e1f0f833e0738c

def z933 : W := mkw 0x27bb37bb20000000 0x04f766f764000000 0x67f3bfdc00000000 0x6cfe77fb80000000

def z934 : W := mkw 0x1044c8441edff18a 0xa208990883dbfe31 0xd8ec40227ffff39f 0xbb1d88044ffffe73

def z935 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08004020781e739c 0x810008040f03ce73

def z936 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x270f87c39f039ce3 0x44e1f0f873e0739c

def z937 : W := mkw 0x000088441b0f39ca 0xa00011088361e739 0x100000001f1f9ce4 0x0200000003e3f39c

def z938 : W := mkw 0x224f708be0000000 0x0449ee117c000000 0x000ff9ffe0000003 0x0001ff3ffc000000

def z939 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0813f9fc781e739c 0xc1027f3f8f03ce73

def z940 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70c06019f018c64 0x76e180c033e0318c

def z941 : W := mkw 0x00208a64182e378e 0xa004114c8305c6f1 0xf8e0062018fe7f9e 0xbf1c00c4031fcff3

def z942 : W := mkw 0x0dd44554cdd4d933 0x41ba88aa99ba9b26 0x071c41dfff1fe0f9 0x40e3883bffe3fc1f

def z943 : W := mkw 0x24f572bae060c634 0x449eae575c0c18c6 0xf8ffffffe0e3ffff 0xff1ffffffc1c7fff

def z944 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x00000000181e6098 0x000000000303cc13

def z945 : W := mkw 0x000088441b0f39ca 0xa00011088361e739 0x080000001f1e739c 0x0100000003e3ce73

def z946 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z947 : W := mkw 0x006552aae0000000 0x000caa555c000000 0xc0f3f9fe60000003 0xd81e7f3fcc000000

def z948 : W := mkw 0x030b85c71b0719c2 0x806170b8e360e338 0xbf1fc7ffff1fffff 0xf7e3f8ffffe3ffff

def z949 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8201ffff307 0xfbffff0403fffe60

def z950 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x47f3b8001ffc0000 0x48fe770003ff8000

def z951 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013f9fc00000003 0xd0027f3f80000000

def z952 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x77f007fc1ffc1f02 0x6efe00ff83ff83e0

def z953 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xcff001fc1ffc1306 0xd9fe003f83ff8260

def z954 : W := mkw 0x0045508ae040c030 0x4008aa115c081806 0x801ff9ffe003e0fb 0xd003ff3ffc007c1f

def z955 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xf7f007fc1ffc0c02 0xfefe00ff83ff8180

def z956 : W := mkw 0x27bb37bb20000000 0x04f766f764000000 0x47f3b9fc00000000 0xc8fe773f80000000

def z957 : W := mkw 0x000088441b0f39ca 0xa00011088361e739 0x000000001f1c0000 0x0000000003e38000

def z958 : W := mkw 0x14d4e80014dae000 0x029a9d00029b5c00 0xdff3f8001ffe6005 0xfbfe7f0003ffcc00

def z959 : W := mkw 0x0cf44230c4f0c635 0x419e8846189e18c6 0x40e0000000e00000 0x081c0000001c0000

def z960 : W := mkw 0x010105c3090018c0 0x802020b861200318 0xb70c07c39f039ce7 0x76e180f873e0739c

def z961 : W := mkw 0x00008844180e318a 0xa00011088301c631 0xb80c0603981fffff 0x370180c07303ffff

def z962 : W := mkw 0x01019dce390e398a 0xa02033b9c721c731 0xbf1fffffff1fffff 0xf7e3ffffffe3ffff

def z963 : W := mkw 0x000088441a0f318a 0xa00011088341e631 0x180000001f1ff39c 0x0300000003e3fe73

def z964 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x47f001dc1ffc0000 0x48fe003b83ff8000

def z965 : W := mkw 0x27ff77bbe0200604 0x04ffeef77c0400c0 0xe7ffffffe0001f03 0xfcfffffffc0003e0

def z966 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xffffffffe0e07f1f 0xfffffffffc1c0fe3

def z967 : W := mkw 0x27bb37bbe0000000 0x04f766f77c000000 0xa713ffffe0000003 0xd4e27ffffc000000

def z968 : W := mkw 0x0490000004900000 0x0092000000920000 0xdff001fc1ffc0006 0xfbfe003f83ff8000

def z969 : W := mkw 0x16dee800169b2000 0x02dbdd0002d36400 0xdffff8001ffc0005 0xfbffff0003ff8000

def z970 : W := mkw 0x279b359b20000000 0x04f366b364000000 0xa713bfdc00000002 0x74e277fb80000000

def z971 : W := mkw 0x030b85c71b0719c2 0x806170b8e360e338 0xb70f87ff9f039fe7 0x76e1f0fff3e073fc

def z972 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370f87c39f038ce1 0x66e1f0f873e0719c

def z973 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xf7ffffffe0e19ffb 0xfefffffffc1c33ff

def z974 : W := mkw 0x16dee800d6dbe000 0x02dbdd001adb7c00 0xdffff803ffffe005 0xfbffff007ffffc00

def z975 : W := mkw 0x030b058303010840 0x006160b060602108 0xb70f87c387039ce7 0x76e1f0f870e0739c

def z976 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x78ec4603e0e3fffd 0x2f1d88c07c1c7fff

def z977 : W := mkw 0x080088441cbe378f 0xa10011088397c6f1 0x0800000018fe739c 0x01000000031fce73

def z978 : W := mkw 0x00008844180e3102 0x000011088301c620 0x8813f9fe781e739f 0xd1027f3fcf03ce73

def z979 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x8713b9fc00000002 0xd0e2773f80000000

def z980 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xbf1f87c39f1f9ce7 0xf7e3f0f873e3f39c

def z981 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x47fff9ffe0000001 0xc8ffff3ffc000000

def z982 : W := mkw 0x169aa80016dbe000 0x02d3550002db7c00 0xdff3b8001fffe004 0xfbfe770003fffc00

def z983 : W := mkw 0x030a05410b011840 0x006140a821602308 0x370c06019f019c64 0x26e180c033e0338c

def z984 : W := mkw 0x0064ca64d86ef7be 0xe00c994c9b0ddef7 0x48e0402078fe739c 0x891c08040f1fce73

def z985 : W := mkw 0x0001188e200c210a 0x20002311c4018421 0x8813f9fe601e739f 0xd1027f3fcc03ce73

def z986 : W := mkw 0x179bbdcf3f9f39ca 0xa2f377b9e7f3e739 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z987 : W := mkw 0x27df759b20000000 0x04fbeeb364000000 0x47ffb9dc00000000 0x68fff73b80000000

def z988 : W := mkw 0x27ff77bbe00000c0 0x84ffeef77c000018 0xe7ffffffe00000e3 0xfcfffffffc00001c

def z989 : W := mkw 0x030a850113030840 0x006150a022606108 0x370c06019f038c64 0x26e180c033e0718c

def z990 : W := mkw 0x292117ffe9241f8f 0xa52422fffd2483f1 0x200007ffe0001f9a 0x040000fffc0003f3

def z991 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x6ff007fc1ffc1f02 0xcdfe00ff83ff83e0

def z992 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x0713f9de60000001 0x40e27f3bcc000000

def z993 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xffffffffe0e3e31f 0xfffffffffc1c7c63

def z994 : W := mkw 0x2fff77bbe1200e05 0x05ffeef77c2401c0 0xe7ffffffe0000c03 0xfcfffffffc000180

def z995 : W := mkw 0x00008844182e37be 0xe00011088305c6f7 0x08000000181e7ffc 0x010000000303cfff

def z996 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70c060387018c63 0x36e180c070e0318c

def z997 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007fe1ffe1f87 0xfffe00ffc3ffc3f0

def z998 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff047fc7ffc7f1e 0xfffe08ff8fff8fe3

def z999 : W := mkw 0x0045508a20000000 0x0008aa1144000000 0xc0fff9fe60000003 0xf81fff3fcc000000

def z1000 : W := mkw 0x08008844192e3f8f 0xa10011088325c7f1 0x08000000181e7f9c 0x010000000303cff3

def z1001 : W := mkw 0x010085401b0318c0 0x802010a803606318 0xb70c07c39f039ce7 0x76e180f873e0739c

def z1002 : W := mkw 0x0000984c380e310a 0x200013098701c621 0x8813f9fc781e731f 0xd1027f3f8f03ce63

def z1003 : W := mkw 0x030b95cf3b0719ca 0xa06172b9e760e339 0xb71fffffff039fff 0xf6e3ffffffe073ff

def z1004 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8227fffe007 0xfbffff044ffffc00

def z1005 : W := mkw 0x27ff77bbe4f0c634 0x44ffeef77c9e18c6 0xffffffffffffffff 0xffffffffffffffff

def z1006 : W := mkw 0x230b95db3b0318c0 0x846172bb67606318 0xb70f87df9f039ce7 0x76e1f0fbf3e0739c

def z1007 : W := mkw 0x030b9dcb3b0b38c8 0xa06173b967616719 0xbf0fffe3ff03ffff 0xf7e1fffc7fe07fff

def z1008 : W := mkw 0x020b108a20000000 0x0041621144000000 0x871ff9fe60000003 0xf0e3ff3fcc000000

def z1009 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfffc47ffffffffff 0xffff88ffffffffff

def z1010 : W := mkw 0x37ff77bbe4d0c000 0x06ffeef77c9a1800 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z1011 : W := mkw 0x27ff77bbe040c000 0x04ffeef77c081800 0xe7ffffffe003e003 0xfcfffffffc007c00

def z1012 : W := mkw 0x27df759be0000000 0x04fbeeb37c000000 0x871ff9ffe0000003 0xd0e3ff3ffc000000

def z1013 : W := mkw 0x16dee80016dbe0c0 0x82dbdd0002db7c18 0xdffff8001fffe0e5 0xfbffff0003fffc1c

def z1014 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x7ff007dc1ffc1f04 0x6ffe00fb83ff83e0

def z1015 : W := mkw 0x030b05c30b0118c0 0x806160b861602318 0xb70c07c387039ce7 0x36e180f870e0739c

def z1016 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0xdff001fc1ffc1306 0xfbfe003f83ff8260

def z1017 : W := mkw 0x27fe6731c0000000 0x04ffcce638000000 0xe7fffffd80000003 0xfcffffffb0000000

def z1018 : W := mkw 0x0000000000000000 0x0000000000000000 0xb70c06039f039ce7 0x76e180c073e0739c

def z1019 : W := mkw 0x030b8dc31b0b38c0 0x806171b863616718 0xb70fffc39f03fce7 0x76e1fff873e07f9c

def z1020 : W := mkw 0x012117ba20000000 0x002422f744000000 0xa013fffe60000003 0xd4027fffcc000000

def z1021 : W := mkw 0x080088441d9e398b 0xa100110883b3c731 0x080000001f1e739c 0x0100000003e3ce73

def z1022 : W := mkw 0x37ff77bbe7d1c840 0x06ffeef77cfa3908 0xf7ffffffe7e18c63 0xfefffffffcfc318c

def z1023 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xfffffe23ffffffff 0xffffffc47fffffff

def z1024 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8813f9fc781e631d 0xd1027f3f8f03cc63

def z1025 : W := mkw 0x37ff77bbe6f1c634 0x46ffeef77cde38c6 0xffffffffe7e3ffff 0xfffffffffcfc7fff

def z1026 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8039fffe0e5 0xfbffff0073fffc1c

def z1027 : W := mkw 0x030b8dc71b0f39ca 0xa06171b8e361e739 0xbf0fc7e3ff1fffff 0xf7e1f8fc7fe3ffff

def z1028 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffffe002609b 0xfcfffffffc004c13

def z1029 : W := mkw 0x002112aae0200634 0x400422555c0400c6 0xa013ffffe0001ffb 0xd4027ffffc0003ff

def z1030 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0xa813fffff81e7fff 0xd5027fffff03cfff

def z1031 : W := mkw 0x030b95cb3b0318c0 0x806172b967606318 0xb70f87ffff039ce7 0x76e1f0ffffe0739c

def z1032 : W := mkw 0x1864ca641fffff07 0x030c994c83ffffe0 0xf8ec46201fffff07 0xbf1d88c403ffffe0

def z1033 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xffffffffe003ffff 0xfffffffffc007fff

def z1034 : W := mkw 0x04b002640cb41706 0x0096004c819682e0 0xfff007fc1ffc1f06 0xfffe00ff83ff83e0

def z1035 : W := mkw 0x37ff77bbe241c000 0x06ffeef77c483800 0xe7ffffffe0018003 0xfcfffffffc003000

def z1036 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x47f3b9dc00000000 0x48fe773b80000000

def z1037 : W := mkw 0x00208a64d82e37be 0xe004114c9b05c6f7 0x28000623f81e7ffe 0x050000c47f03cfff

def z1038 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xefffffffe0e07ffb 0xfdfffffffc1c0fff

def z1039 : W := mkw 0x27bb37bbe0000000 0x04f766f77c000000 0xa71fbfffe0000003 0x74e3f7fffc000000

def z1040 : W := mkw 0x1ffe6730c7f1ce35 0x43ffcce618fe39c6 0x77ec060187e18c60 0x2efd80c030fc318c

def z1041 : W := mkw 0x34f47a38e4f8e634 0x469e8f471c9f1cc6 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z1042 : W := mkw 0x030a050103010840 0x006140a020602108 0x370c060187039ce4 0x26e180c030e0739c

def z1043 : W := mkw 0x26ff72bbe0000000 0x04dfee577c000000 0xc0fff9ffe0000003 0xd81fff3ffc000000

def z1044 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xbf1fffdf9f1ffce7 0xf7e3fffbf3e3ff9c

def z1045 : W := mkw 0x0db007750db41f47 0x01b600eea1b683e8 0xfff007fd9ffc1f66 0xfffe00ffb3ff83ec

def z1046 : W := mkw 0x030b95cb3b0318c0 0x806172b967606318 0xbf1fffffff03ffff 0xf7e3ffffffe07fff

def z1047 : W := mkw 0x27ff77bbe040c000 0x04ffeef77c081800 0xf7ffffffe0e18003 0xfefffffffc1c3000

def z1048 : W := mkw 0x030b9dcb3b0b38c8 0xa06173b967616719 0xb71fffffff03fcff 0xf6e3ffffffe07f9f

def z1049 : W := mkw 0x030b9dcb3b0b38c0 0x806173b967616718 0xbf1fffffff1ffce7 0xf7e3ffffffe3ff9c

def z1050 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x0713b9fe60000002 0x40e2773fcc000000

def z1051 : W := mkw 0x024ec800124be000 0x0049d90002497c00 0xdffff8001fffe005 0xfbffff0003fffc00

def z1052 : W := mkw 0x0100050001000800 0x002000a000200100 0xb70c060387039ce7 0x36e180c070e0739c

def z1053 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffffe0021087 0xfcfffffffc004210

def z1054 : W := mkw 0x27ff77bbe0000030 0x44ffeef77c000006 0xe7ffffffe00000fb 0xfcfffffffc00001f

def z1055 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xefffffffe0e2739f 0xfdfffffffc1c4e73

def z1056 : W := mkw 0x030a05410b011840 0x006140a821602308 0xb70c07c39f039ce7 0x76e180f873e0739c

def z1057 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x9f13f9fe7f1e739f 0xf3e27f3fcfe3ce73

def z1058 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xc7f3f9fe60000003 0xd8fe7f3fcc000000

def z1059 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x67fffffde0000000 0xecffffffbc000000

def z1060 : W := mkw 0x27ff77bbe3010840 0x04ffeef77c602108 0xf7ffffffe7039ce7 0xfefffffffce0739c

def z1061 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xefffffffe0e3e3fb 0xfdfffffffc1c7c7f

def z1062 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8001ffffce5 0xfbffff0003ffff9c

def z1063 : W := mkw 0x230b359b20000000 0x046166b364000000 0x0003b9dc00000000 0x0000773b80000000

def z1064 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70f87c19f038c65 0x76e1f0f833e0718c

def z1065 : W := mkw 0x27ff77bbe361ce74 0x44ffeef77c6c39ce 0xffffffffe7e3ffff 0xfffffffffcfc7fff

def z1066 : W := mkw 0x030b05c309001800 0x006160b861200300 0xb70f87c39f039ce7 0x76e1f0f873e0739c

def z1067 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xf7f007dc1ffc1c06 0x7efe00fb83ff8380

def z1068 : W := mkw 0x24f572bae060c634 0x449eae575c0c18c6 0xc8f3f9fe60e2739f 0xd91e7f3fcc1c4e73

def z1069 : W := mkw 0x130badc31b0b38c0 0x826175b863616718 0xb70fbfc39f039ce7 0x76e1f7f873e0739c

def z1070 : W := mkw 0x180088441fffffc7 0x8300110883fffff8 0x180000001fffffe4 0x0300000003fffffc

def z1071 : W := mkw 0x030b158b20000000 0x006162b164000000 0xa71fbfdf80000003 0x74e3f7fbf0000000

def z1072 : W := mkw 0x212117bbe0000000 0x042422f77c000000 0x2003ffffe0000003 0x04007ffffc000000

def z1073 : W := mkw 0x27ff77bbe4d0c000 0x04ffeef77c9a1800 0xffffffffffffe007 0xfffffffffffffc00

def z1074 : W := mkw 0x24f572bae0000000 0x049eae575c000000 0x40f3f9fc60000000 0xc81e7f3f8c000000

def z1075 : W := mkw 0x080088441fbf3fcf 0xa100110883f7e7f9 0x180000001ffffffc 0x0300000003ffffff

def z1076 : W := mkw 0x27ff77bbe1000840 0x04ffeef77c200108 0xe7ffffffe0000c63 0xfcfffffffc00018c

def z1077 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xcffff8001ffc6001 0xf9ffff0003ff8c00

def z1078 : W := mkw 0x100088441efff7be 0xe200110883dffef7 0x180000001ffffffc 0x0300000003ffffff

def z1079 : W := mkw 0x0001988a300a2000 0x0000331146014400 0x8813f9fe781e739f 0xd1027f3fcf03ce73

def z1080 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70fc7c3ff03fcff 0x76e1f8f87fe07f9f

def z1081 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x0713f9fc60000000 0xc0e27f3f8c000000

def z1082 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013f9fe60021087 0xd0027f3fcc004210

def z1083 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08004002781e739d 0x010008004f03ce73

def z1084 : W := mkw 0x230bb5cb3b0318c0 0x846176b967606318 0xb70fbfc39f039ce7 0x76e1f7f873e0739c

def z1085 : W := mkw 0x030a85411b0318c0 0x806150a823606318 0xb70f86019f039ce5 0x76e1f0c033e0739c

def z1086 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xb71fbfffff1f9fff 0x76e3f7ffffe3f3ff

def z1087 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x881ff9fff81ff3ff 0xd103ff3fff03fe7f

def z1088 : W := mkw 0x27ff77bbe0200604 0x04ffeef77c0400c0 0xefffffffe0e00303 0xfdfffffffc1c0060

def z1089 : W := mkw 0x00008844186ef7be 0xe0001108830ddef7 0x0800000018fe739c 0x01000000031fce73

def z1090 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70f860187018c61 0x76e1f0c030e0318c

def z1091 : W := mkw 0x036f57abe060c634 0x406deaf57c0c18c6 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z1092 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x5ff3f8001fffe004 0xcbfe7f0003fffc00

def z1093 : W := mkw 0x234f759be0000000 0x0469eeb37c000000 0x000ff9dfe0000001 0x0001ff3bfc000000

def z1094 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff3fffc1ffc1f07 0xfffe7fff83ff83e0

def z1095 : W := mkw 0x100088441edff102 0x0200110883dbfe20 0x180000001ffff304 0x0300000003fffe60

def z1096 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x271fbfdd80000000 0x64e3f7fbb0000000

def z1097 : W := mkw 0x27df759be040c030 0x44fbeeb37c081806 0x071ff9dfe003e0f9 0x40e3ff3bfc007c1f

def z1098 : W := mkw 0x232b37bbe0000000 0x046566f77c000000 0x2003bfffe0000002 0x040077fffc000000

def z1099 : W := mkw 0x16dee800d6dbe030 0x42dbdd001adb7c06 0xfffffe03fffffcff 0xffffffc07fffff9f

def z1100 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x871fb9dc00000001 0x70e3f73b80000000

def z1101 : W := mkw 0x020b98ce3a0f318a 0xa0417319c741e631 0xbf1fffffff1fffff 0xf7e3ffffffe3ffff

def z1102 : W := mkw 0x0001108a20000000 0x0000221144000000 0x0003f9fe60000003 0x00007f3fcc000000

def z1103 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x8813f9fc781c731e 0xd1027f3f8f038e63

def z1104 : W := mkw 0x0001188e200c210a 0x20002311c4018421 0x0813f9fc601c6318 0xc1027f3f8c038c63

def z1105 : W := mkw 0x27ff77bbe040c000 0x04ffeef77c081800 0xefffffffe0e06003 0xfdfffffffc1c0c00

def z1106 : W := mkw 0x279b359b23010840 0x04f366b364602108 0x371fbfdd87018c60 0x66e3f7fbb0e0318c

def z1107 : W := mkw 0x0100054009001800 0x002000a801200300 0xb70c07c19f019c66 0x76e180f833e0338c

def z1108 : W := mkw 0x2491309a20000000 0x0492261344000000 0x0013b9dc00000000 0x4002773b80000000

def z1109 : W := mkw 0x16dee80116dbe040 0x02dbdd0022db7c08 0xdffff8019fffe065 0xfbffff0033fffc0c

def z1110 : W := mkw 0x212117bbe0000000 0x042422f77c000000 0x2013bfffe0000002 0x440277fffc000000

def z1111 : W := mkw 0x0db117ba25b00e05 0x01b622f744b601c0 0xf7f3fffe67e00c03 0xfefe7fffccfc0180

def z1112 : W := mkw 0x030b95cf3b0719ca 0xa06172b9e760e339 0xb70f87df9f039ce7 0x76e1f0fbf3e0739c

def z1113 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xfffffe019fffec65 0xffffffc033fffd8c

def z1114 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x88000020181e739e 0x910000040303ce73

def z1115 : W := mkw 0x27bb37bb20200604 0x04f766f7640400c0 0xfff3bffc00e01f06 0xfffe77ff801c03e0

def z1116 : W := mkw 0x324ff88b324be000 0x0649ff1166497c00 0x000ff8000003e001 0x0001ff0000007c00

def z1117 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x2713bfdf80000002 0x44e277fbf0000000

def z1118 : W := mkw 0x27ff77bbe4b00604 0x04ffeef77c9600c0 0xfffffffffffc1f07 0xffffffffffff83e0

def z1119 : W := mkw 0x0ede60440db41f07 0x01dbcc0881b683e0 0xdffff8001ffc1f05 0xfbffff0003ff83e0

def z1120 : W := mkw 0x0491108a24900000 0x0092221144920000 0xdff3f9fe7ffc0007 0xfbfe7f3fcfff8000

def z1121 : W := mkw 0x020a800012030000 0x0041500002406000 0xb70f86019f038c65 0x76e1f0c033e0718c

def z1122 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0xd8f3f9fe78fe739f 0xfb1e7f3fcf1fce73

def z1123 : W := mkw 0x180088441fffff37 0x4300110883ffffe6 0x180000001ffffffc 0x0300000003ffffff

def z1124 : W := mkw 0x0d9005540db41f07 0x01b200aa81b683e0 0xdff001dc1ffc1f04 0xfbfe003b83ff83e0

def z1125 : W := mkw 0x030a850113030840 0x006150a022606108 0x370f860187038c61 0x26e1f0c030e0718c

def z1126 : W := mkw 0x226f72abe0000000 0x044dee557c000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1127 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xcff3f8001ffe6005 0xd9fe7f0003ffcc00

def z1128 : W := mkw 0x06df708a2040c000 0x00dbee1144081800 0xdffff9fe60e3f39f 0xfbffff3fcc1c7e73

def z1129 : W := mkw 0x279b359be0000000 0x04f366b37c000000 0x0713b9dfe0000000 0x40e2773bfc000000

def z1130 : W := mkw 0x030b8dc31b0b38c0 0x806171b863616718 0xbf0f87c39f1ffce7 0x77e1f0f873e3ff9c

def z1131 : W := mkw 0x0001108a20000000 0x0000221144000000 0x0013f9fc60000000 0xc0027f3f8c000000

def z1132 : W := mkw 0x024fd88bf24be0f8 0xe049fb117e497c1f 0x000ff803e003e0f9 0x0001ff007c007c1f

def z1133 : W := mkw 0x2fff77bbe5b00e05 0x05ffeef77cb601c0 0xfffffffffffc0c07 0xffffffffffff8180

def z1134 : W := mkw 0x000198ce390e398a 0xa0003319c721c731 0x9813f9fe7f1e7f9f 0xd3027f3fcfe3cff3

def z1135 : W := mkw 0x000198ce3a0f31ca 0xa0003319c741e639 0x8813f9fe781ff3ff 0xd1027f3fcf03fe7f

def z1136 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0x4ff3f9fc60e06318 0xc9fe7f3f8c1c0c63

def z1137 : W := mkw 0x27bb37bbe0200634 0x44f766f77c0400c6 0x2713bfffe0001ffa 0x44e277fffc0003ff

def z1138 : W := mkw 0x27df759b2040c000 0x04fbeeb364081800 0xdffff9dc00e3e005 0xfbffff3b801c7c00

def z1139 : W := mkw 0x27df759be0000000 0x04fbeeb37c000000 0x0713f9dc60000000 0x40e27f3b8c000000

def z1140 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x88000002181e739f 0x110000004303ce73

def z1141 : W := mkw 0x279b359b20000000 0x04f366b364000000 0xb71fbfdf80039ce7 0x76e3f7fbf000739c

def z1142 : W := mkw 0x37ff77bbe6f1c634 0x46ffeef77cde38c6 0xf7ffffffe7e18c63 0xfefffffffcfc318c

def z1143 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0x57f001dc1ffc0000 0x6afe003b83ff8000

def z1144 : W := mkw 0x0db007740d941903 0x01b600ee81b28320 0xfff007fc1ffc0006 0xfffe00ff83ff8000

def z1145 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0xa81ffffff81e739f 0xf503ffffff03ce73

def z1146 : W := mkw 0x0db00774cdb41f37 0x41b600ee99b683e6 0xfff047fffffe7fff 0xfffe08ffffffcfff

def z1147 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xeff007fc1ffc0302 0xfdfe00ff83ff8060

def z1148 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x7ff007fc1ffc0f00 0xeffe00ff83ff81e0

def z1149 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0xdff3f8001ffe6005 0xfbfe7f0003ffcc00

def z1150 : W := mkw 0x00008844190e398a 0xa00011088321c731 0x180000001f1e7f9c 0x0300000003e3cff3

def z1151 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0013f9fe781e739b 0x40027f3fcf03ce73

def z1152 : W := mkw 0x030b9d8b330b28c8 0xa06173b166616519 0x370ffe03e703ecf9 0x26e1ffc07ce07d9f

def z1153 : W := mkw 0x05b117ba20200604 0x00b622f7440400c0 0xfff3fffe60e27f9f 0xfffe7fffcc1c4ff3

def z1154 : W := mkw 0x000088441a0f31ca 0xa00011088341e639 0x08000000181ff3fc 0x010000000303fe7f

def z1155 : W := mkw 0x2db00775cdb41f07 0x05b600eeb9b683e0 0xfff007fd9ffc1f06 0xfffe00ffb3ff83e0

def z1156 : W := mkw 0x2101159b20000000 0x042022b364000000 0x0013b9dc00000000 0x4002773b80000000

def z1157 : W := mkw 0x000118ce280c310a 0x20002319c5018621 0x8813f9fe781c731f 0xd1027f3fcf038e63

def z1158 : W := mkw 0x27ff77bbe0000088 0xa4ffeef77c000011 0xe7ffffffe000009b 0xfcfffffffc000013

def z1159 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007dc1ffc0c04 0xfffe00fb83ff8180

def z1160 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0xdfffb8001fff8005 0xfbfff70003fff000

def z1161 : W := mkw 0x020a000002010000 0x0041400000402000 0xb70c060387039ce7 0x36e180c070e0739c

def z1162 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08000000181c1304 0x0100000003038260

def z1163 : W := mkw 0x07fe67300060c604 0x00ffcce6000c18c0 0xfffffffc00e3ff07 0xffffffff801c7fe0

def z1164 : W := mkw 0x006552aae060c634 0x400caa555c0c18c6 0xc8f3f9fe60e0631b 0xd91e7f3fcc1c0c63

def z1165 : W := mkw 0x26df708be0000000 0x04dbee117c000000 0xc7fff9ffe0000003 0xf8ffff3ffc000000

def z1166 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x68ec4623e0e3fffb 0x8d1d88c47c1c7fff

def z1167 : W := mkw 0x0001108a20000088 0xa000221144000011 0x8013f9fe6000009b 0xd0027f3fcc000013

def z1168 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xbf0fc7c39f03fce7 0xf7e1f8f873e07f9c

def z1169 : W := mkw 0x37ff77bbe6d1c000 0x06ffeef77cda3800 0xffffffffe7e3e007 0xfffffffffcfc7c00

def z1170 : W := mkw 0x27bb37bb20000000 0x04f766f764000000 0xe7f3fffe60000003 0xfcfe7fffcc000000

def z1171 : W := mkw 0x37ff77bbe6d1c000 0x06ffeef77cda3800 0xfffffffffffd8007 0xffffffffffffb000

def z1172 : W := mkw 0x236f77bbe0000000 0x046deef77c000000 0xe0efffffe0000003 0xbc1dfffffc000000

def z1173 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xbf1fbfff9f1f9fe7 0xf7e3f7fff3e3f3fc

def z1174 : W := mkw 0x04d5708a20000000 0x009aae1144000000 0xc0f3f9fe60000003 0xd81e7f3fcc000000

def z1175 : W := mkw 0x030a85411b0318c0 0x806150a823606318 0xb70c07c19f039ce6 0x76e180f833e0739c

def z1176 : W := mkw 0x0d9005540d941903 0x01b200aa81b28320 0x4ff001dc1ffc0000 0xc9fe003b83ff8000

def z1177 : W := mkw 0x07fe6730c060c634 0x40ffcce6180c18c6 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z1178 : W := mkw 0x092117fe29241f8f 0xa12422ffc52483f1 0x200007fc00001f02 0x040000ff800003e0

def z1179 : W := mkw 0x0100050001000800 0x002000a000200100 0x370c060187018c60 0x26e180c030e0318c

def z1180 : W := mkw 0x180088441fdff903 0x0300110883fbff20 0x180000001fffe004 0x0300000003fffc00

def z1181 : W := mkw 0x080088441dbe3f8f 0xa100110883b7c7f1 0x180000001ffc1f04 0x0300000003ff83e0

def z1182 : W := mkw 0x0cf44274ccf4d737 0x419e884e999e9ae6 0xc8f041fe78fe739f 0xd91e083fcf1fce73

def z1183 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70c07c187018c62 0x76e180f830e0318c

def z1184 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8813f9fe6000631b 0xd1027f3fcc000c63

def z1185 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8207fffe31d 0xfbffff040ffffc63

def z1186 : W := mkw 0x14f46220c4f0c634 0x429e8c44189e18c6 0x40e0000000e00000 0x081c0000001c0000

def z1187 : W := mkw 0x14f4ea20d4fae634 0x429e9d441a9f5cc6 0xc8f3f82278fe739f 0xd91e7f044f1fce73

def z1188 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb71f87ff9f039ce7 0xf6e3f0fff3e0739c

def z1189 : W := mkw 0x020a80401b0318c0 0x8041500803606318 0xb70f86039f039ce7 0x76e1f0c073e0739c

def z1190 : W := mkw 0x27ff77bbe0200604 0x04ffeef77c0400c0 0xffffffffe0e39fe7 0xfffffffffc1c73fc

def z1191 : W := mkw 0x27ff77bbe0200634 0x44ffeef77c0400c6 0xe7ffffffe000031b 0xfcfffffffc000063

def z1192 : W := mkw 0x092117fee9241fbf 0xe12422ffdd2483f7 0x200007ffe0001ffa 0x040000fffc0003ff

def z1193 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x00000000181c1398 0x0000000003038273

def z1194 : W := mkw 0x0f9b9ddf3f9f39cb 0xa1f373bbe7f3e739 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z1195 : W := mkw 0x0cb002740cb41707 0x0196004e819682e0 0xdff001fc1ffc1306 0xfbfe003f83ff8260

def z1196 : W := mkw 0x030b05c30b011840 0x006160b861602308 0xb70f87c39f019c67 0x76e1f0f873e0338c

def z1197 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xffffffffe0e3ec67 0xfffffffffc1c7d8c

def z1198 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0x57f3b8001ffc0000 0x6afe770003ff8000

def z1199 : W := mkw 0x030b858313030840 0x006170b062606108 0xb70f87c39f038c67 0x76e1f0f873e0718c

def z1200 : W := mkw 0x202112bae0000000 0x040422575c000000 0x8013f9fe60000003 0xd0027f3fcc000000

def z1201 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370f86039f039ce5 0x26e1f0c073e0739c

def z1202 : W := mkw 0x08208a641dbe3f8f 0xa104114c83b7c7f1 0xf8e046227ffe7f9f 0xbf1c08c44fffcff3

def z1203 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7ffffffe000139b 0xfcfffffffc000273

def z1204 : W := mkw 0x030b85c71b0719c2 0x806170b8e360e338 0xbf0f87c39f1f9fe7 0x77e1f0f873e3f3fc

def z1205 : W := mkw 0x2fff77bbe5f0ce35 0x45ffeef77cbe19c6 0xffffffffe7e3ffff 0xfffffffffcfc7fff

def z1206 : W := mkw 0x27ff77bbe040c000 0x04ffeef77c081800 0xffffffffe0e3fce7 0xfffffffffc1c7f9c

def z1207 : W := mkw 0x27ff77bbe040c030 0x44ffeef77c081806 0xe7ffffffe000601b 0xfcfffffffc000c03

def z1208 : W := mkw 0x030a050103010840 0x006140a020602108 0xb70c060187038c65 0x36e180c030e0718c

def z1209 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8813f9fe781c0007 0xd1027f3fcf038000

def z1210 : W := mkw 0x37fe6731c6f1c634 0x46ffcce638de38c6 0x77ec060187e18c60 0x2efd80c030fc318c

def z1211 : W := mkw 0x27df759b20000000 0x04fbeeb364000000 0xc7fff9fe60000003 0xf8ffff3fcc000000

def z1212 : W := mkw 0x14f46220c4f0c634 0x429e8c44189e18c6 0x48e0402060e06318 0x891c08040c1c0c63

def z1213 : W := mkw 0x124ff88a324be000 0x0249ff1146497c00 0x000ff8026003e001 0x0001ff004c007c00

def z1214 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007ff9ffc1fe6 0xfffe00fff3ff83fc

def z1215 : W := mkw 0x049000440c941102 0x0092000881928220 0xdff001dc1ffc0004 0xfbfe003b83ff8000

def z1216 : W := mkw 0x030b15cf2b0519ca 0xa06162b9e560a339 0x370c07ffe7019ffa 0x26e180fffce033ff

def z1217 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xd7ffb8001fff8005 0x7afff70003fff000

def z1218 : W := mkw 0x07de651000000000 0x00fbcca200000000 0xc7fff9dc00000001 0xf8ffff3b80000000

def z1219 : W := mkw 0x030b8dc71b0f39ca 0xa06171b8e361e739 0xbf1f87ff9f1fffff 0xf7e3f0fff3e3ffff

def z1220 : W := mkw 0x0cf45a3ce4fce73f 0x619e8b479c9f9ce7 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z1221 : W := mkw 0x030a050103010840 0x006140a020602108 0x370c060387038ce1 0x26e180c070e0719c

def z1222 : W := mkw 0x030a05410b011840 0x006140a821602308 0x370c07c187019c62 0x26e180f830e0338c

def z1223 : W := mkw 0x0044c844184ef18a 0xa00899088309de31 0xd8ec400018fff39d 0xbb1d8800031ffe73

def z1224 : W := mkw 0x030b8dc71b0f39ca 0xa06171b8e361e739 0xbf1fffc39f1fffff 0xf7e3fff873e3ffff

def z1225 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8001ffff39d 0xfbffff0003fffe73

def z1226 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff047fc1ffe7f07 0xfffe08ff83ffcfe0

def z1227 : W := mkw 0x07ff77ba20000000 0x00ffeef744000000 0xe7fffffe60000003 0xfcffffffcc000000

def z1228 : W := mkw 0x030b8dc31b0b38c0 0x806171b863616718 0xbf1fffe3ff1fffff 0xf7e3fffc7fe3ffff

def z1229 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x071fb9df80000001 0x40e3f73bf0000000

def z1230 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x60ffffffe0000003 0x8c1ffffffc000000

def z1231 : W := mkw 0x220b308b20000000 0x0441661164000000 0x8013f9fe60000003 0xd0027f3fcc000000

def z1232 : W := mkw 0x180088441fbf3f07 0x0300110883f7e7e0 0x180000001ffc1f04 0x0300000003ff83e0

def z1233 : W := mkw 0x000198ce3b0f39ca 0xa0003319c761e739 0xb81fffffff1fffff 0xf703ffffffe3ffff

def z1234 : W := mkw 0x100088441edff18a 0xa200110883dbfe31 0x180000001fffe004 0x0300000003fffc00

def z1235 : W := mkw 0x324ff88bf24be030 0x4649ff117e497c06 0x000ff803e003e0f9 0x0001ff007c007c1f

def z1236 : W := mkw 0x180088441fffff8f 0xa300110883fffff1 0x180000001fffff9c 0x0300000003fffff3

def z1237 : W := mkw 0x279b359b24900000 0x04f366b364920000 0x0713b9dc1f1c0000 0x40e2773b83e38000

def z1238 : W := mkw 0x1864ca64dfffff37 0x430c994c9bffffe6 0xf8ec4623ffffffff 0xbf1d88c47fffffff

def z1239 : W := mkw 0x0db00774cdb41f37 0x41b600ee99b683e6 0xfff007fd9ffc1f66 0xfffe00ffb3ff83ec

def z1240 : W := mkw 0x06dee00016930000 0x00dbdc0002d26000 0xdffff8001fff8005 0xfbffff0003fff000

def z1241 : W := mkw 0x000088441c9e318a 0xa00011088393c631 0x180000001ffe739c 0x0300000003ffce73

def z1242 : W := mkw 0x030b85c71b0719c2 0x806170b8e360e338 0xb71f87df9f1f9ce7 0x76e3f0fbf3e3f39c

def z1243 : W := mkw 0x05f557bae060c634 0x40beaaf75c0c18c6 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z1244 : W := mkw 0x030b05c30b0118c0 0x806160b861602318 0x370c07c187018c60 0x26e180f830e0318c

def z1245 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x5feff8001fffe005 0x2bfdff0003fffc00

def z1246 : W := mkw 0x16dee800d6dbe030 0x42dbdd001adb7c06 0xdffff823fffff3ff 0xfbffff047ffffe7f

def z1247 : W := mkw 0x2fbb37bb25b00e05 0x05f766f764b601c0 0x77f3bfdc07e00c00 0x6efe77fb80fc0180

def z1248 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0x370f87c39f019ce2 0x66e1f0f873e0339c

def z1249 : W := mkw 0x0101158b20000000 0x002022b164000000 0xa013ffffe0000003 0xd4027ffffc000000

def z1250 : W := mkw 0x080088441dbe3f07 0x0100110883b7c7e0 0x180000001ffe7f04 0x0300000003ffcfe0

def z1251 : W := mkw 0x16df708a26d1c000 0x02dbee1144da3800 0xd7fff9fe67e18003 0xfaffff3fccfc3000

def z1252 : W := mkw 0x379b359b26910000 0x06f366b364d22000 0x0713b9dc07000000 0x40e2773b80e00000

def z1253 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0x5ff001fc1ffc1f04 0xcbfe003f83ff83e0

def z1254 : W := mkw 0x16dee800d6dbe030 0x42dbdd001adb7c06 0xdffff8007fffe01d 0xfbffff000ffffc03

def z1255 : W := mkw 0x080088441dfeffbf 0xe100110883bfdff7 0x180000001ffffffc 0x0300000003ffffff

def z1256 : W := mkw 0x020b8083120300c0 0x8041701062406018 0xb70f86039f039ce7 0x76e1f0c073e0739c

def z1257 : W := mkw 0x06ff72aae060c634 0x40dfee555c0c18c6 0xffffffffe0e3ffff 0xfffffffffc1c7fff

def z1258 : W := mkw 0x030a05410b0118c0 0x806140a821602318 0x370c060187019ce0 0x26e180c030e0339c

def z1259 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x08000022781e739e 0x010000044f03ce73

def z1260 : W := mkw 0x27bb37bbe0000000 0x04f766f77c000000 0x0713b9fc60000000 0x40e2773f8c000000

def z1261 : W := mkw 0x324ff88bf24be0c0 0x8649ff117e497c18 0x000ff803e003e0e1 0x0001ff007c007c1c

def z1262 : W := mkw 0x0001988e300e218a 0xa0003311c601c431 0x8813f9fe601e639b 0xd1027f3fcc03cc73

def z1263 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdffff8021ffff087 0xfbffff0043fffe10

def z1264 : W := mkw 0x030b8583130308c0 0x806170b062606118 0xb70f860387039ce7 0x36e1f0c070e0739c

def z1265 : W := mkw 0x279b359b20000000 0x04f366b364000000 0xc7f3b9dc00000000 0xf8fe773b80000000

def z1266 : W := mkw 0x216557bbe0000000 0x042caaf77c000000 0xe0ffffffe0000003 0xfc1ffffffc000000

def z1267 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0x271fffffe0000003 0x44e3fffffc000000

def z1268 : W := mkw 0x030a05410b011840 0x006140a821602308 0x370c07c19f018c60 0x66e180f833e0318c

def z1269 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0813f9fe781c739a 0xc1027f3fcf038e73

def z1270 : W := mkw 0x25b117bbe0000000 0x04b622f77c000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z1271 : W := mkw 0x27df759b20000000 0x04fbeeb364000000 0xe7ffffdf80000003 0xfcfffffbf0000000

def z1272 : W := mkw 0x020a8800120b2000 0x0041510002416400 0xbf1ffe23ff1fffff 0xf7e3ffc47fe3ffff

def z1273 : W := mkw 0x0864ca64ddfeffbf 0xe10c994c9bbfdff7 0xf8ec4623ffffffff 0xbf1d88c47fffffff

def z1274 : W := mkw 0x002112aae0000000 0x000422555c000000 0xa013ffffe0000003 0xd4027ffffc000000

def z1275 : W := mkw 0x069a200004900000 0x00d3440000920000 0xdff3b8001ffc0004 0xfbfe770003ff8000

def z1276 : W := mkw 0x030b9dcb3b0b38c8 0xa06173b967616719 0xb70fbfc39f039ce7 0x76e1f7f873e0739c

def z1277 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0x70ec4623e0e3fffb 0x2e1d88c47c1c7fff

def z1278 : W := mkw 0x069b308a20000000 0x00d3661144000000 0x8713f9fe60000003 0xd0e27f3fcc000000

def z1279 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x0813f9fe781e6399 0xc1027f3fcf03cc73

def z1280 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70f87e3ff039fff 0x76e1f0fc7fe073ff

def z1281 : W := mkw 0x0044c844d84ef1ba 0xe00899089b09de37 0x080c4003f81ff3fd 0x010188007f03fe7f

def z1282 : W := mkw 0x27df759be0000000 0x04fbeeb37c000000 0xc7fff9dfe0000001 0xf8ffff3bfc000000

def z1283 : W := mkw 0x16dee80016dbe030 0x42dbdd0002db7c06 0xdffff8001fffe0fd 0xfbffff0003fffc1f

def z1284 : W := mkw 0x0c9000440db41f07 0x0192000881b683e0 0xdff001fc1ffc1f06 0xfbfe003f83ff83e0

def z1285 : W := mkw 0x1ffe673007f1ce05 0x03ffcce600fe39c0 0xf7fffffc07e18c03 0xfeffffff80fc3180

def z1286 : W := mkw 0x27bb37bbe0000000 0x04f766f77c000000 0xe7f3bfffe0000002 0xfcfe77fffc000000

def z1287 : W := mkw 0x05b007700d901800 0x00b600ee01b20300 0xfff007fc1ffc1c06 0xfffe00ff83ff8380

def z1288 : W := mkw 0x030a850113030840 0x006150a022606108 0xb70f86039f039ce7 0x76e1f0c073e0739c

def z1289 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xfff007fc1fff9fe6 0xfffe00ff83fff3fc

def z1290 : W := mkw 0x236f77bbe0000000 0x046deef77c000000 0xa70fffffe0000003 0x74e1fffffc000000

def z1291 : W := mkw 0x27ff77bbe0200634 0x44ffeef77c0400c6 0xf7ffffffe0039fff 0xfefffffffc0073ff

def z1292 : W := mkw 0x030b8dc31b0b38c8 0xa06171b863616719 0xb70f87c39f03fcff 0x76e1f0f873e07f9f

def z1293 : W := mkw 0x024f708a20000000 0x0049ee1144000000 0x801ff9fe60000003 0xd003ff3fcc000000

def z1294 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x0000000000027398 0x0000000000004e73

def z1295 : W := mkw 0x2fff77bbe7b10e45 0x05ffeef77cf621c8 0xf7ffffffe7e18c63 0xfefffffffcfc318c

def z1296 : W := mkw 0x030b95cf3b0719ca 0xa06172b9e760e339 0xbf1f87ffff1f9fff 0xf7e3f0ffffe3f3ff

def z1297 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0x57fff8001fffe001 0x6affff0003fffc00

def z1298 : W := mkw 0x2fff77bbe5b00e05 0x05ffeef77cb601c0 0xffffffffe7e01f07 0xfffffffffcfc03e0

def z1299 : W := mkw 0x0b0b85d71b0719c3 0x816170bae360e338 0xb70f87df9f039ce7 0x76e1f0fbf3e0739c

def z1300 : W := mkw 0x169aa800169b2000 0x02d3550002d36400 0x4ff3b8001ffc0000 0xc9fe770003ff8000

def z1301 : W := mkw 0x37df759b26d1c000 0x06fbeeb364da3800 0x57ffb9dc07e18000 0x6afff73b80fc3000

def z1302 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xf8fc47ffe0e3ffff 0xff1f88fffc1c7fff

def z1303 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xe7f3fffc60000002 0xfcfe7fff8c000000

def z1304 : W := mkw 0x000198cf380e31ca 0xa0003319e701c639 0x8813f9fff81e73ff 0xd1027f3fff03ce7f

def z1305 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xb71fffffff1f9ce7 0xf6e3ffffffe3f39c

def z1306 : W := mkw 0x27ff77bbe040c030 0x44ffeef77c081806 0xf7ffffffe003fcff 0xfefffffffc007f9f

def z1307 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xb70f87c19f019c66 0x76e1f0f833e0338c

def z1308 : W := mkw 0x030b8583130308c0 0x806170b062606118 0xb70f86039f038ce5 0x76e1f0c073e0719c

def z1309 : W := mkw 0x0db007740db41f37 0x41b600ee81b683e6 0xfff007fc1ffc1ffe 0xfffe00ff83ff83ff

def z1310 : W := mkw 0x020b108b20000000 0x0041621164000000 0x801ff9ffe0000003 0xd003ff3ffc000000

def z1311 : W := mkw 0x3fff77bbe7f1ce05 0x07ffeef77cfe39c0 0xf7ffffffe7e18c03 0xfefffffffcfc3180

def z1312 : W := mkw 0x2fff77bbe5f0ce35 0x45ffeef77cbe19c6 0xf7ffffffe7e18c63 0xfefffffffcfc318c

def z1313 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8813f9fe60026007 0xd1027f3fcc004c00

def z1314 : W := mkw 0x27df759b20000000 0x04fbeeb364000000 0x071ff9dc00000001 0x40e3ff3b80000000

def z1315 : W := mkw 0x27fe7738e0000000 0x04ffcee71c000000 0xe7fffffc60000003 0xfcffffff8c000000

def z1316 : W := mkw 0x27bb37bbe0000000 0x04f766f77c000000 0x2713bfdd80000000 0x44e277fbb0000000

def z1317 : W := mkw 0x030a050103010840 0x006140a020602108 0xbf0c4623e703ffff 0xb7e188c47ce07fff

def z1318 : W := mkw 0x2001108be0000000 0x040022117c000000 0x8013f9ffe0000003 0xd0027f3ffc000000

def z1319 : W := mkw 0x27bb37bb20000000 0x04f766f764000000 0x2713bffc00000002 0x44e277ff80000000

def z1320 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0x9813f9fe781fffff 0xd3027f3fcf03ffff

def z1321 : W := mkw 0x030b158b20000000 0x006162b164000000 0x8713f9fe60000003 0xd0e27f3fcc000000

def z1322 : W := mkw 0x1cf46a34c4fce737 0x439e8d46989f9ce6 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z1323 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x00000000181e1084 0x000000000303c210

def z1324 : W := mkw 0x030b05c30b0118c0 0x806160b861602318 0xb70c07c39f019ce6 0x76e180f873e0339c

def z1325 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xd7fff8001ffd8001 0xfaffff0003ffb000

def z1326 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0xb70fffffff03ffff 0x76e1ffffffe07fff

def z1327 : W := mkw 0x324ff88bf24be088 0xa649ff117e497c11 0x000ff803e003e099 0x0001ff007c007c13

def z1328 : W := mkw 0x030a8501130308c0 0x806150a022606118 0x370c060187038ce0 0x26e180c030e0719c

def z1329 : W := mkw 0x2f9b359b25900801 0x05f366b364b20100 0x0713b9dc07000000 0x40e2773b80e00000

def z1330 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013f9dc00000001 0xd0027f3b80000000

def z1331 : W := mkw 0x27ff77bbe4900000 0x04ffeef77c920000 0xe7ffffffff1c0003 0xfcffffffffe38000

def z1332 : W := mkw 0x0cf44230c4f0c635 0x419e8846189e18c6 0x48e0402060e06318 0x891c08040c1c0c63

def z1333 : W := mkw 0x00008844180e318a 0xa00011088301c631 0x18000000181ffffc 0x030000000303ffff

def z1334 : W := mkw 0x27ff77bbe060c604 0x04ffeef77c0c18c0 0xffffffffe0e3ff07 0xfffffffffc1c7fe0

def z1335 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xffffffffe0e1ef7b 0xfffffffffc1c3def

def z1336 : W := mkw 0x030b9dcb3b0b38c8 0xa06173b967616719 0xbf1fffc3ff1ffcff 0xf7e3fff87fe3ff9f

def z1337 : W := mkw 0x05b0073000000000 0x00b600e600000000 0xe7f3fffc00000003 0xfcfe7fff80000000

def z1338 : W := mkw 0x279b359b20000000 0x04f366b364000000 0x8f13f9fe6002739f 0xd1e27f3fcc004e73

def z1339 : W := mkw 0x00644220c060c634 0x400c8844180c18c6 0xffec4623ffe3ffff 0xfffd88c47ffc7fff

def z1340 : W := mkw 0x0001108a20000000 0x0000221144000000 0x8013f9fe6002609b 0xd0027f3fcc004c13

def z1341 : W := mkw 0x0591159a20000000 0x00b222b344000000 0x8713f9fe60000003 0xd0e27f3fcc000000

def z1342 : W := mkw 0x27ff77bbe0200634 0x44ffeef77c0400c6 0xefffffffe0027fff 0xfdfffffffc004fff

def z1343 : W := mkw 0x04f44220c4f0c634 0x409e8844189e18c6 0x48f0402060fc6318 0x891e08040c1f8c63

def z1344 : W := mkw 0x030b058303010840 0x006160b060602108 0x370f860387018c61 0x26e1f0c070e0318c

def z1345 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xf7ffffffe0038007 0xfefffffffc007000

def z1346 : W := mkw 0x37ff77bbe6910000 0x06ffeef77cd22000 0xe7ffffffe7000003 0xfcfffffffce00000

def z1347 : W := mkw 0x0db0073404b40707 0x01b600e6809680e0 0xfff007fc1ffc0306 0xfffe00ff83ff8060

def z1348 : W := mkw 0x030b9dcf3b0f39ca 0xa06173b9e761e739 0x371fbfdd9f1d8c60 0x66e3f7fbb3e3b18c

def z1349 : W := mkw 0x27ff77bbe060c634 0x44ffeef77c0c18c6 0xffffffffe0e19f67 0xfffffffffc1c33ec

def z1350 : W := mkw 0x27ff77bbe4900000 0x04ffeef77c920000 0xf7ffffffe7e00003 0xfefffffffcfc0000

def z1351 : W := mkw 0x2101159b20000000 0x042022b364000000 0x8013f9fe60000003 0xd0027f3fcc000000

def z1352 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdff3f8001ffc6004 0xfbfe7f0003ff8c00

def z1353 : W := mkw 0x07ff67b300000000 0x00ffecf660000000 0xe7ffffff80000003 0xfcfffffff0000000

def z1354 : W := mkw 0x14f46a20c4f8e634 0x429e8d44189f1cc6 0x48f0780000fc6000 0x891e0f00001f8c00

def z1355 : W := mkw 0x27ff77bbe361ce74 0x44ffeef77c6c39ce 0xf7ffffffe7e18c63 0xfefffffffcfc318c

def z1356 : W := mkw 0x06df708a20000000 0x00dbee1144000000 0xc7fff9dc00000001 0xf8ffff3b80000000

def z1357 : W := mkw 0x100088441cdef18a 0xa2001108839bde31 0x0800000018fe739c 0x01000000031fce73

def z1358 : W := mkw 0x020a000002010000 0x0041400000402000 0x370c060187018c60 0x26e180c030e0318c

def z1359 : W := mkw 0x16dee80016dbe000 0x02dbdd0002db7c00 0xdfffb8001ffd8004 0xfbfff70003ffb000

def z1360 : W := mkw 0x030b85c31b0318c0 0x806170b863606318 0xbf0f87e39f039fe7 0xf7e1f0fc73e073fc

def z1361 : W := mkw 0x0db08f741dbe3f8f 0xa1b611ee83b7c7f1 0x7fe006001ffe7f9c 0x2ffc00c003ffcff3

def z1362 : W := mkw 0x14f47a2ce4fce73e 0x629e8f459c9f9ce7 0x48f0783c60fc6318 0x891e0f078c1f8c63

def z1363 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xf7ffffffff000007 0xfeffffffffe00000

def z1364 : W := mkw 0x0100054409041902 0x002000a881208320 0xbf1c47ffff1fffff 0xf7e388ffffe3ffff

def z1365 : W := mkw 0x06de600000000000 0x00dbcc0000000000 0xc7fff9fc00000003 0xf8ffff3f80000000

def z1366 : W := mkw 0x27bb37bb20000000 0x04f766f764000000 0xe7ffbfff80000003 0xfcfff7fff0000000

def z1367 : W := mkw 0x236f77bbe060c634 0x446deef77c0c18c6 0x200fffffe003fffb 0x0401fffffc007fff

def z1368 : W := mkw 0x27ff77bbe4900000 0x04ffeef77c920000 0xefffffffe0fc0003 0xfdfffffffc1f8000

def z1369 : W := mkw 0x000198ce380e318a 0xa0003319c701c631 0xb813fffe781e7f9f 0xf7027fffcf03cff3

def z1370 : W := mkw 0x0064ca64d86ef7be 0xe00c994c9b0ddef7 0x78ec060198fffffc 0x2f1d80c0331fffff

def z1371 : W := mkw 0x05b007740c941102 0x00b600ee81928220 0xfff007fc1ffc1306 0xfffe00ff83ff8260

def z1372 : W := mkw 0x0db007740db41f07 0x01b600ee81b683e0 0xdff001fc1ffc0304 0xfbfe003f83ff8060

def z1373 : W := mkw 0x279b359b24900000 0x04f366b364920000 0xdff3b9dc1ffc0004 0xfbfe773b83ff8000

def z1374 : W := mkw 0x000198ce390e39ca 0xa0003319c721c739 0x8813f9fe781e7fff 0xd1027f3fcf03cfff

def z1375 : W := mkw 0x0001108a20000000 0x0000221144000000 0x0013f9de60000001 0x40027f3bcc000000

def z1376 : W := mkw 0x06dee800149a2000 0x00dbdd0002934400 0xdffff8001ffe6005 0xfbffff0003ffcc00

def z1377 : W := mkw 0x079a251000000000 0x00f344a200000000 0x0713b9dc00000000 0x40e2773b80000000

def z1378 : W := mkw 0x14f5faeefcfef7be 0xe29ebf5ddf9fdef7 0xc8f3f9fe78fe739f 0xd91e7f3fcf1fce73

def z1379 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xefffffffe0026007 0xfdfffffffc004c00

def z1380 : W := mkw 0x27ff77bbe0000000 0x04ffeef77c000000 0xeffffffff81c0007 0xfdffffffff038000

def z1381 : W := mkw 0x0cf5dafefcfef7bf 0xe19ebb5fdf9fdef7 0xc8f3f9fe78fe739f 0xd91e7f3fcf1fce73

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z8,z2,z3,z4,z5]),(0,[z9,z10,z0,z1,z2,z3,z4]),(0,[z0,z11,z1,z2,z3,z4,z12]),(1,[z0,z1,z13,z3,z4,z5]),(0,[z0,z1,z13,z2,z3,z4,z5]),(0,[z0,z14,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z15,z5])],[(0,[z0,z1,z16,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z18]),(0,[z0,z1,z2,z3,z19,z4,z5]),(0,[z0,z1,z2,z20,z3,z4,z21])],[(1,[z0,z1,z2,z3,z4,z22]),(0,[z23,z9,z0,z1,z2,z3,z4]),(0,[z0,z1,z24,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z25,z4,z5]),(0,[z0,z1,z2,z20,z3,z26,z5])],[(0,[z27,z0,z1,z2,z3,z4,z28]),(1,[z29,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z4,z30,z21]),(0,[z0,z1,z2,z3,z31,z32,z5]),(0,[z0,z1,z2,z3,z33,z4,z5])],[(1,[z34,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z35,z3,z4]),(0,[z0,z1,z2,z3,z36,z4,z5])],[(0,[z0,z1,z37,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z28]),(0,[z0,z1,z2,z3,z4,z5,z38]),(0,[z0,z1,z2,z3,z4,z26,z21])],[(0,[z0,z1,z39,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z4,z5]),(0,[z0,z1,z2,z3,z4,z21,z41]),(0,[z42,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z43])],[(0,[z44,z1,z2,z3,z45,z4,z5])],[],[(0,[z0,z1,z46,z3,z4,z47,z5]),(0,[z0,z48,z1,z2,z49,z4,z5])],[(0,[z0,z8,z1,z2,z3,z4,z22]),(0,[z0,z1,z46,z2,z3,z4,z5]),(0,[z50,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z51,z4,z5]),(1,[z0,z1,z2,z3,z4,z52])],[(0,[z27,z1,z53,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z21,z54])],[(0,[z44,z0,z1,z17,z3,z4,z5]),(0,[z55,z9,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z56,z4,z12]),(0,[z0,z1,z2,z3,z4,z57,z5]),(0,[z58,z9,z0,z1,z2,z3,z4]),(0,[z0,z48,z1,z2,z3,z4,z5])],[(0,[z59,z0,z1,z2,z3,z4,z60]),(0,[z61,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z62,z3,z4,z5]),(0,[z63,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z64,z5]),(0,[z29,z0,z1,z2,z3,z65,z4]),(0,[z0,z66,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z67,z4,z5])],[(0,[z0,z68,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z69,z4,z5]),(1,[z0,z1,z70,z3,z4,z5])]],
   [[(0,[z55,z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z71,z5]),(0,[z0,z1,z2,z72,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z73])],[(0,[z27,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z46,z74,z3,z4,z5]),(0,[z0,z1,z46,z2,z3,z4,z75])],[],[(1,[z0,z1,z2,z3,z76,z5]),(1,[z0,z1,z46,z3,z4,z5]),(0,[z77,z0,z1,z46,z3,z4,z5]),(0,[z78,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z79,z4,z5])],[(0,[z0,z1,z46,z2,z3,z4,z80]),(1,[z81,z1,z2,z3,z56,z5]),(0,[z82,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z83,z4,z5])],[(0,[z0,z1,z2,z84,z3,z45,z5]),(0,[z0,z1,z85,z2,z3,z4,z5])],[(0,[z9,z0,z1,z2,z86,z3,z4]),(0,[z0,z1,z2,z3,z4,z87,z5]),(0,[z0,z1,z2,z88,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z89,z5]),(0,[z29,z0,z1,z2,z3,z4,z54]),(0,[z50,z29,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z90,z3,z4]),(1,[z0,z1,z2,z3,z4,z91]),(0,[z0,z1,z2,z3,z4,z21,z92]),(0,[z0,z1,z2,z3,z4,z5,z93])],[(0,[z0,z1,z2,z3,z4,z94,z5]),(0,[z0,z95,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z96,z3,z4,z5]),(0,[z0,z97,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z98,z4,z5,z99])],[(0,[z0,z1,z2,z3,z100,z4,z5]),(0,[z0,z1,z46,z101,z3,z4,z5]),(1,[z0,z1,z46,z3,z4,z75]),(0,[z0,z2,z3,z4,z12,z5,z21]),(0,[z0,z1,z102,z103,z3,z4,z5])],[(1,[z0,z1,z104,z3,z4,z5]),(0,[z0,z8,z1,z46,z3,z4,z5]),(0,[z0,z1,z105,z2,z3,z4,z21])],[(0,[z9,z0,z106,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z32,z12]),(0,[z0,z1,z2,z90,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z107,z5])],[(0,[z0,z1,z2,z3,z108,z4,z5]),(1,[z0,z1,z46,z3,z4,z80]),(0,[z0,z1,z2,z109,z3,z4,z5])],[(0,[z0,z1,z17,z90,z3,z4,z5]),(1,[z29,z0,z1,z110,z3,z4]),(0,[z59,z0,z1,z102,z3,z4,z5])],[(0,[z7,z0,z53,z2,z3,z4,z5]),(0,[z23,z0,z1,z2,z3,z4,z12])]],
   [[(0,[z59,z0,z1,z17,z3,z4,z5]),(0,[z29,z0,z1,z2,z111,z3,z4])],[(0,[z0,z1,z2,z112,z4,z64,z5]),(0,[z0,z1,z2,z20,z3,z51,z5])],[(0,[z0,z1,z2,z3,z4,z113,z5]),(0,[z0,z1,z2,z110,z3,z4,z5]),(0,[z0,z114,z1,z2,z3,z4,z5])],[(0,[z27,z0,z8,z2,z3,z4,z5]),(0,[z0,z1,z53,z2,z3,z4,z12]),(0,[z115,z0,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z4,z92]),(0,[z116,z0,z1,z2,z3,z4,z5]),(0,[z117,z0,z1,z2,z3,z4,z5])],[],[(0,[z118,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z103,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z119,z5]),(0,[z0,z1,z2,z90,z120,z3,z5]),(0,[z0,z1,z2,z120,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z121]),(0,[z0,z1,z2,z3,z4,z21,z18]),(0,[z0,z1,z2,z3,z4,z47,z12]),(0,[z0,z1,z2,z3,z4,z122,z5])],[(1,[z9,z0,z1,z46,z3,z4]),(0,[z0,z1,z2,z3,z123,z4,z5])],[(0,[z0,z1,z17,z3,z4,z47,z5]),(0,[z0,z1,z2,z3,z4,z5,z124]),(1,[z125,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z5])],[(0,[z58,z0,z1,z46,z3,z4,z5]),(0,[z29,z0,z1,z2,z101,z3,z4]),(0,[z0,z1,z2,z3,z4,z127,z21])],[],[(0,[z0,z1,z128,z17,z3,z4,z5]),(0,[z0,z1,z2,z129,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z130,z4,z5]),(0,[z59,z0,z2,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z131]),(0,[z132,z0,z1,z2,z3,z4,z5]),(0,[z0,z133,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z45,z49,z4,z5]),(0,[z9,z0,z1,z2,z134,z3,z4]),(0,[z0,z1,z2,z74,z3,z4,z12]),(0,[z0,z1,z2,z3,z135,z4,z5]),(1,[z0,z1,z2,z3,z5,z136])],[(0,[z63,z0,z1,z137,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z30]),(0,[z0,z1,z2,z90,z3,z138,z5])]],
   [[(0,[z0,z1,z17,z74,z3,z4,z5]),(0,[z0,z1,z139,z17,z3,z4,z5]),(0,[z0,z1,z2,z140,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z99])],[(0,[z0,z97,z1,z2,z3,z141,z5])],[(0,[z0,z1,z46,z3,z142,z4,z5]),(0,[z0,z1,z2,z3,z4,z143,z5]),(0,[z118,z29,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z144,z4]),(0,[z145,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z134,z3,z4,z92]),(0,[z0,z1,z2,z146,z3,z4,z5])],[(0,[z9,z0,z1,z17,z3,z4,z5])],[(0,[z0,z1,z17,z3,z147,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z148]),(0,[z81,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z149,z5]),(1,[z150,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z151,z4,z5])],[(1,[z152,z0,z1,z17,z3,z4]),(0,[z153,z9,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z154,z3,z4,z5])],[(0,[z0,z1,z2,z35,z3,z4,z64]),(0,[z29,z0,z155,z1,z2,z3,z4]),(0,[z0,z1,z105,z3,z4,z156,z5])],[(0,[z0,z1,z2,z101,z3,z4,z12])],[(1,[z7,z8,z2,z3,z4,z5]),(0,[z29,z0,z8,z1,z2,z3,z4]),(0,[z0,z1,z2,z157,z3,z4,z5]),(0,[z0,z1,z2,z84,z3,z4,z5]),(1,[z63,z1,z2,z3,z64,z5]),(0,[z0,z158,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z159,z5])],[(0,[z0,z1,z17,z101,z3,z4,z5]),(1,[z9,z0,z1,z2,z3,z4]),(0,[z9,z1,z2,z3,z4,z5,z54])],[(0,[z0,z1,z2,z160,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z161,z5])],[(0,[z1,z53,z2,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z162,z5]),(1,[z163,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z74,z101,z4,z5]),(0,[z0,z1,z2,z164,z49,z4,z5]),(0,[z0,z1,z2,z165,z3,z4,z5]),(0,[z0,z1,z166,z2,z3,z4,z5]),(0,[z58,z0,z1,z2,z3,z4,z47])],[(0,[z167,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z168,z5])],[(0,[z0,z1,z2,z169,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z65,z4]),(0,[z9,z0,z1,z2,z3,z31,z4]),(0,[z0,z1,z2,z3,z170,z4,z5])]],
   [[(0,[z171,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z172,z4]),(0,[z0,z1,z2,z3,z4,z173,z5])],[(0,[z174,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z175,z2,z3,z4,z5])],[(0,[z0,z176,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z51,z64,z5]),(0,[z0,z1,z2,z3,z177,z4,z5]),(0,[z0,z1,z2,z3,z4,z178,z5])],[(1,[z0,z1,z179,z2,z3,z4]),(0,[z0,z1,z2,z180,z3,z4,z5]),(0,[z0,z1,z181,z2,z3,z4,z5])],[(0,[z0,z182,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z183,z5])],[(0,[z29,z0,z1,z2,z3,z4,z168]),(0,[z0,z1,z184,z2,z3,z4,z5])],[(0,[z7,z0,z1,z2,z3,z4,z5]),(1,[z1,z17,z3,z4,z30,z5]),(0,[z0,z1,z185,z2,z3,z4,z21]),(0,[z0,z1,z186,z2,z3,z4,z5])],[(1,[z0,z1,z96,z3,z4,z5]),(0,[z187,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z188,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z90,z3,z4]),(0,[z9,z0,z1,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z4,z5,z21])],[(0,[z59,z189,z1,z2,z3,z4,z5]),(0,[z190,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z191,z4,z5])],[(0,[z0,z1,z2,z192,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z193,z4]),(0,[z0,z1,z2,z194,z3,z4,z5])],[(0,[z0,z1,z2,z195,z3,z4,z5]),(0,[z0,z1,z1,z2,z3,z4,z12])],[(0,[z0,z1,z196,z2,z3,z4,z5])],[(0,[z29,z0,z1,z2,z17,z3,z4]),(0,[z0,z97,z1,z2,z3,z4,z21])],[],[(0,[z197,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z3,z198,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z199]),(0,[z0,z97,z1,z2,z74,z4,z5]),(0,[z0,z1,z2,z3,z142,z4,z12]),(0,[z0,z1,z2,z3,z4,z5,z200]),(0,[z0,z1,z2,z146,z3,z5,z92])]],
   [[(0,[z27,z0,z1,z2,z3,z4,z201]),(0,[z202,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z203,z3,z4,z26])],[(0,[z0,z1,z17,z3,z56,z4,z5]),(0,[z0,z1,z17,z3,z142,z4,z5]),(0,[z204,z9,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z31,z4]),(1,[z0,z1,z110,z3,z4,z5]),(0,[z59,z0,z1,z86,z3,z4,z5]),(0,[z0,z205,z1,z2,z3,z4,z5])],[(0,[z0,z1,z46,z20,z3,z4,z5]),(0,[z206,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z5,z136,z92])],[(0,[z27,z0,z1,z2,z3,z4,z12]),(0,[z207,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z92]),(0,[z29,z0,z97,z1,z2,z3,z4]),(0,[z208,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z209,z3,z4,z5]),(0,[z0,z1,z46,z210,z3,z4,z5]),(1,[z0,z1,z2,z3,z211,z5]),(0,[z0,z1,z2,z3,z4,z21,z99]),(0,[z0,z1,z2,z134,z3,z4,z168])],[(0,[z0,z106,z1,z17,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z26,z5]),(0,[z0,z1,z2,z212,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z12]),(0,[z0,z213,z1,z2,z3,z4,z5])],[(0,[z0,z214,z1,z2,z3,z4,z5]),(1,[z0,z1,z215,z3,z4,z5])],[(0,[z0,z1,z2,z216,z3,z4,z5])],[(0,[z0,z11,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z31,z4,z21]),(0,[z0,z1,z2,z3,z4,z217,z12]),(0,[z0,z1,z218,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z92,z99])],[(0,[z9,z0,z1,z2,z101,z3,z4])],[(0,[z9,z0,z1,z102,z2,z3,z4]),(0,[z0,z1,z24,z2,z3,z4,z5]),(0,[z0,z219,z1,z2,z3,z4,z5])],[(0,[z220,z0,z1,z2,z3,z4,z5])],[(1,[z1,z46,z17,z3,z4,z5]),(0,[z0,z221,z1,z2,z222,z4,z5]),(0,[z0,z1,z2,z223,z3,z4,z5]),(0,[z0,z1,z224,z2,z3,z4,z5])],[(0,[z0,z8,z1,z2,z3,z4,z12])],[(0,[z0,z1,z225,z2,z3,z4,z5]),(0,[z226,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z46,z3,z4,z5,z227]),(0,[z228,z0,z1,z2,z3,z4,z5]),(1,[z23,z0,z2,z3,z4,z12])],[(0,[z0,z1,z17,z3,z4,z32,z5]),(0,[z29,z0,z1,z2,z3,z4,z99]),(0,[z0,z1,z229,z2,z3,z4,z5])],[(0,[z0,z1,z2,z222,z3,z4,z5])],[(0,[z0,z1,z2,z230,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z231])],[(0,[z0,z232,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z233,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z234])],[],[(0,[z63,z0,z1,z2,z3,z4,z5])],[(0,[z235,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z212,z3,z45,z4]),(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z236,z3,z4,z5])],[(0,[z9,z0,z8,z1,z2,z3,z4]),(0,[z237,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z210,z17,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z238]),(0,[z0,z1,z103,z2,z3,z4,z21]),(0,[z239,z0,z1,z2,z3,z4,z5])],[(0,[z7,z1,z2,z17,z3,z4,z5]),(0,[z0,z1,z2,z215,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z240,z5]),(0,[z29,z0,z1,z2,z3,z4,z241]),(0,[z0,z1,z242,z2,z3,z4,z5]),(0,[z0,z1,z3,z31,z4,z156,z5])],[(0,[z0,z1,z2,z3,z4,z243,z5]),(0,[z10,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z244,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z141,z5]),(0,[z58,z0,z1,z2,z3,z4,z12])],[(0,[z163,z0,z1,z2,z3,z4,z21]),(0,[z245,z0,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z102,z2,z3,z4]),(0,[z0,z1,z2,z49,z65,z4,z5])],[(0,[z0,z1,z2,z3,z246,z4,z5]),(0,[z0,z1,z247,z2,z3,z4,z5])],[(0,[z189,z0,z1,z2,z3,z4,z5]),(0,[z248,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z249]),(0,[z0,z1,z2,z3,z250,z4,z5]),(0,[z0,z1,z2,z3,z4,z251,z21]),(0,[z0,z1,z2,z20,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z252,z5]),(0,[z0,z1,z253,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z254])]],
   [[(0,[z0,z1,z2,z3,z4,z255,z5]),(0,[z0,z1,z2,z3,z193,z4,z5]),(0,[z0,z1,z2,z256,z3,z4,z5])],[(0,[z0,z1,z17,z20,z3,z4,z5]),(0,[z0,z257,z1,z2,z3,z4,z5]),(0,[z0,z1,z258,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z259,z5]),(0,[z0,z1,z2,z260,z3,z4,z12])],[(0,[z9,z0,z1,z261,z2,z3,z4]),(1,[z0,z1,z2,z3,z262,z5]),(0,[z263,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z26,z12]),(0,[z0,z1,z2,z264,z3,z4,z5])],[(0,[z0,z1,z2,z3,z265,z4,z5]),(0,[z0,z1,z2,z266,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z267,z5]),(0,[z268,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z17,z3,z4,z26,z5]),(1,[z0,z1,z2,z269,z3,z5]),(0,[z63,z81,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z90,z3,z4,z5])],[(0,[z0,z270,z1,z17,z3,z4,z5]),(0,[z271,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z272]),(0,[z0,z1,z2,z273,z4,z168,z5]),(0,[z0,z1,z2,z3,z142,z4,z159])],[(0,[z0,z1,z2,z274,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z168]),(0,[z0,z1,z275,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z91]),(0,[z0,z106,z1,z2,z3,z32,z5]),(1,[z0,z1,z2,z98,z4,z5])],[(0,[z0,z1,z2,z3,z276,z4,z5]),(0,[z277,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z278,z2,z3,z31,z5]),(0,[z0,z1,z2,z3,z4,z279,z5])],[(0,[z0,z1,z2,z3,z280,z4,z5]),(0,[z29,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z31,z51,z5])],[(1,[z0,z1,z195,z3,z4,z5]),(0,[z0,z1,z2,z3,z281,z4,z5])],[(0,[z0,z1,z2,z17,z3,z4,z21]),(0,[z0,z1,z282,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z283,z5])],[(0,[z0,z1,z53,z2,z3,z4,z5]),(1,[z0,z221,z2,z3,z51,z5]),(0,[z0,z1,z102,z2,z164,z4,z5])],[],[(0,[z0,z1,z284,z53,z2,z3,z4]),(0,[z9,z0,z1,z2,z17,z3,z4]),(0,[z29,z0,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z285]),(0,[z286,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z278,z3,z31,z4,z5]),(0,[z0,z1,z2,z3,z4,z47,z5])]],
   [[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z287,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z288]),(0,[z0,z1,z2,z120,z3,z5,z99])],[(0,[z0,z1,z289,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z290,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z54])],[(0,[z55,z0,z1,z17,z3,z4,z5]),(0,[z0,z0,z1,z46,z3,z4,z5]),(0,[z0,z291,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z292,z12])],[(0,[z44,z0,z1,z2,z3,z4,z21])],[(0,[z29,z0,z1,z2,z3,z4,z26])],[(0,[z293,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z53,z2,z3,z4,z5]),(0,[z294,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z97,z1,z2,z3,z4]),(0,[z0,z1,z2,z295,z3,z4,z5])],[(0,[z59,z0,z1,z296,z3,z4,z5]),(0,[z0,z2,z74,z3,z49,z4,z5]),(0,[z0,z1,z2,z297,z3,z4,z5])],[(0,[z0,z1,z2,z298,z3,z4,z5]),(0,[z0,z1,z2,z74,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z299])],[(0,[z1,z2,z17,z3,z4,z30,z5]),(0,[z0,z1,z2,z134,z3,z4,z21])],[(0,[z0,z1,z105,z46,z3,z4,z5]),(0,[z0,z300,z1,z2,z3,z4,z5])],[(0,[z301,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z302,z5]),(0,[z29,z0,z48,z1,z2,z3,z4]),(0,[z0,z106,z1,z2,z3,z4,z21])],[(0,[z0,z1,z303,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z147,z4,z5]),(0,[z0,z1,z2,z3,z304,z4,z5]),(0,[z0,z1,z2,z137,z3,z4,z5])],[(0,[z55,z163,z1,z2,z3,z4,z5]),(0,[z10,z0,z1,z305,z3,z4,z5]),(0,[z29,z81,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z306,z5]),(0,[z58,z0,z1,z2,z3,z4,z227]),(0,[z0,z1,z2,z307,z3,z4,z5])],[(0,[z81,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z308,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z92])],[(0,[z0,z1,z2,z273,z3,z4,z92])],[(0,[z0,z1,z2,z3,z309,z4,z5]),(0,[z0,z1,z296,z17,z3,z4,z5]),(1,[z0,z1,z2,z84,z3,z5])]],
   [[(0,[z0,z1,z2,z101,z3,z4,z5]),(0,[z0,z310,z1,z2,z3,z4,z5])],[(0,[z29,z7,z0,z1,z2,z3,z4]),(0,[z0,z221,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z311])],[(0,[z0,z1,z2,z3,z312,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z99]),(0,[z29,z0,z1,z296,z2,z3,z4])],[(0,[z29,z0,z1,z2,z3,z4,z156]),(0,[z0,z1,z313,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z314,z4,z5])],[(1,[z0,z1,z2,z3,z4,z201]),(0,[z0,z1,z102,z17,z3,z4,z5]),(0,[z0,z1,z103,z46,z3,z4,z5]),(0,[z0,z315,z1,z2,z3,z4,z5])],[(1,[z9,z0,z1,z17,z3,z4]),(0,[z0,z1,z316,z2,z3,z4,z5])],[(0,[z0,z1,z46,z3,z4,z30,z5]),(0,[z0,z125,z1,z2,z3,z4,z5]),(0,[z59,z0,z1,z2,z3,z4,z21])],[(0,[z163,z0,z1,z46,z3,z4,z5]),(0,[z317,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z318,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z319]),(0,[z0,z1,z2,z3,z4,z320,z5])],[(0,[z0,z1,z2,z3,z4,z321,z5])],[(0,[z322,z0,z1,z2,z3,z4,z5]),(0,[z59,z0,z1,z2,z323,z4,z5]),(0,[z0,z1,z2,z324,z3,z4,z5])],[(0,[z325,z0,z1,z2,z3,z4,z5]),(0,[z326,z0,z1,z2,z3,z4,z5])],[(0,[z327,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z328])],[(0,[z329,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z330,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z331]),(0,[z0,z1,z210,z2,z3,z4,z21])],[(0,[z34,z7,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z332,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z5,z75]),(0,[z333,z0,z1,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z159,z5,z99])],[(0,[z0,z1,z284,z2,z3,z4,z5]),(0,[z0,z1,z278,z17,z3,z4,z5]),(0,[z0,z1,z334,z46,z3,z4,z5])],[(0,[z0,z1,z2,z74,z65,z4,z5])],[(0,[z0,z1,z2,z335,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z5,z22]),(1,[z55,z1,z46,z3,z4,z5]),(0,[z336,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z337,z5])],[(0,[z0,z1,z2,z3,z198,z4,z5])],[],[(0,[z0,z1,z2,z3,z56,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z338]),(0,[z0,z1,z2,z339,z3,z4,z5]),(0,[z0,z1,z2,z3,z142,z4,z5]),(0,[z0,z1,z2,z3,z4,z340,z5])],[],[(1,[z0,z1,z17,z3,z4,z21]),(0,[z0,z1,z46,z3,z31,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z21])],[(0,[z59,z0,z11,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z341,z5])],[(0,[z55,z1,z46,z2,z3,z4,z5]),(0,[z0,z1,z2,z74,z45,z4,z5]),(0,[z0,z1,z2,z86,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z12,z94]),(0,[z0,z1,z2,z3,z342,z4,z5])],[(0,[z27,z0,z1,z2,z3,z4,z5])],[(0,[z27,z0,z1,z2,z343,z4,z5]),(0,[z44,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z103,z164,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z77,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z0,z1,z2,z3,z4])]],
   [[(1,[z0,z1,z2,z343,z4,z5]),(0,[z0,z1,z2,z3,z4,z21,z21]),(0,[z0,z344,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z172,z4,z64]),(0,[z0,z1,z2,z3,z4,z5,z345]),(0,[z0,z1,z2,z273,z3,z4,z168]),(0,[z0,z346,z1,z2,z3,z4,z5])],[(0,[z9,z0,z347,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z217,z5]),(0,[z0,z221,z1,z2,z3,z32,z5])],[(1,[z0,z1,z348,z3,z4,z5])],[(0,[z0,z296,z2,z86,z3,z4,z5]),(0,[z349,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z17,z350,z3,z4,z5]),(0,[z0,z1,z351,z46,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z26]),(0,[z0,z1,z2,z90,z49,z4,z5]),(0,[z0,z1,z2,z3,z4,z352,z5])],[(0,[z0,z1,z17,z3,z4,z30,z5])],[(0,[z0,z8,z1,z2,z3,z4,z5]),(0,[z63,z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z112,z4,z5])],[(0,[z0,z1,z353,z2,z3,z4,z5]),(0,[z0,z1,z2,z354,z3,z4,z5]),(1,[z0,z1,z2,z355,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z5])],[],[(0,[z27,z29,z0,z1,z2,z3,z4]),(1,[z0,z1,z137,z3,z4,z5]),(1,[z0,z1,z2,z356,z4,z5])],[(0,[z0,z97,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z101,z3,z4,z357]),(0,[z0,z358,z1,z2,z3,z4,z5]),(0,[z9,z0,z48,z1,z2,z3,z4]),(0,[z23,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z12,z359])],[(0,[z0,z1,z2,z3,z172,z4,z5]),(0,[z9,z81,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z360,z3,z4,z5])],[(0,[z0,z1,z361,z2,z3,z4,z5])],[(0,[z0,z1,z46,z3,z4,z362,z5]),(0,[z0,z1,z2,z3,z4,z363,z5])]],
   [[(0,[z27,z7,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z364,z4,z5]),(0,[z0,z365,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z366,z3,z4,z5]),(1,[z0,z1,z210,z3,z4,z227])],[(0,[z9,z7,z0,z1,z2,z3,z4]),(0,[z0,z1,z17,z3,z4,z5,z227]),(0,[z59,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z367,z2,z3,z4,z5])],[(0,[z9,z0,z1,z296,z2,z3,z4]),(0,[z0,z1,z2,z111,z3,z4,z5]),(0,[z0,z1,z296,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z368,z5])],[(0,[z10,z0,z1,z369,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z156]),(0,[z58,z0,z1,z3,z4,z47,z5])],[(0,[z370,z0,z1,z2,z3,z4,z5]),(0,[z0,z221,z1,z2,z3,z4,z21]),(0,[z58,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z20,z3,z138,z5])],[(0,[z63,z0,z1,z2,z90,z3,z5]),(0,[z271,z29,z0,z1,z2,z3,z4])],[(0,[z204,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z4,z21]),(0,[z0,z1,z2,z3,z31,z4,z12])],[(0,[z0,z1,z371,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z372]),(0,[z23,z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z373,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z374]),(0,[z0,z1,z2,z3,z375,z4,z5]),(0,[z0,z1,z2,z20,z3,z4,z5])],[(0,[z0,z1,z17,z3,z31,z4,z5])],[(0,[z29,z9,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z74,z138,z4,z5]),(0,[z0,z1,z2,z3,z4,z156,z21]),(0,[z376,z0,z1,z2,z3,z4,z5])],[(0,[z377,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z260,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z99])],[(0,[z0,z1,z46,z17,z3,z4,z5]),(0,[z317,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z105,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z26,z5])],[(0,[z0,z1,z2,z3,z4,z5,z378]),(0,[z0,z1,z2,z3,z4,z379,z21]),(0,[z0,z1,z2,z3,z4,z380,z5])],[(0,[z0,z381,z1,z2,z3,z4,z5]),(0,[z0,z48,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z382,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z383,z5])],[(1,[z1,z53,z17,z3,z4,z5]),(0,[z384,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z385]),(0,[z386,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z101,z49,z4,z5]),(1,[z0,z1,z2,z20,z138,z5])],[(0,[z387,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z388,z5]),(0,[z0,z1,z2,z3,z45,z4,z21]),(0,[z59,z0,z1,z105,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z389])],[(0,[z0,z390,z1,z46,z3,z4,z5]),(0,[z58,z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z12,z252])],[(1,[z0,z1,z2,z3,z388,z5]),(0,[z0,z1,z2,z391,z3,z4,z5])],[(0,[z44,z9,z0,z1,z2,z3,z4]),(0,[z9,z0,z1,z392,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z393,z5])],[(0,[z9,z0,z1,z46,z3,z4,z5])],[],[(1,[z0,z1,z2,z394,z4,z5]),(0,[z59,z125,z1,z2,z3,z4,z5])],[(0,[z34,z9,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z49,z138,z4,z5]),(0,[z0,z1,z2,z395,z3,z4,z5]),(0,[z0,z1,z103,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z159,z92])],[(0,[z0,z1,z46,z134,z3,z4,z5]),(0,[z10,z1,z2,z101,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z396]),(1,[z0,z1,z2,z134,z4,z92]),(0,[z0,z1,z2,z397,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z357]),(0,[z301,z29,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z20,z3,z4]),(0,[z0,z398,z1,z2,z3,z4,z5]),(1,[z0,z270,z2,z3,z4,z21]),(0,[z0,z1,z399,z2,z3,z4,z5])],[(0,[z163,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z400,z5]),(0,[z59,z0,z1,z164,z3,z4,z5]),(0,[z0,z1,z2,z401,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z292,z5])],[(0,[z384,z29,z0,z1,z2,z3,z4]),(1,[z0,z1,z278,z3,z31,z5]),(0,[z0,z1,z2,z90,z20,z4,z5]),(0,[z0,z1,z2,z3,z4,z402,z5])],[(0,[z29,z0,z1,z105,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z403,z5])],[(0,[z44,z10,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z404])],[]],
   [[(1,[z0,z1,z2,z146,z3,z5])],[(1,[z44,z1,z2,z45,z4,z5]),(0,[z29,z0,z1,z2,z3,z142,z4]),(1,[z0,z11,z296,z3,z4,z5]),(0,[z0,z1,z102,z3,z65,z4,z5]),(0,[z0,z1,z2,z90,z3,z4,z405])],[(0,[z0,z1,z406,z2,z3,z4,z5])],[(1,[z55,z9,z1,z2,z3,z4]),(0,[z63,z0,z1,z2,z3,z64,z5]),(0,[z0,z1,z2,z3,z4,z5,z407]),(0,[z408,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z21]),(0,[z0,z1,z2,z3,z409,z4,z5])],[(1,[z0,z1,z179,z17,z3,z4]),(0,[z0,z1,z2,z273,z3,z4,z21])],[(0,[z0,z1,z2,z3,z56,z4,z149]),(0,[z0,z410,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z411,z0,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z46,z3,z4,z5])],[(0,[z59,z9,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z17,z3,z4,z12]),(0,[z9,z0,z1,z2,z3,z4,z47]),(0,[z0,z412,z1,z2,z3,z4,z5])],[(0,[z0,z1,z413,z2,z3,z4,z5])],[(0,[z0,z1,z17,z17,z3,z4,z5])],[(0,[z81,z0,z1,z2,z90,z3,z5]),(0,[z0,z155,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z49,z4,z21])],[(0,[z0,z1,z2,z3,z4,z414,z5]),(1,[z29,z0,z1,z46,z3,z4]),(0,[z0,z106,z1,z2,z3,z51,z5]),(0,[z0,z270,z1,z2,z3,z4,z21]),(0,[z0,z1,z415,z2,z3,z4,z5])],[(0,[z44,z0,z1,z2,z90,z4,z5]),(0,[z153,z0,z1,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z12,z21])],[(0,[z0,z1,z46,z296,z3,z4,z5]),(0,[z0,z1,z416,z2,z3,z4,z5]),(0,[z0,z417,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z418]),(0,[z9,z0,z1,z2,z419,z3,z4]),(0,[z333,z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z127,z5]),(0,[z0,z1,z2,z134,z3,z142,z4])],[(0,[z44,z0,z1,z2,z3,z4,z12]),(1,[z420,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z421,z12]),(0,[z0,z1,z2,z3,z4,z5,z422]),(0,[z0,z1,z2,z3,z423,z4,z5])],[(0,[z0,z221,z2,z3,z51,z4,z5]),(0,[z0,z1,z2,z424,z3,z4,z5])],[(0,[z29,z0,z221,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z425,z5])],[(0,[z0,z1,z2,z3,z4,z426,z5]),(0,[z29,z0,z1,z2,z273,z3,z4]),(0,[z0,z1,z2,z427,z3,z4,z5]),(0,[z0,z1,z428,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z201]),(0,[z9,z0,z1,z2,z3,z4,z429]),(0,[z0,z347,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z93])],[(0,[z0,z1,z2,z3,z4,z76,z5]),(0,[z0,z1,z2,z3,z4,z5,z430]),(0,[z431,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z134,z3,z4,z12])],[(0,[z0,z11,z1,z2,z3,z4,z432]),(0,[z0,z1,z2,z3,z4,z433,z21])],[(0,[z0,z1,z17,z3,z4,z434,z5]),(0,[z0,z106,z1,z46,z3,z4,z5]),(0,[z0,z221,z106,z2,z3,z4,z5])],[(0,[z55,z0,z1,z2,z3,z4,z21]),(1,[z0,z1,z2,z3,z4,z75]),(0,[z0,z11,z1,z3,z31,z4,z5])],[(1,[z0,z48,z2,z49,z4,z5])],[(0,[z9,z9,z0,z1,z2,z3,z4]),(0,[z435,z9,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z4,z47]),(0,[z0,z1,z2,z3,z4,z159,z168])],[(1,[z0,z1,z2,z3,z4,z80]),(0,[z0,z106,z1,z2,z3,z4,z91])],[(0,[z0,z1,z46,z86,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z56,z4]),(0,[z0,z1,z2,z3,z436,z4,z5]),(0,[z0,z97,z1,z2,z3,z211,z5]),(0,[z0,z1,z2,z90,z4,z168,z5]),(0,[z0,z437,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z244,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z331]),(0,[z0,z97,z1,z2,z3,z4,z12]),(1,[z0,z106,z2,z3,z32,z5]),(0,[z0,z1,z438,z2,z3,z4,z5])],[(0,[z7,z0,z1,z371,z3,z4,z5]),(1,[z29,z0,z1,z2,z3,z4])]],
   [[(1,[z0,z1,z2,z3,z4,z439]),(0,[z0,z1,z46,z2,z3,z4,z21]),(0,[z44,z0,z1,z2,z101,z4,z5]),(0,[z0,z1,z2,z3,z51,z4,z21]),(0,[z0,z1,z440,z2,z3,z4,z5])],[],[(0,[z0,z48,z1,z2,z3,z4,z21])],[(0,[z0,z1,z2,z120,z3,z4,z99])],[(1,[z384,z0,z1,z2,z3,z4]),(0,[z0,z1,z441,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z442,z4,z5]),(0,[z0,z1,z2,z3,z4,z64,z21]),(0,[z0,z48,z1,z2,z74,z4,z5])],[(0,[z0,z1,z46,z443,z3,z4,z5]),(0,[z59,z0,z1,z2,z3,z4,z12])],[(0,[z0,z1,z2,z3,z444,z4,z5]),(0,[z0,z1,z2,z3,z4,z445,z5]),(0,[z0,z1,z2,z3,z446,z4,z5])],[(0,[z55,z9,z0,z1,z2,z3,z4])],[(0,[z0,z8,z1,z2,z3,z4,z439])],[(0,[z7,z0,z1,z17,z3,z4,z5]),(0,[z81,z0,z1,z2,z3,z64,z5]),(0,[z0,z1,z2,z3,z4,z447,z5]),(1,[z9,z0,z1,z70,z3,z4])],[(0,[z0,z1,z448,z2,z3,z4,z5]),(0,[z420,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z449,z3,z4,z5])],[(0,[z10,z0,z1,z2,z90,z4,z5]),(0,[z9,z0,z1,z2,z20,z3,z4]),(0,[z29,z0,z1,z2,z3,z450,z4]),(0,[z451,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z120,z3,z142,z5])],[(0,[z0,z1,z2,z350,z3,z4,z5]),(1,[z0,z1,z452,z2,z3,z4]),(0,[z0,z1,z3,z453,z4,z32,z5]),(0,[z0,z1,z102,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z454,z4,z5])],[(0,[z0,z1,z2,z3,z388,z4,z5]),(0,[z0,z1,z2,z3,z4,z30,z5])],[(0,[z0,z1,z179,z2,z3,z4,z5]),(0,[z10,z0,z1,z46,z3,z4,z5]),(0,[z9,z0,z1,z105,z2,z3,z4]),(0,[z0,z1,z2,z3,z32,z156,z5]),(0,[z0,z1,z185,z2,z3,z4,z5])],[(0,[z29,z0,z1,z2,z3,z56,z4]),(0,[z29,z0,z1,z2,z110,z3,z4]),(0,[z0,z1,z2,z3,z4,z455,z5])]],
   [[(0,[z58,z0,z1,z210,z3,z4,z5])],[(0,[z29,z0,z1,z46,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z51,z4]),(0,[z0,z1,z2,z456,z3,z4,z5]),(0,[z0,z106,z1,z2,z3,z4,z249])],[(0,[z27,z0,z1,z2,z274,z4,z5]),(0,[z9,z0,z1,z2,z3,z142,z4]),(0,[z0,z1,z2,z457,z3,z4,z5]),(0,[z458,z0,z1,z2,z3,z4,z5])],[],[(1,[z0,z1,z2,z274,z4,z5]),(0,[z152,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z70,z3,z4,z5]),(0,[z459,z0,z1,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z404,z5])],[(0,[z0,z1,z2,z460,z3,z4,z5])],[(0,[z461,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z17,z3,z4,z12]),(0,[z0,z270,z1,z46,z3,z4,z5]),(0,[z0,z1,z46,z3,z65,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z278,z2,z3,z4,z21]),(0,[z0,z1,z2,z462,z3,z4,z5])],[(0,[z0,z11,z1,z102,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z227])],[(0,[z0,z1,z2,z86,z3,z4,z12]),(0,[z0,z1,z463,z2,z3,z4,z5])],[(0,[z0,z11,z1,z17,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z156,z5]),(0,[z0,z48,z2,z3,z49,z4,z5]),(0,[z0,z1,z2,z120,z3,z4,z21]),(1,[z0,z1,z2,z3,z4,z405]),(0,[z0,z1,z2,z90,z3,z159,z5])],[(0,[z0,z1,z17,z86,z3,z4,z5]),(0,[z9,z0,z1,z2,z392,z3,z4]),(0,[z29,z0,z1,z2,z164,z3,z4]),(0,[z0,z1,z2,z3,z4,z168,z99])],[(0,[z10,z0,z1,z2,z101,z4,z5]),(0,[z0,z1,z2,z3,z464,z4,z5]),(0,[z317,z9,z0,z1,z2,z3,z4]),(0,[z465,z9,z0,z1,z2,z3,z4])],[(0,[z55,z1,z53,z2,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z80,z5]),(0,[z0,z1,z2,z3,z51,z56,z5]),(0,[z0,z466,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z467,z3,z4,z5]),(0,[z0,z1,z468,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z357,z5]),(0,[z0,z1,z70,z2,z3,z4,z5]),(0,[z469,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z31,z4,z5]),(0,[z0,z1,z210,z2,z3,z4,z47])],[(1,[z0,z1,z470,z3,z4,z5]),(1,[z0,z1,z3,z453,z4,z5])],[(1,[z0,z1,z284,z2,z3,z4]),(0,[z59,z0,z1,z2,z3,z262,z5])],[(0,[z0,z1,z2,z3,z4,z5,z288]),(0,[z0,z1,z2,z471,z3,z4,z5])],[(0,[z55,z0,z1,z46,z3,z4,z5]),(0,[z9,z0,z221,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z472]),(0,[z0,z1,z105,z2,z3,z156,z5]),(0,[z473,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z138,z4,z168,z5])],[(0,[z9,z0,z1,z2,z273,z3,z4]),(0,[z29,z0,z1,z110,z3,z4,z5]),(0,[z0,z1,z105,z2,z3,z4,z5])],[(0,[z474,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z130,z5])],[(0,[z0,z1,z2,z475,z3,z4,z5]),(0,[z0,z221,z1,z2,z3,z51,z5])],[(0,[z63,z0,z1,z17,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z321])],[(0,[z29,z0,z1,z2,z3,z4,z12])],[(0,[z0,z1,z2,z3,z476,z4,z5]),(0,[z477,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z478,z4,z5])],[],[(0,[z0,z1,z2,z3,z479,z4,z5]),(0,[z0,z1,z46,z3,z4,z5,z54]),(0,[z0,z480,z1,z2,z3,z4,z5]),(0,[z481,z0,z1,z2,z3,z4,z5])],[(0,[z482,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z483,z5])],[(1,[z0,z1,z2,z3,z4,z149]),(0,[z0,z1,z2,z3,z4,z484,z5]),(0,[z29,z1,z2,z3,z4,z30,z5])]],
   [[],[(1,[z0,z1,z416,z3,z4,z5]),(0,[z0,z1,z2,z3,z485,z4,z5]),(0,[z0,z1,z103,z2,z3,z4,z5]),(0,[z0,z1,z2,z486,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z487,z5])],[(0,[z0,z1,z2,z3,z4,z488,z5]),(0,[z0,z1,z2,z3,z138,z4,z21])],[(0,[z0,z221,z1,z46,z3,z4,z5]),(0,[z0,z1,z13,z3,z49,z4,z5]),(0,[z0,z221,z1,z2,z3,z4,z12]),(0,[z0,z1,z489,z2,z3,z4,z5])],[(0,[z163,z0,z1,z2,z3,z4,z5]),(0,[z490,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z168,z21])],[(0,[z0,z1,z46,z273,z3,z4,z5]),(0,[z44,z0,z1,z215,z3,z4,z5]),(0,[z0,z1,z2,z3,z453,z4,z5]),(0,[z0,z1,z2,z3,z65,z4,z12]),(0,[z0,z1,z491,z2,z3,z4,z5])],[(0,[z0,z1,z492,z46,z3,z4,z5]),(0,[z63,z0,z1,z318,z3,z4,z5]),(0,[z0,z1,z2,z164,z3,z4,z21])],[(0,[z0,z1,z17,z3,z65,z4,z5]),(0,[z0,z1,z102,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z493,z5]),(0,[z0,z1,z2,z3,z4,z5,z494])],[(0,[z0,z1,z2,z164,z74,z4,z5]),(0,[z34,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z156,z12])],[(0,[z0,z1,z46,z3,z4,z5,z92]),(0,[z495,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z177,z4,z21])],[(0,[z23,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z156,z5]),(0,[z317,z0,z1,z46,z3,z4,z5]),(0,[z0,z97,z2,z74,z3,z4,z5])],[(0,[z0,z1,z17,z134,z3,z4,z5]),(0,[z0,z106,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z496,z3,z4,z12])],[(0,[z0,z1,z2,z497,z3,z4,z5]),(0,[z0,z1,z498,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z499,z4,z5]),(0,[z0,z1,z46,z3,z49,z4,z5]),(0,[z0,z1,z334,z2,z3,z4,z5]),(1,[z0,z1,z2,z222,z4,z5]),(0,[z0,z1,z2,z3,z500,z4,z5]),(1,[z0,z1,z2,z120,z3,z99])],[(0,[z0,z1,z53,z17,z3,z4,z5]),(0,[z0,z1,z2,z501,z3,z4,z5]),(0,[z9,z0,z1,z70,z2,z3,z4]),(0,[z0,z11,z1,z296,z3,z4,z5]),(0,[z502,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z21,z227]),(0,[z0,z1,z2,z3,z4,z503,z5]),(1,[z0,z1,z2,z203,z3,z4])],[(0,[z0,z1,z16,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z504,z5])]],
   [[(0,[z0,z1,z2,z3,z505,z4,z5]),(0,[z506,z9,z0,z1,z2,z3,z4])],[(0,[z0,z1,z507,z2,z3,z4,z5]),(0,[z0,z508,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z17,z3,z4,z5]),(0,[z0,z1,z46,z3,z509,z4,z5]),(0,[z9,z0,z1,z46,z2,z3,z4]),(0,[z9,z0,z1,z2,z3,z51,z4]),(0,[z0,z1,z2,z3,z4,z510,z5])],[(0,[z0,z1,z278,z46,z3,z4,z5])],[(0,[z0,z1,z39,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z511,z4,z5])],[(0,[z512,z0,z1,z2,z3,z4,z5])],[(0,[z0,z97,z1,z2,z3,z4,z331])],[(0,[z0,z1,z513,z2,z3,z4,z5]),(1,[z0,z1,z102,z65,z4,z5]),(0,[z0,z1,z2,z120,z20,z3,z5])],[],[],[(0,[z0,z1,z2,z3,z4,z421,z5]),(0,[z29,z163,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z4,z227]),(1,[z0,z1,z2,z3,z4,z514]),(1,[z59,z0,z86,z3,z4,z5]),(0,[z0,z515,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z249,z5]),(1,[z0,z1,z2,z90,z26,z5])],[(0,[z0,z516,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z439,z5]),(1,[z0,z1,z46,z3,z4,z21]),(0,[z0,z11,z1,z86,z3,z4,z5]),(0,[z0,z1,z103,z2,z65,z4,z5]),(0,[z0,z1,z2,z273,z3,z142,z4])],[(0,[z9,z0,z1,z2,z164,z3,z4])],[(0,[z0,z1,z2,z20,z138,z4,z5]),(0,[z0,z1,z2,z3,z142,z159,z5])],[(0,[z81,z0,z1,z17,z3,z4,z5]),(0,[z517,z0,z1,z2,z3,z4,z5]),(0,[z518,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z210,z2,z3,z4,z12]),(0,[z0,z1,z2,z203,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z519,z3,z4,z12])],[(0,[z0,z1,z46,z3,z51,z4,z5]),(0,[z0,z1,z351,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z12]),(0,[z29,z0,z1,z2,z3,z4,z159]),(0,[z0,z11,z1,z2,z3,z4,z510])],[(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z2,z273,z3,z4,z12]),(0,[z0,z1,z278,z105,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z520,z5]),(0,[z0,z1,z2,z3,z4,z5,z136]),(0,[z0,z1,z2,z3,z521,z4,z5])],[(0,[z0,z522,z1,z2,z3,z4,z5])],[(0,[z523,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z524,z5]),(0,[z0,z1,z2,z3,z4,z262,z5]),(0,[z0,z48,z1,z2,z3,z4,z328]),(0,[z0,z1,z2,z109,z3,z4,z21]),(0,[z0,z1,z2,z525,z3,z4,z5])],[(0,[z63,z1,z2,z3,z4,z64,z5]),(0,[z0,z97,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z526,z5])],[(0,[z163,z1,z2,z17,z3,z4,z5]),(0,[z0,z1,z2,z527,z3,z4,z5]),(0,[z528,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z90,z3,z32,z5]),(0,[z0,z270,z2,z3,z4,z5,z21])],[(0,[z27,z0,z1,z37,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z75]),(0,[z0,z1,z2,z3,z4,z5,z529])],[(0,[z0,z1,z17,z3,z4,z530,z5])],[(1,[z0,z1,z37,z3,z4,z5]),(0,[z0,z270,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z531,z5]),(0,[z58,z532,z1,z2,z3,z4,z5])],[(1,[z29,z0,z1,z17,z3,z4]),(0,[z533,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z534,z2,z3,z4,z5])],[(0,[z0,z1,z2,z269,z3,z45,z5])],[(0,[z59,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z60]),(0,[z150,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z21,z430])],[(0,[z0,z1,z2,z535,z3,z4,z5])]],
   [[(0,[z29,z0,z1,z53,z2,z3,z4])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z536,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z537,z4,z5]),(0,[z0,z1,z470,z3,z4,z32,z5])],[(1,[z29,z9,z1,z2,z3,z4]),(0,[z0,z538,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z539,z3,z4,z5]),(0,[z540,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z144,z4,z5])],[(0,[z0,z1,z46,z3,z45,z4,z5]),(0,[z81,z0,z1,z541,z3,z4,z5]),(0,[z0,z106,z2,z3,z4,z32,z5])],[(0,[z0,z1,z2,z542,z3,z4,z5])],[(1,[z0,z1,z371,z3,z4,z5]),(0,[z55,z0,z1,z2,z3,z4,z12]),(0,[z377,z0,z1,z2,z3,z4,z5]),(0,[z59,z0,z1,z2,z355,z4,z5]),(0,[z0,z1,z2,z3,z4,z543,z5]),(0,[z0,z1,z2,z4,z5,z299,z99])],[(0,[z29,z0,z1,z2,z120,z3,z4]),(0,[z0,z1,z2,z544,z3,z4,z5]),(0,[z0,z1,z3,z4,z47,z5,z227])],[(0,[z0,z1,z128,z2,z3,z4,z5]),(0,[z263,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z545,z5])],[(0,[z0,z1,z2,z394,z3,z4,z5]),(0,[z0,z1,z348,z2,z3,z4,z5]),(0,[z0,z1,z2,z546,z3,z4,z5]),(0,[z0,z1,z2,z547,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z548,z5])],[(0,[z0,z1,z2,z90,z3,z4,z21])],[(0,[z0,z1,z46,z120,z3,z4,z5]),(0,[z0,z1,z261,z2,z3,z4,z5])],[(0,[z549,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z90,z74,z4,z5]),(0,[z0,z1,z470,z2,z3,z4,z5]),(0,[z0,z1,z550,z2,z3,z4,z5]),(0,[z0,z1,z2,z551,z3,z4,z5]),(0,[z0,z1,z552,z2,z3,z4,z5])],[(0,[z0,z1,z139,z2,z3,z4,z5]),(0,[z0,z1,z46,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z51,z4,z12]),(0,[z0,z1,z2,z20,z3,z159,z5])],[(0,[z27,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z323,z3,z4,z5]),(0,[z0,z1,z2,z3,z553,z4,z5]),(0,[z0,z1,z210,z2,z3,z4,z227]),(0,[z0,z1,z2,z554,z3,z4,z5])]],
   [[(0,[z0,z48,z1,z46,z3,z4,z5]),(0,[z0,z48,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z555,z4,z5]),(0,[z0,z1,z556,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z557,z5])],[(0,[z558,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z159,z21])],[(0,[z0,z1,z2,z101,z3,z4,z148]),(0,[z29,z0,z1,z2,z3,z138,z4])],[],[(0,[z0,z1,z2,z467,z3,z45,z4]),(0,[z0,z1,z296,z2,z3,z4,z12])],[],[],[(0,[z0,z1,z46,z3,z4,z12,z5]),(0,[z0,z1,z46,z3,z4,z5,z99]),(0,[z29,z0,z1,z2,z3,z4,z64]),(1,[z9,z0,z1,z392,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z559]),(0,[z0,z1,z2,z134,z120,z3,z4]),(0,[z0,z1,z560,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z362,z5]),(0,[z0,z1,z561,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z562,z5])],[(0,[z0,z8,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z251,z5])],[(0,[z0,z1,z2,z563,z3,z4,z5]),(0,[z0,z1,z102,z2,z3,z4,z12])],[(0,[z9,z163,z0,z1,z2,z3,z4]),(0,[z9,z0,z1,z2,z3,z4,z227]),(0,[z0,z1,z2,z564,z3,z4,z5]),(0,[z0,z1,z105,z2,z3,z31,z5])],[(1,[z0,z97,z2,z74,z4,z5])],[(0,[z317,z0,z1,z2,z3,z4,z12])],[(1,[z0,z1,z318,z3,z4,z5]),(0,[z0,z565,z1,z2,z3,z4,z5])],[]],
   [[(0,[z7,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z269,z3,z4,z5]),(1,[z0,z1,z2,z4,z5,z299])],[(0,[z0,z176,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z45,z4,z12]),(0,[z9,z0,z1,z2,z3,z4,z159]),(0,[z0,z11,z296,z2,z3,z4,z5]),(0,[z566,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z567,z3,z4,z5])],[(0,[z0,z1,z46,z3,z138,z4,z5]),(0,[z0,z568,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z4,z5]),(0,[z569,z0,z1,z2,z3,z4,z5])],[(1,[z7,z1,z17,z3,z4,z5]),(0,[z0,z1,z17,z3,z45,z4,z5]),(0,[z490,z29,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z278,z2,z3,z4]),(0,[z0,z48,z1,z2,z3,z4,z238])],[(0,[z0,z1,z2,z570,z3,z4,z5]),(0,[z571,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z572,z4,z5])],[(2,[z9,z1,z17,z3,z4]),(0,[z187,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z101,z3,z4,z21]),(0,[z0,z1,z573,z2,z3,z4,z5]),(0,[z0,z97,z1,z2,z3,z4,z404]),(0,[z0,z1,z278,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z5,z574]),(0,[z0,z1,z2,z3,z142,z4,z99])],[(0,[z58,z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z46,z164,z3,z4,z5]),(0,[z81,z0,z1,z563,z3,z4,z5]),(1,[z0,z1,z541,z3,z4,z5]),(0,[z29,z0,z1,z348,z3,z4,z5]),(0,[z0,z1,z2,z575,z3,z4,z5]),(0,[z576,z0,z1,z2,z3,z4,z5])],[(1,[z532,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z577]),(0,[z0,z1,z2,z3,z578,z4,z5])],[(0,[z0,z11,z1,z105,z3,z4,z5]),(1,[z0,z1,z2,z3,z141,z5]),(0,[z0,z1,z2,z120,z3,z4,z12]),(0,[z0,z1,z2,z579,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z56,z32,z5]),(0,[z0,z1,z2,z90,z4,z26,z5]),(0,[z0,z1,z2,z134,z4,z5,z92]),(0,[z0,z1,z2,z3,z580,z4,z5])],[],[(0,[z0,z1,z179,z17,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z581,z4,z5]),(0,[z582,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z65,z4,z5])],[(0,[z0,z583,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z5,z54]),(1,[z9,z1,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z584,z4,z5])]],
   [[(0,[z9,z0,z1,z2,z3,z4,z32]),(0,[z29,z29,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z432])],[(0,[z9,z0,z1,z53,z2,z3,z4]),(0,[z558,z0,z1,z53,z2,z3,z4]),(0,[z34,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z305,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z156,z5])],[(0,[z0,z1,z2,z3,z4,z434,z5]),(0,[z0,z11,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z134,z3,z4,z5])],[(0,[z152,z0,z1,z17,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z80,z5]),(0,[z0,z106,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z379,z5]),(0,[z0,z1,z2,z3,z4,z12,z12]),(0,[z0,z1,z2,z496,z3,z4,z5])],[(0,[z9,z1,z2,z17,z3,z4,z5]),(1,[z152,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z45,z4])],[(0,[z0,z585,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z12,z5]),(0,[z0,z1,z17,z3,z4,z5,z586]),(0,[z587,z0,z1,z2,z3,z4,z5]),(0,[z0,z588,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z120,z273,z3,z4])],[(0,[z0,z1,z17,z273,z3,z4,z5]),(0,[z0,z97,z1,z2,z49,z4,z5]),(0,[z0,z221,z1,z2,z356,z4,z5])],[(0,[z589,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z64,z5]),(0,[z0,z1,z2,z3,z590,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z591])],[(0,[z9,z0,z1,z2,z120,z3,z4]),(0,[z0,z592,z1,z2,z3,z4,z5])],[(0,[z44,z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z369,z3,z4,z5]),(1,[z189,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z52,z5]),(0,[z0,z1,z2,z3,z4,z321,z26])],[(0,[z0,z1,z17,z3,z4,z5,z92]),(0,[z0,z1,z305,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z593,z4,z5])],[(0,[z0,z1,z2,z3,z49,z4,z12]),(0,[z0,z1,z2,z594,z3,z4,z5])],[(0,[z0,z1,z2,z3,z56,z4,z21]),(0,[z0,z48,z97,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z41]),(0,[z0,z1,z2,z233,z3,z4,z21]),(0,[z0,z1,z2,z3,z142,z4,z21]),(0,[z0,z1,z2,z595,z3,z4,z5]),(0,[z0,z1,z2,z596,z3,z4,z5])],[(0,[z0,z1,z17,z3,z49,z4,z5]),(0,[z517,z29,z0,z1,z2,z3,z4]),(1,[z0,z1,z103,z164,z4,z5]),(0,[z0,z1,z2,z98,z3,z4,z5])]],
   [[(0,[z63,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z211,z4,z5]),(0,[z0,z221,z1,z2,z3,z4,z288]),(0,[z0,z1,z2,z3,z138,z4,z12])],[(0,[z0,z1,z2,z4,z168,z5,z92])],[(0,[z0,z1,z17,z3,z138,z4,z5]),(0,[z29,z0,z1,z2,z3,z4,z32]),(0,[z167,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z597,z3,z4,z5])],[(0,[z27,z0,z1,z2,z3,z4,z21]),(0,[z9,z0,z1,z2,z3,z138,z4])],[(0,[z0,z1,z2,z164,z3,z4,z12])],[(0,[z0,z1,z2,z3,z56,z4,z199]),(0,[z598,z0,z1,z2,z3,z4,z5])],[(0,[z1,z46,z2,z17,z3,z4,z5]),(0,[z0,z1,z17,z164,z3,z4,z5]),(0,[z0,z1,z175,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z450,z4,z5]),(0,[z0,z1,z2,z3,z599,z4,z5]),(0,[z0,z1,z2,z3,z4,z600,z5]),(0,[z420,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z142,z159])],[(0,[z1,z2,z3,z56,z4,z64,z5]),(0,[z1,z2,z3,z4,z30,z5,z54]),(1,[z0,z1,z2,z3,z4,z510])],[(0,[z9,z0,z1,z2,z3,z4,z64]),(0,[z0,z1,z210,z2,z3,z4,z5])],[(1,[z0,z1,z563,z3,z4,z5]),(0,[z0,z1,z2,z519,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z183,z12]),(0,[z0,z1,z2,z601,z3,z4,z5])],[(0,[z10,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z514]),(0,[z0,z1,z602,z2,z3,z4,z5])],[(0,[z7,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z603,z4,z5]),(0,[z0,z1,z2,z20,z3,z32,z5]),(0,[z0,z1,z102,z2,z65,z4,z5])],[(0,[z0,z1,z188,z46,z3,z4,z5]),(0,[z0,z604,z1,z2,z3,z4,z5])],[(0,[z23,z0,z270,z2,z3,z4,z5])],[(0,[z63,z9,z0,z1,z2,z3,z4]),(0,[z59,z29,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z74,z3,z4]),(0,[z0,z1,z2,z605,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z21]),(0,[z0,z1,z2,z606,z3,z4,z5]),(0,[z0,z607,z1,z2,z3,z4,z5])],[(0,[z55,z1,z2,z3,z4,z30,z5]),(0,[z81,z0,z1,z2,z20,z3,z5]),(0,[z0,z1,z2,z90,z3,z26,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z28,z5]),(0,[z0,z1,z196,z46,z3,z4,z5]),(0,[z1,z2,z101,z3,z45,z4,z5]),(1,[z0,z1,z2,z112,z4,z5]),(0,[z0,z608,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z609,z5])],[(0,[z0,z1,z2,z3,z4,z530,z5]),(0,[z0,z390,z1,z2,z3,z4,z5]),(0,[z0,z1,z46,z2,z3,z4,z12]),(1,[z0,z1,z261,z2,z3,z4]),(0,[z29,z0,z1,z348,z2,z3,z4]),(0,[z23,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z164,z3,z65,z4,z5])],[(0,[z610,z0,z1,z2,z3,z4,z5]),(0,[z44,z0,z1,z2,z45,z4,z5]),(0,[z0,z611,z1,z2,z3,z4,z5])],[(0,[z0,z1,z17,z3,z51,z4,z5]),(0,[z0,z1,z612,z2,z3,z4,z5]),(0,[z0,z613,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z614,z3,z4,z5]),(0,[z0,z615,z1,z2,z3,z4,z5])],[(0,[z435,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z5]),(0,[z29,z0,z270,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z12,z227])],[(0,[z0,z1,z53,z2,z3,z4,z21]),(0,[z0,z1,z46,z129,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z64,z12]),(0,[z9,z0,z1,z278,z2,z3,z4]),(0,[z0,z616,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z67,z4,z12])],[(0,[z0,z1,z2,z3,z3,z4,z5]),(1,[z10,z1,z2,z101,z4,z5]),(0,[z0,z1,z2,z86,z3,z4,z5]),(0,[z0,z221,z1,z2,z3,z4,z396]),(0,[z0,z1,z2,z617,z3,z4,z5])],[(0,[z0,z1,z2,z3,z343,z4,z5]),(0,[z0,z1,z17,z3,z4,z64,z5]),(0,[z0,z1,z2,z3,z4,z5,z618]),(0,[z0,z1,z2,z619,z3,z4,z5]),(0,[z0,z1,z2,z620,z3,z4,z5])],[(0,[z0,z621,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z47,z21]),(0,[z0,z1,z2,z622,z3,z4,z5])],[],[(1,[z0,z1,z46,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z60,z5])],[(0,[z58,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z623,z5])],[(0,[z0,z1,z2,z90,z134,z4,z5])],[(1,[z9,z1,z17,z3,z4,z5]),(0,[z0,z11,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z624])],[(0,[z0,z1,z2,z443,z3,z4,z5]),(0,[z63,z0,z1,z2,z3,z56,z5]),(0,[z0,z1,z2,z625,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z433,z5]),(0,[z0,z1,z2,z3,z4,z5,z405])],[(0,[z0,z1,z2,z3,z626,z4,z5]),(0,[z0,z1,z2,z3,z355,z4,z5])]],
   [[(0,[z55,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z74,z3,z4,z21]),(0,[z627,z0,z1,z2,z3,z4,z5])],[(0,[z0,z628,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z356,z4,z5]),(0,[z23,z0,z2,z3,z4,z12,z5]),(0,[z0,z1,z2,z629,z3,z4,z5])],[(0,[z0,z630,z1,z2,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z159,z5]),(0,[z0,z1,z2,z394,z4,z64,z5]),(0,[z0,z1,z2,z3,z631,z4,z5])],[(0,[z0,z1,z632,z2,z3,z4,z5])],[(0,[z633,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z634,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z635])],[(1,[z9,z1,z2,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z241,z5]),(0,[z29,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z636,z4,z5]),(0,[z384,z0,z1,z2,z3,z4,z21])],[(0,[z0,z1,z2,z637,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z45,z4]),(0,[z81,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z419,z3,z4,z5]),(0,[z0,z1,z2,z3,z51,z156,z5]),(0,[z638,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z639,z2,z3,z4,z5]),(0,[z287,z9,z0,z1,z2,z3,z4])],[(0,[z0,z1,z46,z3,z290,z4,z5]),(0,[z0,z1,z46,z3,z4,z168,z5]),(0,[z0,z1,z2,z3,z640,z4,z5])],[(0,[z641,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z369,z3,z4,z5]),(0,[z0,z1,z2,z642,z3,z4,z5])],[(0,[z0,z643,z1,z2,z3,z4,z5])],[(0,[z63,z0,z1,z46,z3,z4,z5])],[(0,[z44,z0,z1,z416,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z644,z5]),(0,[z63,z0,z1,z2,z20,z3,z5]),(0,[z29,z0,z11,z1,z2,z3,z4]),(0,[z58,z627,z1,z2,z3,z4,z5])],[(0,[z0,z645,z1,z2,z3,z4,z5]),(0,[z0,z1,z296,z2,z3,z4,z5]),(0,[z0,z646,z1,z2,z3,z4,z5])],[(0,[z27,z0,z1,z2,z3,z76,z5]),(0,[z0,z1,z647,z2,z3,z4,z5]),(0,[z648,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z120,z3,z4,z5]),(1,[z0,z1,z2,z212,z3,z4]),(0,[z0,z1,z2,z90,z3,z51,z5]),(0,[z0,z1,z2,z395,z3,z4,z21]),(0,[z0,z1,z2,z649,z3,z4,z5])],[(0,[z0,z1,z2,z650,z3,z4,z5]),(0,[z10,z0,z1,z2,z45,z4,z5]),(0,[z29,z10,z0,z1,z2,z3,z4]),(0,[z29,z9,z1,z2,z3,z4,z5]),(1,[z0,z1,z392,z3,z4,z5]),(0,[z0,z221,z1,z2,z3,z4,z5]),(0,[z0,z1,z651,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z652,z5]),(0,[z0,z1,z2,z3,z4,z653,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z654,z5]),(0,[z44,z0,z1,z2,z138,z4,z5]),(0,[z0,z1,z2,z90,z3,z4,z52]),(0,[z0,z1,z2,z134,z273,z4,z5])],[],[(1,[z27,z53,z2,z3,z4,z5]),(0,[z0,z1,z492,z2,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z5,z21])],[(0,[z0,z655,z1,z2,z3,z4,z5]),(0,[z55,z7,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z656,z3,z4,z5]),(0,[z0,z1,z102,z2,z3,z4,z5]),(0,[z0,z1,z2,z657,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z148]),(0,[z81,z1,z2,z3,z56,z4,z5]),(0,[z0,z1,z2,z3,z4,z658,z5])],[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z2,z134,z138,z4,z5])],[(0,[z317,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z104,z3,z4,z5]),(0,[z465,z0,z1,z2,z3,z4,z5]),(0,[z59,z0,z1,z2,z3,z130,z5]),(0,[z0,z11,z1,z164,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z659])],[(0,[z0,z1,z179,z2,z17,z3,z4]),(0,[z9,z0,z1,z2,z3,z49,z4])],[(0,[z0,z1,z17,z3,z4,z5,z99])],[(1,[z29,z0,z1,z348,z3,z4]),(0,[z0,z1,z660,z2,z3,z4,z5]),(0,[z0,z1,z103,z2,z164,z4,z5])],[(0,[z0,z1,z2,z3,z45,z4,z5]),(0,[z0,z1,z2,z3,z4,z429,z5]),(0,[z0,z1,z2,z661,z3,z4,z5])],[(0,[z23,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z21,z618]),(0,[z662,z0,z1,z2,z3,z4,z5])],[(0,[z384,z7,z0,z1,z2,z3,z4]),(0,[z0,z1,z663,z2,z3,z4,z5]),(0,[z0,z1,z1,z2,z3,z4,z21])],[(0,[z152,z0,z1,z2,z17,z3,z4]),(0,[z0,z1,z2,z664,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z665,z5]),(0,[z0,z1,z2,z3,z4,z5,z359]),(1,[z0,z1,z105,z3,z156,z5]),(0,[z0,z1,z278,z2,z3,z156,z5])],[(0,[z9,z0,z1,z2,z74,z3,z4]),(0,[z0,z1,z2,z3,z4,z159,z12]),(0,[z0,z1,z278,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z53,z46,z3,z4,z5]),(0,[z7,z0,z1,z96,z3,z4,z5]),(0,[z7,z8,z1,z2,z3,z4,z5]),(0,[z0,z666,z1,z2,z3,z4,z5]),(0,[z0,z0,z1,z17,z3,z4,z5]),(0,[z29,z0,z1,z452,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z667,z5])],[(0,[z0,z1,z17,z3,z4,z159,z5]),(0,[z668,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z195,z3,z49,z4,z5]),(0,[z669,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z670,z5])],[(0,[z0,z1,z671,z2,z3,z4,z5])],[(1,[z0,z1,z2,z467,z3,z4]),(0,[z327,z9,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z392,z3,z4,z5]),(0,[z317,z29,z0,z1,z2,z3,z4])],[(0,[z81,z0,z1,z2,z3,z56,z5]),(0,[z0,z1,z2,z3,z4,z672,z5])],[(0,[z9,z0,z270,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z86,z3,z4]),(0,[z0,z673,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z168,z12]),(0,[z0,z1,z674,z2,z3,z4,z5]),(1,[z58,z0,z1,z3,z4,z47])],[(0,[z0,z675,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z210,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z54]),(0,[z0,z1,z2,z3,z4,z238,z5])],[(0,[z0,z1,z17,z3,z4,z168,z5]),(0,[z0,z1,z105,z17,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z21])],[(0,[z676,z0,z1,z2,z3,z4,z5])],[(0,[z29,z0,z1,z2,z3,z49,z4])],[(0,[z8,z1,z53,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z677,z5]),(0,[z29,z0,z106,z1,z2,z3,z4]),(1,[z0,z1,z2,z323,z4,z5]),(0,[z0,z1,z2,z3,z678,z4,z5]),(0,[z0,z1,z2,z3,z679,z4,z5])],[(0,[z0,z1,z2,z104,z3,z4,z5]),(0,[z0,z1,z2,z680,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z586]),(0,[z10,z0,z1,z2,z138,z4,z5]),(0,[z9,z0,z1,z2,z3,z314,z4]),(0,[z0,z1,z2,z3,z4,z5,z681]),(0,[z0,z1,z2,z3,z682,z4,z5]),(0,[z0,z1,z2,z3,z4,z12,z5])],[(0,[z7,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z683,z5]),(0,[z684,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z685,z4,z5]),(0,[z0,z1,z686,z2,z3,z4,z5]),(0,[z0,z1,z2,z273,z3,z4,z5])],[(0,[z0,z1,z46,z3,z56,z4,z5]),(0,[z0,z1,z2,z3,z4,z687,z5]),(1,[z0,z1,z2,z3,z4,z199]),(0,[z0,z1,z2,z3,z688,z4,z5]),(0,[z0,z1,z2,z3,z689,z4,z5])]],
   [[(0,[z0,z8,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z5,z432]),(0,[z0,z1,z2,z3,z4,z690,z5])],[(0,[z0,z1,z17,z3,z4,z5,z21]),(0,[z81,z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z691,z5]),(0,[z692,z0,z1,z2,z3,z4,z5])],[(0,[z693,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z541,z2,z3,z4,z5]),(0,[z0,z694,z1,z2,z3,z4,z5]),(0,[z695,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z92])],[(0,[z0,z1,z103,z17,z3,z4,z5]),(1,[z0,z1,z2,z273,z4,z168]),(0,[z0,z1,z2,z120,z3,z4,z159])],[(0,[z27,z9,z0,z1,z2,z3,z4]),(1,[z558,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z103,z2,z3,z4]),(0,[z0,z1,z2,z3,z696,z4,z5])],[(0,[z0,z1,z2,z3,z697,z4,z5]),(0,[z0,z1,z2,z3,z4,z698,z5]),(0,[z0,z2,z3,z51,z4,z32,z5]),(0,[z0,z1,z2,z3,z4,z396,z5]),(0,[z0,z1,z2,z138,z4,z26,z5])],[(0,[z163,z0,z1,z17,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z30]),(0,[z0,z1,z2,z3,z49,z4,z5]),(0,[z0,z1,z2,z3,z4,z699,z5])],[(0,[z0,z1,z452,z2,z3,z4,z5]),(0,[z0,z270,z1,z2,z3,z4,z5]),(0,[z0,z532,z1,z2,z3,z4,z5])],[(0,[z29,z0,z1,z210,z2,z3,z4])],[(0,[z506,z0,z1,z2,z3,z4,z5]),(0,[z59,z0,z1,z2,z3,z4,z514]),(1,[z0,z1,z2,z3,z4,z328]),(0,[z0,z1,z2,z700,z3,z4,z5]),(1,[z627,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z138,z4,z5])],[(0,[z0,z1,z2,z3,z64,z32,z5]),(0,[z0,z1,z701,z2,z3,z4,z5]),(0,[z0,z1,z702,z2,z3,z4,z5]),(0,[z0,z1,z703,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z509,z4,z5])],[],[(0,[z9,z0,z11,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z704,z5]),(0,[z29,z0,z1,z2,z134,z3,z4]),(0,[z0,z1,z2,z164,z3,z4,z5])],[(0,[z705,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z209,z3,z4,z5]),(0,[z59,z0,z1,z3,z31,z4,z5]),(0,[z0,z1,z2,z706,z3,z4,z5]),(0,[z0,z1,z210,z3,z4,z5,z227])],[(0,[z0,z1,z46,z3,z4,z32,z5]),(0,[z0,z1,z46,z90,z3,z4,z5]),(0,[z0,z1,z2,z35,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z2,z3,z4]),(0,[z0,z257,z2,z3,z4,z21]),(0,[z0,z1,z708,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z709]),(0,[z0,z2,z547,z3,z4,z12]),(0,[z710,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z711])],[(0,[z712,z0,z1,z2,z3,z4]),(0,[z669,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z357]),(0,[z29,z0,z1,z105,z3,z156]),(0,[z0,z270,z2,z3,z4,z21]),(0,[z0,z1,z2,z98,z159,z5])],[(0,[z7,z0,z452,z2,z3,z4]),(0,[z0,z261,z2,z3,z4,z12]),(0,[z125,z1,z2,z3,z4,z21])],[(0,[z0,z1,z2,z3,z4,z713]),(0,[z0,z1,z278,z3,z31,z5]),(0,[z714,z0,z1,z2,z3,z4])],[(0,[z1,z2,z17,z3,z4,z80]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z716,z1,z2,z3,z4,z5]),(0,[z0,z1,z470,z3,z156,z5]),(0,[z150,z1,z2,z3,z4,z430])],[(0,[z0,z663,z2,z3,z4,z21]),(0,[z125,z1,z2,z323,z4,z5]),(0,[z0,z1,z2,z3,z717,z4])],[(0,[z0,z1,z2,z3,z718,z4]),(0,[z420,z0,z1,z46,z3,z4]),(0,[z1,z2,z3,z719,z4,z5]),(0,[z0,z1,z2,z3,z720,z5]),(0,[z0,z1,z2,z3,z262,z60]),(0,[z0,z1,z2,z721,z4,z5])],[(0,[z9,z627,z1,z2,z3,z4]),(0,[z0,z97,z46,z74,z4,z5]),(0,[z0,z1,z46,z3,z4,z722]),(0,[z0,z97,z2,z74,z4,z12]),(0,[z723,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z146,z3,z5])],[(0,[z0,z1,z2,z724,z3,z4]),(0,[z0,z1,z17,z3,z4,z725]),(0,[z481,z1,z17,z3,z4,z5]),(0,[z118,z0,z1,z348,z3,z4]),(0,[z1,z110,z3,z4,z30,z5]),(0,[z0,z11,z296,z3,z4,z5])],[(0,[z0,z1,z318,z3,z4,z12])],[(0,[z55,z9,z1,z2,z3,z4]),(0,[z0,z726,z2,z3,z4,z5]),(0,[z0,z1,z2,z98,z4,z405])],[(0,[z0,z1,z2,z3,z4,z727]),(0,[z9,z0,z1,z2,z355,z4]),(0,[z728,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z130,z5]),(0,[z0,z1,z2,z222,z4,z12]),(0,[z1,z2,z3,z4,z21,z729])],[(0,[z27,z53,z2,z3,z4,z28]),(0,[z294,z1,z17,z3,z4,z5]),(0,[z9,z1,z392,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z29,z1,z2,z3,z4,z272])],[(0,[z9,z1,z46,z17,z3,z4]),(0,[z731,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z321])],[(0,[z0,z1,z732,z2,z3,z5]),(0,[z0,z1,z2,z733,z4,z5]),(0,[z0,z95,z2,z3,z51,z5])],[(0,[z7,z1,z17,z3,z4,z12]),(0,[z29,z0,z1,z734,z3,z4]),(0,[z0,z1,z2,z735,z4,z5])]],
   [[(0,[z0,z1,z2,z736,z3,z5]),(1,[z9,z1,z737,z3,z4]),(0,[z0,z1,z17,z3,z4,z238]),(0,[z0,z1,z2,z138,z644,z5]),(0,[z9,z0,z1,z2,z3,z738])],[(0,[z739,z0,z1,z2,z3,z4]),(0,[z740,z0,z1,z2,z3,z4])],[(0,[z1,z17,z3,z696,z4,z5]),(0,[z0,z1,z17,z741,z3,z5]),(0,[z0,z1,z541,z3,z4,z12]),(0,[z9,z0,z1,z2,z146,z3]),(0,[z29,z0,z1,z2,z3,z262]),(0,[z0,z1,z2,z3,z742,z5])],[(0,[z9,z0,z1,z2,z112,z4]),(1,[z0,z743,z3,z4,z5]),(0,[z0,z565,z2,z3,z32,z5]),(0,[z532,z1,z2,z3,z4,z12])],[(0,[z9,z163,z1,z17,z3,z4]),(0,[z9,z1,z179,z17,z3,z4]),(0,[z1,z17,z614,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z744]),(0,[z9,z268,z1,z2,z3,z4]),(0,[z29,z0,z1,z13,z3,z4]),(0,[z0,z1,z2,z355,z130,z5]),(0,[z0,z1,z2,z745,z4,z5]),(0,[z0,z1,z2,z3,z141,z12])],[(0,[z0,z1,z746,z2,z3,z4]),(0,[z0,z1,z17,z3,z4,z249]),(0,[z0,z1,z16,z209,z4,z5]),(0,[z29,z0,z1,z737,z3,z4]),(0,[z0,z1,z747,z3,z4,z5]),(0,[z0,z2,z3,z4,z12,z21])],[(0,[z9,z7,z8,z2,z3,z4]),(0,[z0,z1,z139,z65,z4,z5]),(0,[z0,z1,z261,z392,z3,z4]),(0,[z9,z1,z556,z2,z3,z4])],[(0,[z7,z8,z371,z3,z4,z5]),(0,[z0,z1,z17,z3,z5,z136]),(0,[z532,z1,z188,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z748]),(0,[z749,z1,z2,z3,z4,z5])],[(0,[z0,z1,z750,z3,z4,z5]),(0,[z1,z406,z17,z3,z4,z5]),(0,[z0,z1,z751,z17,z3,z4]),(0,[z9,z1,z17,z3,z4,z47]),(0,[z0,z1,z17,z3,z262,z5]),(0,[z0,z1,z2,z752,z4,z5])],[(0,[z27,z53,z2,z3,z76,z5]),(0,[z27,z53,z46,z3,z4,z5]),(0,[z0,z1,z753,z3,z4,z12])],[(0,[z0,z1,z754,z3,z4,z5]),(0,[z29,z125,z1,z2,z3,z4])],[(0,[z9,z1,z105,z17,z3,z4]),(0,[z0,z1,z2,z755,z3,z4]),(0,[z0,z1,z46,z3,z4,z148]),(0,[z0,z1,z2,z3,z4,z756])],[(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z758,z3,z4,z5]),(0,[z0,z759,z1,z2,z3,z4]),(0,[z0,z1,z13,z3,z4,z21]),(0,[z0,z1,z760,z3,z4,z5]),(0,[z692,z0,z2,z3,z4,z12])],[(0,[z29,z0,z1,z2,z761,z4])],[(1,[z1,z762,z3,z4,z5]),(0,[z569,z1,z17,z3,z4,z5]),(0,[z0,z1,z763,z3,z4,z5])]],
   [[(0,[z0,z1,z104,z3,z76,z5]),(0,[z0,z1,z764,z3,z4,z5]),(0,[z9,z1,z17,z419,z3,z4])],[(0,[z0,z1,z2,z3,z4,z765]),(0,[z63,z1,z17,z3,z64,z5]),(0,[z9,z9,z1,z17,z3,z4]),(0,[z0,z1,z452,z46,z3,z4]),(0,[z0,z1,z46,z766,z4,z5]),(0,[z0,z1,z2,z35,z112,z4]),(0,[z0,z1,z2,z767,z3,z5])],[(0,[z27,z53,z104,z3,z4,z5]),(0,[z204,z9,z1,z17,z3,z4]),(0,[z116,z1,z17,z3,z4,z5]),(0,[z0,z221,z17,z3,z51,z5]),(0,[z0,z1,z2,z768,z4,z5]),(0,[z0,z1,z2,z203,z3,z4])],[(0,[z23,z9,z1,z17,z3,z4]),(0,[z9,z0,z221,z2,z3,z51])],[(0,[z0,z1,z769,z2,z3,z4])],[(0,[z0,z1,z37,z3,z4,z201]),(0,[z0,z1,z2,z770,z4,z5]),(0,[z9,z1,z17,z3,z4,z429]),(0,[z0,z1,z2,z3,z4,z771]),(0,[z772,z0,z1,z2,z3,z4]),(0,[z189,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z90,z368,z5]),(0,[z0,z106,z2,z3,z32,z5]),(0,[z0,z1,z2,z3,z4,z773])],[],[(0,[z0,z1,z2,z3,z4,z439]),(0,[z408,z1,z2,z3,z56,z5]),(0,[z29,z1,z2,z3,z4,z311])],[(0,[z465,z1,z17,z3,z4,z5]),(0,[z1,z762,z2,z3,z4,z5]),(0,[z0,z1,z210,z3,z4,z75]),(0,[z29,z0,z1,z2,z4,z299])],[(0,[z0,z1,z2,z3,z4,z774]),(0,[z9,z0,z775,z2,z3,z4])],[(0,[z0,z1,z46,z3,z4,z776]),(0,[z29,z0,z1,z777,z3,z4]),(0,[z0,z778,z1,z2,z3,z4]),(0,[z0,z588,z2,z3,z32,z5]),(0,[z0,z1,z103,z164,z4,z12])],[(0,[z779,z0,z1,z17,z3,z4]),(0,[z0,z1,z46,z467,z3,z4]),(0,[z9,z1,z2,z3,z4,z426]),(0,[z0,z1,z2,z3,z780,z5]),(0,[z0,z1,z2,z90,z781,z5])],[(0,[z27,z782,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z1,z70,z3,z4,z21]),(0,[z0,z1,z2,z90,z203,z26])],[(0,[z9,z1,z17,z3,z56,z4]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z785,z3,z4,z5]),(0,[z0,z1,z2,z90,z203,z3])],[(0,[z63,z1,z2,z597,z3,z5]),(0,[z0,z1,z2,z3,z4,z514])],[(0,[z0,z1,z2,z3,z786,z5]),(0,[z9,z0,z1,z2,z274,z4]),(0,[z34,z9,z1,z17,z3,z4]),(0,[z9,z1,z17,z3,z51,z4]),(0,[z150,z0,z1,z787,z3,z4]),(0,[z0,z1,z2,z3,z5,z788])]],
   [[(0,[z0,z1,z46,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z662,z1,z46,z3,z4,z5]),(0,[z9,z0,z1,z70,z3,z4]),(0,[z9,z0,z1,z790,z3,z4]),(0,[z0,z205,z2,z3,z4,z12])],[(0,[z81,z1,z2,z3,z56,z21])],[(0,[z9,z221,z1,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z791]),(0,[z0,z1,z185,z3,z4,z618]),(0,[z0,z1,z2,z307,z4,z168]),(0,[z0,z1,z2,z120,z3,z792])],[(0,[z0,z1,z452,z2,z3,z4]),(0,[z0,z1,z793,z3,z4,z5]),(0,[z0,z1,z46,z323,z4,z5]),(0,[z63,z1,z2,z3,z172,z64]),(0,[z0,z1,z794,z3,z4,z5]),(0,[z0,z2,z3,z742,z4,z5])],[(0,[z1,z17,z88,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z795]),(0,[z0,z1,z563,z3,z4,z12]),(1,[z0,z2,z3,z742,z5]),(0,[z0,z1,z796,z3,z4,z5]),(0,[z797,z1,z2,z3,z4,z5])],[(0,[z29,z0,z1,z2,z343,z4]),(0,[z0,z1,z2,z3,z798,z5]),(0,[z0,z1,z371,z3,z4,z12]),(0,[z0,z1,z2,z222,z4,z288]),(0,[z0,z1,z2,z3,z799,z4])],[(0,[z0,z1,z2,z98,z120,z5])],[(0,[z27,z29,z53,z2,z3,z4]),(0,[z0,z1,z284,z46,z3,z4]),(0,[z1,z46,z17,z3,z4,z21]),(0,[z0,z1,z46,z3,z4,z199]),(0,[z0,z1,z2,z355,z4,z514])],[(0,[z9,z0,z1,z2,z3,z76]),(0,[z81,z1,z2,z3,z56,z199]),(0,[z29,z0,z48,z2,z49,z4]),(0,[z0,z1,z800,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z801]),(0,[z0,z1,z2,z802,z3,z5])],[(0,[z0,z1,z803,z3,z4,z5]),(0,[z1,z229,z46,z3,z4,z5]),(0,[z0,z2,z3,z4,z804,z21])],[(0,[z0,z1,z2,z274,z4,z5]),(0,[z0,z1,z17,z3,z4,z201]),(0,[z420,z34,z1,z2,z3,z4]),(1,[z9,z1,z17,z3,z4]),(0,[z9,z1,z17,z20,z3,z4]),(0,[z0,z1,z46,z112,z4,z5]),(0,[z0,z1,z46,z273,z4,z168]),(0,[z0,z1,z2,z112,z4,z12]),(0,[z9,z0,z1,z348,z3,z4]),(0,[z0,z1,z2,z3,z4,z805])],[(0,[z0,z1,z2,z3,z4,z806]),(0,[z9,z0,z1,z110,z3,z4]),(0,[z204,z0,z1,z2,z419,z4]),(0,[z125,z1,z105,z3,z4,z5])],[(1,[z34,z1,z17,z3,z4]),(0,[z376,z1,z17,z3,z4,z5]),(0,[z627,z1,z70,z3,z4,z5]),(0,[z23,z0,z452,z2,z3,z4]),(0,[z0,z1,z807,z3,z4,z5])],[(0,[z0,z1,z17,z3,z211,z5]),(0,[z0,z808,z17,z3,z4,z5]),(0,[z0,z218,z2,z3,z4,z21]),(0,[z0,z1,z809,z2,z3,z4]),(0,[z0,z1,z2,z90,z402,z5]),(0,[z0,z1,z2,z98,z4,z92])],[(0,[z9,z1,z17,z3,z198,z4]),(0,[z29,z0,z1,z810,z3,z4]),(0,[z0,z1,z2,z3,z4,z811])]],
   [[(0,[z0,z1,z37,z343,z4,z5]),(0,[z7,z53,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z812])],[(0,[z627,z1,z46,z3,z4,z5]),(0,[z10,z1,z2,z101,z4,z12])],[(0,[z189,z1,z2,z3,z262,z5]),(0,[z0,z1,z2,z3,z4,z405]),(0,[z0,z1,z2,z3,z33,z159])],[(0,[z9,z0,z813,z2,z3,z4]),(0,[z0,z221,z2,z3,z742,z5]),(0,[z0,z1,z2,z134,z146,z5])],[(0,[z0,z1,z17,z3,z4,z331]),(0,[z0,z1,z2,z3,z814,z5])],[(0,[z0,z1,z2,z815,z3,z5]),(0,[z0,z1,z816,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z817]),(0,[z44,z1,z416,z45,z4,z5]),(0,[z490,z0,z1,z110,z3,z4]),(0,[z0,z1,z2,z818,z4,z5])],[(0,[z9,z1,z17,z3,z4,z12]),(0,[z0,z819,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z98,z4]),(0,[z0,z1,z470,z3,z4,z5]),(0,[z0,z1,z3,z453,z4,z5])],[(0,[z0,z1,z284,z2,z3,z4]),(0,[z517,z0,z1,z2,z3,z241]),(0,[z0,z97,z2,z74,z211,z5])],[(0,[z0,z694,z2,z3,z4,z21]),(0,[z0,z1,z2,z820,z3,z4])],[(0,[z0,z1,z2,z821,z4,z5]),(0,[z55,z1,z762,z3,z4,z5]),(0,[z9,z0,z106,z2,z3,z32]),(0,[z0,z1,z2,z3,z822,z5]),(0,[z0,z1,z2,z222,z4,z396]),(0,[z0,z1,z2,z120,z3,z93])],[(0,[z9,z1,z70,z17,z3,z4]),(0,[z0,z1,z46,z35,z3,z4]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z824,z4,z5]),(1,[z0,z1,z3,z4,z825])],[(0,[z0,z1,z2,z3,z76,z28]),(0,[z9,z1,z16,z17,z3,z4]),(0,[z1,z17,z3,z4,z12,z30]),(0,[z638,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z262,z21]),(0,[z0,z1,z826,z3,z4,z5]),(0,[z0,z2,z620,z3,z4,z12])],[(0,[z9,z10,z1,z17,z3,z4]),(0,[z0,z1,z2,z3,z827,z5]),(0,[z0,z1,z2,z3,z4,z828])],[(0,[z0,z97,z2,z74,z4,z331]),(0,[z829,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z323,z262,z5])],[(0,[z0,z1,z2,z3,z830,z5]),(0,[z0,z1,z46,z3,z4,z831]),(0,[z29,z0,z1,z2,z832,z4]),(0,[z833,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z834,z3,z4])],[(0,[z55,z150,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z835,z5]),(0,[z0,z1,z2,z3,z836,z4]),(0,[z0,z1,z2,z120,z3,z487])],[(0,[z0,z1,z369,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z837]),(0,[z0,z106,z470,z3,z32,z5])],[(0,[z0,z1,z104,z3,z4,z28]),(0,[z7,z8,z2,z3,z4,z21]),(0,[z9,z1,z17,z273,z3,z4]),(0,[z63,z1,z2,z3,z64,z21]),(0,[z0,z1,z2,z3,z12,z838]),(0,[z627,z1,z2,z3,z4,z47])],[(0,[z0,z1,z17,z343,z4,z5]),(0,[z34,z1,z17,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z149])],[(0,[z1,z70,z17,z3,z4,z5]),(0,[z44,z0,z1,z2,z269,z5]),(0,[z0,z1,z839,z3,z4,z12]),(0,[z0,z1,z2,z840,z4,z5])],[(0,[z0,z1,z416,z3,z4,z5]),(0,[z1,z2,z3,z4,z30,z841]),(0,[z0,z1,z2,z3,z4,z842])],[(0,[z0,z1,z843,z3,z4,z5]),(0,[z0,z1,z46,z212,z3,z4]),(1,[z0,z1,z2,z134,z146])],[(0,[z29,z0,z1,z37,z3,z4]),(0,[z558,z1,z53,z17,z3,z4]),(0,[z163,z1,z17,z3,z4,z21]),(0,[z0,z1,z2,z844,z4,z5]),(0,[z0,z1,z2,z3,z5,z845])],[(0,[z0,z1,z46,z3,z76,z5]),(0,[z1,z17,z3,z4,z162,z5]),(0,[z9,z0,z1,z416,z3,z4]),(0,[z9,z0,z1,z392,z3,z4]),(0,[z333,z0,z1,z2,z144,z4]),(0,[z0,z1,z2,z3,z142,z433])],[(0,[z0,z1,z2,z3,z4,z846]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z1,z102,z355,z4,z5]),(0,[z0,z1,z2,z3,z141,z331])],[(0,[z1,z53,z104,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z848]),(0,[z27,z53,z2,z3,z4,z12]),(0,[z0,z1,z707,z17,z3,z4])],[(0,[z0,z1,z17,z269,z3,z5]),(0,[z712,z0,z1,z17,z3,z4]),(0,[z0,z1,z17,z849,z3,z4]),(0,[z9,z81,z1,z2,z3,z56]),(0,[z29,z0,z97,z2,z74,z4])],[(0,[z0,z1,z2,z274,z388,z5]),(0,[z0,z1,z46,z3,z4,z91]),(0,[z0,z1,z305,z3,z4,z12]),(0,[z9,z189,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z850]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z0,z1,z17,z356,z4,z5]),(0,[z0,z1,z17,z98,z4,z5]),(0,[z63,z1,z2,z112,z64,z5]),(0,[z477,z1,z2,z3,z64,z5]),(0,[z0,z1,z852,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z853])],[(0,[z0,z1,z2,z98,z4,z168])],[(0,[z0,z1,z2,z3,z4,z854]),(0,[z0,z1,z2,z855,z4,z5]),(0,[z0,z1,z318,z3,z4,z5]),(0,[z0,z1,z856,z3,z4,z5]),(0,[z0,z11,z3,z25,z4,z5]),(0,[z0,z1,z2,z395,z4,z41])],[(0,[z0,z1,z37,z3,z388,z5]),(0,[z502,z1,z17,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z857])],[(0,[z1,z17,z3,z4,z30,z21]),(0,[z44,z9,z1,z2,z45,z4]),(0,[z29,z0,z1,z858,z3,z4]),(0,[z0,z1,z2,z3,z859,z5]),(0,[z0,z1,z2,z222,z4,z5]),(0,[z0,z1,z2,z120,z3,z99])],[(0,[z0,z1,z96,z3,z4,z21]),(0,[z29,z213,z1,z2,z3,z4]),(0,[z0,z2,z3,z4,z653,z12])],[(0,[z59,z125,z86,z3,z4,z5]),(0,[z860,z1,z2,z3,z4,z5])],[(0,[z55,z9,z1,z17,z3,z4]),(0,[z0,z1,z2,z3,z861,z4]),(0,[z862,z0,z1,z2,z3,z4])],[(0,[z7,z1,z17,z3,z4,z5]),(0,[z9,z1,z17,z3,z4,z227]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z9,z0,z1,z2,z394,z4])],[(0,[z0,z1,z17,z3,z4,z288]),(0,[z0,z1,z17,z864,z4,z5]),(0,[z0,z1,z2,z865,z3,z4]),(0,[z34,z0,z1,z392,z3,z4]),(0,[z29,z0,z1,z2,z3,z130]),(0,[z0,z1,z866,z3,z4,z5]),(0,[z0,z1,z105,z3,z156,z12])],[(0,[z0,z1,z867,z17,z4,z5]),(0,[z0,z1,z196,z443,z4,z5]),(0,[z0,z97,z261,z2,z3,z4]),(0,[z9,z1,z2,z579,z3,z4]),(0,[z29,z0,z1,z2,z3,z868]),(0,[z869,z0,z1,z2,z3,z4]),(0,[z870,z0,z1,z2,z3,z4])],[(0,[z0,z1,z541,z3,z4,z5]),(0,[z532,z1,z3,z4,z47,z5]),(0,[z0,z1,z2,z98,z120,z4])],[(0,[z532,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z871,z4,z5]),(0,[z0,z1,z2,z872,z3,z4]),(0,[z0,z1,z873,z3,z4,z5]),(0,[z0,z1,z874,z3,z4,z5])],[(0,[z29,z0,z1,z2,z3,z388]),(0,[z0,z1,z3,z4,z80,z227]),(0,[z875,z0,z1,z2,z3,z4]),(0,[z662,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z876]),(0,[z0,z1,z110,z3,z4,z21]),(0,[z0,z1,z102,z65,z4,z5]),(0,[z0,z1,z877,z3,z4,z5])],[(0,[z9,z1,z17,z3,z4,z159]),(0,[z0,z1,z878,z3,z4,z5])]],
   [[(0,[z29,z0,z1,z96,z3,z4]),(0,[z125,z1,z46,z3,z4,z5]),(0,[z879,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z880]),(0,[z0,z1,z2,z881,z4,z5]),(0,[z29,z10,z1,z2,z101,z4]),(0,[z59,z0,z86,z3,z4,z5]),(0,[z0,z412,z2,z3,z4,z21]),(0,[z0,z1,z2,z90,z26,z5])],[(0,[z0,z1,z2,z3,z4,z882]),(0,[z55,z1,z2,z3,z4,z80]),(0,[z10,z1,z2,z511,z4,z5]),(0,[z0,z1,z2,z3,z211,z21]),(0,[z0,z1,z2,z3,z4,z883]),(0,[z0,z1,z3,z4,z825,z227])],[(0,[z0,z1,z753,z3,z4,z5]),(0,[z63,z1,z2,z3,z884,z5]),(0,[z9,z1,z2,z3,z4,z54]),(0,[z0,z1,z2,z3,z4,z804]),(0,[z0,z1,z2,z146,z3,z405])],[(0,[z0,z1,z215,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z1,z2,z3,z4,z432]),(0,[z0,z1,z2,z74,z211,z5]),(0,[z0,z1,z2,z3,z4,z886])],[(0,[z0,z1,z2,z3,z4,z887]),(0,[z384,z0,z1,z96,z3,z4]),(0,[z420,z0,z1,z17,z3,z4]),(0,[z0,z775,z2,z3,z4,z5]),(0,[z29,z1,z2,z88,z3,z4]),(0,[z0,z1,z888,z3,z4,z5])],[(0,[z0,z1,z2,z323,z4,z12]),(0,[z0,z1,z2,z3,z4,z889]),(0,[z890,z1,z2,z3,z4,z21])],[(0,[z0,z1,z891,z17,z3,z4]),(0,[z0,z1,z2,z892,z3,z4])],[(0,[z0,z1,z2,z893,z3,z4]),(0,[z0,z1,z17,z84,z3,z5]),(0,[z29,z9,z1,z46,z3,z4]),(0,[z29,z0,z1,z137,z3,z4]),(0,[z0,z894,z1,z2,z3,z4]),(0,[z0,z1,z2,z134,z146,z4])],[(0,[z0,z1,z17,z3,z388,z5]),(0,[z0,z1,z2,z3,z4,z895]),(0,[z0,z1,z2,z3,z4,z896])],[(0,[z8,z782,z2,z3,z4,z5]),(0,[z0,z261,z2,z3,z4,z32]),(0,[z59,z0,z86,z355,z4,z5])],[(0,[z29,z0,z1,z2,z897,z4]),(0,[z29,z1,z2,z3,z478,z4]),(0,[z0,z1,z2,z898,z3,z4])],[(0,[z420,z9,z1,z2,z3,z4]),(0,[z9,z0,z1,z899,z3,z4]),(0,[z900,z0,z1,z2,z3,z4])],[(0,[z0,z1,z901,z3,z4,z5]),(0,[z0,z1,z17,z394,z4,z5]),(0,[z9,z1,z17,z164,z3,z4]),(0,[z0,z1,z902,z3,z4,z5]),(0,[z29,z1,z2,z3,z4,z379]),(0,[z23,z0,z2,z3,z4,z804])],[(0,[z152,z532,z1,z2,z3,z4]),(0,[z903,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z103,z164,z4])],[(0,[z0,z1,z2,z3,z4,z904]),(0,[z0,z1,z17,z3,z4,z396]),(0,[z0,z1,z17,z134,z4,z92]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z1,z2,z3,z21,z845]),(0,[z906,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z907,z3,z4]),(0,[z7,z8,z46,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z357]),(0,[z9,z1,z278,z17,z3,z4]),(0,[z0,z1,z2,z134,z4,z908])],[(0,[z515,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z909,z4,z12])],[(0,[z0,z1,z37,z3,z4,z5]),(0,[z152,z1,z17,z3,z4,z30]),(0,[z536,z1,z46,z3,z4,z5]),(0,[z910,z0,z1,z2,z3,z4]),(0,[z384,z1,z2,z3,z4,z379]),(0,[z0,z1,z2,z3,z4,z792])],[(0,[z29,z0,z1,z17,z3,z4]),(0,[z0,z390,z296,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z141]),(0,[z0,z155,z2,z3,z4,z21])],[(0,[z0,z1,z17,z3,z4,z404]),(0,[z0,z1,z46,z3,z4,z328]),(0,[z911,z0,z1,z2,z3,z4]),(0,[z627,z1,z2,z3,z4,z12])],[(0,[z0,z1,z2,z3,z4,z912]),(0,[z163,z1,z762,z3,z4,z5]),(0,[z0,z1,z2,z3,z868,z5]),(0,[z9,z0,z1,z318,z3,z4]),(0,[z0,z1,z2,z3,z4,z60]),(0,[z0,z1,z3,z4,z21,z853])],[(0,[z0,z1,z2,z3,z4,z913]),(0,[z0,z1,z2,z3,z914,z4])],[(0,[z44,z1,z17,z45,z4,z5]),(0,[z1,z179,z17,z3,z4,z30]),(0,[z1,z242,z46,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z915]),(0,[z63,z9,z1,z2,z3,z64]),(0,[z189,z1,z2,z355,z4,z5]),(0,[z0,z1,z105,z3,z262,z5])],[(0,[z384,z0,z1,z17,z3,z4]),(0,[z0,z1,z46,z3,z172,z4]),(0,[z44,z1,z2,z269,z45,z5]),(0,[z0,z1,z916,z3,z4,z5]),(0,[z0,z1,z2,z3,z917,z5])],[(0,[z0,z1,z2,z3,z4,z918]),(0,[z0,z919,z17,z3,z4,z5]),(0,[z132,z9,z1,z2,z3,z4]),(0,[z125,z1,z164,z3,z4,z5]),(0,[z920,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z921,z3,z5]),(0,[z0,z1,z2,z3,z4,z922]),(0,[z29,z9,z1,z2,z3,z4]),(0,[z9,z0,z1,z2,z923,z3]),(0,[z0,z1,z2,z20,z5,z234]),(0,[z0,z1,z2,z3,z142,z159])],[(0,[z0,z1,z13,z3,z4,z12])],[(0,[z1,z17,z129,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z924]),(0,[z0,z1,z46,z3,z4,z22]),(0,[z0,z1,z2,z925,z3,z4]),(0,[z125,z1,z2,z3,z262,z5]),(0,[z0,z1,z2,z3,z4,z926])],[(0,[z0,z1,z371,z3,z4,z5]),(0,[z0,z1,z2,z927,z3,z4]),(0,[z150,z7,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z29,z1,z46,z3,z4,z30]),(0,[z0,z1,z46,z3,z4,z929]),(0,[z29,z0,z1,z470,z3,z4]),(0,[z0,z1,z2,z355,z4,z60])],[(0,[z0,z1,z930,z3,z4,z5]),(0,[z152,z7,z1,z17,z3,z4]),(0,[z0,z97,z2,z74,z4,z404]),(0,[z0,z1,z2,z931,z3,z4])]],
   [[(0,[z0,z1,z46,z3,z4,z28]),(0,[z0,z1,z452,z17,z3,z4]),(0,[z0,z1,z932,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z1,z2,z3,z934,z4])],[(0,[z0,z1,z2,z269,z3,z21]),(0,[z935,z0,z1,z2,z3,z4]),(0,[z0,z1,z936,z3,z4,z5]),(0,[z0,z1,z2,z3,z67,z159])],[(0,[z937,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z305,z3,z4]),(0,[z0,z1,z2,z3,z4,z938]),(0,[z9,z1,z2,z3,z4,z341]),(0,[z939,z1,z2,z3,z4,z5]),(0,[z0,z1,z940,z3,z4,z5]),(0,[z0,z1,z2,z90,z487,z5])],[(0,[z9,z0,z1,z371,z3,z4]),(0,[z163,z1,z179,z17,z3,z4]),(0,[z1,z17,z3,z4,z5,z272]),(0,[z0,z1,z137,z3,z4,z21]),(0,[z0,z1,z2,z98,z4,z21])],[(0,[z0,z1,z46,z3,z4,z52]),(0,[z0,z941,z1,z2,z3,z4]),(0,[z0,z2,z942,z49,z4,z5]),(1,[z0,z2,z3,z4,z804]),(0,[z0,z1,z787,z3,z4,z21])],[(0,[z152,z0,z1,z179,z3,z4]),(0,[z0,z1,z46,z3,z4,z943]),(0,[z0,z358,z2,z3,z51,z5]),(0,[z944,z0,z1,z2,z3,z4]),(0,[z945,z0,z1,z2,z3,z4])],[(0,[z0,z1,z17,z3,z4,z946]),(0,[z0,z1,z947,z2,z3,z4]),(0,[z0,z1,z948,z3,z4,z5]),(0,[z0,z1,z195,z3,z4,z21]),(0,[z0,z106,z3,z453,z32,z5])],[(0,[z0,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z949,z5]),(0,[z55,z1,z284,z2,z3,z4]),(0,[z0,z1,z17,z3,z950,z5])],[(0,[z187,z9,z1,z17,z3,z4]),(0,[z951,z0,z1,z2,z3,z4]),(0,[z0,z221,z2,z3,z51,z21])],[(0,[z0,z1,z2,z952,z4,z5]),(0,[z202,z1,z17,z3,z4,z5]),(0,[z0,z1,z46,z953,z4,z5]),(0,[z10,z1,z2,z101,z4,z5]),(0,[z0,z954,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z955,z4]),(0,[z0,z1,z2,z109,z3,z18]),(0,[z167,z0,z1,z3,z4,z217]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z1,z2,z90,z26,z405])],[(0,[z957,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z958,z5]),(0,[z50,z0,z1,z2,z3,z450]),(0,[z0,z2,z264,z3,z4,z21])],[(0,[z27,z53,z2,z3,z4,z201]),(0,[z0,z1,z2,z3,z141,z404])],[(0,[z0,z1,z959,z3,z4,z5]),(0,[z239,z1,z17,z3,z4,z5]),(0,[z9,z0,z1,z102,z65,z4]),(0,[z0,z1,z392,z3,z4,z12]),(0,[z0,z1,z960,z3,z4,z5]),(0,[z0,z1,z210,z3,z4,z94])],[(0,[z0,z1,z2,z3,z76,z12]),(0,[z0,z1,z46,z3,z4,z12]),(0,[z9,z1,z2,z3,z4,z15]),(0,[z0,z1,z470,z3,z31,z5]),(0,[z0,z1,z103,z840,z4,z5])],[(0,[z9,z1,z53,z17,z3,z4]),(0,[z0,z1,z17,z3,z4,z75]),(0,[z187,z0,z350,z3,z4,z5]),(0,[z81,z1,z2,z3,z56,z12]),(0,[z961,z0,z1,z2,z3,z4]),(0,[z0,z1,z962,z3,z4,z5]),(0,[z0,z611,z2,z3,z4,z21]),(0,[z963,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z17,z964,z4,z5]),(0,[z0,z48,z17,z49,z4,z5]),(0,[z59,z0,z399,z3,z4,z5]),(0,[z0,z97,z2,z942,z4,z5]),(0,[z0,z1,z2,z90,z159,z168])],[(0,[z9,z1,z17,z3,z4,z5]),(0,[z0,z1,z17,z355,z4,z5]),(0,[z29,z0,z1,z2,z269,z3])],[(0,[z34,z0,z1,z371,z3,z4]),(0,[z0,z1,z17,z3,z4,z80]),(0,[z44,z1,z2,z84,z45,z5]),(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z1,z2,z3,z4,z966])],[(0,[z0,z1,z2,z3,z4,z967]),(0,[z1,z261,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z722]),(0,[z9,z0,z1,z2,z968,z4]),(0,[z0,z97,z2,z74,z4,z5])],[(0,[z0,z106,z17,z3,z32,z5]),(0,[z29,z0,z1,z2,z84,z3]),(0,[z0,z1,z2,z3,z969,z5]),(0,[z627,z1,z2,z3,z4,z227])],[(0,[z1,z46,z762,z3,z4,z5]),(0,[z377,z0,z1,z3,z4,z80]),(0,[z1,z2,z3,z4,z841,z5]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z0,z1,z2,z3,z159,z405])],[(0,[z0,z1,z104,z3,z4,z12]),(0,[z0,z1,z284,z17,z3,z4]),(0,[z0,z1,z17,z3,z4,z439]),(0,[z0,z1,z971,z3,z4,z5]),(0,[z0,z1,z2,z3,z130,z514]),(0,[z59,z0,z86,z3,z130,z5]),(0,[z0,z11,z296,z3,z4,z432]),(0,[z0,z1,z2,z4,z781,z5])],[(0,[z0,z1,z972,z3,z4,z5]),(0,[z7,z0,z261,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z973]),(0,[z0,z1,z2,z3,z974,z5]),(0,[z0,z1,z2,z4,z5,z299])],[(0,[z879,z125,z1,z2,z3,z4])],[(0,[z0,z1,z179,z392,z3,z4]),(0,[z0,z1,z105,z3,z362,z5]),(0,[z59,z9,z0,z86,z3,z4]),(0,[z9,z1,z229,z2,z3,z4]),(0,[z125,z1,z492,z3,z4,z5]),(0,[z0,z1,z2,z203,z20,z3])],[(0,[z1,z782,z2,z3,z4,z5]),(0,[z152,z0,z1,z46,z3,z4]),(0,[z0,z1,z975,z3,z4,z21])],[(0,[z1,z261,z2,z17,z3,z4]),(0,[z0,z976,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z825,z5])],[(0,[z0,z1,z2,z84,z3,z21]),(0,[z29,z0,z1,z541,z3,z4]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z2,z977,z3,z4])],[(0,[z1,z2,z3,z56,z884,z5]),(0,[z29,z286,z1,z2,z3,z4]),(0,[z978,z1,z2,z3,z4,z5])],[(0,[z187,z53,z17,z3,z4,z5]),(0,[z0,z1,z732,z17,z3,z5]),(0,[z0,z1,z2,z3,z4,z979]),(0,[z0,z1,z980,z3,z4,z5]),(0,[z0,z1,z70,z3,z4,z47]),(0,[z0,z1,z2,z3,z4,z981]),(0,[z0,z1,z2,z3,z982,z5]),(0,[z0,z2,z74,z942,z4,z5]),(0,[z0,z1,z840,z65,z4,z5]),(0,[z0,z1,z983,z3,z4,z5])],[(0,[z34,z1,z17,z3,z4,z5]),(0,[z1,z17,z3,z4,z5,z311]),(0,[z9,z0,z1,z843,z3,z4]),(0,[z9,z0,z1,z2,z90,z26]),(0,[z0,z1,z984,z2,z3,z4]),(0,[z985,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z17,z3,z4,z986,z5]),(0,[z0,z1,z2,z3,z4,z987]),(0,[z0,z1,z2,z3,z141,z5]),(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z1,z2,z3,z159,z574]),(0,[z0,z1,z989,z3,z4,z5])],[(0,[z150,z1,z2,z3,z4,z54])],[(0,[z7,z8,z2,z3,z4,z22]),(0,[z9,z1,z17,z209,z3,z4]),(0,[z0,z1,z46,z3,z4,z238]),(0,[z0,z1,z2,z3,z5,z990]),(0,[z0,z1,z2,z991,z4,z5])],[(0,[z0,z1,z2,z3,z4,z992]),(0,[z125,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z993])],[(0,[z1,z46,z179,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z994]),(0,[z995,z0,z1,z2,z3,z4]),(0,[z0,z1,z996,z3,z4,z5])],[(0,[z0,z1,z2,z997,z4,z5]),(0,[z0,z1,z2,z998,z4,z5]),(0,[z7,z8,z96,z3,z4,z5]),(0,[z9,z1,z2,z3,z4,z841]),(0,[z0,z999,z1,z2,z3,z4]),(0,[z0,z1,z2,z1000,z3,z4])],[(0,[z27,z53,z2,z3,z4,z5]),(0,[z0,z1,z2,z395,z4,z92]),(0,[z0,z1,z1001,z3,z4,z12])],[(0,[z27,z53,z2,z343,z4,z5]),(0,[z420,z1,z53,z2,z3,z4]),(0,[z34,z1,z2,z17,z3,z4]),(0,[z0,z1,z46,z3,z4,z249]),(0,[z1002,z1,z2,z3,z4,z5]),(0,[z532,z1,z210,z3,z4,z5])],[(0,[z27,z284,z53,z2,z3,z4]),(0,[z0,z1,z305,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z148]),(0,[z29,z0,z1,z369,z3,z4]),(0,[z0,z1,z1003,z3,z4,z5])],[(0,[z27,z558,z53,z2,z3,z4]),(0,[z0,z1,z17,z20,z138,z5]),(0,[z0,z1,z46,z3,z5,z136])],[(0,[z0,z1,z39,z3,z31,z5]),(0,[z9,z0,z1,z2,z3,z1004]),(0,[z29,z0,z1,z975,z3,z4]),(0,[z0,z1,z2,z3,z130,z60]),(0,[z0,z1,z2,z3,z4,z1005]),(0,[z0,z1,z3,z4,z1006,z12])],[(0,[z0,z1,z46,z3,z262,z5])],[(0,[z152,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z67,z292])],[(0,[z0,z1,z2,z766,z4,z5]),(0,[z9,z1,z2,z3,z4,z586]),(0,[z29,z0,z1,z2,z356,z4]),(0,[z0,z1,z1007,z3,z4,z5]),(0,[z0,z1,z1008,z2,z3,z4])],[(0,[z0,z1,z2,z1009,z4,z5]),(1,[z0,z1,z2,z98,z120])],[(0,[z0,z1,z858,z3,z4,z5]),(0,[z384,z0,z1,z975,z3,z4]),(0,[z10,z1,z2,z719,z4,z5]),(0,[z9,z0,z1,z2,z323,z4])]],
   [[(0,[z9,z1,z17,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z1010]),(0,[z9,z1,z2,z3,z4,z267]),(0,[z0,z1,z2,z3,z4,z1011])],[(0,[z189,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1012]),(0,[z58,z9,z1,z17,z3,z4]),(0,[z55,z1,z46,z3,z4,z21]),(0,[z0,z261,z2,z3,z49,z4]),(0,[z0,z1,z2,z3,z1013,z5]),(0,[z0,z1,z2,z3,z792,z99])],[(0,[z0,z1,z2,z1014,z4,z5]),(0,[z0,z1,z1015,z3,z4,z5]),(0,[z7,z8,z2,z3,z4,z12]),(0,[z0,z1,z2,z1016,z4,z5]),(0,[z0,z270,z17,z3,z4,z21]),(0,[z63,z1,z46,z3,z64,z5]),(0,[z150,z1,z2,z101,z3,z4]),(0,[z63,z1,z2,z3,z64,z12]),(0,[z0,z1,z2,z172,z112,z4]),(0,[z9,z0,z1,z195,z3,z4]),(0,[z29,z0,z1,z2,z3,z211])],[(0,[z0,z221,z46,z3,z51,z5]),(0,[z0,z1,z2,z3,z4,z1017]),(0,[z9,z1,z2,z3,z4,z252]),(0,[z29,z0,z1,z930,z3,z4]),(0,[z1018,z0,z1,z3,z4,z5])],[(0,[z0,z1,z179,z3,z4,z227]),(0,[z10,z1,z2,z101,z4,z357])],[(0,[z558,z0,z1,z46,z3,z4]),(0,[z0,z1,z261,z46,z3,z4]),(0,[z0,z1,z2,z3,z4,z776]),(0,[z0,z1,z1019,z3,z4,z5]),(0,[z0,z1,z2,z273,z4,z251]),(0,[z0,z1,z103,z164,z4,z5]),(0,[z0,z1,z1020,z2,z3,z4])],[(1,[z150,z1,z17,z3,z4]),(0,[z0,z1,z2,z467,z3,z4]),(0,[z0,z1,z2,z120,z3,z429]),(0,[z0,z1,z2,z1021,z3,z4]),(0,[z0,z1,z2,z3,z4,z1022])],[(0,[z163,z1,z17,z3,z4,z12]),(0,[z0,z1,z17,z3,z718,z4]),(0,[z0,z1,z2,z3,z1023,z5]),(0,[z1024,z1,z2,z3,z4,z5])],[(0,[z384,z0,z1,z930,z3,z4]),(0,[z9,z1,z17,z120,z3,z4]),(0,[z0,z1,z17,z146,z3,z5]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z9,z0,z1,z753,z3,z4]),(0,[z0,z1,z2,z3,z1026,z5]),(0,[z59,z0,z86,z3,z4,z514]),(0,[z0,z1,z2,z109,z3,z99]),(0,[z420,z0,z1,z1027,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1028]),(0,[z0,z1,z17,z724,z3,z4]),(0,[z0,z1029,z1,z2,z3,z4]),(0,[z1030,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z168,z405]),(0,[z0,z1,z2,z3,z781,z5])],[(0,[z0,z1,z1031,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z0,z1,z3,z31,z780,z5])],[(0,[z0,z1,z2,z3,z4,z21]),(0,[z9,z1,z17,z74,z3,z4]),(0,[z29,z1,z110,z3,z4,z30]),(0,[z0,z1,z2,z4,z21,z299])],[(0,[z0,z1,z2,z343,z4,z21]),(0,[z1,z17,z3,z4,z243,z5]),(0,[z0,z1,z17,z3,z130,z5]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z1,z128,z3,z156,z5]),(0,[z0,z1,z790,z3,z4,z5]),(0,[z29,z627,z1,z2,z3,z4])],[(0,[z0,z1,z2,z1034,z4,z5]),(0,[z55,z29,z1,z46,z3,z4]),(0,[z0,z1,z2,z3,z4,z510]),(0,[z58,z532,z1,z3,z4,z47])],[(0,[z0,z1,z17,z3,z4,z321]),(0,[z0,z1,z2,z3,z4,z1035]),(0,[z118,z9,z1,z392,z3,z4]),(0,[z29,z0,z1,z2,z20,z138]),(0,[z0,z1,z2,z323,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1036]),(0,[z0,z1,z563,z3,z4,z5]),(0,[z0,z1,z2,z269,z49,z5]),(0,[z0,z1037,z1,z2,z3,z4]),(0,[z0,z1,z348,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z2,z4,z168,z635])],[(0,[z0,z1,z2,z394,z35,z4]),(0,[z29,z0,z1,z2,z355,z4]),(0,[z0,z1,z2,z3,z4,z1039]),(0,[z1,z2,z3,z4,z1040,z5]),(0,[z0,z1,z2,z20,z36,z5]),(0,[z0,z1,z3,z4,z5,z1041]),(0,[z0,z1,z1042,z3,z4,z5]),(0,[z0,z1,z3,z4,z47,z825])],[(0,[z34,z1,z2,z3,z4,z252]),(0,[z0,z2,z3,z4,z161,z12])],[(0,[z0,z1,z96,z3,z4,z12]),(0,[z9,z1,z17,z3,z138,z4]),(0,[z0,z1,z46,z3,z4,z1043]),(0,[z0,z1,z2,z3,z4,z199]),(0,[z9,z1,z242,z2,z3,z4]),(0,[z29,z150,z1,z2,z3,z4]),(0,[z0,z1,z1044,z3,z4,z5]),(0,[z58,z0,z1,z3,z4,z825])],[(0,[z0,z1,z46,z1045,z4,z5]),(0,[z0,z48,z2,z49,z4,z21]),(0,[z0,z1,z102,z840,z4,z5])],[(0,[z0,z1,z17,z3,z4,z149]),(0,[z1,z17,z3,z4,z267,z5]),(0,[z0,z1,z2,z355,z4,z21]),(0,[z0,z1,z1046,z3,z4,z21]),(0,[z0,z1,z2,z4,z5,z908])],[(0,[z0,z1,z2,z3,z4,z1047]),(0,[z512,z1,z46,z3,z4,z5]),(0,[z0,z48,z2,z942,z4,z5]),(0,[z0,z1,z1048,z3,z4,z5]),(0,[z0,z1,z1049,z3,z4,z5])],[(0,[z34,z0,z1,z753,z3,z4]),(0,[z0,z1,z2,z112,z4,z5]),(0,[z0,z1,z2,z3,z4,z1050]),(0,[z9,z0,z1,z2,z770,z4]),(0,[z9,z627,z1,z70,z3,z4]),(0,[z0,z296,z743,z3,z4,z5]),(0,[z0,z1,z2,z356,z4,z21]),(0,[z150,z0,z1,z1046,z3,z4])],[(0,[z558,z0,z1,z2,z3,z4]),(0,[z0,z1,z261,z2,z3,z4]),(0,[z0,z1,z1051,z2,z3,z5]),(0,[z384,z150,z1,z2,z3,z4]),(0,[z9,z1,z17,z3,z4,z64]),(0,[z0,z1,z737,z3,z4,z5]),(0,[z0,z1,z1052,z3,z4,z5]),(0,[z29,z0,z1,z2,z146,z3])],[(0,[z29,z0,z1,z2,z112,z4])],[(0,[z0,z1,z2,z3,z4,z1053]),(0,[z27,z53,z2,z3,z388,z5]),(0,[z29,z163,z1,z17,z3,z4]),(0,[z55,z9,z1,z70,z3,z4]),(0,[z0,z1,z2,z909,z4,z5])],[(0,[z1,z2,z3,z884,z64,z5]),(0,[z0,z1,z2,z3,z4,z1054])],[(0,[z29,z7,z8,z2,z3,z4]),(0,[z0,z1,z46,z3,z4,z1055]),(0,[z0,z1,z110,z3,z4,z12])],[(0,[z0,z1,z2,z3,z76,z201]),(0,[z0,z1,z46,z3,z4,z201]),(0,[z0,z1,z1056,z3,z4,z5]),(0,[z627,z1,z2,z3,z4,z5]),(0,[z1,z737,z17,z3,z4,z5]),(0,[z0,z1,z70,z3,z4,z12]),(0,[z1057,z1,z2,z3,z4,z5])],[(0,[z571,z1,z17,z3,z4,z5]),(0,[z0,z1,z17,z755,z3,z4]),(0,[z152,z0,z1,z3,z4,z434]),(0,[z0,z1,z46,z3,z4,z1058])],[(0,[z150,z1,z17,z3,z4,z5]),(0,[z9,z532,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z46,z3,z211,z5]),(0,[z1,z2,z101,z719,z4,z5]),(0,[z9,z0,z1,z3,z453,z4]),(0,[z0,z1,z2,z3,z211,z12])],[(0,[z0,z1,z2,z3,z4,z1059]),(0,[z0,z782,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z384,z7,z8,z2,z3,z4]),(0,[z9,z1,z737,z3,z4,z5]),(0,[z248,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z394,z32,z5]),(0,[z0,z1,z70,z392,z3,z4]),(0,[z0,z1,z2,z3,z4,z1061])],[(0,[z0,z1,z2,z3,z1062,z5]),(0,[z0,z1,z2,z3,z4,z1063])],[(0,[z0,z1,z1064,z3,z4,z5]),(0,[z9,z1,z17,z3,z4,z30]),(0,[z0,z1,z46,z3,z4,z1065]),(0,[z0,z1,z2,z134,z146,z92])],[(0,[z0,z1,z17,z203,z3,z4]),(0,[z0,z1,z1066,z3,z4,z21])],[(0,[z0,z1,z104,z3,z4,z201]),(0,[z0,z1,z2,z1067,z4,z5]),(0,[z1,z737,z2,z17,z3,z4]),(0,[z0,z1,z2,z419,z4,z168]),(0,[z0,z1,z2,z260,z3,z93]),(0,[z0,z1,z2,z146,z3,z99]),(0,[z0,z1,z2,z3,z159,z792])],[(0,[z0,z1,z46,z3,z4,z331]),(0,[z0,z1,z46,z3,z4,z1068]),(0,[z0,z1,z2,z120,z596,z3])],[(0,[z0,z1,z37,z274,z4,z5]),(0,[z29,z9,z1,z17,z3,z4]),(0,[z0,z1,z17,z3,z4,z771]),(0,[z150,z1,z2,z17,z3,z4]),(0,[z0,z1,z3,z1069,z4,z5]),(0,[z0,z1,z2,z3,z4,z1070])],[(0,[z0,z1,z1071,z2,z3,z4]),(0,[z1,z46,z17,z3,z4,z12]),(0,[z9,z0,z1,z215,z3,z4]),(0,[z0,z1,z2,z3,z4,z1072])],[(0,[z29,z0,z221,z2,z3,z51]),(0,[z0,z1,z2,z3,z4,z1073])],[(0,[z0,z1,z2,z343,z4,z28]),(0,[z1,z762,z17,z3,z4,z5]),(0,[z613,z1,z17,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z136]),(0,[z29,z0,z1,z758,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1074]),(0,[z1,z17,z3,z4,z379,z21]),(0,[z0,z1,z139,z198,z4,z5]),(0,[z0,z1,z2,z1075,z3,z4]),(0,[z0,z1,z46,z3,z4,z1076]),(0,[z34,z0,z347,z2,z3,z4]),(0,[z0,z1,z2,z3,z1077,z5])],[(0,[z1,z53,z17,z3,z4,z21]),(0,[z9,z1,z2,z17,z3,z4]),(0,[z0,z1,z2,z120,z299,z99])],[(0,[z9,z1,z17,z3,z4,z434]),(0,[z0,z1,z128,z3,z530,z5]),(0,[z1,z17,z3,z4,z306,z5]),(0,[z0,z1,z2,z3,z4,z831]),(0,[z29,z0,z1,z856,z3,z4]),(0,[z0,z1,z2,z20,z138,z21])],[(0,[z0,z1,z2,z3,z1078,z4]),(0,[z34,z0,z261,z2,z3,z4]),(0,[z1079,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z20,z781,z5])],[(0,[z0,z1,z1080,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1081]),(0,[z0,z1,z2,z20,z265,z5]),(0,[z1082,z0,z1,z2,z3,z4]),(0,[z1083,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z1084,z12])]],
   [[(0,[z0,z1,z2,z3,z388,z21]),(0,[z0,z1,z17,z90,z26,z5]),(0,[z0,z1,z17,z3,z4,z514]),(0,[z0,z1,z369,z3,z4,z5])],[(0,[z0,z1,z3,z4,z80,z75]),(0,[z0,z1,z1085,z3,z4,z5]),(0,[z81,z1,z2,z486,z3,z5]),(0,[z0,z1,z1086,z3,z4,z5])],[(0,[z1,z17,z3,z4,z393,z5]),(0,[z1,z188,z179,z17,z3,z4]),(0,[z9,z0,z11,z296,z3,z4]),(0,[z1087,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1088])],[(0,[z0,z1,z839,z3,z4,z5]),(0,[z9,z270,z1,z17,z3,z4]),(0,[z9,z1,z2,z3,z4,z526])],[(0,[z7,z782,z2,z3,z4,z5]),(0,[z9,z1,z210,z17,z3,z4]),(0,[z63,z0,z1,z2,z394,z5]),(0,[z0,z1,z2,z394,z4,z21]),(0,[z9,z0,z1,z278,z3,z31]),(0,[z0,z2,z3,z4,z455,z21])],[(0,[z29,z0,z1,z2,z274,z4]),(0,[z0,z1,z2,z212,z3,z4]),(0,[z1089,z0,z1,z2,z3,z4]),(0,[z0,z1,z1090,z3,z4,z5])],[(0,[z9,z1,z17,z3,z45,z4]),(0,[z0,z1,z392,z3,z4,z5]),(0,[z0,z1,z2,z1091,z3,z4]),(0,[z9,z1,z2,z3,z4,z121]),(0,[z29,z0,z1,z70,z3,z4]),(0,[z189,z1,z2,z3,z130,z5]),(0,[z0,z1,z2,z3,z1092,z5]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z0,z1,z3,z4,z21,z1041])],[(0,[z0,z1,z2,z3,z76,z5]),(0,[z44,z29,z1,z2,z45,z4]),(0,[z9,z0,z1,z2,z1094,z4])],[(0,[z0,z1,z46,z343,z4,z5]),(0,[z0,z1,z2,z343,z76,z5]),(0,[z0,z1,z2,z3,z1004,z5]),(0,[z81,z1,z2,z3,z56,z5]),(0,[z9,z0,z1,z105,z3,z156]),(1,[z0,z1,z2,z781,z5])],[(0,[z0,z1,z2,z3,z1095,z4]),(0,[z0,z1,z278,z3,z31,z21])],[(0,[z0,z1,z810,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z1096]),(0,[z0,z1,z2,z3,z4,z1097])],[(0,[z9,z0,z1,z2,z733,z4]),(0,[z0,z11,z743,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z1,z2,z3,z4,z91]),(0,[z0,z2,z3,z4,z340,z12]),(0,[z0,z1,z2,z3,z1099,z5]),(0,[z0,z1,z2,z3,z4,z1100])],[(0,[z9,z176,z1,z17,z3,z4]),(0,[z9,z0,z1,z1031,z3,z4]),(0,[z474,z9,z1,z2,z3,z4]),(0,[z0,z1,z1101,z3,z4,z5]),(0,[z0,z1,z2,z90,z321,z26]),(0,[z0,z1,z2,z98,z142,z4])],[(0,[z0,z1,z17,z274,z4,z5]),(1,[z9,z1,z110,z3,z4]),(0,[z1102,z0,z1,z2,z3,z4]),(0,[z0,z1,z70,z3,z4,z227]),(0,[z0,z1,z2,z146,z3,z21])],[(0,[z29,z0,z1,z2,z3,z76]),(0,[z44,z1,z2,z45,z4,z21]),(0,[z1103,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z262,z12]),(0,[z0,z11,z296,z3,z4,z21]),(0,[z1104,z1,z2,z3,z4,z12])],[(0,[z0,z1,z104,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1105]),(0,[z0,z1,z13,z65,z4,z5])]],
   [[(0,[z0,z1,z104,z343,z4,z5]),(0,[z0,z1,z46,z269,z3,z5]),(0,[z0,z1,z2,z269,z3,z12]),(0,[z0,z11,z296,z3,z4,z510])],[(0,[z0,z1,z46,z3,z4,z1106]),(0,[z29,z0,z1,z348,z3,z4]),(0,[z0,z2,z3,z4,z12,z393])],[(0,[z0,z1,z1107,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z812]),(0,[z0,z1,z737,z2,z3,z4]),(0,[z0,z1,z46,z356,z4,z5]),(0,[z0,z1,z46,z98,z4,z5]),(0,[z0,z1,z2,z98,z4,z12])],[(0,[z9,z1,z17,z86,z3,z4]),(0,[z0,z1,z2,z269,z74,z5]),(0,[z536,z9,z1,z2,z3,z4])],[(0,[z0,z1,z17,z3,z4,z405]),(0,[z0,z1,z46,z3,z4,z1108])],[(0,[z0,z1,z46,z3,z1109,z5]),(0,[z0,z1,z195,z3,z4,z12]),(0,[z0,z1,z105,z3,z156,z5])],[(0,[z0,z1,z2,z3,z4,z1110]),(0,[z384,z0,z452,z2,z3,z4]),(0,[z150,z0,z1,z46,z3,z4]),(0,[z384,z0,z1,z348,z3,z4]),(0,[z0,z1,z2,z273,z144,z4]),(0,[z576,z0,z1,z2,z90,z5])],[(0,[z0,z2,z3,z4,z986,z5]),(0,[z384,z0,z1,z110,z3,z4]),(0,[z0,z221,z2,z3,z51,z12])],[(1,[z1,z17,z3,z4,z80]),(0,[z9,z1,z17,z3,z49,z4]),(0,[z0,z1,z2,z3,z1111,z4]),(0,[z0,z1,z2,z90,z600,z5])],[(0,[z1,z492,z17,z3,z4,z5]),(0,[z0,z221,z261,z2,z3,z4])],[],[(0,[z0,z1,z1112,z3,z4,z5]),(0,[z9,z0,z1,z46,z3,z4]),(0,[z9,z11,z1,z17,z3,z4]),(0,[z0,z1,z46,z3,z1113,z5]),(0,[z0,z1,z46,z3,z4,z288])],[(1,[z1,z284,z17,z3,z4]),(0,[z125,z1,z2,z3,z4,z5]),(0,[z1114,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1115]),(0,[z0,z1,z2,z4,z5,z1116]),(0,[z58,z0,z1,z3,z4,z47])],[(0,[z0,z1,z2,z3,z388,z28]),(0,[z0,z1,z702,z164,z4,z5]),(0,[z0,z1,z2,z3,z4,z1117]),(0,[z0,z1,z2,z138,z781,z5])],[(0,[z0,z1,z452,z348,z3,z4]),(0,[z0,z1,z2,z942,z4,z5]),(0,[z0,z1,z2,z3,z4,z1118])],[(0,[z1,z17,z3,z4,z421,z12]),(0,[z0,z1,z348,z3,z4,z47]),(0,[z0,z1,z1001,z3,z4,z5]),(0,[z0,z1,z2,z3,z1119,z4])]],
   [[(0,[z336,z1,z2,z101,z4,z5]),(0,[z0,z1,z2,z1120,z3,z4])],[(0,[z9,z1,z139,z17,z3,z4]),(0,[z63,z150,z1,z2,z3,z4]),(0,[z29,z0,z106,z2,z3,z32])],[(0,[z7,z1,z104,z3,z4,z5]),(0,[z0,z1,z1121,z3,z4,z5]),(1,[z1,z2,z3,z4,z841]),(0,[z29,z598,z1,z2,z3,z4]),(0,[z1122,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1123]),(0,[z0,z1,z2,z1124,z4,z5]),(0,[z0,z1,z1125,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z3,z4,z1006,z5])],[(0,[z0,z1,z2,z394,z51,z5]),(0,[z9,z0,z1,z2,z222,z4]),(0,[z0,z1,z2,z98,z120,z99])],[(0,[z0,z1,z2,z3,z4,z1126]),(0,[z326,z9,z1,z2,z3,z4]),(0,[z125,z1,z2,z355,z4,z5]),(0,[z0,z1,z2,z496,z4,z183]),(0,[z0,z1,z2,z3,z4,z825])],[(0,[z29,z1,z46,z17,z3,z4]),(0,[z0,z1,z46,z3,z1127,z5]),(0,[z0,z1,z2,z1128,z3,z4]),(0,[z0,z2,z3,z742,z32,z5])],[(0,[z9,z0,z1,z2,z3,z835])],[(0,[z150,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1129])],[(0,[z34,z0,z1,z46,z3,z4]),(0,[z152,z0,z1,z17,z3,z4]),(0,[z29,z0,z1,z1130,z3,z4]),(0,[z189,z1,z2,z3,z4,z514])],[(0,[z0,z1,z46,z84,z3,z5]),(0,[z0,z813,z2,z3,z4,z5]),(0,[z63,z29,z1,z2,z3,z64]),(0,[z0,z1,z2,z273,z4,z168])],[(0,[z27,z53,z2,z274,z4,z5]),(0,[z0,z1,z46,z3,z388,z5]),(0,[z9,z1,z17,z134,z3,z4]),(0,[z0,z106,z2,z3,z32,z21])],[(0,[z420,z1,z2,z3,z4,z30]),(0,[z1131,z189,z1,z2,z3,z4])],[(0,[z9,z0,z1,z2,z3,z4]),(0,[z9,z1,z17,z3,z314,z4]),(0,[z0,z1,z2,z90,z464,z5]),(0,[z0,z1,z210,z3,z4,z825])],[(0,[z152,z532,z1,z17,z3,z4]),(0,[z0,z1,z102,z290,z4,z5])],[(0,[z0,z1,z46,z394,z4,z5]),(0,[z9,z502,z1,z2,z3,z4]),(0,[z248,z9,z1,z2,z3,z4]),(0,[z9,z0,z1,z2,z4,z299])]],
   [[(0,[z27,z9,z1,z17,z3,z4]),(0,[z0,z1,z1132,z2,z4,z5]),(0,[z937,z0,z1,z96,z3,z4]),(0,[z55,z1,z371,z3,z4,z5]),(0,[z152,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1133]),(0,[z58,z0,z1,z110,z3,z4]),(0,[z59,z0,z86,z3,z4,z60]),(0,[z0,z1,z2,z3,z4,z328]),(0,[z1134,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z90,z134,z120])],[(0,[z163,z1,z17,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z396]),(0,[z0,z1,z46,z134,z4,z92]),(0,[z29,z0,z1,z416,z3,z4]),(0,[z0,z1,z2,z203,z138,z4])],[(0,[z0,z1,z46,z3,z4,z357]),(0,[z1135,z1,z2,z3,z4,z5])],[(0,[z0,z1,z104,z3,z388,z5]),(0,[z0,z1,z348,z110,z3,z4]),(0,[z0,z1,z2,z3,z4,z1136])],[(0,[z0,z1,z810,z2,z3,z4]),(0,[z29,z81,z1,z2,z3,z56]),(0,[z0,z1,z2,z3,z4,z1137])],[(0,[z63,z9,z1,z17,z3,z4]),(0,[z506,z9,z1,z17,z3,z4]),(0,[z0,z1,z215,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z0,z1,z2,z3,z4,z1139])],[(0,[z1,z53,z179,z17,z3,z4]),(0,[z0,z1,z17,z222,z4,z5]),(0,[z0,z1,z17,z120,z3,z99]),(0,[z0,z1,z17,z4,z5,z299]),(0,[z0,z1,z46,z3,z4,z404]),(0,[z1140,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1141]),(0,[z0,z1,z2,z3,z4,z1142])],[(0,[z9,z1,z244,z17,z3,z4]),(0,[z55,z1,z261,z2,z3,z4]),(0,[z0,z1,z278,z3,z509,z5]),(0,[z459,z1,z46,z3,z4,z5]),(0,[z63,z1,z137,z3,z64,z5]),(0,[z0,z1,z13,z3,z4,z5]),(0,[z0,z1,z2,z323,z4,z514])],[(0,[z9,z0,z1,z563,z3,z4]),(0,[z0,z1,z2,z1143,z4,z5]),(0,[z0,z48,z2,z49,z4,z328]),(0,[z0,z1,z2,z3,z211,z331]),(0,[z0,z1,z2,z1144,z4,z5])],[(0,[z0,z1,z2,z3,z4,z22]),(0,[z44,z1,z46,z45,z4,z5]),(0,[z59,z0,z129,z3,z4,z5]),(0,[z1145,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z496,z4,z168])],[(0,[z0,z1,z2,z3,z4,z929]),(0,[z9,z106,z1,z17,z3,z4]),(0,[z0,z1,z2,z1146,z4,z5]),(0,[z29,z1,z2,z3,z4,z30])],[(0,[z34,z0,z1,z2,z3,z4]),(0,[z1,z17,z3,z4,z30,z5]),(0,[z0,z1,z2,z35,z3,z4]),(0,[z0,z1,z2,z1147,z4,z5]),(0,[z0,z1,z2,z90,z203,z5])],[(0,[z0,z1,z2,z3,z4,z28]),(0,[z0,z1,z96,z3,z4,z5]),(0,[z0,z1,z2,z1148,z4,z5]),(0,[z0,z1,z2,z3,z1149,z5]),(0,[z0,z441,z2,z3,z4,z21])],[(0,[z189,z1,z2,z3,z4,z60]),(0,[z1150,z0,z1,z2,z3,z4])],[(0,[z532,z1,z17,z3,z4,z5]),(0,[z29,z0,z1,z2,z394,z4]),(0,[z29,z1,z348,z3,z4,z30]),(0,[z1151,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1152,z3,z4,z5]),(0,[z0,z1,z17,z3,z141,z5]),(0,[z0,z1,z2,z1153,z3,z4]),(0,[z0,z48,z13,z49,z4,z5]),(0,[z1154,z0,z1,z2,z3,z4])]],
   [[(0,[z9,z0,z1,z104,z3,z4]),(0,[z55,z1,z46,z3,z4,z12]),(0,[z0,z1,z2,z4,z5,z1155]),(0,[z0,z1,z2,z3,z4,z1156]),(0,[z0,z1,z13,z355,z4,z5]),(1,[z0,z2,z942,z4,z5])],[(0,[z0,z1,z2,z274,z4,z21]),(0,[z1,z703,z17,z3,z4,z5]),(0,[z598,z1,z17,z3,z4,z5]),(0,[z29,z1,z2,z3,z4,z562]),(0,[z0,z221,z2,z3,z51,z288]),(0,[z1157,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z52])],[(0,[z287,z9,z1,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z943]),(0,[z0,z1,z3,z780,z156,z5])],[(0,[z9,z7,z1,z17,z3,z4]),(0,[z317,z9,z1,z17,z3,z4]),(0,[z0,z1,z17,z881,z4,z5]),(0,[z9,z1,z103,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z1,z3,z780,z4,z5])],[(0,[z0,z1,z2,z1159,z4,z5]),(0,[z9,z8,z1,z17,z3,z4]),(0,[z0,z1,z2,z3,z1160,z5])],[(0,[z9,z1,z17,z90,z3,z4]),(0,[z0,z1,z261,z17,z3,z4]),(0,[z9,z1,z17,z3,z4,z54]),(0,[z0,z1,z1051,z17,z3,z5]),(0,[z0,z1,z1161,z3,z4,z5]),(0,[z9,z61,z1,z2,z3,z4]),(0,[z1162,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z51,z742,z5]),(0,[z0,z1,z2,z1163,z3,z4])],[(0,[z0,z1,z70,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z432])],[(0,[z9,z1,z17,z3,z193,z4]),(0,[z0,z1,z1164,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1165]),(0,[z0,z1166,z2,z3,z4,z5]),(0,[z1167,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z98,z120,z3])],[(0,[z1,z2,z3,z4,z841,z54]),(0,[z0,z133,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z908])],[(0,[z0,z1,z46,z3,z4,z5]),(0,[z0,z1,z1168,z3,z4,z5]),(0,[z27,z0,z452,z2,z3,z4]),(0,[z0,z97,z2,z74,z141,z5])],[(0,[z0,z1,z2,z343,z4,z12]),(0,[z0,z1,z2,z3,z4,z1169]),(0,[z0,z1,z2,z3,z4,z1170]),(0,[z957,z0,z1,z17,z3,z4]),(0,[z0,z390,z492,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1171]),(0,[z0,z1,z2,z3,z4,z1172]),(0,[z0,z106,z2,z3,z742,z5])],[(0,[z9,z1,z17,z3,z4,z586]),(0,[z0,z347,z2,z3,z4,z12]),(0,[z0,z1,z1173,z3,z4,z5])],[],[(0,[z0,z1,z2,z761,z4,z5]),(0,[z0,z1,z348,z3,z4,z12]),(0,[z0,z1,z470,z3,z4,z21]),(0,[z0,z1,z3,z453,z4,z21]),(0,[z0,z1,z2,z1174,z3,z4])],[(0,[z0,z1,z17,z3,z4,z1010]),(0,[z58,z0,z1,z392,z3,z4]),(0,[z9,z0,z1,z2,z98,z4])]],
   [[(0,[z189,z1,z17,z3,z4,z5]),(0,[z0,z1,z70,z3,z4,z80]),(0,[z0,z1,z1175,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z814]),(0,[z0,z1,z2,z1176,z4,z5]),(0,[z0,z1,z2,z1177,z3,z4])],[(0,[z0,z1,z2,z1178,z3,z5]),(0,[z34,z7,z1,z17,z3,z4]),(0,[z1,z46,z17,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z75]),(0,[z9,z1,z17,z3,z4,z92]),(0,[z0,z1,z1179,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1180])],[(0,[z0,z48,z46,z49,z4,z5]),(0,[z0,z1,z2,z824,z4,z21]),(0,[z0,z1,z2,z4,z12,z299])],[(0,[z0,z1,z2,z1181,z3,z4]),(0,[z0,z1,z46,z355,z4,z5])],[(0,[z0,z1,z46,z3,z4,z80]),(0,[z0,z1,z1182,z3,z4,z5]),(0,[z63,z1,z2,z394,z64,z5]),(0,[z0,z1,z2,z3,z130,z21]),(0,[z0,z2,z3,z4,z804,z5]),(0,[z0,z1,z1183,z3,z4,z5])],[(0,[z0,z1,z2,z897,z4,z5]),(0,[z0,z1,z137,z3,z4,z12]),(0,[z29,z0,z1,z110,z3,z4]),(0,[z0,z1,z2,z356,z4,z12]),(0,[z0,z1,z2,z134,z146,z3])],[(0,[z0,z1,z2,z3,z4,z725]),(0,[z0,z106,z46,z3,z32,z5]),(0,[z1184,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1185,z5]),(1,[z782,z2,z3,z4,z5]),(0,[z0,z1,z3,z1186,z4,z5]),(0,[z0,z1,z17,z3,z4,z60]),(0,[z0,z1,z2,z323,z130,z5]),(0,[z0,z1,z2,z222,z32,z5])],[(0,[z1,z46,z17,z3,z4,z75]),(0,[z55,z9,z1,z392,z3,z4]),(0,[z0,z1,z3,z1187,z4,z5]),(0,[z9,z0,z1,z1188,z3,z4]),(0,[z301,z0,z452,z2,z3,z4])],[(0,[z1,z17,z3,z478,z4,z5]),(0,[z187,z0,z86,z3,z4,z5]),(0,[z1,z556,z46,z3,z4,z5]),(0,[z0,z1,z2,z269,z212,z3]),(0,[z0,z365,z2,z74,z4,z5])],[(0,[z0,z106,z2,z3,z32,z91]),(0,[z0,z1,z1189,z3,z4,z12]),(0,[z0,z1,z3,z840,z4,z5]),(0,[z0,z1,z2,z3,z4,z1190])],[(0,[z1,z46,z17,z3,z4,z80]),(0,[z29,z0,z1,z318,z3,z4]),(0,[z0,z1,z2,z3,z4,z1191])],[(0,[z0,z1,z2,z1192,z3,z5]),(0,[z0,z1,z17,z921,z3,z5]),(0,[z0,z1,z17,z3,z142,z159]),(0,[z0,z1,z2,z394,z172,z4]),(0,[z9,z0,z1,z2,z3,z262])],[(0,[z0,z1,z17,z3,z4,z510]),(0,[z0,z1,z46,z3,z4,z783]),(0,[z1193,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z955,z4,z5]),(0,[z9,z81,z1,z17,z3,z4]),(0,[z0,z17,z3,z1194,z4,z5]),(0,[z9,z1,z737,z2,z3,z4]),(0,[z0,z1,z46,z1195,z4,z5]),(0,[z0,z1,z416,z3,z4,z21]),(0,[z0,z1,z1196,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1197]),(0,[z9,z0,z1,z13,z3,z4]),(0,[z0,z1,z2,z3,z4,z238])],[(0,[z9,z0,z1,z737,z3,z4]),(0,[z0,z1,z2,z1094,z4,z5])]],
   [[(0,[z0,z1,z2,z741,z3,z5]),(0,[z0,z1,z2,z3,z1198,z5]),(0,[z0,z1,z1199,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1200])],[(0,[z286,z1,z17,z3,z4,z5]),(0,[z9,z0,z1,z1201,z3,z4])],[(0,[z0,z1,z452,z110,z3,z4])],[(0,[z0,z1,z2,z1202,z3,z4]),(0,[z0,z1,z2,z832,z4,z5]),(0,[z0,z1,z2,z3,z4,z249])],[(0,[z0,z1,z2,z3,z4,z1203]),(0,[z0,z1,z2,z90,z578,z5])],[(0,[z0,z1,z1204,z3,z4,z5]),(0,[z9,z125,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z5,z136])],[(0,[z0,z1,z2,z3,z4,z1205]),(0,[z59,z0,z743,z3,z4,z5]),(0,[z0,z48,z2,z49,z4,z238])],[(0,[z9,z1,z2,z360,z3,z4]),(0,[z0,z2,z3,z4,z484,z21]),(0,[z0,z1,z2,z3,z262,z5]),(0,[z0,z1,z2,z3,z4,z1206])],[(0,[z152,z0,z1,z210,z3,z4]),(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z1208,z3,z4,z5]),(0,[z1209,z0,z1,z2,z3,z4])],[(0,[z0,z568,z2,z49,z4,z5]),(0,[z1,z2,z3,z4,z5,z1210])],[(0,[z1,z53,z17,z3,z4,z12]),(0,[z29,z0,z1,z371,z3,z4]),(0,[z0,z1,z2,z3,z4,z1211]),(0,[z0,z1,z3,z1212,z4,z5]),(0,[z29,z9,z1,z70,z3,z4]),(0,[z0,z1,z2,z1213,z4,z5]),(0,[z0,z1,z2,z222,z4,z21]),(0,[z0,z1,z2,z767,z3,z21])],[(0,[z1,z17,z3,z500,z4,z5]),(0,[z0,z1,z46,z20,z138,z5]),(0,[z29,z481,z1,z2,z3,z4]),(0,[z0,z1,z2,z1214,z4,z5]),(0,[z0,z1,z105,z3,z780,z5])],[(0,[z0,z1,z2,z274,z76,z5]),(0,[z0,z1,z2,z1215,z4,z5]),(0,[z10,z1,z17,z101,z4,z5]),(0,[z0,z1,z1216,z3,z4,z5]),(0,[z0,z46,z3,z4,z12,z21]),(0,[z0,z1,z164,z355,z4,z5]),(0,[z0,z1,z787,z3,z4,z5])],[(0,[z0,z1,z2,z84,z3,z12])],[(0,[z0,z1,z2,z3,z1217,z5]),(0,[z0,z1,z2,z3,z388,z12]),(0,[z0,z11,z244,z3,z4,z5]),(0,[z0,z1,z195,z3,z4,z5]),(0,[z0,z1,z2,z1218,z3,z4]),(0,[z0,z1,z1219,z3,z4,z5])],[(0,[z7,z8,z2,z3,z4,z5]),(0,[z0,z1,z1220,z3,z4,z5]),(0,[z384,z0,z1,z371,z3,z4]),(0,[z549,z0,z1,z2,z90,z5]),(0,[z63,z1,z2,z3,z64,z5]),(0,[z0,z743,z86,z3,z4,z5]),(0,[z0,z1,z1221,z3,z4,z5]),(0,[z0,z1,z1027,z3,z4,z12]),(0,[z0,z1,z1222,z3,z4,z5])]],
   [[(0,[z9,z0,z1,z2,z3,z130]),(0,[z0,z1223,z1,z2,z3,z4]),(0,[z0,z1,z2,z355,z262,z5]),(0,[z0,z221,z2,z3,z51,z5]),(0,[z0,z1,z2,z90,z203,z4]),(0,[z0,z1,z1224,z3,z4,z5])],[(0,[z27,z9,z53,z2,z3,z4]),(0,[z29,z0,z1,z2,z3,z1225])],[(0,[z27,z53,z37,z3,z4,z5]),(0,[z0,z1,z2,z1226,z4,z5]),(0,[z1,z2,z719,z45,z4,z5]),(0,[z0,z1,z2,z394,z4,z12]),(1,[z0,z1,z3,z780,z5])],[(0,[z0,z1,z2,z1227,z3,z4]),(0,[z0,z1,z1228,z3,z4,z5]),(0,[z0,z2,z3,z4,z21,z200]),(0,[z0,z1,z2,z3,z4,z1229])],[(0,[z0,z1,z104,z274,z4,z5]),(0,[z29,z0,z1,z392,z3,z4]),(0,[z125,z1,z2,z3,z4,z514]),(0,[z0,z1,z102,z65,z4,z21])],[(0,[z29,z1,z53,z17,z3,z4]),(0,[z0,z97,z17,z74,z4,z5]),(0,[z0,z270,z46,z3,z4,z21]),(0,[z29,z9,z1,z348,z3,z4]),(0,[z9,z1,z2,z625,z3,z4]),(0,[z459,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1230])],[(0,[z0,z1,z2,z3,z884,z5]),(0,[z150,z1,z2,z3,z56,z4]),(0,[z9,z1,z534,z2,z3,z4]),(0,[z0,z1,z2,z968,z4,z5]),(0,[z0,z1,z2,z3,z4,z1231]),(0,[z0,z1,z2,z3,z4,z1232]),(0,[z0,z417,z2,z3,z4,z21]),(0,[z420,z0,z1,z760,z3,z4]),(0,[z1233,z1,z2,z3,z4,z12])],[(0,[z0,z1,z2,z3,z172,z4]),(0,[z59,z0,z86,z3,z4,z21]),(0,[z0,z1,z2,z90,z26,z21]),(0,[z0,z604,z2,z3,z4,z21])],[(0,[z1,z17,z3,z4,z421,z5]),(0,[z0,z1,z2,z3,z1234,z4]),(0,[z384,z0,z155,z2,z3,z4]),(0,[z29,z189,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z211,z404]),(0,[z0,z1,z2,z3,z142,z557])],[(1,[z0,z1,z737,z3,z4]),(0,[z451,z1,z17,z3,z4,z5]),(0,[z9,z1,z102,z17,z3,z4]),(0,[z0,z1,z2,z4,z5,z1235])],[(0,[z0,z1,z2,z3,z4,z1236]),(0,[z0,z1,z210,z110,z3,z4]),(0,[z59,z0,z86,z323,z4,z5]),(0,[z0,z1,z2,z4,z908,z92])],[(0,[z9,z1,z17,z17,z3,z4]),(0,[z0,z1,z179,z2,z3,z4]),(0,[z0,z1,z46,z146,z3,z5]),(0,[z9,z1,z2,z110,z3,z4]),(0,[z0,z1,z2,z923,z3,z5]),(0,[z0,z221,z2,z356,z51,z5]),(0,[z0,z1,z2,z146,z3,z12]),(0,[z0,z1,z2,z3,z4,z1237]),(0,[z0,z1,z2,z3,z4,z1238])],[(0,[z0,z1,z2,z1239,z4,z5]),(0,[z386,z1,z17,z3,z4,z5]),(0,[z44,z1,z2,z45,z4,z12]),(0,[z0,z607,z2,z74,z4,z5])],[(0,[z7,z8,z2,z3,z4,z439]),(0,[z420,z1,z2,z3,z4,z421]),(0,[z0,z1,z2,z1240,z3,z5]),(0,[z1241,z0,z1,z2,z3,z4])],[(0,[z0,z1,z1242,z3,z4,z5]),(0,[z0,z1,z2,z719,z4,z5]),(0,[z0,z1,z2,z1243,z3,z4])],[(0,[z9,z0,z1,z2,z343,z4]),(0,[z158,z1,z17,z3,z4,z5]),(0,[z9,z1,z17,z3,z65,z4]),(0,[z9,z1,z17,z3,z31,z4]),(0,[z0,z1,z46,z3,z130,z5]),(0,[z0,z1,z2,z3,z4,z1043]),(0,[z0,z645,z2,z74,z4,z5]),(0,[z0,z1,z1244,z3,z4,z5]),(0,[z0,z1,z2,z356,z4,z288]),(0,[z0,z2,z397,z3,z4,z12])]],
   [[(0,[z152,z163,z1,z17,z3,z4]),(0,[z0,z1,z2,z1045,z4,z5]),(0,[z9,z0,z1,z2,z802,z3]),(0,[z0,z2,z3,z580,z4,z21])],[(0,[z0,z1,z975,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z321]),(0,[z0,z1,z2,z3,z1245,z5]),(0,[z0,z1,z800,z3,z4,z21]),(0,[z0,z1,z24,z3,z4,z94])],[(0,[z0,z1,z2,z3,z1246,z5]),(0,[z9,z0,z48,z2,z49,z4]),(0,[z0,z1,z2,z146,z168,z5])],[(0,[z0,z1,z2,z212,z84,z3]),(0,[z0,z1,z2,z3,z4,z1247])],[(0,[z81,z1,z2,z3,z884,z5])],[(0,[z0,z1,z1248,z3,z4,z5]),(0,[z0,z1,z1071,z96,z3,z4]),(0,[z0,z1,z1249,z2,z3,z4])],[],[(0,[z0,z1,z46,z3,z4,z149])],[(0,[z0,z1,z37,z3,z4,z21]),(0,[z27,z53,z17,z3,z4,z5]),(0,[z558,z0,z1,z17,z3,z4]),(0,[z0,z1,z39,z3,z147,z5]),(0,[z0,z1,z110,z3,z4,z5]),(0,[z1,z534,z46,z3,z4,z5]),(0,[z0,z1,z334,z3,z362,z5]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z1,z2,z1250,z3,z4]),(0,[z81,z1,z2,z3,z56,z149]),(0,[z9,z0,z1,z2,z1014,z4]),(0,[z435,z0,z1,z70,z3,z4]),(0,[z9,z1,z2,z594,z3,z4])],[(0,[z0,z1,z2,z3,z4,z201]),(0,[z189,z1,z371,z3,z4,z5]),(0,[z0,z1,z2,z953,z4,z5]),(0,[z9,z0,z1,z810,z3,z4]),(0,[z0,z1,z2,z90,z89,z5]),(0,[z0,z1,z2,z3,z4,z1251]),(0,[z0,z315,z2,z3,z32,z5]),(0,[z325,z0,z2,z3,z4,z12]),(0,[z0,z1,z2,z49,z211,z5]),(0,[z0,z2,z3,z4,z12,z804])],[(0,[z0,z1,z2,z343,z4,z201]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z0,z1,z17,z3,z4,z148]),(0,[z9,z1,z39,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z1252]),(0,[z9,z0,z976,z2,z3,z4]),(0,[z0,z1,z2,z1253,z4,z5]),(0,[z0,z1,z2,z3,z1254,z5]),(0,[z0,z1,z2,z3,z21,z136])],[(0,[z0,z1,z2,z1255,z3,z4]),(0,[z1,z181,z17,z3,z4,z5]),(0,[z0,z17,z3,z4,z12,z21]),(0,[z44,z1,z2,z719,z4,z5]),(0,[z0,z1,z1256,z3,z4,z5])],[(0,[z0,z808,z2,z3,z4,z5]),(0,[z10,z1,z305,z101,z4,z5]),(0,[z0,z1,z2,z1257,z3,z4]),(0,[z0,z1,z2,z3,z211,z5])],[(0,[z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z1258,z3,z4,z5])],[(0,[z0,z1,z215,z3,z4,z5]),(0,[z9,z0,z1,z754,z3,z4]),(0,[z0,z1,z2,z323,z4,z60]),(0,[z0,z1,z2,z90,z107,z5])],[(0,[z1,z188,z17,z3,z4,z5]),(0,[z9,z1,z17,z3,z4,z99]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z474,z1,z2,z45,z4,z5]),(0,[z59,z29,z0,z86,z3,z4]),(0,[z59,z0,z550,z3,z4,z5]),(0,[z1259,z0,z1,z2,z3,z4]),(0,[z920,z1,z2,z3,z4,z21])]],
   [[(0,[z0,z1,z17,z1009,z4,z5]),(0,[z890,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1260])],[(0,[z0,z1,z46,z179,z3,z4]),(0,[z9,z1,z261,z17,z3,z4]),(0,[z9,z1,z110,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z1261])],[(0,[z0,z1,z2,z3,z4,z1068]),(0,[z0,z1,z2,z3,z4,z331]),(0,[z1262,z1,z2,z3,z4,z5])],[(0,[z29,z0,z1,z1204,z3,z4])],[(0,[z0,z1,z371,z3,z4,z21]),(0,[z125,z1,z2,z3,z130,z5]),(0,[z0,z300,z2,z3,z4,z12])],[(0,[z0,z48,z2,z49,z4,z12]),(0,[z0,z1,z930,z3,z4,z21])],[(0,[z0,z1,z2,z3,z1263,z5]),(0,[z0,z1,z46,z203,z3,z4]),(0,[z477,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z355,z4,z12])],[(0,[z0,z1,z1264,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1076]),(0,[z23,z0,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z1265])],[(0,[z34,z0,z1,z17,z3,z4]),(0,[z1,z46,z579,z3,z4,z5]),(0,[z0,z1,z188,z3,z4,z75]),(0,[z0,z1,z103,z443,z4,z5]),(0,[z0,z1,z2,z467,z84,z3])],[(0,[z0,z1,z2,z3,z4,z1266]),(0,[z0,z1,z17,z467,z3,z4]),(0,[z0,z1,z210,z392,z3,z4]),(0,[z29,z0,z1,z195,z3,z4]),(0,[z0,z1,z2,z3,z4,z1267]),(0,[z0,z1,z1268,z3,z4,z5]),(0,[z0,z106,z2,z3,z32,z12]),(0,[z0,z1,z2,z134,z4,z405])],[(0,[z9,z1,z17,z101,z3,z4]),(0,[z0,z1,z17,z3,z1023,z5]),(0,[z0,z2,z743,z3,z4,z5]),(0,[z0,z1,z164,z682,z4,z5]),(0,[z0,z221,z2,z3,z51,z396])],[(0,[z779,z0,z1,z2,z3,z4]),(0,[z0,z1,z46,z3,z4,z439]),(0,[z0,z1,z3,z4,z1084,z5])],[(0,[z9,z0,z1,z1085,z3,z4]),(0,[z9,z512,z1,z2,z3,z4]),(0,[z1269,z1,z2,z3,z4,z5])],[(0,[z213,z1,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1270]),(0,[z0,z1,z13,z164,z4,z5])],[(0,[z420,z7,z1,z2,z3,z4]),(0,[z0,z1,z17,z3,z4,z21]),(1,[z0,z1,z840,z4,z5])],[(0,[z9,z1,z17,z3,z4,z530]),(0,[z0,z1,z17,z3,z4,z1033])]],
   [[(0,[z9,z1,z17,z350,z3,z4]),(0,[z9,z0,z1,z750,z3,z4]),(0,[z0,z1,z2,z3,z4,z1271])],[(0,[z0,z1,z2,z274,z4,z28]),(0,[z0,z1,z17,z323,z4,z5]),(0,[z118,z9,z1,z2,z3,z4]),(0,[z287,z0,z1,z2,z193,z4])],[(0,[z0,z1,z17,z3,z4,z1036]),(0,[z0,z176,z244,z3,z4,z5]),(0,[z0,z1,z1272,z3,z4,z5]),(0,[z0,z1,z46,z90,z26,z5]),(0,[z0,z1,z46,z3,z4,z514]),(0,[z0,z1,z2,z1273,z3,z4]),(0,[z0,z1274,z1,z2,z3,z4])],[(0,[z1,z284,z53,z17,z3,z4]),(0,[z9,z97,z1,z17,z3,z4]),(1,[z0,z1,z810,z3,z4]),(0,[z0,z1,z2,z1275,z3,z12])],[(0,[z9,z0,z1,z37,z3,z4]),(0,[z0,z1,z1276,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z789]),(0,[z0,z1,z185,z3,z4,z227]),(0,[z0,z346,z2,z3,z4,z21])],[(0,[z0,z1,z17,z3,z4,z199]),(0,[z0,z1277,z2,z3,z4,z5]),(0,[z0,z1,z2,z269,z467,z3])],[(0,[z53,z244,z17,z3,z4,z5]),(0,[z327,z9,z1,z17,z3,z4]),(0,[z1,z17,z3,z4,z562,z5]),(0,[z0,z1,z46,z737,z3,z4]),(0,[z0,z1,z2,z3,z4,z1096]),(0,[z740,z189,z1,z2,z3,z4]),(0,[z0,z1,z2,z1278,z3,z4])],[(0,[z329,z1,z17,z3,z4,z5])],[(0,[z9,z0,z1,z2,z269,z3]),(0,[z0,z1,z734,z3,z4,z5]),(0,[z9,z0,z97,z2,z74,z4])],[(0,[z0,z1,z2,z3,z738,z5]),(0,[z0,z1,z371,z3,z4,z1060]),(0,[z0,z1,z17,z112,z4,z5]),(0,[z0,z1,z17,z273,z4,z168]),(0,[z1279,z1,z2,z3,z4,z5]),(0,[z0,z97,z2,z74,z4,z21])],[(0,[z458,z1,z17,z3,z4,z5]),(0,[z29,z239,z1,z2,z3,z4]),(0,[z0,z1,z2,z519,z4,z359]),(0,[z1104,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1280,z3,z4,z5]),(1,[z1,z261,z17,z3,z4]),(0,[z9,z0,z1,z2,z84,z3]),(0,[z0,z1,z318,z3,z4,z21]),(0,[z0,z1281,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1282])],[(0,[z0,z1,z2,z849,z3,z4]),(0,[z0,z1,z2,z269,z3,z5]),(0,[z0,z1,z2,z3,z1283,z5])],[(0,[z0,z1,z2,z3,z388,z201]),(0,[z0,z1,z16,z164,z4,z5])],[(0,[z0,z1,z137,z3,z4,z5]),(0,[z58,z0,z1,z3,z4,z80]),(0,[z0,z1,z2,z1284,z4,z5]),(0,[z0,z1,z2,z356,z4,z5]),(0,[z0,z1,z2,z20,z138,z12]),(0,[z0,z1,z2,z98,z4,z5])],[(0,[z0,z1,z46,z274,z4,z5]),(0,[z627,z1,z17,z3,z4,z5])]],
   [[(0,[z0,z1,z46,z3,z4,z806]),(0,[z0,z1,z175,z290,z4,z5]),(0,[z0,z1,z2,z3,z4,z1108]),(0,[z29,z458,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1285]),(0,[z0,z1,z2,z3,z4,z1286]),(0,[z0,z1,z2,z1287,z4,z5])],[(0,[z0,z1,z1288,z3,z4,z5]),(0,[z7,z1,z17,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z857]),(0,[z0,z1,z348,z3,z4,z227]),(0,[z0,z1,z2,z1289,z4,z5])],[(0,[z0,z1,z737,z17,z3,z4]),(0,[z0,z106,z2,z3,z32,z249]),(0,[z167,z0,z1,z3,z4,z47]),(0,[z0,z1,z2,z3,z4,z1290])],[(0,[z0,z1,z37,z3,z76,z5]),(0,[z0,z1,z371,z3,z4,z1074]),(0,[z9,z0,z1,z541,z3,z4]),(0,[z0,z1,z1189,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1291])],[(0,[z0,z1,z541,z3,z4,z21])],[(0,[z0,z2,z3,z1194,z4,z5]),(0,[z9,z0,z1,z2,z1213,z4]),(0,[z29,z0,z1,z1292,z3,z4]),(0,[z532,z1,z2,z3,z4,z21]),(0,[z0,z1,z210,z3,z4,z227])],[(0,[z0,z1,z46,z3,z4,z405]),(0,[z29,z0,z1,z3,z453,z4]),(0,[z29,z0,z1,z102,z65,z4]),(0,[z0,z1,z2,z3,z141,z21]),(0,[z0,z1,z1293,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1113,z5]),(0,[z9,z1,z17,z3,z4,z168]),(0,[z0,z1,z2,z864,z4,z5]),(0,[z0,z1,z2,z3,z4,z288]),(0,[z0,z1,z2,z4,z12,z1116])],[(0,[z9,z0,z1,z2,z3,z388]),(0,[z465,z9,z1,z17,z3,z4]),(0,[z0,z1,z261,z70,z3,z4]),(0,[z0,z1,z2,z3,z314,z159]),(0,[z1294,z0,z1,z2,z3,z4]),(0,[z0,z270,z2,z3,z4,z804]),(0,[z0,z1,z2,z3,z4,z1295]),(0,[z0,z1,z1296,z3,z4,z5])],[(0,[z29,z9,z1,z110,z3,z4]),(0,[z0,z48,z195,z49,z4,z5])],[(0,[z0,z1,z2,z3,z1297,z5]),(0,[z9,z0,z1,z96,z3,z4]),(0,[z0,z1,z2,z3,z4,z1298]),(0,[z0,z1,z17,z35,z3,z4]),(0,[z0,z365,z2,z3,z51,z5]),(0,[z58,z0,z1,z3,z4,z127]),(0,[z0,z1,z278,z3,z31,z12]),(1,[z0,z1,z2,z4,z908])],[(0,[z9,z1,z737,z17,z3,z4]),(0,[z0,z1,z46,z3,z4,z817]),(0,[z9,z10,z1,z2,z101,z4]),(0,[z0,z1,z1299,z3,z4,z5]),(0,[z0,z1,z2,z3,z142,z792])],[(0,[z152,z1,z46,z17,z3,z4]),(0,[z435,z9,z1,z17,z3,z4]),(0,[z125,z1,z3,z31,z4,z5]),(0,[z0,z1,z470,z3,z4,z12]),(0,[z0,z1,z2,z3,z1300,z5])],[(0,[z0,z1,z17,z1075,z3,z4]),(0,[z0,z1,z2,z3,z4,z1301]),(0,[z9,z0,z1302,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1303]),(0,[z0,z522,z2,z3,z4,z12])],[(0,[z29,z0,z1,z215,z3,z4]),(0,[z0,z1,z305,z3,z4,z21]),(0,[z0,z1,z743,z3,z4,z5]),(0,[z1304,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z792])],[(0,[z0,z1,z2,z3,z262,z514]),(0,[z0,z1,z1305,z3,z4,z5])]],
   [[(0,[z44,z1,z215,z45,z4,z5]),(0,[z29,z0,z1,z2,z3,z136]),(0,[z0,z1,z2,z3,z4,z1306])],[(0,[z0,z1,z1307,z3,z4,z5]),(0,[z0,z1,z1308,z3,z4,z5]),(0,[z0,z1,z2,z1309,z4,z5]),(0,[z0,z1,z1310,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1311])],[(0,[z0,z1,z2,z3,z1127,z5]),(0,[z1,z17,z3,z4,z80,z5]),(0,[z9,z0,z1,z137,z3,z4]),(0,[z0,z1,z2,z3,z130,z12]),(0,[z263,z0,z1,z3,z4,z127]),(0,[z0,z1,z2,z134,z578,z4])],[(0,[z1,z53,z17,z3,z4,z5]),(0,[z44,z1,z2,z467,z45,z4]),(0,[z0,z1,z2,z134,z193,z4]),(0,[z59,z189,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1312]),(0,[z1313,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1314])],[(0,[z0,z1302,z2,z3,z4,z5]),(0,[z10,z1,z369,z101,z4,z5])],[(0,[z0,z508,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z4,z1315])],[(0,[z0,z1,z2,z84,z3,z5]),(0,[z0,z1,z1292,z3,z4,z5]),(0,[z0,z1,z1130,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1316])],[(0,[z0,z1,z1317,z3,z4,z5]),(0,[z0,z1,z17,z212,z3,z4]),(0,[z9,z569,z1,z2,z3,z4]),(0,[z189,z1,z2,z3,z4,z21]),(1,[z0,z1,z2,z90,z203])],[(0,[z0,z1,z2,z343,z388,z5]),(0,[z34,z0,z1,z96,z3,z4]),(0,[z150,z0,z1,z17,z3,z4]),(0,[z0,z1,z17,z1091,z3,z4]),(0,[z349,z1,z17,z3,z4,z5]),(0,[z9,z0,z1,z103,z164,z4]),(0,[z29,z0,z1,z2,z90,z26]),(0,[z0,z1,z1027,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1318]),(0,[z0,z1,z2,z3,z4,z1319])],[(0,[z0,z1,z17,z3,z76,z5]),(0,[z782,z53,z2,z3,z4,z5]),(0,[z0,z1,z762,z3,z4,z5]),(0,[z291,z1,z17,z3,z4,z5]),(0,[z9,z0,z1,z1175,z3,z4]),(0,[z1320,z1,z2,z3,z4,z5]),(0,[z0,z1,z1321,z2,z3,z4]),(0,[z0,z1,z3,z4,z1322,z5])],[(0,[z81,z1,z17,z3,z56,z5]),(0,[z1323,z0,z1,z2,z3,z4]),(0,[z189,z1,z2,z323,z4,z5]),(0,[z0,z1,z2,z3,z5,z838]),(0,[z0,z1,z2,z273,z4,z908])],[(0,[z0,z1,z1324,z3,z4,z5]),(0,[z125,z1,z2,z3,z4,z60])],[(0,[z0,z1,z751,z2,z3,z4]),(0,[z0,z1,z416,z3,z4,z12]),(0,[z0,z1,z103,z164,z4,z21]),(0,[z0,z1,z2,z3,z177,z433])],[(0,[z9,z0,z1,z17,z3,z4]),(0,[z0,z1,z17,z3,z4,z91]),(0,[z1,z46,z625,z3,z4,z5]),(0,[z9,z0,z1,z839,z3,z4]),(0,[z9,z0,z1,z2,z3,z141]),(0,[z0,z1,z2,z3,z4,z396]),(0,[z0,z1,z2,z222,z51,z5]),(0,[z0,z1,z2,z134,z4,z92])],[(0,[z153,z9,z1,z17,z3,z4]),(0,[z0,z1,z899,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z1325]),(0,[z29,z1,z2,z3,z4,z841])],[(0,[z10,z1,z2,z101,z4,z148]),(0,[z0,z1,z2,z140,z138,z5]),(0,[z1233,z1,z2,z3,z4,z5]),(0,[z0,z1,z278,z3,z780,z5])]],
   [[(0,[z9,z347,z1,z17,z3,z4]),(0,[z152,z9,z1,z17,z3,z4]),(0,[z0,z1,z1132,z17,z4,z5]),(0,[z1,z17,z597,z3,z4,z5]),(0,[z152,z1,z2,z3,z4,z30]),(0,[z495,z1,z17,z3,z4,z5]),(0,[z0,z1,z46,z810,z3,z4]),(0,[z29,z208,z1,z2,z3,z4]),(0,[z0,z1,z1326,z3,z4,z5])],[(0,[z59,z9,z1,z17,z3,z4]),(0,[z0,z1,z2,z4,z5,z1327]),(0,[z1,z2,z3,z4,z21,z1210]),(0,[z0,z1,z2,z4,z168,z908])],[(0,[z9,z42,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z404]),(0,[z0,z1,z1328,z3,z4,z5])],[],[(0,[z0,z1,z810,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z1329]),(0,[z1330,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z450,z99]),(0,[z0,z1,z2,z3,z4,z1331]),(0,[z0,z1,z760,z3,z4,z12])],[(1,[z1,z737,z17,z3,z4]),(0,[z44,z1,z2,z45,z4,z5]),(0,[z0,z1,z2,z323,z4,z21])],[(0,[z0,z1,z1332,z3,z4,z5]),(0,[z0,z1,z563,z3,z4,z21]),(0,[z153,z0,z1,z2,z3,z429]),(0,[z9,z0,z1,z2,z20,z138]),(0,[z1333,z0,z1,z2,z3,z4]),(0,[z0,z11,z542,z3,z4,z5]),(0,[z0,z2,z3,z4,z21,z254])],[(0,[z152,z0,z1,z3,z4,z47]),(0,[z0,z919,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1334])],[(0,[z0,z1,z2,z3,z4,z1335]),(0,[z0,z1,z179,z17,z3,z4]),(0,[z55,z1,z70,z3,z4,z5]),(0,[z0,z1,z46,z222,z4,z5]),(0,[z0,z1,z46,z120,z3,z99]),(0,[z0,z1,z46,z4,z5,z299]),(0,[z29,z9,z1,z392,z3,z4]),(0,[z9,z0,z1,z470,z3,z4]),(0,[z29,z0,z1,z2,z323,z4]),(0,[z0,z14,z2,z49,z4,z5]),(0,[z0,z1,z2,z356,z4,z396]),(0,[z0,z1,z1336,z3,z4,z5])],[(0,[z55,z34,z1,z2,z3,z4]),(0,[z9,z48,z1,z17,z3,z4]),(0,[z0,z1,z2,z1337,z3,z4]),(0,[z0,z1,z470,z3,z262,z5])],[(0,[z0,z1,z2,z3,z4,z1338]),(0,[z0,z1,z867,z2,z4,z5]),(0,[z7,z1,z1317,z3,z4,z5]),(0,[z0,z270,z261,z2,z3,z4]),(0,[z0,z1339,z2,z3,z4,z5])],[(0,[z34,z0,z1,z839,z3,z4]),(0,[z1,z1317,z17,z3,z4,z5]),(0,[z1340,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1341,z3,z4]),(0,[z0,z1,z2,z273,z4,z548])],[(0,[z55,z1,z46,z3,z4,z5]),(0,[z1,z17,z605,z3,z4,z5]),(0,[z0,z1,z1201,z3,z4,z5]),(1,[z1,z2,z3,z884,z5]),(0,[z0,z1,z2,z3,z4,z1342]),(0,[z125,z1,z102,z3,z4,z5]),(0,[z0,z615,z2,z49,z4,z5]),(0,[z0,z1,z1343,z3,z4,z5]),(0,[z0,z1,z2,z90,z26,z52])],[(0,[z9,z0,z1,z305,z3,z4]),(0,[z0,z1,z2,z112,z4,z21]),(0,[z0,z1,z2,z233,z4,z251])],[(0,[z125,z1,z17,z3,z4,z5]),(0,[z44,z150,z1,z2,z3,z4])],[(0,[z271,z0,z1,z2,z111,z4])]],
   [[(0,[z532,z1,z46,z3,z4,z5]),(0,[z81,z1,z541,z3,z56,z5]),(0,[z0,z1,z1344,z3,z4,z5])],[(0,[z29,z0,z1,z46,z3,z4]),(0,[z9,z1,z296,z17,z3,z4]),(0,[z77,z0,z129,z3,z4,z5]),(0,[z0,z1,z46,z3,z141,z5]),(0,[z0,z1,z2,z4,z21,z1235])],[(0,[z0,z1,z2,z3,z4,z1345]),(0,[z0,z1,z102,z65,z4,z12])],[(0,[z0,z1,z2,z3,z4,z1346]),(0,[z55,z1,z46,z3,z4,z75]),(0,[z10,z1,z2,z101,z4,z21]),(0,[z9,z1,z70,z3,z4,z54]),(0,[z627,z1,z2,z3,z4,z21])],[(1,[z1,z2,z719,z4,z5]),(0,[z0,z1,z2,z90,z259,z5]),(0,[z0,z1,z164,z840,z4,z5]),(0,[z0,z1,z2,z1347,z4,z5]),(0,[z118,z627,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1225,z5]),(0,[z420,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z946]),(0,[z150,z1,z17,z3,z4,z21]),(0,[z59,z0,z86,z3,z4,z12]),(0,[z0,z1,z2,z90,z26,z12]),(0,[z0,z1,z2,z146,z3,z159])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z384,z0,z1,z46,z3,z4]),(0,[z0,z1,z2,z3,z950,z5]),(0,[z55,z1,z46,z3,z4,z80]),(0,[z9,z1,z392,z3,z4,z54])],[(0,[z0,z1,z2,z343,z4,z5]),(0,[z0,z1,z891,z2,z3,z4]),(0,[z9,z1,z46,z3,z4,z54])],[(0,[z0,z1,z37,z3,z4,z28]),(0,[z0,z1,z1348,z3,z4,z5]),(0,[z1,z284,z17,z3,z4,z5]),(0,[z0,z1,z46,z3,z4,z432]),(0,[z0,z1,z2,z3,z4,z1349]),(0,[z0,z1,z3,z31,z493,z5])],[(0,[z0,z621,z2,z3,z4,z21])],[(0,[z7,z68,z2,z3,z4,z5]),(0,[z0,z1,z348,z3,z4,z5]),(0,[z9,z1,z17,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z1350]),(0,[z1,z2,z3,z4,z884,z5]),(0,[z1131,z0,z1,z2,z3,z4]),(0,[z29,z0,z1,z2,z222,z4]),(0,[z0,z1,z2,z3,z4,z1351])],[(0,[z7,z1,z179,z17,z3,z4]),(0,[z58,z0,z1,z179,z3,z4]),(0,[z152,z0,z1,z110,z3,z4]),(0,[z0,z1,z2,z3,z1352,z5]),(0,[z0,z1,z2,z1353,z3,z4])],[(0,[z0,z1,z3,z1354,z4,z5]),(0,[z0,z1,z179,z3,z4,z586]),(0,[z0,z1,z3,z4,z47,z75]),(0,[z0,z452,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z1355]),(0,[z0,z1,z308,z3,z31,z5]),(0,[z0,z1,z2,z138,z5,z591])],[(0,[z0,z1,z2,z1356,z3,z4]),(0,[z0,z1,z2,z3,z4,z75]),(0,[z0,z2,z3,z942,z4,z5])],[(0,[z0,z1,z2,z274,z4,z201]),(0,[z7,z8,z17,z3,z4,z5]),(0,[z0,z1,z2,z964,z4,z5]),(0,[z10,z0,z1,z2,z269,z5]),(0,[z0,z48,z2,z49,z4,z5]),(0,[z0,z643,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z1357,z4])],[(0,[z27,z0,z261,z2,z3,z4]),(0,[z61,z1,z46,z3,z4,z5]),(0,[z0,z1,z2,z355,z4,z5]),(0,[z0,z1,z1046,z3,z4,z5])]],
   [[(0,[z1,z284,z2,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z80]),(0,[z0,z1,z2,z3,z4,z1106]),(0,[z327,z0,z1,z2,z3,z314]),(0,[z0,z1,z2,z111,z4,z92])],[(0,[z34,z7,z8,z2,z3,z4]),(0,[z0,z1,z1358,z3,z4,z5]),(0,[z0,z1,z348,z3,z4,z75]),(0,[z44,z1,z2,z212,z45,z4])],[(0,[z0,z1,z2,z274,z4,z12]),(0,[z44,z9,z1,z17,z3,z4]),(0,[z0,z1,z17,z3,z4,z328]),(0,[z189,z1,z46,z3,z4,z5]),(0,[z465,z0,z1,z392,z3,z4])],[(0,[z29,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1359,z5])],[(0,[z9,z1,z128,z17,z3,z4]),(0,[z0,z1,z2,z3,z1109,z5]),(0,[z506,z0,z261,z2,z3,z4]),(0,[z1079,z1,z2,z3,z4,z21])],[(0,[z9,z1,z17,z3,z4,z26])],[(0,[z0,z1,z37,z3,z4,z12]),(0,[z0,z1,z1360,z3,z4,z5]),(0,[z0,z1,z17,z3,z172,z4]),(0,[z0,z1,z2,z3,z1361,z4]),(0,[z0,z1,z369,z3,z4,z21]),(0,[z1,z2,z3,z4,z5,z729])],[(0,[z0,z1,z3,z1362,z4,z5]),(0,[z0,z1,z2,z3,z142,z241]),(0,[z0,z1,z2,z3,z4,z1363])],[(0,[z384,z0,z1,z2,z3,z4]),(0,[z0,z1,z1364,z3,z4,z5]),(0,[z208,z1,z17,z3,z4,z5]),(0,[z29,z532,z1,z2,z3,z4]),(0,[z985,z1,z2,z3,z4,z21])],[(0,[z0,z1,z46,z3,z4,z60])],[(0,[z9,z1,z17,z3,z147,z4]),(0,[z0,z1,z2,z1195,z4,z5]),(0,[z0,z1,z2,z1365,z3,z4])],[(0,[z0,z1,z17,z3,z4,z22]),(0,[z63,z1,z318,z3,z64,z5]),(0,[z0,z1,z2,z3,z4,z1366])],[(0,[z187,z53,z2,z3,z4,z5]),(0,[z29,z1,z17,z3,z4,z30]),(0,[z0,z1,z392,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z1367]),(0,[z0,z1,z2,z134,z4,z359]),(0,[z0,z1,z2,z1275,z3,z5])],[(0,[z0,z1,z2,z3,z76,z21]),(0,[z0,z1,z46,z3,z4,z918]),(0,[z44,z1,z2,z597,z4,z5]),(0,[z0,z1,z2,z134,z123,z4])],[(0,[z0,z1,z17,z3,z4,z28]),(0,[z0,z1,z46,z3,z142,z159]),(0,[z29,z0,z1,z563,z3,z4]),(0,[z0,z1,z1066,z3,z4,z5]),(0,[z0,z221,z2,z222,z51,z5]),(0,[z0,z1,z2,z3,z4,z1368])],[(0,[z27,z53,z2,z3,z4,z21]),(0,[z0,z1,z46,z3,z4,z510]),(0,[z0,z1,z3,z453,z4,z12])]],
   [[(0,[z9,z1,z703,z2,z3,z4]),(0,[z1369,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z12,z136])],[(0,[z9,z1,z2,z3,z603,z4]),(0,[z125,z1,z296,z3,z4,z5])],[(0,[z9,z0,z1,z369,z3,z4]),(0,[z81,z1,z563,z3,z56,z5]),(0,[z9,z0,z1,z2,z3,z1245]),(0,[z59,z0,z86,z3,z262,z5]),(0,[z0,z1,z2,z120,z3,z405]),(0,[z0,z1,z2,z781,z26,z5])],[(0,[z0,z1,z1370,z2,z3,z4]),(0,[z0,z1,z17,z3,z4,z52]),(0,[z0,z1,z2,z1371,z4,z5]),(0,[z0,z1,z2,z1372,z4,z5]),(0,[z0,z1,z2,z3,z4,z1373]),(0,[z1374,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1325,z5]),(0,[z9,z1,z17,z3,z4,z156]),(0,[z1375,z0,z1,z2,z3,z4])],[(0,[z0,z1,z104,z3,z4,z21]),(0,[z1,z17,z3,z4,z379,z5]),(0,[z0,z1,z2,z1376,z3,z5]),(0,[z81,z0,z1,z2,z394,z5]),(0,[z0,z1,z2,z146,z273,z3])],[(0,[z29,z0,z1,z104,z3,z4]),(0,[z58,z627,z1,z3,z4,z47])],[(0,[z63,z1,z2,z35,z3,z64]),(0,[z9,z0,z1,z2,z356,z4]),(0,[z29,z0,z1,z1196,z3,z4]),(0,[z0,z1,z3,z31,z262,z5]),(0,[z0,z1,z2,z20,z138,z5])],[(0,[z55,z9,z1,z46,z3,z4]),(0,[z0,z1,z2,z1377,z3,z4])],[(0,[z29,z7,z1,z17,z3,z4]),(0,[z576,z1,z17,z3,z4,z5]),(0,[z533,z1,z17,z3,z4,z5]),(0,[z0,z1,z3,z1378,z4,z5])],[(0,[z0,z1,z2,z3,z388,z5]),(0,[z150,z1,z53,z2,z3,z4]),(0,[z370,z1,z17,z3,z4,z5]),(0,[z29,z0,z1,z1199,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1379]),(0,[z152,z1,z53,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z1380]),(0,[z34,z0,z1,z70,z3,z4]),(0,[z29,z0,z11,z296,z3,z4]),(0,[z0,z1,z1381,z3,z4,z5]),(0,[z0,z1,z105,z3,z156,z21])],[(0,[z0,z1,z777,z3,z4,z5]),(0,[z0,z1,z17,z3,z4,z12])],[(0,[z9,z0,z1,z2,z3,z211]),(0,[z29,z0,z1,z278,z3,z31])],[(0,[z384,z7,z1,z17,z3,z4]),(0,[z10,z1,z46,z101,z4,z5]),(0,[z0,z1,z2,z394,z4,z5]),(0,[z1333,z125,z1,z2,z3,z4]),(0,[z0,z1,z2,z134,z136,z92])],[(0,[z1,z371,z17,z3,z4,z5]),(0,[z9,z1,z17,z3,z142,z4]),(0,[z1,z17,z3,z4,z670,z5]),(0,[z0,z1,z46,z3,z958,z5]),(0,[z0,z1,z351,z3,z509,z5]),(0,[z0,z1,z1188,z3,z4,z5]),(0,[z125,z1,z86,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z792])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 478).take 481) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 959).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1438).take 129) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1567)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [478, 481, 479, 129] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 90).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 173).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 248).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 324).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 408).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 483).take 29).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [90, 83, 75, 76, 84, 75, 29] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38705

theorem PEqualNP.Outside.L_meta_38705 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4274571464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4274571464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38705.solve