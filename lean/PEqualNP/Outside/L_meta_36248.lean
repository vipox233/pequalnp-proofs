import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36248

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2004200a886315c0#64 ++ 0x82004200a886315c#64 ++ 0xd02c619f88e73fcd#64 ++ 0xfd02c619f88e73fc#64 : BitVec 256),
   (0x404591260b284c50#64 ++ 0xc404591260b284c5#64 ++ 0xb4d791660f38ccfb#64 ++ 0xbb4d791660f38ccf#64 : BitVec 256),
   (0x811806583015b0a9#64 ++ 0x0811806583015b0a#64 ++ 0x7b181e78703ff0ff#64 ++ 0xf7b181e78703ff0f#64 : BitVec 256),
   (0x02e01b805580ea02#64 ++ 0x102e01b805580ea0#64 ++ 0xfbe01f807fc0ff0f#64 ++ 0x6fbe01f807fc0ff0#64 : BitVec 256),
   (0x07bee0006efe0003#64 ++ 0xe07bee0006efe000#64 ++ 0xf7ffe0007fff0007#64 ++ 0x1f7ffe0007fff000#64 : BitVec 256),
   (0x03fb5df50000000c#64 ++ 0x003fb5df50000000#64 ++ 0xffffffff80000000#64 ++ 0xfffffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01f807fc0ff0f 0x6fbe01f807fc0ff0

def z1 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff80000000 0xfffffffff8000000

def z2 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0007fff0007 0x1f7ffe0007fff000

def z3 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c619f88e73fcd 0xfd02c619f88e73fc

def z4 : W := mkw 0x400580260b284c50 0xc400580260b284c5 0x041780660f38ccfb 0x9041780660f38ccf

def z5 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d791660f38ccfb 0xbb4d791660f38ccf

def z6 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181e78703ff0ff 0xf7b181e78703ff0f

def z7 : W := mkw 0x4041112601004c50 0x04041112601004c5 0xb0c011660f00ccfb 0xab0c011660f00ccf

def z8 : W := mkw 0x0041112400000000 0x0004111240000000 0x84c7810600000000 0x084c781060000000

def z9 : W := mkw 0x2404a00aeeff15c3 0xe2404a00aeeff15c 0x000000007fff3fcf 0x0000000007fff3fc

def z10 : W := mkw 0x82e01fd85581faaa 0x182e01fd85581faa 0xfbe01ff87fc0ffff 0xefbe01ff87fc0fff

def z11 : W := mkw 0x4001802402080010 0x4400180240208001 0x0413806000180030 0x0041380600018003

def z12 : W := mkw 0x000002001000a000 0x0000002001000a00 0x7b001e007000f00f 0x67b001e007000f00

def z13 : W := mkw 0x83f81fd87595faab 0x183f81fd87595faa 0xfbf81ff87fffffff 0xffbf81ff87ffffff

def z14 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0x7b001e007fc0ff0f 0x67b001e007fc0ff0

def z15 : W := mkw 0x02e359a500000004 0x002e359a50000000 0xb4f7f1e780000000 0xbb4f7f1e78000000

def z16 : W := mkw 0x000480000a280000 0xc000480000a28000 0x000000000f380003 0x0000000000f38000

def z17 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d791660f000c00 0xbb4d791660f000c0

def z18 : W := mkw 0x43fbddf50308481c 0x443fbddf50308481 0xffffffff8718c032 0xfffffffff8718c03

def z19 : W := mkw 0x0118045000000008 0x0011804500000000 0x7b181e7800000000 0xf7b181e780000000

def z20 : W := mkw 0x03fb5ff55580ea0e 0x103fb5ff55580ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0xd020018008c03f0d 0x6d020018008c03f0

def z22 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x802c619f88e70fc0 0x9802c619f88e70fc

def z23 : W := mkw 0x02e0198045804a02 0x102e0198045804a0 0x80e001800fc00f00 0x080e001800fc00f0

def z24 : W := mkw 0x81180458201510a9 0x081180458201510a 0x00180078003f00f0 0x900180078003f00f

def z25 : W := mkw 0x851ca6587effb0ab 0xe851ca6587effb0a 0x7b181e787ffff0ff 0xf7b181e787ffff0f

def z26 : W := mkw 0x2004200288620540 0x8200420028862054 0x0000000008c00f00 0x00000000008c00f0

def z27 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x9004010608e73fcd 0xb9004010608e73fc

def z28 : W := mkw 0x02e359a500000004 0x002e359a50000000 0x84e7e18780000000 0x084e7e1878000000

def z29 : W := mkw 0x83fb5ffd3015b0ad 0x083fb5ffd3015b0a 0xfffffffff03ff0ff 0xffffffffff03ff0f

def z30 : W := mkw 0x06a6e0004eea0002 0xe06a6e0004eea000 0x84e7e0000fc00000 0x084e7e0000fc0000

def z31 : W := mkw 0x07ba600064d60003 0x207ba600064d6000 0x4328600070c70004 0x04328600070c7000

def z32 : W := mkw 0x000480000a280000 0xc000480000a28000 0xb4d790600f38c0fb 0xbb4d790600f38c0f

def z33 : W := mkw 0xc11d847e2a3d14f9 0xcc11d847e2a3d14f 0x041f807e003f00f0 0x9041f807e003f00f

def z34 : W := mkw 0x02e0198000000000 0x002e019800000000 0x80e0018000000000 0x080e001800000000

def z35 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4f791e60ff8ffff 0xff4f791e60ff8fff

def z36 : W := mkw 0x47fff1266ffe4c53 0xe47fff1266ffe4c5 0xf7fff1667fffccff 0xbf7fff1667fffccf

def z37 : W := mkw 0x26a6e00aceeb15c2 0xe26a6e00aceeb15c 0xd4efe19f8fe73fcd 0xfd4efe19f8fe73fc

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x301010600038c0fb 0xb301010600038c0f

def z39 : W := mkw 0xc15d977e3b3dfcf9 0xcc15d977e3b3dfcf 0xffdf9f7e7f3ffcff 0xfffdf9f7e7f3ffcf

def z40 : W := mkw 0x011b44750000000c 0x0011b44750000000 0x0413806000000000 0x0041380600000000

def z41 : W := mkw 0x415fd5770b284c5c 0xc415fd5770b284c5 0xb4dff17f8f38ccfb 0xbb4dff17f8f38ccf

def z42 : W := mkw 0x07fadb80779cea03 0x707fadb80779cea0 0x2fd39e007718c002 0x02fd39e007718c00

def z43 : W := mkw 0x43ffddf70b284c5c 0xc43ffddf70b284c5 0xffffffff8f38ccfb 0xfffffffff8f38ccf

def z44 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0x27d3800077180002 0x027d380007718000

def z45 : W := mkw 0x03fa598000000000 0x003fa59800000000 0xffffff8000000000 0x7ffffff800000000

def z46 : W := mkw 0x07fb7df564d6000f 0x207fb7df564d6000 0xfffffffff0c70004 0xffffffffff0c7000

def z47 : W := mkw 0x03fb59a500000004 0x003fb59a50000000 0xf7ffe18780000000 0x1f7ffe1878000000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x7b001e0000000000 0x67b001e000000000

def z49 : W := mkw 0x211f647f886315cc 0x8211f647f886315c 0x041fe07f802700c0 0x9041fe07f802700c

def z50 : W := mkw 0x2004200288620540 0x8200420028862054 0x8024618788c00f00 0x08024618788c00f0

def z51 : W := mkw 0xa11c265ab877b5e9 0x8a11c265ab877b5e 0xfb3c7ffff8ffffff 0xffb3c7ffff8fffff

def z52 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x27dfe000773f0002 0x127dfe000773f000

def z53 : W := mkw 0x2000200880431180 0x0200020088043118 0x0000000000c73304 0x00000000000c7330

def z54 : W := mkw 0x000480000a280000 0xc000480000a28000 0xb4d780000f380003 0x1b4d780000f38000

def z55 : W := mkw 0x02e35df50000000c 0x002e35df50000000 0x8ce7ffff80000000 0xe8ce7ffff8000000

def z56 : W := mkw 0x4445b1266ffe4c53 0xe4445b1266ffe4c5 0xb4d791667fffccff 0xbb4d791667fffccf

def z57 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x2bc01e007fc0ff0f 0x02bc01e007fc0ff0

def z58 : W := mkw 0x03ba4cd10000000c 0x003ba4cd10000000 0x4b286e9980000000 0x44b286e998000000

def z59 : W := mkw 0xa7bee65afeffb5eb 0xea7bee65afeffb5e 0xffffffffffffffff 0xffffffffffffffff

def z60 : W := mkw 0x40459df70b284c5c 0xc40459df70b284c5 0xbcd79fff8f38ccfb 0xfbcd79fff8f38ccf

def z61 : W := mkw 0x0118045000000008 0x0011804500000000 0x4b080e1800000000 0x44b080e180000000

def z62 : W := mkw 0x800006581001b0a8 0x0800006581001b0a 0x08001e780000f0f8 0xe08001e780000f0f

def z63 : W := mkw 0x0400200064d60003 0x20400200064d6000 0x0000000070c70004 0x00000000070c7000

def z64 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0x77db8000773f0007 0x177db8000773f000

def z65 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x4b080e1870073004 0x44b080e187007300

def z66 : W := mkw 0x800006581001b0a8 0x0800006581001b0a 0x7b001e787000f0ff 0xe7b001e787000f0f

def z67 : W := mkw 0x2004220a9863b5c0 0x82004220a9863b5c 0xfb2c7f9ff8e7ffcf 0xffb2c7f9ff8e7ffc

def z68 : W := mkw 0x27fffdffeeff15cf 0xe27fffdffeeff15c 0xffffffffffff3fcf 0xfffffffffffff3fc

def z69 : W := mkw 0xa11c265ab877b5e9 0x8a11c265ab877b5e 0x7b181e7878ffffff 0xf7b181e7878fffff

def z70 : W := mkw 0xc041177e1101fcf8 0x0c041177e1101fcf 0x08001f7e0000fcf8 0xe08001f7e0000fcf

def z71 : W := mkw 0x011b44750000000c 0x0011b44750000000 0x041fe07f80000000 0x9041fe07f8000000

def z72 : W := mkw 0x02e0198000000000 0x002e019800000000 0xfbe01f8000000000 0x6fbe01f800000000

def z73 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c619f802700c0 0xfd02c619f802700c

def z74 : W := mkw 0x02a00a805580ea02 0x102a00a805580ea0 0x4b200e807fc0ff0f 0x44b200e807fc0ff0

def z75 : W := mkw 0x0004000a082114c0 0x80004000a082114c 0xd00c011e08273ccd 0xfd00c011e08273cc

def z76 : W := mkw 0x0404a2007ffeea03 0xf0404a2007ffeea0 0x000000007fffff0f 0x0000000007fffff0

def z77 : W := mkw 0x4001002600000450 0x0400100260000045 0x00000066000000f0 0x800000066000000f

def z78 : W := mkw 0x0041112400000000 0x0004111240000000 0xb4d7916600000000 0xbb4d791660000000

def z79 : W := mkw 0x811c86583a3db0a9 0xc811c86583a3db0a 0xffdf9e787f3ff0ff 0xfffdf9e787f3ff0f

def z80 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xcfefef9f80000000 0x4cfefef9f8000000

def z81 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x24d390600f38ccfb 0x024d390600f38ccf

def z82 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xfffffe6000000000 0x1fffffe600000000

def z83 : W := mkw 0x06e6fb805feaea02 0xf06e6fb805feaea0 0xffe7ff807fc0ff0f 0x6ffe7ff807fc0ff0

def z84 : W := mkw 0x22e03b88d5c3fb82 0x122e03b88d5c3fb8 0xfbe87f99ffc7ff0f 0x6fbe87f99ffc7ff0

def z85 : W := mkw 0x0000000800011080 0x0000000080001108 0x50080018002730cd 0xf50080018002730c

def z86 : W := mkw 0x83fb5ffd7595faaf 0x183fb5ffd7595faa 0xffffffffffffffff 0xffffffffffffffff

def z87 : W := mkw 0x27bee00aeeff15c3 0xe27bee00aeeff15c 0xf7ffe01fffff00c7 0x9f7ffe01fffff00c

def z88 : W := mkw 0xa11c265ab877b5e9 0x8a11c265ab877b5e 0xdb2c6f9ff8e73fcd 0xfdb2c6f9ff8e73fc

def z89 : W := mkw 0x011a400000000000 0x0011a40000000000 0x041fe00000000000 0x1041fe0000000000

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x8020018008c00f00 0x08020018008c00f0

def z91 : W := mkw 0x0000000800011080 0x0000000080001108 0x00000018000030c8 0xe00000018000030c

def z92 : W := mkw 0x2004220adde3ffc2 0x92004220adde3ffc 0xd02c619fffe7ffcf 0xfd02c619fffe7ffc

def z93 : W := mkw 0x0004200008620000 0x8000420000862000 0x000c600000270000 0x1000c60000027000

def z94 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff88c03f0d 0xfffffffff88c03f0

def z95 : W := mkw 0x2000200880431180 0x0200020088043118 0x0008601980070000 0x0000860198007000

def z96 : W := mkw 0x22e779af886315c4 0x822e779af886315c 0xd4efe19f88e73fcd 0xfd4efe19f88e73fc

def z97 : W := mkw 0x0004000208200440 0x8000400020820044 0x9004010608200cc9 0xb9004010608200cc

def z98 : W := mkw 0x6045b12e8b6b5dd0 0xc6045b12e8b6b5dd 0xf4fff1ff8fffffff 0xff4fff1ff8ffffff

def z99 : W := mkw 0x03fb5dfd0001108c 0x003fb5dfd0001108 0xffffffff802730cd 0xfffffffff802730c

def z100 : W := mkw 0x811806503014a029 0x0811806503014a02 0x2b101e607018c032 0x02b101e607018c03

def z101 : W := mkw 0x404491020b284c50 0xc404491020b284c5 0xb0c011000f38ccfb 0x2b0c011000f38ccf

def z102 : W := mkw 0x0404a0006efe0003 0xe0404a0006efe000 0x000000007fff0007 0x0000000007fff000

def z103 : W := mkw 0x20411dff800115cc 0x020411dff800115c 0x08001fff80003fc8 0xe08001fff80003fc

def z104 : W := mkw 0x4041112601004c50 0x04041112601004c5 0x000011660000ccf8 0xa000011660000ccf

def z105 : W := mkw 0x87ba665874d7b0ab 0x287ba665874d7b0a 0x4b286e1870c73004 0x44b286e1870c7300

def z106 : W := mkw 0xc1599774331ce839 0x4c1599774331ce83 0x2fd39e607718c032 0x02fd39e607718c03

def z107 : W := mkw 0x07bfe4756efe000f 0xe07bfe4756efe000 0xf7ffe07fffff0007 0x9f7ffe07fffff000

def z108 : W := mkw 0x06a6e0004eea0002 0xe06a6e0004eea000 0xf7e7e0007fc00007 0x0f7e7e0007fc0000

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0xd02c619f80000000 0xfd02c619f8000000

def z110 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x2fd39e6000000000 0x02fd39e600000000

def z111 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x432860007fff0007 0x0432860007fff000

def z112 : W := mkw 0x02e0198001004800 0x002e019800100480 0xfbe01f800f00cc0b 0x6fbe01f800f00cc0

def z113 : W := mkw 0x42e7d9a70b284c54 0xc42e7d9a70b284c5 0xb4f7f1e78f38ccfb 0xbb4f7f1e78f38ccf

def z114 : W := mkw 0x800002083015b0a1 0x0800002083015b0a 0x00000000703ff0ff 0x000000000703ff0f

def z115 : W := mkw 0x0004200008620000 0x8000420000862000 0xd02c600008e70005 0x1d02c600008e7000

def z116 : W := mkw 0x27bee00aeeff15c3 0xe27bee00aeeff15c 0xf7ffe19fffff3fcf 0xff7ffe19fffff3fc

def z117 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7ffe1067fff0ccf 0xbf7ffe1067fff0cc

def z118 : W := mkw 0x22e4398a886315c0 0x822e4398a886315c 0xfbec7f9f88e73fcd 0xffbec7f9f88e73fc

def z119 : W := mkw 0x03fb5df50100480c 0x003fb5df50100480 0xffffffff8f00cc0b 0xfffffffff8f00cc0

def z120 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0x000000007fc0ff0f 0x0000000007fc0ff0

def z121 : W := mkw 0x051ee0006efe0003 0xe051ee0006efe000 0x041fe0007fff0007 0x1041fe0007fff000

def z122 : W := mkw 0x404591260a280450 0xc404591260a28045 0xb4d79166003800f0 0xbb4d79166003800f

def z123 : W := mkw 0x800002083015b0a1 0x0800002083015b0a 0x7b001e00703ff0ff 0x67b001e00703ff0f

def z124 : W := mkw 0x4041912403084810 0x4404191240308481 0x24d390600718c032 0x024d390600718c03

def z125 : W := mkw 0x42e59ba65fa8ee52 0xd42e59ba65fa8ee5 0xfff79fe67ff8ffff 0xffff79fe67ff8fff

def z126 : W := mkw 0x80401fd81101faa8 0x180401fd81101faa 0x08001ff80000fff8 0xe08001ff80000fff

def z127 : W := mkw 0x80411ffd1001b0ac 0x080411ffd1001b0a 0x08001fff8000f0f8 0xe08001fff8000f0f

def z128 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x4b081e787007f0fc 0xe4b081e787007f0f

def z129 : W := mkw 0x87bee6587effb0ab 0xe87bee6587effb0a 0xfffffe787ffff0ff 0xffffffe787ffff0f

def z130 : W := mkw 0x07ba6a8074d6a203 0x307ba6a8074d6a20 0x4b286e8070c73304 0x44b286e8070c7330

def z131 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01e007fc0c007 0x0fbe01e007fc0c00

def z132 : W := mkw 0x83f81fd07594ea2b 0x183f81fd07594ea2 0xfbf01fe07fd8ff3f 0x6fbf01fe07fd8ff3

def z133 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe1807fff3f0f 0x7f7ffe1807fff3f0

def z134 : W := mkw 0x6045b12e8b6b5dd0 0xc6045b12e8b6b5dd 0xb4dff17f8f3fccfb 0xbb4dff17f8f3fccf

def z135 : W := mkw 0x07beecd16efe000f 0xe07beecd16efe000 0xffffee99ffff0007 0x5ffffee99ffff000

def z136 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x000c601f88e73fcd 0x9000c601f88e73fc

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000019f80000000 0xe0000019f8000000

def z138 : W := mkw 0x8159177c3015b0a9 0x08159177c3015b0a 0xffdf9f7e703ff0ff 0xfffdf9f7e703ff0f

def z139 : W := mkw 0x0004000208200440 0x8000400020820044 0xd02c619f88200cc9 0xfd02c619f88200cc

def z140 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0x67fbe00077df0006 0x067fbe00077df000

def z141 : W := mkw 0x011802003014a001 0x0011802003014a00 0x7b181e00703ff00f 0x77b181e00703ff00

def z142 : W := mkw 0x22e4398acde35fc2 0x922e4398acde35fc 0xd0ec619f8fe73fcd 0xfd0ec619f8fe73fc

def z143 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbec7f9fffc0ff0f 0xffbec7f9fffc0ff0

def z144 : W := mkw 0x47fff1246ffe4813 0xe47fff1246ffe481 0xf7fff0607fffc037 0x1f7fff0607fffc03

def z145 : W := mkw 0x07fefb807ffeea03 0xf07fefb807ffeea0 0xffffff807fffff0f 0x7ffffff807fffff0

def z146 : W := mkw 0x80000458000110a8 0x080000458000110a 0x00000078000000f0 0x800000078000000f

def z147 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x2bc01e007700c002 0x02bc01e007700c00

def z148 : W := mkw 0x22e43b8adde3ffc2 0x922e43b8adde3ffc 0xfbec7f9fffe7ffcf 0xffbec7f9fffe7ffc

def z149 : W := mkw 0x0040110001004800 0x0004011000100480 0xb0c011000f00cc0b 0x2b0c011000f00cc0

def z150 : W := mkw 0x815817583115f8a9 0x0815817583115f8a 0xfbd81f787f3ffcff 0xffbd81f787f3ffcf

def z151 : W := mkw 0x07fffdf56efe000f 0xe07fffdf56efe000 0xffffffffffff0007 0xfffffffffffff000

def z152 : W := mkw 0x03ba4cd10000000c 0x003ba4cd10000000 0x0b000e0000000000 0x00b000e000000000

def z153 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xc02c619f88c73f04 0x4c02c619f88c73f0

def z154 : W := mkw 0x00401b801100ea00 0x100401b801100ea0 0x08001f800000ff08 0x608001f800000ff0

def z155 : W := mkw 0x051ee0002a7e0001 0xe051ee0002a7e000 0x041fe000003f0000 0x1041fe000003f000

def z156 : W := mkw 0x011b44750000000c 0x0011b44750000000 0x7f1ffe7f80000000 0xf7f1ffe7f8000000

def z157 : W := mkw 0x211c200aa87715c1 0x8211c200aa87715c 0xf33c619ff8ff3fcf 0xff33c619ff8ff3fc

def z158 : W := mkw 0xa004265a9863b5e8 0x8a004265a9863b5e 0xd82c7fff88e7fffd 0xfd82c7fff88e7fff

def z159 : W := mkw 0x02e119a400000000 0x002e119a40000000 0xfff79fe600000000 0xffff79fe60000000

def z160 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x0000000008e73fcd 0x00000000008e73fc

def z161 : W := mkw 0x03ba4cd10000000c 0x003ba4cd10000000 0x7b387ef980000000 0xf7b387ef98000000

def z162 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x84c781060f000c00 0x084c781060f000c0

def z163 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x041791660038ccf8 0xb041791660038ccf

def z164 : W := mkw 0x00000a801000a200 0x100000a801000a20 0x08000e8000003300 0x408000e800000330

def z165 : W := mkw 0x02e0198044800002 0x002e019804480000 0xfbe01f807fc00007 0x6fbe01f807fc0000

def z166 : W := mkw 0x0404a0006efe0003 0xe0404a0006efe000 0xb4d780007fff0007 0x1b4d780007fff000

def z167 : W := mkw 0x4404a0026ffe4c53 0xe4404a0026ffe4c5 0x000000007fffccff 0x0000000007fffccf

def z168 : W := mkw 0x00401b801100ea00 0x100401b801100ea0 0xb8c01f800f00ff0b 0x6b8c01f800f00ff0

def z169 : W := mkw 0x02a0000000000000 0x002a000000000000 0xf3e0000000000000 0x0f3e000000000000

def z170 : W := mkw 0x455ff1262b7e4c51 0xe455ff1262b7e4c5 0xb4dff1660f3fccfb 0xbb4dff1660f3fccf

def z171 : W := mkw 0x03ba400000000000 0x003ba40000000000 0x27d3800000000000 0x027d380000000000

def z172 : W := mkw 0x26a6e002ceea0542 0xe26a6e002ceea054 0x84e7e1878fc00f00 0x084e7e1878fc00f0

def z173 : W := mkw 0x211f647f886315cc 0x8211f647f886315c 0xd43fe1ff88e73fcd 0xfd43fe1ff88e73fc

def z174 : W := mkw 0x23ba6cd98043118c 0x023ba6cd98043118 0x4b286e9980c73304 0x44b286e9980c7330

def z175 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b101e787018f0fa 0xe2b101e787018f0f

def z176 : W := mkw 0x03f81b807594ea03 0x103f81b807594ea0 0xfbf81f807fffff0f 0x7fbf81f807fffff0

def z177 : W := mkw 0x2000200a804315c0 0x02000200a804315c 0x4028619f80c73fcc 0xe4028619f80c73fc

def z178 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x88e01f800fc0ff08 0x688e01f800fc0ff0

def z179 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x500c601f802730cd 0xf500c601f802730c

def z180 : W := mkw 0x4041912603084c50 0x44041912603084c5 0x24d391660718ccfa 0xa24d391660718ccf

def z181 : W := mkw 0x80000008201510a1 0x080000008201510a 0x00000000003f00f0 0x000000000003f00f

def z182 : W := mkw 0x011b44750000000c 0x0011b44750000000 0xd43fe1ff80000000 0xfd43fe1ff8000000

def z183 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7fff0607fffc0ff 0xbf7fff0607fffc0f

def z184 : W := mkw 0x2000200880431180 0x0200020088043118 0x5028609980e733cd 0xf5028609980e733c

def z185 : W := mkw 0x0040110001004800 0x0004011000100480 0x000011000000cc08 0x2000011000000cc0

def z186 : W := mkw 0x07fef9806ffe4a03 0xf07fef9806ffe4a0 0xf7ffe1807fff0f07 0x1f7ffe1807fff0f0

def z187 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b101e60703ff0ff 0x02b101e60703ff0f

def z188 : W := mkw 0x82e01b887595faa3 0x182e01b887595faa 0xfbe01f807fffffff 0x6fbe01f807ffffff

def z189 : W := mkw 0x2000200880431180 0x0200020088043118 0x4028609980c73304 0x44028609980c7330

def z190 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x000c601f802700c0 0x9000c601f802700c

def z191 : W := mkw 0x00411df50000000c 0x000411df50000000 0x08001fff80000000 0xe08001fff8000000

def z192 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x4b201f8070c0ff0c 0x64b201f8070c0ff0

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c601f80000000 0x9000c601f8000000

def z194 : W := mkw 0x42e59ba65fa8ee52 0xd42e59ba65fa8ee5 0xbfd79f667f38ccfb 0xbbfd79f667f38ccf

def z195 : W := mkw 0x43ffddf70a28045c 0xc43ffddf70a28045 0xffffffff803800f0 0xfffffffff803800f

def z196 : W := mkw 0x0118000020140001 0x0011800002014000 0x73180000703f0007 0x173180000703f000

def z197 : W := mkw 0x03ba4ed15480a20e 0x103ba4ed15480a20 0x4b286e99f0c03304 0x44b286e99f0c0330

def z198 : W := mkw 0xc15d957e2b3d5cf9 0xcc15d957e2b3d5cf 0xb4df917e0f3fccfb 0xbb4df917e0f3fccf

def z199 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0xd02001807fc0ff0f 0x6d02001807fc0ff0

def z200 : W := mkw 0x02e11df50000000c 0x002e11df50000000 0xfbe01fff80000000 0xefbe01fff8000000

def z201 : W := mkw 0x43ffdff75fa8ee5e 0xd43ffdff75fa8ee5 0xfffffffffff8ffff 0xffffffffffff8fff

def z202 : W := mkw 0x20453dff886315cc 0x820453dff886315c 0xd82c7fff88e73fcd 0xfd82c7fff88e73fc

def z203 : W := mkw 0x811806581001b0a8 0x0811806581001b0a 0x7b181e780000f0f8 0xf7b181e780000f0f

def z204 : W := mkw 0x2000000a800115c0 0x02000000a800115c 0x0000019f80003fc8 0xe0000019f80003fc

def z205 : W := mkw 0x03ba400000000000 0x003ba40000000000 0xf7ffe00000000000 0x1f7ffe0000000000

def z206 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c600008e73fcd 0x1d02c600008e73fc

def z207 : W := mkw 0x07fffdf56efe000f 0xe07fffdf56efe000 0xfffffe607fff0007 0x1fffffe607fff000

def z208 : W := mkw 0x0118000020140001 0x0011800002014000 0x2310000070180002 0x0231000007018000

def z209 : W := mkw 0x27bee008eeff1183 0xe27bee008eeff118 0xf7ffe099ffff3307 0x5f7ffe099ffff330

def z210 : W := mkw 0x2004a00a8a6b15c0 0xc2004a00a8a6b15c 0xf4ffe19f8fff3fcf 0xff4ffe19f8fff3fc

def z211 : W := mkw 0x03ba4cd10000000c 0x003ba4cd10000000 0xffffee9980000000 0x5ffffee998000000

def z212 : W := mkw 0x22e779a788620544 0x822e779a78862054 0x84e7e18788c00f00 0x084e7e18788c00f0

def z213 : W := mkw 0xc159977c331df8b9 0x4c159977c331df8b 0x7fdb9e78773ff0ff 0xf7fdb9e78773ff0f

def z214 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbf01fe07ff8ffff 0xffbf01fe07ff8fff

def z215 : W := mkw 0xc3fd9ffe7fbdfefb 0xdc3fd9ffe7fbdfef 0xffff9ffe7fffffff 0xfffff9ffe7ffffff

def z216 : W := mkw 0x00411df50000000c 0x000411df50000000 0x08001e6000000000 0x008001e600000000

def z217 : W := mkw 0x03fb5df52014000d 0x003fb5df52014000 0xfffffffff03f0007 0xffffffffff03f000

def z218 : W := mkw 0x400480020b284c50 0xc400480020b284c5 0x301010600f38ccfb 0xb301010600f38ccf

def z219 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x000011660f38ccfb 0xa000011660f38ccf

def z220 : W := mkw 0x6045b12e8b6b5dd0 0xc6045b12e8b6b5dd 0xb4d791660fffffff 0xbb4d791660ffffff

def z221 : W := mkw 0x46e7f1264fea4c52 0xe46e7f1264fea4c5 0xb4f7f1660ff8ccfb 0xbb4f7f1660ff8ccf

def z222 : W := mkw 0xa3fc3fdafdf7ffeb 0x9a3fc3fdafdf7ffe 0xfbfc7fffffffffff 0xffbfc7ffffffffff

def z223 : W := mkw 0xc11c865a3b3dfcf9 0xcc11c865a3b3dfcf 0x7b181e787f3ffcff 0xf7b181e787f3ffcf

def z224 : W := mkw 0x03ba400020140001 0x003ba40002014000 0xf7ffe000703f0007 0x1f7ffe000703f000

def z225 : W := mkw 0x051ee0002a7e0001 0xe051ee0002a7e000 0xb4dfe0000f3f0003 0x1b4dfe0000f3f000

def z226 : W := mkw 0x02e01b801000a000 0x002e01b801000a00 0xfbe01f807000f00f 0x6fbe01f807000f00

def z227 : W := mkw 0x03fb5ff55580ea0e 0x103fb5ff55580ea0 0xfffffffff700c002 0xffffffffff700c00

def z228 : W := mkw 0x03f81dd000000008 0x003f81dd00000000 0xfbf81ff800000000 0xffbf81ff80000000

def z229 : W := mkw 0x400480020b284c50 0xc400480020b284c5 0x000000000f38ccfb 0x0000000000f38ccf

def z230 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x2fd39fff80000000 0xe2fd39fff8000000

def z231 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xc7efe0007fc70004 0x0c7efe0007fc7000

def z232 : W := mkw 0x03b8000064940003 0x003b800006494000 0xf3f800007fff0007 0x1f3f800007fff000

def z233 : W := mkw 0x0040110001004800 0x0004011000100480 0x20c010000700c002 0x020c010000700c00

def z234 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x84c791660f00ccf8 0xa84c791660f00ccf

def z235 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x00000000002700c0 0x000000000002700c

def z236 : W := mkw 0x015b5df50000000c 0x0015b5df50000000 0x0c1fffff80000000 0xf0c1fffff8000000

def z237 : W := mkw 0x400580260a280450 0xc400580260a28045 0x04178066003800f0 0x904178066003800f

def z238 : W := mkw 0x83ba4ed93015b0ad 0x083ba4ed93015b0a 0x7b387ef9f03ff0ff 0xf7b387ef9f03ff0f

def z239 : W := mkw 0x800006581001b0a8 0x0800006581001b0a 0x08000e1800003000 0x408000e180000300

def z240 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x6be01e8077c0f306 0x46be01e8077c0f30

def z241 : W := mkw 0x43ffddf70b284c5c 0xc43ffddf70b284c5 0xffffffff8f000c00 0xfffffffff8f000c0

def z242 : W := mkw 0x23ff7dff886315cc 0x823ff7dff886315c 0xffffffff88e73fcd 0xfffffffff88e73fc

def z243 : W := mkw 0x4000000201004c50 0x04000000201004c5 0x000000000000ccf8 0x0000000000000ccf

def z244 : W := mkw 0x42e11ba65580ee52 0x142e11ba65580ee5 0xfbe01fe67fc0ffff 0xefbe01fe67fc0fff

def z245 : W := mkw 0x02e0198045804a02 0x102e0198045804a0 0x00c0000007000000 0x000c000000700000

def z246 : W := mkw 0x2000000a800115c0 0x02000000a800115c 0xd02c619f80003fc8 0xfd02c619f80003fc

def z247 : W := mkw 0x47bee0026ffe4c53 0xe47bee0026ffe4c5 0xf7ffe0007fffccff 0x1f7ffe0007fffccf

def z248 : W := mkw 0x07fbddf5669c000f 0x607fbddf5669c000 0xfffffffff7180002 0xffffffffff718000

def z249 : W := mkw 0x03fb5df54480000e 0x003fb5df54480000 0xffffffffffc00007 0xfffffffffffc0000

def z250 : W := mkw 0x02a0000044800002 0x002a000004480000 0x23c0000077000002 0x023c000007700000

def z251 : W := mkw 0x0118045000000008 0x0011804500000000 0x2b101e6000000000 0x02b101e600000000

def z252 : W := mkw 0x051ee0002a7e0001 0xe051ee0002a7e000 0xd43fe00008ff0005 0x1d43fe00008ff000

def z253 : W := mkw 0x000002001000a000 0x0000002001000a00 0x4b000e0070003004 0x44b000e007000300

def z254 : W := mkw 0x83fb5ffd1001b0ac 0x083fb5ffd1001b0a 0xffffffff8000f0f8 0xfffffffff8000f0f

def z255 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff8038c0fb 0xfffffffff8038c0f

def z256 : W := mkw 0x02a0000044800002 0x002a000004480000 0xf3e000007fc00007 0x0f3e000007fc0000

def z257 : W := mkw 0x27bee002eefe0543 0xe27bee002eefe054 0xf7ffe187ffff0f07 0x1f7ffe187ffff0f0

def z258 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b181e78703fc0f2 0x92b181e78703fc0f

def z259 : W := mkw 0x62e5bbaedfebffd2 0xd62e5bbaedfebffd 0xffffffffffffffff 0xffffffffffffffff

def z260 : W := mkw 0x07bee2007ffeea03 0xf07bee2007ffeea0 0xf7ffe0007fffff0f 0x1f7ffe0007fffff0

def z261 : W := mkw 0x0000000800011080 0x0000000080001108 0x70181078003ff0ff 0xf70181078003ff0f

def z262 : W := mkw 0x000002001000a000 0x0000002001000a00 0xfb201f8078c0ff0f 0x6fb201f8078c0ff0

def z263 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf03c71ff88ffffff 0xff03c71ff88fffff

def z264 : W := mkw 0x02e01b885581fa82 0x102e01b885581fa8 0xfbe81f987fe7ffcf 0xffbe81f987fe7ffc

def z265 : W := mkw 0x0004200008620000 0x8000420000862000 0x0000000008e70005 0x00000000008e7000

def z266 : W := mkw 0x800002083015b0a1 0x0800002083015b0a 0x50080018703ff0ff 0xf50080018703ff0f

def z267 : W := mkw 0x411fc4770a28045c 0xc411fc4770a28045 0x041fe07f803800f0 0x9041fe07f803800f

def z268 : W := mkw 0xa3ff7fffb877b5ed 0x8a3ff7fffb877b5e 0xfffffffff8ffffff 0xffffffffff8fffff

def z269 : W := mkw 0x400480020b284c50 0xc400480020b284c5 0x900401060f38ccfb 0xb900401060f38ccf

def z270 : W := mkw 0x43fbddf50308481c 0x443fbddf50308481 0x2fd39e600718c032 0x02fd39e600718c03

def z271 : W := mkw 0x27ba6008e4d71183 0x227ba6008e4d7118 0x43286099f0c73304 0x443286099f0c7330

def z272 : W := mkw 0x02a420004ce20002 0x802a420004ce2000 0xf3ec60007fe70007 0x1f3ec60007fe7000

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0xb4d7800000000000 0x1b4d780000000000

def z274 : W := mkw 0x6004a00a8b6b5dd0 0xc6004a00a8b6b5dd 0xd02c619f8fffffff 0xfd02c619f8ffffff

def z275 : W := mkw 0x0000000045804a02 0x10000000045804a0 0x000000000fc00f00 0x0000000000fc00f0

def z276 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x000c619f80273fc8 0xf000c619f80273fc

def z277 : W := mkw 0xa11c245aa87715e9 0x8a11c245aa87715e 0x001c607f803f00f0 0x9001c607f803f00f

def z278 : W := mkw 0x47fffba67ffeee53 0xf47fffba67ffeee5 0xffffffe67fffffff 0xfffffffe67ffffff

def z279 : W := mkw 0x000002081001b080 0x0000002081001b08 0x7b081e187027f0cf 0xf7b081e187027f0c

def z280 : W := mkw 0x6004a00a8b6b5dd0 0xc6004a00a8b6b5dd 0x000000000fffffff 0x0000000000ffffff

def z281 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x94c781060f200cc9 0xb94c781060f200cc

def z282 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x7fdb9e7800000000 0xf7fdb9e780000000

def z283 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x24d790660738c0f2 0x924d790660738c0f

def z284 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x2fdffe7f80000000 0x92fdffe7f8000000

def z285 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe19fffff0007 0xff7ffe19fffff000

def z286 : W := mkw 0x8404a2087effb0a3 0xe8404a2087effb0a 0x000000007ffff0ff 0x0000000007ffff0f

def z287 : W := mkw 0x0004000208200440 0x8000400020820044 0xd024018608e03fcd 0xfd024018608e03fc

def z288 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb3c7ffff03ff0ff 0xffb3c7ffff03ff0f

def z289 : W := mkw 0x800002003014a021 0x0800002003014a02 0x000000007018c032 0x0000000007018c03

def z290 : W := mkw 0x42e7d9a70b284c54 0xc42e7d9a70b284c5 0x84e7e1878f000c00 0x084e7e1878f000c0

def z291 : W := mkw 0x0000800002080000 0x4000080000208000 0x24d3800007180002 0x024d380000718000

def z292 : W := mkw 0x02e49b805fa8ea02 0xd02e49b805fa8ea0 0xfff79f807ff8ff0f 0x7fff79f807ff8ff0

def z293 : W := mkw 0x0004000208200440 0x8000400020820044 0xb01411660838ccfb 0xbb01411660838ccf

def z294 : W := mkw 0x81180458201510a9 0x081180458201510a 0x30181078003fc0fb 0xb30181078003fc0f

def z295 : W := mkw 0x400480020b284c50 0xc400480020b284c5 0x000000000f000c00 0x0000000000f000c0

def z296 : W := mkw 0x2004200288620540 0x8200420028862054 0x9024618788e00fc9 0xb9024618788e00fc

def z297 : W := mkw 0x0404a0002a7e0001 0xe0404a0002a7e000 0x00000000003f0000 0x000000000003f000

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000000000300d 0x6500000000000300

def z299 : W := mkw 0x47bfe0266efe0453 0xe47bfe0266efe045 0xf7ffe0667fff00f7 0x9f7ffe0667fff00f

def z300 : W := mkw 0x83fb5ff53014a02d 0x083fb5ff53014a02 0x2fd39e607018c032 0x02fd39e607018c03

def z301 : W := mkw 0x400580260a280450 0xc400580260a28045 0x9417816608380cf9 0xb9417816608380cf

def z302 : W := mkw 0x0041112400000000 0x0004111240000000 0x0000116600000000 0xa000011660000000

def z303 : W := mkw 0x87ba665874d7b0ab 0x287ba665874d7b0a 0x7b387e7870fff0ff 0xf7b387e7870fff0f

def z304 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xa7f7e0007fd80002 0x0a7f7e0007fd8000

def z305 : W := mkw 0xa1182658b057b1a9 0x0a1182658b057b1a 0x4b286e99f0c73304 0x44b286e99f0c7330

def z306 : W := mkw 0x06a6e0004eea0002 0xe06a6e0004eea000 0xb4f7e0000ff80003 0x1b4f7e0000ff8000

def z307 : W := mkw 0x02e0198000000000 0x002e019800000000 0x2bc01e0000000000 0x02bc01e000000000

def z308 : W := mkw 0x00411df50000000c 0x000411df50000000 0xd82c7fff80000000 0xfd82c7fff8000000

def z309 : W := mkw 0x2004200288620540 0x8200420028862054 0x0004600780000000 0x0000460078000000

def z310 : W := mkw 0x40411ba61100ee50 0x140411ba61100ee5 0x08001fe60000fff8 0xe08001fe60000fff

def z311 : W := mkw 0x415d91262b3c4c51 0xc415d91262b3c4c5 0xf7df91667f3fccff 0xbf7df91667f3fccf

def z312 : W := mkw 0x0118000020140001 0x0011800002014000 0x4308000070070004 0x0430800007007000

def z313 : W := mkw 0x27fefb8affffffc3 0xf27fefb8affffffc 0xffffff9fffffffcf 0xfffffff9fffffffc

def z314 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x84ffe1ff80000000 0x984ffe1ff8000000

def z315 : W := mkw 0x87bee4586eff10ab 0xe87bee4586eff10a 0xf7ffe0787fff00f7 0x9f7ffe0787fff00f

def z316 : W := mkw 0x06a6e0006efe0003 0xe06a6e0006efe000 0x84e7e0007fff0007 0x084e7e0007fff000

def z317 : W := mkw 0x0000200000420000 0x0000020000042000 0x4028600000c70004 0x04028600000c7000

def z318 : W := mkw 0x2000200080420100 0x0200020008042010 0x0020608180c00300 0x00020608180c0030

def z319 : W := mkw 0x02e359a500000004 0x002e359a50000000 0xd4efe19f80000000 0xfd4efe19f8000000

def z320 : W := mkw 0x02a0088000000000 0x002a008800000000 0x4b200e8000000000 0x44b200e800000000

def z321 : W := mkw 0x81581fd83115faa9 0x181581fd83115faa 0x7b181ff8703fffff 0xf7b181ff8703ffff

def z322 : W := mkw 0x87bac650769ca02b 0x687bac650769ca02 0x2fd39e607718c032 0x02fd39e607718c03

def z323 : W := mkw 0xa004220ab877b5e1 0x8a004220ab877b5e 0x0000000078ffffff 0x00000000078fffff

def z324 : W := mkw 0x800002083015b0a1 0x0800002083015b0a 0x30101060703ff0ff 0xb30101060703ff0f

def z325 : W := mkw 0x6005a02e8a6b15d0 0xc6005a02e8a6b15d 0x041fe07f803f00f0 0x9041fe07f803f00f

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x7300000070000007 0x0730000007000000

def z327 : W := mkw 0x03fb5df545804a0e 0x103fb5df545804a0 0xffffffff8fc00f00 0xfffffffff8fc00f0

def z328 : W := mkw 0x0118045020140009 0x0011804502014000 0x7b181e78703f0007 0xf7b181e78703f000

def z329 : W := mkw 0x000480000a280000 0xc000480000a28000 0x84c780000f000000 0x084c780000f00000

def z330 : W := mkw 0x01591df50000000c 0x001591df50000000 0x7b181fff80000000 0xf7b181fff8000000

def z331 : W := mkw 0x051fe4752a7e000d 0xe051fe4752a7e000 0x041fe07f803f0000 0x9041fe07f803f000

def z332 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x00180078703ff0ff 0x900180078703ff0f

def z333 : W := mkw 0x20401b8a9101ffc0 0x120401b8a9101ffc 0x08001f9f8000ffc8 0xe08001f9f8000ffc

def z334 : W := mkw 0x03bb4cf50000000c 0x003bb4cf50000000 0x4f3feeff80000000 0xd4f3feeff8000000

def z335 : W := mkw 0x00401b805580ea02 0x100401b805580ea0 0x08001f807fc0ff0f 0x608001f807fc0ff0

def z336 : W := mkw 0x000002001100ea00 0x1000002001100ea0 0x000000000000ff08 0x0000000000000ff0

def z337 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x402c609f80e733c4 0xd402c609f80e733c

def z338 : W := mkw 0x0404a0004eea0002 0xe0404a0004eea000 0x000000000fc00000 0x0000000000fc0000

def z339 : W := mkw 0x0041112400000000 0x0004111240000000 0x24d3906000000000 0x024d390600000000

def z340 : W := mkw 0x02e0110045804802 0x002e011004580480 0xf3e011007fc0cc0f 0x2f3e011007fc0cc0

def z341 : W := mkw 0x0004200808631080 0x8000420080863108 0xd02c601808e730cd 0xfd02c601808e730c

def z342 : W := mkw 0x02a00a805480a202 0x102a00a805480a20 0x4b200e8070c03304 0x44b200e8070c0330

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z344 : W := mkw 0x23ff7dff886315cc 0x823ff7dff886315c 0xffffffff802700c0 0xfffffffff802700c

def z345 : W := mkw 0x0118045000000008 0x0011804500000000 0xfb3c7fff80000000 0xffb3c7fff8000000

def z346 : W := mkw 0x000104750000000c 0x0000104750000000 0x0000007f80000000 0x80000007f8000000

def z347 : W := mkw 0x22a02a88d4c3b382 0x122a02a88d4c3b38 0x4b286e99f0c73304 0x44b286e99f0c7330

def z348 : W := mkw 0x6045912e8b295dd0 0xc6045912e8b295dd 0xb4d791ff8f38fffb 0xfb4d791ff8f38fff

def z349 : W := mkw 0x800006583015b0a9 0x0800006583015b0a 0x08001e78703ff0ff 0xe08001e78703ff0f

def z350 : W := mkw 0x451fe0262a7e0451 0xe451fe0262a7e045 0x041fe066003f00f0 0x9041fe066003f00f

def z351 : W := mkw 0x07beea807efea203 0xf07beea807efea20 0xffffee807fff3307 0x5ffffee807fff330

def z352 : W := mkw 0x02a2400000000000 0x002a240000000000 0x84e7e00000000000 0x084e7e0000000000

def z353 : W := mkw 0x07fadb80779cea03 0x707fadb80779cea0 0xfff39f807fd8ff0f 0x6fff39f807fd8ff0

def z354 : W := mkw 0x400480020a280450 0xc400480020a28045 0x00000000003800f0 0x000000000003800f

def z355 : W := mkw 0x42e591264fa84c52 0xc42e591264fa84c5 0xf7f791667ff8ccff 0xbf7f791667ff8ccf

def z356 : W := mkw 0x015b55750000000c 0x0015b55750000000 0xb4dff17f80000000 0xbb4dff17f8000000

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000018000003f08 0x60000018000003f0

def z358 : W := mkw 0x0004200008620000 0x8000420000862000 0xd02c619f88e70005 0xfd02c619f88e7000

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x5008001800000000 0xf500800180000000

def z360 : W := mkw 0x83fb5ffd3015b0ad 0x083fb5ffd3015b0a 0xfffffffff0073004 0xffffffffff007300

def z361 : W := mkw 0x404593265fa8ee52 0xd404593265fa8ee5 0xb4d791667ff8ffff 0xbb4d791667ff8fff

def z362 : W := mkw 0x2004200888631180 0x8200420088863118 0xd02c609988e73305 0x5d02c609988e7330

def z363 : W := mkw 0x07ba600064d60003 0x207ba600064d6000 0xf7ffe00070c70004 0x1f7ffe00070c7000

def z364 : W := mkw 0x23ff7df78862054c 0x823ff7df78862054 0xffffffff88c00f00 0xfffffffff88c00f0

def z365 : W := mkw 0x000002005480a202 0x1000002005480a20 0x0000000070c03304 0x00000000070c0330

def z366 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb381ff878ffffff 0xffb381ff878fffff

def z367 : W := mkw 0x07fbddf5669c000f 0x607fbddf5669c000 0x2fd39e6077180002 0x02fd39e607718000

def z368 : W := mkw 0x2000000a800115c0 0x02000000a800115c 0x0000000000003fc8 0x00000000000003fc

def z369 : W := mkw 0x004013005580ea02 0x1004013005580ea0 0xb0c011007fc0ff0f 0x2b0c011007fc0ff0

def z370 : W := mkw 0x800006581001b0a8 0x0800006581001b0a 0x58081e780027f0fd 0xf58081e780027f0f

def z371 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x7bc01e007700f00f 0x67bc01e007700f00

def z372 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0xb4f7f1e78ff8cffb 0xbb4f7f1e78ff8cff

def z373 : W := mkw 0x06a4a0006efe0003 0xe06a4a0006efe000 0xf3e000007fff0007 0x0f3e000007fff000

def z374 : W := mkw 0x004491000b284800 0xc004491000b28480 0xb4d791000f38cc0b 0x3b4d791000f38cc0

def z375 : W := mkw 0x42e599a64fa84e52 0xd42e599a64fa84e5 0xb4f791e60ff8cffb 0xbb4f791e60ff8cff

def z376 : W := mkw 0xc3ffdfff3b3dfcfd 0xcc3ffdfff3b3dfcf 0xffffffffff3ffcff 0xfffffffffff3ffcf

def z377 : W := mkw 0x03ff7df50862000c 0x803ff7df50862000 0xffffffff88e70005 0xfffffffff88e7000

def z378 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xcbe00f807fc03f04 0x4cbe00f807fc03f0

def z379 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x84d781660f380cf0 0x984d781660f380cf

def z380 : W := mkw 0x40411df701004c5c 0x040411df701004c5 0x08001fff8000ccf8 0xe08001fff8000ccf

def z381 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xabe01f807fc0cf02 0x0abe01f807fc0cf0

def z382 : W := mkw 0x2000200880431180 0x0200020088043118 0xd028619988c73f0d 0x6d028619988c73f0

def z383 : W := mkw 0x04008000669c0003 0x604008000669c000 0x0000000077180002 0x0000000007718000

def z384 : W := mkw 0x051ca0006efe0003 0xe051ca0006efe000 0x731800007fff0007 0x1731800007fff000

def z385 : W := mkw 0x811806503014a029 0x0811806503014a02 0x3b101e607038c0fb 0xb3b101e607038c0f

def z386 : W := mkw 0x011c80002a3c0001 0xc011c80002a3c000 0xf7df80007f3f0007 0x1f7df80007f3f000

def z387 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4c791060f00cc0b 0x2b4c791060f00cc0

def z388 : W := mkw 0x06e7f9a54eea0006 0xe06e7f9a54eea000 0x84e7e1878fc00000 0x084e7e1878fc0000

def z389 : W := mkw 0x47fbd124679c4813 0x647fbd124679c481 0x27d390607718c032 0x027d390607718c03

def z390 : W := mkw 0x2004220adde3ffc2 0x92004220adde3ffc 0x000000007fe7ffcf 0x0000000007fe7ffc

def z391 : W := mkw 0x2044310a89635dc0 0x82044310a89635dc 0xf0ec719f8fe7ffcf 0xff0ec719f8fe7ffc

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x00100060003800f0 0x900100060003800f

def z393 : W := mkw 0x0040110001004800 0x0004011000100480 0xb0d011600f38ccfb 0xbb0d011600f38ccf

def z394 : W := mkw 0x415d95760b284c58 0xc415d95760b284c5 0xffdf9f7e0f38ccfb 0xfffdf9f7e0f38ccf

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0xd020018000000000 0x6d02001800000000

def z396 : W := mkw 0x02e0198000000000 0x002e019800000000 0xfbec7f9f80000000 0xffbec7f9f8000000

def z397 : W := mkw 0x004119a500000004 0x0004119a50000000 0x0000018780000000 0x0000001878000000

def z398 : W := mkw 0x0000000020140001 0x0000000002014000 0x00000000703f0007 0x000000000703f000

def z399 : W := mkw 0x23be6cdb886315cc 0x823be6cdb886315c 0xdb2c6f9f88e73fcd 0xfdb2c6f9f88e73fc

def z400 : W := mkw 0x800006501000a028 0x0800006501000a02 0x08001e600000c030 0x008001e600000c03

def z401 : W := mkw 0x07bec0006ebc0003 0xe07bec0006ebc000 0xb7d780007f380003 0x1b7d780007f38000

def z402 : W := mkw 0x20443b8a9963ffc0 0x920443b8a9963ffc 0xd82c7f9f88e7ffcd 0xfd82c7f9f88e7ffc

def z403 : W := mkw 0x051ac000221c0001 0x6051ac000221c000 0x0413800000180000 0x0041380000018000

def z404 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x80e001807fc0ff0f 0x080e001807fc0ff0

def z405 : W := mkw 0x0000000800011080 0x0000000080001108 0xd028019808e73fcd 0xfd028019808e73fc

def z406 : W := mkw 0x2000000a800115c0 0x02000000a800115c 0xd020019f88c03fcd 0xed020019f88c03fc

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x000010600000c0f8 0xa000010600000c0f

def z408 : W := mkw 0x03fa5b805580ea02 0x103fa5b805580ea0 0xffffff807fc0ff0f 0x7ffffff807fc0ff0

def z409 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x27d380007fff0007 0x027d380007fff000

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x8024618780000000 0x0802461878000000

def z411 : W := mkw 0x011c200028760001 0x8011c20002876000 0xf33c600078ff0007 0x1f33c600078ff000

def z412 : W := mkw 0x404593261b28ec50 0xc404593261b28ec5 0xffd79f667f38fcff 0xfffd79f667f38fcf

def z413 : W := mkw 0x0000000200000440 0x0000000020000044 0x0000010600000cc8 0xa0000010600000cc

def z414 : W := mkw 0x43ffd1260b284c50 0xc43ffd1260b284c5 0xf7fff1660f38ccfb 0xbf7fff1660f38ccf

def z415 : W := mkw 0x07fef1006ffe4803 0xe07fef1006ffe480 0xf7fff1007fffcc0f 0x3f7fff1007fffcc0

def z416 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181e7870073004 0xf7b181e787007300

def z417 : W := mkw 0x2045312e886315c0 0x82045312e886315c 0xf4fff1ff88e73fcd 0xff4fff1ff88e73fc

def z418 : W := mkw 0x0041112400000000 0x0004111240000000 0xf4fff1ff80000000 0xff4fff1ff8000000

def z419 : W := mkw 0xc004820a3b3dfcf1 0xcc004820a3b3dfcf 0x000000007f3ffcff 0x0000000007f3ffcf

def z420 : W := mkw 0x83f81fd07594ea2b 0x183f81fd07594ea2 0x2bd01e607718c032 0x02bd01e607718c03

def z421 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b180e18703f3007 0x57b180e18703f300

def z422 : W := mkw 0x02e0198045804a02 0x102e0198045804a0 0xb0e011800fc0cf0b 0x2b0e011800fc0cf0

def z423 : W := mkw 0x87bee6587effb0ab 0xe87bee6587effb0a 0xffffee187fff3007 0x5ffffee187fff300

def z424 : W := mkw 0x42e599a60b284c50 0xc42e599a60b284c5 0xfff79fe60f38ccfb 0xffff79fe60f38ccf

def z425 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x08181e78003ff0f8 0xf08181e78003ff0f

def z426 : W := mkw 0x00401b801100ea00 0x100401b801100ea0 0xd8201f8008c0ff0d 0x6d8201f8008c0ff0

def z427 : W := mkw 0x03fb5ff51100ea0c 0x103fb5ff51100ea0 0xffffffff8000ff08 0xfffffffff8000ff0

def z428 : W := mkw 0x03bec0000a280000 0xc03bec0000a28000 0xf7ffe0000f380003 0x1f7ffe0000f38000

def z429 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x0000019f88e73fcd 0xe0000019f88e73fc

def z430 : W := mkw 0x800002081001b0a0 0x0800002081001b0a 0x000000000000f0f8 0x0000000000000f0f

def z431 : W := mkw 0x40459ba61b28ee50 0xd40459ba61b28ee5 0xbcd79fe60f38fffb 0xfbcd79fe60f38fff

def z432 : W := mkw 0xc7fff77e7ffffcfb 0xec7fff77e7ffffcf 0xffffff7e7ffffcff 0xfffffff7e7ffffcf

def z433 : W := mkw 0x83f81fd83015b0a9 0x083f81fd83015b0a 0xfbf81ff8703ff0ff 0xffbf81ff8703ff0f

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000010008000c09 0x29000010008000c0

def z435 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x6ffbfef980000000 0x46ffbfef98000000

def z436 : W := mkw 0x03fa5fd15580ea0e 0x103fa5fd15580ea0 0xfbe87f99ffc0ff0f 0x6fbe87f99ffc0ff0

def z437 : W := mkw 0x02a00a805480a202 0x102a00a805480a20 0xdb200f8078c03f0d 0x6db200f8078c03f0

def z438 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0x000000007700c002 0x0000000007700c00

def z439 : W := mkw 0x07fffdf52a7e000d 0xe07fffdf52a7e000 0xffffffff803f0000 0xfffffffff803f000

def z440 : W := mkw 0x02e359a500000004 0x002e359a50000000 0x04c3800000000000 0x004c380000000000

def z441 : W := mkw 0x22e43b8adde3ffc2 0x922e43b8adde3ffc 0xfbe01f807fe7ffcf 0x6fbe01f807fe7ffc

def z442 : W := mkw 0x47fffdf76ffe4c5f 0xe47fffdf76ffe4c5 0xffffffffffffccff 0xfffffffffffffccf

def z443 : W := mkw 0x02e35ba55580ea06 0x102e35ba55580ea0 0xffe7ff87ffc0ff0f 0x6ffe7ff87ffc0ff0

def z444 : W := mkw 0x011a44510000000c 0x0011a44510000000 0x0008601980000000 0x0000860198000000

def z445 : W := mkw 0x22e43b82dde2ef42 0x922e43b82dde2ef4 0xfbe47f87ffc0ff0f 0x6fbe47f87ffc0ff0

def z446 : W := mkw 0x051a600020560001 0x2051a60002056000 0x0008600000070000 0x0000860000007000

def z447 : W := mkw 0x07fa7b8075d6ea03 0x307fa7b8075d6ea0 0xfbe87f807fc7ff0f 0x6fbe87f807fc7ff0

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000002000c9 0xb10000000002000c

def z449 : W := mkw 0xc15d97763b3cec79 0xcc15d97763b3cec7 0xbfd79f667f38ccfb 0xbbfd79f667f38ccf

def z450 : W := mkw 0x42e19ba45788ea12 0x542e19ba45788ea1 0x2fd39e607718c032 0x02fd39e607718c03

def z451 : W := mkw 0x6005a02e8a6b15d0 0xc6005a02e8a6b15d 0xd43fe1ff88ff3ffd 0xfd43fe1ff88ff3ff

def z452 : W := mkw 0x404591240b284810 0xc404591240b28481 0xb4d790600f38c033 0x1b4d790600f38c03

def z453 : W := mkw 0x00411df50000000c 0x000411df50000000 0xbcd79fff80000000 0xfbcd79fff8000000

def z454 : W := mkw 0x03be600008620000 0x803be60000862000 0xf7ffe00008e70005 0x1f7ffe00008e7000

def z455 : W := mkw 0x22e01b8ad581ffc2 0x122e01b8ad581ffc 0xfbe01f9fffc0ffcf 0xefbe01f9fffc0ffc

def z456 : W := mkw 0x03ffddf50a28000c 0xc03ffddf50a28000 0xffffffff8f380003 0xfffffffff8f38000

def z457 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0xf7f380007fd80007 0x0f7f380007fd8000

def z458 : W := mkw 0x02e0198045804a02 0x102e0198045804a0 0xfbe01f800fc00f00 0x6fbe01f800fc00f0

def z459 : W := mkw 0x0118000820151081 0x0011800082015108 0x73180018703f30cf 0xf73180018703f30c

def z460 : W := mkw 0x07be60006cf60003 0xa07be60006cf6000 0xd32c600078e70005 0x1d32c600078e7000

def z461 : W := mkw 0x000002001000a000 0x0000002001000a00 0x08001e000000f008 0x608001e000000f00

def z462 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xa4d791660f18cc32 0x0a4d791660f18cc3

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0c000000f000003 0x0b0c000000f00000

def z464 : W := mkw 0x07fffdf54eea000e 0xe07fffdf54eea000 0xffffffff8fc00000 0xfffffffff8fc0000

def z465 : W := mkw 0x42e59ba65fa8ee52 0xd42e59ba65fa8ee5 0xffe79f867fc0ff0f 0x6ffe79f867fc0ff0

def z466 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd020018008e73fcd 0x6d020018008e73fc

def z467 : W := mkw 0x27be600aecf715c3 0xa27be600aecf715c 0xd32c619ff8e73fcd 0xfd32c619ff8e73fc

def z468 : W := mkw 0x02a00a805480a202 0x102a00a805480a20 0xfbe00e807fc03307 0x4fbe00e807fc0330

def z469 : W := mkw 0x0000000800011080 0x0000000080001108 0x4008001800073004 0x4400800180007300

def z470 : W := mkw 0x06e6f9804fea4a02 0xf06e6f9804fea4a0 0x84e7e1800fc00f00 0x084e7e1800fc00f0

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x3010106000000000 0xb301010600000000

def z472 : W := mkw 0x02a0000044800002 0x002a000004480000 0x80e000000fc00000 0x080e000000fc0000

def z473 : W := mkw 0x0004a0000a6a0000 0xc0004a0000a6a000 0xf4ffe0000fff0007 0x1f4ffe0000fff000

def z474 : W := mkw 0x851ee6583a7fb0a9 0xe851ee6583a7fb0a 0x7f1ffe78703ff0ff 0xf7f1ffe78703ff0f

def z475 : W := mkw 0x2404a00aeeff15c3 0xe2404a00aeeff15c 0xd02c619fffff3fcf 0xfd02c619fffff3fc

def z476 : W := mkw 0x0118045000000008 0x0011804500000000 0x0018007800000000 0x9001800780000000

def z477 : W := mkw 0x43ffddf70b284c5c 0xc43ffddf70b284c5 0xbfd79f660f38ccfb 0xbbfd79f660f38ccf

def z478 : W := mkw 0x2004000a882115c0 0x82004000a882115c 0x9004019f88203fc9 0xf9004019f88203fc

def z479 : W := mkw 0x83f81fd87595faab 0x183f81fd87595faa 0x7bd81e78773ff0ff 0xf7bd81e78773ff0f

def z480 : W := mkw 0x4045912e0b295cd0 0xc4045912e0b295cd 0xf4df917e0f3ffcff 0xff4df917e0f3ffcf

def z481 : W := mkw 0x000002001000a000 0x0000002001000a00 0x2b001e007000c002 0x02b001e007000c00

def z482 : W := mkw 0x811806503014a029 0x0811806503014a02 0x7b101e607018f03f 0x67b101e607018f03

def z483 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4fff1ff8f38ccfb 0xff4fff1ff8f38ccf

def z484 : W := mkw 0x02a0000044800002 0x002a000004480000 0x4320000070c00004 0x04320000070c0000

def z485 : W := mkw 0x83ba46583015b0a9 0x083ba46583015b0a 0xfffffe78703ff0ff 0xffffffe78703ff0f

def z486 : W := mkw 0x0041112401004800 0x0004111240100480 0xb4d791660f00cc0b 0xbb4d791660f00cc0

def z487 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xbbc01f007f00cc0b 0x2bbc01f007f00cc0

def z488 : W := mkw 0x2000000880011180 0x0200000088001118 0x0000009980003300 0x4000000998000330

def z489 : W := mkw 0x000002001000a000 0x0000002001000a00 0x7b101e607038f0ff 0xf7b101e607038f0f

def z490 : W := mkw 0x0118045800011088 0x0011804580001108 0x7b181e78002730cd 0xf7b181e78002730c

def z491 : W := mkw 0x4041912403084810 0x4404191240308481 0xb4d791660718c032 0xbb4d791660718c03

def z492 : W := mkw 0x400580260a280450 0xc400580260a28045 0x341790660038c0fb 0xb341790660038c0f

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x4028609980000000 0x4402860998000000

def z494 : W := mkw 0x0004000208200440 0x8000400020820044 0x8004010608000c00 0x08004010608000c0

def z495 : W := mkw 0x0118000020140001 0x0011800002014000 0x00180000003f0000 0x100180000003f000

def z496 : W := mkw 0x42e49b825fa8ee52 0xd42e49b825fa8ee5 0xfbe01f807ff8ffff 0x6fbe01f807ff8fff

def z497 : W := mkw 0x81180458201510a9 0x081180458201510a 0x73180078703f00f7 0x973180078703f00f

def z498 : W := mkw 0x0041112400000000 0x0004111240000000 0xb4d791660038c0fb 0xbb4d791660038c0f

def z499 : W := mkw 0x4041112401004810 0x0404111240100481 0x000010600000c030 0x0000010600000c03

def z500 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d781060f380c03 0x1b4d781060f380c0

def z501 : W := mkw 0x02e01b801100ea00 0x102e01b801100ea0 0xfbe01f800000ff08 0x6fbe01f800000ff0

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000008c03f0d 0x00000000008c03f0

def z503 : W := mkw 0x07ba600064d60003 0x207ba600064d6000 0xf3e860007fc70007 0x0f3e860007fc7000

def z504 : W := mkw 0x06a2600044c20002 0x206a2600044c2000 0x0020600000c00000 0x00020600000c0000

def z505 : W := mkw 0x43fb5df701004c5c 0x043fb5df701004c5 0xffffffff8000ccf8 0xfffffffff8000ccf

def z506 : W := mkw 0x06e4bb807ffeea03 0xf06e4bb807ffeea0 0xfbe01f807fffff0f 0x6fbe01f807fffff0

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x3010000000380003 0x1301000000038000

def z508 : W := mkw 0x811806503014a029 0x0811806503014a02 0x0b000e0070000000 0x00b000e007000000

def z509 : W := mkw 0x0044110209204c40 0x80044110209204c4 0xb0c411060f20cccb 0xbb0c411060f20ccc

def z510 : W := mkw 0x0004000208200440 0x8000400020820044 0x00040006002000c0 0x900040006002000c

def z511 : W := mkw 0x03fb5ff55480a20e 0x103fb5ff55480a20 0xfffffffff0c03304 0xffffffffff0c0330

def z512 : W := mkw 0x4041912403084810 0x4404191240308481 0xb4d391600f18cc3b 0x2b4d391600f18cc3

def z513 : W := mkw 0x87bee6507efea02b 0xe87bee6507efea02 0xfffffe607fffc037 0x1fffffe607fffc03

def z514 : W := mkw 0x07bee0002a7e0001 0xe07bee0002a7e000 0xf7ffe000003f0000 0x1f7ffe000003f000

def z515 : W := mkw 0x22a4200acce315c2 0x822a4200acce315c 0xf3ec619fffe73fcf 0xff3ec619fffe73fc

def z516 : W := mkw 0x0040198001004a00 0x10040198001004a0 0x0000018000000f00 0x00000018000000f0

def z517 : W := mkw 0x000480000a280000 0xc000480000a28000 0x0417800000380000 0x1041780000038000

def z518 : W := mkw 0x83fb5ffd3015b0ad 0x083fb5ffd3015b0a 0x7fdb9e78703ff0ff 0xf7fdb9e78703ff0f

def z519 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x4028609988e73fcd 0x44028609988e73fc

def z520 : W := mkw 0x46e7f1264fea4c52 0xe46e7f1264fea4c5 0x84e7e1060fc00c00 0x084e7e1060fc00c0

def z521 : W := mkw 0x851ee4582a7f10a9 0xe851ee4582a7f10a 0x041fe078003f00f0 0x9041fe078003f00f

def z522 : W := mkw 0x22a42a8adce3b7c2 0x922a42a8adce3b7c 0xdb2c6f9ff8e73fcd 0xfdb2c6f9ff8e73fc

def z523 : W := mkw 0x2004200288620540 0x8200420028862054 0xd024618788c03f0d 0x6d024618788c03f0

def z524 : W := mkw 0x81591ffd3015b0ad 0x081591ffd3015b0a 0x7b181ffff03ff0ff 0xf7b181ffff03ff0f

def z525 : W := mkw 0x0118045000000008 0x0011804500000000 0x7b181e780038c0fb 0xf7b181e780038c0f

def z526 : W := mkw 0xc045977e1b29fcf8 0xcc045977e1b29fcf 0xbcd79f7e0f38fcfb 0xfbcd79f7e0f38fcf

def z527 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x6b181e78701ff036 0x46b181e78701ff03

def z528 : W := mkw 0x0040110000000000 0x0004011000000000 0xb0c0110000000000 0x2b0c011000000000

def z529 : W := mkw 0x0004200008620000 0x8000420000862000 0xd02c618008e73f0d 0x7d02c618008e73f0

def z530 : W := mkw 0x0406e0000a6a0000 0xe0406e0000a6a000 0x0407e00000000000 0x00407e0000000000

def z531 : W := mkw 0x03ba445000000008 0x003ba44500000000 0xfffffe7800000000 0xffffffe780000000

def z532 : W := mkw 0x251ee00aaa7f15c1 0xe251ee00aaa7f15c 0xd43fe19f88ff3fcd 0xfd43fe19f88ff3fc

def z533 : W := mkw 0x02e01b805480a202 0x102e01b805480a20 0xfbe01f8070c03304 0x6fbe01f8070c0330

def z534 : W := mkw 0x4045b1260b6a4c50 0xc4045b1260b6a4c5 0xf4fff1660fffccff 0xbf4fff1660fffccf

def z535 : W := mkw 0x00000cd10000000c 0x000000cd10000000 0x08000e9980000000 0x408000e998000000

def z536 : W := mkw 0x02e43b805de2ea02 0x902e43b805de2ea0 0xfbec7f807fe7ff0f 0x7fbec7f807fe7ff0

def z537 : W := mkw 0x07bee4506efe000b 0xe07bee4506efe000 0xfffffe787fff0007 0xffffffe787fff000

def z538 : W := mkw 0x0004000008200000 0x8000400000820000 0x9004000008200001 0x1900400000820000

def z539 : W := mkw 0x87bac658769db0ab 0x687bac658769db0a 0x7fdb9e78773ff0ff 0xf7fdb9e78773ff0f

def z540 : W := mkw 0x2004200288620540 0x8200420028862054 0xd02c618788e70f05 0x1d02c618788e70f0

def z541 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0x84e7e1878fc00f00 0x084e7e1878fc00f0

def z542 : W := mkw 0x07bee2007efea003 0xe07bee2007efea00 0xfffffe007ffff00f 0x7fffffe007ffff00

def z543 : W := mkw 0x4041912403084810 0x4404191240308481 0x34d390600738c0fb 0xb34d390600738c0f

def z544 : W := mkw 0x07bee0004eea0002 0xe07bee0004eea000 0xf7ffe0000fc00000 0x1f7ffe0000fc0000

def z545 : W := mkw 0x800006581001b0a8 0x0800006581001b0a 0x38101e780038f0fb 0xf38101e780038f0f

def z546 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b081e187007f00f 0x67b081e187007f00

def z547 : W := mkw 0x07ba600064d60003 0x207ba600064d6000 0x7338600070ff0007 0x17338600070ff000

def z548 : W := mkw 0x83b80ed87495b2ab 0x183b80ed87495b2a 0x4b280e9870c73304 0x44b280e9870c7330

def z549 : W := mkw 0x811806503014a029 0x0811806503014a02 0x7b181e60703fc037 0x17b181e60703fc03

def z550 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xbfd79f6600000000 0xbbfd79f660000000

def z551 : W := mkw 0x0000000800011080 0x0000000080001108 0x00000000002730cd 0x000000000002730c

def z552 : W := mkw 0x06a6e0004eea0002 0xe06a6e0004eea000 0xd4efe0000fe70005 0x1d4efe0000fe7000

def z553 : W := mkw 0x4041112601004c50 0x04041112601004c5 0x0000010600000c00 0x00000010600000c0

def z554 : W := mkw 0x83fb5ff53014a02d 0x083fb5ff53014a02 0xfffffffff018c032 0xffffffffff018c03

def z555 : W := mkw 0x83b806587495b0ab 0x083b806587495b0a 0xfbf81e787ffff0ff 0xffbf81e787ffff0f

def z556 : W := mkw 0x000480020a280440 0xc000480020a28044 0xb4d781060f380ccb 0xbb4d781060f380cc

def z557 : W := mkw 0xa118065ab015b5e9 0x0a118065ab015b5e 0x7b181ffff03fffff 0xf7b181ffff03ffff

def z558 : W := mkw 0x23ff7fffdde3ffce 0x923ff7fffdde3ffc 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z559 : W := mkw 0x400580260a280450 0xc400580260a28045 0x0407800600000000 0x0040780060000000

def z560 : W := mkw 0x02a0088044800202 0x102a008804480020 0x0020008000c00300 0x00020008000c0030

def z561 : W := mkw 0x07fff9a56efe0007 0xe07fff9a56efe000 0xf7ffe187ffff0007 0x1f7ffe187ffff000

def z562 : W := mkw 0xe15db77ebb7ffdf9 0xce15db77ebb7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z563 : W := mkw 0x42e19ba45788ea12 0x542e19ba45788ea1 0xfff39fe07fd8ff3f 0x6fff39fe07fd8ff3

def z564 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x2bc01f807700ff0a 0x62bc01f807700ff0

def z565 : W := mkw 0x2000000a800115c0 0x02000000a800115c 0x5008019f80273fcd 0xf5008019f80273fc

def z566 : W := mkw 0x051ee0002a7e0001 0xe051ee0002a7e000 0x771fe000703f0007 0x1771fe000703f000

def z567 : W := mkw 0xa000065a9001b5e8 0x0a000065a9001b5e 0x08001fff8000fff8 0xe08001fff8000fff

def z568 : W := mkw 0x03fb5ff55580ea0e 0x103fb5ff55580ea0 0x2fd39e607700c002 0x02fd39e607700c00

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0xd02c600000000000 0x1d02c60000000000

def z570 : W := mkw 0x23be600a886315c0 0x823be600a886315c 0xf7ffe19f88e73fcd 0xff7ffe19f88e73fc

def z571 : W := mkw 0xa004220ab877b5e1 0x8a004220ab877b5e 0xd02c619ff8ffffff 0xfd02c619ff8fffff

def z572 : W := mkw 0x0000000001004800 0x0000000000100480 0x000000000f00cc0b 0x0000000000f00cc0

def z573 : W := mkw 0x07fefb807ffeea03 0xf07fefb807ffeea0 0xfffffe007fffc007 0x1fffffe007fffc00

def z574 : W := mkw 0x400482025fa8ee52 0xd400482025fa8ee5 0x000000007ff8ffff 0x0000000007ff8fff

def z575 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x900c611f88270cc9 0xb900c611f88270cc

def z576 : W := mkw 0x0004200208620440 0x8000420020862044 0xd02c610608e70ccd 0xbd02c610608e70cc

def z577 : W := mkw 0x0040110001004800 0x0004011000100480 0x80c001000f000c00 0x080c001000f000c0

def z578 : W := mkw 0x47ffd1266fbc4c53 0xe47ffd1266fbc4c5 0xb7d791667f38ccfb 0xbb7d791667f38ccf

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0xd02c619f88c03f0d 0xfd02c619f88c03f0

def z580 : W := mkw 0x811b467d3015b0ad 0x0811b467d3015b0a 0x7f1ffe7ff03ff0ff 0xf7f1ffe7ff03ff0f

def z581 : W := mkw 0x811802083015b0a1 0x0811802083015b0a 0x73180000703ff0ff 0x173180000703ff0f

def z582 : W := mkw 0x02a002005480a002 0x002a002005480a00 0xfbe01e007fc0f00f 0x6fbe01e007fc0f00

def z583 : W := mkw 0x81180458201510a9 0x081180458201510a 0x0008001800070000 0x0000800180007000

def z584 : W := mkw 0x07fff1246efe0003 0xe07fff1246efe000 0xf7fff1667fff0007 0xbf7fff1667fff000

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000038c0fb 0x0000000000038c0f

def z586 : W := mkw 0x07ba400064940003 0x207ba40006494000 0x0300000070000000 0x0030000007000000

def z587 : W := mkw 0x03fb512400000000 0x003fb51240000000 0xf7fff16600000000 0xbf7fff1660000000

def z588 : W := mkw 0x011806501000a008 0x0011806501000a00 0x7b181e787000f00f 0xf7b181e787000f00

def z589 : W := mkw 0x81180458201510a9 0x081180458201510a 0x7b181e78003f00f0 0xf7b181e78003f00f

def z590 : W := mkw 0x0118000000000000 0x0011800000000000 0x7318000000000000 0x1731800000000000

def z591 : W := mkw 0x03fb5ff55580ea0e 0x103fb5ff55580ea0 0xfff39fe07fc0ff0f 0x6fff39fe07fc0ff0

def z592 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0xf7ffe00077180002 0x1f7ffe0007718000

def z593 : W := mkw 0x6045312e89635dd0 0x86045312e89635dd 0xd02c71ff88e7fffd 0xfd02c71ff88e7fff

def z594 : W := mkw 0x03fa5dd10000000c 0x003fa5dd10000000 0xfbe87f9980000000 0x6fbe87f998000000

def z595 : W := mkw 0x07fffff57ffeea0f 0xf07fffff57ffeea0 0xffffffffffffff0f 0xfffffffffffffff0

def z596 : W := mkw 0x0045112608200440 0x8004511260820044 0xb4d7916608200cc9 0xbb4d7916608200cc

def z597 : W := mkw 0x03ba400044800002 0x003ba40004480000 0xf7ffe0007fc00007 0x1f7ffe0007fc0000

def z598 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x473fe00070ff0004 0x1473fe00070ff000

def z599 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x5008001808e73fcd 0xf5008001808e73fc

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x5008000000270005 0x1500800000027000

def z601 : W := mkw 0x0003402500000004 0x0000340250000000 0x0407e00780000000 0x00407e0078000000

def z602 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01f807700c002 0x6fbe01f807700c00

def z603 : W := mkw 0x23fb7dfd8043118c 0x023fb7dfd8043118 0xffffffff80c73304 0xfffffffff80c7330

def z604 : W := mkw 0xa1182658b057b1a9 0x0a1182658b057b1a 0x7b387ef9f0fff3ff 0xf7b387ef9f0fff3f

def z605 : W := mkw 0x0000000044800002 0x0000000004480000 0x000000007fc00007 0x0000000007fc0000

def z606 : W := mkw 0x2004200288620540 0x8200420028862054 0xd02c619f88c00f00 0xfd02c619f88c00f0

def z607 : W := mkw 0x811806587595faab 0x1811806587595faa 0x7b181e787fffffff 0xf7b181e787ffffff

def z608 : W := mkw 0x0000000800011080 0x0000000080001108 0x00080018002700c0 0x900080018002700c

def z609 : W := mkw 0x0000045000000008 0x0000004500000000 0x08001e7800000000 0xe08001e780000000

def z610 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x4b080e18703ff0ff 0x44b080e18703ff0f

def z611 : W := mkw 0x87bee2087effb0a3 0xe87bee2087effb0a 0xf7ffe0007ffff0ff 0x1f7ffe0007ffff0f

def z612 : W := mkw 0x02e359a545804a06 0x102e359a545804a0 0x84e7e1878fc00f00 0x084e7e1878fc00f0

def z613 : W := mkw 0x2000000a800115c0 0x02000000a800115c 0x0000001f800000c0 0x80000001f800000c

def z614 : W := mkw 0x02a002005580ea02 0x102a002005580ea0 0xf3e000007fc0ff0f 0x0f3e000007fc0ff0

def z615 : W := mkw 0x02e11ba45580ea02 0x102e11ba45580ea0 0xfff79fe67fc0ff0f 0xffff79fe67fc0ff0

def z616 : W := mkw 0x800002083015b0a1 0x0800002083015b0a 0x0000000070073004 0x0000000007007300

def z617 : W := mkw 0x27bee00aeeff15c3 0xe27bee00aeeff15c 0xf7ffe0007fff3fcf 0x1f7ffe0007fff3fc

def z618 : W := mkw 0x03fb5ff51000a00c 0x003fb5ff51000a00 0xfffffffff000f00f 0xffffffffff000f00

def z619 : W := mkw 0x02a2488100000004 0x002a248810000000 0x0020608180000000 0x0002060818000000

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020008000c03304 0x44020008000c0330

def z621 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x4b180e78703f30f4 0xd4b180e78703f30f

def z622 : W := mkw 0x004591240a280000 0xc004591240a28000 0xb4d791660f380003 0xbb4d791660f38000

def z623 : W := mkw 0x2000200880431180 0x0200020088043118 0xd02c619f80c73304 0xfd02c619f80c7330

def z624 : W := mkw 0x811c065a3835b4e9 0x8811c065a3835b4e 0xfb1c1f7e783ffcff 0xffb1c1f7e783ffcf

def z625 : W := mkw 0x0040110001004800 0x0004011000100480 0xf0e011800fc0ff0f 0x6f0e011800fc0ff0

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x201010600018c032 0x0201010600018c03

def z627 : W := mkw 0x251ee00aaa7f15c1 0xe251ee00aaa7f15c 0x041fe01f803f00c0 0x9041fe01f803f00c

def z628 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c601f88e700c5 0x9d02c601f88e700c

def z629 : W := mkw 0x02e0198045804a02 0x102e0198045804a0 0xd0e001800fc03f0d 0x6d0e001800fc03f0

def z630 : W := mkw 0xa11c245aa87715e9 0x8a11c245aa87715e 0xd03c61ff88ff3ffd 0xfd03c61ff88ff3ff

def z631 : W := mkw 0x400480020b284c50 0xc400480020b284c5 0xb4d780000f38ccfb 0x1b4d780000f38ccf

def z632 : W := mkw 0x87feffd87ffffaab 0xf87feffd87ffffaa 0xfffffff87fffffff 0xffffffff87ffffff

def z633 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x8024618788e73fcd 0x08024618788e73fc

def z634 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x84c781060f38ccfb 0x084c781060f38ccf

def z635 : W := mkw 0x02a0000044800002 0x002a000004480000 0xf3e001807fc03f0f 0x6f3e001807fc03f0

def z636 : W := mkw 0x00401b801100ea00 0x100401b801100ea0 0x08001e000000c000 0x008001e000000c00

def z637 : W := mkw 0x811b447d201510ad 0x0811b447d201510a 0x041fe07f803f00f0 0x9041fe07f803f00f

def z638 : W := mkw 0x0000000800011080 0x0000000080001108 0xd02c619f802730cd 0xfd02c619f802730c

def z639 : W := mkw 0x67fff12eefff5dd3 0xe67fff12eefff5dd 0xf7fff1ffffffffff 0xff7fff1fffffffff

def z640 : W := mkw 0x00401b801100ea00 0x100401b801100ea0 0x7b001f807000ff0f 0x67b001f807000ff0

def z641 : W := mkw 0x07fef9806efe0003 0xe07fef9806efe000 0xffffff807fff0007 0x7ffffff807fff000

def z642 : W := mkw 0x211c245a886315c8 0x8211c245a886315c 0xfb3c7fff88e73fcd 0xffb3c7fff88e73fc

def z643 : W := mkw 0x02e11ff55580ea0e 0x102e11ff55580ea0 0xfbe01fffffc0ff0f 0xefbe01fffffc0ff0

def z644 : W := mkw 0x6041112e81015dd0 0x06041112e81015dd 0x000011ff8000fff8 0xe000011ff8000fff

def z645 : W := mkw 0x0159157400000008 0x0015915740000000 0xffdf9f7e00000000 0xfffdf9f7e0000000

def z646 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x5b080e18702730cd 0xf5b080e18702730c

def z647 : W := mkw 0x0001002400000000 0x0000100240000000 0x0417806600000000 0x9041780660000000

def z648 : W := mkw 0x02a00a805480a202 0x102a00a805480a20 0x0b000e0070000000 0x00b000e007000000

def z649 : W := mkw 0x4041112601004c50 0x04041112601004c5 0x301011660038ccfb 0xb301011660038ccf

def z650 : W := mkw 0x83f81fd87595faab 0x183f81fd87595faa 0xfbe81f987fc7ff0f 0x6fbe81f987fc7ff0

def z651 : W := mkw 0x02a480004ea80002 0xc02a480004ea8000 0xf7f780007ff80007 0x1f7f780007ff8000

def z652 : W := mkw 0x800002087595faa3 0x1800002087595faa 0x000000007fffffff 0x0000000007ffffff

def z653 : W := mkw 0x02e0198045804a02 0x102e0198045804a0 0xf3e001807fc00f07 0x0f3e001807fc00f0

def z654 : W := mkw 0x83fb5dfd201510ad 0x083fb5dfd201510a 0xffffffff803f00f0 0xfffffffff803f00f

def z655 : W := mkw 0x00411ff51100ea0c 0x100411ff51100ea0 0x08001fff8000ff08 0xe08001fff8000ff0

def z656 : W := mkw 0x03ba400000000000 0x003ba40000000000 0x4328600000000000 0x0432860000000000

def z657 : W := mkw 0x03ba4cd10000000c 0x003ba4cd10000000 0xdb2c6f9f80000000 0xfdb2c6f9f8000000

def z658 : W := mkw 0x0040198000000000 0x0004019800000000 0x08001f8000000000 0x608001f800000000

def z659 : W := mkw 0x000002001000a000 0x0000002001000a00 0x000000007000f00f 0x0000000007000f00

def z660 : W := mkw 0x81180458201510a9 0x081180458201510a 0x50180078003f30fd 0xf50180078003f30f

def z661 : W := mkw 0x02e41b825da0ee42 0x902e41b825da0ee4 0xfbe41f867fe0ffcf 0xffbe41f867fe0ffc

def z662 : W := mkw 0x42e599a64fa84e52 0xd42e599a64fa84e5 0x84e781860fc00f00 0x084e781860fc00f0

def z663 : W := mkw 0x4041112601004c50 0x04041112601004c5 0xb4d791660000ccf8 0xbb4d791660000ccf

def z664 : W := mkw 0xc045932e3b3dfcf1 0xcc045932e3b3dfcf 0xb4d791667f3ffcff 0xbb4d791667f3ffcf

def z665 : W := mkw 0x811c26583877b0a9 0x8811c26583877b0a 0xfb3c7e7878fff0ff 0xffb3c7e7878fff0f

def z666 : W := mkw 0x23fb5dff800115cc 0x023fb5dff800115c 0xffffffff80003fc8 0xfffffffff80003fc

def z667 : W := mkw 0xc11d867e3a3db4f9 0xcc11d867e3a3db4f 0x7f1f9e7e703ff0ff 0xf7f1f9e7e703ff0f

def z668 : W := mkw 0x03ba400000000000 0x003ba40000000000 0xf7ffe19f80000000 0xff7ffe19f8000000

def z669 : W := mkw 0x03f81fd05580ea0a 0x103f81fd05580ea0 0xfbf81ff87fc0ff0f 0xffbf81ff87fc0ff0

def z670 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xfff39fe000000000 0x6fff39fe00000000

def z671 : W := mkw 0xa11c265ab877b5e9 0x8a11c265ab877b5e 0x7b1c7e7ff03ff0ff 0xf7b1c7e7ff03ff0f

def z672 : W := mkw 0x03ff5df70820044c 0x803ff5df70820044 0xffffffff88200cc9 0xfffffffff88200cc

def z673 : W := mkw 0x6045b12e8b6b5dd0 0xc6045b12e8b6b5dd 0xd4efe19f8fe73fcd 0xfd4efe19f8fe73fc

def z674 : W := mkw 0x8118045020140029 0x0811804502014002 0x0010006000180030 0x0001000600018003

def z675 : W := mkw 0x07ba6cd164d6000f 0x207ba6cd164d6000 0x4b286e99f0c70004 0x44b286e99f0c7000

def z676 : W := mkw 0x4000800003084810 0x4400080000308481 0x000000000718c032 0x0000000000718c03

def z677 : W := mkw 0x400580260a280450 0xc400580260a28045 0xb4d780660f3800f3 0x9b4d780660f3800f

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0x300010000000c00b 0x2300010000000c00

def z679 : W := mkw 0x02e0198000000000 0x002e019800000000 0xfbe01f8008c03f0d 0x6fbe01f8008c03f0

def z680 : W := mkw 0x2000000280000540 0x0200000028000054 0x0000018780000f00 0x00000018780000f0

def z681 : W := mkw 0x22e43982cde24f42 0x922e43982cde24f4 0x80e461878fc00f00 0x080e461878fc00f0

def z682 : W := mkw 0x0404a0006efe0003 0xe0404a0006efe000 0xd02c60007fff0007 0x1d02c60007fff000

def z683 : W := mkw 0x02a00a805480a202 0x102a00a805480a20 0x7b201e8070c0f30f 0x67b201e8070c0f30

def z684 : W := mkw 0x03bb44750000000c 0x003bb44750000000 0xf7ffe07f80000000 0x9f7ffe07f8000000

def z685 : W := mkw 0x811806503014a029 0x0811806503014a02 0x7b181e787018c032 0xf7b181e787018c03

def z686 : W := mkw 0x0004200008620000 0x8000420000862000 0x8024600008c00000 0x08024600008c0000

def z687 : W := mkw 0x63fffdff8b6b5ddc 0xc63fffdff8b6b5dd 0xffffffff8fffffff 0xfffffffff8ffffff

def z688 : W := mkw 0x0004000208200440 0x8000400020820044 0x0000000008200cc9 0x00000000008200cc

def z689 : W := mkw 0x06a2c00046880002 0x606a2c0004688000 0x04c3800007000000 0x004c380000700000

def z690 : W := mkw 0x4041912403084810 0x4404191240308481 0x04c3800007000000 0x004c380000700000

def z691 : W := mkw 0x87fffffd7effb0af 0xe87fffffd7effb0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x9004010600000000 0xb900401060000000

def z693 : W := mkw 0x47fff1266ffe4c53 0xe47fff1266ffe4c5 0xf7ffe1067fff0c07 0x1f7ffe1067fff0c0

def z694 : W := mkw 0x4045112609204c50 0x84045112609204c5 0x900411660820ccf9 0xb900411660820ccf

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0xd020000008c00005 0x0d020000008c0000

def z696 : W := mkw 0x02e359a500000004 0x002e359a50000000 0xffe7ff8780000000 0x6ffe7ff878000000

def z697 : W := mkw 0x83ba4ed93015b0ad 0x083ba4ed93015b0a 0x4b286e99f0073004 0x44b286e99f007300

def z698 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xaff7ffe780000000 0x0aff7ffe78000000

def z699 : W := mkw 0x07bee0086eff1083 0xe07bee0086eff108 0xf7ffe0187fff30cf 0xff7ffe0187fff30c

def z700 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x8024619f88c03fc8 0xe8024619f88c03fc

def z701 : W := mkw 0x004013001100e800 0x0004013001100e80 0xfbc01f007f00fc0f 0x6fbc01f007f00fc0

def z702 : W := mkw 0x83b80ed87495b2ab 0x183b80ed87495b2a 0x7b381ef870fff3ff 0xf7b381ef870fff3f

def z703 : W := mkw 0xc159177e3115fcf9 0x0c159177e3115fcf 0x7b181f7e703ffcff 0xf7b181f7e703ffcf

def z704 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x84ffe0000fff0000 0x184ffe0000fff000

def z705 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x4b287fff80000000 0xe4b287fff8000000

def z706 : W := mkw 0x0118000020140001 0x0011800002014000 0x73181060703fc0ff 0xb73181060703fc0f

def z707 : W := mkw 0x07ba600064d60003 0x207ba600064d6000 0xf7ffe0007fc70007 0x1f7ffe0007fc7000

def z708 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x34d390600f38ccfb 0xb34d390600f38ccf

def z709 : W := mkw 0x404599a60b284e50 0xd404599a60b284e5 0xb4d791e60f38cffb 0xbb4d791e60f38cff

def z710 : W := mkw 0x2004a00a8a6b15c0 0xc2004a00a8a6b15c 0xd43fe19f88ff3fcd 0xfd43fe19f88ff3fc

def z711 : W := mkw 0x4041912403084810 0x4404191240308481 0xb4d791660738c0fb 0xbb4d791660738c0f

def z712 : W := mkw 0x42a58aa65ea8a652 0xd42a58aa65ea8a65 0x4f378ee670f833f4 0xd4f378ee670f833f

def z713 : W := mkw 0x004013005580ea02 0x1004013005580ea0 0xfbc01f007fc0ff0f 0x6fbc01f007fc0ff0

def z714 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xc7ffe0007fff0004 0x1c7ffe0007fff000

def z715 : W := mkw 0x051ee0002a7e0001 0xe051ee0002a7e000 0xf7dfe0007f3f0007 0x1f7dfe0007f3f000

def z716 : W := mkw 0x20411fff9101ffcc 0x120411fff9101ffc 0x08001fff8000ffc8 0xe08001fff8000ffc

def z717 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b1c7e7ff03ff0ff 0xf7b1c7e7ff03ff0f

def z718 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf0ec619f8fe73fcf 0xff0ec619f8fe73fc

def z719 : W := mkw 0x87bee4506efe002b 0xe87bee4506efe002 0xf7ffe0607fff0037 0x1f7ffe0607fff003

def z720 : W := mkw 0x23ff7dff886315cc 0x823ff7dff886315c 0x2fd39e6008e73fcd 0x02fd39e6008e73fc

def z721 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0x47ebe00077c70004 0x047ebe00077c7000

def z722 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe1807fff0f07 0x1f7ffe1807fff0f0

def z723 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf4ffe19f88e73fcd 0xff4ffe19f88e73fc

def z724 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0xf7ffe00077df0006 0x1f7ffe00077df000

def z725 : W := mkw 0x055efb803b7eea01 0xf055efb803b7eea0 0x0c1fff80003fff08 0x70c1fff80003fff0

def z726 : W := mkw 0x4045b1260b6a4c50 0xc4045b1260b6a4c5 0xf4fff1e60fffffff 0xff4fff1e60ffffff

def z727 : W := mkw 0x2000200a804315c0 0x02000200a804315c 0x4028619f80c73f04 0x44028619f80c73f0

def z728 : W := mkw 0x87ba6ed874d7b2ab 0x387ba6ed874d7b2a 0x4b286e9870c73304 0x44b286e9870c7330

def z729 : W := mkw 0x06a6e0004eea0002 0xe06a6e0004eea000 0xf7efe0007fe70007 0x1f7efe0007fe7000

def z730 : W := mkw 0xc0411ffe1101fef8 0x1c0411ffe1101fef 0x08001ffe0000fff8 0xe08001ffe0000fff

def z731 : W := mkw 0x47fb712665d64c53 0x247fb712665d64c5 0x4328716670c7ccfc 0xa4328716670c7ccf

def z732 : W := mkw 0x86a6e6585eebb0aa 0xe86a6e6585eebb0a 0x8ce7fe780fc0f0f8 0xe8ce7fe780fc0f0f

def z733 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0x67db8000771f0006 0x067db8000771f000

def z734 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d790660f38c0f3 0x9b4d790660f38c0f

def z735 : W := mkw 0x22e43b8adde3ffc2 0x922e43b8adde3ffc 0x2bcc7e1ff727c0c2 0x92bcc7e1ff727c0c

def z736 : W := mkw 0x03fb5df50100480c 0x003fb5df50100480 0xffffffff8000cc08 0xfffffffff8000cc0

def z737 : W := mkw 0x03fb5df545804a0e 0x103fb5df545804a0 0xffffffff8fc03f0d 0xfffffffff8fc03f0

def z738 : W := mkw 0x015b5df50000000c 0x0015b5df50000000 0xbcdfffff80000000 0xfbcdfffff8000000

def z739 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe1007fff0c0f 0x3f7ffe1007fff0c0

def z740 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4f791e60ff8cffb 0xbb4f791e60ff8cff

def z741 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181ffff03ff0ff 0xf7b181ffff03ff0f

def z742 : W := mkw 0x07bee8806efe0203 0xf07bee8806efe020 0xf7ffe0807fff0307 0x1f7ffe0807fff030

def z743 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xc02c619f88e73fcd 0x4c02c619f88e73fc

def z744 : W := mkw 0x03fb5df545804a0e 0x103fb5df545804a0 0xffffffffffc00f07 0xfffffffffffc00f0

def z745 : W := mkw 0x03bc80006ebc0003 0xc03bc80006ebc000 0xf7ff80007fff0007 0x1f7ff80007fff000

def z746 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xefffffff80000000 0x4efffffff8000000

def z747 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe187ffff0007 0x1f7ffe187ffff000

def z748 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xcbe00f807fc0ff0f 0x4cbe00f807fc0ff0

def z749 : W := mkw 0x2004a00a8a6b15c0 0xc2004a00a8a6b15c 0xd4efe19f8fe73fcd 0xfd4efe19f8fe73fc

def z750 : W := mkw 0x80411ffd1101faac 0x180411ffd1101faa 0x08001fff8000fff8 0xe08001fff8000fff

def z751 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7f380007fff0007 0x0f7f380007fff000

def z752 : W := mkw 0x00411df50000000c 0x000411df50000000 0xfcffffff80000000 0xffcffffff8000000

def z753 : W := mkw 0x02e11ba45580ea02 0x102e11ba45580ea0 0xfff39fe07fc0ff0f 0x6fff39fe07fc0ff0

def z754 : W := mkw 0xc15d977e3b3dfcf9 0xcc15d977e3b3dfcf 0xcfcf8f1e7f073c04 0x4cfcf8f1e7f073c0

def z755 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff8000c00b 0xfffffffff8000c00

def z756 : W := mkw 0x03ba4cd10000000c 0x003ba4cd10000000 0xffffef9f80000000 0xfffffef9f8000000

def z757 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01f807fc03f04 0x6fbe01f807fc03f0

def z758 : W := mkw 0x02e11ba45580ea02 0x102e11ba45580ea0 0xfff79fe67ff8ffff 0xffff79fe67ff8fff

def z759 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xfffffe7f80000000 0x9fffffe7f8000000

def z760 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x27d38000773f0002 0x027d38000773f000

def z761 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe000773f0002 0x1f7ffe000773f000

def z762 : W := mkw 0x83ba4ed97495b2af 0x183ba4ed97495b2a 0x4b286e99f0c73304 0x44b286e99f0c7330

def z763 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0807fff3307 0x5f7ffe0807fff330

def z764 : W := mkw 0x27bee002eefe0543 0xe27bee002eefe054 0xf7ffe0007fff0f07 0x1f7ffe0007fff0f0

def z765 : W := mkw 0x03fb5df50100480c 0x003fb5df50100480 0xffffffff8fc0ff0f 0xfffffffff8fc0ff0

def z766 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181e78703fc0f2 0xf7b181e78703fc0f

def z767 : W := mkw 0x404599a70b284c54 0xc404599a70b284c5 0xb4d791e78f38ccfb 0xbb4d791e78f38ccf

def z768 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0x2b001e007fc0ff0f 0x02b001e007fc0ff0

def z769 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0007fff300f 0x7f7ffe0007fff300

def z770 : W := mkw 0x27bac00ae69d15c3 0x627bac00ae69d15c 0x27d3819ff7183fca 0xe27d3819ff7183fc

def z771 : W := mkw 0x03fb5df52014000d 0x003fb5df52014000 0xfffffffff03fc0ff 0xffffffffff03fc0f

def z772 : W := mkw 0x6041b12c834b5990 0x46041b12c834b599 0x64fbf0f987dff336 0x464fbf0f987dff33

def z773 : W := mkw 0xe004a20abb7ffdf1 0xce004a20abb7ffdf 0x000000007fffffff 0x0000000007ffffff

def z774 : W := mkw 0x4041912403084810 0x4404191240308481 0xb4d391600f38ccfb 0xbb4d391600f38ccf

def z775 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181e7878ffffff 0xf7b181e7878fffff

def z776 : W := mkw 0x015b55750000000c 0x0015b55750000000 0xffdfff7f80000000 0xfffdfff7f8000000

def z777 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x34d790660738c0fb 0xb34d790660738c0f

def z778 : W := mkw 0x06a6e0006efe0003 0xe06a6e0006efe000 0xf7e7e0007fff0007 0x0f7e7e0007fff000

def z779 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b181e78703ff0fa 0xf2b181e78703ff0f

def z780 : W := mkw 0x02e25b815580ea06 0x102e25b815580ea0 0xfbe07f81ffc0ff0f 0x6fbe07f81ffc0ff0

def z781 : W := mkw 0x051ee0006efe0003 0xe051ee0006efe000 0xb4dfe0007fff0007 0x1b4dfe0007fff000

def z782 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xd7efe0007fe70005 0x1d7efe0007fe7000

def z783 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x67ffe00077ff0006 0x167ffe00077ff000

def z784 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe81f987fc0ff0f 0xffbe81f987fc0ff0

def z785 : W := mkw 0x4041912403084810 0x4404191240308481 0x24d390600738c0f2 0x924d390600738c0f

def z786 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xbbc01f007fc0ff0f 0x2bbc01f007fc0ff0

def z787 : W := mkw 0x07bec0006ebc0003 0xe07bec0006ebc000 0xf7df80007f3f0007 0x1f7df80007f3f000

def z788 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xa4d791660f38ccfb 0x0a4d791660f38ccf

def z789 : W := mkw 0x011b44750000000c 0x0011b44750000000 0xff3fffff80000000 0xfff3fffff8000000

def z790 : W := mkw 0x800486581a29b0a8 0xc800486581a29b0a 0xbcd79e780f38f0fb 0xfbcd79e780f38f0f

def z791 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe1067fff0007 0xbf7ffe1067fff000

def z792 : W := mkw 0x011802003014a001 0x0011802003014a00 0x7b181e60703ff0ff 0xf7b181e60703ff0f

def z793 : W := mkw 0x83f81dd865955aab 0x183f81dd865955aa 0x80f801f80fff0ff0 0x980f801f80fff0ff

def z794 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x2bc01f807fc0ff0f 0x62bc01f807fc0ff0

def z795 : W := mkw 0x02a00a805580ea02 0x102a00a805580ea0 0xdb200f807fc0ff0f 0x6db200f807fc0ff0

def z796 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x84d791660f38ccf8 0xb84d791660f38ccf

def z797 : W := mkw 0x07fb5df56494000f 0x207fb5df56494000 0xfffffffff0000000 0xffffffffff000000

def z798 : W := mkw 0xc041132e1101fcf0 0x0c041132e1101fcf 0x000011660000fcf8 0xa000011660000fcf

def z799 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff80003f08 0xfffffffff80003f0

def z800 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff88c00f00 0xfffffffff88c00f0

def z801 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe47f87ffc0ff0f 0x6fbe47f87ffc0ff0

def z802 : W := mkw 0x03fb5df54480000e 0x003fb5df54480000 0xfffffffff0c00004 0xffffffffff0c0000

def z803 : W := mkw 0x02e35df50000000c 0x002e35df50000000 0xffe7ffff80000000 0xeffe7ffff8000000

def z804 : W := mkw 0x0445bdf56efe000f 0xe0445bdf56efe000 0x08001fffffff0007 0xe08001fffffff000

def z805 : W := mkw 0x4041912603084c50 0x44041912603084c5 0x24d390600718ccfa 0x024d390600718ccf

def z806 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb381e7878fff0ff 0xffb381e7878fff0f

def z807 : W := mkw 0x27bee002eefe0543 0xe27bee002eefe054 0xf7ffe007ffff0007 0x1f7ffe007ffff000

def z808 : W := mkw 0x82e35bad3015b0a5 0x082e35bad3015b0a 0x84e7e187f03ff0ff 0x084e7e187f03ff0f

def z809 : W := mkw 0x6004a20adfebffd2 0xd6004a20adfebffd 0x000000007fffffff 0x0000000007ffffff

def z810 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x7bc01e007fc0ff0f 0x67bc01e007fc0ff0

def z811 : W := mkw 0x000480002a3c0001 0xc000480002a3c000 0xb4d780007f3f0007 0x1b4d780007f3f000

def z812 : W := mkw 0x83fb5ff57594ea2f 0x183fb5ff57594ea2 0x2fd39e607718c032 0x02fd39e607718c03

def z813 : W := mkw 0x02e11ba45580ea02 0x102e11ba45580ea0 0xfbe01fe67fc0ff0f 0xefbe01fe67fc0ff0

def z814 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf03c619f88ff3fcf 0xff03c619f88ff3fc

def z815 : W := mkw 0x03be60004ce20002 0x803be60004ce2000 0xf7ffe0007fe70007 0x1f7ffe0007fe7000

def z816 : W := mkw 0x000002081001b080 0x0000002081001b08 0x7b181e78703ff0ff 0xf7b181e78703ff0f

def z817 : W := mkw 0x46e7f9a74fea4c56 0xe46e7f9a74fea4c5 0x84e7e1878fc00c00 0x084e7e1878fc00c0

def z818 : W := mkw 0x011b44750000000c 0x0011b44750000000 0x2f1ffe7f80000000 0x92f1ffe7f8000000

def z819 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0007fc70004 0x1f7ffe0007fc7000

def z820 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff80c03304 0xfffffffff80c0330

def z821 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd03c61ff88ff3ffd 0xfd03c61ff88ff3ff

def z822 : W := mkw 0x4159112621144c51 0x04159112621144c5 0x73181166703fccff 0xb73181166703fccf

def z823 : W := mkw 0x47bee0026efe0453 0xe47bee0026efe045 0xf7ffe0007fff00f7 0x1f7ffe0007fff00f

def z824 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfbd81e787f3ff0ff 0xffbd81e787f3ff0f

def z825 : W := mkw 0x83fb5df52014002d 0x083fb5df52014002 0xffffffff80180030 0xfffffffff8018003

def z826 : W := mkw 0x02a00a805580ea02 0x102a00a805580ea0 0x7b201e807fc0ff0f 0x67b201e807fc0ff0

def z827 : W := mkw 0x2004a00a8a6b15c0 0xc2004a00a8a6b15c 0xd02c619f8fff3fcf 0xfd02c619f8fff3fc

def z828 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf32c619ff8e73fcf 0xff32c619ff8e73fc

def z829 : W := mkw 0x06a6e0006efe0003 0xe06a6e0006efe000 0xb4f7e0007fff0007 0x1b4f7e0007fff000

def z830 : W := mkw 0x07bee8806efe0003 0xe07bee8806efe000 0xffffee807fff0007 0x5ffffee807fff000

def z831 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x6ffffeff80000000 0xd6ffffeff8000000

def z832 : W := mkw 0x03fb5df50100480c 0x003fb5df50100480 0xffffffff8f000c00 0xfffffffff8f000c0

def z833 : W := mkw 0x02e11ba55580ea06 0x102e11ba55580ea0 0xfbe01f87ffc0ff0f 0x6fbe01f87ffc0ff0

def z834 : W := mkw 0xe11da47eaa7f15f9 0xce11da47eaa7f15f 0x041fe07f803f00f0 0x9041fe07f803f00f

def z835 : W := mkw 0x27bee002eefe0543 0xe27bee002eefe054 0xf7ffe187ffff3f0f 0x7f7ffe187ffff3f0

def z836 : W := mkw 0x87ba46587495b0ab 0x287ba46587495b0a 0x4b080e1870073004 0x44b080e187007300

def z837 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0x27d3800077df0006 0x027d3800077df000

def z838 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c619f88ffffff 0xfd02c619f88fffff

def z839 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffef9f80000000 0x5ffffef9f8000000

def z840 : W := mkw 0x2004a00a8a6b15c0 0xc2004a00a8a6b15c 0xf4fff1ff8fffffff 0xff4fff1ff8ffffff

def z841 : W := mkw 0x03ba400064940003 0x003ba40006494000 0xf7ffe0007fff0007 0x1f7ffe0007fff000

def z842 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d791660738c0f2 0xbb4d791660738c0f

def z843 : W := mkw 0x400480020b284c50 0xc400480020b284c5 0xb4d790600f38ccfb 0xbb4d790600f38ccf

def z844 : W := mkw 0x03fb5df501004a0c 0x103fb5df501004a0 0xffffffff80000f00 0xfffffffff80000f0

def z845 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb181f78783ffcff 0xffb181f78783ffcf

def z846 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7ffe0067fff00c7 0x9f7ffe0067fff00c

def z847 : W := mkw 0xa7ba6658f4d7b1ab 0x2a7ba6658f4d7b1a 0x4b286e99f0c73304 0x44b286e99f0c7330

def z848 : W := mkw 0xe041177e9101fdf8 0x0e041177e9101fdf 0x08001fff8000fff8 0xe08001fff8000fff

def z849 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x7fdffe7f80000000 0xf7fdffe7f8000000

def z850 : W := mkw 0x02e359a500000004 0x002e359a50000000 0xffefff9f80000000 0xfffefff9f8000000

def z851 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0007fff3f0f 0x1f7ffe0007fff3f0

def z852 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff8f000003 0xfffffffff8f00000

def z853 : W := mkw 0x4041912603084c50 0x44041912603084c5 0xb4d391660f18ccfb 0xab4d391660f18ccf

def z854 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0xfb201f807fc0ff0f 0x6fb201f807fc0ff0

def z855 : W := mkw 0x011ca0002a7e0001 0xc011ca0002a7e000 0xf7ffe0007fff0007 0x1f7ffe0007fff000

def z856 : W := mkw 0x0041112401004800 0x0004111240100480 0xb4d791660f38ccfb 0xbb4d791660f38ccf

def z857 : W := mkw 0x03bb44750000000c 0x003bb44750000000 0xfffffe7f80000000 0xffffffe7f8000000

def z858 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xcfffefff80000000 0xdcfffefff8000000

def z859 : W := mkw 0x43fb5df50100481c 0x043fb5df50100481 0xffffffff8000c030 0xfffffffff8000c03

def z860 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7fff1667fffccff 0xbf7fff1667fffccf

def z861 : W := mkw 0x011b46755580ea0e 0x1011b46755580ea0 0x041fe07fffc0ff0f 0x9041fe07fffc0ff0

def z862 : W := mkw 0x87ba6ed974d7b0af 0x287ba6ed974d7b0a 0x4b286e99f0c73004 0x44b286e99f0c7300

def z863 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xabe01f807fc0ff0f 0x0abe01f807fc0ff0

def z864 : W := mkw 0xc0411fff1101fcfc 0x0c0411fff1101fcf 0x08001fff8000fcf8 0xe08001fff8000fcf

def z865 : W := mkw 0x4045b1260b6a4c50 0xc4045b1260b6a4c5 0xb4f7f1660ff8ccfb 0xbb4f7f1660ff8ccf

def z866 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xebe01f807fc0ff06 0x4ebe01f807fc0ff0

def z867 : W := mkw 0x400580260b284c50 0xc400580260b284c5 0xb4d780660f38ccfb 0x9b4d780660f38ccf

def z868 : W := mkw 0x03fa598000000000 0x003fa59800000000 0xffffff9f80000000 0xfffffff9f8000000

def z869 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x67fbe0007fff0007 0x067fbe0007fff000

def z870 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4dff17f8f38ccfb 0xbb4dff17f8f38ccf

def z871 : W := mkw 0xc041177c1101f8b8 0x0c041177c1101f8b 0x08001e780000f0f8 0xe08001e780000f0f

def z872 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0xf7fb80007fff0007 0x1f7fb80007fff000

def z873 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4f7f1e78f38ccfb 0xbb4f7f1e78f38ccf

def z874 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01f807ff8ffff 0x6fbe01f807ff8fff

def z875 : W := mkw 0x03bb4cf50000000c 0x003bb4cf50000000 0xffffeeff80000000 0xdffffeeff8000000

def z876 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01e007fc0ff0f 0x0fbe01e007fc0ff0

def z877 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d791ff8f38ccfb 0xfb4d791ff8f38ccf

def z878 : W := mkw 0x015b5df50000000c 0x0015b5df50000000 0x0c1ffe7f80000000 0x90c1ffe7f8000000

def z879 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0x27db8000773f0002 0x127db8000773f000

def z880 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x3b181e78703fc0fb 0xb3b181e78703fc0f

def z881 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0xb4d791660ff8cffb 0xbb4d791660ff8cff

def z882 : W := mkw 0x07bee8816efe0007 0xe07bee8816efe000 0xf7ffe081ffff0007 0x1f7ffe081ffff000

def z883 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b381ef870fff3ff 0xf7b381ef870fff3f

def z884 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xa7f7e0007fff0007 0x0a7f7e0007fff000

def z885 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe19fffff3f0f 0xff7ffe19fffff3f0

def z886 : W := mkw 0x27bee002eefe0543 0xe27bee002eefe054 0xf7ffe19fffff0f07 0xff7ffe19fffff0f0

def z887 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7fff0007fffc00f 0x3f7fff0007fffc00

def z888 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0007fff00cf 0xbf7ffe0007fff00c

def z889 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x6be01e807fc0ff0f 0x46be01e807fc0ff0

def z890 : W := mkw 0x03ba445000000008 0x003ba44500000000 0xffffffff80000000 0xfffffffff8000000

def z891 : W := mkw 0x604591268b284d50 0xc604591268b284d5 0xb4d791e78f38cffb 0xbb4d791e78f38cff

def z892 : W := mkw 0x60411bae9101ffd0 0x160411bae9101ffd 0x08001fff8000fff8 0xe08001fff8000fff

def z893 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe41f867fc0ff0f 0xffbe41f867fc0ff0

def z894 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d391600f38ccfb 0x2b4d391600f38ccf

def z895 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xb7d780007fff0007 0x1b7d780007fff000

def z896 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b101e60703ff0ff 0x67b101e60703ff0f

def z897 : W := mkw 0x4041912403084810 0x4404191240308481 0x24d390600738c0fb 0x024d390600738c0f

def z898 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbf01fe07fd8ff3f 0x6fbf01fe07fd8ff3

def z899 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7fff0607fff0007 0xbf7fff0607fff000

def z900 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbf01f807ff8ff0f 0x7fbf01f807ff8ff0

def z901 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff8000c0f8 0xfffffffff8000c0f

def z902 : W := mkw 0xa11c2652b876a569 0x8a11c2652b876a56 0xab347fe7f8d8cf32 0x0ab347fe7f8d8cf3

def z903 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0xb4d7f1678f38ccfb 0xbb4d7f1678f38ccf

def z904 : W := mkw 0x0118045020140009 0x0011804502014000 0x7b181e78703fc0ff 0xf7b181e78703fc0f

def z905 : W := mkw 0x004591240a280000 0xc004591240a28000 0xb4d791660f38c0fb 0xbb4d791660f38c0f

def z906 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff8018c032 0xfffffffff8018c03

def z907 : W := mkw 0x43beccd30b284c5c 0xc43beccd30b284c5 0x4b286e998f38ccfb 0x44b286e998f38ccf

def z908 : W := mkw 0x404591240b284810 0xc404591240b28481 0xb4d790600f38c0fb 0xbb4d790600f38c0f

def z909 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c619f88c73f0d 0x6d02c619f88c73f0

def z910 : W := mkw 0x00435df50000000c 0x000435df50000000 0x0c07ffff80000000 0xe0c07ffff8000000

def z911 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7ffe0007fff0ccf 0x1f7ffe0007fff0cc

def z912 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xc7efe0007fff0007 0x0c7efe0007fff000

def z913 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x8cffffff80000000 0xf8cffffff8000000

def z914 : W := mkw 0x06a6e0006efe0003 0xe06a6e0006efe000 0x84e7e0007fc70004 0x084e7e0007fc7000

def z915 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d791660ff8ffff 0xbb4d791660ff8fff

def z916 : W := mkw 0x811a46583015b0a9 0x0811a46583015b0a 0x7f1ffe78703ff0ff 0xf7f1ffe78703ff0f

def z917 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4f791660ff8ccff 0xbf4f791660ff8ccf

def z918 : W := mkw 0x2000200a804315c0 0x02000200a804315c 0x5028619f80e73fcd 0xf5028619f80e73fc

def z919 : W := mkw 0x07fbdff5779cea0f 0x707fbdff5779cea0 0x2fd39e607718c002 0x02fd39e607718c00

def z920 : W := mkw 0x4045b1260b6a4c50 0xc4045b1260b6a4c5 0xb4d791660fffccff 0xbb4d791660fffccf

def z921 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0007fffc0ff 0x1f7ffe0007fffc0f

def z922 : W := mkw 0x03bb4cf50000000c 0x003bb4cf50000000 0x7f3ffeff80000000 0xf7f3ffeff8000000

def z923 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181ff8703fffff 0xf7b181ff8703ffff

def z924 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x84d781660f38ccfb 0x984d781660f38ccf

def z925 : W := mkw 0x07bee4506efe000b 0xe07bee4506efe000 0xfffffe607fff0007 0x1fffffe607fff000

def z926 : W := mkw 0x02e35ba55580ea06 0x102e35ba55580ea0 0xffefff9fffc0ff0f 0xfffefff9fffc0ff0

def z927 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0xf7fbe0007fdf0007 0x0f7fbe0007fdf000

def z928 : W := mkw 0x2000200880431180 0x0200020088043118 0xd02c619f88c73f0d 0xfd02c619f88c73f0

def z929 : W := mkw 0x2000200a804315c0 0x02000200a804315c 0xd028619f88c73fcd 0xed028619f88c73fc

def z930 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xafffffff80000000 0x9afffffff8000000

def z931 : W := mkw 0x03fb5df50100480c 0x003fb5df50100480 0xffffffff8f38ccfb 0xfffffffff8f38ccf

def z932 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xa4d791660f18ccfa 0xaa4d791660f18ccf

def z933 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xcbe01f807fc0ff0c 0x6cbe01f807fc0ff0

def z934 : W := mkw 0x02e119a400000000 0x002e119a40000000 0xffffffff80000000 0xfffffffff8000000

def z935 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01fe07fc0ffff 0xefbe01fe07fc0fff

def z936 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01f807fe0ffcf 0xffbe01f807fe0ffc

def z937 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0x27dbe000771f0002 0x027dbe000771f000

def z938 : W := mkw 0x03fb5df545804a0e 0x103fb5df545804a0 0xffffffff8fc0cf0b 0xfffffffff8fc0cf0

def z939 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbec7f807fc0ff0f 0x7fbec7f807fc0ff0

def z940 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7ffe19fffff0ccf 0xff7ffe19fffff0cc

def z941 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4fff1660f38ccfb 0xbf4fff1660f38ccf

def z942 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x24d391660f38ccfb 0xa24d391660f38ccf

def z943 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe81f807fe7ff0f 0x7fbe81f807fe7ff0

def z944 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xe7ffe0007fdf0006 0x0e7ffe0007fdf000

def z945 : W := mkw 0x4041912603084c50 0x44041912603084c5 0xb4d791660718ccfa 0xbb4d791660718ccf

def z946 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4df917e0f38ccfb 0xff4df917e0f38ccf

def z947 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff802000c9 0xfffffffff802000c

def z948 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbf01fe07fc0ff0f 0xffbf01fe07fc0ff0

def z949 : W := mkw 0x07beecd16efe000f 0xe07beecd16efe000 0xffffee007fff0007 0x1ffffee007fff000

def z950 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff80380003 0xfffffffff8038000

def z951 : W := mkw 0x404599a60b284c50 0xc404599a60b284c5 0xbcd79fe60f38ccfb 0xfbcd79fe60f38ccf

def z952 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffefff9f80000000 0x6ffefff9f8000000

def z953 : W := mkw 0x07bee4506efe000b 0xe07bee4506efe000 0xffffffffffff0007 0xfffffffffffff000

def z954 : W := mkw 0x03fb5df52014000d 0x003fb5df52014000 0xffffffff803f0000 0xfffffffff803f000

def z955 : W := mkw 0x0404a0006efe0003 0xe0404a0006efe000 0xf4ffe0007fff0007 0x1f4ffe0007fff000

def z956 : W := mkw 0x07bee4506efe000b 0xe07bee4506efe000 0xffffee187fff0007 0x5ffffee187fff000

def z957 : W := mkw 0x015b5df50000000c 0x0015b5df50000000 0xdc3fffff80000000 0xfdc3fffff8000000

def z958 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xaff7ffff80000000 0xeaff7ffff8000000

def z959 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff88000c09 0xfffffffff88000c0

def z960 : W := mkw 0x06a6e0006efe0003 0xe06a6e0006efe000 0xd4efe0007fff0007 0x1d4efe0007fff000

def z961 : W := mkw 0x03fb5df56494000f 0x003fb5df56494000 0xffffffffffff0007 0xfffffffffffff000

def z962 : W := mkw 0x03bb4cf50000000c 0x003bb4cf50000000 0x4f2fee9f80000000 0x44f2fee9f8000000

def z963 : W := mkw 0x4045b1260b6a4c50 0xc4045b1260b6a4c5 0xf4fff1ff8fffccff 0xff4fff1ff8fffccf

def z964 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xcfefffff80000000 0xecfefffff8000000

def z965 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xfffffe007fff0007 0x7fffffe007fff000

def z966 : W := mkw 0x811a46593015b0ad 0x0811a46593015b0a 0x7b187e79f03ff0ff 0xf7b187e79f03ff0f

def z967 : W := mkw 0x4041912603084c50 0x44041912603084c5 0x24d390660718c0f2 0x824d390660718c0f

def z968 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x3b101e60703ff0ff 0xb3b101e60703ff0f

def z969 : W := mkw 0x02a00a805480a202 0x102a00a805480a20 0xfbe00f807fc03f0f 0x6fbe00f807fc03f0

def z970 : W := mkw 0x0000800002080000 0x4000080000208000 0x34d390600738c0fb 0xb34d390600738c0f

def z971 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff88c00005 0xfffffffff88c0000

def z972 : W := mkw 0x03fb5df54480000e 0x003fb5df54480000 0xffffffff8fc00000 0xfffffffff8fc0000

def z973 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xb7dfe0007f3f0003 0x1b7dfe0007f3f000

def z974 : W := mkw 0x27bee002eefe0543 0xe27bee002eefe054 0xf7ffe187ffff0fcf 0xbf7ffe187ffff0fc

def z975 : W := mkw 0x6004a00a8a6b15d0 0xc6004a00a8a6b15d 0xd02c619f88ff3ffd 0xfd02c619f88ff3ff

def z976 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x77db80007fff0007 0x177db80007fff000

def z977 : W := mkw 0x07beecd16efe000f 0xe07beecd16efe000 0xffffef9fffff0007 0xfffffef9fffff000

def z978 : W := mkw 0x0000000800011080 0x0000000080001108 0xd02c619f88e73fcd 0xfd02c619f88e73fc

def z979 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x402c619f80e73fcc 0xf402c619f80e73fc

def z980 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d790600f38ccfb 0x1b4d790600f38ccf

def z981 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0xf7ffe000773f0007 0x1f7ffe000773f000

def z982 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4df91660f3fccff 0xbf4df91660f3fccf

def z983 : W := mkw 0x03fb5df54480020e 0x103fb5df54480020 0xffffffff80c00300 0xfffffffff80c0030

def z984 : W := mkw 0x07bee4506efe000b 0xe07bee4506efe000 0xf7ffe0787fff0007 0x9f7ffe0787fff000

def z985 : W := mkw 0x03bec0002a3c0001 0xc03bec0002a3c000 0xf7ffe0007f3f0007 0x1f7ffe0007f3f000

def z986 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181e60703ff0ff 0x17b181e60703ff0f

def z987 : W := mkw 0x42e11ba45580ea12 0x142e11ba45580ea1 0xfbe01fe07fc0ff3f 0x6fbe01fe07fc0ff3

def z988 : W := mkw 0x02a002005480a002 0x002a002005480a00 0xfbe01f807fc0ff0f 0x6fbe01f807fc0ff0

def z989 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xc02c619f88e73fc4 0xdc02c619f88e73fc

def z990 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe099ffff0007 0x5f7ffe099ffff000

def z991 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe00f807fc03f07 0x4fbe00f807fc03f0

def z992 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xffd79f660f38ccfb 0xfffd79f660f38ccf

def z993 : W := mkw 0x2000200a804315c0 0x02000200a804315c 0xd02c619f80c73fcc 0xfd02c619f80c73fc

def z994 : W := mkw 0x02e11ba45580ea02 0x102e11ba45580ea0 0xffe79f867fc0ff0f 0x6ffe79f867fc0ff0

def z995 : W := mkw 0x02e11ba45580ea02 0x102e11ba45580ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z996 : W := mkw 0x27bee000eefe0103 0xe27bee000eefe010 0xf7ffe081ffff0307 0x1f7ffe081ffff030

def z997 : W := mkw 0x015b5df50000000c 0x0015b5df50000000 0x7f1fffff80000000 0xf7f1fffff8000000

def z998 : W := mkw 0x000480020a280440 0xc000480020a28044 0xb4d791660f38ccfb 0xbb4d791660f38ccf

def z999 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x27dfe0007fff0007 0x127dfe0007fff000

def z1000 : W := mkw 0xa404a20afeffb5e3 0xea404a20afeffb5e 0x000000007fffffff 0x0000000007ffffff

def z1001 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x4f3fffff80000000 0xf4f3fffff8000000

def z1002 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf03c71ff88e73fcd 0xff03c71ff88e73fc

def z1003 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7ffe1867fff3fcf 0xff7ffe1867fff3fc

def z1004 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff80270005 0xfffffffff8027000

def z1005 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x24d390600738c0f2 0x024d390600738c0f

def z1006 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xfb2c7f9f88e73fcd 0xffb2c7f9f88e73fc

def z1007 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0x4b201f807fc0ff0f 0x64b201f807fc0ff0

def z1008 : W := mkw 0x02a002005580ea02 0x102a002005580ea0 0xfbe01e007fc0ff0f 0x6fbe01e007fc0ff0

def z1009 : W := mkw 0x051ca0006efe0003 0xe051ca0006efe000 0xf7df80007fff0007 0x1f7df80007fff000

def z1010 : W := mkw 0x011b44750000000c 0x0011b44750000000 0x0c1ffe7f80000000 0xf0c1ffe7f8000000

def z1011 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x802c619f88e73fc8 0xf802c619f88e73fc

def z1012 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x6b181e78703ff0f6 0xd6b181e78703ff0f

def z1013 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x4028619f88e73fcd 0xe4028619f88e73fc

def z1014 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0x802c619f88e73fcd 0x9802c619f88e73fc

def z1015 : W := mkw 0x0004200008620000 0x8000420000862000 0xd02c619f88e73f0d 0xfd02c619f88e73f0

def z1016 : W := mkw 0x4041912403084810 0x4404191240308481 0x24d390600718c0fa 0xa24d390600718c0f

def z1017 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xf02c719f88e7ffcf 0xff02c719f88e7ffc

def z1018 : W := mkw 0xa1180658b015b1a9 0x0a1180658b015b1a 0x7b181ef9f03ff3ff 0xf7b181ef9f03ff3f

def z1019 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0607fff00f7 0x9f7ffe0607fff00f

def z1020 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7fff0607fffc037 0x1f7fff0607fffc03

def z1021 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x24d791660738ccfa 0xb24d791660738ccf

def z1022 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x4b081e78703ff0ff 0xe4b081e78703ff0f

def z1023 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b101e78703ff0ff 0xe2b101e78703ff0f

def z1024 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c71ff88e7fffd 0xfd02c71ff88e7fff

def z1025 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0x24d790660f38ccfb 0x924d790660f38ccf

def z1026 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b101e60703fc0f2 0x02b101e60703fc0f

def z1027 : W := mkw 0x62e5b9a6cfea4f52 0xd62e5b9a6cfea4f5 0x84e7e1878fc00f00 0x084e7e1878fc00f0

def z1028 : W := mkw 0x03fb5df52014000d 0x003fb5df52014000 0xfffffffff0180002 0xffffffffff018000

def z1029 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe0187fff0007 0xff7ffe0187fff000

def z1030 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xbfdfff7f80000000 0xbbfdfff7f8000000

def z1031 : W := mkw 0x03fb5df50100480c 0x003fb5df50100480 0xffffffff8700c002 0xfffffffff8700c00

def z1032 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c619f88c73f04 0xfd02c619f88c73f0

def z1033 : W := mkw 0x03bb4cf50000000c 0x003bb4cf50000000 0xdf3fefff80000000 0xfdf3fefff8000000

def z1034 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0xf4fff1ff8ff8cffb 0xff4fff1ff8ff8cff

def z1035 : W := mkw 0x01188000221c0001 0x401188000221c000 0x77db8000773f0007 0x177db8000773f000

def z1036 : W := mkw 0x4045b1260b6a4c50 0xc4045b1260b6a4c5 0xb4dff1660f3fccfb 0xbb4dff1660f3fccf

def z1037 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb3c7e78703ff0ff 0xffb3c7e78703ff0f

def z1038 : W := mkw 0x02e35df50000000c 0x002e35df50000000 0xbcf7ffff80000000 0xfbcf7ffff8000000

def z1039 : W := mkw 0x02e25b805580ea02 0x102e25b805580ea0 0xffe7ff807fc0ff0f 0x6ffe7ff807fc0ff0

def z1040 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x6b181e78703ff0ff 0x46b181e78703ff0f

def z1041 : W := mkw 0x811806503014a029 0x0811806503014a02 0x7b181e60703fc0ff 0xb7b181e60703fc0f

def z1042 : W := mkw 0x03fb5df54580480e 0x003fb5df54580480 0xffffffffffc0cc0f 0xfffffffffffc0cc0

def z1043 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4f791e60f38ccfb 0xff4f791e60f38ccf

def z1044 : W := mkw 0x800002083015b0a1 0x0800002083015b0a 0x7b101e60703ff0ff 0xf7b101e60703ff0f

def z1045 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xb4d791e60f38fffb 0xfb4d791e60f38fff

def z1046 : W := mkw 0xa51ee45aaa7f15e9 0xea51ee45aaa7f15e 0x041fe07f803f00f0 0x9041fe07f803f00f

def z1047 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xdbe00f807fc03f0d 0x6dbe00f807fc03f0

def z1048 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb381ff8703ff0ff 0xffb381ff8703ff0f

def z1049 : W := mkw 0x02e35df50000000c 0x002e35df50000000 0xdcefffff80000000 0xfdcefffff8000000

def z1050 : W := mkw 0x03bb4cf50000000c 0x003bb4cf50000000 0x0f1fee7f80000000 0x90f1fee7f8000000

def z1051 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x84ffe0007fff0007 0x184ffe0007fff000

def z1052 : W := mkw 0x00401b805580ea02 0x100401b805580ea0 0x7b001f807fc0ff0f 0x67b001f807fc0ff0

def z1053 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xdfefef9f80000000 0xfdfefef9f8000000

def z1054 : W := mkw 0x0404a0006efe0003 0xe0404a0006efe000 0x24d380007fff0007 0x024d380007fff000

def z1055 : W := mkw 0x06a4a0006efe0003 0xe06a4a0006efe000 0xf7f780007fff0007 0x1f7f780007fff000

def z1056 : W := mkw 0x4041912603084c50 0x44041912603084c5 0x34d391660738ccfb 0xb34d391660738ccf

def z1057 : W := mkw 0x06a6e0006efe0003 0xe06a6e0006efe000 0x04c380007fff0007 0x004c380007fff000

def z1058 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe1807fff0007 0x7f7ffe1807fff000

def z1059 : W := mkw 0x000002005580ea02 0x1000002005580ea0 0x4b000e007fc0ff0f 0x44b000e007fc0ff0

def z1060 : W := mkw 0x251fe47faa7f15cd 0xe251fe47faa7f15c 0x041fe07f803f00c0 0x9041fe07f803f00c

def z1061 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe01f9fffc0ff0f 0xefbe01f9fffc0ff0

def z1062 : W := mkw 0x07bae00066de0003 0x607bae00066de000 0x77fbe00077ff0007 0x177fbe00077ff000

def z1063 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4fff1ff8ff8ffff 0xff4fff1ff8ff8fff

def z1064 : W := mkw 0x2404a20affffffc3 0xf2404a20affffffc 0x000000007fffffcf 0x0000000007fffffc

def z1065 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xa7ffe0007fff0002 0x1a7ffe0007fff000

def z1066 : W := mkw 0x02e35ba55580ea06 0x102e35ba55580ea0 0xfff7ffe7ffc0ff0f 0xffff7ffe7ffc0ff0

def z1067 : W := mkw 0x02a4a0004eea0002 0xc02a4a0004eea000 0xf7ffe0007fff0007 0x1f7ffe0007fff000

def z1068 : W := mkw 0x02a00a805580ea02 0x102a00a805580ea0 0xfbe00e807fc0ff0f 0x4fbe00e807fc0ff0

def z1069 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b387ef9f03ff0ff 0xf7b387ef9f03ff0f

def z1070 : W := mkw 0x07beecd16efe000f 0xe07beecd16efe000 0xfffffef9ffff0007 0xffffffef9ffff000

def z1071 : W := mkw 0x02e35ba55580ea06 0x102e35ba55580ea0 0xffe39f807fc0ff0f 0x6ffe39f807fc0ff0

def z1072 : W := mkw 0x011b4cf50000000c 0x0011b4cf50000000 0x0c1feeff80000000 0xd0c1feeff8000000

def z1073 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff8000300d 0xfffffffff8000300

def z1074 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0xf4fff1e78fffcfff 0xbf4fff1e78fffcff

def z1075 : W := mkw 0x0159157400000008 0x0015915740000000 0xffffffff80000000 0xfffffffff8000000

def z1076 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xffffffff803800f0 0xfffffffff803800f

def z1077 : W := mkw 0x03fb5df54480000e 0x003fb5df54480000 0xfffffffff7000002 0xffffffffff700000

def z1078 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0xfffffffff0000007 0xffffffffff000000

def z1079 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xabe01f807fc0ff0a 0x6abe01f807fc0ff0

def z1080 : W := mkw 0x800006583015b0a9 0x0800006583015b0a 0x7b001e78703ff0ff 0xe7b001e78703ff0f

def z1081 : W := mkw 0x07bac000669c0003 0x607bac000669c000 0x27d38000773f0007 0x027d38000773f000

def z1082 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xd02c619f88e73f05 0x5d02c619f88e73f0

def z1083 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xa4d791660f38ccf2 0x9a4d791660f38ccf

def z1084 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0x77dfe000773f0007 0x177dfe000773f000

def z1085 : W := mkw 0x02a00a805580ea02 0x102a00a805580ea0 0x4b200e807fc03f04 0x44b200e807fc03f0

def z1086 : W := mkw 0x03fb5df52014000d 0x003fb5df52014000 0xfffffffff0070004 0xffffffffff007000

def z1087 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7efe0007fc70007 0x0f7efe0007fc7000

def z1088 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xffdf9e78703ff0ff 0xfffdf9e78703ff0f

def z1089 : W := mkw 0x02e35df50000000c 0x002e35df50000000 0x8ce7ef9f80000000 0x48ce7ef9f8000000

def z1090 : W := mkw 0x0404a0006efe0003 0xe0404a0006efe000 0x84c780007fff0007 0x084c780007fff000

def z1091 : W := mkw 0x004491000b284800 0xc004491000b28480 0xb4d791600f38ccfb 0xbb4d791600f38ccf

def z1092 : W := mkw 0x400580260a280450 0xc400580260a28045 0xb4d790660f38c0fb 0xbb4d790660f38c0f

def z1093 : W := mkw 0x004013001100e800 0x0004013001100e80 0xfbe01f807fc0ff0f 0x6fbe01f807fc0ff0

def z1094 : W := mkw 0x46e7f9a64fea4e52 0xf46e7f9a64fea4e5 0x84e7e1860fc00f00 0x084e7e1860fc00f0

def z1095 : W := mkw 0x6045b1268b6a4d50 0xc6045b1268b6a4d5 0xf4f7f1e78ff8ffff 0xff4f7f1e78ff8fff

def z1096 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x4b181e78703ff0fc 0xf4b181e78703ff0f

def z1097 : W := mkw 0x07bee4516efe000f 0xe07bee4516efe000 0xf7ffe019ffff0007 0x1f7ffe019ffff000

def z1098 : W := mkw 0x02e0198044800002 0x002e019804480000 0xfbe01f807fc03f0f 0x6fbe01f807fc03f0

def z1099 : W := mkw 0x2004200a886315c0 0x82004200a886315c 0xc02c619f88c73fcc 0xec02c619f88c73fc

def z1100 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf4d791660f38fcff 0xff4d791660f38fcf

def z1101 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfbe87f99ffc0ff0f 0x6fbe87f99ffc0ff0

def z1102 : W := mkw 0x07bee4506efe000b 0xe07bee4506efe000 0xfffffe787fffc0ff 0xffffffe787fffc0f

def z1103 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb3c7ffff8ffffff 0xffb3c7ffff8fffff

def z1104 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x7b181e78703fc0f7 0x97b181e78703fc0f

def z1105 : W := mkw 0x03fb5df54480000e 0x003fb5df54480000 0xffffffffffc03f0f 0xfffffffffffc03f0

def z1106 : W := mkw 0x07bee0026efe0443 0xe07bee0026efe044 0xf7ffe1067fff0c07 0x1f7ffe1067fff0c0

def z1107 : W := mkw 0x011b44750000000c 0x0011b44750000000 0x4f1fee7f80000000 0xd4f1fee7f8000000

def z1108 : W := mkw 0x03fb5df50000000c 0x003fb5df50000000 0x2fdfffff80000000 0xf2fdfffff8000000

def z1109 : W := mkw 0x404591260b284c50 0xc404591260b284c5 0xf7d791667f38ccff 0xbf7d791667f38ccf

def z1110 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0xfb1c1f7e703ff0ff 0xffb1c1f7e703ff0f

def z1111 : W := mkw 0x03fb5df545804a0e 0x103fb5df545804a0 0xffffffff87000000 0xfffffffff8700000

def z1112 : W := mkw 0x02a00a805580ea02 0x102a00a805580ea0 0x0b000e007fc0ff0f 0x00b000e007fc0ff0

def z1113 : W := mkw 0x811806583015b0a9 0x0811806583015b0a 0x2b181e78703ff0ff 0x92b181e78703ff0f

def z1114 : W := mkw 0x02e01b805580ea02 0x102e01b805580ea0 0xfff79f807fc0ff0f 0x7fff79f807fc0ff0

def z1115 : W := mkw 0x07bee0006efe0003 0xe07bee0006efe000 0xf7ffe01fffff0007 0x9f7ffe01fffff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z8,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z9,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z10])],[(0,[z0,z1,z2,z3,z11,z5,z6]),(0,[z12,z1,z2,z3,z5,z6,z13]),(1,[z14,z1,z2,z3,z5,z6]),(0,[z0,z15,z1,z2,z3,z5,z6])],[(0,[z16,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z17,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z6])],[(0,[z19,z0,z20,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z22,z3,z5,z6]),(0,[z23,z0,z1,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z6,z25]),(0,[z0,z1,z2,z26,z3,z5,z6]),(0,[z0,z1,z2,z27,z3,z5,z6]),(0,[z0,z28,z1,z2,z3,z5,z29])],[(0,[z0,z1,z30,z31,z3,z5,z6]),(0,[z32,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z33])],[(0,[z34,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z35,z6]),(0,[z0,z1,z2,z3,z5,z36,z6]),(0,[z0,z1,z2,z3,z37,z5,z6]),(0,[z38,z0,z1,z2,z3,z6,z39])],[(0,[z40,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z41,z6]),(0,[z0,z1,z2,z42,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z43,z6]),(0,[z0,z1,z31,z44,z3,z5,z6])],[(0,[z0,z45,z1,z2,z3,z5,z6]),(1,[z19,z0,z2,z3,z5,z29]),(0,[z0,z1,z2,z46,z3,z5,z6]),(0,[z0,z47,z1,z2,z3,z5,z6])]],
   [[(0,[z48,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z49,z5,z6]),(0,[z0,z1,z2,z50,z3,z5,z51])],[(0,[z21,z0,z1,z52,z3,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z54,z0,z1,z31,z3,z5,z6]),(0,[z0,z55,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z56,z6]),(0,[z57,z0,z1,z2,z3,z5,z6]),(0,[z0,z28,z58,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z59]),(0,[z38,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z60,z6]),(0,[z61,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z30,z3,z5,z62])],[(0,[z0,z1,z63,z2,z3,z5,z6]),(0,[z0,z1,z64,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z65,z6])],[(0,[z0,z1,z2,z3,z5,z66,z6]),(0,[z0,z1,z2,z3,z67,z5,z6]),(0,[z0,z1,z2,z3,z68,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z69]),(1,[z0,z1,z3,z5,z6,z70])],[(0,[z71,z72,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z73,z3,z5,z6]),(1,[z74,z1,z2,z3,z5,z6]),(0,[z75,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z76,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z77,z5,z6]),(0,[z78,z74,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z79]),(0,[z0,z80,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z81,z5,z6]),(0,[z0,z82,z1,z2,z3,z5,z6]),(0,[z0,z1,z83,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z84,z5,z6]),(1,[z85,z0,z1,z2,z5,z51])],[(0,[z0,z1,z2,z3,z5,z6,z86]),(0,[z0,z1,z2,z3,z87,z5,z6]),(1,[z38,z0,z1,z2,z3,z39]),(0,[z0,z1,z2,z3,z5,z6,z88])],[(0,[z89,z0,z1,z2,z3,z5,z6]),(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z91,z0,z1,z2,z3,z5,z6])],[(0,[z71,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z92,z5,z6]),(0,[z93,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z94,z2,z3,z5,z6]),(0,[z0,z1,z2,z95,z3,z5,z6]),(0,[z0,z1,z2,z3,z96,z5,z6]),(1,[z97,z0,z1,z2,z98,z6]),(0,[z0,z1,z99,z2,z3,z5,z6]),(0,[z0,z1,z2,z50,z3,z5,z100])],[(0,[z0,z1,z2,z3,z101,z5,z6]),(0,[z0,z1,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z103,z5,z6]),(0,[z0,z1,z3,z104,z5,z62,z6]),(0,[z0,z1,z2,z3,z5,z6,z105]),(0,[z0,z1,z2,z3,z5,z6,z106])],[(0,[z0,z1,z2,z107,z3,z5,z6]),(0,[z0,z1,z108,z2,z3,z5,z6]),(0,[z109,z0,z110,z2,z3,z5,z6]),(0,[z0,z1,z111,z2,z3,z5,z6]),(0,[z112,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z113,z6]),(0,[z0,z28,z1,z2,z3,z5,z114]),(1,[z115,z0,z1,z116,z5,z6]),(1,[z0,z1,z117,z3,z5,z6])],[(0,[z0,z1,z2,z3,z118,z5,z6]),(1,[z0,z119,z2,z3,z5,z6])],[(0,[z120,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z121,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z122,z5,z6]),(0,[z0,z1,z2,z3,z5,z123,z6]),(0,[z0,z1,z2,z3,z124,z125,z6]),(0,[z0,z1,z2,z3,z5,z126,z6]),(0,[z0,z1,z2,z3,z5,z127,z6]),(0,[z0,z1,z2,z3,z5,z128,z6]),(0,[z0,z1,z2,z3,z5,z6,z129])]],
   [[(0,[z0,z1,z130,z2,z3,z5,z6]),(0,[z131,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z132])],[(0,[z0,z1,z2,z133,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z134,z6]),(0,[z0,z58,z1,z135,z3,z5,z6])],[(0,[z0,z1,z2,z136,z3,z5,z6]),(0,[z137,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z138]),(0,[z0,z2,z3,z5,z43,z6,z29]),(0,[z139,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z140,z3,z5,z6])],[(0,[z141,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z13,z51]),(0,[z0,z1,z2,z3,z142,z5,z6]),(0,[z109,z143,z1,z2,z3,z5,z6]),(0,[z115,z0,z1,z3,z116,z5,z6]),(0,[z0,z1,z2,z3,z5,z144,z6])],[],[(0,[z0,z1,z145,z3,z116,z5,z6]),(0,[z0,z1,z2,z3,z5,z146,z6]),(0,[z147,z0,z1,z2,z148,z5,z6]),(0,[z149,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z150]),(0,[z0,z1,z151,z3,z5,z6,z129]),(0,[z0,z152,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z153,z5,z6])],[(0,[z154,z1,z155,z2,z3,z5,z6]),(1,[z156,z0,z2,z3,z5,z6]),(1,[z0,z55,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z157,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z158])]],
   [[(0,[z0,z159,z1,z2,z3,z5,z6]),(0,[z0,z110,z1,z2,z160,z5,z6]),(0,[z0,z161,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z162,z5,z65])],[(0,[z0,z1,z2,z3,z163,z5,z6]),(0,[z164,z0,z1,z2,z3,z5,z6]),(0,[z165,z0,z1,z2,z3,z5,z6]),(0,[z0,z58,z1,z166,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z167,z6]),(0,[z168,z0,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z98,z6])],[(0,[z169,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z170,z6]),(0,[z0,z1,z119,z2,z3,z5,z6]),(0,[z0,z171,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z116,z5,z6]),(0,[z0,z1,z2,z3,z172,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z51])],[(0,[z0,z1,z2,z3,z173,z5,z6]),(0,[z0,z1,z2,z3,z174,z5,z6]),(0,[z0,z1,z2,z3,z5,z175,z6]),(0,[z0,z176,z1,z2,z3,z5,z6])],[(0,[z14,z28,z1,z2,z3,z5,z6]),(0,[z0,z28,z2,z3,z5,z114,z6]),(0,[z0,z1,z2,z177,z3,z5,z6]),(0,[z178,z0,z1,z2,z3,z5,z6])],[(0,[z12,z120,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z179,z3,z5,z6]),(0,[z0,z1,z2,z3,z180,z5,z6])],[]],
   [[(0,[z0,z1,z2,z3,z5,z181,z6]),(0,[z182,z0,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z183,z3,z5,z6]),(0,[z0,z1,z2,z184,z3,z5,z6])],[(0,[z185,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z186,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z5,z187]),(0,[z0,z1,z2,z3,z5,z6,z188]),(0,[z0,z1,z2,z189,z116,z5,z6]),(0,[z0,z1,z2,z189,z5,z6,z51])],[(0,[z21,z0,z1,z2,z190,z5,z6]),(0,[z0,z1,z151,z3,z116,z5,z6]),(0,[z191,z0,z2,z3,z5,z6,z29]),(0,[z192,z0,z1,z2,z3,z5,z6])],[(0,[z193,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z194,z6]),(0,[z0,z1,z2,z3,z5,z195,z6]),(0,[z196,z0,z1,z2,z3,z5,z129]),(0,[z38,z0,z80,z2,z3,z5,z6])],[(0,[z0,z197,z1,z2,z3,z5,z6]),(0,[z71,z0,z2,z3,z5,z114,z6]),(0,[z0,z1,z2,z3,z5,z6,z198]),(0,[z199,z0,z1,z2,z3,z5,z6]),(0,[z196,z0,z1,z30,z3,z5,z6]),(0,[z97,z0,z1,z2,z5,z98,z6])],[(0,[z0,z200,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z201,z6]),(0,[z0,z1,z2,z3,z202,z5,z6]),(0,[z0,z1,z2,z3,z5,z203,z6]),(0,[z0,z1,z2,z204,z189,z5,z6])],[(0,[z0,z205,z2,z151,z3,z5,z6]),(0,[z0,z1,z2,z206,z3,z5,z6]),(0,[z0,z1,z2,z207,z3,z5,z6]),(0,[z208,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z2,z3,z65,z6]),(0,[z0,z1,z2,z3,z209,z5,z6])]],
   [[(1,[z78,z0,z2,z3,z43,z6]),(0,[z54,z0,z1,z2,z210,z5,z6]),(0,[z0,z211,z1,z2,z3,z5,z6])],[(0,[z23,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z30,z151,z3,z5,z6]),(0,[z0,z1,z2,z3,z212,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z213]),(0,[z38,z214,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z215]),(0,[z216,z0,z1,z2,z3,z5,z6]),(1,[z0,z217,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z124,z5,z6])],[(0,[z0,z1,z2,z3,z218,z5,z6]),(0,[z0,z1,z30,z3,z5,z62,z6])],[(0,[z0,z1,z2,z3,z5,z24,z51]),(0,[z0,z1,z2,z3,z219,z5,z6]),(0,[z0,z1,z2,z3,z5,z220,z6]),(0,[z0,z1,z2,z3,z5,z221,z6])],[(0,[z0,z1,z2,z3,z5,z6,z222]),(1,[z12,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z6,z223]),(0,[z0,z224,z1,z2,z3,z5,z6]),(1,[z0,z28,z2,z3,z5,z114])],[(0,[z0,z1,z225,z2,z3,z5,z6]),(0,[z226,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z227,z2,z3,z5,z6])]],
   [[(0,[z23,z1,z2,z3,z5,z125,z6]),(0,[z0,z228,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z229,z124,z6]),(0,[z0,z1,z2,z3,z5,z114,z51]),(0,[z0,z230,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z3,z5,z62,z6]),(0,[z0,z1,z2,z189,z124,z5,z6]),(0,[z38,z0,z1,z231,z3,z5,z6])],[(0,[z0,z232,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z233,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z3,z5,z36,z6]),(0,[z0,z1,z2,z3,z234,z5,z6]),(0,[z97,z0,z1,z2,z3,z124,z6])],[(0,[z0,z1,z2,z235,z3,z5,z6]),(1,[z236,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z237,z124,z6]),(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z238]),(0,[z0,z1,z2,z3,z5,z239,z6]),(0,[z240,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z241,z6])],[(0,[z71,z0,z2,z3,z242,z5,z6]),(0,[z0,z1,z2,z3,z243,z5,z6]),(0,[z0,z1,z2,z3,z5,z244,z6])],[(0,[z245,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z44,z3,z5,z36,z6])],[(0,[z0,z1,z2,z246,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z247,z6]),(0,[z0,z1,z2,z248,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z70,z39])],[(1,[z0,z249,z2,z3,z5,z6]),(0,[z250,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z102,z3,z104,z5,z6]),(0,[z251,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z229,z5,z43,z6]),(0,[z0,z1,z217,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z252,z2,z3,z5,z6]),(0,[z253,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z254]),(0,[z38,z0,z255,z2,z3,z5,z6])],[(0,[z154,z256,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z257,z5,z6])],[(0,[z21,z147,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z258,z6]),(0,[z0,z1,z2,z3,z5,z259,z6])],[(0,[z0,z1,z2,z260,z3,z5,z6]),(0,[z147,z1,z2,z190,z3,z5,z6]),(0,[z38,z54,z0,z1,z2,z3,z6]),(0,[z261,z0,z1,z2,z3,z5,z6]),(0,[z262,z0,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z263,z5,z6])],[(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z151,z3,z5,z6])],[(0,[z0,z28,z2,z3,z5,z43,z6]),(0,[z0,z1,z2,z3,z104,z124,z6]),(0,[z0,z264,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z162,z6]),(0,[z0,z1,z2,z3,z5,z6,z70])],[(0,[z149,z0,z1,z2,z3,z125,z6]),(0,[z265,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z266,z6]),(0,[z0,z1,z2,z3,z5,z267,z6]),(0,[z19,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z62,z6])],[(0,[z0,z1,z20,z2,z3,z5,z6]),(0,[z0,z205,z1,z151,z3,z5,z6]),(1,[z109,z0,z2,z242,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z268]),(0,[z0,z1,z2,z3,z269,z5,z6]),(0,[z0,z1,z2,z3,z5,z270,z6]),(0,[z196,z0,z1,z3,z5,z6,z129])]],
   [[(0,[z0,z1,z2,z3,z271,z5,z6])],[(0,[z272,z0,z1,z2,z3,z5,z6]),(0,[z273,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z274,z6]),(0,[z54,z0,z1,z2,z177,z5,z6])],[(0,[z275,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z276,z3,z5,z6]),(1,[z57,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z189,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z277])],[(0,[z0,z1,z2,z3,z5,z278,z6]),(0,[z279,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z280,z6]),(0,[z0,z1,z2,z3,z281,z5,z6])],[(0,[z0,z1,z249,z2,z3,z5,z6]),(0,[z0,z282,z1,z2,z3,z5,z6])],[(0,[z0,z205,z1,z102,z3,z5,z6]),(0,[z0,z1,z2,z117,z3,z5,z6])],[(0,[z21,z0,z1,z2,z3,z283,z6]),(0,[z0,z2,z3,z5,z114,z6,z29]),(1,[z196,z0,z1,z3,z5,z129])],[(1,[z256,z1,z145,z3,z5,z6]),(0,[z21,z0,z284,z2,z3,z5,z6]),(1,[z0,z1,z285,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z286])]],
   [[(0,[z287,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z102,z44,z3,z5,z6]),(0,[z109,z57,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z288]),(0,[z0,z1,z2,z3,z5,z289,z6]),(0,[z0,z1,z2,z3,z5,z290,z6]),(0,[z291,z0,z1,z2,z3,z5,z6]),(0,[z0,z292,z1,z2,z3,z5,z6]),(0,[z293,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z294,z6]),(0,[z0,z2,z160,z3,z242,z5,z6]),(0,[z0,z1,z2,z3,z295,z5,z6]),(0,[z115,z0,z1,z2,z204,z5,z6]),(0,[z0,z1,z2,z296,z3,z5,z6])],[(0,[z0,z1,z297,z2,z3,z5,z6]),(0,[z298,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z299,z6]),(0,[z78,z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z5,z6,z300]),(0,[z0,z1,z31,z2,z3,z65,z6])],[(0,[z1,z20,z2,z3,z5,z24,z6]),(0,[z0,z1,z2,z3,z301,z5,z6]),(0,[z302,z0,z1,z2,z3,z5,z6]),(0,[z196,z0,z1,z3,z116,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z303]),(0,[z0,z1,z304,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z305]),(0,[z0,z1,z306,z2,z3,z5,z6])],[(0,[z307,z0,z1,z2,z3,z5,z6]),(0,[z120,z1,z2,z3,z5,z24,z6]),(0,[z71,z0,z58,z2,z3,z5,z6]),(0,[z308,z0,z1,z2,z3,z5,z6]),(0,[z32,z0,z1,z2,z3,z6,z129])],[(0,[z0,z1,z155,z2,z3,z5,z6]),(0,[z0,z1,z2,z309,z3,z5,z6]),(0,[z0,z1,z2,z3,z310,z5,z6]),(0,[z0,z1,z2,z3,z5,z311,z6])],[(0,[z120,z147,z1,z2,z3,z5,z6]),(0,[z312,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z313,z5,z6]),(0,[z0,z284,z1,z2,z3,z5,z6]),(0,[z0,z314,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z315]),(0,[z0,z1,z316,z2,z3,z5,z6]),(0,[z317,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z318,z3,z5,z6]),(0,[z0,z319,z1,z2,z3,z5,z6])]],
   [[(0,[z320,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z321]),(0,[z191,z0,z28,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z322])],[(0,[z0,z1,z2,z3,z5,z6,z323])],[(0,[z236,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z151,z3,z5,z6,z29]),(0,[z0,z1,z2,z3,z5,z324,z6]),(0,[z0,z1,z2,z3,z5,z325,z6])],[(0,[z0,z20,z2,z3,z5,z114,z6]),(0,[z191,z71,z0,z2,z3,z5,z6]),(0,[z326,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z258]),(0,[z23,z0,z327,z2,z3,z5,z6]),(0,[z328,z0,z1,z2,z3,z5,z6]),(0,[z329,z0,z1,z2,z3,z5,z6]),(0,[z330,z0,z1,z2,z3,z5,z6]),(1,[z0,z80,z2,z3,z5,z6])],[(0,[z0,z1,z331,z2,z3,z5,z6]),(1,[z0,z1,z44,z204,z5,z6])],[(0,[z0,z1,z2,z3,z5,z332,z6]),(0,[z85,z0,z1,z2,z3,z5,z51])],[(0,[z0,z1,z2,z3,z333,z5,z6]),(0,[z0,z334,z1,z2,z3,z5,z6]),(0,[z149,z0,z1,z2,z3,z237,z6]),(0,[z335,z0,z1,z2,z3,z5,z6])],[(0,[z120,z72,z1,z2,z3,z5,z6]),(0,[z336,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z337,z3,z5,z6]),(0,[z0,z1,z338,z2,z3,z5,z6]),(0,[z339,z0,z1,z2,z3,z5,z6]),(0,[z340,z0,z1,z2,z3,z5,z6]),(0,[z341,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z1,z20,z2,z3,z5,z125,z6]),(1,[z342,z1,z2,z3,z237,z6])],[(0,[z343,z0,z1,z2,z3,z5,z6]),(0,[z120,z1,z2,z3,z5,z125,z6]),(0,[z0,z1,z2,z3,z344,z5,z6]),(0,[z345,z0,z1,z2,z3,z5,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z58,z20,z2,z3,z5,z6]),(0,[z346,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z347,z5,z6]),(0,[z342,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z348,z6]),(1,[z0,z1,z31,z3,z104,z6])],[(0,[z0,z1,z2,z3,z5,z349,z6]),(0,[z0,z1,z2,z3,z5,z350,z6])],[(0,[z0,z1,z2,z351,z3,z5,z6]),(0,[z352,z0,z1,z2,z3,z5,z6])],[(0,[z236,z256,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z353,z3,z5,z6]),(0,[z0,z1,z2,z3,z65,z6,z39])],[(0,[z0,z1,z2,z3,z354,z5,z6]),(0,[z0,z1,z2,z3,z5,z355,z6]),(0,[z0,z1,z2,z153,z3,z5,z6])],[(0,[z0,z1,z2,z3,z125,z98,z6]),(0,[z356,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z357,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z133,z3,z5,z6]),(0,[z149,z1,z2,z3,z5,z125,z6]),(0,[z358,z0,z1,z2,z3,z5,z6]),(0,[z359,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z189,z50,z5,z6]),(0,[z85,z0,z1,z2,z3,z5,z100]),(1,[z0,z1,z231,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z360])],[(0,[z72,z0,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z361,z6]),(0,[z0,z1,z2,z362,z3,z5,z6])],[(0,[z0,z58,z1,z2,z3,z43,z6]),(0,[z0,z1,z363,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z364,z5,z6])],[(0,[z0,z20,z2,z3,z242,z5,z6]),(0,[z365,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z366]),(0,[z0,z1,z2,z367,z3,z5,z6]),(0,[z0,z1,z2,z368,z3,z5,z6]),(0,[z369,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z2,z3,z36,z6])],[(0,[z149,z0,z334,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z370,z6]),(0,[z54,z0,z1,z2,z3,z104,z6]),(0,[z97,z0,z1,z117,z3,z5,z6])],[(0,[z23,z1,z2,z3,z5,z24,z6]),(0,[z371,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z50,z3,z372,z6])],[(0,[z0,z1,z373,z2,z3,z5,z6]),(0,[z374,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z375,z6]),(0,[z0,z1,z2,z3,z5,z6,z376]),(1,[z0,z1,z316,z3,z5,z6]),(0,[z0,z1,z377,z2,z3,z5,z6]),(0,[z0,z1,z31,z3,z5,z6,z129]),(0,[z38,z0,z1,z2,z3,z124,z6]),(0,[z38,z378,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z379,z5,z6]),(0,[z0,z110,z1,z2,z242,z5,z6]),(0,[z0,z1,z2,z3,z380,z5,z6]),(1,[z0,z255,z2,z3,z5,z6])],[(0,[z0,z1,z2,z160,z3,z5,z6]),(1,[z0,z110,z2,z160,z5,z6]),(0,[z381,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z2,z145,z3,z5,z6]),(0,[z0,z1,z2,z382,z3,z5,z6]),(0,[z0,z1,z383,z2,z3,z5,z6]),(0,[z0,z1,z384,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z385,z6]),(1,[z386,z0,z1,z3,z5,z6])],[(1,[z120,z71,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z387,z5,z6]),(0,[z0,z1,z388,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z98,z65,z6]),(0,[z0,z1,z2,z50,z3,z5,z6]),(1,[z0,z1,z2,z263,z5,z6])],[(0,[z0,z1,z2,z3,z5,z389,z6])],[(0,[z0,z1,z2,z3,z390,z5,z6]),(0,[z0,z1,z2,z3,z391,z5,z6]),(0,[z392,z0,z1,z2,z3,z5,z6]),(0,[z393,z0,z1,z2,z3,z5,z6]),(0,[z0,z205,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z394,z6]),(0,[z54,z196,z0,z1,z3,z5,z6])],[(0,[z395,z0,z1,z2,z3,z5,z6]),(0,[z396,z0,z1,z2,z3,z5,z6]),(0,[z397,z0,z1,z2,z3,z5,z6]),(0,[z191,z0,z102,z2,z3,z5,z6]),(0,[z398,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z102,z3,z5,z6,z129]),(0,[z0,z1,z2,z3,z399,z5,z6])],[(0,[z0,z1,z2,z3,z5,z400,z6]),(0,[z0,z1,z401,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z124,z65,z6])]],
   [[(0,[z0,z1,z2,z3,z402,z5,z6]),(0,[z0,z1,z403,z2,z3,z5,z6]),(0,[z404,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z372,z6])],[(0,[z405,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z151,z3,z5,z6]),(0,[z0,z1,z2,z3,z257,z5,z6])],[(0,[z0,z1,z2,z406,z3,z5,z6])],[(0,[z0,z110,z20,z2,z3,z5,z6]),(0,[z191,z0,z1,z151,z3,z5,z6]),(0,[z19,z0,z1,z316,z3,z5,z6]),(0,[z0,z1,z31,z3,z116,z5,z6]),(0,[z407,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z366]),(0,[z0,z408,z1,z2,z3,z5,z6]),(0,[z0,z1,z44,z151,z3,z5,z6]),(1,[z0,z1,z409,z3,z5,z6]),(0,[z410,z0,z1,z2,z3,z5,z6]),(0,[z411,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z263,z5,z6])],[(0,[z0,z1,z2,z3,z5,z412,z6]),(0,[z0,z1,z44,z3,z5,z62,z6]),(0,[z413,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z414,z6]),(0,[z54,z0,z1,z102,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z372,z6]),(0,[z0,z1,z2,z3,z5,z6,z39])]],
   [[(0,[z0,z1,z2,z415,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z416,z6]),(0,[z19,z0,z1,z2,z3,z5,z29]),(0,[z0,z1,z2,z204,z3,z5,z6])],[(0,[z0,z1,z2,z3,z417,z5,z6]),(0,[z418,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z419])],[(1,[z72,z20,z2,z3,z5,z6]),(0,[z256,z0,z1,z155,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z24,z100])],[(1,[z0,z1,z52,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z420]),(0,[z0,z28,z2,z151,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z421,z6]),(0,[z97,z0,z1,z2,z189,z5,z6]),(0,[z422,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z423])],[(0,[z0,z1,z2,z3,z5,z424,z6]),(0,[z0,z1,z2,z3,z5,z425,z6]),(0,[z21,z0,z1,z2,z3,z35,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z19,z0,z2,z3,z5,z6,z29]),(0,[z426,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z427,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z283,z6]),(0,[z0,z428,z1,z2,z3,z5,z6])],[(0,[z120,z71,z0,z2,z3,z5,z6]),(1,[z0,z284,z2,z3,z5,z6]),(0,[z21,z1,z2,z3,z148,z5,z6]),(0,[z0,z1,z2,z429,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z430,z6]),(0,[z0,z1,z2,z3,z5,z114,z100])],[(0,[z0,z1,z2,z3,z5,z431,z6]),(0,[z0,z1,z2,z285,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z432]),(0,[z196,z0,z55,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z433]),(0,[z434,z0,z1,z2,z3,z5,z6]),(1,[z0,z334,z2,z3,z5,z6]),(0,[z0,z435,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z5,z65])],[(0,[z0,z436,z1,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z116,z5,z6]),(0,[z437,z0,z1,z2,z3,z5,z6]),(0,[z0,z214,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z342,z1,z20,z2,z3,z5,z6]),(0,[z438,z0,z1,z2,z3,z5,z6]),(0,[z342,z0,z1,z2,z3,z125,z6]),(1,[z32,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z439,z3,z5,z6]),(0,[z0,z440,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z441,z5,z6])],[(0,[z0,z1,z2,z3,z5,z442,z6]),(1,[z443,z1,z2,z3,z5,z6])],[(0,[z444,z0,z1,z2,z3,z5,z6]),(1,[z0,z94,z2,z3,z5,z6]),(0,[z115,z0,z1,z2,z116,z5,z6]),(0,[z0,z1,z2,z3,z445,z5,z6])],[(0,[z0,z1,z446,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z31,z2,z3,z36,z6]),(0,[z0,z1,z2,z447,z3,z5,z6])],[(0,[z71,z0,z2,z3,z5,z43,z6]),(0,[z0,z1,z409,z2,z3,z5,z6]),(0,[z448,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z449])]],
   [[(0,[z1,z2,z3,z5,z125,z6,z13]),(0,[z0,z1,z2,z3,z5,z450,z6]),(0,[z0,z1,z2,z3,z5,z451,z6]),(0,[z0,z1,z44,z2,z204,z5,z6]),(0,[z0,z1,z2,z3,z452,z5,z6]),(0,[z0,z1,z31,z2,z3,z104,z6]),(1,[z0,z1,z2,z189,z124,z6])],[(0,[z72,z1,z20,z2,z3,z5,z6]),(0,[z0,z1,z155,z44,z3,z5,z6]),(0,[z156,z23,z0,z2,z3,z5,z6]),(0,[z453,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z153,z5,z6])],[(0,[z12,z0,z1,z2,z3,z5,z6]),(0,[z0,z454,z1,z2,z3,z5,z6]),(0,[z19,z0,z1,z2,z3,z5,z114]),(0,[z0,z1,z2,z3,z455,z5,z6]),(0,[z0,z1,z456,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z237,z5,z6]),(0,[z0,z1,z2,z3,z162,z5,z39])],[],[(0,[z0,z1,z457,z2,z3,z5,z6]),(0,[z458,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z36,z6,z129])],[(0,[z459,z0,z1,z2,z3,z5,z6])],[(0,[z256,z0,z1,z2,z3,z5,z6]),(0,[z256,z0,z1,z145,z3,z5,z6]),(0,[z0,z1,z460,z2,z3,z5,z6])]],
   [[(0,[z461,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z100,z13]),(0,[z0,z102,z2,z151,z3,z5,z6]),(0,[z109,z0,z1,z285,z3,z5,z6]),(0,[z0,z1,z2,z3,z462,z5,z6]),(0,[z0,z1,z2,z3,z5,z100,z6])],[(0,[z1,z20,z2,z3,z148,z5,z6]),(0,[z463,z0,z1,z2,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z5,z288]),(0,[z0,z1,z204,z3,z116,z5,z6]),(0,[z0,z1,z2,z464,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z465,z6])],[(0,[z120,z1,z2,z3,z148,z5,z6]),(0,[z0,z1,z2,z466,z3,z5,z6]),(0,[z0,z1,z94,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z467,z5,z6]),(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z196,z0,z217,z2,z3,z5,z6]),(0,[z469,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z470,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z98,z6]),(1,[z0,z1,z183,z3,z5,z6])],[(0,[z256,z0,z249,z2,z3,z5,z6]),(0,[z471,z0,z1,z2,z3,z5,z6]),(0,[z386,z0,z1,z2,z3,z5,z6])],[(0,[z472,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z104,z5,z6]),(0,[z473,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z474]),(0,[z0,z1,z2,z3,z475,z5,z6]),(0,[z0,z1,z102,z30,z3,z5,z6])],[(0,[z476,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z24,z6]),(0,[z0,z1,z2,z3,z5,z477,z6]),(0,[z0,z1,z2,z478,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z479]),(1,[z147,z1,z2,z190,z5,z6]),(0,[z0,z1,z2,z3,z5,z480,z6])],[(0,[z481,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z482,z6]),(1,[z0,z1,z2,z3,z483,z6])],[(0,[z484,z0,z1,z2,z3,z5,z6]),(0,[z342,z0,z1,z2,z3,z237,z6]),(0,[z191,z0,z205,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z485]),(0,[z0,z1,z30,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z162,z5,z6])],[(0,[z85,z0,z1,z2,z50,z5,z6])],[(0,[z486,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z148,z5,z6]),(0,[z147,z0,z1,z2,z190,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z288]),(0,[z0,z1,z2,z189,z3,z98,z6]),(0,[z487,z0,z1,z2,z3,z5,z6]),(1,[z214,z1,z2,z3,z5,z6])],[(0,[z147,z1,z20,z2,z3,z5,z6]),(0,[z71,z0,z110,z2,z3,z5,z6]),(0,[z0,z110,z2,z160,z3,z5,z6]),(0,[z0,z58,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z488,z3,z5,z6])],[(0,[z154,z0,z1,z145,z3,z5,z6]),(0,[z489,z0,z1,z2,z3,z5,z6]),(0,[z490,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z491,z5,z6]),(0,[z0,z1,z30,z2,z3,z5,z62])],[(0,[z256,z1,z2,z145,z3,z5,z6]),(0,[z12,z0,z1,z2,z3,z5,z24]),(1,[z0,z327,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z492,z5,z6]),(0,[z493,z0,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z2,z3,z5,z6]),(0,[z494,z0,z1,z2,z3,z5,z6]),(0,[z85,z0,z1,z2,z5,z6,z51])]],
   [[(0,[z495,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z496,z6])],[(0,[z191,z0,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z497,z6]),(0,[z498,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z499,z5,z6]),(0,[z0,z1,z2,z3,z500,z5,z6]),(0,[z386,z0,z1,z3,z5,z6,z39])],[(0,[z0,z1,z44,z145,z3,z5,z6]),(0,[z501,z0,z1,z2,z3,z5,z6])],[(0,[z502,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z503,z2,z3,z5,z6]),(0,[z0,z1,z504,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z505,z6]),(0,[z0,z1,z50,z3,z257,z5,z6])],[(0,[z72,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z125,z6])],[(0,[z0,z1,z506,z2,z3,z5,z6]),(0,[z507,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z508,z6])],[(0,[z509,z0,z1,z2,z3,z5,z6]),(0,[z510,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z511,z2,z3,z5,z6]),(0,[z115,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z512,z5,z6]),(1,[z0,z1,z135,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z513])]],
   [[(0,[z0,z1,z514,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z515,z5,z6])],[(0,[z516,z0,z1,z2,z3,z5,z6]),(0,[z517,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z518]),(0,[z0,z1,z2,z519,z3,z5,z6]),(0,[z19,z0,z28,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z520,z6]),(0,[z0,z1,z3,z5,z62,z6,z129])],[(0,[z0,z1,z2,z3,z242,z5,z6]),(0,[z0,z1,z2,z3,z124,z36,z6]),(0,[z0,z1,z2,z3,z5,z6,z521])],[(0,[z0,z1,z2,z3,z522,z5,z6]),(0,[z0,z1,z2,z523,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z524]),(0,[z0,z1,z2,z3,z124,z43,z6]),(0,[z525,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z166,z2,z3,z5,z6]),(0,[z0,z443,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z104,z98,z6]),(0,[z0,z1,z2,z3,z5,z6,z526]),(0,[z0,z1,z2,z3,z5,z527,z6])],[(0,[z528,z0,z1,z2,z3,z5,z6]),(0,[z19,z71,z0,z2,z3,z5,z6]),(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z530,z2,z3,z5,z6]),(0,[z0,z531,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z532,z5,z6]),(1,[z23,z1,z2,z3,z5,z24]),(1,[z191,z0,z102,z3,z5,z6]),(1,[z0,z1,z166,z3,z5,z6]),(0,[z533,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z534,z6]),(0,[z97,z0,z1,z140,z3,z5,z6])],[(0,[z535,z0,z1,z2,z3,z5,z6]),(0,[z78,z0,z2,z3,z5,z43,z6]),(0,[z0,z536,z1,z2,z3,z5,z6])]],
   [[(1,[z0,z1,z537,z3,z5,z6]),(0,[z538,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z539]),(0,[z0,z1,z44,z204,z3,z5,z6]),(0,[z0,z1,z2,z5,z98,z6,z51])],[],[(0,[z12,z1,z20,z2,z3,z5,z6]),(0,[z120,z342,z1,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z540,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z541,z6])],[(1,[z0,z1,z2,z3,z35,z6]),(1,[z21,z1,z2,z148,z5,z6]),(0,[z0,z1,z2,z542,z3,z5,z6])],[(0,[z0,z58,z1,z2,z3,z229,z6]),(0,[z0,z1,z3,z116,z5,z62,z6]),(1,[z0,z1,z2,z3,z543,z6])],[(0,[z78,z0,z1,z2,z3,z43,z6]),(0,[z0,z1,z544,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z534,z6]),(0,[z0,z1,z2,z3,z5,z545,z6]),(1,[z0,z1,z64,z3,z5,z6])],[(0,[z0,z20,z2,z3,z5,z43,z6]),(0,[z0,z1,z2,z3,z5,z546,z6]),(0,[z0,z110,z1,z2,z3,z5,z6]),(0,[z14,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z116,z5,z36,z6]),(0,[z0,z1,z547,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z548]),(0,[z78,z0,z58,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z549,z6])]],
   [[(0,[z1,z155,z2,z145,z3,z5,z6]),(0,[z147,z0,z1,z2,z3,z5,z6]),(0,[z38,z0,z1,z31,z2,z3,z6]),(0,[z0,z550,z1,z2,z3,z5,z6]),(0,[z0,z1,z255,z2,z3,z5,z6])],[(0,[z149,z342,z1,z2,z3,z5,z6]),(0,[z551,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z552,z2,z3,z5,z6]),(0,[z0,z1,z231,z2,z3,z5,z6])],[(1,[z0,z205,z151,z3,z5,z6]),(0,[z0,z1,z2,z3,z553,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z554])],[(0,[z0,z1,z155,z3,z116,z5,z6]),(1,[z0,z1,z2,z210,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z555]),(0,[z0,z1,z2,z3,z283,z5,z6]),(0,[z191,z0,z1,z102,z3,z5,z6]),(0,[z19,z0,z1,z537,z3,z5,z6]),(0,[z556,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z557])],[(0,[z0,z1,z2,z3,z558,z5,z6]),(0,[z0,z1,z2,z3,z559,z5,z6]),(0,[z0,z1,z102,z3,z116,z5,z6]),(0,[z109,z0,z1,z409,z3,z5,z6])],[(0,[z560,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z561,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z562]),(0,[z0,z1,z2,z3,z5,z563,z6])],[(0,[z564,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z565,z3,z5,z6]),(0,[z0,z1,z2,z50,z5,z100,z6])]],
   [[(0,[z0,z1,z566,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z29]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z567])],[(0,[z0,z1,z568,z2,z3,z5,z6]),(0,[z342,z23,z1,z2,z3,z5,z6]),(0,[z569,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z570,z5,z6]),(0,[z0,z28,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z571])],[(0,[z572,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z52,z2,z3,z5,z6]),(0,[z0,z1,z2,z573,z3,z5,z6]),(0,[z0,z1,z2,z3,z574,z5,z6]),(0,[z0,z1,z2,z575,z3,z5,z6]),(0,[z0,z1,z31,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z6,z105]),(0,[z0,z1,z2,z3,z6,z105,z129]),(0,[z0,z1,z2,z50,z5,z98,z6]),(0,[z0,z1,z64,z50,z3,z5,z6])],[(0,[z74,z0,z1,z2,z3,z5,z6]),(0,[z28,z443,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z180,z6]),(0,[z576,z0,z1,z2,z3,z5,z6])],[(0,[z577,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z578,z6])],[(0,[z579,z0,z1,z2,z3,z5,z6]),(0,[z71,z0,z2,z151,z3,z5,z6]),(0,[z0,z1,z2,z3,z210,z5,z6]),(0,[z196,z0,z1,z3,z104,z5,z6]),(0,[z378,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z580]),(0,[z0,z1,z2,z3,z5,z581,z6]),(0,[z582,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z583,z6]),(0,[z0,z1,z2,z584,z3,z5,z6]),(0,[z585,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z586,z2,z3,z5,z6]),(0,[z0,z587,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z124,z5,z98,z6])]],
   [[(0,[z588,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z589,z6]),(0,[z590,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z591,z2,z3,z5,z6]),(0,[z0,z1,z592,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z593,z6])],[(0,[z342,z1,z2,z3,z5,z6,z13]),(0,[z0,z594,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z13])],[(0,[z0,z1,z2,z595,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z100,z29])],[(0,[z120,z71,z1,z2,z3,z5,z6]),(1,[z143,z1,z2,z3,z5,z6]),(0,[z596,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z229,z5,z6]),(0,[z0,z1,z2,z116,z5,z98,z6]),(0,[z0,z1,z3,z104,z5,z36,z6]),(0,[z0,z1,z2,z183,z3,z5,z6])],[(0,[z120,z0,z20,z2,z3,z5,z6]),(0,[z0,z597,z1,z2,z3,z5,z6]),(0,[z154,z0,z1,z155,z3,z5,z6]),(0,[z0,z1,z598,z2,z3,z5,z6]),(0,[z0,z1,z2,z599,z3,z5,z6]),(0,[z600,z0,z1,z2,z3,z5,z6])],[(0,[z601,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z258]),(0,[z12,z0,z1,z2,z3,z5,z13]),(0,[z602,z0,z1,z2,z3,z5,z6]),(0,[z97,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z603,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z604])],[(0,[z605,z0,z1,z2,z3,z5,z6]),(0,[z342,z1,z2,z3,z237,z5,z6]),(0,[z0,z1,z2,z606,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z607]),(0,[z608,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z237,z5,z125,z6]),(0,[z609,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z610,z6]),(0,[z0,z1,z2,z3,z5,z6,z611]),(0,[z0,z1,z2,z204,z5,z98,z6])]],
   [[(0,[z0,z612,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z613,z3,z5,z6]),(0,[z614,z0,z1,z2,z3,z5,z6]),(0,[z0,z615,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z616,z6])],[(0,[z0,z1,z2,z3,z617,z5,z6])],[(0,[z0,z1,z618,z2,z3,z5,z6]),(0,[z619,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z543,z5,z6])],[(0,[z620,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z621,z6]),(0,[z622,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z623,z3,z5,z6]),(1,[z0,z1,z2,z177,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z624]),(0,[z625,z0,z1,z2,z3,z5,z6]),(0,[z626,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z627,z5,z6])],[(1,[z149,z1,z2,z3,z125,z6]),(0,[z196,z0,z1,z44,z3,z5,z6])],[(0,[z0,z1,z2,z628,z3,z5,z6]),(0,[z629,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z630]),(0,[z0,z1,z2,z3,z631,z5,z6]),(1,[z0,z1,z2,z3,z5,z187])],[(0,[z0,z1,z2,z3,z5,z6,z632]),(0,[z0,z1,z2,z633,z3,z5,z6]),(0,[z0,z1,z2,z3,z634,z5,z6]),(0,[z635,z0,z1,z2,z3,z5,z6])],[(0,[z636,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z133,z3,z5,z6]),(1,[z378,z1,z2,z3,z5,z6])],[(0,[z0,z58,z2,z3,z5,z6,z29]),(0,[z0,z1,z2,z3,z5,z6,z637]),(0,[z638,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z639,z6]),(1,[z54,z0,z1,z3,z36,z6]),(0,[z640,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z641,z3,z5,z6]),(0,[z0,z1,z2,z3,z642,z5,z6])],[(0,[z0,z1,z2,z190,z3,z5,z6]),(0,[z0,z1,z2,z3,z148,z5,z6]),(0,[z0,z643,z1,z2,z3,z5,z6]),(0,[z109,z0,z1,z2,z160,z5,z6]),(0,[z196,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z644,z6]),(0,[z645,z0,z1,z2,z3,z5,z6])],[(0,[z1,z2,z190,z3,z148,z5,z6]),(1,[z0,z1,z2,z3,z81,z6]),(0,[z0,z1,z2,z3,z5,z114,z6]),(0,[z0,z1,z2,z3,z5,z29,z51]),(0,[z0,z1,z2,z3,z5,z646,z6])],[(0,[z647,z0,z1,z2,z3,z5,z6]),(0,[z648,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z151,z3,z104,z5,z6]),(0,[z0,z1,z2,z135,z3,z5,z6]),(0,[z115,z0,z1,z2,z3,z534,z6]),(0,[z0,z1,z2,z3,z649,z5,z6]),(0,[z0,z1,z2,z3,z162,z65,z6]),(0,[z0,z1,z2,z3,z5,z6,z650])]],
   [[(0,[z651,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z652,z6]),(0,[z0,z1,z30,z2,z3,z5,z129]),(0,[z653,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z140,z2,z3,z5,z6])],[(0,[z154,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z654]),(0,[z196,z0,z1,z2,z3,z5,z62])],[(0,[z655,z0,z1,z2,z3,z5,z6]),(0,[z0,z656,z1,z2,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z483,z6]),(0,[z0,z1,z2,z3,z229,z98,z6]),(0,[z115,z0,z1,z44,z3,z5,z6]),(0,[z0,z657,z1,z2,z3,z5,z6])],[(0,[z658,z0,z1,z2,z3,z5,z6]),(0,[z659,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z660,z6]),(0,[z0,z1,z2,z3,z5,z483,z6]),(0,[z0,z1,z2,z3,z5,z187,z6])],[(1,[z154,z1,z155,z3,z5,z6]),(0,[z191,z0,z1,z2,z3,z5,z6]),(0,[z109,z0,z1,z2,z3,z81,z6]),(0,[z0,z661,z1,z2,z3,z5,z6]),(0,[z97,z0,z1,z2,z3,z98,z6])],[(0,[z0,z1,z2,z3,z5,z662,z6]),(0,[z0,z1,z2,z3,z237,z98,z6]),(0,[z0,z1,z2,z3,z663,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z664]),(0,[z0,z1,z44,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z665]),(0,[z0,z1,z2,z3,z666,z5,z6])],[(0,[z23,z0,z1,z2,z3,z5,z6]),(0,[z0,z58,z2,z3,z229,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z667]),(0,[z109,z0,z2,z3,z242,z5,z6]),(0,[z0,z668,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z669,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z537,z3,z5,z6]),(0,[z0,z1,z2,z3,z36,z98,z6])],[(0,[z21,z0,z1,z2,z3,z5,z366]),(0,[z0,z670,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z671]),(0,[z109,z0,z1,z2,z242,z5,z6]),(0,[z0,z1,z30,z3,z5,z36,z6]),(0,[z0,z1,z672,z2,z3,z5,z6]),(0,[z0,z1,z2,z189,z3,z124,z6])],[(1,[z615,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z673,z6])],[(0,[z78,z615,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z100,z6,z51])],[(0,[z0,z1,z2,z3,z5,z674,z6]),(0,[z0,z1,z675,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z676,z5,z6]),(0,[z0,z1,z31,z3,z104,z5,z6]),(0,[z0,z1,z2,z50,z3,z543,z6])],[(0,[z0,z1,z2,z3,z677,z5,z6]),(0,[z678,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z24,z6,z13]),(0,[z679,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z680,z3,z5,z6])],[(0,[z0,z1,z2,z3,z681,z5,z6]),(0,[z0,z1,z327,z2,z3,z5,z6]),(0,[z0,z1,z682,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z43,z98,z6]),(0,[z683,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z71,z1,z20,z2,z3,z5,z6]),(0,[z0,z684,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z685,z6]),(0,[z686,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z50,z5,z100])],[(0,[z12,z23,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z687,z6]),(0,[z688,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z689,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z690,z5,z6])],[(0,[z149,z0,z119,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z691]),(0,[z692,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z693,z6])],[(0,[z0,z143,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z694,z5,z6]),(0,[z38,z0,z1,z2,z3,z5,z39])],[(0,[z0,z20,z2,z151,z3,z5,z6]),(0,[z695,z0,z1,z2,z3,z5,z6]),(0,[z0,z696,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z697]),(0,[z115,z0,z1,z2,z3,z180,z6]),(0,[z0,z698,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z699,z3,z5,z6])],[(0,[z0,z1,z2,z700,z3,z5,z6]),(0,[z701,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z702]),(0,[z0,z1,z2,z3,z5,z6,z703])],[(0,[z0,z1,z704,z2,z3,z5,z6]),(0,[z0,z705,z1,z2,z3,z5,z6]),(0,[z706,z0,z1,z2,z3,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z5,z6]),(0,[z0,z1,z2,z3,z708,z6]),(1,[z0,z1,z210,z36,z6]),(0,[z0,z1,z31,z3,z649,z6])],[(0,[z0,z1,z2,z3,z709,z6]),(0,[z0,z1,z2,z710,z5,z6]),(0,[z0,z1,z2,z3,z711,z6])],[(0,[z149,z1,z2,z3,z712,z6])],[(0,[z156,z0,z2,z3,z5,z6]),(0,[z0,z55,z2,z3,z5,z6]),(0,[z0,z1,z2,z177,z5,z6])],[(0,[z21,z1,z133,z148,z5,z6]),(0,[z0,z1,z2,z3,z283,z258]),(0,[z713,z1,z2,z3,z5,z6])],[(0,[z0,z284,z2,z3,z5,z258]),(0,[z0,z1,z714,z3,z5,z6]),(0,[z0,z1,z715,z3,z5,z6])],[],[(0,[z0,z1,z3,z716,z5,z6]),(0,[z0,z1,z2,z3,z5,z717]),(0,[z0,z1,z2,z718,z5,z6]),(0,[z0,z1,z3,z5,z6,z719]),(0,[z23,z327,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z187]),(0,[z0,z110,z2,z720,z5,z6]),(0,[z0,z1,z721,z3,z5,z6])]],
   [[(0,[z0,z1,z722,z3,z5,z6]),(0,[z0,z1,z2,z723,z5,z6]),(0,[z0,z1,z724,z3,z5,z6])],[(0,[z0,z1,z725,z3,z5,z6]),(0,[z0,z1,z2,z3,z726,z6]),(0,[z32,z0,z1,z2,z727,z6])],[(0,[z0,z1,z2,z3,z6,z728]),(0,[z0,z1,z729,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z730]),(0,[z0,z1,z31,z3,z731,z6]),(0,[z0,z1,z3,z5,z6,z732]),(0,[z0,z1,z733,z3,z5,z6])],[(0,[z147,z1,z2,z73,z5,z6]),(0,[z0,z1,z2,z3,z734,z6]),(0,[z1,z2,z3,z735,z5,z6])],[(0,[z0,z736,z2,z3,z5,z6]),(0,[z0,z1,z409,z3,z81,z6]),(1,[z0,z2,z720,z5,z6]),(0,[z0,z737,z2,z3,z5,z6])],[(0,[z738,z0,z2,z3,z5,z6]),(0,[z0,z1,z739,z3,z5,z6]),(0,[z0,z1,z2,z3,z740,z6]),(1,[z1,z2,z735,z5,z6]),(0,[z0,z1,z2,z3,z5,z741])],[(0,[z0,z1,z742,z3,z5,z6]),(0,[z0,z1,z2,z743,z5,z6]),(1,[z0,z1,z116,z534,z6]),(0,[z556,z0,z1,z2,z98,z6])],[(0,[z143,z1,z285,z3,z5,z6]),(0,[z443,z2,z3,z5,z114,z6]),(0,[z0,z744,z2,z3,z5,z6]),(0,[z0,z1,z2,z543,z98,z6])]],
   [[(0,[z149,z334,z2,z3,z125,z6]),(0,[z0,z745,z1,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z288]),(0,[z0,z746,z2,z3,z5,z6])],[(0,[z0,z1,z133,z3,z283,z6]),(0,[z0,z1,z747,z3,z5,z6]),(0,[z748,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z749,z5,z6])],[(0,[z0,z1,z3,z5,z750,z6]),(0,[z0,z1,z751,z3,z5,z6]),(0,[z0,z284,z133,z3,z5,z6]),(0,[z752,z0,z2,z3,z5,z6])],[(0,[z120,z314,z2,z3,z5,z6]),(0,[z154,z1,z155,z3,z5,z6]),(0,[z753,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z754])],[(0,[z20,z2,z3,z5,z332,z6]),(0,[z0,z755,z2,z3,z5,z6]),(0,[z0,z211,z151,z3,z5,z6])],[(0,[z0,z756,z2,z3,z5,z6])],[(0,[z0,z217,z2,z3,z5,z6]),(0,[z757,z1,z2,z3,z5,z6]),(0,[z758,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z172,z5,z62]),(0,[z196,z0,z1,z3,z5,z539])],[(0,[z0,z759,z2,z3,z5,z6]),(0,[z54,z0,z1,z3,z311,z6])]],
   [[(0,[z0,z1,z760,z3,z5,z6]),(0,[z0,z537,z3,z5,z6,z29])],[(0,[z0,z1,z761,z3,z5,z6]),(0,[z0,z94,z133,z3,z5,z6]),(0,[z12,z1,z2,z3,z5,z13]),(0,[z0,z2,z160,z720,z5,z6]),(0,[z0,z28,z2,z3,z5,z114])],[(0,[z615,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z762]),(0,[z0,z1,z763,z3,z5,z6]),(0,[z0,z1,z3,z764,z5,z6]),(0,[z0,z765,z2,z3,z5,z6]),(0,[z0,z1,z2,z50,z372,z100])],[(0,[z330,z0,z102,z3,z5,z6]),(0,[z38,z0,z1,z2,z153,z39])],[(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z1,z285,z3,z5,z187])],[(0,[z0,z1,z2,z3,z767,z6]),(0,[z0,z1,z2,z153,z124,z6]),(0,[z378,z1,z2,z153,z5,z6]),(0,[z0,z1,z2,z3,z6,z754])],[(0,[z256,z1,z725,z3,z5,z6]),(0,[z0,z1,z133,z3,z5,z258]),(0,[z768,z1,z2,z3,z5,z6])],[(0,[z159,z20,z2,z3,z5,z6]),(0,[z12,z1,z2,z3,z5,z607]),(0,[z0,z1,z769,z3,z5,z6]),(0,[z0,z531,z151,z3,z5,z6]),(0,[z0,z1,z44,z770,z5,z6]),(0,[z0,z1,z2,z50,z5,z100])]],
   [[(0,[z21,z1,z2,z148,z35,z6]),(0,[z19,z0,z316,z3,z5,z29]),(0,[z0,z771,z2,z3,z5,z6]),(0,[z196,z0,z217,z3,z5,z129]),(0,[z0,z1,z2,z3,z772,z6]),(0,[z0,z2,z3,z5,z6,z773])],[(0,[z0,z1,z2,z3,z774,z6]),(0,[z78,z615,z2,z3,z43,z6])],[(0,[z0,z1,z2,z3,z5,z775]),(0,[z776,z0,z2,z3,z5,z6]),(0,[z0,z1,z44,z700,z5,z6])],[(0,[z0,z249,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z777,z6]),(0,[z0,z1,z64,z3,z543,z6])],[(0,[z0,z1,z778,z3,z5,z6]),(0,[z236,z256,z145,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z779]),(0,[z780,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z257,z5,z6])],[(0,[z0,z1,z781,z3,z5,z6]),(0,[z0,z1,z2,z189,z452,z6]),(0,[z0,z1,z782,z3,z5,z6])],[(0,[z0,z1,z183,z3,z124,z6]),(0,[z378,z1,z183,z3,z5,z6])]],
   [[(0,[z14,z1,z2,z3,z5,z6]),(0,[z0,z1,z783,z3,z5,z6]),(0,[z784,z1,z2,z3,z5,z6])],[(0,[z342,z1,z2,z3,z122,z6]),(0,[z0,z1,z2,z735,z5,z6]),(0,[z0,z1,z2,z3,z785,z6]),(0,[z786,z1,z2,z3,z5,z6]),(0,[z345,z0,z2,z3,z5,z29]),(0,[z0,z1,z787,z3,z5,z6])],[(0,[z378,z80,z2,z3,z5,z6])],[(0,[z629,z1,z2,z3,z5,z24]),(0,[z109,z0,z2,z242,z5,z6]),(0,[z0,z1,z2,z3,z788,z6])],[(0,[z789,z0,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z790,z6])],[(0,[z48,z20,z2,z3,z5,z6]),(0,[z0,z1,z791,z3,z5,z6]),(0,[z38,z0,z255,z2,z3,z39])],[(0,[z57,z1,z2,z3,z5,z6]),(0,[z792,z0,z1,z2,z3,z5]),(0,[z12,z1,z2,z3,z5,z793]),(0,[z97,z0,z1,z117,z98,z6])],[(0,[z612,z1,z2,z3,z5,z24]),(0,[z308,z0,z102,z3,z5,z6]),(0,[z0,z2,z3,z720,z5,z6]),(0,[z443,z2,z3,z5,z43,z6]),(0,[z0,z1,z2,z210,z65,z6])]],
   [[(1,[z1,z725,z3,z5,z6]),(0,[z794,z1,z2,z3,z5,z6]),(0,[z795,z1,z2,z3,z5,z6]),(0,[z214,z1,z2,z3,z124,z6])],[(0,[z0,z1,z2,z3,z796,z6]),(0,[z0,z2,z797,z3,z5,z6])],[(0,[z23,z1,z2,z3,z5,z294]),(0,[z525,z0,z2,z3,z5,z29]),(0,[z638,z0,z1,z2,z5,z51]),(0,[z0,z1,z3,z5,z6,z798]),(0,[z115,z0,z1,z116,z534,z6])],[(0,[z0,z799,z2,z3,z5,z6]),(0,[z0,z800,z2,z3,z5,z6]),(0,[z801,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z382,z124,z6])],[(0,[z74,z1,z2,z3,z5,z6]),(0,[z0,z802,z2,z3,z5,z6]),(0,[z0,z803,z2,z3,z5,z6]),(0,[z0,z804,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z805,z6])],[(0,[z38,z0,z1,z3,z70,z39])],[(0,[z679,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z806]),(0,[z0,z1,z3,z807,z5,z6]),(0,[z443,z58,z2,z3,z5,z6]),(0,[z19,z0,z2,z3,z5,z808]),(0,[z0,z1,z50,z257,z5,z100])]],
   [[(0,[z579,z1,z2,z148,z5,z6]),(0,[z256,z249,z145,z3,z5,z6]),(0,[z0,z2,z3,z5,z809,z6]),(0,[z810,z1,z2,z3,z5,z6]),(0,[z811,z0,z1,z3,z5,z6]),(0,[z556,z0,z1,z3,z36,z6]),(0,[z0,z1,z257,z5,z98,z6])],[(0,[z191,z0,z373,z3,z5,z6])],[(0,[z320,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z812]),(0,[z0,z1,z2,z3,z35,z258]),(0,[z813,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z814,z5,z6]),(0,[z97,z0,z1,z2,z98,z6])],[(0,[z20,z2,z3,z5,z424,z6]),(0,[z0,z815,z1,z3,z5,z6]),(0,[z1,z2,z735,z148,z5,z6]),(0,[z816,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z817]),(0,[z0,z28,z2,z3,z5,z324])],[(0,[z143,z1,z409,z3,z5,z6]),(0,[z818,z0,z2,z3,z5,z6])],[(0,[z1,z2,z3,z237,z712,z6]),(0,[z0,z1,z819,z3,z5,z6]),(0,[z0,z1,z3,z210,z36,z6]),(1,[z0,z1,z3,z731,z6]),(0,[z38,z0,z80,z2,z3,z39])],[(0,[z0,z820,z2,z3,z5,z6]),(0,[z0,z1,z2,z821,z5,z6]),(0,[z0,z1,z3,z5,z822,z6])],[(0,[z0,z1,z2,z296,z98,z6])]],
   [[(0,[z0,z1,z3,z5,z823,z6]),(0,[z0,z1,z2,z3,z5,z824]),(0,[z109,z0,z285,z242,z5,z6]),(0,[z0,z1,z44,z204,z5,z6])],[(0,[z109,z0,z2,z242,z5,z288]),(0,[z0,z217,z3,z104,z5,z6]),(1,[z0,z1,z117,z98,z6])],[(0,[z0,z2,z3,z5,z6,z825]),(0,[z826,z1,z2,z3,z5,z6]),(0,[z0,z28,z135,z3,z5,z6]),(0,[z0,z1,z140,z3,z5,z6])],[(0,[z12,z327,z2,z3,z5,z6]),(0,[z0,z1,z2,z827,z5,z6]),(0,[z57,z1,z285,z3,z5,z6]),(0,[z0,z2,z3,z5,z114,z808]),(0,[z0,z1,z770,z116,z5,z6]),(0,[z291,z0,z1,z3,z36,z6])],[(0,[z0,z1,z2,z828,z5,z6]),(0,[z342,z1,z2,z3,z237,z6]),(0,[z57,z1,z2,z3,z5,z288]),(0,[z0,z1,z829,z3,z5,z6])],[(0,[z71,z0,z135,z3,z5,z6]),(0,[z0,z1,z540,z116,z5,z6])],[],[(0,[z0,z1,z830,z3,z5,z6]),(0,[z0,z1,z133,z3,z35,z6]),(0,[z0,z831,z2,z3,z5,z6]),(0,[z0,z832,z2,z3,z5,z6])]],
   [[(0,[z833,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z834])],[(0,[z0,z1,z3,z835,z5,z6]),(0,[z0,z1,z409,z3,z5,z187]),(0,[z0,z1,z2,z3,z6,z836]),(0,[z706,z0,z1,z3,z5,z129]),(0,[z32,z0,z1,z183,z3,z6])],[(0,[z0,z1,z44,z406,z5,z6]),(0,[z0,z1,z837,z3,z5,z6]),(0,[z0,z1,z2,z838,z5,z6]),(0,[z0,z839,z2,z3,z5,z6]),(0,[z0,z1,z2,z840,z5,z6])],[(0,[z0,z841,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z842,z6]),(0,[z0,z28,z537,z3,z5,z6]),(0,[z0,z1,z3,z116,z534,z6]),(0,[z38,z214,z1,z2,z3,z39])],[(0,[z120,z356,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z843,z6]),(0,[z19,z443,z2,z3,z5,z6]),(0,[z0,z1,z31,z210,z5,z6]),(0,[z0,z1,z2,z50,z5,z385])],[(0,[z0,z844,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z845]),(0,[z0,z1,z846,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z847]),(0,[z0,z1,z3,z5,z6,z848])],[(0,[z120,z182,z2,z3,z5,z6]),(0,[z71,z0,z537,z3,z5,z6]),(0,[z0,z849,z2,z3,z5,z6]),(0,[z0,z850,z2,z3,z5,z6]),(0,[z32,z0,z1,z2,z840,z6]),(0,[z0,z1,z2,z189,z543,z6])],[(0,[z0,z1,z851,z3,z5,z6]),(0,[z0,z852,z2,z3,z5,z6]),(0,[z1,z725,z145,z3,z5,z6]),(0,[z1,z725,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z366])]],
   [[(0,[z54,z0,z1,z210,z36,z6])],[(0,[z0,z1,z2,z3,z853,z6]),(0,[z854,z1,z2,z3,z5,z6])],[(0,[z0,z217,z44,z3,z5,z6])],[(0,[z0,z28,z2,z3,z5,z808]),(0,[z0,z1,z117,z3,z98,z6]),(0,[z855,z0,z1,z3,z5,z6])],[(0,[z856,z0,z1,z2,z3,z6]),(0,[z0,z857,z2,z3,z5,z6])],[(0,[z0,z1,z52,z3,z5,z366]),(0,[z0,z858,z2,z3,z5,z6]),(0,[z0,z110,z2,z160,z5,z6])],[(0,[z0,z2,z3,z5,z859,z6]),(0,[z0,z1,z860,z3,z5,z6])],[(0,[z120,z861,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z862]),(0,[z863,z1,z2,z3,z5,z6]),(0,[z78,z0,z2,z3,z43,z6]),(0,[z0,z1,z3,z5,z6,z864]),(0,[z0,z1,z2,z3,z865,z6]),(0,[z866,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z867,z6]),(0,[z0,z868,z2,z3,z5,z6]),(0,[z0,z1,z869,z3,z5,z6])],[(0,[z0,z1,z2,z3,z870,z6])],[(0,[z0,z1,z3,z5,z6,z871])],[(0,[z0,z1,z872,z3,z5,z6]),(0,[z149,z119,z2,z3,z125,z6]),(0,[z625,z1,z2,z3,z125,z6]),(0,[z0,z1,z2,z3,z873,z6]),(0,[z615,z58,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z372,z6])],[(0,[z191,z443,z2,z3,z5,z6]),(0,[z874,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z50,z543,z100])],[(0,[z0,z875,z2,z3,z5,z6]),(0,[z876,z1,z2,z3,z5,z6])]],
   [[(0,[z635,z1,z145,z3,z5,z6]),(0,[z0,z1,z2,z3,z877,z6]),(0,[z878,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z772,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z879,z3,z5,z6]),(0,[z143,z1,z2,z3,z483,z6])],[(0,[z236,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z880]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z0,z1,z882,z3,z5,z6]),(0,[z28,z443,z2,z3,z5,z114]),(0,[z0,z1,z3,z731,z36,z6]),(0,[z0,z1,z3,z5,z62,z703])],[(0,[z0,z1,z2,z3,z5,z883]),(0,[z0,z1,z30,z3,z5,z203]),(0,[z143,z1,z2,z3,z81,z6]),(0,[z0,z1,z884,z3,z5,z6]),(0,[z0,z1,z3,z257,z372,z6])],[(0,[z0,z1,z885,z3,z5,z6]),(0,[z0,z1,z3,z886,z5,z6])],[(0,[z0,z1,z887,z3,z5,z6]),(0,[z0,z1,z888,z3,z5,z6])],[(0,[z72,z20,z2,z3,z5,z6]),(0,[z143,z2,z3,z242,z5,z6]),(0,[z889,z1,z2,z3,z5,z6]),(0,[z0,z890,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z891,z6])],[(0,[z0,z1,z52,z3,z5,z6]),(0,[z405,z0,z1,z2,z5,z51])]],
   [[(0,[z0,z1,z3,z5,z892,z6]),(0,[z147,z1,z2,z735,z5,z6]),(0,[z893,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z894,z6]),(0,[z0,z1,z895,z3,z5,z6]),(0,[z19,z0,z537,z3,z5,z29]),(0,[z54,z0,z1,z177,z36,z6])],[(0,[z0,z1,z2,z3,z5,z896]),(0,[z0,z1,z2,z3,z897,z6]),(0,[z576,z0,z1,z116,z5,z6]),(0,[z898,z1,z2,z3,z5,z6])],[(0,[z0,z1,z899,z3,z5,z6]),(0,[z0,z1,z2,z210,z36,z6]),(0,[z900,z1,z2,z3,z5,z6]),(0,[z0,z901,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z902])],[(0,[z342,z1,z2,z3,z712,z6]),(0,[z437,z1,z2,z3,z237,z6])],[(0,[z0,z1,z2,z3,z903,z6]),(0,[z443,z2,z151,z3,z5,z6]),(0,[z904,z0,z1,z2,z3,z5]),(0,[z905,z0,z1,z2,z3,z6]),(0,[z109,z0,z409,z242,z5,z6]),(0,[z0,z1,z2,z210,z104,z6]),(0,[z0,z906,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z483,z187]),(0,[z78,z0,z2,z3,z907,z6]),(0,[z0,z1,z2,z3,z908,z6]),(0,[z32,z0,z1,z2,z3,z6]),(0,[z0,z1,z189,z257,z5,z6])],[]],
   [[(0,[z0,z1,z2,z909,z5,z6]),(0,[z910,z0,z2,z3,z5,z6]),(0,[z57,z1,z409,z3,z5,z6]),(0,[z0,z1,z2,z3,z81,z187]),(0,[z0,z1,z911,z3,z5,z6]),(0,[z0,z1,z912,z3,z5,z6])],[(0,[z0,z94,z2,z3,z5,z6]),(0,[z342,z327,z2,z3,z5,z6]),(0,[z0,z1,z210,z5,z62,z6])],[(0,[z0,z913,z2,z3,z5,z6]),(0,[z0,z1,z914,z3,z5,z6])],[(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z1,z2,z3,z5,z916]),(0,[z0,z1,z2,z3,z917,z6]),(0,[z358,z0,z1,z116,z5,z6]),(0,[z413,z0,z1,z2,z98,z6]),(0,[z0,z1,z210,z5,z36,z6])],[(0,[z0,z668,z151,z3,z5,z6]),(0,[z0,z1,z2,z918,z5,z6]),(0,[z0,z1,z2,z189,z124,z6])],[(0,[z0,z1,z2,z919,z5,z6]),(0,[z0,z1,z2,z3,z920,z6]),(0,[z0,z1,z2,z720,z5,z6]),(0,[z0,z1,z921,z3,z5,z6]),(0,[z0,z1,z2,z606,z5,z100]),(0,[z317,z0,z1,z116,z5,z6]),(0,[z196,z0,z1,z210,z5,z6]),(0,[z54,z0,z1,z183,z3,z6]),(0,[z196,z0,z1,z3,z5,z129])],[(0,[z307,z20,z2,z3,z5,z6]),(0,[z256,z1,z145,z3,z5,z6]),(0,[z0,z1,z285,z3,z5,z6]),(0,[z0,z1,z409,z3,z5,z288])],[(0,[z109,z57,z2,z242,z5,z6]),(0,[z0,z1,z2,z3,z5,z288]),(0,[z0,z2,z3,z5,z808,z29]),(0,[z0,z1,z3,z5,z731,z6])]],
   [[(0,[z0,z922,z2,z3,z5,z6]),(0,[z352,z0,z151,z3,z5,z6]),(1,[z0,z1,z770,z5,z6]),(0,[z0,z217,z3,z5,z6,z129]),(0,[z0,z1,z30,z3,z5,z732])],[(0,[z0,z1,z2,z3,z5,z923]),(0,[z0,z1,z151,z210,z5,z6]),(0,[z0,z1,z2,z116,z534,z6]),(0,[z0,z1,z3,z104,z6,z526]),(0,[z196,z0,z1,z3,z5,z732]),(0,[z38,z378,z1,z2,z3,z39])],[(0,[z0,z1,z2,z3,z924,z6]),(0,[z0,z1,z925,z3,z5,z6]),(0,[z926,z1,z2,z3,z5,z6])],[(0,[z486,z1,z2,z3,z125,z6]),(0,[z0,z1,z927,z3,z5,z6])],[(0,[z0,z1,z2,z928,z5,z6])],[(0,[z0,z1,z2,z929,z5,z6]),(0,[z0,z930,z2,z3,z5,z6]),(0,[z0,z931,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z932,z6]),(0,[z933,z1,z2,z3,z5,z6])],[(0,[z0,z934,z2,z3,z5,z6]),(0,[z935,z1,z2,z3,z5,z6])],[(0,[z71,z861,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z62,z732]),(0,[z936,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z204,z534,z6])],[(0,[z0,z1,z937,z3,z5,z6]),(0,[z0,z938,z2,z3,z5,z6])],[(0,[z939,z1,z2,z3,z5,z6]),(0,[z0,z80,z2,z3,z5,z6])],[(0,[z489,z1,z2,z3,z5,z13]),(1,[z0,z1,z3,z5,z732])],[],[(0,[z0,z1,z940,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z79])],[(0,[z0,z612,z2,z3,z5,z114]),(0,[z1,z2,z3,z712,z125,z6]),(0,[z0,z1,z2,z3,z941,z6])],[(0,[z0,z1,z2,z3,z942,z6]),(0,[z943,z1,z2,z3,z5,z6]),(0,[z0,z1,z944,z3,z5,z6])]],
   [[(0,[z861,z0,z2,z3,z5,z6]),(0,[z486,z0,z2,z3,z43,z6]),(0,[z214,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z907,z43,z6]),(0,[z0,z1,z2,z727,z5,z6])],[(0,[z0,z1,z2,z3,z945,z6]),(0,[z0,z1,z31,z3,z104,z6])],[(0,[z199,z71,z2,z3,z5,z6]),(0,[z115,z0,z1,z116,z180,z6])],[(0,[z0,z1,z2,z3,z946,z6]),(0,[z0,z947,z2,z3,z5,z6])],[(0,[z262,z1,z2,z3,z5,z13]),(0,[z143,z110,z2,z3,z5,z6]),(0,[z0,z1,z285,z3,z5,z288]),(0,[z948,z1,z2,z3,z5,z6])],[(0,[z21,z1,z2,z148,z5,z366]),(0,[z0,z28,z2,z3,z5,z581]),(0,[z109,z0,z2,z720,z5,z6]),(0,[z0,z1,z949,z3,z5,z6]),(0,[z0,z950,z2,z3,z5,z6]),(0,[z54,z0,z1,z3,z731,z6])],[(0,[z0,z1,z2,z3,z951,z6]),(0,[z0,z952,z2,z3,z5,z6])],[(0,[z0,z1,z231,z3,z5,z6]),(0,[z0,z1,z953,z3,z5,z6])]],
   [[],[],[(0,[z861,z20,z2,z3,z5,z6]),(0,[z0,z954,z2,z3,z5,z6]),(0,[z109,z0,z2,z242,z483,z6]),(0,[z0,z1,z955,z3,z5,z6]),(0,[z0,z1,z956,z3,z5,z6])],[(0,[z0,z20,z135,z3,z5,z6]),(0,[z957,z0,z2,z3,z5,z6]),(0,[z0,z958,z2,z3,z5,z6]),(0,[z0,z1,z117,z5,z98,z6])],[(0,[z0,z959,z2,z3,z5,z6]),(0,[z0,z1,z960,z3,z5,z6])],[(0,[z0,z102,z804,z3,z5,z6]),(0,[z32,z0,z1,z102,z3,z6]),(0,[z57,z1,z2,z3,z483,z6])],[(0,[z0,z1,z316,z3,z5,z6]),(0,[z615,z2,z3,z5,z43,z6]),(0,[z0,z1,z2,z3,z5,z902])],[(0,[z112,z20,z2,z3,z5,z6]),(0,[z0,z961,z2,z3,z5,z6]),(0,[z57,z1,z2,z3,z81,z6]),(0,[z0,z255,z2,z3,z5,z6])]],
   [[(0,[z32,z196,z0,z1,z3,z6])],[(0,[z0,z962,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z963,z6]),(0,[z0,z705,z102,z3,z5,z6]),(0,[z0,z964,z2,z3,z5,z6]),(0,[z386,z0,z1,z3,z5,z6])],[(0,[z120,z71,z2,z3,z5,z6]),(0,[z0,z1,z965,z3,z5,z6]),(0,[z0,z1,z2,z3,z283,z366]),(0,[z0,z1,z166,z3,z5,z6]),(0,[z0,z1,z2,z3,z534,z6]),(0,[z0,z1,z2,z263,z5,z6])],[(0,[z0,z284,z2,z3,z5,z366]),(0,[z0,z2,z720,z242,z5,z6]),(0,[z32,z0,z1,z3,z36,z6])],[(0,[z0,z20,z537,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z966]),(0,[z0,z1,z2,z3,z967,z6]),(0,[z0,z1,z2,z3,z5,z968]),(0,[z0,z319,z2,z3,z5,z114]),(0,[z969,z1,z2,z3,z5,z6])],[(0,[z342,z119,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z793])],[(0,[z0,z224,z151,z3,z5,z6]),(0,[z498,z0,z2,z3,z43,z6]),(0,[z970,z0,z1,z2,z3,z6]),(0,[z0,z1,z44,z478,z5,z6])],[(0,[z0,z971,z2,z3,z5,z6]),(0,[z0,z972,z2,z3,z5,z6]),(0,[z21,z1,z2,z148,z5,z6]),(0,[z97,z0,z1,z2,z772,z6])]],
   [[(0,[z0,z1,z973,z3,z5,z6]),(0,[z143,z1,z2,z3,z5,z187]),(0,[z0,z217,z30,z3,z5,z6]),(0,[z0,z1,z3,z974,z5,z6])],[(0,[z0,z1,z2,z5,z975,z6]),(0,[z0,z1,z976,z3,z5,z6]),(0,[z0,z1,z116,z5,z534,z6]),(0,[z0,z1,z117,z3,z124,z6])],[(0,[z0,z94,z2,z3,z5,z366]),(1,[z0,z804,z3,z5,z6]),(0,[z32,z0,z1,z151,z3,z6]),(0,[z0,z1,z401,z204,z5,z6]),(0,[z0,z1,z977,z3,z5,z6]),(0,[z0,z1,z64,z50,z5,z100])],[(0,[z156,z23,z2,z3,z5,z24]),(0,[z0,z1,z409,z3,z5,z6]),(0,[z0,z1,z231,z153,z5,z6])],[(0,[z978,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z979,z5,z6]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z981,z3,z5,z6]),(0,[z0,z1,z2,z3,z982,z6])],[(0,[z21,z1,z52,z148,z5,z6]),(0,[z0,z983,z2,z3,z5,z6]),(0,[z78,z74,z2,z3,z43,z6])],[(0,[z0,z1,z984,z3,z5,z6]),(0,[z0,z985,z1,z3,z5,z6])],[(1,[z861,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z986]),(0,[z0,z1,z117,z189,z5,z6]),(0,[z38,z0,z1,z2,z3,z213]),(0,[z0,z1,z3,z257,z543,z6])]],
   [[(0,[z191,z0,z384,z3,z5,z6]),(0,[z1,z2,z3,z5,z987,z6]),(0,[z988,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z731,z6]),(0,[z0,z1,z460,z3,z104,z6])],[(0,[z0,z1,z2,z989,z5,z6]),(0,[z214,z80,z2,z3,z5,z6])],[(0,[z0,z1,z990,z3,z5,z6]),(0,[z991,z1,z2,z3,z5,z6]),(0,[z196,z0,z55,z3,z5,z129])],[(0,[z0,z1,z2,z3,z992,z6]),(0,[z0,z597,z151,z3,z5,z6]),(0,[z328,z0,z2,z3,z5,z29]),(0,[z0,z255,z2,z153,z5,z6])],[(0,[z0,z1,z2,z3,z283,z6]),(0,[z1,z2,z190,z735,z5,z6]),(0,[z0,z1,z2,z993,z5,z6]),(0,[z994,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z117,z98,z6]),(0,[z995,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z996,z5,z6])],[(0,[z0,z284,z2,z3,z5,z6]),(0,[z196,z0,z1,z3,z105,z129])],[(0,[z997,z0,z2,z3,z5,z6]),(0,[z998,z0,z1,z2,z3,z6]),(0,[z0,z255,z2,z3,z98,z6])],[(0,[z0,z1,z999,z3,z5,z6]),(0,[z0,z334,z2,z3,z5,z6]),(0,[z21,z94,z2,z148,z5,z6]),(0,[z191,z0,z804,z3,z5,z6]),(0,[z0,z1,z2,z3,z180,z6])]],
   [[(0,[z147,z94,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1000]),(0,[z196,z0,z1,z3,z5,z79]),(0,[z0,z80,z231,z3,z5,z6])],[(0,[z0,z1001,z2,z3,z5,z6]),(0,[z0,z1,z2,z1002,z5,z6])],[(0,[z0,z1,z52,z3,z283,z6]),(0,[z0,z1,z1003,z3,z5,z6]),(0,[z0,z1004,z2,z3,z5,z6]),(0,[z473,z0,z1,z3,z36,z6])],[(0,[z443,z1,z2,z3,z5,z6]),(0,[z0,z284,z52,z3,z5,z6]),(0,[z0,z1,z2,z3,z754,z39])],[(0,[z0,z1,z2,z3,z1005,z6]),(0,[z0,z1,z2,z50,z5,z902])],[(0,[z0,z1,z2,z1006,z5,z6]),(0,[z94,z2,z3,z148,z5,z6]),(0,[z0,z284,z2,z3,z283,z6]),(0,[z328,z0,z1,z3,z5,z129]),(0,[z0,z1,z3,z770,z5,z6])],[(0,[z1007,z1,z2,z3,z5,z6]),(0,[z1008,z1,z2,z3,z5,z6]),(0,[z214,z1,z231,z3,z5,z6]),(0,[z38,z0,z1,z2,z3,z754])],[(0,[z0,z1,z1009,z3,z5,z6]),(0,[z1010,z0,z2,z3,z5,z6])]],
   [[(0,[z696,z20,z2,z3,z5,z6]),(0,[z458,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z1011,z5,z6]),(0,[z0,z1,z2,z3,z5,z1012]),(0,[z0,z1,z2,z1013,z5,z6]),(0,[z0,z1,z2,z153,z5,z6]),(0,[z0,z1,z183,z263,z5,z6])],[(0,[z0,z1,z2,z3,z5,z258]),(0,[z0,z1,z2,z3,z5,z793])],[(0,[z0,z1,z2,z1014,z5,z6]),(0,[z0,z94,z52,z3,z5,z6]),(0,[z327,z2,z3,z5,z125,z6])],[(0,[z0,z80,z2,z263,z5,z6])],[(0,[z1015,z0,z1,z2,z5,z6]),(0,[z0,z94,z2,z3,z283,z6]),(0,[z0,z1,z2,z3,z1016,z6])],[(0,[z0,z1,z2,z1017,z5,z6]),(0,[z0,z1,z2,z3,z5,z1018])],[(0,[z0,z1,z1019,z3,z5,z6]),(0,[z0,z1,z1020,z3,z5,z6]),(0,[z214,z255,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1021,z6]),(0,[z0,z1,z52,z3,z5,z258])]],
   [[(0,[z0,z1,z2,z3,z5,z1022])],[(0,[z0,z1,z2,z3,z5,z1023]),(0,[z0,z205,z804,z3,z5,z6]),(0,[z139,z0,z1,z2,z98,z6]),(1,[z0,z2,z3,z5,z808]),(0,[z0,z1,z2,z1024,z5,z6]),(0,[z214,z1,z2,z263,z5,z6])],[(0,[z0,z1,z2,z3,z1025,z6]),(0,[z0,z1,z2,z3,z5,z1026]),(0,[z149,z1,z2,z3,z125,z6]),(0,[z0,z1,z102,z210,z5,z6]),(0,[z0,z1,z183,z3,z5,z6]),(0,[z0,z1,z31,z3,z6,z423])],[(0,[z0,z151,z3,z5,z6,z485]),(0,[z0,z1,z2,z5,z902,z51])],[(0,[z0,z804,z151,z3,z5,z6])],[(0,[z165,z20,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1027]),(0,[z0,z1028,z2,z3,z5,z6]),(0,[z0,z255,z231,z3,z5,z6])],[(0,[z369,z71,z2,z3,z5,z6]),(0,[z0,z1,z133,z3,z5,z6]),(0,[z21,z1,z2,z735,z5,z6]),(0,[z378,z1,z2,z3,z5,z6]),(0,[z0,z1,z1029,z3,z5,z6])],[(0,[z147,z1,z2,z190,z5,z6]),(0,[z0,z1030,z2,z3,z5,z6]),(0,[z0,z1031,z2,z3,z5,z6]),(0,[z0,z1,z409,z3,z483,z6]),(0,[z0,z217,z3,z116,z5,z6]),(0,[z54,z0,z1,z3,z36,z6])]],
   [[(0,[z0,z1,z804,z3,z5,z6]),(0,[z0,z1,z2,z3,z483,z6]),(0,[z0,z1,z2,z1032,z5,z6]),(0,[z0,z1,z231,z263,z5,z6])],[(0,[z0,z94,z2,z3,z5,z258]),(0,[z0,z1033,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z712,z6]),(0,[z0,z1,z2,z3,z1034,z6]),(0,[z1035,z0,z1,z3,z5,z6])],[(0,[z0,z1,z2,z3,z81,z6]),(0,[z0,z135,z3,z5,z6,z29]),(0,[z32,z0,z1,z31,z3,z6])],[(0,[z861,z72,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1036,z6]),(0,[z0,z1,z2,z3,z5,z1037]),(0,[z0,z1038,z2,z3,z5,z6]),(0,[z0,z1,z2,z124,z772,z6])],[(0,[z1039,z1,z2,z3,z5,z6]),(0,[z54,z0,z1,z3,z56,z6]),(0,[z0,z1,z2,z3,z5,z1040])],[(0,[z20,z2,z3,z118,z5,z6]),(0,[z473,z0,z1,z116,z5,z6]),(0,[z0,z1,z2,z772,z98,z6])],[(0,[z0,z327,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1041]),(0,[z0,z1042,z2,z3,z5,z6]),(0,[z0,z1,z2,z189,z772,z6])],[(0,[z38,z0,z1,z2,z210,z6]),(0,[z0,z1,z2,z153,z98,z6])]],
   [[(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z1,z2,z3,z5,z1044]),(0,[z71,z614,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1045,z6]),(0,[z154,z1,z725,z3,z5,z6]),(0,[z0,z1,z2,z3,z35,z366]),(0,[z1,z2,z3,z5,z6,z1046]),(0,[z1047,z1,z2,z3,z5,z6]),(0,[z0,z255,z2,z263,z5,z6]),(0,[z38,z0,z1,z183,z3,z39])],[(0,[z0,z1,z2,z3,z5,z1048]),(0,[z109,z0,z2,z242,z5,z187]),(0,[z0,z1049,z2,z3,z5,z6]),(0,[z261,z0,z1,z2,z5,z51])],[(0,[z0,z1,z2,z362,z124,z6]),(0,[z0,z1050,z2,z3,z5,z6])],[(0,[z0,z1,z1051,z3,z5,z6]),(0,[z287,z0,z1,z2,z98,z6]),(0,[z1052,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z104,z731,z6]),(0,[z0,z1053,z2,z3,z5,z6]),(0,[z38,z386,z0,z1,z3,z39])],[(0,[z57,z1,z2,z3,z5,z187]),(0,[z0,z1,z116,z36,z98,z6]),(0,[z293,z0,z1,z2,z98,z6]),(0,[z0,z1,z1054,z3,z5,z6])],[(0,[z861,z1,z2,z3,z5,z6]),(0,[z0,z1,z1055,z3,z5,z6])],[(0,[z0,z1,z135,z3,z5,z6]),(0,[z0,z1,z44,z3,z534,z6]),(0,[z0,z1,z2,z3,z1056,z6]),(0,[z0,z1,z1057,z3,z5,z6]),(0,[z0,z1,z183,z153,z5,z6])],[(0,[z0,z1,z44,z246,z5,z6]),(0,[z109,z0,z2,z242,z81,z6]),(0,[z85,z0,z1,z2,z5,z902])]],
   [[(0,[z0,z1,z1058,z3,z5,z6]),(0,[z1059,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1061,z1,z2,z3,z5,z6]),(0,[z0,z1,z1062,z3,z5,z6]),(0,[z0,z1,z183,z3,z98,z6]),(0,[z0,z80,z2,z153,z5,z6])],[(0,[z0,z1,z2,z3,z1063,z6]),(0,[z1,z2,z3,z5,z793,z13])],[(0,[z0,z2,z3,z1064,z5,z6])],[(0,[z0,z110,z2,z466,z5,z6]),(0,[z119,z2,z3,z5,z125,z6]),(0,[z32,z0,z1,z3,z62,z6]),(0,[z97,z0,z1,z140,z98,z6])],[(0,[z23,z1,z2,z3,z5,z24]),(0,[z23,z1,z2,z3,z5,z793]),(0,[z191,z0,z102,z3,z5,z6]),(0,[z0,z1,z285,z3,z483,z6]),(0,[z0,z1,z30,z3,z5,z545])],[(0,[z0,z1,z1065,z3,z5,z6]),(0,[z0,z1,z2,z3,z483,z288]),(0,[z418,z0,z2,z3,z43,z6]),(0,[z32,z196,z0,z1,z3,z129]),(0,[z386,z0,z1,z3,z65,z6]),(0,[z1066,z1,z2,z3,z5,z6])],[(0,[z0,z1,z537,z3,z5,z6]),(0,[z0,z1,z285,z3,z81,z6]),(0,[z115,z0,z1,z770,z5,z6]),(0,[z0,z1,z64,z3,z372,z6]),(0,[z214,z1,z2,z153,z5,z6])]],
   [[(0,[z1067,z0,z1,z3,z5,z6]),(0,[z1068,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1069]),(0,[z0,z1,z2,z3,z81,z288]),(0,[z14,z28,z2,z3,z5,z114]),(0,[z0,z1,z2,z5,z6,z902]),(0,[z38,z0,z1,z2,z263,z39]),(0,[z0,z1,z1070,z3,z5,z6])],[(0,[z1071,z1,z2,z3,z5,z6]),(0,[z1072,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z35,z6]),(0,[z0,z1073,z2,z3,z5,z6]),(0,[z576,z0,z1,z2,z98,z6]),(0,[z0,z1,z2,z3,z1074,z6]),(0,[z214,z1,z2,z3,z98,z6]),(0,[z38,z386,z0,z1,z3,z6])],[(0,[z529,z0,z1,z116,z5,z6]),(0,[z0,z1,z2,z770,z5,z6]),(0,[z0,z1,z2,z3,z543,z6]),(0,[z1075,z0,z2,z3,z5,z6]),(0,[z0,z80,z183,z3,z5,z6])],[(0,[z0,z1076,z2,z3,z5,z6]),(0,[z0,z1,z64,z3,z5,z6])],[(0,[z0,z1077,z2,z3,z5,z6]),(0,[z0,z1078,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z793]),(0,[z109,z143,z2,z242,z5,z6]),(0,[z1079,z1,z2,z3,z5,z6]),(0,[z54,z706,z0,z1,z3,z6])],[(0,[z0,z1,z2,z3,z5,z1080]),(0,[z0,z1,z1081,z3,z5,z6]),(0,[z0,z1,z2,z1082,z5,z6])],[(0,[z0,z1,z2,z3,z5,z808])]],
   [[(0,[z0,z1,z52,z3,z35,z6]),(0,[z0,z1,z2,z623,z124,z6])],[(0,[z393,z1,z2,z3,z125,z6]),(0,[z0,z205,z151,z3,z5,z6]),(0,[z214,z1,z183,z3,z5,z6])],[(0,[z426,z1,z155,z3,z5,z6]),(0,[z21,z1,z2,z148,z283,z6]),(0,[z0,z1,z2,z3,z1083,z6]),(0,[z0,z1,z1084,z3,z5,z6]),(0,[z1085,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z210,z5,z6]),(0,[z0,z1086,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z100,z902])],[(0,[z0,z284,z2,z3,z35,z6]),(0,[z21,z284,z2,z148,z5,z6]),(0,[z1,z2,z3,z5,z712,z6]),(0,[z0,z1,z1087,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1088]),(0,[z19,z0,z2,z3,z5,z29]),(0,[z0,z2,z3,z5,z6,z808])],[(0,[z0,z1,z2,z523,z5,z100]),(0,[z0,z1089,z2,z3,z5,z6]),(0,[z0,z1,z1090,z3,z5,z6])],[(0,[z1091,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1092,z6]),(0,[z1093,z1,z2,z3,z5,z6])],[(0,[z71,z404,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1094]),(0,[z0,z1,z2,z3,z1095,z6]),(0,[z0,z1,z3,z5,z732,z129]),(0,[z0,z1,z2,z3,z5,z732]),(0,[z38,z0,z1,z231,z3,z39])],[(0,[z0,z1,z2,z3,z5,z1096]),(0,[z0,z1,z30,z3,z5,z62])]],
   [[(0,[z0,z1,z1097,z3,z5,z6]),(1,[z1,z2,z3,z712,z6]),(0,[z327,z2,z3,z5,z24,z6]),(0,[z1098,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1099,z5,z6])],[(0,[z19,z0,z2,z3,z5,z580]),(0,[z0,z1,z204,z770,z5,z6]),(0,[z54,z0,z217,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z70]),(0,[z0,z1,z2,z3,z6,z105])],[(0,[z0,z94,z2,z3,z35,z6]),(0,[z0,z1,z31,z183,z3,z6])],[(0,[z0,z1,z2,z3,z1100,z6]),(0,[z1101,z1,z2,z3,z5,z6]),(0,[z0,z1,z1102,z3,z5,z6])],[(0,[z0,z2,z3,z5,z907,z6]),(0,[z85,z0,z1,z2,z5,z51]),(0,[z378,z1,z231,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1103]),(0,[z0,z1,z2,z3,z5,z1104]),(0,[z0,z1105,z2,z3,z5,z6]),(0,[z0,z1,z1106,z3,z5,z6]),(1,[z0,z1,z2,z772,z6]),(0,[z38,z0,z1,z2,z3,z39])],[(0,[z342,z1,z2,z3,z492,z6]),(0,[z1,z2,z3,z5,z24,z793]),(0,[z1107,z0,z2,z3,z5,z6])],[(0,[z0,z1108,z2,z3,z5,z6]),(0,[z0,z1,z133,z3,z5,z366]),(0,[z21,z1,z2,z148,z5,z258]),(0,[z0,z1,z2,z153,z543,z6])]],
   [[(0,[z0,z1,z2,z3,z1109,z6]),(0,[z0,z1,z2,z3,z5,z1110]),(0,[z0,z1,z31,z3,z694,z6]),(0,[z0,z255,z183,z3,z5,z6])],[(0,[z115,z0,z1,z116,z5,z6]),(0,[z0,z1,z117,z3,z5,z6])],[(0,[z143,z1,z2,z3,z5,z6]),(0,[z0,z119,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z907,z6])],[],[(0,[z579,z0,z2,z242,z5,z6]),(0,[z1,z155,z725,z3,z5,z6]),(0,[z0,z1111,z2,z3,z5,z6]),(0,[z0,z255,z2,z3,z124,z6]),(0,[z378,z255,z2,z3,z5,z6])],[(0,[z54,z0,z1,z3,z239,z6]),(0,[z1112,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1113]),(0,[z1114,z1,z2,z3,z5,z6]),(0,[z0,z1,z675,z3,z104,z6])],[(0,[z396,z20,z2,z3,z5,z6]),(0,[z0,z1,z1115,z3,z5,z6]),(0,[z378,z1,z2,z263,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 548) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 548).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1072)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [548, 524] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 156).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 156).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [156, 100] = true :=
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

end PEqualNP.Outside.L_meta_36248

theorem PEqualNP.Outside.L_meta_36248 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276153024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36248.solve