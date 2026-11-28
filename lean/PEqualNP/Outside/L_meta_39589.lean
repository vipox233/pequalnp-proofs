import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39589

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
  Nat.testBit (4294901486 * 2 ^ 32 + 4278124168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0409000088414151#64 ++ 0x0040900008841415#64 ++ 0xf76a8089994343ff#64 ++ 0xdf76a8089994343f#64 : BitVec 256),
   (0x28120002208484a0#64 ++ 0x828120002208484a#64 ++ 0xeed9c116628c8cff#64 ++ 0xbeed9c116628c8cf#64 : BitVec 256),
   (0x311c022780d0d0c1#64 ++ 0x0311c022780d0d0c#64 ++ 0x5dc7866784f0f0c5#64 ++ 0x75dc7866784f0f0c#64 : BitVec 256),
   (0x0060185807002a0a#64 ++ 0x10060185807002a0#64 ++ 0x3c3fb8780700ff0c#64 ++ 0xf3c3fb8780700ff0#64 : BitVec 256),
   (0x42402d80072a0002#64 ++ 0x242402d80072a000#64 ++ 0x03ffff8007ff0003#64 ++ 0xf03ffff8007ff000#64 : BitVec 256),
   (0x838037fd5000000c#64 ++ 0x3838037fd5000000#64 ++ 0xffffbffff8000000#64 ++ 0x0ffffbffff800000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000105800000008 0x1000010580000000 0x3c3fb87800000000 0x03c3fb8780000000

def z1 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c0000780000ff0c 0x03c0000780000ff0

def z2 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089994343ff 0xdf76a8089994343f

def z3 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116628c8cff 0xbeed9c116628c8cf

def z4 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866784f0f0c5 0x75dc7866784f0f0c

def z5 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8007ff0003 0xf03ffff8007ff000

def z6 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8000000 0x0ffffbffff800000

def z7 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780700ff0c 0xf3c3fb8780700ff0

def z8 : W := mkw 0x150d022588515151 0x0150d02258851515 0xf76e86e99d7373ff 0xdf76e86e99d7373f

def z9 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x023ff980070f0002 0xf023ff980070f000

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0x03ef868005f30003 0xf03ef868005f3000

def z11 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffef86ef9df3f3ff 0xfffef86ef9df3f3f

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0x02d9c100028c0003 0xb02d9c100028c000

def z13 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c2638780500ff0c 0x43c2638780500ff0

def z14 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffa8c0003 0xbfffffffffa8c000

def z15 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb87805007300 0x43c3fb8780500730

def z16 : W := mkw 0x0100022500000000 0x0010002250000000 0x1106066180000000 0x0110606618000000

def z17 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1106066184707000 0x4110606618470700

def z18 : W := mkw 0x40400800072a0002 0x040400800072a000 0x0000400007ff0003 0xf0000400007ff000

def z19 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01263e8005730000 0x401263e800573000

def z20 : W := mkw 0x8180022550000004 0x0818002255000000 0xc0000007f8000000 0x0c0000007f800000

def z21 : W := mkw 0x28120002208484a0 0x828120002208484a 0x08914116628c8c00 0x208914116628c8c0

def z22 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffdfc777e6fcfcff 0xfffdfc777e6fcfcf

def z23 : W := mkw 0x2010000200808080 0x0201000020080808 0x0881000600808000 0x2088100060080800

def z24 : W := mkw 0x3114022700909080 0x0311402270090908 0x0885066604b0b000 0x20885066604b0b00

def z25 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0xfffffffffa8c8cff 0xbfffffffffa8c8cf

def z26 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x0020388001030000 0x0002038800103000

def z27 : W := mkw 0x43402fa5072a0002 0x243402fa5072a000 0x5fffffe787ff0003 0xf5fffffe787ff000

def z28 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x41c0060780f000c1 0x041c0060780f000c

def z29 : W := mkw 0x0409000088414151 0x0040900008841415 0xd7428081984340f7 0x5d7428081984340f

def z30 : W := mkw 0x0008000080404041 0x0000800008040404 0x55428001804040c5 0x555428001804040c

def z31 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00957f0007ff0003 0xf00957f0007ff000

def z32 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0xffffffffffff0003 0xfffffffffffff000

def z33 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x000000000700ff0c 0xf000000000700ff0

def z34 : W := mkw 0x838027a550000004 0x2838027a55000000 0xc3c00787f8000000 0x0c3c00787f800000

def z35 : W := mkw 0x0609258088414151 0x2060925808841415 0xf7ffbf89994343ff 0xdf7ffbf89994343f

def z36 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0xffffbfffff00ff0c 0xfffffbfffff00ff0

def z37 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x03ffff8007ffff0f 0xf03ffff8007ffff0

def z38 : W := mkw 0xaf9b37fff8c5c5fd 0xbaf9b37fff8c5c5f 0xfffffffffbcfcfff 0xffffffffffbcfcff

def z39 : W := mkw 0x0409000088414151 0x0040900008841415 0x1122008999434300 0x4112200899943430

def z40 : W := mkw 0x0409000088414151 0x0040900008841415 0x00000000014343ff 0xd00000000014343f

def z41 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0xffffbffff80043fc 0x0ffffbffff80043f

def z42 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x08953f7660000000 0x008953f766000000

def z43 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfd263efff8000000 0x0fd263efff800000

def z44 : W := mkw 0x0000105800000008 0x1000010580000000 0xff7fb8f998000000 0x0ff7fb8f99800000

def z45 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x51c6066784f070c1 0x451c6066784f070c

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0780600400f004 0x71c0780600400f00

def z47 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xe3f83f9ff8000000 0x0e3f83f9ff800000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z49 : W := mkw 0x828035d85000000c 0x3828035d85000000 0xa238399878000000 0x0a23839987800000

def z50 : W := mkw 0x838027a550000004 0x2838027a55000000 0xf7ea878ff8000000 0x0f7ea878ff800000

def z51 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x1026386805007300 0x4102638680500730

def z52 : W := mkw 0x28120002208484a0 0x828120002208484a 0xc2c04106608c00f3 0x0c2c04106608c00f

def z53 : W := mkw 0xb39437ff5090908c 0x3b39437ff5090908 0xffffbffffcb0b000 0x2ffffbffffcb0b00

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6d9c100028c00ff 0xbe6d9c100028c00f

def z55 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0xfffffffffebc0000 0x2fffffffffebc000

def z56 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x0885066604f0f0c5 0x70885066604f0f0c

def z57 : W := mkw 0x808010585000000c 0x1808010585000000 0xa000001878000000 0x0a00000187800000

def z58 : W := mkw 0x110c022580505041 0x0110c02258050504 0x55468661847070c5 0x555468661847070c

def z59 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0x08953f766600bc00 0x208953f766600bc0

def z60 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00957f0006bc0000 0x200957f0006bc000

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76a808998000000 0x0f76a80899800000

def z62 : W := mkw 0x28120002208484a0 0x828120002208484a 0x00004000028c8cff 0xb00004000028c8cf

def z63 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dc7c66786fcfcff 0xf5dc7c66786fcfcf

def z64 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb87803000f08 0x83c3fb87803000f0

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0x342a80080100430c 0xd342a80080100430

def z66 : W := mkw 0x0409000088414151 0x0040900008841415 0xc3400081984300f3 0x0c3400081984300f

def z67 : W := mkw 0x0040080007000002 0x0004008000700000 0x003fb80007000000 0xf003fb8000700000

def z68 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x3ffffff807ffff0f 0xf3ffffff807ffff0

def z69 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfffbc19ffa8c8cff 0xbfffbc19ffa8c8cf

def z70 : W := mkw 0x28120002208484a0 0x828120002208484a 0xa2184110628c8cff 0xba2184110628c8cf

def z71 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x2038381803000f08 0x82038381803000f0

def z72 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c0780678400f0c4 0x75c0780678400f0c

def z73 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x11263ee998000000 0x011263ee99800000

def z74 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x0bffbff660000000 0x00bffbff66000000

def z75 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x081538700700ff0c 0xf081538700700ff0

def z76 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfc00007ff8000000 0x0fc00007ff800000

def z77 : W := mkw 0x828035d85000000c 0x3828035d85000000 0xbe3fb9f878000000 0x0be3fb9f87800000

def z78 : W := mkw 0x731c27a780fad0c1 0x2731c27a780fad0c 0x5fc7c7e784fff0c7 0x75fc7c7e784fff0c

def z79 : W := mkw 0x735c2fa787fad0c3 0x2735c2fa787fad0c 0x5fffffe787fff0c7 0xf5fffffe787fff0c

def z80 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5cc180678080f0c5 0x35cc180678080f0c

def z81 : W := mkw 0x40400800072a0002 0x040400800072a000 0x0000000005730000 0x4000000000573000

def z82 : W := mkw 0x331c27a780d0d0c1 0x2331c27a780d0d0c 0x5fffbfe784f0f0c5 0x75fffbfe784f0f0c

def z83 : W := mkw 0x0200258000000000 0x2020025800000000 0x03ffbf8000000000 0x003ffbf800000000

def z84 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0xff7fb8f99f43ffff 0xfff7fb8f99f43fff

def z85 : W := mkw 0x0200258000000000 0x2020025800000000 0x01263e8000000000 0x001263e800000000

def z86 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x1fffffe007fff007 0xf1fffffe007fff00

def z87 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03c0478000ff0003 0x003c0478000ff000

def z88 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfc3fb87ff8000000 0x0fc3fb87ff800000

def z89 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x0010381002000c00 0x00010381002000c0

def z90 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5dc7866785f3f3ff 0xf5dc7866785f3f3f

def z91 : W := mkw 0x0000105800000008 0x1000010580000000 0x3c3fb8780100430c 0xd3c3fb8780100430

def z92 : W := mkw 0x0008000080404041 0x0000800008040404 0xf74a8001804040ff 0xdf74a8001804040f

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed9811660000000 0x0eed981166000000

def z94 : W := mkw 0x0409000088414151 0x0040900008841415 0xf5428009984043fd 0x5f5428009984043f

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6488000000000ff 0x9e6488000000000f

def z96 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01b77f8007ff0000 0x601b77f8007ff000

def z97 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c2a80780100ff0c 0xd3c2a80780100ff0

def z98 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0xefffff9667ff8cff 0xfefffff9667ff8cf

def z99 : W := mkw 0xb39c37ffd0d0d0cd 0x3b39c37ffd0d0d0c 0xffffbffffcf0f0c5 0x7ffffbffffcf0f0c

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c01800000008004 0x30c0180000000800

def z101 : W := mkw 0x317c1a7f87d0facb 0x1317c1a7f87d0fac 0x7dffbe7f87f0ffcd 0xf7dffbe7f87f0ffc

def z102 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xe7ffff8007ff00ff 0xfe7ffff8007ff00f

def z103 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xfffbc19ffbcfcfff 0xffffbc19ffbcfcff

def z104 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c0000678000f0c4 0x05c0000678000f0c

def z105 : W := mkw 0x1104022500101000 0x0110402250010100 0x0004066004303000 0x0000406600430300

def z106 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fdfc76786fcf0c7 0xf5fdfc76786fcf0c

def z107 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0xfffffffffb0f0002 0x8fffffffffb0f000

def z108 : W := mkw 0x0100022500000000 0x0010002250000000 0x5dc7866780000000 0x05dc786678000000

def z109 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x37ffff8807ff430f 0xf37ffff8807ff430

def z110 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe2d84116628c0cfb 0x8e2d84116628c0cf

def z111 : W := mkw 0x82e03dd857002a0e 0x382e03dd857002a0 0xa23839987b000f08 0x8a23839987b000f0

def z112 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xc3c0068798f300f3 0x0c3c0068798f300f

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x036a808001430003 0xd036a80800143000

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c7860004f00001 0x701c7860004f0000

def z115 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0xffffbffff94343ff 0xdffffbffff94343f

def z116 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0xf7ffff899fff43ff 0xff7ffff899fff43f

def z117 : W := mkw 0x7b5e2fa7a7fed4e3 0xa7b5e2fa7a7fed4e 0xfffffff7e7fffcff 0xffffffff7e7fffcf

def z118 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x081538700600bc00 0x2081538700600bc0

def z119 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x3d3fbef998000000 0x03d3fbef99800000

def z120 : W := mkw 0x39160227209494a0 0x839160227209494a 0x0895477666bcbc00 0x20895477666bcbc0

def z121 : W := mkw 0x42002580002a0000 0x242002580002a000 0x0080470000bc0000 0x00080470000bc000

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c19801002008c0c 0xb2c19801002008c0

def z123 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffa008c0c 0xbffffbffffa008c0

def z124 : W := mkw 0x0409000088414151 0x0040900008841415 0xf4000009980043fc 0x0f4000009980043f

def z125 : W := mkw 0x2010000200808080 0x0201000020080808 0x4cc18006008080c5 0x34cc18006008080c

def z126 : W := mkw 0x02603dd807002a0a 0x302603dd807002a0 0x3fffbff80700ff0c 0xf3fffbff80700ff0

def z127 : W := mkw 0x735c2fa787fad0c3 0x2735c2fa787fad0c 0x5dd7ff6786fcf0c5 0x75dd7ff6786fcf0c

def z128 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x08957f7006bcbc00 0x208957f7006bcbc0

def z129 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866780f000c1 0x05dc7866780f000c

def z130 : W := mkw 0x828035d85000000c 0x3828035d85000000 0x0020388818000000 0x0002038881800000

def z131 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffbf8005730000 0x403ffbf800573000

def z132 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffcf00001 0x7ffffbffffcf0000

def z133 : W := mkw 0x0802000020040420 0x8080200002004042 0xa2d9c110628c0c3b 0xba2d9c110628c0c3

def z134 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x0000000004f0f0c5 0x70000000004f0f0c

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0x340000080000430c 0x0340000080000430

def z136 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfedfc176668cfcff 0xffedfc176668cfcf

def z137 : W := mkw 0x0200258000000000 0x2020025800000000 0x03c0078000000000 0x003c007800000000

def z138 : W := mkw 0x100c000080505041 0x0100c00008050504 0x0000000004707000 0x4000000000470700

def z139 : W := mkw 0x42002580002a0000 0x242002580002a000 0x02004180000f0002 0x002004180000f000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00001000008c0c 0x02c00001000008c0

def z141 : W := mkw 0x0409000088414151 0x0040900008841415 0xe3680089994303fb 0x8e3680089994303f

def z142 : W := mkw 0x28520802278484a2 0x828520802278484a 0xeefff916678c8cff 0xfeefff916678c8cf

def z143 : W := mkw 0x3114022700909080 0x0311402270090908 0x09c7866604f0b001 0x709c7866604f0b00

def z144 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0x08957f1666bc8c00 0x208957f1666bc8c0

def z145 : W := mkw 0x838027a550000004 0x2838027a55000000 0xefd98797f8000000 0x0efd98797f800000

def z146 : W := mkw 0x42482d80876a4043 0x242482d80876a404 0x57ffff8187ff40c7 0xf57ffff8187ff40c

def z147 : W := mkw 0x2832105a2084aea8 0x92832105a2084aea 0xfc00007e6000fffc 0x0fc00007e6000fff

def z148 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff9430003 0xdffffbffff943000

def z149 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03f87f8003ff0003 0x803f87f8003ff000

def z150 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x2c39b81803008f0c 0xb2c39b81803008f0

def z151 : W := mkw 0x6e5b2d82afefc5f3 0xa6e5b2d82afefc5f 0xffffff9fffffcfff 0xfffffff9fffffcff

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0xfffb819ff8000000 0x0fffb819ff800000

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed98116600000ff 0x9eed98116600000f

def z154 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfefbc11e638ccfff 0xffefbc11e638ccff

def z155 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x40000007800000c0 0x040000007800000c

def z156 : W := mkw 0x28120002208484a0 0x828120002208484a 0x00804106608c0000 0x000804106608c000

def z157 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x1000006800007300 0x0100000680000730

def z158 : W := mkw 0x81a0127d50002a0c 0x181a0127d50002a0 0xfc00007ff800ff0c 0x0fc00007ff800ff0

def z159 : W := mkw 0x317c0a2787d0fac3 0x0317c0a2787d0fac 0x5dc7866787f0ffcd 0xf5dc7866787f0ffc

def z160 : W := mkw 0x828035d85000000c 0x3828035d85000000 0xeef9b99e78000000 0x0eef9b99e7800000

def z161 : W := mkw 0x0000105800000008 0x1000010580000000 0x0815387000000000 0x0081538700000000

def z162 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7ddf867786f0fccd 0xf7ddf867786f0fcc

def z163 : W := mkw 0x0068185887406a4b 0x10068185887406a4 0x7d7fb8798740ffcd 0xf7d7fb8798740ffc

def z164 : W := mkw 0x0802000020040420 0x8080200002004042 0xa2184110620c0c3a 0x8a2184110620c0c3

def z165 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3efff978078cff0f 0xf3efff978078cff0

def z166 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x080000700000bc00 0x0080000700000bc0

def z167 : W := mkw 0x46092580886b4151 0x246092580886b415 0xc3c0478198ff00f3 0x0c3c0478198ff00f

def z168 : W := mkw 0x0200258000000000 0x2020025800000000 0xefffbf9660000000 0x0efffbf966000000

def z169 : W := mkw 0x28120002208484a0 0x828120002208484a 0x4cc1c006028c8cff 0xb4cc1c006028c8cf

def z170 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x0bfffff007ffbc03 0xf0bfffff007ffbc0

def z171 : W := mkw 0x838837fdd040404d 0x3838837fdd040404 0xffffbffff84040c5 0x5ffffbffff84040c

def z172 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00107900020c0000 0x000107900020c000

def z173 : W := mkw 0x0040080007000002 0x0004008000700000 0x343fb8080700430c 0xf343fb8080700430

def z174 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01267e8007ff0003 0xf01267e8007ff000

def z175 : W := mkw 0x868135d85801011c 0x3868135d85801011 0xa23839987903033a 0x8a23839987903033

def z176 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x342a80080700ff0c 0xf342a80080700ff0

def z177 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfe3839fff8000000 0x0fe3839fff800000

def z178 : W := mkw 0x0040080007000002 0x0004008000700000 0x2c3fb81007008c0c 0xf2c3fb81007008c0

def z179 : W := mkw 0x3114022700909080 0x0311402270090908 0x1c87866604b0f004 0x71c87866604b0f00

def z180 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0x0bffff9667ff8c03 0xf0bffff9667ff8c0

def z181 : W := mkw 0x3114022700909080 0x0311402270090908 0x5dc7866784b0b000 0x25dc7866784b0b00

def z182 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7def866f85f0f3cd 0xf7def866f85f0f3c

def z183 : W := mkw 0x046118580f012b1a 0x1046118580f012b1 0xa23838981b030f3a 0x8a23838981b030f3

def z184 : W := mkw 0x0409000088414151 0x0040900008841415 0xff7b80999b43cfff 0xfff7b80999b43cff

def z185 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1106066184f0f0c5 0x71106066184f0f0c

def z186 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xcbd53ff7f8000000 0x0cbd53ff7f800000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x1006006004007000 0x4100600600400700

def z188 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03c7c78004ff0003 0x703c7c78004ff000

def z189 : W := mkw 0xb39c37ffd0d0d0cd 0x3b39c37ffd0d0d0c 0x5dd7bf77e4f0f0c5 0x75dd7bf77e4f0f0c

def z190 : W := mkw 0x40400800072a0002 0x040400800072a000 0x02d9c10007ff0003 0xf02d9c10007ff000

def z191 : W := mkw 0x0802000020040420 0x8080200002004042 0x00004000020c0c3a 0x800004000020c0c3

def z192 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xff6a809ff943cfff 0xdff6a809ff943cff

def z193 : W := mkw 0x0862185827042e2a 0x90862185827042e2 0xbe3ff978670cff3e 0xfbe3ff978670cff3

def z194 : W := mkw 0x0000000000000000 0x0000000000000000 0x0248800000000003 0x9024880000000000

def z195 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3f7fb8f80743ff0f 0xf3f7fb8f80743ff0

def z196 : W := mkw 0x28120002208484a0 0x828120002208484a 0xc2d9c106628c00f3 0xbc2d9c106628c00f

def z197 : W := mkw 0x3114022700909080 0x0311402270090908 0x080000660000b000 0x0080000660000b00

def z198 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xc3c04707e0fc00f3 0x0c3c04707e0fc00f

def z199 : W := mkw 0x116c1a7d87507a4b 0x1116c1a7d87507a4 0x3d3fbe798770ff0c 0xf3d3fbe798770ff0

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76a8089980000ff 0x9f76a8089980000f

def z201 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x1c07806004f0f0c5 0x71c07806004f0f0c

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0xa20800000000003a 0x8a20800000000003

def z203 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x02387980030f0002 0x802387980030f000

def z204 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffc007fff8000000 0x0ffc007fff800000

def z205 : W := mkw 0x3014000200909080 0x0301400020090908 0x0000000004b0b000 0x20000000004b0b00

def z206 : W := mkw 0x0401000008010110 0x0040100000801011 0xb62a80881903433e 0xdb62a80881903433

def z207 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfed9817ff8000000 0x0fed9817ff800000

def z208 : W := mkw 0x0200258000000000 0x2020025800000000 0x0238398000000000 0x0023839800000000

def z209 : W := mkw 0x0401000008010110 0x0040100000801011 0xa22800881903033a 0x8a22800881903033

def z210 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1d0786618470f004 0x71d0786618470f00

def z211 : W := mkw 0xab9227a7708484a4 0xaab9227a7708484a 0xefd9c797fa8c8cff 0xbefd9c797fa8c8cf

def z212 : W := mkw 0x73542fa707ba9082 0x273542fa707ba908 0x0bffffe607ffb003 0xf0bffffe607ffb00

def z213 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0x13ffffe99fff0003 0xf13ffffe99fff000

def z214 : W := mkw 0xabf23fff7784aeae 0xbabf23fff7784aea 0xffffffffff8cffff 0xfffffffffff8cfff

def z215 : W := mkw 0xb39c37ffd0d0d0cd 0x3b39c37ffd0d0d0c 0xffffbffff8f000c1 0x0ffffbffff8f000c

def z216 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1987066784f0f000 0x61987066784f0f00

def z217 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0xfefff97e678cffff 0xffefff97e678cfff

def z218 : W := mkw 0x110c022580505041 0x0110c02258050504 0x11c7866184f07001 0x711c7866184f0700

def z219 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x11263ee805737300 0x411263ee80573730

def z220 : W := mkw 0x28120002208484a0 0x828120002208484a 0x2c19c010028c8cff 0xb2c19c010028c8cf

def z221 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffcf866784f0f0ff 0xfffcf866784f0f0f

def z222 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec00001660008cfc 0x0ec00001660008cf

def z223 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x3cbfff7807bcff0c 0xf3cbfff7807bcff0

def z224 : W := mkw 0x0409000088414151 0x0040900008841415 0x11220089994343ff 0xd11220089994343f

def z225 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc786678000f0c4 0x05dc786678000f0c

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x342a800800000000 0x0342a80080000000

def z227 : W := mkw 0x46412d800f2b0112 0x246412d800f2b011 0xa3ffff881fff033b 0xfa3ffff881fff033

def z228 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x303e387807007f08 0xc303e387807007f0

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x4cc1800600000000 0x04cc180060000000

def z230 : W := mkw 0x0401000008010110 0x0040100000801011 0xe6688088190303ff 0x9e6688088190303f

def z231 : W := mkw 0x0040080007000002 0x0004008000700000 0x0015380006000000 0x2001538000600000

def z232 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x000000000600bc00 0x2000000000600bc0

def z233 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x037af980034f0003 0xd037af980034f000

def z234 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeffbc19663cf8cff 0xfeffbc19663cf8cf

def z235 : W := mkw 0x0409000088414151 0x0040900008841415 0xf6280089990343fe 0x8f6280089990343f

def z236 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0x08957976668cbc00 0x208957976668cbc0

def z237 : W := mkw 0x39160227209494a0 0x839160227209494a 0xeeddc77666bcbcff 0xbeeddc77666bcbcf

def z238 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03ffff8000ff0003 0x003ffff8000ff000

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x0106060004700000 0x4010606000470000

def z240 : W := mkw 0x0409000088414151 0x0040900008841415 0xf6488009980043ff 0x9f6488009980043f

def z241 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0xf76ebee9994343ff 0xdf76ebee9994343f

def z242 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00043e0004300000 0x000043e000430000

def z243 : W := mkw 0x381e0002a0d4d4e1 0x8381e0002a0d4d4e 0x0000400006fcfcff 0xf0000400006fcfcf

def z244 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x4cc1800604f0f0c5 0x74cc1800604f0f0c

def z245 : W := mkw 0x0401000008010110 0x0040100000801011 0xf76a80899903033a 0x8f76a80899903033

def z246 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0xc3ffff8667ff00f3 0xfc3ffff8667ff00f

def z247 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec19801662008cfc 0xbec19801662008cf

def z248 : W := mkw 0x8589127dd841415d 0x18589127dd841415 0xfc00007ff80043fc 0x0fc00007ff80043f

def z249 : W := mkw 0x81e01a7d57002a0e 0x181e01a7d57002a0 0xfc3fb87fff00ff0c 0xffc3fb87fff00ff0

def z250 : W := mkw 0x2c130002288585b0 0x82c130002288585b 0xeef9c19e7b8f8fff 0xbeef9c19e7b8f8ff

def z251 : W := mkw 0x2010000200808080 0x0201000020080808 0x4ed9c106028c80c7 0xb4ed9c106028c80c

def z252 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0xc3ffff819fff00f3 0xfc3ffff819fff00f

def z253 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000400f004 0x7000000000400f00

def z254 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffef86ef9cf0f0c5 0x7ffef86ef9cf0f0c

def z255 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xb33e3ff9f8000000 0x0b33e3ff9f800000

def z256 : W := mkw 0x46092580886b4151 0x246092580886b415 0xf7eac78999ff43ff 0xdf7eac78999ff43f

def z257 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x5542800184f0f0c5 0x75542800184f0f0c

def z258 : W := mkw 0x28120002208484a0 0x828120002208484a 0x0ad9c116628c8c03 0xb0ad9c116628c8c0

def z259 : W := mkw 0x020035d800000008 0x3020035d80000000 0x3fffbff800000000 0x03fffbff80000000

def z260 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x19b73ffff8000000 0x019b73ffff800000

def z261 : W := mkw 0x0100022500000000 0x0010002250000000 0xffef86ef98000000 0x0ffef86ef9800000

def z262 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x0000000000f000c1 0x00000000000f000c

def z263 : W := mkw 0x838027a550000004 0x2838027a55000000 0xc3ffbf87f8000000 0x0c3ffbf87f800000

def z264 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xeeddbf7660000000 0x0eeddbf766000000

def z265 : W := mkw 0xa39037ff5080808c 0x3a39037ff5080808 0xffffbffff88080c5 0x3ffffbffff88080c

def z266 : W := mkw 0x2110022700808080 0x0211002270080808 0x5dc78667808080c5 0x35dc78667808080c

def z267 : W := mkw 0x317c1a7f87d0facb 0x1317c1a7f87d0fac 0x7c3fb87f8700ffcc 0xf7c3fb87f8700ffc

def z268 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xd3e63feff8000000 0x0d3e63feff800000

def z269 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfdc78677e4f0fcfd 0x7fdc78677e4f0fcf

def z270 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfeffb97e6700ff0c 0xffeffb97e6700ff0

def z271 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xfffffffff8ff0003 0x0fffffffff8ff000

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002008c0c 0xb0000000002008c0

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x02c04100008c0003 0x002c04100008c000

def z274 : W := mkw 0x28120002208484a0 0x828120002208484a 0x00004000008c00f3 0x000004000008c00f

def z275 : W := mkw 0x0200258000000000 0x2020025800000000 0xf7ffbf8998000000 0x0f7ffbf899800000

def z276 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1000006180007000 0x0100000618000700

def z277 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089980043fc 0x0f76a8089980043f

def z278 : W := mkw 0x0000000000000000 0x0000000000000000 0x0019800002000000 0xb001980000200000

def z279 : W := mkw 0x0409000088414151 0x0040900008841415 0xd3620089994343f3 0x4d3620089994343f

def z280 : W := mkw 0x40400800072a0002 0x040400800072a000 0x036ac08007ff0003 0xf036ac08007ff000

def z281 : W := mkw 0x0409000088414151 0x0040900008841415 0xf5220089994343fc 0x4f5220089994343f

def z282 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfdc7867ff8000000 0x0fdc7867ff800000

def z283 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x203838180700ff0c 0xf203838180700ff0

def z284 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xf7eac18ff9cf43ff 0xdf7eac18ff9cf43f

def z285 : W := mkw 0x2812105a208484a8 0x92812105a208484a 0xfefff97e628c8cff 0xbfefff97e628c8cf

def z286 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x183738780700ff00 0x6183738780700ff0

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0xee59801002008cff 0xbee59801002008cf

def z288 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0xffffbffff9434300 0x4ffffbffff943430

def z289 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780600bc00 0x23c3fb8780600bc0

def z290 : W := mkw 0x0409000088414151 0x0040900008841415 0x55628089994343c5 0x555628089994343c

def z291 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0x03ffff8007ff8cff 0xf03ffff8007ff8cf

def z292 : W := mkw 0x2010000200808080 0x0201000020080808 0x00000000008080c5 0x300000000008080c

def z293 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x2c1980100700ff0c 0xf2c1980100700ff0

def z294 : W := mkw 0x28120002208484a0 0x828120002208484a 0xcad14116628c8cf3 0x2cad14116628c8cf

def z295 : W := mkw 0x31741a7f0790ba8a 0x131741a7f0790ba8 0x08953e7606b0bc00 0x208953e7606b0bc0

def z296 : W := mkw 0x2010000200808080 0x0201000020080808 0x6cd9801602808ccd 0xb6cd9801602808cc

def z297 : W := mkw 0x0401000008010110 0x0040100000801011 0x000000000103033a 0x8000000000103033

def z298 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0xeeddff76628c8cff 0xbeeddff76628c8cf

def z299 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01e7be8005f30001 0x701e7be8005f3000

def z300 : W := mkw 0x28120002208484a0 0x828120002208484a 0x08914116628c8cff 0xb08914116628c8cf

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0xec00001660000000 0x0ec0000166000000

def z302 : W := mkw 0x0040080007000002 0x0004008000700000 0x02fff900078c0003 0xf02fff900078c000

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x00004000028c0003 0xb00004000028c000

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x2018001002000c08 0x82018001002000c0

def z305 : W := mkw 0x28120002208484a0 0x828120002208484a 0x4cd1c116628c8cc5 0x34cd1c116628c8cc

def z306 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfc953f7ff8000000 0x0fc953f7ff800000

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0xe648800000000000 0x0e64880000000000

def z308 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x2c1db8700600bc0c 0xb2c1db8700600bc0

def z309 : W := mkw 0x0000105800000008 0x1000010580000000 0x3c3fb8780400f004 0x73c3fb8780400f00

def z310 : W := mkw 0x287208022784aea2 0x8287208022784aea 0xeed9c116678cffff 0xfeed9c116678cfff

def z311 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03d57f8006ff0003 0x203d57f8006ff000

def z312 : W := mkw 0x8280258050000004 0x2828025805000000 0x8200018078000000 0x0820001807800000

def z313 : W := mkw 0x0040080007000002 0x0004008000700000 0x0000000007000000 0xf000000000700000

def z314 : W := mkw 0x40400800072a0002 0x040400800072a000 0x003ff80007ff0003 0xf003ff80007ff000

def z315 : W := mkw 0x0100022500000000 0x0010002250000000 0x0885066600000000 0x0088506660000000

def z316 : W := mkw 0xebd23fff77ae84ae 0xbebd23fff77ae84a 0xffffffffffff8cff 0xfffffffffffff8cf

def z317 : W := mkw 0x0409000088414151 0x0040900008841415 0xc0000001980000f0 0x0c0000001980000f

def z318 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c3b80180300cf0c 0xf3c3b80180300cf0

def z319 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0x3d3fb8f99f43ff0c 0xf3d3fb8f99f43ff0

def z320 : W := mkw 0x0401000008010110 0x0040100000801011 0xa000000818000338 0x0a00000081800033

def z321 : W := mkw 0x0802000020040420 0x8080200002004042 0xae19c110620c8c3e 0xbae19c110620c8c3

def z322 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x02ddff0006bc0003 0xb02ddff0006bc000

def z323 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff900430c 0xdffffbffff900430

def z324 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xf76ebee998000000 0x0f76ebee99800000

def z325 : W := mkw 0x0802000020040420 0x8080200002004042 0x00104110620c0c00 0x000104110620c0c0

def z326 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0x11263ee999434300 0x411263ee99943430

def z327 : W := mkw 0x28120002208484a0 0x828120002208484a 0x00004000028c8c00 0x200004000028c8c0

def z328 : W := mkw 0xbb9e37fff0d4d4ed 0xbbb9e37fff0d4d4e 0xfffffffffefcfcff 0xffffffffffefcfcf

def z329 : W := mkw 0x8a8235d87004042c 0xb8a8235d87004042 0xa23879987a0c0c3a 0x8a23879987a0c0c3

def z330 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe6c8c106608c00ff 0x9e6c8c106608c00f

def z331 : W := mkw 0x6a723dda27aeaeaa 0xb6a723dda27aeaea 0xfffffffe67ffffff 0xffffffffe67fffff

def z332 : W := mkw 0x0000105800000008 0x1000010580000000 0x2038381800000000 0x0203838180000000

def z333 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff80000ff 0x9ffffbffff80000f

def z334 : W := mkw 0xb79d37ffd8d1d1dd 0x3b79d37ffd8d1d1d 0xffffbffffdf3f3ff 0xfffffbffffdf3f3f

def z335 : W := mkw 0x0409000088414151 0x0040900008841415 0x00000000000043fc 0x000000000000043f

def z336 : W := mkw 0x0200258000000000 0x2020025800000000 0x00953f0000000000 0x000953f000000000

def z337 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0x0bfffff667ff0003 0xf0bfffff667ff000

def z338 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0xffffbffff84300f3 0x0ffffbffff84300f

def z339 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fef86e785f3f0c7 0xf5fef86e785f3f0c

def z340 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x5de7beef98000000 0x05de7beef9800000

def z341 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x02f9f980038f0003 0xb02f9f980038f000

def z342 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7fbc1899bcf43ff 0xff7fbc1899bcf43f

def z343 : W := mkw 0x0000105800000008 0x1000010580000000 0x3c3fb87802008c0c 0xb3c3fb87802008c0

def z344 : W := mkw 0x28120002208484a0 0x828120002208484a 0xee184116620c8cfe 0x8ee184116620c8cf

def z345 : W := mkw 0x46693dd88f6b6b5b 0x346693dd88f6b6b5 0xfffffff99fffffff 0xffffffff99ffffff

def z346 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x41c7860784f000c1 0x741c7860784f000c

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c19801000000000 0x02c1980100000000

def z348 : W := mkw 0x838027a550000004 0x2838027a55000000 0x0100068198000000 0x0010006819800000

def z349 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x013fbe8007730000 0xf013fbe800773000

def z350 : W := mkw 0x313c127f80d0fac9 0x1313c127f80d0fac 0x7c00007f8000ffcc 0x07c00007f8000ffc

def z351 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xefd9c717e2fc8cff 0xbefd9c717e2fc8cf

def z352 : W := mkw 0x046908008f416b53 0x0046908008f416b5 0xf76a80899f43ffff 0xff76a80899f43fff

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x5542800180000000 0x0554280018000000

def z354 : W := mkw 0x0040080007000002 0x0004008000700000 0x0038380003000000 0x8003838000300000

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0x0085060004b00000 0x20085060004b0000

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x2028000801000308 0x8202800080100030

def z357 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0xf77ab8999b434fff 0xdf77ab8999b434ff

def z358 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xfc00001ff800cffc 0x0fc00001ff800cff

def z359 : W := mkw 0x3114022700909080 0x0311402270090908 0x4cc5866604b0b0c5 0x34cc5866604b0b0c

def z360 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfc000077e000fcfc 0x0fc000077e000fcf

def z361 : W := mkw 0x6a12258220ae84a0 0xa6a12258220ae84a 0xc3c0478660ff00f3 0x0c3c0478660ff00f

def z362 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0xeef9f996638f8cff 0xbeef9f996638f8cf

def z363 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c00006784f0f0c5 0x75c00006784f0f0c

def z364 : W := mkw 0x28120002208484a0 0x828120002208484a 0xcec1c106608c80f7 0x3cec1c106608c80f

def z365 : W := mkw 0x0409000088414151 0x0040900008841415 0x1000000998004300 0x0100000099800430

def z366 : W := mkw 0xc7c93ffddf6b415f 0x3c7c93ffddf6b415 0xffffffffffff43ff 0xfffffffffffff43f

def z367 : W := mkw 0x2070185a0780aa8a 0x12070185a0780aa8 0x7cffb87e0780ffcd 0xf7cffb87e0780ffc

def z368 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffc00f004 0x7ffffbffffc00f00

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x00914100028c0000 0x200914100028c000

def z370 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3dffbe7807f0ff0d 0xf3dffbe7807f0ff0

def z371 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0xeeddf976668cbcff 0xbeeddf976668cbcf

def z372 : W := mkw 0x0862185827042e2a 0x90862185827042e2 0xa2387918630c0f3a 0x8a2387918630c0f3

def z373 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x02bd7f8007bf0002 0xa02bd7f8007bf000

def z374 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xff6a80fff8000000 0x0ff6a80fff800000

def z375 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffffc7ffffffffff 0xfffffc7fffffffff

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c7860000000000 0x001c786000000000

def z377 : W := mkw 0x2010000200808080 0x0201000020080808 0x5cc780660480f0c5 0x75cc780660480f0c

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x0811001002008c00 0x20811001002008c0

def z379 : W := mkw 0x307c080287d0fac3 0x0307c080287d0fac 0x0000000007f0ffcd 0xf0000000007f0ffc

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x1dc7866004f0f005 0x71dc7866004f0f00

def z381 : W := mkw 0x341d000288d1d1d1 0x0341d000288d1d1d 0x0000000005f3f3ff 0xf0000000005f3f3f

def z382 : W := mkw 0x828035d85000000c 0x3828035d85000000 0xf77ab999f8000000 0x0f77ab999f800000

def z383 : W := mkw 0x46412d800f2b0112 0x246412d800f2b011 0xa23879881b0f033a 0x8a23879881b0f033

def z384 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c3fb8780000ff0c 0x03c3fb8780000ff0

def z385 : W := mkw 0x0802000020040420 0x8080200002004042 0x82004100600c0032 0x082004100600c003

def z386 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x23ffff9807ff0f0b 0xf23ffff9807ff0f0

def z387 : W := mkw 0x62502d8207aa8082 0x262502d8207aa808 0x4fffff8607ff80c7 0xf4fffff8607ff80c

def z388 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03e67f8005ff0003 0x403e67f8005ff000

def z389 : W := mkw 0x83c03ffd5700000e 0x383c03ffd5700000 0xffffbfffff000000 0xfffffbfffff00000

def z390 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffff800ff0c 0x0ffffbffff800ff0

def z391 : W := mkw 0x444908008f6b4153 0x0444908008f6b415 0x0000400007ff43ff 0xf0000400007ff43f

def z392 : W := mkw 0x004018580700000a 0x1004018580700000 0x3c3fb87807000000 0xf3c3fb8780700000

def z393 : W := mkw 0x110c022580505041 0x0110c02258050504 0x0100060180700000 0x0010006018070000

def z394 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xdfc786e79cf3f0f7 0x7dfc786e79cf3f0f

def z395 : W := mkw 0x313c127f80d0fac9 0x1313c127f80d0fac 0x7dc7867f84f0ffcd 0x77dc7867f84f0ffc

def z396 : W := mkw 0x0008000080404041 0x0000800008040404 0x1102000180404000 0x4110200018040400

def z397 : W := mkw 0x315c0a2787d0d0c3 0x0315c0a2787d0d0c 0x5dffbe6787f0f0c5 0xf5dffbe6787f0f0c

def z398 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0xfc3fb8799f00fffc 0xffc3fb8799f00fff

def z399 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0x08957f76628c8c00 0x208957f76628c8c0

def z400 : W := mkw 0xb39c27a7d0d0d0c5 0x2b39c27a7d0d0d0c 0xc3c00787f8f000c1 0x0c3c00787f8f000c

def z401 : W := mkw 0xa992127f708484ac 0x9a992127f708484a 0xfed9c17ffa8c8cff 0xbfed9c17ffa8c8cf

def z402 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec914116628c8cfc 0x2ec914116628c8cf

def z403 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xf7ffff899fff0003 0xff7ffff899fff000

def z404 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x55c2860780f040c5 0x555c2860780f040c

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x376a80880143430f 0xd376a80880143430

def z406 : W := mkw 0x40000000002a0000 0x040000000002a000 0x0000400000ff0003 0x00000400000ff000

def z407 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0xf76ebe899d7343ff 0xdf76ebe899d7343f

def z408 : W := mkw 0x0409000088414151 0x0040900008841415 0x342a8008014343ff 0xd342a8008014343f

def z409 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x343ab81803004f0c 0xd343ab81803004f0

def z410 : W := mkw 0x0802000020040420 0x8080200002004042 0xe658c110620c0cff 0x9e658c110620c0cf

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c1f80700600fc0c 0xf3c1f80700600fc0

def z412 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x102638680700ff0c 0xf102638680700ff0

def z413 : W := mkw 0x317c1a7f87d0facb 0x1317c1a7f87d0fac 0x5dd7be7786f0fcc5 0x75dd7be7786f0fcc

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2c0010660000000 0x0c2c001066000000

def z415 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c1538780600ff0c 0x23c1538780600ff0

def z416 : W := mkw 0x0100022500000000 0x0010002250000000 0xffdf8777e0000000 0x0ffdf8777e000000

def z417 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0x1000006998000000 0x0100000699800000

def z418 : W := mkw 0x0409000088414151 0x0040900008841415 0xfffb819ff94343ff 0xdfffb819ff94343f

def z419 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dd7c777e6fcfcc5 0x75dd7c777e6fcfcc

def z420 : W := mkw 0x4a422d80272e0422 0xa4a422d80272e042 0xa3ffff9067ff0c3b 0xfa3ffff9067ff0c3

def z421 : W := mkw 0x307c185a87d0facb 0x1307c185a87d0fac 0x3c3fb87807f0ffcd 0xf3c3fb87807f0ffc

def z422 : W := mkw 0x938c37fdd050504d 0x3938c37fdd050504 0xffffbffffc707000 0x4ffffbffffc70700

def z423 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x3d3fbef80773ff0c 0xf3d3fbef80773ff0

def z424 : W := mkw 0x0409000088414151 0x0040900008841415 0xe6488000014343ff 0xde6488000014343f

def z425 : W := mkw 0x0040080007000002 0x0004008000700000 0x01ffbe0007f00001 0xf01ffbe0007f0000

def z426 : W := mkw 0x28120002208484a0 0x828120002208484a 0xecc1801660808cfd 0x3ecc1801660808cf

def z427 : W := mkw 0xc3c02fa5572a0006 0x2c3c02fa5572a000 0xc3ffff87ffff0003 0xfc3ffff87ffff000

def z428 : W := mkw 0x828035d85000000c 0x3828035d85000000 0xa3ffbf9878000000 0x0a3ffbf987800000

def z429 : W := mkw 0x42002580002a0000 0x242002580002a000 0x0100068000730000 0x0010006800073000

def z430 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x49c5066784f0b0c1 0x249c5066784f0b0c

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0x03fbc18003cf0003 0xf03fbc18003cf000

def z432 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0xffffbffffd007300 0x4ffffbffffd00730

def z433 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5d0606678470f0c4 0x45d0606678470f0c

def z434 : W := mkw 0x868935d8d841415d 0x3868935d8d841415 0xf77ab999f94343ff 0xdf77ab999f94343f

def z435 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x2fffff9007ff8c0f 0xf2fffff9007ff8c0

def z436 : W := mkw 0x044908008f414153 0x0044908008f41415 0xf77fb8899f4343ff 0xff77fb8899f4343f

def z437 : W := mkw 0x0802000020040420 0x8080200002004042 0xa000001060000c38 0x0a000001060000c3

def z438 : W := mkw 0x40400800072a0002 0x040400800072a000 0x00004000030f0002 0x800004000030f000

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x0891011660000000 0x0089101166000000

def z440 : W := mkw 0x150d022588515151 0x0150d02258851515 0x112606e99d737300 0x4112606e99d73730

def z441 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9811660008cfc 0x0eed9811660008cf

def z442 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0xffffbffffe00bc00 0x2ffffbffffe00bc0

def z443 : W := mkw 0x01601a7d07002a0a 0x101601a7d07002a0 0x7dffbe7f8700ff0c 0xf7dffbe7f8700ff0

def z444 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfed9c177e28cfcff 0xbfed9c177e28cfcf

def z445 : W := mkw 0xb39c37ffd0d0d0cd 0x3b39c37ffd0d0d0c 0xffffbffff800f0c4 0x0ffffbffff800f0c

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0xa228008818000000 0x0a22800881800000

def z447 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfdc7866f9cf0f3fd 0x7fdc7866f9cf0f3f

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x02d9810000000000 0x002d981000000000

def z449 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xf76ac0899bcfcfff 0xff76ac0899bcfcff

def z450 : W := mkw 0x444908008f6b4153 0x0444908008f6b415 0xf76ac0899fff43ff 0xff76ac0899fff43f

def z451 : W := mkw 0x116c1a7d87507a4b 0x1116c1a7d87507a4 0x11263e6985707300 0x411263e698570730

def z452 : W := mkw 0x0100022500000000 0x0010002250000000 0x41c0060780000000 0x041c006078000000

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x036a808000000000 0x0036a80800000000

def z454 : W := mkw 0x705c080287fad0c3 0x0705c080287fad0c 0x0000400007fff0c7 0xf0000400007fff0c

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x0340008000430003 0x0034000800043000

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x0228008001030002 0x8022800800103000

def z457 : W := mkw 0x0008000080404041 0x0000800008040404 0x756a8009814043cd 0xd756a8009814043c

def z458 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xff6a80ef9943f3ff 0xdff6a80ef9943f3f

def z459 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c1980780200ff0c 0xb3c1980780200ff0

def z460 : W := mkw 0x2832105a2084aea8 0x92832105a2084aea 0xfed9c17e628cffff 0xbfed9c17e628cfff

def z461 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x00043e6000000000 0x000043e600000000

def z462 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5dc7866784707000 0x45dc786678470700

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x1402800000004004 0x5140280000000400

def z464 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0xeef9f91e638c8fff 0xbeef9f91e638c8ff

def z465 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0x11263ee99d007300 0x411263ee99d00730

def z466 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff80030f0002 0x803ffff80030f000

def z467 : W := mkw 0xc38027a5502a0004 0x2c38027a5502a000 0xc3c04787f8ff0003 0x0c3c04787f8ff000

def z468 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xfed9c11ffa8ccfff 0xbfed9c11ffa8ccff

def z469 : W := mkw 0x0409000088414151 0x0040900008841415 0x352a80899943430c 0xd352a80899943430

def z470 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfc00006f9800f3fc 0x0fc00006f9800f3f

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x080500600400b000 0x2080500600400b00

def z472 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a808999434300 0x4f76a80899943430

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000000ff 0x900000000000000f

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x1122008998000000 0x0112200899800000

def z475 : W := mkw 0x534c2fa5877a5043 0x2534c2fa5877a504 0x13ffffe187ff7003 0xf13ffffe187ff700

def z476 : W := mkw 0x40400800072a0002 0x040400800072a000 0x01c7c60007ff0003 0xf01c7c60007ff000

def z477 : W := mkw 0x0401000008010110 0x0040100000801011 0x8200008018030032 0x0820000801803003

def z478 : W := mkw 0x0409000088414151 0x0040900008841415 0x00000000004300f3 0x000000000004300f

def z479 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc0066780f0f0c5 0x05dc0066780f0f0c

def z480 : W := mkw 0x2010000200808080 0x0201000020080808 0x4dc7860604f080c5 0x74dc7860604f080c

def z481 : W := mkw 0xc2c03dd8572a000e 0x3c2c03dd8572a000 0xa3ffff987fff0003 0xfa3ffff987fff000

def z482 : W := mkw 0x0040080007000002 0x0004008000700000 0x037fb88007430003 0xf037fb8800743000

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0x0142800000400001 0x5014280000040000

def z484 : W := mkw 0x31741a7f0790ba8a 0x131741a7f0790ba8 0x3cbfbe7e07b0ff0c 0xf3cbfbe7e07b0ff0

def z485 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000600000f004 0x01c0000600000f00

def z486 : W := mkw 0x828035d85000000c 0x3828035d85000000 0x0010391060000000 0x0001039106000000

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0xf66a8008010043ff 0xdf66a8008010043f

def z488 : W := mkw 0x2010000200808080 0x0201000020080808 0xeed98116608080c5 0x3eed98116608080c

def z489 : W := mkw 0x28120002208484a0 0x828120002208484a 0xc0000006600000f0 0x0c0000006600000f

def z490 : W := mkw 0x0008000080404041 0x0000800008040404 0x54000001800040c4 0x054000001800040c

def z491 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xefffff9667ff0003 0xfefffff9667ff000

def z492 : W := mkw 0x82e03dd857002a0e 0x382e03dd857002a0 0xbe3fb9f87f00ff0c 0xfbe3fb9f87f00ff0

def z493 : W := mkw 0x28120002208484a0 0x828120002208484a 0x02d9c100028c8cff 0xb02d9c100028c8cf

def z494 : W := mkw 0x0429105888416b59 0x10429105888416b5 0xff6a80f99943ffff 0xdff6a80f99943fff

def z495 : W := mkw 0x878137fd5801011c 0x3878137fd5801011 0xffffbffff903033a 0x8ffffbffff903033

def z496 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c0000780700ff0c 0xf3c0000780700ff0

def z497 : W := mkw 0x02402d8007000002 0x202402d800700000 0x03ffbf8007000000 0xf03ffbf800700000

def z498 : W := mkw 0x40400800072a0002 0x040400800072a000 0x0000400006bc0000 0x20000400006bc000

def z499 : W := mkw 0x0100022500000000 0x0010002250000000 0x5dc7866784f00001 0x75dc7866784f0000

def z500 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xf7ea868f99f343ff 0xdf7ea868f99f343f

def z501 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0x0800007660000000 0x0080000766000000

def z502 : W := mkw 0x381e0002a0d4d4e1 0x8381e0002a0d4d4e 0xeed9c11666fcfcff 0xfeed9c11666fcfcf

def z503 : W := mkw 0x6852080227ae84a2 0x86852080227ae84a 0xeed9c11667ff8cff 0xfeed9c11667ff8cf

def z504 : W := mkw 0x0020000000002a00 0x00020000000002a0 0x000000000000ff0c 0x0000000000000ff0

def z505 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03d9c78002ff0003 0xb03d9c78002ff000

def z506 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeec04116608c8cff 0x0eec04116608c8cf

def z507 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0x13ffff899fff4303 0xf13ffff899fff430

def z508 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe648c000028c8cff 0xbe648c000028c8cf

def z509 : W := mkw 0x0008000080404041 0x0000800008040404 0x41400001804000c1 0x041400001804000c

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76a80899900430c 0xdf76a80899900430

def z511 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec004016628c8cff 0xbec004016628c8cf

def z512 : W := mkw 0x878927a5d8414155 0x2878927a5d841415 0xc3c00787f84300f3 0x0c3c00787f84300f

def z513 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffdf8777e4f0f0c5 0x7ffdf8777e4f0f0c

def z514 : W := mkw 0xb39c37ffd0d0d0cd 0x3b39c37ffd0d0d0c 0x5de7beef9cf0f0c5 0x75de7beef9cf0f0c

def z515 : W := mkw 0x0040080007000002 0x0004008000700000 0x1c3fb8600700f004 0xf1c3fb8600700f00

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c2f80680500f30c 0xf3c2f80680500f30

def z517 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c85066784b0f0c4 0x25c85066784b0f0c

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0xa218011060000000 0x0a21801106000000

def z519 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3838780300ff0c 0x83c3838780300ff0

def z520 : W := mkw 0x030027a500000000 0x2030027a50000000 0x5fffbfe780000000 0x05fffbfe78000000

def z521 : W := mkw 0x0409000088414151 0x0040900008841415 0x0000000001434300 0x4000000000143430

def z522 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x01c7860004f0f0c5 0x701c7860004f0f0c

def z523 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x22387998030f0f0a 0x822387998030f0f0

def z524 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8006bc0000 0x203ffff8006bc000

def z525 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0xffffbffffd730000 0x4ffffbffffd73000

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0xf400000998000000 0x0f40000099800000

def z527 : W := mkw 0xc2c03dd8572a000e 0x3c2c03dd8572a000 0xa23879987b0f0002 0x8a23879987b0f000

def z528 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x003fb8000700ff0c 0xf003fb8000700ff0

def z529 : W := mkw 0x2018000280c0c0c1 0x02018000280c0c0c 0x5dc3800780c0c0c5 0x75dc3800780c0c0c

def z530 : W := mkw 0x3114022700909080 0x0311402270090908 0x0080060600b00000 0x00080060600b0000

def z531 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfe7fb8780700ffff 0xffe7fb8780700fff

def z532 : W := mkw 0x2010000200808080 0x0201000020080808 0xeec98006008080ff 0xbeec98006008080f

def z533 : W := mkw 0x2010000200808080 0x0201000020080808 0x4c000006000080c4 0x04c000006000080c

def z534 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x000000000000f0c4 0x0000000000000f0c

def z535 : W := mkw 0x0000105800000008 0x1000010580000000 0x3c00007800000000 0x03c0000780000000

def z536 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0xfffffffffa8c8c00 0x2fffffffffa8c8c0

def z537 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x3cbfbf7e60000000 0x03cbfbf7e6000000

def z538 : W := mkw 0x2010000200808080 0x0201000020080808 0x40c00006008000c1 0x040c00006008000c

def z539 : W := mkw 0x0c03000028050530 0x80c0300002805053 0xa23841987b0f0f3a 0x8a23841987b0f0f3

def z540 : W := mkw 0x735c2fa787fad0c3 0x2735c2fa787fad0c 0x5de7bee785f3f0c5 0x75de7bee785f3f0c

def z541 : W := mkw 0x0008000080404041 0x0000800008040404 0xf76a8089984040c5 0x5f76a8089984040c

def z542 : W := mkw 0x0409000088414151 0x0040900008841415 0x0100008198430000 0x0010000819843000

def z543 : W := mkw 0x281a0002a0c4c4e1 0x8281a0002a0c4c4e 0xffdbc117e2ccccff 0xfffdbc117e2ccccf

def z544 : W := mkw 0x0200258000000000 0x2020025800000000 0x03ffff80028c0003 0xb03ffff80028c000

def z545 : W := mkw 0xb19c127fd0d0d0cd 0x1b19c127fd0d0d0c 0xfdc7867ffcf0f0c5 0x7fdc7867ffcf0f0c

def z546 : W := mkw 0x735c2fa787fad0c3 0x2735c2fa787fad0c 0x43ffff8787ff00c3 0xf43ffff8787ff00c

def z547 : W := mkw 0x28120002208484a0 0x828120002208484a 0x0800001660008c00 0x00800001660008c0

def z548 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xaabd3ffe78000000 0x0aabd3ffe7800000

def z549 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0x3cbfbf7e6700ff0c 0xf3cbfbf7e6700ff0

def z550 : W := mkw 0x0409000088414151 0x0040900008841415 0xa2280088194343ff 0xda2280088194343f

def z551 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xefd9c197facf8cff 0xbefd9c197facf8cf

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x0007800004000000 0x7000780000400000

def z553 : W := mkw 0x0008000080404041 0x0000800008040404 0x55c7860184f040c5 0x755c7860184f040c

def z554 : W := mkw 0x0008000080404041 0x0000800008040404 0x576a8081814340c7 0xd576a8081814340c

def z555 : W := mkw 0x534c2fa5877a5043 0x2534c2fa5877a504 0x11263ee185737000 0x411263ee18573700

def z556 : W := mkw 0x4a422d80272e0422 0xa4a422d80272e042 0xa2387990630f0c3a 0x8a2387990630f0c3

def z557 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x2000001800000f08 0x02000001800000f0

def z558 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xc3c04187f8cf00f3 0x0c3c04187f8cf00f

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000004f00001 0x70000000004f0000

def z560 : W := mkw 0x0100127d00000008 0x10100127d0000000 0x7dffbe7f80000000 0x07dffbe7f8000000

def z561 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0x112638e99d437300 0x4112638e99d43730

def z562 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xdfc7c767e4fcf0f7 0x7dfc7c767e4fcf0f

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x2ed9c110028c8c0f 0xb2ed9c110028c8c0

def z564 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0x11263ee99d730000 0x411263ee99d73000

def z565 : W := mkw 0x0409000088414151 0x0040900008841415 0xff6f80e99d43f3ff 0xfff6f80e99d43f3f

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c0060000f00001 0x001c0060000f0000

def z567 : W := mkw 0x0802000020040420 0x8080200002004042 0xeed9c116620c0c3a 0x8eed9c116620c0c3

def z568 : W := mkw 0x0409000088414151 0x0040900008841415 0xc36a8081994300f3 0xdc36a8081994300f

def z569 : W := mkw 0x0401000008010110 0x0040100000801011 0xa36a80881943033b 0xda36a80881943033

def z570 : W := mkw 0x0429105888416b59 0x10429105888416b5 0xfc0000799800fffc 0x0fc0000799800fff

def z571 : W := mkw 0x287208022784aea2 0x8287208022784aea 0x00004000078cffff 0xf00004000078cfff

def z572 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0xfffffffff88c00f3 0x0fffffffff88c00f

def z573 : W := mkw 0x0409105888414159 0x1040910588841415 0xff7fb8f9994343ff 0xdff7fb8f9994343f

def z574 : W := mkw 0x397e1a7fa7d4feeb 0x9397e1a7fa7d4fee 0xffffff7fe7fcffff 0xfffffff7fe7fcfff

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x03dfc70006fc0003 0xf03dfc70006fc000

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x003fb80000000000 0x0003fb8000000000

def z577 : W := mkw 0x40600800072a2a02 0x040600800072a2a0 0x0000400007ffff0f 0xf0000400007ffff0

def z578 : W := mkw 0xb3fc3fffd7d0facf 0x3b3fc3fffd7d0fac 0xffffbffffff0ffcd 0xfffffbffffff0ffc

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x44408000000000c5 0x144408000000000c

def z580 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0x11263e899d734300 0x411263e899d73430

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0xe4000000000000fc 0x0e4000000000000f

def z582 : W := mkw 0x0200258000000000 0x2020025800000000 0x03ffbf8001430003 0xd03ffbf800143000

def z583 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x203fb81807000f08 0xf203fb81807000f0

def z584 : W := mkw 0x0409000088414151 0x0040900008841415 0xf4000009994343ff 0xdf4000009994343f

def z585 : W := mkw 0x0409000088414151 0x0040900008841415 0x036a8080014343ff 0xd036a8080014343f

def z586 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x0020380801000300 0x0002038080100030

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x02184100020c0002 0x802184100020c000

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0xf76a808999430003 0xdf76a80899943000

def z589 : W := mkw 0x0100022500000000 0x0010002250000000 0x5dc786678400f004 0x75dc786678400f00

def z590 : W := mkw 0xb19c127fd0d0d0cd 0x1b19c127fd0d0d0c 0xfc00007ff800f0c4 0x0fc00007ff800f0c

def z591 : W := mkw 0x341d000288d1d1d1 0x0341d000288d1d1d 0xf76a80899df3f3ff 0xff76a80899df3f3f

def z592 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0x3c3ff878078cffff 0xf3c3ff878078cfff

def z593 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089984300f3 0x0f76a8089984300f

def z594 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x283d38780700bf08 0xa283d38780700bf0

def z595 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xff7fb8f99f00ff0c 0xfff7fb8f99f00ff0

def z596 : W := mkw 0x311c127f80d0d0c9 0x1311c127f80d0d0c 0x7dffbe7f84f0f0c5 0x77dffbe7f84f0f0c

def z597 : W := mkw 0x0401000008010110 0x0040100000801011 0x0020008819030300 0x0002000881903030

def z598 : W := mkw 0x0409000088414151 0x0040900008841415 0x136a808999434303 0xd136a80899943430

def z599 : W := mkw 0x0409000088414151 0x0040900008841415 0xe7488081984300ff 0x9e7488081984300f

def z600 : W := mkw 0x0040080007000002 0x0004008000700000 0x0026380005000000 0x4002638000500000

def z601 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0xeed9c11663cfcfff 0xfeed9c11663cfcff

def z602 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x0238798007ff0003 0xf0238798007ff000

def z603 : W := mkw 0xaa9235da708484ac 0xbaa9235da708484a 0xeef9f99e7a8c8cff 0xbeef9f99e7a8c8cf

def z604 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7400089984343ff 0x0f7400089984343f

def z605 : W := mkw 0x42403dd8072a000a 0x342403dd8072a000 0x3ffffff807ff0003 0xf3ffffff807ff000

def z606 : W := mkw 0x0008000080404041 0x0000800008040404 0x00000000004040c5 0x500000000004040c

def z607 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5de786ef9df3f3c5 0x75de786ef9df3f3c

def z608 : W := mkw 0x0409000088414151 0x0040900008841415 0x55428001814343ff 0xd55428001814343f

def z609 : W := mkw 0x29120227208484a0 0x829120227208484a 0xffdfc777e28c8cff 0xbffdfc777e28c8cf

def z610 : W := mkw 0x737c3fff87fafacb 0x3737c3fff87fafac 0x7fffffff87ffffcf 0xf7fffffff87ffffc

def z611 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3c3ff87807ffff0f 0xf3c3ff87807ffff0

def z612 : W := mkw 0x8589127dd841415d 0x18589127dd841415 0xff6a80fff94343ff 0xdff6a80fff94343f

def z613 : W := mkw 0x715c0a2787fad0c3 0x0715c0a2787fad0c 0x5dc7c66787fff0c7 0xf5dc7c66787fff0c

def z614 : W := mkw 0x28120002208484a0 0x828120002208484a 0x2c99c116628c8c0c 0xb2c99c116628c8c0

def z615 : W := mkw 0x317c1a7f87d0facb 0x1317c1a7f87d0fac 0x5de7be6f85f0f3c5 0x75de7be6f85f0f3c

def z616 : W := mkw 0x0108022580404041 0x0010802258040404 0x5dc78667804040c5 0x55dc78667804040c

def z617 : W := mkw 0x8b8237fd7004042c 0xb8b8237fd7004042 0xfffffffffa0c0c3a 0x8fffffffffa0c0c3

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0xe76a8080014300ff 0xde76a8080014300f

def z619 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03eac78001ff0003 0xd03eac78001ff000

def z620 : W := mkw 0x0000105800000008 0x1000010580000000 0xfeffb97e60000000 0x0feffb97e6000000

def z621 : W := mkw 0x775d2fa78ffbd1d3 0x2775d2fa78ffbd1d 0xffffffef9ffff3ff 0xfffffffef9ffff3f

def z622 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0x3d3fbef99f00ff0c 0xf3d3fbef99f00ff0

def z623 : W := mkw 0xc3e03ffd572a2a0e 0x3c3e03ffd572a2a0 0xffffffffffffff0f 0xfffffffffffffff0

def z624 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116608c00f3 0x0eed9c116608c00f

def z625 : W := mkw 0x731c27a780fad0c1 0x2731c27a780fad0c 0x43c0478780ff00c3 0x043c0478780ff00c

def z626 : W := mkw 0x2a122582208484a0 0xa2a122582208484a 0xefffff96628c8cff 0xbefffff96628c8cf

def z627 : W := mkw 0x357d1a7f8fd1fbdb 0x1357d1a7f8fd1fbd 0xffffbeff9ff3ffff 0xfffffbeff9ff3fff

def z628 : W := mkw 0x0200258000000000 0x2020025800000000 0x03ffbf8004f00001 0x703ffbf8004f0000

def z629 : W := mkw 0x73542fa707ba9082 0x273542fa707ba908 0x08957f6606bcb000 0x208957f6606bcb00

def z630 : W := mkw 0xb39437ff5090908c 0x3b39437ff5090908 0x08953f7664b0b000 0x208953f7664b0b00

def z631 : W := mkw 0xc3c03ffd572a000e 0x3c3c03ffd572a000 0x08957f7666bc0000 0x208957f7666bc000

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x002a800001000000 0xd002a80000100000

def z633 : W := mkw 0x0008000080404041 0x0000800008040404 0x5d4780618440f0c5 0x75d4780618440f0c

def z634 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefdfc71666fc8cff 0xfefdfc71666fc8cf

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001430003 0xd000000000143000

def z636 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0x3c3fb8780743ffff 0xf3c3fb8780743fff

def z637 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7ef86899df343ff 0xff7ef86899df343f

def z638 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x13ffffe807ff7303 0xf13ffffe807ff730

def z639 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x41c0060784f0f0c5 0x741c0060784f0f0c

def z640 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0x0000400003cfcfff 0xf0000400003cfcff

def z641 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0xeeddff1666bc8cff 0xbeeddff1666bc8cf

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed9811662008c0c 0xbeed9811662008c0

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c1800000800001 0x300c180000080000

def z644 : W := mkw 0x6852080227ae84a2 0x86852080227ae84a 0x0000400007ff8cff 0xf0000400007ff8cf

def z645 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0x3cbff97e678cff0c 0xf3cbff97e678cff0

def z646 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x342eb8680500730c 0xd342eb8680500730

def z647 : W := mkw 0x2c7b185aafc5effb 0x92c7b185aafc5eff 0xfffff9ffffcfffff 0xffffff9ffffcffff

def z648 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x3e3ff9f8070fff0e 0xf3e3ff9f8070fff0

def z649 : W := mkw 0x87e93ffddf416b5f 0x387e93ffddf416b5 0xffffbfffff43ffff 0xfffffbfffff43fff

def z650 : W := mkw 0x28120002208484a0 0x828120002208484a 0xaa994116628c8c3a 0xaaa994116628c8c3

def z651 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x5dd7bf77e0000000 0x05dd7bf77e000000

def z652 : W := mkw 0x838027a550000004 0x2838027a55000000 0xdfc787e7f8000000 0x0dfc787e7f800000

def z653 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0x03ffff8007ff43ff 0xf03ffff8007ff43f

def z654 : W := mkw 0x0c0b0000a8454571 0x80c0b0000a845457 0xf77ac199fb4f4fff 0xdf77ac199fb4f4ff

def z655 : W := mkw 0x046908008f416b53 0x0046908008f416b5 0x000000000743ffff 0xf000000000743fff

def z656 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116628c8c00 0x2eed9c116628c8c0

def z657 : W := mkw 0xf3dc3fffd7fad0cf 0x3f3dc3fffd7fad0c 0xfffffffffffff0c7 0xffffffffffffff0c

def z658 : W := mkw 0x83e03ffd57002a0e 0x383e03ffd57002a0 0xffffbffffb000f08 0x8ffffbffffb000f0

def z659 : W := mkw 0x28120002208484a0 0x828120002208484a 0xee48801660008cff 0x9ee48801660008cf

def z660 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0xfc3fb87e6700fffc 0xffc3fb87e6700fff

def z661 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x1c17b8700600fc04 0x71c17b8700600fc0

def z662 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed9c116628c0003 0xbeed9c116628c000

def z663 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c0780780400ff0c 0x73c0780780400ff0

def z664 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2400000000000f3 0x0c2400000000000f

def z665 : W := mkw 0x6a12258220ae84a0 0xa6a12258220ae84a 0xefd9c79662ff8cff 0xbefd9c79662ff8cf

def z666 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x13ffbfe998000000 0x013ffbfe99800000

def z667 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x4dc1860780f080c5 0x34dc1860780f080c

def z668 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x0000000005007300 0x4000000000500730

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x0122008001430000 0x4012200800143000

def z670 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x103fb86807007300 0xf103fb8680700730

def z671 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0xf76eb8e99d4373ff 0xdf76eb8e99d4373f

def z672 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x1c0780600700ff0c 0xf1c0780600700ff0

def z673 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x083fb8700700bc00 0xf083fb8700700bc0

def z674 : W := mkw 0x046118580f012b1a 0x1046118580f012b1 0xbe3fb8f81f03ff3e 0xfbe3fb8f81f03ff3

def z675 : W := mkw 0xa992127f708484ac 0x9a992127f708484a 0xfc00007ff8008cfc 0x0fc00007ff8008cf

def z676 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x033e7f80077f0002 0xc033e7f80077f000

def z677 : W := mkw 0x2419000288c1c1d1 0x02419000288c1c1d 0xffeb808f99c3c3ff 0xfffeb808f99c3c3f

def z678 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x0004386004003000 0x0000438600400300

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0xc340008198000000 0x0c34000819800000

def z680 : W := mkw 0xab9227a7708484a4 0xaab9227a7708484a 0xc3c04787f88c00f3 0x0c3c04787f88c00f

def z681 : W := mkw 0xb39c27a7d0d0d0c5 0x2b39c27a7d0d0d0c 0xdfc787e7fcf0f0c5 0x7dfc787e7fcf0f0c

def z682 : W := mkw 0x838027a550000004 0x2838027a55000000 0x0080070660000000 0x0008007066000000

def z683 : W := mkw 0x0409000088414151 0x0040900008841415 0xb32a00899943433a 0xcb32a00899943433

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x1022000801004300 0x4102200080100430

def z685 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x0000000003000f08 0x80000000003000f0

def z686 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x036ebe8005730003 0xd036ebe800573000

def z687 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x1c27b8680500f304 0x71c27b8680500f30

def z688 : W := mkw 0x938c37fdd050504d 0x3938c37fdd050504 0x11263ee99c707000 0x411263ee99c70700

def z689 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0xf77af9899b4f43ff 0xdf77af9899b4f43f

def z690 : W := mkw 0x0100022500000000 0x0010002250000000 0x5c00006780000000 0x05c0000678000000

def z691 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0xffffbffff8008cfc 0x0ffffbffff8008cf

def z692 : W := mkw 0x28120002208484a0 0x828120002208484a 0xc2c04106628c8cff 0xbc2c04106628c8cf

def z693 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03c0478007ff0003 0xf03c0478007ff000

def z694 : W := mkw 0x0000105800000008 0x1000010580000000 0x1026386800000000 0x0102638680000000

def z695 : W := mkw 0x878927a5d8414155 0x2878927a5d841415 0xf7ea878ff94343ff 0xdf7ea878ff94343f

def z696 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01d7ff0006fc0001 0x701d7ff0006fc000

def z697 : W := mkw 0x725c2d8287fad0c3 0x2725c2d8287fad0c 0x03ffff8007fff0c7 0xf03ffff8007fff0c

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000100430c 0xd000000000100430

def z699 : W := mkw 0x0409000088414151 0x0040900008841415 0xc3400081994343ff 0xdc3400081994343f

def z700 : W := mkw 0x28120002208484a0 0x828120002208484a 0x0000000000008cfc 0x00000000000008cf

def z701 : W := mkw 0x0509022588414151 0x0050902258841415 0xffef86ef994343ff 0xdffef86ef994343f

def z702 : W := mkw 0x0000000000000000 0x0000000000000000 0x240880000000000c 0x9240880000000000

def z703 : W := mkw 0x0409000088414151 0x0040900008841415 0xf42a8009990043fc 0xdf42a8009990043f

def z704 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00bfff0007bc0000 0xf00bfff0007bc000

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c07806000000000 0x01c0780600000000

def z706 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5d4280678040f0c5 0x55d4280678040f0c

def z707 : W := mkw 0x110c022580505041 0x0110c02258050504 0x110606618470f004 0x7110606618470f00

def z708 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866784b0f0c4 0x25dc7866784b0f0c

def z709 : W := mkw 0x0409000088414151 0x0040900008841415 0xe3680089994343ff 0xde3680089994343f

def z710 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xc3d03f97f8000000 0x0c3d03f97f800000

def z711 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03fd7f8007ff0003 0xa03fd7f8007ff000

def z712 : W := mkw 0x0000000000000000 0x0000000000000000 0x3fdfc77006fcfc0f 0xf3fdfc77006fcfc0

def z713 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xc3c43fe7f8000000 0x0c3c43fe7f800000

def z714 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xff7fb8f80743ffff 0xfff7fb8f80743fff

def z715 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x103fb8680700ff0c 0xf103fb8680700ff0

def z716 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xcbc506e79cf3b0f3 0x2cbc506e79cf3b0f

def z717 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc6066784f0f0c5 0x45dc6066784f0f0c

def z718 : W := mkw 0x39160227209494a0 0x839160227209494a 0x0885466606bcbcff 0xb0885466606bcbcf

def z719 : W := mkw 0x838027a550000004 0x2838027a55000000 0xc3d53f87f8000000 0x0c3d53f87f800000

def z720 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec104116620c8cfc 0x0ec104116620c8cf

def z721 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfc10397ff8000000 0x0fc10397ff800000

def z722 : W := mkw 0x38160002209494a0 0x838160002209494a 0xeed9c11666bcbcff 0xbeed9c11666bcbcf

def z723 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089994343fc 0x4f76a8089994343f

def z724 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc0066784f0f0c5 0x75dc0066784f0f0c

def z725 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffd00f30c 0xfffffbffffd00f30

def z726 : W := mkw 0x6a522d8227ae84a2 0xa6a522d8227ae84a 0xed263e9665738cfc 0x4ed263e9665738cf

def z727 : W := mkw 0x878937fdd841415d 0x3878937fdd841415 0x08953f76614343ff 0xd08953f76614343f

def z728 : W := mkw 0x0409000088414151 0x0040900008841415 0xff7b8099994343ff 0xdff7b8099994343f

def z729 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffefc6ef9fffffff 0xfffefc6ef9ffffff

def z730 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1506866184707004 0x5150686618470700

def z731 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x7def866f85f3f3ff 0xf7def866f85f3f3f

def z732 : W := mkw 0x83e02fa557002a06 0x283e02fa557002a0 0xc3c00787ff00ff0c 0xfc3c00787ff00ff0

def z733 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x7d7fb8798700ff0c 0xf7d7fb8798700ff0

def z734 : W := mkw 0x46492d808f6b4153 0x246492d808f6b415 0xf4957f099ebc43fc 0x2f4957f099ebc43f

def z735 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfc3fb87e6700ff0c 0xffc3fb87e6700ff0

def z736 : W := mkw 0x28120002208484a0 0x828120002208484a 0xffdfc77666fcfcff 0xfffdfc77666fcfcf

def z737 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfc2038fff8000000 0x0fc2038fff800000

def z738 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc786678470f0c4 0x45dc786678470f0c

def z739 : W := mkw 0x735c2fa787fad0c3 0x2735c2fa787fad0c 0x5e3879e7830ff0c6 0x85e3879e7830ff0c

def z740 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3fffbef807f3ff0f 0xf3fffbef807f3ff0

def z741 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c1038780200ff0c 0x03c1038780200ff0

def z742 : W := mkw 0x3114022700909080 0x0311402270090908 0x080406660430b000 0x0080406660430b00

def z743 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffa000000 0xbffffbffffa00000

def z744 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xc8953f77f8000000 0x0c8953f77f800000

def z745 : W := mkw 0x301c000280d0d0c1 0x0301c000280d0d0c 0x1dc7866004f0f0c5 0x71dc7866004f0f0c

def z746 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03d07f8002ff0003 0x003d07f8002ff000

def z747 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x37ffff8807ff0003 0xf37ffff8807ff000

def z748 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3e7fb8780700ff0f 0xf3e7fb8780700ff0

def z749 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x3ffffff007fffc0f 0xf3ffffff007fffc0

def z750 : W := mkw 0x3114022700909080 0x0311402270090908 0x0084066604b03000 0x00084066604b0300

def z751 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xd3c64767e4fc70f3 0x4d3c64767e4fc70f

def z752 : W := mkw 0x828035d85000000c 0x3828035d85000000 0xfffbb99ff8000000 0x0fffbb99ff800000

def z753 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfeffb97e6700ffff 0xffeffb97e6700fff

def z754 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffc00b000 0x2ffffbffffc00b00

def z755 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3ab8780300ff0c 0xd3c3ab8780300ff0

def z756 : W := mkw 0x150d022588515151 0x0150d02258851515 0xffef86ef9d7373ff 0xdffef86ef9d7373f

def z757 : W := mkw 0x046918588f416b5b 0x1046918588f416b5 0xcb5538f19e43bcf3 0x2cb5538f19e43bcf

def z758 : W := mkw 0x110c022580505041 0x0110c02258050504 0x55c7866184f070c5 0x755c7866184f070c

def z759 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3fffff7807fcff0f 0xf3fffff7807fcff0

def z760 : W := mkw 0x0409000088414151 0x0040900008841415 0xff6a80e99943f3ff 0xdff6a80e99943f3f

def z761 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01bfff8007ff0000 0xf01bfff8007ff000

def z762 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x13ffffe007ff7003 0xf13ffffe007ff700

def z763 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7ffc7899fff43ff 0xff7ffc7899fff43f

def z764 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03ffff8001ff0003 0xd03ffff8001ff000

def z765 : W := mkw 0x3114022700909080 0x0311402270090908 0x0bef86e605f3b003 0xf0bef86e605f3b00

def z766 : W := mkw 0x3114022700909080 0x0311402270090908 0x09c7866604b0b000 0x209c7866604b0b00

def z767 : W := mkw 0x39160227209494a0 0x839160227209494a 0xcac5476664bcb0f3 0x2cac5476664bcb0f

def z768 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfef9b9fff8000000 0x0fef9b9fff800000

def z769 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5dc786678470f004 0x75dc786678470f00

def z770 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xbe3fb9786700ff0c 0xfbe3fb9786700ff0

def z771 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116620c8cfe 0x8eed9c116620c8cf

def z772 : W := mkw 0x3114022700909080 0x0311402270090908 0x0c85866604b0b004 0x30c85866604b0b00

def z773 : W := mkw 0x0409000088414151 0x0040900008841415 0xffef86e99df3f3ff 0xfffef86e99df3f3f

def z774 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c17b8780600ff0c 0x73c17b8780600ff0

def z775 : W := mkw 0x190e0225a0545461 0x8190e0225a054546 0xb31e4771e67c7c3a 0xcb31e4771e67c7c3

def z776 : W := mkw 0x3114022700909080 0x0311402270090908 0x0004066004b0b000 0x20004066004b0b00

def z777 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffa000c08 0x8ffffbffffa000c0

def z778 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffef86ef9cf0f0ff 0xfffef86ef9cf0f0f

def z779 : W := mkw 0xc1c01a7d572a000e 0x1c1c01a7d572a000 0xfc00407fffff0003 0xffc00407fffff000

def z780 : W := mkw 0x40400800072a0002 0x040400800072a000 0x01fffe0007ff0003 0xf01fffe0007ff000

def z781 : W := mkw 0x110c022580505041 0x0110c02258050504 0x136e86e185737003 0xd136e86e18573700

def z782 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03d57f8007ff0003 0xf03d57f8007ff000

def z783 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x183738780700ff0c 0xf183738780700ff0

def z784 : W := mkw 0x28120002208484a0 0x828120002208484a 0x2c99c116628c8cff 0xb2c99c116628c8cf

def z785 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff90043ff 0xdffffbffff90043f

def z786 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5546866184707000 0x4554686618470700

def z787 : W := mkw 0x3114022700909080 0x0311402270090908 0x0987066604f0b000 0x60987066604f0b00

def z788 : W := mkw 0x39160227209494a0 0x839160227209494a 0xffdfc777e6bcbc00 0x2ffdfc777e6bcbc0

def z789 : W := mkw 0x0409000088414151 0x0040900008841415 0xff6a809ff94343ff 0xdff6a809ff94343f

def z790 : W := mkw 0x838027a550000004 0x2838027a55000000 0xc3e63f87f8000000 0x0c3e63f87f800000

def z791 : W := mkw 0x3114022700909080 0x0311402270090908 0x1c87866604b0b000 0x21c87866604b0b00

def z792 : W := mkw 0x0401000008010110 0x0040100000801011 0xf76a8089990303ff 0x9f76a8089990303f

def z793 : W := mkw 0x110c022580505041 0x0110c02258050504 0x3d1f86718670fc0c 0xf3d1f86718670fc0

def z794 : W := mkw 0x150d022588515151 0x0150d02258851515 0x110606e19c737000 0x4110606e19c73700

def z795 : W := mkw 0x317c1a7f87d0facb 0x1317c1a7f87d0fac 0x61f83e1f83f00fc9 0x861f83e1f83f00fc

def z796 : W := mkw 0x0000105800000008 0x1000010580000000 0xffffb9fff8000000 0x0ffffb9fff800000

def z797 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8000003 0x9ffffbffff800000

def z798 : W := mkw 0x110c022580505041 0x0110c02258050504 0x13dfc76186fc7003 0xf13dfc76186fc700

def z799 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c0406678430f0c4 0x05c0406678430f0c

def z800 : W := mkw 0x3515022708919190 0x0351502270891919 0xaaad06ee1db3b33a 0xaaaad06ee1db3b33

def z801 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dd7867786f0fcc5 0x75dd7867786f0fcc

def z802 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3d3fbe780770ff0c 0xf3d3fbe780770ff0

def z803 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb87807f0ff0d 0xf3c3fb87807f0ff0

def z804 : W := mkw 0xb29c35dad0d0d0cd 0x3b29c35dad0d0d0c 0xa23839987cf0f0c5 0x7a23839987cf0f0c

def z805 : W := mkw 0x0409000088414151 0x0040900008841415 0xe2280089990303fa 0x8e2280089990303f

def z806 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffcf0f005 0x7ffffbffffcf0f00

def z807 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x036efe8007ff0003 0xf036efe8007ff000

def z808 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffcf8677e4f0fcff 0xfffcf8677e4f0fcf

def z809 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3dffbe780700ff0c 0xf3dffbe780700ff0

def z810 : W := mkw 0x3114022700909080 0x0311402270090908 0x1c85066604b0f004 0x21c85066604b0f00

def z811 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x41c4066784f030c1 0x041c4066784f030c

def z812 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffcb00000 0x2ffffbffffcb0000

def z813 : W := mkw 0x0060080007002a02 0x00060080007002a0 0x1c3fb8600700ff0c 0xf1c3fb8600700ff0

def z814 : W := mkw 0x150d022588515151 0x0150d02258851515 0xf50606699c7073fc 0x4f50606699c7073f

def z815 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffc700000 0x4ffffbffffc70000

def z816 : W := mkw 0xc2e03dd8572a2a0e 0x3c2e03dd8572a2a0 0xa23879987b0f0f0a 0x8a23879987b0f0f0

def z817 : W := mkw 0x110c022580505041 0x0110c02258050504 0x51c6066784707000 0x451c606678470700

def z818 : W := mkw 0x3114022700909080 0x0311402270090908 0x1987066784b0b000 0x21987066784b0b00

def z819 : W := mkw 0x28120002208484a0 0x828120002208484a 0xc8914116628c8cf0 0x2c8914116628c8cf

def z820 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x383f38780700ff08 0xe383f38780700ff0

def z821 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1106066184f0f000 0x61106066184f0f00

def z822 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xff7fb8f99f00ffff 0xfff7fb8f99f00fff

def z823 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x55c6866784f070c5 0x555c6866784f070c

def z824 : W := mkw 0x150d022588515151 0x0150d02258851515 0xff6f86e99d73f3ff 0xfff6f86e99d73f3f

def z825 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5dc7866785f3f3c5 0x75dc7866785f3f3c

def z826 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffdf8777e4f0f0ff 0xfffdf8777e4f0f0f

def z827 : W := mkw 0x0409000088414151 0x0040900008841415 0xf6688089990343ff 0x9f6688089990343f

def z828 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c2638780000ff0c 0x03c2638780000ff0

def z829 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff800000c 0x9ffffbffff800000

def z830 : W := mkw 0x938437fd5010100c 0x3938437fd5010100 0xffffbffffc303000 0x0ffffbffffc30300

def z831 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffbcf0003 0xffffffffffbcf000

def z832 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03faff8003ff0003 0xd03faff8003ff000

def z833 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x02387988030f0302 0x802387988030f030

def z834 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffc007000 0x4ffffbffffc00700

def z835 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x0885066604b0f0c4 0x20885066604b0f0c

def z836 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffff87fffcf0f0c5 0x7ffff87fffcf0f0c

def z837 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfc3fb8799f00ff0c 0xffc3fb8799f00ff0

def z838 : W := mkw 0x0409000088414151 0x0040900008841415 0xf72a0089994343fe 0xcf72a0089994343f

def z839 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefdfc716628c8cff 0xbefdfc716628c8cf

def z840 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfdb73ffff8000000 0x0fdb73ffff800000

def z841 : W := mkw 0x0409000088414151 0x0040900008841415 0xff7f80f99f43ffff 0xfff7f80f99f43fff

def z842 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x2fffff9007ffff0f 0xf2fffff9007ffff0

def z843 : W := mkw 0x0000000000000000 0x0000000000000000 0x0885066004b0b000 0x20885066004b0b00

def z844 : W := mkw 0x110c022580505041 0x0110c02258050504 0xffdf8777e4707000 0x4ffdf8777e470700

def z845 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03f87f8007ff0003 0xf03f87f8007ff000

def z846 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a80899d43f3ff 0xff76a80899d43f3f

def z847 : W := mkw 0x3114022700909080 0x0311402270090908 0xffef86ef9cb0b000 0x2ffef86ef9cb0b00

def z848 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5d87066784f0f0c4 0x65d87066784f0f0c

def z849 : W := mkw 0x28120002208484a0 0x828120002208484a 0x4cd1c116628c8cff 0xb4cd1c116628c8cf

def z850 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfed9c11ffa8c8cff 0xbfed9c11ffa8c8cf

def z851 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00957f0007ff0000 0x600957f0007ff000

def z852 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfdef866f9df0f3fd 0xffdef866f9df0f3f

def z853 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x4fffff8607ff0003 0xf4fffff8607ff000

def z854 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xff3e3ffff8000000 0x0ff3e3ffff800000

def z855 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x303e38780700ff0c 0xf303e38780700ff0

def z856 : W := mkw 0x0000000000000000 0x0000000000000000 0x11c7866004f07001 0x711c7866004f0700

def z857 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x03ffff8007ff7303 0xf03ffff8007ff730

def z858 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffffc7ef9ffff3ff 0xfffffc7ef9ffff3f

def z859 : W := mkw 0x110c022580505041 0x0110c02258050504 0x112606e99c707000 0x4112606e99c70700

def z860 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8004004 0x5ffffbffff800400

def z861 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffc7c777e4fcfcff 0x7ffc7c777e4fcfcf

def z862 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffff86ff9ff3ffff 0xfffff86ff9ff3fff

def z863 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fc786e784f3f0c7 0x75fc786e784f3f0c

def z864 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3cbff978078cff0c 0xf3cbff978078cff0

def z865 : W := mkw 0x1104022500101000 0x0110402250010100 0x080506600430b000 0x2080506600430b00

def z866 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xdfc786e79cf0f0c5 0x7dfc786e79cf0f0c

def z867 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xf7ffff899fff430f 0xff7ffff899fff430

def z868 : W := mkw 0xab9237ff708484ac 0xbab9237ff708484a 0x11267ee99a8c8cff 0xb11267ee99a8c8cf

def z869 : W := mkw 0x0409000088414151 0x0040900008841415 0xff6b80899943c3ff 0xfff6b80899943c3f

def z870 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116668cfcff 0xfeed9c116668cfcf

def z871 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffa8c0000 0x2fffffffffa8c000

def z872 : W := mkw 0x28120002208484a0 0x828120002208484a 0xaa994116628c8cff 0xbaa994116628c8cf

def z873 : W := mkw 0x0409000088414151 0x0040900008841415 0xfffbc19ffbcf43ff 0xffffbc19ffbcf43f

def z874 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfe7fb8780700ff0c 0xffe7fb8780700ff0

def z875 : W := mkw 0x422035d8002a2a08 0x3422035d8002a2a0 0x3fc047f800ffff0f 0x03fc047f800ffff0

def z876 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffb00cf0c 0xfffffbffffb00cf0

def z877 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff943430f 0xdffffbffff943430

def z878 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffdf30003 0xfffffbffffdf3000

def z879 : W := mkw 0x28120002208484a0 0x828120002208484a 0xecd1c116628c8cfd 0x3ecd1c116628c8cf

def z880 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeec04116628c8cff 0xbeec04116628c8cf

def z881 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x000438600700ff0c 0xf000438600700ff0

def z882 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8006ff0003 0x203ffff8006ff000

def z883 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xd3e606ef9df373f3 0x4d3e606ef9df373f

def z884 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffdfc777e4fcf0f7 0x7ffdfc777e4fcf0f

def z885 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffdfc777e7ffffff 0xfffdfc777e7fffff

def z886 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x19c7866784f0f001 0x719c7866784f0f00

def z887 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff80000fc 0x0ffffbffff80000f

def z888 : W := mkw 0x3114022700909080 0x0311402270090908 0x08c5866604b0b001 0x308c5866604b0b00

def z889 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5d06066784707000 0x45d0606678470700

def z890 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xbe3fb8780700ff3e 0xfbe3fb8780700ff3

def z891 : W := mkw 0x0409000088414151 0x0040900008841415 0xf6280089994343ff 0xdf6280089994343f

def z892 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x1c27b8680700ff0c 0xf1c27b8680700ff0

def z893 : W := mkw 0x39160227209494a0 0x839160227209494a 0x3c9fc77666bcfc0c 0xf3c9fc77666bcfc0

def z894 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c1db8780600ff0c 0xb3c1db8780600ff0

def z895 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x09953ff7f8000000 0x009953ff7f800000

def z896 : W := mkw 0x0409000088414151 0x0040900008841415 0xfffb819ffb43cfff 0xffffb819ffb43cff

def z897 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7dff867f87f0ffcd 0xf7dff867f87f0ffc

def z898 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866784f070c1 0x45dc7866784f070c

def z899 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76e86899d7343ff 0xdf76e86899d7343f

def z900 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x1bffbffff8000000 0x01bffbffff800000

def z901 : W := mkw 0x150d022588515151 0x0150d02258851515 0x11060661857373ff 0xd11060661857373f

def z902 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xddc78667e4f0f0f5 0x7ddc78667e4f0f0f

def z903 : W := mkw 0x1104022500101000 0x0110402250010100 0x0885066604303000 0x0088506660430300

def z904 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfc954777e6bcfcfc 0x2fc954777e6bcfcf

def z905 : W := mkw 0x3114022700909080 0x0311402270090908 0x4c85066604b0b0c4 0x24c85066604b0b0c

def z906 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x51060667847070c0 0x451060667847070c

def z907 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffe00fc0c 0xfffffbffffe00fc0

def z908 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x7c7fb8780700ffcd 0xf7c7fb8780700ffc

def z909 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x0bffffe007ffb003 0xf0bffffe007ffb00

def z910 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe6d8c116628c0cff 0x9e6d8c116628c0cf

def z911 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfefff97e678cff0f 0xffefff97e678cff0

def z912 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffff88c0003 0x0fffffffff88c000

def z913 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c39b8780300ff0c 0xb3c39b8780300ff0

def z914 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780300ff0c 0x83c3fb8780300ff0

def z915 : W := mkw 0x28120002208484a0 0x828120002208484a 0xead94116628c8cfb 0xaead94116628c8cf

def z916 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c1538780000ff0c 0x03c1538780000ff0

def z917 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff800430c 0x0ffffbffff800430

def z918 : W := mkw 0x2c1b0002a8c5c5f1 0x82c1b0002a8c5c5f 0x19b3419ffbcfcf00 0x619b3419ffbcfcf0

def z919 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x19263efff8000000 0x019263efff800000

def z920 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeef9c11e638c8fff 0xbeef9c11e638c8ff

def z921 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xe7ffff8007ff0003 0xfe7ffff8007ff000

def z922 : W := mkw 0x28120002208484a0 0x828120002208484a 0xcad14116628c8cff 0xbcad14116628c8cf

def z923 : W := mkw 0x39160227209494a0 0x839160227209494a 0x0885466606bcbc00 0x20885466606bcbc0

def z924 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffdf8777e4f0fcfd 0x7ffdf8777e4f0fcf

def z925 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x51c6066784f0f0c5 0x751c6066784f0f0c

def z926 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780700ffff 0xf3c3fb8780700fff

def z927 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefd9c71662fc8cff 0xbefd9c71662fc8cf

def z928 : W := mkw 0x150d022588515151 0x0150d02258851515 0xffef86ef9d737300 0x4ffef86ef9d73730

def z929 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffff8000f08 0x0ffffbffff8000f0

def z930 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffefc0003 0xffffffffffefc000

def z931 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x0fffff8007ff8007 0xf0fffff8007ff800

def z932 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5dc7866784f07001 0x75dc7866784f0700

def z933 : W := mkw 0x0000000000000000 0x0000000000000000 0x09c7866004f0b001 0x709c7866004f0b00

def z934 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116628c0cfb 0x8eed9c116628c0cf

def z935 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x13ffff899fff0003 0xf13ffff899fff000

def z936 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x283d38780700ff0c 0xf283d38780700ff0

def z937 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fc7c76784fcf0c7 0x75fc7c76784fcf0c

def z938 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03d7ff8006ff0003 0x703d7ff8006ff000

def z939 : W := mkw 0x2010000200808080 0x0201000020080808 0x5dc7866604f0f0c5 0x75dc7866604f0f0c

def z940 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xdfc78767e4f0f0c5 0x7dfc78767e4f0f0c

def z941 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03f9ff8003ff0003 0xb03f9ff8003ff000

def z942 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeefff916628c8cff 0xbeefff916628c8cf

def z943 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x1c37b8780700ff04 0x71c37b8780700ff0

def z944 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03bf7f8007ff0002 0xe03bf7f8007ff000

def z945 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xdfc7c7e7fcfff0f7 0x7dfc7c7e7fcfff0f

def z946 : W := mkw 0x2872185a2784aeaa 0x92872185a2784aea 0xd2e6796e658c73f3 0x4d2e6796e658c73f

def z947 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866784f0f0ff 0xf5dc7866784f0f0f

def z948 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x102638680500ff0c 0x4102638680500ff0

def z949 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01a67f8005ff0000 0x401a67f8005ff000

def z950 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffef86e785f3f0ff 0xfffef86e785f3f0f

def z951 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffa008c00 0x2ffffbffffa008c0

def z952 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7fef86ef85f3f3cf 0xf7fef86ef85f3f3c

def z953 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff94300ff 0xdffffbffff94300f

def z954 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfffbc19ffbcf8cff 0xffffbc19ffbcf8cf

def z955 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8430003 0x0ffffbffff843000

def z956 : W := mkw 0x80e0185857002a0e 0x180e0185857002a0 0xbc3fb8787f00ff0c 0xfbc3fb8787f00ff0

def z957 : W := mkw 0x2c7b0802afc5eff3 0x82c7b0802afc5eff 0x0000400007cfffff 0xf0000400007cffff

def z958 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x112606e99df3f3ff 0xf112606e99df3f3f

def z959 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xa3ffff9067ff0003 0xfa3ffff9067ff000

def z960 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfff83ffff8000000 0x0fff83ffff800000

def z961 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x342eb8680700ff0c 0xf342eb8680700ff0

def z962 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xf7ffff899fff00ff 0xff7ffff899fff00f

def z963 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xdfc7866784f0f0f7 0x7dfc7866784f0f0f

def z964 : W := mkw 0x81e01a7d57002a0e 0x181e01a7d57002a0 0xfc00007fff00ff0c 0xffc00007fff00ff0

def z965 : W := mkw 0x0200258000000000 0x2020025800000000 0xffffbf9ff8000000 0x0ffffbf9ff800000

def z966 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5de786ef9cf0f0c5 0x75de786ef9cf0f0c

def z967 : W := mkw 0x110c022580505041 0x0110c02258050504 0x0104066184703000 0x0010406618470300

def z968 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780600ff0c 0x23c3fb8780600ff0

def z969 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff80000f3 0x0ffffbffff80000f

def z970 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xeff9bf9ff8000000 0x0eff9bf9ff800000

def z971 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x3fffff9807ffcf0f 0xf3fffff9807ffcf0

def z972 : W := mkw 0x0409000088414151 0x0040900008841415 0xf77a80999b434fff 0xdf77a80999b434ff

def z973 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x4cc5866604f0f0c5 0x74cc5866604f0f0c

def z974 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffef86ef9df3f0c7 0xfffef86ef9df3f0c

def z975 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x23ffff8807ff030b 0xf23ffff8807ff030

def z976 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xf7ee86ef9df373ff 0xdf7ee86ef9df373f

def z977 : W := mkw 0x28120002208484a0 0x828120002208484a 0xee19c116620c8cfe 0xbee19c116620c8cf

def z978 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5de786ef9df3f3ff 0xf5de786ef9df3f3f

def z979 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3f7ff8f807ffff0f 0xf3f7ff8f807ffff0

def z980 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1106066184f07001 0x71106066184f0700

def z981 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfedfc176628c8cff 0xbfedfc176628c8cf

def z982 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x13ffff8807ff4303 0xf13ffff8807ff430

def z983 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dc7c767e4fcf0c5 0x75dc7c767e4fcf0c

def z984 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01957f8006ff0000 0x201957f8006ff000

def z985 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089994343f3 0x4f76a8089994343f

def z986 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1d07866184f0f0c5 0x71d07866184f0f0c

def z987 : W := mkw 0x150d022588515151 0x0150d02258851515 0x13ef86e99df37303 0xf13ef86e99df3730

def z988 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fef86e784f0f0c5 0x75fef86e784f0f0c

def z989 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03d57f8000ff0003 0x003d57f8000ff000

def z990 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfdffbe7ff8000000 0x0fdffbe7ff800000

def z991 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dc78677e4f0fcc5 0x75dc78677e4f0fcc

def z992 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x0bffff9667ff0003 0xf0bffff9667ff000

def z993 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xff7ab9fff8000000 0x0ff7ab9fff800000

def z994 : W := mkw 0x0409000088414151 0x0040900008841415 0xf77a8199f94343ff 0xdf77a8199f94343f

def z995 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x081538700600ff0c 0x2081538700600ff0

def z996 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8008004 0x3ffffbffff800800

def z997 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1186066784f07000 0x41186066784f0700

def z998 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xf7fabf9ff8000000 0x0f7fabf9ff800000

def z999 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fcf866784f0f0c7 0xf5fcf866784f0f0c

def z1000 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5cc5866784b0f0c5 0x35cc5866784b0f0c

def z1001 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x081538700700ff00 0x6081538700700ff0

def z1002 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xa3ffff8007ff003b 0xfa3ffff8007ff003

def z1003 : W := mkw 0x3114022700909080 0x0311402270090908 0x4cc5866604b0b000 0x24cc5866604b0b00

def z1004 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116628c8cfc 0x2eed9c116628c8cf

def z1005 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xf7ffff8807ff43ff 0xff7ffff8807ff43f

def z1006 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8007ff8c0f 0xf03ffff8007ff8c0

def z1007 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dc7c66784fcf0f7 0x75dc7c66784fcf0f

def z1008 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0x5dc7c66787ffffff 0xf5dc7c66787fffff

def z1009 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x59c7066784f0f0c1 0x659c7066784f0f0c

def z1010 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec99c116628c8cfc 0xbec99c116628c8cf

def z1011 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xdfd7c777e6fcfcf7 0x7dfd7c777e6fcfcf

def z1012 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffd53ffff8000000 0x0ffd53ffff800000

def z1013 : W := mkw 0x0409000088414151 0x0040900008841415 0xf62a8089990343fe 0xdf62a8089990343f

def z1014 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xefffff9667ff00ff 0xfefffff9667ff00f

def z1015 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xcbffbff7f8000000 0x0cbffbff7f800000

def z1016 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeeddc71666bc8cff 0xbeeddc71666bc8cf

def z1017 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c0438780400ff0c 0x03c0438780400ff0

def z1018 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefffc79667ff8cff 0xfefffc79667ff8cf

def z1019 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe2184116620c0cfa 0x8e2184116620c0cf

def z1020 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3cffb8780780ff0d 0xf3cffb8780780ff0

def z1021 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8008c0c 0x0ffffbffff8008c0

def z1022 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3cbfbe7807b0ff0c 0xf3cbfbe7807b0ff0

def z1023 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c2638780700ff0c 0xf3c2638780700ff0

def z1024 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1126066985707300 0x4112606698570730

def z1025 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xdfc7c767e6fcfcff 0xfdfc7c767e6fcfcf

def z1026 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01f7ff8007ff0001 0x701f7ff8007ff000

def z1027 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeffbc196628c8cff 0xbeffbc196628c8cf

def z1028 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffffc7fffefcfcff 0xfffffc7fffefcfcf

def z1029 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3dfffe7807ffff0f 0xf3dfffe7807ffff0

def z1030 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7eac18999cf43ff 0xdf7eac18999cf43f

def z1031 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed14116628c8cff 0x2eed14116628c8cf

def z1032 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c2038780100ff0c 0x03c2038780100ff0

def z1033 : W := mkw 0x110c022580505041 0x0110c02258050504 0x11c7866184707000 0x411c786618470700

def z1034 : W := mkw 0x6a723dda27aeaeaa 0xb6a723dda27aeaea 0xeef9f99e638f8fff 0xbeef9f99e638f8ff

def z1035 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xeeddc77666fcfcff 0xfeeddc77666fcfcf

def z1036 : W := mkw 0x0802000020040420 0x8080200002004042 0xeed9c116620c0cff 0x9eed9c116620c0cf

def z1037 : W := mkw 0x28120002208484a0 0x828120002208484a 0xec914116628c8cff 0xbec914116628c8cf

def z1038 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3efff97807ffff0f 0xf3efff97807ffff0

def z1039 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116638ccfff 0xfeed9c116638ccff

def z1040 : W := mkw 0x28120002208484a0 0x828120002208484a 0xee58c116620c8cff 0x9ee58c116620c8cf

def z1041 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00bfff0007ff0003 0xf00bfff0007ff000

def z1042 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffefc7effdfff3ff 0xfffefc7effdfff3f

def z1043 : W := mkw 0x3114022700909080 0x0311402270090908 0x0895476606bcb000 0x20895476606bcb00

def z1044 : W := mkw 0x3114022700909080 0x0311402270090908 0x0895067606b0bc00 0x20895067606b0bc0

def z1045 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfc3fb8780700fffc 0xffc3fb8780700fff

def z1046 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03f87f8000ff0003 0x003f87f8000ff000

def z1047 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x1fffffe007ff0003 0xf1fffffe007ff000

def z1048 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xdfdfc767e6fcf0f7 0xfdfdfc767e6fcf0f

def z1049 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x083fb8700700ff0c 0xf083fb8700700ff0

def z1050 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c3838780000ff0c 0x03c3838780000ff0

def z1051 : W := mkw 0x838027a550000004 0x2838027a55000000 0xf7ffbf8ff8000000 0x0f7ffbf8ff800000

def z1052 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dc7866784f0fcfd 0x75dc7866784f0fcf

def z1053 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffef86ef9df0f3cd 0xfffef86ef9df0f3c

def z1054 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfeddc777e6bcfcff 0xbfeddc777e6bcfcf

def z1055 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffff87fffdf3f3ff 0xfffff87fffdf3f3f

def z1056 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffcf86e79cf3f0ff 0xfffcf86e79cf3f0f

def z1057 : W := mkw 0x3114022700909080 0x0311402270090908 0x5dc7866784f0b001 0x75dc7866784f0b00

def z1058 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03fe7f8007ff0003 0xc03fe7f8007ff000

def z1059 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeef9c196638f8cff 0xbeef9c196638f8cf

def z1060 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x37ffff8807ffff0f 0xf37ffff8807ffff0

def z1061 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfc38387ff8000000 0x0fc38387ff800000

def z1062 : W := mkw 0x0000000000000000 0x0000000000000000 0x3fef86e805f3f30f 0xf3fef86e805f3f30

def z1063 : W := mkw 0x3114022700909080 0x0311402270090908 0x0885066604f0b001 0x70885066604f0b00

def z1064 : W := mkw 0x150d022588515151 0x0150d02258851515 0x1106066185737300 0x4110606618573730

def z1065 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76ac0899bcf43ff 0xff76ac0899bcf43f

def z1066 : W := mkw 0x39160227209494a0 0x839160227209494a 0xaa9d477666bcbc3a 0xaaa9d477666bcbc3

def z1067 : W := mkw 0x150d022588515151 0x0150d02258851515 0xd34606e19c7370f3 0x4d34606e19c7370f

def z1068 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffe63ffff8000000 0x0ffe63ffff800000

def z1069 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780700ff00 0x63c3fb8780700ff0

def z1070 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03e07f8001ff0003 0x003e07f8001ff000

def z1071 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfcbfbf7ff8000000 0x0fcbfbf7ff800000

def z1072 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8400001 0x5ffffbffff840000

def z1073 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x49c7866784f0b0c1 0x749c7866784f0b0c

def z1074 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c3fb8780100ff0c 0xd3c3fb8780100ff0

def z1075 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00047e0007ff0003 0xf00047e0007ff000

def z1076 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3ff878078cff0f 0xf3c3ff878078cff0

def z1077 : W := mkw 0x0000000000000000 0x0000000000000000 0x1106066004707000 0x4110606600470700

def z1078 : W := mkw 0x110c022580505041 0x0110c02258050504 0x190706618470f000 0x6190706618470f00

def z1079 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfd060677e470fcfc 0x4fd060677e470fcf

def z1080 : W := mkw 0x0409000088414151 0x0040900008841415 0xf52a8089994343fc 0xdf52a8089994343f

def z1081 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x013ffe8007ff0003 0xf013ffe8007ff000

def z1082 : W := mkw 0x0409000088414151 0x0040900008841415 0xd7628089994343f7 0x5d7628089994343f

def z1083 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x49c5066784f0f0c5 0x749c5066784f0f0c

def z1084 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7620089994343ff 0x4f7620089994343f

def z1085 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffffc00ff0c 0x7ffffbffffc00ff0

def z1086 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xc3ffff819fff0003 0xfc3ffff819fff000

def z1087 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x51c7866784f070c1 0x751c7866784f070c

def z1088 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a80899b43cfff 0xff76a80899b43cff

def z1089 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7dcf866784f0f0cd 0xf7dcf866784f0f0c

def z1090 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x0885066605f3f3ff 0xf0885066605f3f3f

def z1091 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfdd7c777e6fcfcfd 0x7fdd7c777e6fcfcf

def z1092 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1d07866184707000 0x41d0786618470700

def z1093 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dd78777e4f0f0c5 0x75dd78777e4f0f0c

def z1094 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x0bffff9007ff8c03 0xf0bffff9007ff8c0

def z1095 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefd9c19662cf8cff 0xbefd9c19662cf8cf

def z1096 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xfefff978078cffff 0xffefff978078cfff

def z1097 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x181538780600ff00 0x2181538780600ff0

def z1098 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xfdc78677e4f0f0c5 0x7fdc78677e4f0f0c

def z1099 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d0786600470f004 0x71d0786600470f00

def z1100 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xe238399ff8000000 0x0e238399ff800000

def z1101 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffa8c00ff 0xbfffffffffa8c00f

def z1102 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fdf876784f0f0c5 0x75fdf876784f0f0c

def z1103 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffcf866784f0f0c5 0x7ffcf866784f0f0c

def z1104 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfc15387ff8000000 0x0fc15387ff800000

def z1105 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed84116628c8cff 0x8eed84116628c8cf

def z1106 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x02ddff0007ff0003 0xf02ddff0007ff000

def z1107 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c85066784f0f0c5 0x75c85066784f0f0c

def z1108 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x27ffff8007ff000f 0xf27ffff8007ff000

def z1109 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7eb808999c343ff 0xff7eb808999c343f

def z1110 : W := mkw 0x28120002208484a0 0x828120002208484a 0xcad9c116628c8cf3 0xbcad9c116628c8cf

def z1111 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089994303fb 0x8f76a8089994303f

def z1112 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x5df7bffff8000000 0x05df7bffff800000

def z1113 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5de786e785f3f0c5 0x75de786e785f3f0c

def z1114 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x033e7f8007ff0003 0xf033e7f8007ff000

def z1115 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffc786ef9cf3f3ff 0x7ffc786ef9cf3f3f

def z1116 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1987066784707000 0x4198706678470700

def z1117 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x17ffff8007ff4007 0xf17ffff8007ff400

def z1118 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1146866184707001 0x5114686618470700

def z1119 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5fdfc777e6fcfcc7 0xf5fdfc777e6fcfcc

def z1120 : W := mkw 0x28120002208484a0 0x828120002208484a 0xced1c116628c8cf7 0x3ced1c116628c8cf

def z1121 : W := mkw 0x39160227209494a0 0x839160227209494a 0xfedfc77666bcfcff 0xffedfc77666bcfcf

def z1122 : W := mkw 0x3114022700909080 0x0311402270090908 0x2c9d867606b0bc0c 0xb2c9d867606b0bc0

def z1123 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866785f3f0c7 0xf5dc7866785f3f0c

def z1124 : W := mkw 0x4a623dd8272e2e2a 0xb4a623dd8272e2e2 0xa2387998630f0f3a 0x8a2387998630f0f3

def z1125 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866784f0f000 0x65dc7866784f0f00

def z1126 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffef86fffdf3ffff 0xfffef86fffdf3fff

def z1127 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfeddbf7ff8000000 0x0feddbf7ff800000

def z1128 : W := mkw 0x150d022588515151 0x0150d02258851515 0xf7ef86e99df373ff 0xff7ef86e99df373f

def z1129 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xc3e03f8ff8000000 0x0c3e03f8ff800000

def z1130 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x02387990030f0c02 0x802387990030f0c0

def z1131 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x00957f0006ff0003 0x200957f0006ff000

def z1132 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xf7eebfeff8000000 0x0f7eebfeff800000

def z1133 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xfffffffff9ff0003 0xdfffffffff9ff000

def z1134 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xfffffffffcff0003 0x7fffffffffcff000

def z1135 : W := mkw 0x0409000088414151 0x0040900008841415 0xffeb808f994343ff 0xdffeb808f994343f

def z1136 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ddff8006ff0003 0xb03ddff8006ff000

def z1137 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeeddc176668cbcff 0xbeeddc176668cbcf

def z1138 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffef866f85f0f3ff 0xfffef866f85f0f3f

def z1139 : W := mkw 0x0409000088414151 0x0040900008841415 0xf77fb889994343ff 0xdf77fb889994343f

def z1140 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xa3ffff881fff0003 0xfa3ffff881fff000

def z1141 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff800f004 0x0ffffbffff800f00

def z1142 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe2d9c116628c0cfb 0xbe2d9c116628c0cf

def z1143 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8003ff0003 0x803ffff8003ff000

def z1144 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfc043e7ff8000000 0x0fc043e7ff800000

def z1145 : W := mkw 0x28120002208484a0 0x828120002208484a 0xee994116628c8cfe 0xaee994116628c8cf

def z1146 : W := mkw 0x140d000088515151 0x0140d00008851515 0xf76a80899d7373ff 0xdf76a80899d7373f

def z1147 : W := mkw 0x28120002208484a0 0x828120002208484a 0x08914116628c8cfc 0x208914116628c8cf

def z1148 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfed9c11e628ccfff 0xbfed9c11e628ccff

def z1149 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfffbc19e63cfcfff 0xffffbc19e63cfcff

def z1150 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3d3fb8f80743ff0c 0xf3d3fb8f80743ff0

def z1151 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfeffb97ff8000000 0x0feffb97ff800000

def z1152 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xfdc7866784f0f0fd 0x7fdc7866784f0f0f

def z1153 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5dc78667847070c5 0x55dc78667847070c

def z1154 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7dc7866f84f0f3cd 0x77dc7866f84f0f3c

def z1155 : W := mkw 0x3114022700909080 0x0311402270090908 0x48c5066604b0b0c1 0x248c5066604b0b0c

def z1156 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x00107910020c0c00 0x000107910020c0c0

def z1157 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffef86ef9cf3f0f7 0x7ffef86ef9cf3f0f

def z1158 : W := mkw 0x28120002208484a0 0x828120002208484a 0xc2d04116628c0cf3 0x0c2d04116628c0cf

def z1159 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1885066784b0f000 0x21885066784b0f00

def z1160 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffff8007300 0x0ffffbffff800730

def z1161 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c2eb8780500ff0c 0xd3c2eb8780500ff0

def z1162 : W := mkw 0x3114022700909080 0x0311402270090908 0x5cc7866604b0f0c5 0x75cc7866604b0f0c

def z1163 : W := mkw 0x46693dd88f6b6b5b 0x346693dd88f6b6b5 0xf77af9999b4f4fff 0xdf77af9999b4f4ff

def z1164 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01e7fe8007ff0003 0xf01e7fe8007ff000

def z1165 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xdfc786e79df3f3ff 0xfdfc786e79df3f3f

def z1166 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8800001 0x3ffffbffff880000

def z1167 : W := mkw 0x3114022700909080 0x0311402270090908 0xeedd877664b0b000 0x2eedd877664b0b00

def z1168 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xfc26387ff8000000 0x0fc26387ff800000

def z1169 : W := mkw 0x39160227209494a0 0x839160227209494a 0x0bdfc77666fcbc03 0xf0bdfc77666fcbc0

def z1170 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dd7c777e6fcfcff 0xf5dd7c777e6fcfcf

def z1171 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffffc7f7e7fffcff 0xfffffc7f7e7fffcf

def z1172 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xffffff9fffff0003 0xfffffff9fffff000

def z1173 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffa008cff 0xbffffbffffa008cf

def z1174 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xfffffffff8bc0000 0x0fffffffff8bc000

def z1175 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x19974777e6fcfc00 0x619974777e6fcfc0

def z1176 : W := mkw 0x3114022700909080 0x0311402270090908 0x0addc76606bcb003 0xb0addc76606bcb00

def z1177 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xfdc7866f9cf0f0c5 0x7fdc7866f9cf0f0c

def z1178 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x0895477666fcfcff 0xf0895477666fcfcf

def z1179 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xcbd54777e6fcbcf3 0x2cbd54777e6fcbcf

def z1180 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xffffb9ffff00ff0c 0xfffffb9ffff00ff0

def z1181 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5fdfc76786fcfcff 0xf5fdfc76786fcfcf

def z1182 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffcfc66786fcfcff 0xfffcfc66786fcfcf

def z1183 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3cbfb97e6700ff0c 0xf3cbfb97e6700ff0

def z1184 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x2038389803030f08 0x82038389803030f0

def z1185 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffff900ff0c 0xdffffbffff900ff0

def z1186 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8005ff0003 0x403ffff8005ff000

def z1187 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5d4686678470f0c5 0x55d4686678470f0c

def z1188 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x2ef9f998038f8f0f 0xb2ef9f998038f8f0

def z1189 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfd2606ef9d73f3fc 0x4fd2606ef9d73f3f

def z1190 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x20387918030c0f08 0x820387918030c0f0

def z1191 : W := mkw 0x110c022580505041 0x0110c02258050504 0x352e86698570730c 0xd352e86698570730

def z1192 : W := mkw 0x0409000088414151 0x0040900008841415 0xd1220089994343f0 0x4d1220089994343f

def z1193 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff800003a 0x8ffffbffff800003

def z1194 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c27b8780500ff0c 0x73c27b8780500ff0

def z1195 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7def866f84f0f0c5 0x77def866f84f0f0c

def z1196 : W := mkw 0x3114022700909080 0x0311402270090908 0x3caf866e05b0f30c 0xf3caf866e05b0f30

def z1197 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03e67f8007ff0003 0xf03e67f8007ff000

def z1198 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfeffc17e678cffff 0xffeffc17e678cfff

def z1199 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c1538780700ff0c 0xf3c1538780700ff0

def z1200 : W := mkw 0x110c022580505041 0x0110c02258050504 0x0004066004707000 0x4000406600470700

def z1201 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x110606618470f0c4 0x4110606618470f0c

def z1202 : W := mkw 0x110c022580505041 0x0110c02258050504 0x11060661847070c5 0x511060661847070c

def z1203 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x2fffff9007ff0003 0xf2fffff9007ff000

def z1204 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866785f0f3cd 0xf5dc7866785f0f3c

def z1205 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03eeff8005ff0003 0xd03eeff8005ff000

def z1206 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x3dbfbffff8000000 0x03dbfbffff800000

def z1207 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7ea868999f343ff 0xdf7ea868999f343f

def z1208 : W := mkw 0x28120002208484a0 0x828120002208484a 0xffdbc117e28c8cff 0xbffdbc117e28c8cf

def z1209 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x1106466186fcfcff 0xf1106466186fcfcf

def z1210 : W := mkw 0x0409000088414151 0x0040900008841415 0x11220089994343fc 0x411220089994343f

def z1211 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xdfe7bfeff8000000 0x0dfe7bfeff800000

def z1212 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x4dc5866784f0b0c5 0x34dc5866784f0b0c

def z1213 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff9030002 0x8ffffbffff903000

def z1214 : W := mkw 0x110c022580505041 0x0110c02258050504 0x5d4786618470f0c5 0x75d4786618470f0c

def z1215 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3ffff9f807cfff0f 0xf3ffff9f807cfff0

def z1216 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x3fffffe807fff30f 0xf3fffffe807fff30

def z1217 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xefffff9007ff8cff 0xfefffff9007ff8cf

def z1218 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xffffbffff8730000 0x0ffffbffff873000

def z1219 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x09c7866604f0f0c5 0x709c7866604f0f0c

def z1220 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c116628c8cf3 0x2eed9c116628c8cf

def z1221 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c3fb8780400ff0c 0x73c3fb8780400ff0

def z1222 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xf3fe3ffff8000000 0x0f3fe3ffff800000

def z1223 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffa8c8c0f 0xbfffffffffa8c8c0

def z1224 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeefbc116638c8cff 0xfeefbc116638c8cf

def z1225 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866784f0b0c1 0x25dc7866784f0b0c

def z1226 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03ffff8002ff0003 0xb03ffff8002ff000

def z1227 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xc3ffff8007ff00f3 0xfc3ffff8007ff00f

def z1228 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3e38780700ff0c 0xc3c3e38780700ff0

def z1229 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3838780700ff0c 0xf3c3838780700ff0

def z1230 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffffc000000 0x7ffffbffffc00000

def z1231 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7ef8689994343ff 0xdf7ef8689994343f

def z1232 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffdfc777e6fcf0c7 0xfffdfc777e6fcf0c

def z1233 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1c87866604f0f0c5 0x71c87866604f0f0c

def z1234 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7dc7867784f0fccd 0x77dc7867784f0fcc

def z1235 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x0885066604f0f000 0x60885066604f0f00

def z1236 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3c3ff878070fff0e 0xf3c3ff878070fff0

def z1237 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc5066784f0f0c5 0x25dc5066784f0f0c

def z1238 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffef86ef9cf0f3fd 0x7ffef86ef9cf0f3f

def z1239 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xfdc7867ffcf0fffd 0x7fdc7867ffcf0fff

def z1240 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeedfc116668c8cff 0xfeedfc116668c8cf

def z1241 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8007ff0000 0x603ffff8007ff000

def z1242 : W := mkw 0x150d022588515151 0x0150d02258851515 0xb32e06e99d73733a 0xcb32e06e99d73733

def z1243 : W := mkw 0x110c022580505041 0x0110c02258050504 0x51460661847070c1 0x451460661847070c

def z1244 : W := mkw 0x1104022500101000 0x0110402250010100 0x0106066004703000 0x4010606600470300

def z1245 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01267e8005ff0003 0x401267e8005ff000

def z1246 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1004066184307000 0x0100406618430700

def z1247 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffcf866f9cf0f3ff 0xfffcf866f9cf0f3f

def z1248 : W := mkw 0x0409000088414151 0x0040900008841415 0xd36a8089994343f3 0xdd36a8089994343f

def z1249 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x183fb8780700ff00 0xf183fb8780700ff0

def z1250 : W := mkw 0x110c022580505041 0x0110c02258050504 0x112606e185737000 0x4112606e18573700

def z1251 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x102638680700ff00 0x6102638680700ff0

def z1252 : W := mkw 0x8180127d5000000c 0x18180127d5000000 0xff7fb8fff8000000 0x0ff7fb8fff800000

def z1253 : W := mkw 0x0409000088414151 0x0040900008841415 0xf36a0089994343fb 0xcf36a0089994343f

def z1254 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1987066784f0f0c5 0x71987066784f0f0c

def z1255 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffff800bc00 0x0ffffbffff800bc0

def z1256 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7ddf867784f0f0c5 0x77ddf867784f0f0c

def z1257 : W := mkw 0x0409000088414151 0x0040900008841415 0x136a8089994343ff 0xd136a8089994343f

def z1258 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfffffffffa0c0002 0x8fffffffffa0c000

def z1259 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefdbc11662cc8cff 0xfefdbc11662cc8cf

def z1260 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76e80e99d4373ff 0xdf76e80e99d4373f

def z1261 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfd3fbefff8000000 0x0fd3fbefff800000

def z1262 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xefddc777e6fcbcff 0xbefddc777e6fcbcf

def z1263 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1d0606618470f004 0x41d0606618470f00

def z1264 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x19a706ef9df3f300 0x619a706ef9df3f30

def z1265 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01d7ff0007ff0003 0xf01d7ff0007ff000

def z1266 : W := mkw 0x1104022500101000 0x0110402250010100 0x0085066004b03000 0x20085066004b0300

def z1267 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfdc7c677e6fcfcff 0xffdc7c677e6fcfcf

def z1268 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffffc77fe7fcffff 0xfffffc77fe7fcfff

def z1269 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xdfe786ef9df3f3f7 0x7dfe786ef9df3f3f

def z1270 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x7cffb87e0700ff0c 0xf7cffb87e0700ff0

def z1271 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffdfc7f7fefffcff 0xfffdfc7f7fefffcf

def z1272 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5d06066784f0f0c5 0x75d06066784f0f0c

def z1273 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03f77f8007ff0003 0x603f77f8007ff000

def z1274 : W := mkw 0x0409000088414151 0x0040900008841415 0xf77ac1899b4f43ff 0xdf77ac1899b4f43f

def z1275 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x03ffff8007ffbc03 0xf03ffff8007ffbc0

def z1276 : W := mkw 0x0409000088414151 0x0040900008841415 0x55628089994343ff 0xd55628089994343f

def z1277 : W := mkw 0x0409000088414151 0x0040900008841415 0xe36a8089994303fb 0xde36a8089994303f

def z1278 : W := mkw 0x0409000088414151 0x0040900008841415 0xf4200089990343fc 0x0f4200089990343f

def z1279 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5fef86e785f3f3ff 0xf5fef86e785f3f3f

def z1280 : W := mkw 0x0409000088414151 0x0040900008841415 0xff6f80e9994343ff 0xdff6f80e9994343f

def z1281 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x03ffff8007ff0f0b 0xf03ffff8007ff0f0

def z1282 : W := mkw 0x1104022500101000 0x0110402250010100 0x1106066184303000 0x0110606618430300

def z1283 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xdbf73ffff8000000 0x0dbf73ffff800000

def z1284 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff9000308 0x8ffffbffff900030

def z1285 : W := mkw 0x3114022700909080 0x0311402270090908 0x09c5066604f0b001 0x209c5066604f0b00

def z1286 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xff7fb8f99f43ff0f 0xfff7fb8f99f43ff0

def z1287 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffdfc76786fcf0ff 0xfffdfc76786fcf0f

def z1288 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffdf867786f0fcff 0xfffdf867786f0fcf

def z1289 : W := mkw 0x3114022700909080 0x0311402270090908 0x1dc7866604f0f005 0x71dc7866604f0f00

def z1290 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780743ff0f 0xf3c3fb8780743ff0

def z1291 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xebfd3ffff8000000 0x0ebfd3ffff800000

def z1292 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5d0786678470f0c4 0x75d0786678470f0c

def z1293 : W := mkw 0x3114022700909080 0x0311402270090908 0x0887866604b0b000 0x70887866604b0b00

def z1294 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c11663cf8cff 0xfeed9c11663cf8cf

def z1295 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3e3fb8f80703ff0e 0xf3e3fb8f80703ff0

def z1296 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3effb9780700ff0c 0xf3effb9780700ff0

def z1297 : W := mkw 0x39160227209494a0 0x839160227209494a 0x0885476664bcb000 0x20885476664bcb00

def z1298 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xdfef86e79df3f0f7 0xfdfef86e79df3f0f

def z1299 : W := mkw 0x3114022700909080 0x0311402270090908 0x49c5066784b0b000 0x249c5066784b0b00

def z1300 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x1c17b8700700ff0c 0xf1c17b8700700ff0

def z1301 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01267e8007ff0000 0x601267e8007ff000

def z1302 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1107866184707000 0x7110786618470700

def z1303 : W := mkw 0x39160227209494a0 0x839160227209494a 0x0885067664b0bc00 0x20885067664b0bc0

def z1304 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5fef86ef9df3f3c7 0xf5fef86ef9df3f3c

def z1305 : W := mkw 0x3114022700909080 0x0311402270090908 0x5dc7866784b0f004 0x75dc7866784b0f00

def z1306 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03c47f8004ff0003 0x003c47f8004ff000

def z1307 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5de7866f85f0f3c5 0x75de7866f85f0f3c

def z1308 : W := mkw 0x150d022588515151 0x0150d02258851515 0x3d2f86e99d73f30c 0xf3d2f86e99d73f30

def z1309 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7680089994343ff 0x8f7680089994343f

def z1310 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfc85066f9cb0f3fc 0x2fc85066f9cb0f3f

def z1311 : W := mkw 0x0409000088414151 0x0040900008841415 0xff6a80999943cfff 0xdff6a80999943cff

def z1312 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff9004300 0x4ffffbffff900430

def z1313 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x7ddfc777e6fcfccd 0xf7ddfc777e6fcfcc

def z1314 : W := mkw 0x3114022700909080 0x0311402270090908 0x0885066604b0f004 0x70885066604b0f00

def z1315 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfde786ef9df3f3fd 0x7fde786ef9df3f3f

def z1316 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5dc786e79cf3f0c5 0x75dc786e79cf3f0c

def z1317 : W := mkw 0x110c022580505041 0x0110c02258050504 0xf74e8661847070ff 0xdf74e8661847070f

def z1318 : W := mkw 0x0409000088414151 0x0040900008841415 0xf5628089994343fd 0x5f5628089994343f

def z1319 : W := mkw 0x0409000088414151 0x0040900008841415 0x352a8089994343ff 0xd352a8089994343f

def z1320 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x377af998034f4f0f 0xd377af998034f4f0

def z1321 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8007ff430f 0xf03ffff8007ff430

def z1322 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x0885066604f0b0c1 0x20885066604f0b0c

def z1323 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7fb8189994343ff 0xdf7fb8189994343f

def z1324 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a8089990343fe 0x8f76a8089990343f

def z1325 : W := mkw 0x3114022700909080 0x0311402270090908 0x5c85066784b0b000 0x25c85066784b0b00

def z1326 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff9000000 0xdffffbffff900000

def z1327 : W := mkw 0x3114022700909080 0x0311402270090908 0x1887066604b0f000 0x61887066604b0f00

def z1328 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffdfc777e6fcfcc5 0x7ffdfc777e6fcfcc

def z1329 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeed9c11666fc8cff 0xfeed9c11666fc8cf

def z1330 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xe3ffbf9ff8000000 0x0e3ffbf9ff800000

def z1331 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xff6e86ef9d73f3ff 0xdff6e86ef9d73f3f

def z1332 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76a80899df343ff 0xff76a80899df343f

def z1333 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfe3fb9fff8000000 0x0fe3fb9fff800000

def z1334 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x7ddfc67786fcfcff 0xf7ddfc67786fcfcf

def z1335 : W := mkw 0x46613dd80f2b2b1a 0x346613dd80f2b2b1 0xa23879981b0f0f3a 0x8a23879981b0f0f3

def z1336 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xfddf8677e6f0fcfd 0xffddf8677e6f0fcf

def z1337 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xefffff9667ff8c0f 0xfefffff9667ff8c0

def z1338 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x47ffff8007ff00c7 0xf47ffff8007ff00c

def z1339 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3d3fb8f99f00ff0c 0xf3d3fb8f99f00ff0

def z1340 : W := mkw 0x1104022500101000 0x0110402250010100 0x5dc7866784303000 0x05dc786678430300

def z1341 : W := mkw 0x39160227209494a0 0x839160227209494a 0xefdfc77666fcbcff 0xfefdfc77666fcbcf

def z1342 : W := mkw 0x42603dd8072a2a0a 0x342603dd8072a2a0 0x0020388801030300 0x0002038880103030

def z1343 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfefbc11e628c8cff 0xbfefbc11e628c8cf

def z1344 : W := mkw 0x0409000088414151 0x0040900008841415 0xe7688089994303ff 0x9e7688089994303f

def z1345 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1106066184f070c1 0x41106066184f070c

def z1346 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x4885066784b0b0c0 0x24885066784b0b0c

def z1347 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5def866785f0f0c5 0xf5def866785f0f0c

def z1348 : W := mkw 0x0409000088414151 0x0040900008841415 0x11220089994343f3 0x411220089994343f

def z1349 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff80000c5 0x1ffffbffff80000c

def z1350 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5c87866784b0f0c4 0x75c87866784b0f0c

def z1351 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5fffc7e787fff0c7 0xf5fffc7e787fff0c

def z1352 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7c66786fcf0c7 0xf5dc7c66786fcf0c

def z1353 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0xc3ffff8667ff0003 0xfc3ffff8667ff000

def z1354 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfed9c176628cfcff 0xbfed9c176628cfcf

def z1355 : W := mkw 0x0409000088414151 0x0040900008841415 0xf76f80899d4343ff 0xff76f80899d4343f

def z1356 : W := mkw 0x110c022580505041 0x0110c02258050504 0xf76e86e99c707000 0x4f76e86e99c70700

def z1357 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03ffff8004ff0003 0x703ffff8004ff000

def z1358 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x57ffff8187ff0003 0xf57ffff8187ff000

def z1359 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xd3ffbfeff8000000 0x0d3ffbfeff800000

def z1360 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3738780700ff0c 0x63c3738780700ff0

def z1361 : W := mkw 0x39160227209494a0 0x839160227209494a 0xffdfc777e6bcbcff 0xbffdfc777e6bcbcf

def z1362 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3e3ff978070cff0e 0xf3e3ff978070cff0

def z1363 : W := mkw 0x0409000088414151 0x0040900008841415 0xc3600089994303f3 0x0c3600089994303f

def z1364 : W := mkw 0xb19c0227d0d0d0c5 0x0b19c0227d0d0d0c 0xddc78667fcf0f0c5 0x7ddc78667fcf0f0c

def z1365 : W := mkw 0x28120002208484a0 0x828120002208484a 0x08914116628c8cf3 0x208914116628c8cf

def z1366 : W := mkw 0x0020105800002a08 0x10020105800002a0 0x3c3fb8780200ff0c 0xb3c3fb8780200ff0

def z1367 : W := mkw 0x28120002208484a0 0x828120002208484a 0xefd9c197fa8c8cff 0xbefd9c197fa8c8cf

def z1368 : W := mkw 0x0409000088414151 0x0040900008841415 0xf77b80899b4343ff 0xff77b80899b4343f

def z1369 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x7fdfc77786fcfccf 0xf7fdfc77786fcfcc

def z1370 : W := mkw 0x83a037fd50002a0c 0x383a037fd50002a0 0xffffbffffa00ff0c 0xbffffbffffa00ff0

def z1371 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x23ffff9007ff0c0b 0xf23ffff9007ff0c0

def z1372 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7400089994343ff 0xdf7400089994343f

def z1373 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0xffdf8777e6f0fccd 0xfffdf8777e6f0fcc

def z1374 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3f7fb8f80700ff0c 0xf3f7fb8f80700ff0

def z1375 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xefddbff7f8000000 0x0efddbff7f800000

def z1376 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3d38780700ff0c 0xa3c3d38780700ff0

def z1377 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xd1263eeff8000000 0x0d1263eeff800000

def z1378 : W := mkw 0x0409000088414151 0x0040900008841415 0xf7ea818ff94343ff 0xdf7ea818ff94343f

def z1379 : W := mkw 0x3114022700909080 0x0311402270090908 0x4dc7866604f0b0c5 0x74dc7866604f0b0c

def z1380 : W := mkw 0x110c022580505041 0x0110c02258050504 0x55060661847070c4 0x455060661847070c

def z1381 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x11c7866184f0f0c5 0x711c7866184f0f0c

def z1382 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1187066184f07000 0x61187066184f0700

def z1383 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dffbe6784f0f0c5 0x75dffbe6784f0f0c

def z1384 : W := mkw 0x1104022500101000 0x0110402250010100 0x01c7866004f03001 0x701c7866004f0300

def z1385 : W := mkw 0x0409000088414151 0x0040900008841415 0xfffbc1999bcfcfff 0xffffbc1999bcfcff

def z1386 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3c3fb8780773ff0c 0xf3c3fb8780773ff0

def z1387 : W := mkw 0x0008000080404041 0x0000800008040404 0x5dc7866184f0f0c5 0x75dc7866184f0f0c

def z1388 : W := mkw 0xc3c02fa5572a0006 0x2c3c02fa5572a000 0xc3c04787ffff0003 0xfc3c04787ffff000

def z1389 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xff6ebefff8000000 0x0ff6ebefff800000

def z1390 : W := mkw 0x42002580002a0000 0x242002580002a000 0x03e67f8000ff0003 0x003e67f8000ff000

def z1391 : W := mkw 0x28120002208484a0 0x828120002208484a 0xee184116628c8cff 0xbee184116628c8cf

def z1392 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dc7866786f0fccd 0xf5dc7866786f0fcc

def z1393 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5dc7866784f0f3fd 0x75dc7866784f0f3f

def z1394 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c87866004b0f004 0x71c87866004b0f00

def z1395 : W := mkw 0x0409000088414151 0x0040900008841415 0xb32a0089994343ff 0xdb32a0089994343f

def z1396 : W := mkw 0x1104022500101000 0x0110402250010100 0x1c0786600430f004 0x71c0786600430f00

def z1397 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfebd3ffff8000000 0x0febd3ffff800000

def z1398 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x02bd7f8007ff0003 0xf02bd7f8007ff000

def z1399 : W := mkw 0x6c5b0802afefc5f3 0x86c5b0802afefc5f 0x0000400007ffcfff 0xf0000400007ffcff

def z1400 : W := mkw 0x3114022700909080 0x0311402270090908 0x5dc7866784b0b0c5 0x35dc7866784b0b0c

def z1401 : W := mkw 0x110c022580505041 0x0110c02258050504 0x1dc7866184f0f005 0x71dc7866184f0f00

def z1402 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5546866184f0f0c5 0x75546866184f0f0c

def z1403 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffcf866785f3f3ff 0xfffcf866785f3f3f

def z1404 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x7def86ef9df3f3cd 0xf7def86ef9df3f3c

def z1405 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff8f00001 0x0ffffbffff8f0000

def z1406 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x18953f7ff8000000 0x018953f7ff800000

def z1407 : W := mkw 0x28120002208484a0 0x828120002208484a 0xeef9c19e7a8c8cff 0xbeef9c19e7a8c8cf

def z1408 : W := mkw 0x3114022700909080 0x0311402270090908 0x0885066604b0b0c5 0x30885066604b0b0c

def z1409 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x0004066004f0f0c5 0x70004066004f0f0c

def z1410 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5dc7866784f3f0f7 0x75dc7866784f3f0f

def z1411 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3c3fb8780500ff0c 0x43c3fb8780500ff0

def z1412 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0x11a63feff8000000 0x011a63feff800000

def z1413 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xddc786679cf0f0f5 0x7ddc786679cf0f0f

def z1414 : W := mkw 0x3114022700909080 0x0311402270090908 0x0895077664b0b000 0x20895077664b0b00

def z1415 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5ddf866786f0f0c5 0xf5ddf866786f0f0c

def z1416 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8007ff00ff 0xf03ffff8007ff00f

def z1417 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03ffff8007fff007 0xf03ffff8007fff00

def z1418 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0x5dc7866f9cf0f3c5 0x75dc7866f9cf0f3c

def z1419 : W := mkw 0x150d022588515151 0x0150d02258851515 0x110606699c707300 0x4110606699c70730

def z1420 : W := mkw 0x28120002208484a0 0x828120002208484a 0xe2d84116628c8cff 0xbe2d84116628c8cf

def z1421 : W := mkw 0x3114022700909080 0x0311402270090908 0xeecd866604b0b0ff 0xbeecd866604b0b0f

def z1422 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfdd7bf7ff8000000 0x0fdd7bf7ff800000

def z1423 : W := mkw 0x0409000088414151 0x0040900008841415 0xf5220089994343ff 0xdf5220089994343f

def z1424 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xffef86ef9df3f3c5 0x7ffef86ef9df3f3c

def z1425 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xfffffffffaff0003 0xbfffffffffaff000

def z1426 : W := mkw 0xc2c02d80572a0006 0x2c2c02d80572a000 0x83ffff807fff0003 0xf83ffff807fff000

def z1427 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfffbc19ffb8ccfff 0xffffbc19ffb8ccff

def z1428 : W := mkw 0x42602d80072a2a02 0x242602d80072a2a0 0x1fffffe007ffff0f 0xf1fffffe007ffff0

def z1429 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x03e7ff8005ff0003 0x703e7ff8005ff000

def z1430 : W := mkw 0x1104022500101000 0x0110402250010100 0x1006066004307000 0x4100606600430700

def z1431 : W := mkw 0x838027a550000004 0x2838027a55000000 0xefffbf97f8000000 0x0efffbf97f800000

def z1432 : W := mkw 0x28120002208484a0 0x828120002208484a 0x0ad9c116628c8cff 0xb0ad9c116628c8cf

def z1433 : W := mkw 0x838027a550000004 0x2838027a55000000 0xc3f83f87f8000000 0x0c3f83f87f800000

def z1434 : W := mkw 0x110c022580505041 0x0110c02258050504 0x11c6066184f07001 0x411c6066184f0700

def z1435 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x2c1db8700700ff0c 0xf2c1db8700700ff0

def z1436 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0x5dc7c66786fcfcc5 0x75dc7c66786fcfcc

def z1437 : W := mkw 0x0409000088414151 0x0040900008841415 0xd3620089994343ff 0xdd3620089994343f

def z1438 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x190606678470f000 0x4190606678470f00

def z1439 : W := mkw 0x28120002208484a0 0x828120002208484a 0xfedbc116628cccff 0xffedbc116628cccf

def z1440 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xf76e86e99df3f3ff 0xff76e86e99df3f3f

def z1441 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0xbe3fb8f81f00ff0c 0xfbe3fb8f81f00ff0

def z1442 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x182638780500ff00 0x4182638780500ff0

def z1443 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x5dd7c76786fcf0c5 0x75dd7c76786fcf0c

def z1444 : W := mkw 0x0060185807002a0a 0x10060185807002a0 0x3d7fb8780740ff0d 0xf3d7fb8780740ff0

def z1445 : W := mkw 0x40601858072a2a0a 0x140601858072a2a0 0x3c3ff87807bcff0c 0xf3c3ff87807bcff0

def z1446 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xdfd7bff7f8000000 0x0dfd7bff7f800000

def z1447 : W := mkw 0x391e0227a0d4d4e1 0x8391e0227a0d4d4e 0xffcfc767e4fcf0ff 0xfffcfc767e4fcf0f

def z1448 : W := mkw 0x42402d80072a0002 0x242402d80072a000 0x01b77f8007ff0003 0xf01b77f8007ff000

def z1449 : W := mkw 0x838027a550000004 0x2838027a55000000 0xdfffbfe7f8000000 0x0dfffbfe7f800000

def z1450 : W := mkw 0xc38037fd502a000c 0x3c38037fd502a000 0xfffffffff80f0002 0x0fffffffff80f000

def z1451 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xffffbffff9430000 0x4ffffbffff943000

def z1452 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x0985066784f0b000 0x20985066784f0b00

def z1453 : W := mkw 0x3d1f0227a8d5d5f1 0x83d1f0227a8d5d5f 0xffdfc77ffefcffff 0xfffdfc77ffefcfff

def z1454 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xfde7befff8000000 0x0fde7befff800000

def z1455 : W := mkw 0x838037fd5000000c 0x3838037fd5000000 0xbbbf3ffff8000000 0x0bbbf3ffff800000

def z1456 : W := mkw 0x39160227209494a0 0x839160227209494a 0xec85067664b0bcfc 0x2ec85067664b0bcf

def z1457 : W := mkw 0x351d022788d1d1d1 0x0351d022788d1d1d 0xfdc7866f9df3f3ff 0xffdc7866f9df3f3f

def z1458 : W := mkw 0x311c022780d0d0c1 0x0311c022780d0d0c 0x1d87866784f0f004 0x71d87866784f0f00

def z1459 : W := mkw 0x0100022500000000 0x0010002250000000 0x5dc7866784f0f005 0x75dc7866784f0f00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z8,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z9,z5,z6]),(0,[z10,z7,z2,z3,z11,z5,z6]),(0,[z12,z13,z2,z3,z4,z5,z6]),(0,[z12,z7,z2,z3,z4,z5,z14]),(0,[z15,z7,z2,z3,z4,z5,z6])],[(0,[z7,z16,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z18,z19,z6])],[(0,[z7,z2,z3,z4,z5,z20,z6]),(0,[z7,z2,z21,z3,z22,z5,z6]),(0,[z7,z2,z23,z3,z24,z5,z6]),(0,[z7,z2,z3,z22,z5,z6,z25]),(0,[z7,z2,z3,z22,z26,z5,z6]),(0,[z7,z2,z3,z4,z5,z27,z6])],[(0,[z7,z2,z3,z28,z4,z5,z6]),(0,[z7,z29,z2,z3,z4,z5,z6]),(0,[z30,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z31,z5,z6]),(0,[z7,z2,z3,z4,z18,z5,z32])],[(0,[z33,z2,z3,z4,z5,z34,z6]),(0,[z7,z2,z35,z3,z4,z5,z6])],[(0,[z7,z2,z3,z11,z5,z6,z36]),(1,[z7,z2,z3,z4,z37,z6]),(0,[z7,z2,z3,z4,z5,z6,z38]),(0,[z7,z39,z21,z3,z4,z5,z6]),(0,[z7,z40,z39,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z41]),(1,[z7,z40,z3,z4,z5,z42]),(1,[z7,z2,z3,z4,z5,z43])],[(0,[z44,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z4,z5,z6]),(0,[z46,z7,z2,z3,z4,z5,z47]),(0,[z7,z2,z21,z4,z5,z6,z25]),(0,[z7,z2,z3,z11,z11,z5,z6]),(0,[z48,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z22,z5,z49,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z50,z6]),(0,[z51,z7,z2,z52,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z53]),(0,[z54,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z55]),(0,[z7,z2,z3,z56,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z57,z6])],[(0,[z7,z2,z3,z4,z5,z47,z6]),(0,[z7,z2,z58,z21,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z59]),(0,[z7,z2,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z24,z60,z5,z6]),(0,[z61,z7,z2,z3,z56,z5,z6]),(0,[z7,z2,z62,z3,z63,z5,z6]),(0,[z64,z7,z2,z3,z4,z5,z6])],[(0,[z65,z7,z66,z3,z4,z5,z6]),(0,[z67,z7,z2,z3,z4,z68,z6]),(1,[z7,z2,z69,z4,z5,z6]),(0,[z7,z2,z70,z3,z4,z5,z6])],[(0,[z71,z2,z3,z28,z4,z5,z6]),(0,[z71,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z72,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z73,z6]),(0,[z7,z2,z3,z4,z5,z74,z6]),(1,[z75,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z76,z6,z32])],[],[(0,[z7,z2,z3,z4,z5,z77,z6]),(0,[z7,z2,z3,z4,z5,z78,z6]),(0,[z7,z2,z3,z4,z5,z6,z36]),(0,[z7,z2,z3,z22,z5,z79,z6]),(0,[z7,z2,z3,z80,z4,z5,z6]),(0,[z7,z2,z3,z4,z81,z5,z6]),(0,[z7,z2,z3,z4,z82,z5,z6]),(0,[z7,z83,z2,z3,z4,z5,z76])],[(0,[z7,z2,z84,z3,z22,z5,z6]),(0,[z0,z33,z2,z3,z4,z5,z6]),(1,[z33,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z4,z11,z5,z6]),(0,[z7,z85,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z86,z6]),(0,[z7,z2,z3,z4,z87,z5,z88]),(1,[z30,z7,z3,z11,z5,z6]),(0,[z89,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z24,z5,z42,z6]),(0,[z7,z40,z2,z3,z90,z5,z6])],[(0,[z91,z7,z2,z3,z4,z5,z6]),(0,[z92,z7,z2,z3,z4,z5,z6]),(0,[z93,z7,z2,z62,z4,z5,z6]),(0,[z7,z94,z2,z3,z4,z5,z6])],[(0,[z7,z39,z84,z3,z4,z5,z6]),(0,[z67,z7,z2,z3,z4,z87,z6]),(0,[z67,z7,z2,z3,z22,z5,z6]),(0,[z33,z7,z2,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z5,z34]),(0,[z95,z7,z2,z3,z4,z96,z6]),(0,[z97,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z22,z5,z98,z6]),(0,[z7,z2,z3,z4,z5,z99,z32])],[(0,[z100,z7,z2,z3,z4,z5,z6]),(0,[z2,z3,z28,z4,z101,z5,z6]),(0,[z7,z2,z3,z11,z5,z34,z6]),(0,[z95,z7,z2,z3,z4,z102,z6]),(0,[z7,z21,z3,z103,z4,z5,z6]),(0,[z7,z2,z3,z104,z11,z5,z6]),(0,[z7,z2,z105,z3,z24,z5,z6]),(0,[z75,z7,z2,z3,z4,z5,z6]),(0,[z12,z7,z2,z3,z106,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z107]),(1,[z7,z108,z2,z3,z5,z99])],[(0,[z71,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z60,z19,z6]),(0,[z7,z2,z3,z4,z19,z6,z32]),(0,[z7,z2,z3,z4,z5,z73,z6])],[(0,[z7,z2,z3,z4,z5,z109,z6]),(1,[z7,z2,z110,z4,z5,z6]),(0,[z0,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z5,z111,z6]),(0,[z7,z39,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z112,z5,z6]),(0,[z113,z7,z2,z3,z24,z5,z6]),(0,[z114,z7,z2,z3,z24,z5,z6])],[(0,[z7,z39,z3,z4,z5,z6,z115]),(0,[z7,z3,z4,z11,z5,z116,z6]),(0,[z7,z2,z3,z4,z5,z117,z6]),(0,[z7,z2,z17,z8,z3,z5,z6])],[(0,[z118,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z5,z119,z6]),(0,[z7,z2,z17,z3,z87,z5,z6]),(0,[z7,z2,z17,z3,z24,z5,z6]),(0,[z7,z2,z3,z120,z22,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z121,z5,z6]),(0,[z122,z7,z2,z3,z4,z5,z123]),(0,[z7,z124,z2,z17,z3,z5,z6]),(0,[z7,z2,z125,z4,z22,z5,z6]),(0,[z7,z126,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z101,z22,z5,z6]),(0,[z93,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z127,z6])],[(1,[z7,z84,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z128,z6]),(0,[z7,z2,z3,z129,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z130,z6]),(0,[z7,z2,z3,z4,z131,z5,z6]),(1,[z7,z2,z3,z4,z5,z132]),(0,[z7,z2,z133,z3,z4,z5,z6]),(0,[z7,z2,z3,z134,z4,z5,z6])],[(0,[z135,z7,z2,z3,z4,z5,z6]),(0,[z46,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z136,z4,z5,z6]),(0,[z7,z137,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z34,z6]),(0,[z7,z2,z138,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z14])],[(0,[z7,z2,z3,z4,z139,z5,z6]),(0,[z7,z2,z17,z3,z5,z68,z6]),(0,[z7,z2,z3,z4,z5,z42,z32]),(0,[z7,z2,z3,z22,z5,z76,z6]),(0,[z7,z2,z3,z4,z98,z6,z32])],[(0,[z140,z7,z2,z3,z4,z5,z6]),(0,[z46,z7,z141,z3,z4,z5,z6]),(0,[z7,z2,z3,z142,z4,z5,z6]),(0,[z0,z7,z2,z3,z22,z5,z6]),(0,[z113,z7,z2,z3,z22,z5,z6]),(1,[z7,z2,z3,z143,z5,z6]),(0,[z114,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z144,z6])],[(0,[z7,z2,z3,z4,z5,z145,z6]),(0,[z46,z7,z2,z136,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z146,z6]),(0,[z7,z40,z2,z3,z24,z5,z6])],[(0,[z7,z2,z3,z147,z4,z5,z6]),(0,[z7,z2,z3,z24,z87,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z36]),(0,[z7,z2,z3,z24,z24,z5,z6]),(0,[z113,z7,z2,z3,z4,z5,z148])]],
   [[(0,[z1,z2,z84,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z149,z6]),(0,[z7,z2,z3,z4,z5,z115,z32]),(0,[z150,z7,z2,z3,z4,z5,z6]),(0,[z7,z108,z2,z17,z3,z5,z6])],[(0,[z33,z51,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z151,z6]),(0,[z152,z7,z2,z3,z4,z5,z6]),(0,[z153,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z154,z4,z5,z6]),(0,[z7,z2,z21,z52,z4,z5,z6]),(0,[z46,z7,z2,z3,z101,z5,z6]),(0,[z7,z2,z3,z155,z4,z5,z6]),(0,[z61,z7,z2,z3,z4,z5,z115]),(0,[z7,z2,z3,z4,z120,z5,z6]),(0,[z7,z2,z17,z3,z19,z5,z6])],[(0,[z48,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z156,z3,z4,z5,z6]),(0,[z157,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z158,z6]),(0,[z7,z2,z3,z4,z159,z5,z6]),(1,[z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z17,z3,z5,z160,z6]),(0,[z7,z2,z3,z4,z63,z5,z6])],[(0,[z161,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z162,z5,z6]),(0,[z7,z2,z3,z24,z5,z68,z6]),(0,[z7,z2,z3,z4,z18,z5,z36]),(0,[z7,z163,z2,z3,z4,z5,z6]),(0,[z7,z2,z164,z17,z4,z5,z6]),(1,[z165,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z5,z73,z6,z25])],[(0,[z166,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z148]),(0,[z7,z2,z3,z4,z5,z167,z6]),(0,[z7,z168,z2,z3,z4,z5,z6]),(0,[z7,z2,z169,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z170,z6]),(0,[z51,z7,z2,z3,z11,z5,z6]),(1,[z7,z2,z52,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z171]),(0,[z7,z2,z3,z11,z172,z5,z6]),(0,[z173,z7,z2,z3,z4,z5,z6]),(0,[z7,z40,z2,z3,z22,z5,z6]),(1,[z7,z2,z3,z4,z174,z6]),(0,[z7,z2,z3,z4,z5,z76,z73])],[(0,[z95,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z23,z3,z4,z5,z6]),(0,[z61,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z24,z22,z5,z6]),(0,[z7,z2,z3,z69,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z175]),(0,[z176,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z174,z5,z6]),(0,[z114,z7,z2,z3,z4,z5,z177])]],
   [[(0,[z7,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z52,z4,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z36,z99]),(0,[z7,z2,z3,z4,z5,z34,z73]),(0,[z30,z7,z3,z4,z11,z5,z6]),(0,[z178,z7,z2,z3,z4,z5,z6])],[(0,[z7,z66,z2,z3,z179,z5,z6]),(0,[z7,z2,z3,z4,z5,z180,z6]),(0,[z7,z2,z3,z11,z5,z6,z32]),(0,[z7,z2,z3,z181,z4,z5,z6])],[(0,[z7,z2,z3,z4,z182,z5,z6]),(0,[z7,z2,z183,z3,z4,z5,z6]),(0,[z7,z2,z184,z3,z4,z5,z6]),(0,[z1,z71,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z18,z98,z6]),(1,[z7,z2,z3,z185,z5,z6]),(0,[z114,z7,z2,z3,z104,z5,z6])],[(0,[z65,z118,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z186]),(0,[z187,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z188,z5,z6]),(0,[z30,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z189]),(0,[z7,z2,z3,z4,z190,z5,z6]),(0,[z7,z108,z2,z3,z4,z5,z49])],[(0,[z7,z2,z191,z3,z4,z5,z6]),(0,[z7,z2,z3,z192,z4,z5,z6])],[(0,[z113,z7,z2,z3,z4,z60,z6]),(0,[z7,z2,z193,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z177]),(0,[z7,z2,z3,z4,z5,z76,z99])],[(0,[z7,z2,z2,z3,z4,z5,z6]),(0,[z194,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z98,z6]),(0,[z7,z2,z3,z4,z172,z5,z6]),(1,[z195,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z134,z4,z5,z99])],[(0,[z7,z66,z3,z103,z4,z5,z6]),(0,[z7,z2,z196,z3,z4,z5,z6]),(0,[z7,z2,z3,z197,z24,z5,z6]),(0,[z7,z2,z3,z4,z198,z5,z6]),(0,[z7,z2,z199,z3,z4,z5,z6]),(0,[z200,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z71,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z201,z4,z5,z6]),(0,[z202,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z73,z115]),(0,[z7,z2,z17,z3,z203,z5,z6])],[(0,[z65,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z204,z6]),(0,[z7,z2,z3,z205,z24,z5,z6]),(0,[z113,z7,z2,z3,z4,z116,z6]),(0,[z7,z2,z3,z4,z5,z6,z32])],[(0,[z7,z206,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z207,z6]),(0,[z7,z208,z2,z3,z4,z5,z6])],[(0,[z33,z7,z2,z3,z11,z5,z6]),(0,[z7,z209,z3,z4,z5,z116,z6]),(0,[z7,z2,z17,z3,z18,z5,z6])],[(0,[z7,z2,z210,z3,z4,z5,z6]),(0,[z46,z7,z2,z110,z4,z5,z6]),(0,[z7,z2,z3,z4,z87,z76,z6]),(0,[z7,z2,z3,z4,z5,z6,z211]),(1,[z7,z2,z105,z3,z5,z6]),(0,[z7,z2,z3,z24,z5,z212,z6]),(0,[z7,z2,z3,z24,z104,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z213])],[(0,[z7,z2,z3,z4,z5,z6,z214]),(0,[z7,z2,z3,z4,z5,z6,z215]),(0,[z95,z7,z2,z3,z216,z5,z6]),(0,[z7,z124,z3,z103,z4,z5,z6])],[(0,[z33,z2,z3,z217,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z98,z6]),(0,[z7,z2,z218,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z5,z32])],[(0,[z7,z2,z3,z4,z5,z219,z6]),(0,[z7,z2,z220,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z221,z5,z6]),(0,[z7,z2,z222,z103,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z116,z6]),(0,[z7,z2,z3,z4,z5,z223,z6]),(0,[z7,z2,z3,z4,z60,z6,z32]),(1,[z7,z224,z3,z4,z5,z6]),(0,[z7,z2,z3,z225,z4,z5,z6])]],
   [[(0,[z226,z7,z2,z3,z4,z5,z6]),(0,[z118,z7,z84,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z227,z6]),(0,[z228,z7,z2,z3,z4,z5,z6]),(0,[z229,z7,z2,z3,z4,z5,z6]),(0,[z92,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z222,z4,z22,z5,z6]),(0,[z7,z230,z2,z17,z3,z5,z6])],[(0,[z231,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z95,z7,z2,z103,z4,z5,z6]),(0,[z7,z2,z62,z3,z11,z5,z6]),(0,[z7,z83,z2,z3,z11,z5,z6]),(0,[z113,z7,z2,z3,z4,z5,z6]),(0,[z114,z7,z2,z3,z4,z5,z6])],[(0,[z232,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z233,z5,z6]),(0,[z7,z2,z125,z3,z24,z5,z6]),(0,[z113,z7,z2,z234,z4,z5,z6]),(0,[z114,z7,z235,z3,z4,z5,z6])],[(0,[z122,z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z3,z11,z5,z6,z25]),(0,[z7,z2,z17,z3,z4,z5,z6]),(0,[z93,z7,z2,z17,z3,z5,z6])],[(0,[z7,z2,z3,z236,z4,z5,z6]),(1,[z46,z2,z3,z101,z5,z6]),(0,[z2,z3,z4,z5,z68,z34,z6]),(0,[z1,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z5,z42,z36]),(0,[z7,z39,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z237,z5,z6])],[(0,[z7,z2,z3,z4,z238,z5,z6]),(0,[z7,z2,z164,z4,z5,z98,z6]),(0,[z239,z7,z2,z3,z4,z5,z6]),(0,[z12,z7,z2,z3,z4,z98,z6]),(0,[z7,z240,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z241])],[(0,[z7,z2,z210,z52,z3,z5,z6]),(0,[z114,z46,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z242,z5,z6]),(0,[z7,z2,z164,z3,z24,z5,z6]),(0,[z7,z2,z3,z243,z22,z5,z6]),(0,[z7,z2,z3,z244,z4,z5,z6]),(0,[z7,z245,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z134,z5,z49])],[(0,[z7,z2,z3,z4,z5,z246,z6]),(0,[z46,z7,z2,z3,z4,z149,z6]),(0,[z7,z2,z247,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z49,z6]),(0,[z7,z2,z3,z4,z5,z6,z248]),(0,[z7,z2,z17,z125,z3,z5,z6]),(0,[z7,z2,z3,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z249,z6])]],
   [[(0,[z7,z2,z21,z3,z11,z5,z6]),(0,[z7,z2,z3,z250,z4,z5,z6]),(1,[z7,z2,z234,z4,z5,z6]),(0,[z7,z2,z251,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z252,z6]),(0,[z253,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z6,z115]),(0,[z7,z2,z3,z4,z254,z5,z6]),(0,[z7,z2,z3,z4,z5,z255,z6]),(0,[z7,z2,z3,z134,z22,z5,z6])],[(0,[z46,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z17,z3,z101,z5,z6]),(0,[z7,z2,z3,z4,z5,z256,z6]),(1,[z7,z2,z3,z4,z5,z88]),(0,[z7,z40,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z24,z4,z5,z6]),(1,[z7,z2,z3,z56,z5,z6]),(0,[z7,z2,z3,z257,z4,z5,z6]),(0,[z7,z2,z3,z4,z26,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z25])],[(0,[z7,z2,z3,z4,z68,z116,z6]),(0,[z1,z7,z2,z3,z4,z87,z6]),(0,[z1,z7,z2,z3,z22,z5,z6]),(0,[z48,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z258,z3,z4,z5,z6])],[(0,[z7,z2,z17,z52,z3,z5,z6]),(0,[z7,z259,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z260,z6]),(0,[z7,z261,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z60,z5,z6]),(0,[z61,z7,z40,z3,z4,z5,z6])],[(0,[z7,z2,z3,z262,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z263]),(0,[z7,z2,z3,z4,z5,z264,z6]),(0,[z7,z2,z3,z11,z5,z79,z6]),(0,[z7,z2,z3,z4,z5,z6,z265]),(0,[z7,z2,z164,z3,z22,z5,z6])],[(0,[z7,z2,z266,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z267,z5,z6]),(0,[z7,z2,z3,z4,z5,z49,z6])]],
   [[(1,[z7,z2,z3,z4,z5,z268]),(0,[z51,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z222,z3,z4,z98,z6]),(0,[z7,z2,z222,z3,z269,z5,z6]),(0,[z93,z270,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z87,z5,z271]),(0,[z95,z7,z2,z17,z3,z5,z6]),(0,[z61,z7,z2,z17,z3,z5,z6])],[(0,[z272,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z52,z3,z24,z5,z6]),(0,[z273,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z274,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z101,z5,z6]),(1,[z7,z2,z3,z237,z5,z6]),(1,[z7,z2,z164,z17,z5,z6])],[(0,[z51,z2,z52,z3,z4,z5,z6]),(1,[z71,z2,z3,z28,z5,z6]),(0,[z33,z7,z2,z3,z4,z5,z76]),(1,[z7,z2,z3,z4,z96,z6]),(0,[z7,z2,z62,z103,z4,z5,z6]),(0,[z7,z3,z24,z4,z11,z5,z6]),(0,[z7,z275,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z42,z6]),(0,[z7,z2,z276,z3,z4,z5,z6]),(0,[z12,z7,z2,z222,z4,z5,z6]),(0,[z7,z2,z3,z4,z106,z5,z6]),(0,[z7,z277,z2,z3,z4,z5,z6])],[(0,[z65,z7,z2,z3,z182,z5,z6]),(0,[z7,z2,z84,z3,z11,z5,z6]),(0,[z278,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z102,z6]),(0,[z7,z2,z3,z4,z96,z5,z6]),(0,[z7,z3,z103,z4,z5,z116,z6])],[(1,[z114,z7,z2,z3,z79,z6])],[(1,[z7,z279,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z149,z5,z6]),(0,[z7,z2,z3,z4,z280,z5,z6]),(0,[z12,z7,z281,z3,z4,z5,z6]),(0,[z7,z2,z3,z104,z4,z79,z6]),(0,[z7,z2,z3,z4,z5,z79,z6]),(0,[z7,z2,z3,z4,z5,z282,z6]),(0,[z283,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z284,z4,z5,z6]),(0,[z67,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z271]),(0,[z7,z2,z3,z285,z4,z5,z6]),(0,[z33,z7,z2,z3,z4,z5,z34]),(0,[z286,z7,z2,z3,z4,z5,z6]),(0,[z95,z7,z2,z3,z221,z5,z6]),(0,[z12,z7,z2,z3,z24,z5,z6])]],
   [[(0,[z287,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z288]),(0,[z289,z7,z2,z3,z4,z5,z6]),(0,[z7,z290,z2,z3,z4,z5,z6]),(0,[z7,z165,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z291,z6]),(0,[z7,z2,z3,z4,z18,z76,z6])],[(1,[z51,z2,z52,z4,z5,z6]),(0,[z71,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z87,z98,z6]),(0,[z7,z2,z292,z3,z4,z5,z6]),(0,[z293,z7,z2,z3,z4,z5,z6])],[(0,[z65,z7,z2,z294,z4,z5,z6]),(0,[z7,z2,z3,z4,z295,z5,z6]),(0,[z7,z2,z296,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z73,z36]),(0,[z7,z297,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z298]),(0,[z7,z2,z3,z22,z19,z5,z6]),(0,[z7,z2,z3,z4,z299,z5,z6])],[(0,[z65,z7,z2,z17,z3,z5,z6]),(0,[z7,z39,z66,z3,z4,z5,z6]),(0,[z7,z2,z21,z217,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z6]),(0,[z7,z2,z3,z197,z4,z5,z6]),(0,[z7,z2,z300,z3,z4,z5,z6])],[(0,[z7,z2,z3,z11,z5,z76,z6]),(0,[z301,z7,z2,z3,z4,z5,z6])],[(0,[z2,z84,z3,z217,z4,z5,z6]),(0,[z302,z7,z2,z3,z4,z5,z6]),(0,[z33,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z205,z4,z5,z6]),(0,[z303,z7,z2,z3,z4,z5,z6])],[(0,[z304,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z101,z11,z5,z6]),(0,[z7,z83,z2,z3,z4,z5,z36]),(0,[z7,z2,z305,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z306])],[(1,[z7,z2,z217,z22,z5,z6]),(0,[z307,z7,z2,z3,z4,z5,z6]),(0,[z308,z7,z2,z3,z4,z5,z6]),(0,[z114,z7,z2,z3,z4,z5,z132]),(0,[z309,z7,z2,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z6,z32])]],
   [[(0,[z7,z2,z3,z310,z4,z5,z6])],[(0,[z65,z7,z2,z3,z4,z311,z6]),(0,[z7,z2,z3,z4,z5,z312,z6]),(0,[z313,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z314,z5,z6]),(0,[z7,z315,z2,z3,z4,z5,z6]),(0,[z61,z7,z2,z3,z254,z5,z6]),(1,[z7,z2,z3,z106,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z316])],[(0,[z7,z317,z2,z3,z4,z5,z6]),(0,[z318,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z319,z3,z4,z5,z6]),(0,[z114,z7,z2,z3,z11,z5,z6]),(0,[z7,z320,z2,z3,z4,z5,z6]),(0,[z7,z195,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z3,z4,z5,z6]),(0,[z7,z2,z321,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z322,z5,z6]),(0,[z7,z2,z17,z62,z3,z5,z6]),(0,[z7,z83,z2,z17,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z323]),(0,[z7,z2,z3,z4,z5,z324,z6]),(0,[z7,z2,z3,z234,z4,z5,z6]),(0,[z7,z124,z3,z4,z60,z5,z6]),(0,[z7,z2,z3,z4,z5,z76,z6])],[(0,[z46,z7,z2,z3,z28,z5,z6]),(0,[z7,z2,z325,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z6,z53]),(0,[z7,z2,z3,z4,z5,z6,z326])],[(0,[z7,z2,z327,z3,z4,z5,z6]),(0,[z7,z2,z3,z22,z5,z6,z328]),(0,[z7,z2,z3,z4,z5,z6,z329])],[(0,[z7,z2,z330,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z123]),(0,[z7,z2,z3,z4,z5,z331,z6]),(0,[z332,z7,z2,z3,z4,z5,z6]),(0,[z95,z7,z2,z3,z4,z5,z333]),(0,[z7,z2,z3,z11,z5,z6,z334]),(0,[z7,z335,z2,z3,z4,z5,z6]),(0,[z7,z336,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z337])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z338]),(0,[z1,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z339,z5,z6]),(0,[z7,z2,z3,z22,z203,z5,z6]),(0,[z7,z2,z3,z4,z5,z340,z6]),(0,[z7,z2,z3,z4,z341,z5,z6]),(0,[z7,z2,z342,z3,z4,z5,z6]),(0,[z343,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z344,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z345,z6]),(0,[z7,z2,z3,z346,z4,z5,z6]),(0,[z7,z2,z3,z22,z5,z6,z99]),(0,[z7,z2,z17,z3,z5,z73,z6]),(0,[z7,z83,z2,z3,z4,z18,z6])],[(0,[z118,z7,z2,z3,z22,z5,z6]),(0,[z347,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z348,z6]),(0,[z7,z2,z3,z4,z349,z5,z6]),(0,[z7,z2,z110,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z350,z5,z6]),(0,[z7,z2,z3,z4,z351,z5,z6]),(0,[z7,z2,z352,z3,z4,z5,z6]),(0,[z353,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z164,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z22,z5,z6])],[(0,[z354,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z6,z36]),(0,[z7,z40,z2,z3,z11,z5,z6]),(0,[z355,z7,z2,z3,z24,z5,z6]),(1,[z7,z2,z125,z22,z5,z6]),(0,[z7,z2,z3,z22,z18,z5,z6])],[(0,[z356,z7,z2,z3,z4,z5,z6]),(0,[z118,z2,z3,z4,z5,z6,z36]),(0,[z7,z2,z3,z24,z11,z5,z6])],[(0,[z122,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z164,z52,z4,z5,z6]),(0,[z7,z2,z357,z3,z4,z5,z6]),(0,[z7,z2,z3,z358,z4,z5,z6]),(1,[z7,z2,z62,z4,z5,z73]),(1,[z7,z2,z3,z104,z203,z6])],[(0,[z95,z7,z3,z103,z4,z5,z6]),(1,[z7,z2,z3,z359,z5,z6]),(0,[z7,z261,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z360,z5,z6]),(0,[z48,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z361,z6]),(0,[z7,z2,z3,z4,z5,z362,z6]),(0,[z7,z2,z3,z363,z4,z5,z6])],[(0,[z7,z2,z3,z4,z311,z5,z6]),(1,[z122,z2,z217,z4,z5,z6]),(0,[z7,z2,z364,z3,z4,z5,z6]),(0,[z7,z365,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z334]),(0,[z7,z2,z3,z22,z5,z116,z6]),(0,[z7,z2,z3,z4,z5,z6,z366]),(0,[z7,z2,z367,z3,z4,z5,z6])]],
   [[(0,[z7,z66,z2,z3,z24,z5,z6]),(1,[z7,z2,z3,z4,z5,z368]),(0,[z7,z2,z3,z28,z11,z5,z6]),(0,[z369,z7,z2,z3,z4,z5,z6]),(0,[z30,z7,z2,z3,z11,z5,z6]),(1,[z370,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z371,z4,z5,z6]),(0,[z7,z2,z372,z3,z4,z5,z6]),(0,[z51,z2,z3,z4,z5,z68,z6]),(1,[z7,z2,z210,z3,z5,z6]),(0,[z7,z2,z3,z4,z87,z79,z6]),(0,[z7,z2,z3,z24,z5,z73,z6])],[(0,[z7,z2,z294,z3,z4,z5,z6]),(0,[z7,z84,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z373,z5,z6]),(0,[z7,z2,z3,z4,z5,z374,z6]),(0,[z7,z2,z3,z22,z375,z5,z6])],[(0,[z7,z2,z3,z217,z24,z5,z6]),(0,[z113,z195,z2,z3,z4,z5,z6]),(0,[z93,z7,z2,z3,z4,z5,z25]),(0,[z376,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z377,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z333]),(0,[z61,z7,z2,z300,z4,z5,z6])],[(0,[z378,z7,z2,z3,z4,z5,z6]),(0,[z7,z66,z3,z4,z11,z5,z6]),(0,[z122,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z379,z4,z5,z6]),(1,[z380,z7,z2,z3,z5,z6]),(1,[z7,z3,z11,z5,z116,z6]),(0,[z7,z2,z3,z4,z381,z5,z6]),(0,[z7,z2,z3,z4,z5,z382,z6]),(0,[z7,z2,z3,z4,z5,z383,z6]),(0,[z384,z2,z3,z4,z18,z5,z6])],[(0,[z7,z2,z84,z17,z3,z5,z6]),(0,[z7,z2,z52,z3,z4,z5,z6]),(0,[z122,z7,z2,z3,z162,z5,z6]),(0,[z7,z2,z385,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z386,z6]),(0,[z7,z2,z3,z4,z5,z387,z6]),(0,[z187,z7,z2,z17,z3,z5,z6]),(0,[z114,z7,z2,z3,z4,z203,z6])],[(1,[z7,z2,z3,z4,z388,z6]),(0,[z1,z51,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z389]),(0,[z7,z2,z3,z4,z5,z6,z390]),(0,[z7,z2,z3,z4,z5,z391,z6]),(0,[z7,z2,z17,z3,z104,z5,z6]),(0,[z392,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z33,z118,z2,z3,z4,z5,z6]),(0,[z7,z66,z2,z3,z22,z5,z6]),(0,[z7,z2,z393,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z34,z6])],[(0,[z7,z66,z2,z3,z394,z5,z6]),(0,[z67,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z395,z5,z6]),(0,[z396,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z42,z25]),(1,[z7,z342,z3,z4,z5,z6])],[(0,[z71,z7,z2,z3,z28,z5,z6]),(0,[z7,z2,z3,z4,z397,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z76]),(0,[z7,z2,z398,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z399]),(0,[z7,z2,z3,z4,z5,z6,z400]),(0,[z7,z2,z3,z4,z5,z6,z401])],[(0,[z7,z2,z3,z217,z22,z5,z6]),(0,[z71,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z36,z115]),(0,[z33,z7,z2,z3,z4,z5,z32]),(0,[z113,z7,z2,z402,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z403,z6]),(1,[z7,z2,z3,z120,z5,z6]),(0,[z12,z7,z2,z3,z4,z5,z6])],[(0,[z7,z209,z84,z3,z4,z5,z6]),(0,[z7,z2,z3,z404,z4,z5,z6]),(0,[z405,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z406,z5,z6]),(0,[z7,z2,z3,z4,z5,z407,z6]),(1,[z7,z2,z3,z63,z5,z6])],[(0,[z7,z408,z2,z3,z4,z5,z6]),(1,[z7,z3,z24,z11,z5,z6]),(0,[z409,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z410,z3,z24,z5,z6]),(0,[z7,z2,z3,z22,z60,z5,z6]),(0,[z7,z2,z3,z4,z5,z115,z25]),(0,[z411,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z269,z5,z6]),(0,[z93,z412,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z73,z32])],[(0,[z65,z7,z2,z3,z4,z109,z6]),(0,[z7,z2,z3,z4,z413,z5,z6]),(0,[z414,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z4,z5,z37,z6]),(0,[z7,z39,z124,z3,z4,z5,z6]),(0,[z7,z108,z2,z3,z24,z5,z6]),(0,[z415,z7,z2,z3,z4,z5,z6]),(0,[z7,z416,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z417,z6]),(0,[z93,z7,z418,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z263,z6]),(0,[z7,z2,z21,z3,z419,z5,z6]),(0,[z7,z2,z3,z4,z5,z420,z6]),(0,[z7,z2,z3,z421,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z76,z115]),(0,[z7,z2,z17,z3,z5,z6,z422]),(0,[z7,z2,z3,z4,z5,z423,z6]),(0,[z7,z424,z2,z3,z4,z5,z6])],[(0,[z118,z7,z66,z3,z4,z5,z6]),(0,[z425,z7,z2,z3,z4,z5,z6]),(0,[z7,z39,z2,z3,z11,z5,z6]),(1,[z7,z2,z402,z4,z5,z6]),(0,[z7,z2,z426,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z34,z115]),(0,[z7,z2,z105,z3,z4,z5,z6])],[(1,[z7,z2,z3,z182,z5,z6]),(0,[z2,z3,z4,z5,z34,z6,z36]),(0,[z7,z2,z3,z4,z5,z6,z427]),(0,[z7,z2,z3,z22,z5,z42,z6])],[(0,[z7,z2,z17,z3,z5,z6,z115]),(0,[z7,z16,z2,z3,z4,z5,z6]),(0,[z114,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z428,z6])],[(0,[z7,z2,z3,z4,z429,z5,z6]),(0,[z12,z7,z2,z3,z4,z5,z43]),(1,[z384,z2,z3,z4,z5,z6])],[(0,[z118,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z430,z4,z5,z6]),(0,[z431,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z325,z3,z11,z5,z6]),(0,[z7,z2,z3,z134,z11,z5,z6]),(0,[z7,z2,z17,z3,z5,z6,z32])],[(0,[z7,z2,z3,z4,z5,z6,z432]),(0,[z46,z7,z2,z3,z11,z5,z6]),(1,[z7,z2,z3,z4,z238,z6]),(0,[z95,z7,z2,z3,z4,z5,z260]),(0,[z7,z39,z2,z3,z359,z5,z6]),(0,[z7,z2,z3,z4,z5,z306,z6]),(0,[z7,z2,z3,z4,z60,z98,z6]),(1,[z7,z2,z3,z433,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z434])]],
   [[(0,[z122,z7,z2,z3,z4,z435,z6]),(0,[z7,z2,z436,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z68,z6]),(0,[z7,z2,z103,z4,z5,z98,z6]),(0,[z7,z2,z437,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z438,z5,z6])],[(0,[z7,z2,z3,z154,z4,z5,z6]),(1,[z7,z2,z294,z4,z5,z6]),(0,[z1,z7,z2,z3,z11,z5,z6]),(0,[z439,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z440,z3,z4,z5,z6]),(0,[z7,z2,z441,z3,z4,z5,z6])],[(0,[z51,z2,z84,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z442]),(1,[z7,z2,z17,z3,z5,z6]),(0,[z7,z443,z2,z3,z4,z5,z6])],[(0,[z7,z2,z164,z3,z11,z5,z6]),(1,[z61,z7,z3,z4,z5,z115]),(0,[z7,z281,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z444,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z445])],[(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z49,z34]),(0,[z446,z7,z2,z3,z4,z5,z6]),(0,[z7,z124,z2,z3,z447,z5,z6]),(0,[z448,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z449,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z450,z6])],[(0,[z122,z7,z184,z3,z4,z5,z6]),(0,[z7,z2,z451,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z28,z5,z6]),(0,[z7,z452,z2,z3,z4,z5,z6]),(0,[z453,z7,z2,z3,z4,z5,z6]),(0,[z7,z40,z2,z17,z3,z5,z6]),(0,[z7,z2,z125,z3,z22,z5,z6])],[(0,[z7,z2,z3,z24,z5,z6,z32]),(0,[z7,z2,z3,z4,z5,z454,z6])],[(0,[z65,z7,z84,z3,z4,z5,z6]),(0,[z455,z7,z2,z3,z4,z5,z6]),(0,[z46,z7,z2,z3,z4,z5,z368]),(0,[z95,z7,z39,z3,z4,z5,z6]),(0,[z456,z7,z2,z3,z4,z5,z6]),(0,[z355,z7,z2,z3,z4,z5,z6]),(0,[z61,z7,z2,z3,z4,z403,z6])]],
   [[(1,[z7,z2,z3,z4,z311,z6]),(0,[z457,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z221,z5,z6]),(0,[z7,z2,z3,z4,z458,z5,z6])],[(0,[z122,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z419,z5,z6]),(1,[z113,z7,z3,z4,z116,z6]),(0,[z7,z2,z4,z19,z5,z98,z6]),(0,[z459,z7,z2,z3,z4,z5,z6])],[(0,[z380,z7,z2,z3,z5,z68,z6]),(0,[z7,z2,z3,z460,z4,z5,z6]),(0,[z7,z2,z3,z22,z87,z5,z6]),(0,[z7,z2,z3,z4,z5,z461,z6]),(0,[z30,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z11,z19,z5,z6]),(0,[z7,z2,z3,z4,z19,z116,z6]),(0,[z7,z2,z3,z360,z22,z5,z6]),(1,[z13,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z14])],[(0,[z7,z39,z2,z103,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z98,z6]),(0,[z7,z2,z62,z3,z4,z5,z25]),(0,[z7,z2,z462,z3,z4,z5,z6])],[(0,[z7,z66,z2,z3,z4,z5,z6]),(0,[z463,z7,z2,z3,z4,z5,z6]),(0,[z122,z7,z2,z52,z4,z5,z6]),(0,[z7,z2,z3,z464,z4,z5,z6]),(0,[z2,z3,z4,z87,z5,z68,z6]),(0,[z7,z2,z3,z4,z5,z6,z465]),(0,[z7,z2,z3,z4,z466,z5,z6]),(1,[z7,z83,z2,z3,z4,z32]),(0,[z7,z2,z3,z4,z5,z6,z467])],[(0,[z65,z2,z84,z3,z4,z5,z6]),(0,[z118,z51,z2,z3,z4,z5,z6]),(0,[z95,z286,z2,z3,z4,z5,z6]),(0,[z7,z2,z103,z4,z5,z6,z25]),(0,[z7,z2,z3,z103,z375,z5,z6]),(0,[z7,z2,z3,z468,z4,z5,z6])],[(0,[z7,z469,z2,z3,z4,z5,z6]),(0,[z7,z39,z3,z4,z5,z116,z6]),(0,[z7,z2,z3,z4,z470,z5,z6]),(0,[z471,z7,z2,z3,z24,z5,z6]),(0,[z61,z7,z2,z3,z4,z5,z42]),(0,[z7,z472,z2,z3,z4,z5,z6]),(0,[z7,z2,z62,z4,z5,z73,z6]),(0,[z7,z108,z2,z3,z134,z5,z6])],[(0,[z7,z2,z3,z217,z4,z5,z6]),(0,[z7,z2,z3,z22,z5,z68,z6]),(0,[z473,z7,z2,z3,z4,z5,z6]),(0,[z474,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z475,z6]),(0,[z7,z2,z3,z433,z4,z5,z6]),(0,[z7,z2,z218,z222,z3,z5,z6]),(1,[z270,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z476,z5,z6])]],
   [[(0,[z7,z477,z2,z3,z4,z5,z6]),(0,[z7,z478,z2,z3,z4,z5,z6]),(0,[z7,z108,z2,z3,z5,z6,z99])],[(0,[z7,z2,z17,z3,z217,z5,z6]),(0,[z7,z2,z3,z479,z4,z5,z6]),(0,[z7,z2,z3,z216,z4,z5,z6]),(0,[z7,z3,z103,z4,z5,z6,z115]),(0,[z7,z2,z3,z24,z237,z5,z6]),(0,[z93,z7,z2,z3,z24,z5,z6]),(0,[z411,z7,z2,z3,z4,z5,z6]),(0,[z12,z7,z2,z4,z5,z98,z6]),(0,[z7,z2,z480,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z481])],[(0,[z482,z7,z2,z3,z4,z5,z6]),(0,[z67,z2,z3,z4,z5,z68,z6]),(0,[z483,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z484,z5,z6]),(0,[z7,z2,z3,z143,z4,z5,z6]),(1,[z7,z2,z3,z254,z5,z6]),(0,[z7,z2,z3,z22,z22,z5,z6]),(0,[z7,z416,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z19,z5,z6])],[(0,[z485,z7,z2,z3,z4,z5,z6]),(0,[z33,z7,z2,z3,z4,z5,z36]),(0,[z7,z2,z3,z470,z11,z5,z6]),(0,[z7,z2,z3,z11,z5,z486,z6]),(0,[z113,z7,z2,z3,z4,z5,z306])],[(0,[z487,z7,z2,z3,z4,z5,z6]),(0,[z71,z2,z3,z4,z5,z68,z6]),(0,[z7,z370,z2,z3,z4,z5,z6]),(0,[z7,z2,z488,z3,z4,z5,z6])],[(0,[z2,z84,z3,z4,z5,z68,z6]),(0,[z7,z2,z489,z3,z4,z5,z6]),(0,[z7,z2,z52,z3,z22,z5,z6]),(0,[z33,z7,z2,z3,z4,z238,z6]),(0,[z490,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z491,z6]),(0,[z7,z2,z3,z4,z5,z492,z6]),(0,[z7,z2,z493,z3,z4,z5,z6])],[(0,[z7,z2,z164,z217,z4,z5,z6]),(0,[z7,z2,z494,z3,z4,z5,z6]),(0,[z95,z7,z2,z21,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z495]),(0,[z7,z209,z2,z3,z24,z5,z6]),(0,[z496,z7,z2,z3,z4,z5,z6])],[(0,[z7,z497,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z419,z5,z6]),(0,[z7,z2,z3,z4,z498,z5,z6]),(0,[z7,z2,z3,z4,z18,z60,z6]),(0,[z7,z499,z2,z3,z4,z5,z6])]],
   [[(1,[z118,z66,z3,z4,z5,z6]),(0,[z122,z51,z2,z3,z4,z5,z6]),(0,[z122,z7,z279,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z500,z5,z6]),(0,[z7,z2,z3,z11,z203,z5,z6]),(0,[z7,z2,z3,z24,z5,z6,z25]),(0,[z7,z2,z3,z4,z5,z501,z6]),(0,[z7,z2,z3,z4,z502,z5,z6]),(0,[z7,z2,z3,z4,z5,z503,z6])],[(0,[z504,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z6,z99]),(0,[z409,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z410,z3,z4,z5,z6]),(0,[z114,z7,z2,z3,z5,z79,z6])],[(0,[z7,z2,z3,z4,z505,z5,z6]),(0,[z7,z2,z506,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z32]),(0,[z7,z2,z3,z4,z5,z507,z6]),(0,[z113,z7,z124,z3,z4,z5,z6]),(0,[z7,z2,z508,z3,z4,z5,z6]),(0,[z12,z7,z2,z3,z22,z5,z6])],[(0,[z509,z7,z2,z3,z4,z5,z6]),(1,[z67,z2,z3,z4,z68,z6]),(1,[z7,z2,z3,z4,z5,z390]),(0,[z510,z7,z2,z3,z4,z5,z6]),(0,[z7,z39,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z11,z18,z5,z6]),(0,[z7,z2,z3,z4,z5,z486,z6]),(0,[z7,z2,z3,z4,z18,z116,z6]),(0,[z7,z2,z17,z3,z5,z79,z6]),(0,[z93,z7,z2,z3,z4,z491,z6]),(0,[z7,z2,z3,z4,z5,z177,z6]),(0,[z7,z2,z511,z3,z4,z5,z6])],[(0,[z65,z7,z2,z3,z4,z5,z323]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z49,z6])],[(0,[z0,z7,z2,z3,z11,z5,z6]),(0,[z113,z7,z2,z3,z11,z5,z6]),(0,[z10,z7,z2,z3,z4,z5,z6]),(1,[z7,z209,z3,z24,z5,z6]),(0,[z7,z2,z222,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z447,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z512]),(0,[z7,z3,z4,z5,z42,z6,z115]),(0,[z7,z2,z3,z4,z513,z5,z6]),(0,[z7,z2,z3,z4,z5,z25,z32]),(0,[z7,z2,z3,z4,z5,z6,z514]),(1,[z7,z2,z344,z4,z5,z6])],[(1,[z65,z84,z3,z4,z5,z6]),(1,[z7,z66,z3,z11,z5,z6]),(0,[z51,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z17,z3,z5,z6,z36]),(0,[z7,z209,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z328]),(0,[z515,z7,z2,z3,z4,z5,z6])],[(0,[z118,z66,z2,z3,z4,z5,z6]),(0,[z118,z7,z2,z3,z11,z5,z6]),(0,[z95,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z11,z5,z116,z6]),(0,[z516,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z11,z5,z6]),(0,[z61,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z517,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z4,z86,z6]),(0,[z7,z2,z3,z359,z4,z5,z6]),(0,[z518,z7,z2,z3,z4,z5,z6]),(0,[z519,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z203,z5,z6])],[(0,[z46,z7,z2,z17,z3,z5,z6]),(0,[z7,z40,z2,z3,z4,z5,z115]),(0,[z7,z2,z125,z3,z4,z5,z6]),(0,[z7,z520,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z99])],[(0,[z118,z2,z3,z217,z4,z5,z6]),(0,[z7,z521,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z375,z5,z6]),(0,[z7,z2,z164,z125,z4,z5,z6]),(1,[z7,z2,z17,z22,z5,z6]),(0,[z7,z2,z3,z522,z4,z5,z6])],[(0,[z7,z2,z217,z103,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z523,z6]),(0,[z1,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z24,z5,z79,z6]),(0,[z7,z2,z3,z4,z524,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z525]),(0,[z7,z2,z3,z4,z18,z5,z6])],[(0,[z526,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z104,z203,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z527]),(0,[z528,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z109,z6]),(0,[z7,z2,z529,z3,z4,z5,z6]),(0,[z7,z2,z3,z530,z24,z5,z6]),(1,[z7,z2,z300,z4,z5,z6]),(0,[z7,z2,z222,z3,z22,z5,z6]),(0,[z7,z2,z164,z17,z3,z5,z6]),(0,[z114,z370,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z435,z6]),(0,[z95,z531,z2,z3,z4,z5,z6]),(0,[z7,z2,z532,z3,z4,z5,z6]),(0,[z7,z2,z533,z3,z4,z5,z6]),(0,[z150,z7,z2,z17,z3,z5,z6]),(1,[z7,z2,z462,z3,z5,z6]),(0,[z7,z2,z3,z534,z4,z5,z6])],[(0,[z2,z52,z3,z217,z4,z5,z6]),(0,[z535,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z536]),(0,[z7,z2,z3,z4,z5,z116,z6]),(0,[z93,z7,z2,z3,z513,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z537,z6]),(0,[z51,z2,z3,z4,z5,z6,z36]),(0,[z7,z2,z538,z3,z4,z5,z6]),(0,[z7,z2,z539,z3,z4,z5,z6]),(0,[z7,z2,z62,z21,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z540,z6]),(0,[z541,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z49,z32])],[(0,[z65,z7,z2,z3,z24,z5,z6]),(0,[z66,z2,z84,z3,z4,z5,z6]),(0,[z7,z542,z2,z3,z4,z5,z6]),(0,[z380,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z543,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z76,z6]),(0,[z7,z544,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z545])],[(0,[z122,z7,z2,z3,z11,z5,z6]),(0,[z2,z3,z217,z4,z5,z68,z6]),(0,[z7,z2,z3,z4,z5,z546,z6]),(0,[z1,z7,z2,z3,z4,z5,z263]),(1,[z0,z2,z3,z4,z5,z36]),(0,[z7,z2,z3,z4,z375,z5,z6]),(0,[z7,z2,z547,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z548,z6]),(1,[z7,z2,z440,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z549]),(0,[z7,z550,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z76,z49])],[(0,[z7,z2,z3,z551,z4,z5,z6]),(0,[z552,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z34,z6]),(0,[z553,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z447,z5,z6]),(0,[z7,z2,z462,z62,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z132]),(0,[z554,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z555,z6]),(0,[z7,z2,z3,z134,z4,z5,z49])],[(0,[z89,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z105,z3,z103,z5,z6]),(0,[z7,z2,z3,z22,z5,z6,z115]),(0,[z7,z2,z3,z4,z5,z556,z6]),(0,[z7,z2,z418,z3,z4,z5,z6])],[(0,[z7,z66,z2,z3,z11,z5,z6]),(0,[z122,z2,z3,z217,z4,z5,z6]),(0,[z557,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z103,z24,z5,z6]),(0,[z7,z2,z17,z3,z341,z5,z6])],[(0,[z7,z2,z3,z558,z4,z5,z6]),(1,[z12,z7,z2,z4,z98,z6]),(0,[z559,z7,z2,z3,z4,z5,z6]),(0,[z7,z108,z2,z3,z4,z5,z99])],[(0,[z7,z560,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z5,z6]),(0,[z7,z2,z3,z104,z4,z5,z6])]],
   [[(0,[z7,z2,z561,z3,z4,z5,z6]),(0,[z7,z2,z3,z217,z11,z5,z6]),(0,[z7,z2,z52,z3,z562,z5,z6]),(0,[z563,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z103,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z564])],[(0,[z7,z2,z565,z3,z4,z5,z6]),(0,[z566,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z5,z523,z6]),(1,[z7,z2,z3,z216,z5,z6]),(0,[z7,z124,z2,z3,z24,z5,z6]),(0,[z7,z2,z62,z3,z24,z5,z6]),(0,[z7,z83,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z24,z5,z76,z6]),(1,[z7,z2,z3,z339,z5,z6]),(0,[z7,z2,z3,z203,z5,z79,z6])],[(0,[z471,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z19,z68,z6]),(0,[z113,z7,z3,z4,z5,z116,z6]),(0,[z7,z2,z567,z3,z4,z5,z6])],[(0,[z7,z2,z3,z179,z4,z5,z6]),(0,[z7,z568,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z42,z6]),(0,[z7,z124,z2,z3,z143,z5,z6]),(0,[z7,z569,z2,z3,z4,z5,z6])],[(0,[z7,z2,z570,z3,z4,z5,z6]),(0,[z7,z2,z3,z571,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z572]),(0,[z7,z2,z573,z3,z4,z5,z6]),(0,[z7,z2,z21,z222,z4,z5,z6]),(0,[z7,z2,z3,z22,z574,z5,z6]),(0,[z575,z7,z2,z3,z22,z5,z6]),(0,[z396,z7,z2,z17,z3,z5,z6])],[(0,[z7,z209,z66,z3,z4,z5,z6]),(0,[z576,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z577,z5,z6]),(0,[z7,z2,z3,z103,z22,z5,z6]),(0,[z7,z2,z58,z3,z4,z5,z6]),(0,[z61,z7,z2,z3,z4,z31,z6]),(0,[z7,z224,z2,z3,z4,z5,z6]),(0,[z93,z7,z2,z3,z4,z5,z6])],[(0,[z7,z141,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z578]),(0,[z579,z7,z2,z3,z4,z5,z6]),(0,[z7,z124,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z148]),(0,[z7,z3,z4,z60,z5,z116,z6]),(0,[z7,z2,z3,z4,z5,z580,z6]),(0,[z7,z2,z3,z134,z5,z49,z6])],[(1,[z7,z2,z3,z517,z5,z6]),(0,[z7,z2,z3,z4,z5,z43,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z88,z6]),(0,[z581,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z260]),(0,[z7,z2,z21,z3,z24,z5,z6]),(0,[z7,z582,z2,z3,z4,z5,z6]),(1,[z7,z2,z222,z22,z5,z6]),(0,[z583,z7,z2,z3,z4,z5,z6]),(0,[z7,z584,z2,z3,z4,z5,z6]),(0,[z7,z585,z2,z3,z4,z5,z6])],[(0,[z7,z124,z2,z3,z22,z5,z6]),(0,[z7,z2,z62,z3,z22,z5,z6])],[(0,[z586,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z36]),(0,[z7,z209,z2,z3,z4,z5,z6]),(0,[z587,z7,z2,z3,z4,z5,z6]),(0,[z588,z7,z2,z3,z4,z5,z6])],[(0,[z7,z589,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z42,z6]),(0,[z7,z270,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z102,z6]),(0,[z7,z2,z3,z4,z90,z5,z6]),(1,[z412,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z590]),(0,[z7,z2,z3,z4,z591,z5,z6])],[(0,[z122,z7,z2,z217,z4,z5,z6]),(0,[z7,z2,z105,z17,z3,z5,z6]),(1,[z7,z418,z3,z4,z5,z6])],[(0,[z1,z118,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z87,z60,z6]),(1,[z7,z2,z3,z4,z5,z271]),(0,[z7,z2,z3,z592,z4,z5,z6])],[(0,[z46,z7,z2,z3,z4,z86,z6]),(0,[z1,z2,z3,z4,z87,z5,z6]),(0,[z0,z7,z2,z17,z3,z5,z6]),(0,[z7,z593,z2,z3,z4,z5,z6]),(0,[z594,z7,z2,z3,z4,z5,z6]),(0,[z113,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z116,z6,z32]),(0,[z61,z595,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z17,z3,z28,z5,z6]),(0,[z7,z2,z3,z4,z203,z68,z6]),(0,[z7,z2,z3,z4,z596,z5,z6]),(0,[z516,z7,z2,z3,z11,z5,z6]),(1,[z7,z2,z3,z4,z403,z6]),(0,[z7,z597,z2,z3,z22,z5,z6]),(0,[z7,z598,z2,z3,z4,z5,z6])],[(0,[z118,z7,z2,z17,z3,z5,z6]),(1,[z7,z124,z3,z11,z5,z6]),(0,[z7,z108,z2,z3,z22,z5,z6]),(0,[z7,z2,z17,z17,z3,z5,z6]),(0,[z7,z2,z222,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z18,z76])],[(0,[z51,z7,z2,z3,z4,z5,z6]),(0,[z7,z599,z2,z3,z4,z5,z6]),(0,[z600,z7,z2,z3,z4,z5,z6]),(1,[z7,z565,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z87,z5,z6]),(0,[z7,z2,z3,z4,z87,z116,z6]),(0,[z7,z2,z125,z3,z11,z5,z6]),(0,[z7,z2,z3,z24,z5,z382,z6]),(0,[z7,z2,z3,z601,z4,z5,z6]),(0,[z93,z7,z2,z3,z4,z5,z73]),(0,[z114,z519,z2,z3,z4,z5,z6])],[(0,[z95,z7,z2,z3,z4,z5,z6]),(0,[z61,z7,z2,z3,z4,z5,z6]),(0,[z239,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z602,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z603])],[(0,[z7,z2,z84,z3,z24,z5,z6]),(0,[z7,z604,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z116,z98,z6]),(0,[z61,z7,z3,z4,z5,z6,z115])],[(0,[z7,z2,z3,z4,z5,z605,z6]),(0,[z606,z7,z2,z3,z4,z5,z6])],[(1,[z286,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z607,z5,z6]),(0,[z7,z2,z17,z3,z5,z98,z6]),(1,[z7,z2,z3,z269,z5,z6]),(0,[z7,z608,z2,z3,z4,z5,z6])],[(0,[z67,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z11,z5,z68,z6]),(1,[z95,z7,z103,z4,z5,z6]),(0,[z7,z2,z532,z3,z11,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z49,z36]),(0,[z7,z531,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z42,z73]),(1,[z519,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z609,z4,z5,z6])],[(0,[z65,z7,z2,z3,z430,z5,z6]),(0,[z7,z2,z3,z530,z4,z5,z6]),(0,[z30,z7,z209,z3,z4,z5,z6]),(0,[z7,z124,z2,z3,z4,z60,z6])],[(0,[z7,z2,z3,z4,z5,z610,z6]),(0,[z7,z2,z3,z4,z87,z5,z6]),(0,[z7,z2,z3,z4,z5,z36,z25]),(0,[z7,z2,z3,z11,z22,z5,z6]),(1,[z7,z2,z3,z90,z5,z6]),(0,[z7,z40,z2,z3,z4,z5,z42]),(0,[z7,z2,z3,z185,z4,z5,z6]),(1,[z2,z3,z4,z611,z5,z6])],[(1,[z7,z2,z3,z4,z5,z323]),(0,[z7,z2,z3,z4,z5,z6,z612])],[(0,[z122,z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z613,z6])],[(0,[z65,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z614,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z268,z6]),(0,[z7,z2,z3,z4,z615,z5,z6]),(0,[z46,z7,z2,z3,z203,z5,z6]),(0,[z7,z124,z2,z3,z4,z116,z6]),(0,[z7,z616,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z617])],[(1,[z7,z2,z3,z4,z5,z123]),(0,[z7,z2,z3,z22,z5,z6,z36]),(0,[z618,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z619,z5,z6]),(0,[z7,z66,z2,z17,z3,z5,z6]),(0,[z620,z7,z2,z3,z4,z5,z6]),(0,[z114,z71,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z68,z6]),(0,[z7,z2,z3,z11,z5,z621,z6]),(0,[z7,z209,z3,z24,z4,z5,z6]),(0,[z113,z415,z2,z3,z4,z5,z6]),(0,[z7,z40,z3,z4,z5,z42,z6]),(0,[z7,z2,z3,z4,z5,z76,z25]),(0,[z7,z2,z3,z4,z5,z6,z622])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z623]),(0,[z7,z2,z3,z4,z5,z6,z6]),(0,[z7,z2,z624,z3,z4,z5,z6]),(0,[z575,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z34,z25]),(0,[z7,z2,z3,z103,z4,z5,z6]),(0,[z7,z2,z276,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z625,z6]),(0,[z7,z2,z3,z626,z4,z5,z6])],[(0,[z33,z2,z84,z3,z4,z5,z6]),(0,[z7,z2,z52,z3,z11,z5,z6]),(0,[z7,z2,z17,z21,z3,z5,z6]),(0,[z7,z2,z3,z11,z627,z5,z6]),(0,[z61,z7,z2,z69,z4,z5,z6]),(0,[z7,z2,z3,z4,z22,z5,z6]),(0,[z12,z7,z2,z3,z4,z19,z6]),(0,[z7,z628,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z394,z5,z6]),(0,[z7,z2,z3,z4,z162,z5,z6]),(0,[z7,z2,z3,z4,z68,z98,z6]),(0,[z61,z75,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z6,z25]),(1,[z93,z7,z2,z4,z5,z25]),(0,[z7,z2,z3,z4,z5,z629,z6]),(0,[z7,z2,z3,z4,z5,z6,z630]),(0,[z7,z2,z3,z4,z5,z6,z631])],[(0,[z2,z84,z3,z4,z5,z6,z36]),(1,[z7,z2,z3,z607,z5,z6]),(1,[z7,z2,z3,z181,z5,z6]),(0,[z7,z2,z3,z22,z5,z73,z6]),(0,[z7,z2,z3,z4,z243,z5,z6])],[(0,[z632,z7,z2,z3,z4,z5,z6]),(0,[z122,z7,z2,z3,z4,z5,z268]),(0,[z7,z2,z3,z4,z60,z68,z6]),(1,[z415,z2,z3,z4,z5,z6]),(0,[z7,z124,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z198,z22,z5,z6]),(0,[z7,z2,z62,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z5,z6])],[(0,[z633,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z22,z5,z117,z6]),(0,[z7,z2,z3,z104,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z160,z6]),(0,[z114,z7,z2,z634,z4,z5,z6])],[(0,[z12,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z621,z6]),(0,[z635,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z636,z3,z4,z5,z6]),(0,[z7,z40,z2,z3,z181,z5,z6]),(1,[z7,z2,z8,z3,z5,z6]),(0,[z7,z2,z17,z222,z3,z5,z6]),(0,[z7,z2,z17,z3,z5,z49,z6]),(1,[z7,z281,z3,z4,z5,z6]),(0,[z7,z2,z637,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z638,z6]),(0,[z7,z2,z3,z639,z4,z5,z6]),(1,[z7,z2,z3,z24,z5,z6]),(0,[z7,z209,z124,z3,z4,z5,z6]),(0,[z7,z2,z138,z3,z4,z5,z6]),(0,[z114,z7,z2,z3,z4,z79,z6])],[(0,[z33,z7,z2,z3,z4,z37,z6])],[(0,[z7,z2,z3,z4,z627,z5,z6]),(1,[z7,z2,z22,z5,z98,z6]),(0,[z7,z2,z3,z22,z5,z130,z6]),(0,[z114,z7,z2,z344,z4,z5,z6])],[(0,[z7,z2,z3,z22,z5,z34,z6]),(1,[z7,z2,z3,z4,z5,z333]),(0,[z7,z2,z3,z640,z4,z5,z6]),(0,[z7,z209,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z641,z6]),(0,[z7,z2,z3,z5,z49,z6,z99]),(0,[z2,z3,z4,z18,z611,z5,z6])],[(1,[z7,z2,z3,z179,z5,z6]),(0,[z642,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z21,z3,z4,z5,z6]),(0,[z7,z597,z2,z3,z4,z5,z6]),(0,[z643,z7,z2,z3,z4,z5,z6]),(0,[z93,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z17,z3,z5,z475,z6]),(0,[z7,z2,z3,z4,z5,z644,z6]),(1,[z7,z2,z634,z4,z5,z6]),(0,[z7,z2,z3,z4,z18,z5,z76])],[(0,[z7,z2,z3,z645,z4,z5,z6]),(0,[z7,z2,z222,z3,z4,z19,z6]),(0,[z7,z108,z2,z3,z4,z5,z6])],[(0,[z646,z7,z2,z3,z4,z5,z6]),(0,[z12,z165,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z647,z4,z5,z6]),(0,[z7,z2,z3,z4,z388,z5,z6]),(1,[z531,z2,z3,z4,z5,z6]),(1,[z7,z2,z58,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z212,z6]),(0,[z93,z7,z2,z3,z4,z174,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z68,z6]),(0,[z7,z2,z3,z4,z18,z5,z34]),(0,[z30,z7,z2,z3,z24,z5,z6]),(0,[z93,z7,z2,z4,z5,z6,z25]),(0,[z7,z2,z3,z4,z5,z648,z6])],[(0,[z7,z2,z3,z4,z5,z6,z649]),(1,[z7,z2,z3,z394,z5,z6]),(0,[z46,z7,z565,z3,z4,z5,z6]),(0,[z7,z2,z650,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z651,z6]),(0,[z7,z595,z2,z3,z4,z5,z6]),(0,[z586,z7,z2,z3,z22,z5,z6]),(1,[z7,z2,z218,z3,z5,z6])],[(0,[z118,z2,z3,z4,z5,z68,z6]),(0,[z7,z2,z3,z4,z5,z652,z6]),(0,[z71,z7,z2,z3,z203,z5,z6]),(0,[z7,z2,z222,z3,z11,z5,z6]),(1,[z7,z2,z3,z4,z491,z6]),(0,[z7,z2,z62,z3,z4,z5,z73]),(0,[z114,z7,z637,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z186,z6]),(0,[z7,z2,z3,z4,z5,z653,z6]),(0,[z7,z2,z654,z3,z4,z5,z6]),(0,[z93,z7,z2,z3,z185,z5,z6])],[(0,[z7,z2,z655,z3,z4,z5,z6]),(0,[z7,z2,z52,z103,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z6,z115]),(0,[z7,z2,z656,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z76,z42]),(0,[z7,z2,z3,z4,z5,z6,z657]),(0,[z7,z2,z3,z104,z4,z203,z6])],[(0,[z46,z71,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z658]),(0,[z7,z2,z3,z5,z523,z68,z6]),(0,[z7,z40,z3,z103,z4,z5,z6]),(0,[z7,z2,z440,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z233,z5,z6])],[(0,[z7,z2,z3,z4,z87,z19,z6]),(0,[z7,z2,z3,z4,z5,z34,z42]),(0,[z7,z2,z659,z3,z4,z5,z6]),(0,[z7,z2,z3,z660,z4,z5,z6])],[(0,[z7,z2,z217,z4,z22,z5,z6]),(0,[z661,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z484,z5,z6]),(0,[z7,z2,z3,z24,z19,z5,z6]),(0,[z662,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z84,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z47]),(0,[z46,z2,z3,z4,z101,z5,z6]),(0,[z7,z2,z3,z28,z22,z5,z6]),(0,[z7,z39,z2,z21,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z422]),(0,[z12,z7,z342,z3,z4,z5,z6]),(1,[z7,z637,z3,z4,z5,z6]),(0,[z663,z7,z2,z3,z4,z5,z6])],[(0,[z7,z84,z3,z103,z4,z5,z6]),(0,[z2,z3,z217,z4,z5,z6,z36]),(0,[z51,z7,z2,z3,z22,z5,z6]),(0,[z412,z7,z2,z3,z4,z5,z6])],[(0,[z664,z7,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z6]),(1,[z1,z2,z3,z4,z87,z6]),(0,[z7,z2,z3,z4,z5,z665,z6]),(0,[z95,z7,z2,z3,z22,z5,z6]),(0,[z61,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z666,z6])],[(0,[z7,z2,z3,z667,z4,z5,z6]),(0,[z668,z7,z2,z3,z4,z5,z6]),(0,[z67,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z68,z79,z6]),(0,[z669,z7,z2,z3,z4,z5,z6]),(0,[z670,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z671,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z34,z99]),(0,[z7,z2,z3,z112,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z115]),(0,[z7,z2,z17,z3,z134,z5,z6]),(0,[z672,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z562,z5,z6]),(0,[z7,z39,z2,z3,z607,z5,z6]),(0,[z673,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z4,z5,z6]),(0,[z33,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z674,z3,z4,z5,z6]),(0,[z113,z7,z2,z3,z339,z5,z6]),(1,[z7,z2,z3,z4,z31,z6]),(0,[z7,z2,z17,z3,z5,z6,z99]),(1,[z7,z2,z3,z513,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z675])],[(0,[z7,z2,z3,z4,z676,z5,z6]),(0,[z7,z2,z17,z199,z3,z5,z6])]],
   [[(0,[z7,z2,z3,z11,z60,z5,z6]),(0,[z7,z2,z677,z3,z4,z5,z6]),(0,[z93,z7,z224,z3,z4,z5,z6])],[(0,[z678,z7,z2,z3,z4,z5,z6]),(0,[z679,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z45,z5,z6]),(0,[z7,z39,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z22,z5,z6,z32]),(0,[z7,z2,z3,z4,z5,z6,z680])],[(0,[z7,z2,z3,z4,z5,z6,z681]),(0,[z7,z2,z3,z103,z11,z5,z6]),(0,[z7,z315,z2,z3,z24,z5,z6]),(0,[z7,z235,z2,z3,z4,z5,z6]),(0,[z384,z7,z2,z3,z4,z5,z6])],[(0,[z65,z7,z2,z154,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z682,z6]),(1,[z7,z2,z3,z4,z435,z6]),(0,[z7,z2,z402,z3,z4,z5,z6]),(0,[z7,z683,z2,z3,z4,z5,z6])],[(0,[z684,z7,z2,z3,z4,z5,z6]),(0,[z65,z7,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z574,z5,z6]),(0,[z71,z7,z2,z3,z101,z5,z6]),(0,[z685,z7,z2,z3,z4,z5,z6]),(0,[z113,z7,z2,z3,z517,z5,z6])],[(0,[z7,z2,z3,z4,z101,z5,z6]),(0,[z7,z83,z2,z3,z4,z68,z6]),(0,[z7,z2,z3,z4,z686,z5,z6]),(0,[z7,z2,z3,z24,z203,z5,z6]),(0,[z7,z2,z17,z4,z22,z5,z6]),(0,[z687,z7,z2,z3,z4,z5,z6]),(0,[z7,z230,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z688])],[(0,[z51,z7,z2,z217,z4,z5,z6]),(0,[z33,z7,z2,z3,z22,z5,z6]),(0,[z7,z124,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z381,z11,z5,z6]),(0,[z7,z2,z3,z24,z5,z6,z99]),(0,[z7,z2,z3,z134,z24,z5,z6]),(0,[z7,z2,z3,z22,z5,z98,z6]),(0,[z7,z2,z393,z17,z3,z5,z6]),(0,[z12,z7,z2,z3,z433,z5,z6]),(0,[z7,z2,z3,z4,z5,z689,z6]),(0,[z7,z2,z3,z4,z611,z5,z6])],[(0,[z46,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z164,z222,z4,z5,z6]),(0,[z7,z690,z2,z3,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z430,z5,z6]),(1,[z7,z184,z3,z4,z5,z6]),(0,[z7,z279,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z101,z5,z68,z6]),(0,[z7,z2,z3,z24,z18,z5,z6]),(0,[z7,z2,z3,z4,z60,z5,z6]),(1,[z595,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z691]),(0,[z7,z2,z222,z4,z19,z5,z6]),(0,[z7,z2,z3,z634,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z368]),(0,[z7,z2,z3,z4,z68,z76,z6]),(0,[z7,z2,z692,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z693,z5,z6]),(0,[z12,z7,z2,z17,z3,z5,z6])],[(0,[z694,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z695]),(0,[z7,z2,z21,z4,z5,z98,z6]),(0,[z7,z2,z3,z4,z696,z5,z6]),(0,[z7,z2,z3,z4,z5,z697,z6])],[(0,[z698,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z562,z5,z6]),(0,[z7,z699,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z375,z5,z6]),(0,[z7,z2,z700,z3,z4,z5,z6]),(0,[z7,z2,z701,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z5,z6]),(0,[z702,z7,z2,z3,z4,z5,z6]),(0,[z65,z7,z2,z3,z4,z5,z186]),(0,[z122,z7,z2,z3,z4,z388,z6]),(0,[z7,z703,z2,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z87,z6]),(0,[z7,z2,z3,z24,z5,z116,z6]),(0,[z7,z83,z2,z3,z22,z5,z6])],[(0,[z7,z2,z3,z4,z704,z5,z6]),(0,[z705,z7,z2,z3,z4,z5,z6]),(0,[z7,z209,z2,z17,z3,z5,z6]),(1,[z7,z235,z3,z4,z5,z6])],[(1,[z7,z141,z3,z4,z5,z6]),(0,[z7,z108,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z706,z4,z5,z6])],[(1,[z7,z2,z136,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z390]),(0,[z7,z2,z3,z4,z87,z203,z6]),(0,[z48,z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z17,z3,z3,z5,z6]),(0,[z13,z7,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z576,z2,z3,z4,z68,z6]),(0,[z7,z2,z707,z3,z5,z6]),(0,[z7,z2,z3,z708,z5,z6]),(0,[z54,z7,z2,z4,z98,z6])],[(0,[z7,z709,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z19,z271]),(0,[z7,z2,z3,z11,z5,z710]),(0,[z7,z224,z3,z4,z491,z6])],[(0,[z7,z2,z3,z4,z711,z6]),(0,[z712,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z713]),(0,[z7,z235,z3,z143,z5,z6]),(0,[z714,z2,z3,z4,z5,z6])],[(0,[z7,z84,z154,z4,z5,z6]),(0,[z7,z2,z17,z402,z5,z6]),(0,[z595,z2,z3,z22,z5,z6]),(0,[z715,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z716,z5,z6]),(0,[z7,z184,z3,z162,z5,z6]),(0,[z7,z2,z3,z717,z5,z6]),(0,[z7,z2,z3,z718,z5,z6]),(0,[z7,z2,z3,z4,z5,z719])],[(0,[z7,z2,z17,z3,z5,z390]),(0,[z7,z418,z3,z11,z5,z6]),(0,[z7,z2,z720,z4,z5,z6]),(0,[z114,z7,z2,z3,z212,z6])],[(0,[z7,z141,z3,z4,z149,z6]),(0,[z7,z2,z3,z11,z5,z271]),(0,[z7,z2,z3,z470,z172,z6]),(0,[z7,z2,z222,z237,z5,z6]),(0,[z195,z2,z3,z4,z60,z6])],[(0,[z7,z2,z3,z22,z5,z6]),(0,[z65,z84,z294,z4,z5,z6]),(0,[z33,z2,z3,z4,z5,z50]),(0,[z7,z565,z3,z4,z86,z6]),(0,[z7,z2,z3,z4,z238,z32]),(0,[z7,z2,z3,z4,z5,z721])],[(0,[z7,z2,z3,z394,z5,z6]),(0,[z7,z2,z3,z182,z109,z6]),(0,[z7,z2,z4,z722,z5,z6]),(0,[z7,z2,z234,z22,z5,z6]),(0,[z7,z2,z441,z22,z5,z6]),(0,[z7,z235,z3,z22,z5,z6]),(0,[z7,z723,z3,z4,z5,z6])],[(0,[z7,z2,z3,z724,z5,z6]),(0,[z7,z2,z3,z11,z5,z725]),(0,[z7,z2,z3,z4,z5,z148]),(0,[z575,z7,z2,z4,z98,z6]),(0,[z7,z2,z3,z4,z726,z6])],[(0,[z7,z565,z3,z11,z5,z6]),(0,[z195,z2,z3,z4,z116,z6]),(0,[z7,z2,z234,z4,z5,z148]),(0,[z7,z2,z3,z4,z5,z727]),(0,[z7,z2,z488,z22,z5,z6]),(0,[z7,z2,z106,z5,z98,z6])],[(0,[z7,z728,z3,z4,z5,z6]),(0,[z7,z3,z11,z5,z146,z6]),(0,[z7,z2,z3,z729,z5,z6]),(0,[z153,z7,z2,z22,z5,z6])],[(0,[z7,z2,z730,z3,z5,z6]),(0,[z46,z2,z3,z101,z5,z47]),(0,[z2,z3,z4,z68,z204,z6])],[(0,[z118,z2,z3,z4,z5,z323]),(0,[z7,z2,z3,z731,z5,z6]),(0,[z7,z240,z3,z11,z5,z6])],[(0,[z0,z2,z3,z4,z5,z732]),(0,[z7,z2,z3,z4,z96,z333]),(0,[z7,z2,z3,z522,z5,z49])],[(0,[z7,z2,z17,z3,z109,z6]),(0,[z7,z2,z3,z4,z5,z47]),(0,[z7,z2,z196,z22,z5,z6]),(0,[z95,z7,z103,z11,z5,z6]),(0,[z733,z2,z3,z4,z5,z6]),(0,[z7,z3,z11,z120,z5,z6]),(0,[z7,z2,z3,z4,z734,z6])]],
   [[(0,[z7,z3,z484,z11,z5,z6]),(0,[z519,z2,z3,z11,z5,z6]),(0,[z195,z2,z3,z517,z5,z6]),(0,[z61,z7,z300,z4,z5,z115]),(0,[z735,z2,z3,z4,z5,z6])],[(0,[z51,z2,z52,z24,z5,z6]),(0,[z563,z7,z2,z4,z98,z6]),(0,[z380,z7,z2,z736,z5,z6]),(0,[z7,z40,z3,z22,z5,z42]),(0,[z7,z2,z3,z22,z5,z43]),(0,[z7,z2,z3,z22,z5,z737]),(0,[z7,z2,z3,z738,z5,z6]),(0,[z7,z2,z3,z4,z5,z177]),(1,[z7,z2,z3,z739,z6])],[(0,[z7,z565,z3,z4,z5,z368]),(0,[z531,z2,z3,z4,z96,z6]),(0,[z7,z3,z11,z5,z167,z6]),(0,[z114,z519,z2,z3,z79,z6]),(0,[z7,z235,z3,z4,z5,z177])],[(0,[z7,z2,z3,z11,z5,z323]),(0,[z740,z2,z3,z11,z5,z6]),(0,[z741,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z742,z5,z6])],[(0,[z7,z184,z3,z45,z5,z6]),(0,[z71,z2,z3,z112,z5,z6]),(0,[z1,z2,z3,z4,z87,z88]),(0,[z0,z2,z17,z3,z5,z36]),(0,[z113,z7,z3,z11,z116,z6]),(0,[z7,z3,z339,z5,z116,z6]),(0,[z12,z13,z2,z4,z98,z6])],[(0,[z7,z2,z371,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z743]),(0,[z7,z2,z321,z17,z5,z6]),(0,[z7,z2,z3,z4,z5,z744]),(0,[z7,z2,z3,z745,z5,z6]),(0,[z7,z2,z3,z11,z746,z6]),(0,[z7,z2,z222,z106,z5,z6])],[(0,[z7,z2,z3,z4,z747,z6]),(0,[z7,z2,z17,z351,z5,z6]),(0,[z748,z2,z3,z4,z5,z6]),(0,[z7,z234,z4,z5,z116,z6]),(0,[z7,z2,z3,z4,z749,z6])],[(0,[z7,z184,z3,z750,z5,z6]),(0,[z7,z2,z3,z751,z5,z6]),(0,[z487,z7,z103,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z249])],[(0,[z7,z2,z105,z3,z5,z6]),(0,[z7,z2,z3,z24,z5,z752]),(0,[z7,z2,z402,z517,z5,z6]),(0,[z753,z2,z3,z4,z5,z6]),(0,[z7,z281,z3,z106,z5,z6]),(0,[z7,z2,z276,z634,z5,z6])],[(0,[z7,z2,z3,z4,z5,z754]),(0,[z2,z3,z217,z4,z5,z123]),(0,[z7,z2,z17,z136,z5,z6]),(0,[z755,z2,z3,z4,z5,z6]),(0,[z93,z7,z2,z17,z5,z25]),(0,[z7,z2,z756,z3,z5,z6])],[(0,[z7,z2,z3,z4,z435,z6]),(0,[z270,z2,z3,z11,z5,z6]),(0,[z10,z7,z2,z3,z621,z6])],[(0,[z7,z757,z3,z4,z5,z6]),(0,[z7,z39,z3,z120,z5,z6]),(0,[z7,z2,z758,z3,z5,z6]),(0,[z93,z7,z2,z11,z5,z25]),(0,[z7,z35,z3,z11,z5,z6]),(0,[z759,z2,z3,z4,z5,z6])],[(0,[z7,z209,z3,z120,z5,z6])],[(0,[z7,z760,z3,z4,z5,z6]),(0,[z380,z370,z2,z3,z5,z6]),(0,[z7,z531,z103,z4,z5,z6]),(0,[z95,z7,z103,z216,z5,z6]),(0,[z415,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z24,z5,z132])],[(0,[z93,z270,z2,z4,z5,z25]),(0,[z412,z418,z3,z4,z5,z6])],[(0,[z7,z2,z3,z430,z5,z6]),(0,[z7,z2,z3,z4,z761,z6]),(0,[z7,z2,z3,z4,z762,z6]),(0,[z7,z281,z3,z11,z5,z6]),(0,[z7,z2,z300,z254,z5,z6]),(0,[z7,z763,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z764,z6]),(0,[z118,z2,z3,z4,z5,z390]),(0,[z7,z2,z110,z22,z5,z6]),(0,[z7,z2,z624,z22,z5,z6]),(0,[z7,z3,z765,z11,z5,z6]),(0,[z7,z2,z634,z5,z79,z6])],[(0,[z114,z7,z637,z3,z79,z6]),(0,[z7,z2,z3,z766,z5,z6])],[(0,[z7,z2,z3,z767,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z149,z6]),(0,[z595,z2,z3,z56,z5,z6]),(0,[z7,z2,z3,z4,z5,z768])],[(0,[z7,z2,z769,z3,z5,z6]),(0,[z7,z2,z234,z4,z5,z6]),(0,[z7,z235,z3,z4,z5,z6]),(0,[z7,z2,z634,z11,z5,z6]),(0,[z7,z2,z3,z134,z5,z382]),(0,[z770,z2,z3,z4,z5,z6]),(0,[z93,z7,z2,z4,z174,z25])],[(0,[z7,z2,z3,z4,z238,z271]),(0,[z7,z2,z62,z24,z5,z73]),(0,[z114,z7,z235,z3,z79,z6]),(0,[z7,z2,z771,z4,z5,z6])],[(1,[z757,z3,z4,z5,z6]),(0,[z7,z2,z3,z772,z5,z6]),(0,[z7,z2,z773,z3,z5,z6]),(0,[z7,z2,z3,z11,z5,z390]),(0,[z774,z2,z3,z4,z5,z6]),(0,[z7,z2,z775,z3,z5,z6]),(0,[z7,z418,z3,z776,z5,z6]),(0,[z384,z2,z3,z4,z18,z76])],[(0,[z7,z2,z3,z4,z5,z777]),(0,[z7,z8,z3,z103,z5,z6]),(0,[z7,z2,z3,z56,z5,z6]),(0,[z7,z2,z480,z22,z5,z6]),(0,[z7,z418,z17,z3,z5,z6]),(0,[z7,z2,z3,z778,z5,z6]),(0,[z7,z2,z3,z4,z76,z779])],[(0,[z7,z2,z110,z4,z5,z47]),(0,[z7,z2,z3,z4,z780,z6]),(0,[z7,z2,z17,z3,z5,z271]),(0,[z2,z3,z4,z37,z34,z6]),(0,[z7,z2,z3,z221,z5,z260]),(0,[z7,z2,z3,z11,z5,z721]),(0,[z7,z2,z344,z11,z5,z6]),(0,[z7,z2,z781,z3,z5,z6]),(0,[z7,z2,z218,z22,z5,z6])],[(0,[z7,z2,z3,z4,z782,z6]),(0,[z7,z279,z3,z4,z435,z6]),(0,[z95,z7,z17,z103,z5,z6])],[(0,[z7,z2,z17,z294,z5,z6]),(0,[z7,z83,z2,z3,z24,z32]),(0,[z7,z2,z3,z360,z26,z6]),(0,[z7,z416,z2,z3,z5,z328])],[(0,[z65,z84,z3,z4,z109,z6]),(0,[z783,z2,z3,z4,z5,z6]),(0,[z61,z7,z3,z4,z403,z115])],[(0,[z7,z2,z784,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z785]),(0,[z7,z565,z17,z3,z5,z6]),(0,[z7,z2,z786,z3,z5,z6]),(0,[z370,z2,z634,z4,z5,z6])],[(0,[z7,z2,z154,z22,z5,z6]),(0,[z89,z2,z3,z112,z5,z6]),(0,[z7,z40,z3,z4,z5,z42]),(0,[z7,z416,z2,z3,z5,z99]),(0,[z7,z342,z222,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z43]),(0,[z7,z2,z3,z787,z5,z6])],[(0,[z7,z2,z3,z182,z5,z323]),(0,[z51,z184,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z96,z260]),(0,[z7,z83,z2,z3,z11,z32]),(0,[z7,z2,z3,z788,z5,z6]),(0,[z7,z2,z164,z17,z5,z6]),(0,[z7,z789,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z790]),(0,[z370,z2,z3,z4,z79,z6])],[(0,[z122,z2,z217,z22,z5,z6]),(0,[z71,z2,z3,z28,z5,z6]),(0,[z7,z2,z3,z791,z5,z6]),(0,[z7,z2,z250,z22,z5,z6]),(0,[z165,z2,z3,z22,z5,z6]),(0,[z7,z792,z17,z3,z5,z6])]],
   [[(0,[z7,z599,z3,z11,z5,z6]),(0,[z7,z2,z793,z52,z5,z6]),(0,[z7,z2,z3,z11,z5,z47]),(0,[z7,z2,z3,z4,z102,z6]),(0,[z7,z2,z3,z22,z5,z148]),(0,[z370,z2,z344,z4,z5,z6])],[(0,[z7,z3,z11,z68,z116,z6]),(0,[z7,z2,z3,z22,z174,z6]),(0,[z7,z16,z2,z3,z5,z422])],[(0,[z7,z279,z3,z4,z5,z6]),(0,[z7,z2,z794,z3,z5,z6]),(0,[z2,z3,z4,z795,z5,z6]),(0,[z1,z2,z3,z11,z87,z6]),(0,[z519,z2,z17,z3,z5,z6])],[(0,[z7,z2,z17,z237,z5,z6])],[(0,[z796,z7,z2,z3,z4,z5]),(0,[z7,z2,z364,z22,z5,z6]),(0,[z7,z2,z692,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z797]),(0,[z7,z2,z798,z22,z5,z6])],[(0,[z7,z2,z17,z3,z5,z323]),(0,[z7,z2,z3,z799,z5,z6]),(0,[z7,z3,z24,z800,z5,z6])],[(0,[z7,z2,z3,z801,z5,z6]),(0,[z118,z757,z3,z4,z5,z6]),(0,[z71,z2,z3,z795,z5,z6]),(0,[z286,z2,z3,z221,z5,z6]),(0,[z7,z2,z325,z440,z5,z6]),(0,[z802,z2,z17,z3,z5,z6]),(0,[z7,z168,z2,z3,z4,z32]),(0,[z803,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z134,z5,z804])],[(0,[z661,z66,z3,z4,z5,z6]),(0,[z12,z7,z342,z4,z98,z6])],[(0,[z2,z3,z142,z4,z68,z6]),(0,[z380,z7,z805,z3,z5,z6]),(0,[z97,z2,z3,z4,z87,z6]),(0,[z7,z2,z3,z517,z5,z306]),(0,[z7,z2,z3,z22,z5,z177]),(0,[z7,z2,z3,z4,z98,z14])],[(0,[z7,z2,z3,z4,z5,z806]),(0,[z7,z2,z3,z4,z807,z6]),(0,[z7,z2,z402,z24,z5,z6]),(0,[z7,z2,z3,z808,z5,z6]),(1,[z7,z418,z4,z5,z25]),(0,[z809,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z254,z403,z6])],[(0,[z7,z2,z3,z4,z311,z323]),(0,[z7,z2,z3,z11,z435,z6]),(0,[z7,z2,z217,z22,z5,z6]),(0,[z7,z2,z3,z810,z5,z6]),(0,[z7,z2,z3,z811,z5,z6]),(0,[z7,z2,z3,z4,z5,z812]),(0,[z595,z2,z3,z4,z5,z115]),(0,[z813,z2,z3,z4,z5,z6])],[(0,[z7,z2,z110,z4,z5,z6]),(0,[z51,z2,z3,z4,z37,z6]),(0,[z286,z2,z3,z4,z96,z6]),(0,[z7,z2,z814,z3,z5,z6]),(0,[z150,z2,z393,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z815])],[(0,[z318,z84,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z6,z816]),(0,[z7,z2,z817,z3,z5,z6]),(0,[z384,z2,z3,z24,z5,z6]),(0,[z61,z75,z3,z4,z5,z115]),(0,[z7,z2,z3,z22,z749,z6]),(0,[z7,z2,z3,z818,z5,z6])],[(0,[z150,z2,z3,z28,z5,z6]),(0,[z7,z2,z819,z4,z5,z6]),(0,[z7,z2,z285,z22,z5,z6]),(0,[z820,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z821,z5,z6]),(0,[z822,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z823,z5,z6]),(0,[z7,z2,z824,z3,z5,z6]),(0,[z7,z2,z17,z543,z5,z6]),(0,[z7,z277,z3,z11,z5,z6]),(0,[z415,z2,z17,z3,z5,z6])]],
   [[(0,[z516,z84,z3,z4,z5,z6]),(0,[z7,z124,z3,z375,z5,z6]),(0,[z7,z2,z3,z825,z5,z6]),(0,[z595,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z826,z5,z6]),(0,[z7,z827,z17,z3,z5,z6])],[(0,[z7,z84,z3,z11,z5,z6]),(0,[z7,z589,z2,z3,z5,z99]),(0,[z7,z2,z3,z197,z233,z6]),(0,[z7,z281,z17,z3,z5,z6]),(0,[z828,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z829]),(0,[z122,z2,z217,z4,z435,z6]),(0,[z71,z370,z2,z3,z5,z6]),(0,[z7,z2,z3,z24,z5,z830]),(0,[z7,z2,z775,z125,z5,z6])],[(0,[z7,z2,z3,z4,z5,z831]),(0,[z61,z7,z3,z24,z5,z115]),(0,[z7,z2,z120,z5,z98,z6])],[(0,[z7,z2,z3,z11,z5,z6]),(0,[z7,z66,z154,z4,z5,z6]),(0,[z7,z2,z3,z143,z5,z6]),(0,[z7,z2,z3,z24,z832,z6]),(0,[z113,z415,z3,z4,z116,z6]),(0,[z411,z2,z3,z574,z5,z6]),(0,[z7,z2,z3,z104,z341,z6])],[(0,[z7,z2,z154,z430,z5,z6]),(0,[z114,z7,z2,z136,z5,z6]),(0,[z7,z2,z506,z22,z5,z6]),(0,[z663,z2,z3,z4,z87,z6]),(0,[z7,z235,z3,z11,z5,z6]),(1,[z7,z2,z3,z4,z779])],[(0,[z7,z2,z3,z5,z833,z6]),(0,[z2,z3,z24,z611,z5,z6]),(0,[z7,z763,z3,z22,z5,z6])],[(0,[z7,z2,z310,z22,z5,z6]),(0,[z95,z7,z103,z4,z5,z333]),(0,[z152,z7,z3,z4,z5,z115]),(0,[z7,z2,z125,z22,z5,z6]),(0,[z7,z2,z17,z3,z5,z834]),(0,[z93,z7,z418,z4,z5,z25]),(0,[z7,z2,z3,z835,z5,z6])],[(0,[z7,z84,z440,z3,z5,z6]),(0,[z7,z2,z218,z344,z5,z6])],[(0,[z7,z2,z154,z4,z5,z6]),(0,[z2,z84,z3,z4,z109,z6]),(0,[z7,z2,z3,z24,z5,z263]),(0,[z239,z7,z2,z3,z475,z6]),(0,[z13,z281,z3,z4,z5,z6]),(0,[z7,z281,z3,z4,z5,z14]),(0,[z7,z224,z3,z185,z5,z6]),(0,[z7,z2,z3,z4,z18,z779])],[(0,[z7,z2,z136,z4,z149,z6]),(0,[z7,z2,z3,z359,z5,z6]),(0,[z7,z2,z3,z836,z5,z6]),(0,[z837,z2,z3,z4,z5,z6]),(0,[z7,z838,z3,z4,z5,z6]),(0,[z7,z544,z2,z3,z4,z32]),(0,[z7,z2,z839,z4,z5,z6])],[(0,[z122,z2,z217,z4,z5,z6]),(0,[z165,z2,z3,z4,z5,z6]),(0,[z354,z2,z3,z4,z68,z6]),(0,[z672,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z221,z5,z333]),(0,[z7,z2,z3,z4,z5,z840])],[(0,[z7,z841,z3,z22,z5,z6]),(0,[z586,z2,z3,z198,z5,z6]),(0,[z7,z2,z17,z502,z5,z6]),(0,[z7,z2,z3,z4,z842,z6])],[(0,[z7,z2,z210,z3,z5,z6]),(0,[z7,z2,z52,z22,z5,z6]),(0,[z843,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z22,z5,z88]),(0,[z496,z2,z3,z4,z87,z6]),(0,[z7,z2,z844,z3,z5,z6]),(0,[z7,z2,z3,z4,z174,z6]),(0,[z370,z235,z3,z4,z5,z6])],[(0,[z694,z2,z3,z4,z5,z36]),(0,[z7,z2,z3,z4,z845,z6]),(0,[z7,z846,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z96,z6]),(0,[z7,z2,z3,z847,z5,z6]),(0,[z7,z2,z3,z11,z5,z43]),(1,[z7,z3,z4,z5,z727])],[(0,[z114,z7,z565,z3,z5,z6]),(0,[z531,z2,z3,z221,z5,z6]),(0,[z7,z2,z3,z848,z5,z6]),(0,[z7,z2,z849,z4,z5,z6]),(0,[z412,z2,z3,z513,z5,z6])]],
   [[(0,[z7,z2,z850,z4,z5,z6]),(0,[z7,z2,z3,z4,z851,z6])],[(1,[z84,z154,z4,z5,z6]),(0,[z65,z84,z3,z4,z5,z323]),(0,[z2,z3,z217,z4,z37,z6]),(0,[z7,z2,z3,z4,z87,z263]),(0,[z7,z3,z800,z11,z5,z6])],[(0,[z7,z2,z17,z3,z5,z47]),(0,[z7,z2,z3,z852,z5,z6]),(0,[z7,z2,z3,z4,z853,z6]),(0,[z7,z2,z567,z17,z5,z6])],[(0,[z7,z2,z3,z22,z5,z268]),(0,[z7,z2,z222,z419,z5,z6]),(0,[z7,z2,z251,z22,z5,z6])],[(0,[z1,z2,z17,z3,z87,z6]),(0,[z75,z2,z3,z11,z5,z6]),(0,[z554,z7,z3,z11,z5,z6]),(0,[z7,z2,z23,z237,z5,z6]),(0,[z7,z2,z3,z4,z5,z854]),(0,[z855,z2,z3,z4,z5,z6])],[(0,[z856,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z4,z857,z6]),(0,[z7,z342,z3,z4,z5,z6]),(0,[z7,z2,z3,z858,z5,z6]),(0,[z7,z2,z859,z3,z5,z6]),(0,[z7,z2,z164,z775,z5,z6]),(0,[z165,z2,z3,z4,z5,z43])],[(0,[z7,z2,z3,z4,z5,z860]),(0,[z7,z2,z3,z861,z5,z6]),(0,[z75,z2,z300,z4,z5,z6])],[(0,[z7,z2,z3,z862,z5,z6]),(0,[z7,z2,z3,z22,z102,z6]),(0,[z10,z7,z3,z4,z116,z6])],[(0,[z231,z2,z3,z4,z68,z6]),(0,[z7,z2,z3,z863,z5,z6]),(0,[z7,z565,z3,z203,z5,z6]),(0,[z864,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z63,z5,z6])],[(0,[z757,z84,z3,z4,z5,z6]),(0,[z2,z184,z217,z4,z5,z6]),(0,[z7,z279,z3,z22,z5,z6]),(0,[z7,z2,z865,z3,z5,z6]),(0,[z7,z2,z3,z24,z5,z306]),(0,[z61,z7,z3,z4,z31,z115])],[(0,[z7,z2,z3,z866,z5,z6]),(0,[z7,z2,z3,z4,z867,z6])],[],[(0,[z7,z84,z3,z182,z5,z6]),(0,[z2,z217,z22,z5,z68,z6]),(0,[z7,z124,z3,z607,z5,z6]),(0,[z7,z2,z4,z5,z73,z868])],[(0,[z7,z869,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z435,z6]),(0,[z7,z2,z110,z11,z5,z6]),(0,[z7,z2,z870,z4,z5,z6]),(0,[z7,z2,z296,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z871]),(0,[z7,z2,z872,z4,z5,z6]),(0,[z7,z2,z4,z5,z726,z6])],[],[(0,[z7,z2,z3,z182,z5,z6]),(0,[z7,z3,z11,z5,z6,z399]),(0,[z7,z2,z17,z69,z5,z6]),(0,[z7,z342,z3,z4,z5,z43])]],
   [[(0,[z7,z2,z538,z22,z5,z6]),(0,[z93,z7,z224,z4,z5,z25]),(0,[z7,z873,z3,z4,z5,z6])],[(0,[z118,z66,z3,z394,z5,z6]),(0,[z874,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z875,z5,z6]),(0,[z7,z2,z3,z4,z5,z876]),(0,[z7,z2,z659,z22,z5,z6]),(0,[z595,z2,z17,z3,z5,z6]),(0,[z114,z7,z2,z3,z79,z177])],[(0,[z7,z2,z793,z3,z5,z6]),(0,[z46,z2,z3,z101,z5,z6]),(0,[z7,z2,z3,z104,z233,z6])],[(0,[z7,z2,z3,z4,z5,z877]),(0,[z7,z2,z3,z4,z5,z878]),(0,[z7,z2,z879,z4,z5,z6])],[(0,[z7,z2,z3,z24,z109,z6]),(0,[z7,z2,z880,z4,z5,z6]),(0,[z881,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z776,z5,z6]),(0,[z7,z2,z3,z134,z5,z49])],[(0,[z7,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z882,z6]),(0,[z7,z2,z3,z4,z435,z268]),(0,[z7,z2,z17,z3,z5,z768])],[(0,[z7,z2,z3,z883,z5,z6]),(0,[z7,z2,z3,z884,z5,z6]),(0,[z95,z7,z103,z4,z5,z260]),(0,[z7,z2,z3,z885,z5,z6]),(0,[z7,z235,z17,z3,z5,z6])],[(0,[z7,z2,z3,z430,z311,z6]),(0,[z7,z2,z136,z28,z5,z6]),(0,[z7,z2,z3,z254,z31,z6]),(0,[z7,z841,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z88]),(0,[z7,z2,z3,z886,z5,z6]),(0,[z7,z2,z720,z11,z5,z6])],[(0,[z7,z2,z154,z11,z5,z6]),(1,[z7,z773,z3,z5,z6]),(0,[z7,z2,z736,z5,z68,z6])],[(1,[z531,z103,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z887]),(0,[z30,z7,z8,z3,z5,z6]),(0,[z113,z7,z3,z517,z116,z6]),(0,[z12,z165,z2,z4,z98,z6]),(0,[z7,z281,z3,z888,z5,z6])],[(0,[z7,z2,z3,z4,z311,z6]),(0,[z7,z3,z11,z5,z6,z434]),(0,[z195,z2,z3,z4,z5,z306]),(0,[z7,z2,z889,z3,z5,z6])],[(0,[z118,z599,z3,z4,z5,z6]),(0,[z890,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z148]),(0,[z7,z637,z344,z4,z5,z6])],[(0,[z7,z2,z3,z11,z174,z6]),(0,[z7,z2,z3,z4,z5,z14]),(0,[z7,z891,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z268]),(0,[z7,z2,z3,z4,z403,z42]),(0,[z892,z2,z3,z4,z5,z6]),(0,[z7,z2,z35,z3,z4,z32])]],
   [[(0,[z7,z2,z3,z893,z5,z6]),(0,[z7,z2,z3,z4,z86,z47]),(0,[z7,z40,z17,z3,z5,z42]),(0,[z7,z2,z17,z3,z5,z43])],[(0,[z7,z2,z3,z237,z5,z6]),(0,[z894,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z804,z99])],[(0,[z7,z2,z3,z4,z5,z895]),(0,[z7,z2,z22,z5,z665,z6]),(0,[z7,z896,z3,z4,z5,z6]),(0,[z7,z2,z3,z897,z5,z6]),(0,[z516,z2,z3,z627,z5,z6])],[(0,[z7,z2,z3,z898,z5,z6]),(0,[z563,z2,z217,z4,z5,z6]),(0,[z7,z2,z3,z22,z5,z368]),(0,[z370,z2,z3,z22,z5,z6]),(0,[z396,z7,z8,z3,z5,z6]),(0,[z7,z899,z17,z3,z5,z6]),(0,[z7,z342,z4,z5,z98,z6])],[(0,[z7,z2,z52,z237,z5,z6]),(0,[z33,z2,z3,z4,z5,z732]),(0,[z7,z2,z3,z4,z5,z900]),(0,[z7,z2,z222,z375,z5,z6]),(0,[z415,z2,z3,z517,z5,z6]),(0,[z114,z7,z2,z3,z79,z6])],[(0,[z664,z7,z103,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z177]),(0,[z7,z2,z901,z3,z5,z6])],[(0,[z7,z2,z3,z902,z5,z6]),(0,[z293,z2,z3,z4,z5,z34]),(0,[z7,z2,z903,z3,z5,z6]),(0,[z7,z2,z3,z904,z5,z6]),(0,[z75,z2,z17,z3,z5,z6]),(0,[z61,z7,z69,z4,z5,z115]),(0,[z12,z7,z2,z22,z98,z6]),(0,[z7,z2,z3,z905,z5,z6]),(0,[z7,z2,z3,z4,z779,z32])],[(0,[z51,z2,z52,z562,z5,z6]),(0,[z46,z7,z2,z634,z5,z6]),(0,[z7,z2,z3,z906,z5,z6]),(0,[z7,z2,z3,z22,z5,z907])],[(0,[z7,z279,z3,z772,z5,z6]),(0,[z10,z7,z3,z11,z116,z6]),(0,[z13,z2,z3,z4,z5,z43]),(0,[z2,z3,z4,z611,z98,z6])],[(0,[z908,z2,z3,z4,z5,z6]),(0,[z7,z2,z138,z3,z5,z160])],[(0,[z7,z2,z3,z22,z388,z6]),(0,[z7,z2,z3,z24,z909,z6]),(0,[z7,z2,z17,z444,z5,z6])],[(0,[z7,z357,z3,z11,z5,z6]),(0,[z7,z2,z910,z24,z5,z6]),(0,[z911,z2,z3,z4,z5,z6])],[(0,[z118,z66,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z912]),(0,[z46,z2,z110,z101,z5,z6]),(1,[z7,z2,z775,z5,z6]),(0,[z7,z342,z3,z22,z5,z6]),(0,[z913,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z491,z25]),(0,[z914,z2,z3,z4,z5,z6])],[(0,[z7,z2,z915,z4,z5,z6]),(0,[z7,z418,z3,z24,z5,z6]),(0,[z916,z2,z3,z4,z5,z6]),(0,[z165,z342,z3,z4,z5,z6]),(0,[z370,z2,z3,z4,z5,z177])],[(0,[z7,z2,z3,z4,z5,z917]),(0,[z510,z84,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z271]),(0,[z95,z7,z918,z4,z5,z6]),(0,[z7,z677,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z5,z919])],[(0,[z7,z2,z920,z4,z5,z6]),(0,[z67,z2,z3,z4,z68,z6]),(0,[z7,z2,z3,z4,z921,z6]),(0,[z7,z39,z8,z3,z5,z6]),(0,[z7,z472,z21,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z815])]],
   [[(0,[z7,z2,z922,z4,z5,z6]),(0,[z7,z2,z3,z106,z5,z6])],[],[(0,[z65,z84,z3,z4,z5,z6]),(0,[z7,z66,z3,z11,z5,z6]),(0,[z2,z84,z3,z4,z5,z390]),(0,[z7,z565,z3,z24,z5,z6]),(0,[z2,z3,z4,z875,z68,z6])],[(0,[z7,z2,z3,z923,z5,z6])],[(0,[z7,z2,z294,z24,z5,z6]),(0,[z7,z2,z3,z4,z86,z6]),(0,[z7,z585,z3,z4,z5,z42]),(0,[z7,z2,z3,z924,z5,z6])],[(0,[z7,z2,z154,z182,z5,z6]),(0,[z7,z2,z3,z925,z5,z6]),(0,[z926,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z11,z5,z878]),(0,[z7,z683,z3,z24,z5,z6]),(0,[z595,z2,z300,z4,z5,z6]),(0,[z7,z2,z69,z254,z5,z6]),(0,[z7,z2,z3,z4,z5,z804])],[(0,[z7,z2,z927,z4,z5,z6]),(0,[z7,z2,z928,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z929]),(0,[z7,z2,z3,z4,z18,z158]),(0,[z95,z7,z103,z24,z5,z6]),(0,[z409,z2,z3,z530,z5,z6]),(0,[z7,z2,z169,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z930]),(0,[z7,z342,z3,z858,z5,z6]),(0,[z7,z418,z3,z4,z491,z6])],[(0,[z7,z2,z3,z4,z931,z6]),(0,[z7,z2,z234,z11,z5,z6]),(0,[z7,z3,z11,z18,z116,z6]),(0,[z519,z2,z3,z24,z5,z6]),(0,[z7,z342,z3,z742,z5,z6]),(0,[z7,z2,z932,z3,z5,z6])],[(0,[z933,z7,z2,z3,z5,z6]),(0,[z7,z2,z934,z4,z5,z6]),(0,[z7,z2,z300,z4,z5,z6])],[(0,[z7,z2,z3,z11,z5,z88]),(0,[z7,z2,z3,z22,z238,z6]),(0,[z7,z2,z462,z3,z5,z6]),(0,[z7,z2,z3,z106,z5,z43])],[(0,[z7,z2,z3,z24,z5,z323]),(0,[z153,z7,z103,z4,z5,z6]),(0,[z7,z2,z3,z4,z935,z6]),(0,[z936,z2,z3,z4,z5,z6]),(0,[z7,z2,z410,z17,z5,z6])],[(0,[z7,z2,z3,z937,z5,z6]),(0,[z46,z2,z3,z101,z5,z368]),(0,[z113,z7,z3,z24,z116,z6]),(0,[z7,z40,z3,z4,z5,z727])],[(0,[z7,z2,z3,z4,z938,z6]),(0,[z7,z2,z939,z3,z5,z6]),(0,[z7,z2,z3,z940,z5,z6]),(0,[z516,z2,z3,z101,z5,z6]),(0,[z7,z2,z62,z4,z5,z324]),(0,[z7,z2,z300,z56,z5,z6]),(0,[z588,z7,z3,z4,z5,z115]),(0,[z7,z2,z133,z17,z5,z6])],[(0,[z7,z2,z3,z4,z941,z6]),(0,[z7,z2,z942,z4,z5,z6]),(0,[z7,z2,z440,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z368]),(0,[z370,z2,z3,z4,z5,z6]),(0,[z943,z2,z3,z4,z5,z6]),(0,[z7,z3,z24,z458,z5,z6]),(0,[z195,z2,z402,z4,z5,z6]),(0,[z7,z2,z17,z3,z5,z148]),(0,[z7,z2,z22,z116,z98,z6])]],
   [[(0,[z7,z2,z3,z4,z944,z6]),(0,[z7,z2,z3,z945,z5,z6]),(0,[z7,z3,z4,z5,z734,z6]),(0,[z7,z2,z17,z3,z174,z6])],[(0,[z122,z2,z946,z4,z5,z6]),(0,[z2,z3,z4,z5,z34,z732]),(0,[z7,z2,z3,z201,z5,z49]),(0,[z7,z2,z3,z947,z5,z6]),(0,[z7,z40,z3,z11,z5,z42]),(0,[z7,z2,z367,z22,z5,z6]),(0,[z948,z2,z3,z4,z5,z6])],[(0,[z7,z2,z154,z4,z311,z6]),(0,[z7,z2,z3,z4,z949,z6]),(0,[z93,z7,z2,z237,z5,z6]),(0,[z270,z2,z3,z24,z5,z6]),(0,[z12,z7,z2,z4,z98,z6]),(0,[z7,z2,z3,z950,z5,z6])],[(0,[z7,z2,z3,z22,z311,z6]),(0,[z7,z2,z3,z4,z5,z951]),(0,[z7,z2,z3,z4,z5,z907])],[(0,[z84,z3,z154,z4,z5,z6]),(0,[z7,z2,z294,z4,z5,z186]),(0,[z7,z2,z3,z203,z386,z6]),(0,[z7,z2,z3,z952,z5,z6]),(0,[z7,z2,z3,z11,z102,z6]),(0,[z7,z3,z11,z5,z116,z6]),(0,[z7,z2,z3,z4,z5,z953]),(0,[z7,z2,z954,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z955]),(0,[z7,z2,z3,z216,z5,z6]),(0,[z415,z2,z3,z24,z5,z6]),(0,[z13,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z22,z5,z14]),(0,[z2,z3,z4,z5,z956,z6])],[(0,[z7,z2,z3,z957,z4,z5]),(0,[z7,z2,z3,z4,z388,z6]),(0,[z7,z279,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z60,z271]),(0,[z7,z2,z3,z243,z5,z130])],[(0,[z122,z2,z217,z4,z5,z268]),(0,[z7,z2,z3,z958,z5,z6]),(0,[z7,z281,z3,z24,z5,z6]),(0,[z7,z275,z2,z3,z4,z32]),(0,[z7,z2,z3,z4,z959,z6]),(0,[z7,z2,z17,z3,z5,z177])],[(0,[z7,z2,z3,z4,z5,z960]),(0,[z961,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z962,z6]),(0,[z519,z637,z3,z4,z5,z6])],[(0,[z7,z84,z3,z375,z5,z6]),(0,[z118,z2,z217,z22,z5,z6])],[(0,[z7,z2,z3,z963,z5,z6]),(0,[z7,z2,z3,z4,z116,z271]),(0,[z7,z2,z3,z4,z5,z964]),(0,[z7,z965,z2,z3,z4,z5]),(0,[z7,z2,z3,z243,z5,z49]),(0,[z384,z2,z3,z4,z5,z76])],[(0,[z7,z2,z3,z966,z5,z6]),(0,[z7,z2,z3,z4,z6,z779])],[(0,[z7,z2,z967,z3,z5,z6]),(0,[z618,z7,z103,z4,z5,z6]),(0,[z7,z2,z634,z24,z5,z6]),(0,[z12,z7,z2,z4,z98,z43]),(0,[z270,z2,z3,z4,z491,z6])],[(0,[z7,z66,z3,z182,z5,z6]),(0,[z122,z279,z217,z4,z5,z6]),(0,[z7,z2,z946,z4,z5,z6]),(0,[z7,z2,z110,z4,z86,z6]),(0,[z7,z124,z3,z11,z116,z6]),(0,[z968,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z24,z5,z390]),(0,[z2,z3,z4,z611,z76,z6])],[(0,[z7,z3,z24,z500,z5,z6]),(0,[z75,z2,z3,z4,z31,z6]),(0,[z662,z7,z2,z4,z98,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z969]),(0,[z412,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z238,z34]),(0,[z7,z2,z344,z24,z5,z6]),(0,[z595,z2,z3,z4,z403,z6])],[(0,[z7,z2,z3,z4,z5,z970]),(0,[z7,z2,z3,z4,z971,z6]),(0,[z7,z108,z2,z3,z5,z53]),(0,[z270,z2,z3,z185,z5,z6])],[(0,[z7,z972,z3,z4,z5,z6]),(0,[z2,z217,z198,z22,z5,z6]),(0,[z7,z2,z3,z216,z102,z6]),(0,[z7,z2,z3,z973,z5,z6]),(0,[z575,z7,z2,z3,z79,z6]),(0,[z7,z2,z3,z974,z5,z6])],[(0,[z7,z2,z3,z4,z975,z6]),(0,[z118,z66,z3,z22,z5,z6]),(0,[z7,z2,z3,z976,z5,z6]),(0,[z7,z2,z3,z22,z5,z333]),(0,[z7,z2,z3,z4,z5,z868])],[(0,[z516,z84,z3,z11,z5,z6]),(0,[z7,z2,z977,z4,z5,z6]),(0,[z113,z7,z3,z4,z734,z6]),(0,[z7,z2,z22,z98,z6,z32]),(0,[z7,z224,z3,z978,z5,z6])],[(0,[z7,z279,z3,z4,z388,z6]),(0,[z7,z2,z217,z237,z5,z6]),(0,[z2,z3,z4,z979,z5,z6]),(0,[z7,z2,z17,z3,z762,z6])],[(0,[z7,z2,z3,z4,z238,z6]),(0,[z67,z2,z3,z22,z68,z6]),(0,[z7,z2,z103,z4,z102,z6])],[(0,[z118,z2,z154,z4,z5,z6]),(0,[z33,z2,z3,z4,z5,z145]),(0,[z7,z2,z980,z3,z5,z6])],[(0,[z65,z84,z154,z4,z5,z6]),(1,[z2,z946,z4,z5,z6]),(0,[z7,z2,z110,z4,z5,z368]),(0,[z7,z2,z3,z24,z5,z47]),(0,[z165,z2,z3,z106,z5,z6])],[(0,[z65,z84,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z435,z123]),(0,[z7,z565,z136,z4,z5,z6]),(0,[z7,z2,z981,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z779])],[(0,[z7,z2,z3,z4,z982,z6]),(0,[z1,z2,z3,z4,z188,z6]),(0,[z1,z2,z3,z24,z87,z6]),(0,[z95,z7,z103,z375,z5,z6]),(0,[z7,z245,z3,z24,z5,z6]),(0,[z165,z2,z3,z4,z19,z6])],[(0,[z7,z2,z3,z983,z5,z6]),(0,[z7,z2,z3,z4,z984,z6]),(0,[z7,z2,z3,z22,z86,z6])],[(0,[z7,z985,z3,z4,z5,z6]),(0,[z7,z2,z3,z986,z5,z6]),(0,[z7,z2,z17,z3,z5,z88]),(0,[z7,z2,z987,z3,z5,z6]),(0,[z7,z2,z3,z988,z5,z6]),(0,[z7,z3,z4,z5,z6,z727]),(0,[z7,z2,z3,z4,z989,z6]),(0,[z7,z637,z634,z4,z5,z6])],[(0,[z7,z2,z17,z154,z5,z6]),(0,[z7,z2,z3,z4,z5,z990]),(0,[z0,z2,z3,z24,z5,z36]),(0,[z7,z2,z3,z991,z5,z6]),(0,[z7,z2,z3,z4,z992,z6]),(0,[z7,z2,z3,z4,z5,z993]),(0,[z7,z994,z3,z4,z5,z6]),(0,[z995,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z996]),(0,[z646,z2,z52,z4,z5,z6]),(0,[z7,z8,z3,z5,z116,z6]),(0,[z7,z2,z3,z22,z5,z930]),(0,[z7,z418,z3,z4,z5,z73])],[(0,[z122,z2,z217,z11,z5,z6]),(0,[z165,z2,z3,z11,z5,z6]),(0,[z7,z2,z17,z62,z5,z73])]],
   [[(0,[z7,z2,z3,z11,z5,z368]),(0,[z370,z2,z3,z11,z5,z6]),(0,[z7,z2,z300,z22,z5,z6])],[(0,[z7,z2,z3,z997,z5,z6]),(0,[z7,z2,z3,z4,z5,z998]),(0,[z13,z2,z3,z4,z5,z6]),(0,[z7,z2,z125,z237,z5,z6]),(0,[z2,z3,z22,z611,z5,z6]),(0,[z12,z7,z2,z17,z98,z6])],[(0,[z2,z84,z3,z4,z5,z323]),(0,[z633,z7,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z123]),(0,[z7,z2,z17,z3,z5,z268]),(0,[z7,z2,z3,z999,z5,z6]),(0,[z7,z2,z3,z1000,z5,z6]),(0,[z7,z342,z3,z106,z5,z6]),(0,[z1001,z2,z3,z4,z5,z6])],[],[(0,[z7,z103,z4,z5,z115,z25]),(0,[z75,z2,z3,z4,z403,z6]),(0,[z7,z342,z3,z4,z19,z6])],[(0,[z7,z84,z3,z607,z5,z6]),(0,[z2,z3,z4,z5,z34,z390]),(0,[z33,z2,z3,z4,z5,z467]),(0,[z7,z2,z3,z4,z1002,z6]),(0,[z7,z224,z3,z1003,z5,z6])],[(0,[z7,z2,z17,z3,z102,z6]),(0,[z7,z2,z1004,z4,z5,z6])],[(0,[z7,z2,z3,z11,z388,z6]),(0,[z318,z2,z217,z4,z5,z6]),(0,[z7,z2,z3,z4,z1005,z6]),(0,[z7,z2,z402,z4,z5,z306])],[(0,[z7,z2,z3,z4,z109,z186]),(0,[z7,z279,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z1006,z6]),(0,[z7,z2,z3,z1007,z5,z6]),(0,[z7,z2,z3,z1008,z5,z6]),(0,[z7,z2,z3,z181,z5,z6]),(0,[z595,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z513,z491,z6])],[(0,[z7,z2,z3,z1009,z5,z6]),(0,[z7,z2,z1010,z4,z5,z6]),(0,[z7,z342,z3,z11,z5,z6])],[(0,[z7,z2,z294,z1011,z5,z6]),(0,[z7,z2,z3,z4,z5,z1012]),(0,[z7,z1013,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z4,z427]),(0,[z7,z163,z3,z11,z5,z6]),(0,[z7,z2,z69,z4,z5,z42]),(0,[z7,z2,z3,z4,z1014,z6])],[(0,[z7,z2,z3,z4,z5,z1015]),(0,[z7,z352,z3,z11,z5,z6]),(0,[z7,z2,z1016,z4,z5,z6])],[(0,[z1017,z2,z3,z4,z5,z6]),(0,[z7,z2,z1018,z4,z5,z6])],[(0,[z7,z2,z1019,z4,z5,z6]),(0,[z7,z2,z3,z381,z5,z486]),(0,[z7,z235,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z5,z779])],[(0,[z122,z2,z217,z4,z388,z6]),(0,[z7,z2,z3,z419,z5,z6]),(0,[z7,z2,z3,z4,z190,z76])],[(0,[z7,z2,z3,z4,z5,z333]),(0,[z1020,z2,z3,z4,z5,z6]),(0,[z913,z2,z17,z3,z5,z6])]],
   [[(0,[z65,z757,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1021]),(0,[z7,z3,z11,z5,z6,z630]),(0,[z1022,z2,z3,z4,z5,z6]),(0,[z1023,z2,z3,z4,z5,z6])],[(0,[z65,z84,z3,z430,z5,z6]),(0,[z7,z279,z3,z4,z5,z268]),(0,[z7,z2,z52,z419,z5,z6]),(0,[z380,z7,z773,z3,z5,z6])],[(0,[z7,z2,z1024,z3,z5,z6]),(0,[z7,z206,z3,z24,z5,z6]),(0,[z7,z2,z3,z1025,z5,z6]),(0,[z7,z2,z3,z4,z1026,z6]),(0,[z7,z2,z1027,z4,z5,z6]),(0,[z7,z2,z3,z1028,z5,z6]),(0,[z7,z40,z3,z181,z5,z42])],[(0,[z531,z2,z3,z4,z5,z6]),(0,[z7,z2,z58,z3,z5,z6]),(0,[z7,z2,z3,z22,z5,z260]),(0,[z270,z2,z3,z4,z5,z73]),(0,[z2,z3,z4,z1029,z5,z6])],[(0,[z2,z52,z217,z22,z5,z6]),(0,[z7,z1030,z3,z4,z5,z6]),(0,[z46,z2,z3,z101,z86,z6]),(0,[z7,z2,z3,z517,z5,z148])],[(0,[z1,z84,z3,z11,z5,z6]),(0,[z7,z2,z218,z3,z5,z6])],[(0,[z7,z2,z393,z22,z5,z6]),(0,[z7,z773,z3,z4,z5,z6]),(0,[z7,z209,z3,z143,z5,z6]),(0,[z7,z2,z3,z4,z491,z6])],[(0,[z7,z2,z1031,z4,z5,z6]),(0,[z7,z2,z3,z11,z238,z6]),(0,[z195,z2,z3,z339,z5,z6]),(0,[z412,z2,z3,z22,z5,z6]),(0,[z1032,z2,z3,z4,z5,z6]),(0,[z7,z2,z1033,z3,z5,z6])],[(0,[z7,z2,z330,z22,z5,z6]),(0,[z7,z2,z3,z5,z1034,z6])],[(0,[z7,z3,z179,z11,z5,z6]),(0,[z380,z7,z2,z3,z203,z6]),(0,[z7,z2,z440,z375,z5,z6]),(0,[z7,z2,z3,z1035,z5,z6])],[(0,[z7,z565,z3,z4,z149,z6]),(0,[z7,z2,z1036,z4,z5,z6]),(0,[z7,z2,z1037,z4,z5,z6]),(0,[z412,z2,z3,z4,z174,z6]),(0,[z2,z3,z4,z1038,z5,z6]),(0,[z519,z2,z3,z4,z5,z132])],[(0,[z7,z2,z1039,z4,z5,z6]),(0,[z2,z3,z285,z4,z5,z36]),(0,[z7,z398,z3,z11,z5,z6]),(0,[z7,z2,z1040,z4,z5,z6]),(0,[z7,z2,z3,z22,z403,z6]),(0,[z7,z2,z3,z106,z5,z14])],[(0,[z7,z2,z3,z4,z1041,z6]),(0,[z7,z66,z440,z3,z5,z6]),(0,[z7,z2,z3,z1042,z5,z6]),(0,[z7,z2,z3,z4,z102,z333]),(0,[z7,z3,z11,z5,z212,z6]),(0,[z7,z637,z3,z4,z5,z6]),(0,[z75,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z22,z18,z76])],[(0,[z7,z2,z3,z1043,z5,z6]),(0,[z7,z2,z3,z4,z19,z14])],[(0,[z7,z141,z3,z4,z5,z47]),(0,[z595,z2,z3,z4,z31,z6]),(0,[z662,z7,z2,z4,z5,z25])],[(0,[z7,z2,z3,z1044,z5,z6]),(0,[z7,z2,z136,z4,z5,z47]),(0,[z380,z2,z3,z101,z5,z6]),(0,[z7,z2,z402,z339,z5,z6]),(0,[z7,z277,z3,z4,z60,z6]),(0,[z7,z418,z3,z185,z5,z6])]],
   [[(0,[z7,z2,z3,z11,z311,z6]),(0,[z380,z71,z2,z3,z5,z6]),(0,[z1045,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z360,z203,z6])],[(0,[z51,z2,z3,z4,z5,z390]),(0,[z286,z2,z3,z22,z5,z6]),(0,[z7,z2,z798,z3,z5,z6]),(0,[z7,z2,z17,z3,z941,z6]),(0,[z165,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z4,z1046,z6])],[(0,[z7,z2,z3,z4,z1047,z6]),(0,[z7,z2,z17,z3,z5,z368]),(0,[z13,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z11,z5,z14]),(0,[z92,z7,z3,z11,z5,z6]),(0,[z7,z2,z3,z447,z5,z6]),(0,[z7,z2,z3,z4,z31,z6]),(0,[z370,z2,z17,z3,z5,z6])],[(0,[z7,z2,z3,z11,z5,z268]),(0,[z71,z2,z3,z346,z5,z6]),(0,[z7,z2,z3,z1048,z5,z6]),(0,[z7,z3,z103,z4,z102,z6]),(0,[z7,z2,z3,z888,z5,z6]),(0,[z7,z2,z462,z62,z5,z73])],[(0,[z1049,z2,z3,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1051]),(0,[z7,z2,z3,z1052,z5,z6])],[(0,[z93,z7,z2,z24,z5,z25]),(0,[z7,z2,z786,z300,z5,z6])],[(0,[z7,z699,z3,z11,z5,z6])],[],[(0,[z7,z2,z17,z3,z388,z6]),(0,[z7,z2,z3,z22,z5,z123]),(0,[z7,z436,z3,z11,z5,z6]),(0,[z7,z2,z22,z87,z98,z6]),(0,[z7,z2,z3,z1053,z5,z6]),(0,[z7,z2,z3,z1054,z5,z6]),(0,[z7,z2,z360,z22,z98,z6]),(0,[z165,z2,z3,z4,z5,z14]),(0,[z7,z418,z3,z1055,z5,z6])],[(0,[z7,z2,z3,z1056,z5,z6]),(0,[z7,z3,z4,z5,z42,z727])],[(0,[z2,z3,z4,z5,z732,z36]),(0,[z7,z2,z3,z1057,z5,z6]),(0,[z7,z342,z17,z3,z5,z6])],[(0,[z7,z2,z3,z4,z1058,z6]),(0,[z7,z2,z1059,z4,z5,z6])],[(0,[z54,z7,z103,z4,z5,z6]),(0,[z7,z2,z1018,z11,z5,z6]),(0,[z7,z2,z3,z4,z1060,z6])],[(0,[z2,z757,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1061]),(0,[z1062,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z517,z5,z6]),(0,[z7,z83,z2,z3,z22,z32]),(0,[z7,z2,z3,z4,z18,z207]),(0,[z7,z637,z3,z197,z5,z6]),(0,[z7,z2,z634,z4,z5,z132]),(0,[z7,z2,z3,z5,z49,z804])],[(0,[z7,z2,z3,z4,z5,z260]),(0,[z7,z2,z3,z375,z5,z6]),(0,[z7,z2,z234,z517,z5,z6]),(0,[z7,z2,z3,z1063,z5,z6])]],
   [[(0,[z118,z66,z3,z11,z5,z6]),(0,[z7,z3,z4,z800,z5,z6]),(0,[z93,z7,z2,z4,z491,z25])],[],[(0,[z7,z141,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z388,z268]),(0,[z384,z2,z3,z4,z5,z36]),(0,[z431,z7,z3,z4,z116,z6]),(0,[z7,z2,z1064,z3,z5,z6]),(0,[z7,z1065,z3,z4,z5,z6]),(0,[z7,z2,z344,z4,z5,z132])],[(0,[z7,z2,z967,z154,z5,z6]),(0,[z2,z52,z946,z4,z5,z6]),(0,[z67,z2,z3,z11,z68,z6]),(0,[z7,z2,z3,z1066,z5,z6]),(0,[z7,z3,z11,z5,z689,z6]),(0,[z61,z7,z8,z3,z5,z6]),(0,[z7,z2,z508,z4,z5,z73]),(0,[z13,z342,z3,z4,z5,z6]),(0,[z7,z342,z3,z4,z5,z14])],[(0,[z7,z2,z1067,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z1068]),(0,[z7,z3,z120,z375,z5,z6])],[(0,[z1069,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z148]),(0,[z7,z2,z22,z5,z6,z326]),(0,[z7,z2,z3,z22,z1070,z6]),(0,[z93,z7,z2,z185,z5,z25])],[(0,[z65,z84,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z1071]),(0,[z7,z2,z3,z4,z5,z1072]),(0,[z7,z2,z3,z24,z174,z6])],[(0,[z7,z2,z3,z1073,z5,z6]),(0,[z7,z2,z103,z237,z5,z6]),(0,[z7,z2,z3,z4,z403,z6]),(0,[z1074,z2,z3,z4,z5,z6])],[(0,[z7,z565,z3,z28,z5,z6]),(0,[z7,z2,z3,z11,z86,z6]),(0,[z405,z7,z3,z4,z116,z6]),(0,[z7,z2,z3,z4,z1075,z6]),(0,[z1076,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z104,z739,z6]),(0,[z7,z2,z3,z4,z18,z76])],[(0,[z1077,z7,z2,z3,z5,z6]),(0,[z7,z2,z17,z3,z238,z6])],[(0,[z7,z2,z1078,z3,z5,z6]),(0,[z302,z2,z3,z4,z68,z6]),(0,[z7,z2,z136,z101,z5,z6]),(0,[z7,z2,z3,z4,z37,z6]),(0,[z531,z2,z3,z22,z5,z6]),(1,[z7,z103,z4,z102,z6]),(0,[z113,z7,z402,z4,z116,z6]),(0,[z7,z2,z3,z1079,z5,z6])],[(0,[z7,z2,z3,z182,z311,z6]),(0,[z7,z3,z11,z5,z252,z6]),(0,[z7,z1080,z3,z4,z5,z6]),(0,[z425,z2,z3,z4,z68,z6]),(0,[z595,z2,z69,z4,z5,z6]),(0,[z7,z2,z3,z56,z403,z6])],[(0,[z7,z2,z3,z4,z102,z260])],[(0,[z286,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z577,z5,z34]),(0,[z1,z2,z3,z4,z5,z88]),(0,[z7,z2,z300,z11,z5,z6]),(0,[z7,z2,z3,z24,z5,z177]),(0,[z7,z2,z3,z22,z491,z6])],[(0,[z7,z2,z3,z4,z1081,z6]),(0,[z7,z2,z419,z5,z98,z6]),(0,[z7,z2,z22,z5,z361,z6]),(0,[z1032,z2,z3,z22,z5,z6]),(0,[z7,z2,z164,z218,z5,z6])],[(0,[z7,z2,z3,z339,z5,z306]),(0,[z12,z7,z2,z106,z98,z6])]],
   [[(0,[z7,z2,z3,z4,z86,z368])],[(0,[z7,z1082,z3,z4,z5,z6]),(0,[z2,z3,z4,z611,z5,z6]),(0,[z7,z2,z3,z90,z5,z6]),(0,[z12,z7,z2,z4,z726,z6]),(0,[z270,z224,z3,z4,z5,z6])],[(0,[z7,z2,z17,z3,z311,z6]),(0,[z7,z2,z217,z419,z5,z6]),(0,[z7,z424,z3,z4,z5,z42])],[(0,[z7,z2,z3,z1083,z5,z6]),(0,[z7,z1084,z3,z4,z5,z6]),(0,[z415,z2,z402,z4,z5,z6]),(0,[z7,z637,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z1085])],[(0,[z7,z2,z3,z4,z1086,z6]),(0,[z7,z2,z3,z1087,z5,z6]),(0,[z7,z1088,z3,z4,z5,z6]),(0,[z7,z39,z3,z4,z102,z6]),(0,[z13,z2,z17,z3,z5,z6]),(0,[z7,z2,z17,z3,z5,z14])],[(0,[z7,z2,z3,z1089,z5,z6]),(0,[z7,z2,z3,z1090,z5,z6]),(0,[z7,z2,z3,z24,z5,z754]),(0,[z7,z2,z410,z105,z5,z6]),(0,[z755,z2,z3,z24,z5,z6]),(0,[z7,z2,z402,z1091,z5,z6])],[(0,[z7,z66,z3,z607,z5,z6]),(0,[z7,z2,z3,z24,z435,z6]),(0,[z7,z2,z1092,z3,z5,z6]),(0,[z12,z7,z2,z11,z98,z6]),(0,[z7,z124,z3,z339,z5,z6]),(0,[z7,z2,z22,z5,z387,z6])],[(0,[z67,z2,z3,z523,z68,z6]),(0,[z7,z2,z3,z1093,z5,z6]),(0,[z7,z2,z199,z22,z5,z6]),(0,[z7,z2,z3,z4,z739,z6]),(0,[z7,z108,z2,z3,z5,z99])],[(0,[z7,z2,z3,z4,z1094,z6]),(0,[z7,z2,z1095,z4,z5,z6]),(0,[z1096,z2,z3,z4,z5,z6]),(0,[z1097,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1098,z5,z6]),(0,[z1099,z7,z2,z3,z5,z6])],[(0,[z380,z7,z2,z3,z5,z1100]),(0,[z7,z654,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z1101]),(0,[z7,z2,z3,z22,z31,z6]),(0,[z7,z2,z276,z3,z341,z6]),(1,[z7,z2,z4,z5,z868])],[(0,[z7,z2,z451,z22,z5,z6]),(0,[z286,z2,z3,z4,z102,z6]),(0,[z95,z7,z103,z4,z96,z6])],[(0,[z2,z84,z217,z22,z5,z6]),(0,[z7,z141,z110,z4,z5,z6]),(0,[z7,z2,z3,z607,z5,z6]),(0,[z7,z103,z4,z5,z102,z6]),(0,[z490,z7,z3,z11,z5,z6]),(0,[z7,z40,z3,z90,z5,z42])],[(0,[z7,z2,z3,z205,z5,z382]),(0,[z13,z2,z3,z4,z5,z14]),(0,[z7,z499,z2,z3,z5,z99])],[(0,[z7,z2,z17,z234,z5,z6]),(0,[z7,z2,z3,z4,z60,z148]),(0,[z61,z7,z3,z254,z5,z115]),(0,[z7,z2,z3,z1102,z5,z6]),(0,[z114,z370,z2,z3,z79,z6]),(0,[z7,z637,z3,z4,z5,z177])],[(0,[z7,z2,z3,z221,z96,z6]),(0,[z7,z2,z3,z1103,z5,z6])],[(0,[z7,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z162,z435,z6]),(0,[z75,z2,z69,z4,z5,z6]),(0,[z7,z2,z62,z4,z5,z868]),(0,[z7,z235,z3,z4,z5,z132])]],
   [[(0,[z7,z2,z3,z4,z5,z1104]),(0,[z7,z2,z1105,z4,z5,z6]),(0,[z46,z2,z3,z484,z5,z6]),(0,[z7,z2,z3,z11,z5,z260]),(0,[z7,z2,z234,z24,z5,z6]),(0,[z7,z637,z3,z104,z5,z6])],[(0,[z65,z84,z3,z182,z5,z6]),(0,[z7,z2,z3,z4,z1106,z6]),(0,[z7,z2,z3,z1107,z5,z6]),(0,[z7,z2,z3,z4,z116,z148]),(0,[z7,z2,z3,z4,z1070,z6])],[(0,[z7,z2,z3,z4,z1108,z6]),(0,[z118,z66,z17,z3,z5,z6]),(0,[z184,z3,z217,z4,z5,z6]),(0,[z1,z2,z217,z22,z5,z6]),(0,[z7,z2,z3,z24,z5,z88]),(0,[z7,z1109,z3,z4,z5,z6])],[(0,[z7,z2,z3,z179,z5,z6]),(0,[z7,z184,z3,z22,z5,z6]),(0,[z7,z2,z21,z4,z102,z6]),(0,[z7,z103,z4,z116,z98,z6]),(0,[z7,z2,z3,z4,z403,z115])],[(0,[z7,z2,z1110,z4,z5,z6]),(0,[z7,z279,z3,z4,z5,z123]),(0,[z7,z1111,z3,z4,z5,z6]),(0,[z412,z2,z3,z11,z5,z6])],[(0,[z67,z2,z17,z3,z68,z6]),(0,[z7,z2,z3,z4,z5,z1112]),(0,[z669,z7,z3,z4,z116,z6]),(0,[z384,z2,z3,z4,z5,z32])],[(0,[z84,z3,z217,z11,z5,z6]),(0,[z7,z2,z3,z1113,z5,z6]),(0,[z7,z2,z164,z440,z5,z6]),(0,[z7,z3,z24,z591,z5,z6]),(0,[z7,z2,z3,z4,z1114,z6])],[(0,[z7,z2,z3,z1115,z5,z6]),(0,[z7,z105,z8,z3,z5,z6]),(0,[z7,z2,z22,z60,z98,z6]),(0,[z7,z2,z1116,z3,z5,z6]),(0,[z93,z7,z2,z4,z5,z868])],[(0,[z65,z84,z17,z3,z5,z6]),(0,[z7,z2,z3,z162,z5,z6]),(0,[z71,z7,z2,z634,z5,z6]),(0,[z7,z2,z3,z11,z403,z6])],[(0,[z2,z84,z154,z4,z5,z6]),(0,[z7,z2,z3,z4,z1117,z6]),(0,[z7,z141,z3,z22,z5,z6]),(0,[z7,z2,z3,z11,z18,z76]),(0,[z7,z40,z3,z24,z5,z42]),(0,[z7,z2,z3,z24,z5,z43])],[(0,[z7,z2,z136,z22,z5,z6]),(0,[z7,z2,z17,z3,z86,z6]),(0,[z2,z3,z795,z101,z5,z6]),(0,[z7,z2,z1118,z402,z5,z6]),(0,[z113,z7,z3,z4,z116,z306]),(0,[z7,z2,z3,z1119,z5,z6])],[(0,[z7,z2,z1120,z4,z5,z6]),(0,[z7,z3,z11,z5,z345,z6]),(0,[z7,z2,z3,z1121,z5,z6]),(0,[z7,z2,z3,z1122,z5,z6])],[(0,[z7,z317,z3,z11,z5,z6]),(0,[z7,z2,z142,z22,z5,z6]),(0,[z7,z2,z3,z24,z102,z6]),(0,[z7,z2,z3,z1123,z5,z6])],[(0,[z7,z570,z3,z11,z5,z6]),(0,[z600,z2,z3,z4,z68,z6]),(0,[z7,z224,z3,z513,z5,z6])],[(0,[z7,z2,z294,z4,z109,z6]),(0,[z65,z84,z3,z4,z311,z6]),(0,[z7,z279,z3,z24,z5,z6]),(0,[z7,z2,z147,z22,z5,z6]),(0,[z7,z2,z3,z5,z1124,z6]),(0,[z286,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z185,z5,z6]),(0,[z13,z2,z3,z106,z5,z6])],[(0,[z7,z2,z3,z45,z435,z6]),(0,[z7,z83,z2,z3,z4,z623])]],
   [[(0,[z7,z2,z3,z1125,z5,z6]),(0,[z7,z2,z17,z300,z5,z6])],[(0,[z33,z2,z217,z22,z5,z6]),(0,[z7,z703,z3,z11,z5,z6]),(0,[z7,z2,z3,z22,z37,z6]),(0,[z7,z39,z656,z4,z5,z6]),(0,[z7,z2,z3,z1126,z5,z6]),(0,[z7,z124,z3,z24,z60,z6])],[(0,[z195,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1127])],[(0,[z7,z2,z217,z375,z5,z6]),(0,[z531,z2,z3,z4,z102,z6]),(0,[z415,z2,z3,z4,z5,z306]),(0,[z7,z2,z1128,z3,z5,z6])],[(0,[z7,z2,z3,z22,z5,z1129]),(0,[z7,z230,z105,z3,z5,z6])],[(0,[z378,z2,z217,z4,z5,z6]),(0,[z7,z2,z3,z5,z1130,z6]),(0,[z7,z2,z3,z4,z1131,z6])],[(0,[z7,z2,z3,z4,z5,z1132]),(0,[z7,z2,z3,z4,z5,z1133]),(0,[z7,z184,z3,z4,z435,z6]),(0,[z7,z2,z3,z11,z5,z123]),(0,[z7,z2,z393,z136,z5,z6]),(0,[z7,z2,z3,z4,z5,z1134]),(0,[z7,z2,z69,z22,z5,z6])],[(0,[z33,z84,z3,z11,z5,z6]),(0,[z7,z124,z3,z765,z5,z6]),(0,[z7,z2,z532,z22,z5,z6]),(0,[z7,z2,z3,z24,z5,z812]),(0,[z7,z1135,z3,z4,z5,z6]),(0,[z7,z597,z3,z120,z5,z6]),(0,[z7,z2,z22,z5,z475,z6])],[(0,[z7,z2,z3,z45,z5,z6]),(0,[z7,z2,z110,z24,z5,z6]),(0,[z46,z7,z637,z3,z5,z6]),(0,[z1,z2,z3,z4,z87,z263]),(0,[z7,z2,z3,z1055,z5,z6]),(0,[z7,z2,z234,z4,z60,z6]),(0,[z7,z2,z4,z5,z6,z868])],[(0,[z7,z2,z3,z4,z1136,z6]),(0,[z7,z2,z1137,z4,z5,z6]),(0,[z7,z2,z3,z1138,z5,z6]),(0,[z510,z7,z3,z4,z5,z115]),(0,[z7,z336,z2,z3,z4,z32]),(0,[z7,z2,z3,z56,z31,z6])],[(0,[z7,z1139,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1140,z6])],[(0,[z7,z2,z3,z750,z5,z6]),(0,[z7,z2,z3,z4,z5,z1141]),(0,[z7,z604,z3,z11,z5,z6]),(0,[z7,z2,z17,z650,z5,z6])],[(0,[z7,z2,z1142,z4,z5,z6]),(0,[z7,z2,z3,z4,z1143,z6]),(0,[z7,z2,z220,z4,z5,z73]),(0,[z7,z2,z3,z4,z5,z1144]),(0,[z7,z2,z1145,z4,z5,z6]),(0,[z7,z2,z234,z4,z116,z6]),(0,[z7,z124,z8,z3,z5,z6]),(0,[z7,z1146,z3,z4,z5,z6]),(0,[z7,z2,z1147,z4,z5,z6])],[(0,[z7,z2,z1148,z4,z5,z6]),(0,[z7,z66,z3,z375,z5,z6]),(0,[z122,z2,z217,z4,z5,z123])],[(0,[z457,z7,z3,z11,z5,z6]),(0,[z7,z2,z1149,z4,z5,z6]),(0,[z618,z7,z3,z4,z116,z6])],[(0,[z7,z184,z3,z4,z5,z6]),(0,[z1150,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z1151]),(0,[z7,z2,z3,z1152,z5,z6]),(0,[z7,z2,z3,z800,z5,z6]),(0,[z7,z2,z22,z5,z503,z6]),(0,[z12,z7,z2,z4,z98,z14])],[(0,[z7,z2,z1153,z3,z5,z6])],[(0,[z7,z2,z3,z1154,z5,z6]),(0,[z7,z184,z52,z4,z5,z6]),(0,[z7,z2,z3,z562,z5,z6]),(0,[z46,z141,z3,z101,z5,z6]),(0,[z7,z2,z17,z3,z5,z260]),(0,[z113,z7,z3,z339,z116,z6])],[(0,[z7,z2,z3,z1155,z5,z6]),(0,[z7,z2,z3,z5,z1156,z6]),(0,[z7,z2,z3,z11,z5,z333])],[(0,[z7,z2,z3,z1157,z5,z6]),(0,[z7,z2,z1158,z4,z5,z6]),(0,[z7,z2,z3,z1159,z5,z6])],[(0,[z7,z2,z154,z24,z5,z6]),(0,[z7,z2,z3,z4,z388,z123]),(0,[z7,z2,z3,z4,z5,z1160]),(0,[z7,z2,z52,z375,z5,z6]),(0,[z7,z2,z3,z22,z5,z132])],[(0,[z7,z2,z136,z4,z5,z6]),(0,[z176,z2,z3,z4,z5,z34]),(0,[z1161,z2,z3,z4,z5,z6]),(0,[z113,z195,z3,z4,z116,z6]),(0,[z588,z7,z3,z4,z116,z6]),(0,[z412,z2,z17,z3,z5,z6])],[(0,[z7,z2,z3,z1162,z5,z6]),(0,[z7,z279,z3,z45,z5,z6]),(0,[z122,z2,z217,z24,z5,z6]),(0,[z7,z2,z3,z4,z875,z6]),(0,[z7,z2,z3,z5,z1163,z6]),(0,[z531,z2,z3,z11,z5,z6]),(0,[z165,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z4,z1164,z6]),(0,[z7,z2,z17,z3,z5,z970])],[(0,[z7,z2,z3,z24,z5,z368]),(0,[z7,z2,z3,z1165,z5,z6]),(0,[z0,z2,z3,z4,z5,z158]),(0,[z7,z2,z3,z4,z5,z1166])],[(0,[z51,z2,z3,z4,z435,z6]),(0,[z2,z3,z217,z4,z5,z390]),(0,[z7,z2,z3,z4,z98,z271]),(0,[z7,z2,z3,z1167,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1168]),(0,[z7,z2,z3,z11,z491,z6]),(0,[z7,z2,z17,z3,z403,z6])],[(0,[z7,z2,z3,z22,z149,z6]),(0,[z7,z2,z3,z1169,z5,z6]),(0,[z7,z2,z17,z3,z18,z76])],[(0,[z7,z2,z3,z1170,z5,z6]),(0,[z7,z637,z3,z5,z79,z6])],[(0,[z83,z2,z3,z4,z68,z34]),(0,[z7,z2,z3,z1171,z5,z6])],[(0,[z287,z2,z217,z4,z5,z6]),(0,[z71,z2,z3,z198,z5,z6]),(0,[z7,z2,z3,z4,z1172,z6]),(0,[z7,z3,z11,z5,z450,z6]),(0,[z7,z2,z234,z1171,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1173]),(0,[z122,z2,z17,z217,z5,z6]),(0,[z7,z3,z11,z5,z256,z6]),(0,[z7,z440,z3,z5,z116,z6]),(0,[z7,z2,z222,z120,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z1174]),(0,[z122,z2,z217,z162,z5,z6]),(0,[z286,z2,z17,z3,z5,z6]),(0,[z7,z2,z3,z1175,z5,z6]),(0,[z7,z637,z3,z11,z5,z6]),(0,[z7,z2,z3,z1176,z5,z6]),(0,[z7,z2,z3,z1177,z5,z6]),(0,[z7,z2,z3,z1178,z5,z6]),(0,[z7,z2,z3,z4,z5,z1129])],[(0,[z7,z2,z3,z1179,z5,z6]),(0,[z2,z3,z4,z314,z68,z6]),(0,[z7,z2,z3,z216,z5,z333]),(0,[z1180,z2,z3,z4,z5,z6]),(0,[z474,z7,z3,z4,z5,z115]),(0,[z7,z342,z3,z24,z5,z6])],[(0,[z7,z2,z69,z4,z5,z6]),(0,[z61,z7,z3,z4,z5,z727]),(0,[z7,z2,z3,z1181,z5,z6])],[(0,[z7,z2,z3,z4,z149,z47]),(0,[z380,z7,z2,z3,z79,z6]),(0,[z7,z2,z3,z381,z5,z49]),(0,[z7,z2,z3,z1182,z5,z6]),(0,[z7,z2,z22,z5,z555,z6])],[(0,[z7,z2,z294,z4,z5,z323]),(0,[z270,z418,z3,z4,z5,z6])],[(0,[z7,z2,z154,z4,z5,z186]),(0,[z7,z2,z3,z1011,z5,z6]),(0,[z531,z2,z3,z216,z5,z6]),(0,[z7,z2,z103,z4,z5,z333]),(0,[z1183,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z1184,z6])],[(0,[z7,z2,z3,z22,z5,z186]),(0,[z7,z2,z3,z203,z86,z6]),(0,[z114,z7,z2,z3,z86,z6]),(0,[z33,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z11,z31,z6]),(0,[z7,z2,z3,z4,z5,z1185]),(0,[z7,z2,z69,z56,z5,z6])],[(0,[z7,z2,z3,z4,z1186,z6]),(0,[z95,z7,z103,z221,z5,z6]),(0,[z7,z2,z3,z1187,z5,z6]),(0,[z30,z7,z3,z11,z5,z6]),(0,[z7,z2,z305,z22,z5,z6])],[(0,[z7,z2,z17,z3,z5,z123]),(0,[z7,z2,z464,z22,z5,z6]),(0,[z7,z2,z3,z5,z1188,z6]),(0,[z7,z2,z3,z1189,z5,z6]),(0,[z7,z2,z3,z185,z174,z6]),(0,[z370,z637,z3,z4,z5,z6])],[(0,[z7,z2,z164,z210,z5,z6]),(0,[z531,z2,z103,z4,z5,z6]),(0,[z95,z531,z103,z4,z5,z6]),(0,[z195,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z5,z1190,z6])],[(0,[z51,z2,z196,z4,z5,z6]),(0,[z7,z2,z3,z626,z4,z32])],[(0,[z195,z2,z3,z4,z5,z148])],[(0,[z66,z757,z3,z4,z5,z6]),(0,[z7,z2,z217,z162,z5,z6])],[(0,[z7,z2,z1191,z3,z5,z6]),(0,[z7,z1192,z3,z4,z5,z6])],[(0,[z2,z3,z217,z4,z435,z6]),(0,[z7,z2,z3,z4,z5,z1193]),(0,[z1194,z2,z3,z4,z5,z6]),(0,[z7,z281,z3,z433,z5,z6])],[(0,[z7,z2,z3,z1195,z5,z6]),(0,[z7,z2,z3,z1196,z5,z6]),(0,[z7,z2,z3,z4,z1197,z6]),(0,[z343,z2,z3,z4,z5,z36]),(0,[z7,z2,z440,z103,z5,z6]),(0,[z7,z2,z1198,z4,z5,z6]),(0,[z7,z290,z3,z11,z5,z6]),(0,[z1199,z2,z3,z4,z5,z6]),(0,[z7,z2,z1200,z69,z5,z6]),(0,[z7,z2,z3,z1201,z5,z6])]],
   [[(0,[z7,z184,z3,z11,z5,z6]),(0,[z122,z2,z217,z45,z5,z6]),(0,[z459,z2,z3,z4,z87,z6]),(0,[z91,z2,z3,z4,z5,z36]),(0,[z7,z2,z1202,z3,z5,z6])],[(0,[z7,z2,z402,z22,z5,z6]),(0,[z7,z3,z4,z5,z727,z115]),(0,[z7,z2,z3,z4,z5,z132])],[(0,[z84,z3,z112,z11,z5,z6]),(0,[z7,z2,z3,z4,z1203,z6]),(0,[z7,z2,z210,z110,z5,z6]),(0,[z7,z224,z3,z22,z5,z6])],[(0,[z7,z2,z3,z1204,z5,z6]),(0,[z7,z2,z3,z4,z1205,z6]),(0,[z7,z2,z3,z4,z5,z1206]),(0,[z7,z1207,z3,z4,z5,z6]),(0,[z384,z2,z3,z4,z5,z390]),(0,[z581,z7,z103,z4,z5,z6]),(0,[z7,z2,z1208,z4,z5,z6]),(0,[z7,z2,z402,z4,z5,z148]),(0,[z7,z2,z3,z1209,z5,z6]),(0,[z7,z1210,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1211]),(0,[z687,z2,z52,z4,z5,z6]),(0,[z7,z2,z21,z237,z5,z6])],[(0,[z7,z671,z3,z11,z5,z6]),(0,[z411,z2,z3,z101,z5,z6]),(0,[z7,z2,z17,z3,z5,z333]),(0,[z7,z224,z3,z4,z174,z6])],[(0,[z7,z2,z3,z1212,z5,z6]),(0,[z7,z141,z3,z11,z5,z6]),(0,[z2,z3,z4,z5,z6,z732]),(0,[z7,z2,z3,z4,z5,z1213]),(0,[z7,z2,z3,z24,z5,z993]),(0,[z7,z2,z1200,z3,z5,z6])],[(0,[z7,z2,z1214,z3,z5,z6]),(0,[z122,z184,z217,z4,z5,z6]),(0,[z7,z2,z3,z4,z149,z6]),(0,[z7,z2,z136,z11,z5,z6]),(0,[z1215,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1216,z6])],[(0,[z7,z2,z3,z24,z311,z6]),(0,[z7,z2,z3,z4,z1217,z6]),(0,[z118,z2,z3,z4,z37,z6]),(0,[z2,z3,z28,z795,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1218]),(0,[z531,z2,z17,z3,z5,z6]),(0,[z7,z3,z234,z4,z116,z6]),(0,[z7,z2,z3,z1219,z5,z6]),(0,[z7,z2,z62,z4,z5,z73]),(0,[z7,z2,z3,z104,z203,z6])],[(0,[z7,z2,z377,z22,z5,z6]),(0,[z2,z3,z4,z397,z68,z6]),(0,[z13,z2,z3,z24,z5,z6]),(0,[z7,z2,z3,z24,z5,z14]),(0,[z200,z7,z3,z4,z5,z115])],[(0,[z7,z2,z1220,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z268]),(0,[z51,z2,z624,z4,z5,z6]),(0,[z1,z2,z3,z4,z693,z6]),(0,[z7,z2,z3,z4,z18,z374]),(0,[z7,z2,z22,z5,z6,z603]),(0,[z1221,z2,z3,z4,z5,z6])],[(0,[z684,z84,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z491,z6])],[(0,[z7,z2,z300,z4,z403,z6]),(0,[z519,z2,z344,z4,z5,z6])],[(0,[z7,z2,z3,z430,z5,z186]),(0,[z7,z2,z52,z162,z5,z6]),(0,[z7,z2,z3,z4,z5,z1222]),(0,[z71,z2,z3,z4,z86,z6]),(0,[z7,z141,z3,z4,z5,z368]),(0,[z7,z2,z3,z4,z5,z1223]),(0,[z7,z2,z3,z11,z37,z6]),(0,[z7,z2,z237,z5,z73,z6]),(0,[z7,z2,z69,z4,z5,z115])],[(0,[z7,z2,z1224,z4,z5,z6]),(0,[z7,z2,z3,z1225,z5,z6]),(0,[z7,z2,z3,z4,z1226,z6]),(0,[z7,z2,z136,z4,z5,z368]),(0,[z7,z2,z3,z4,z76,z271]),(0,[z200,z7,z3,z11,z5,z6]),(0,[z7,z124,z3,z4,z696,z6])]],
   [[(0,[z51,z84,z3,z11,z5,z6]),(0,[z0,z2,z3,z4,z5,z623]),(0,[z2,z3,z4,z611,z19,z6]),(0,[z7,z418,z3,z513,z5,z6])],[(0,[z7,z2,z3,z4,z1227,z6]),(0,[z2,z3,z4,z101,z86,z6]),(0,[z7,z2,z3,z22,z5,z263]),(0,[z7,z2,z3,z216,z5,z260])],[(0,[z7,z2,z3,z4,z5,z186]),(0,[z7,z637,z17,z3,z5,z6])],[(0,[z7,z184,z217,z4,z5,z6]),(0,[z7,z184,z3,z862,z5,z6]),(0,[z7,z2,z69,z11,z5,z6]),(0,[z1228,z2,z3,z4,z5,z6]),(0,[z1229,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z162,z5,z268]),(0,[z7,z2,z3,z4,z5,z1230]),(0,[z7,z2,z1016,z24,z5,z6]),(0,[z7,z2,z3,z134,z5,z160]),(0,[z7,z1231,z3,z4,z5,z6])],[(0,[z7,z261,z2,z3,z5,z334]),(0,[z7,z2,z3,z1232,z5,z6])],[(0,[z7,z2,z3,z22,z96,z6]),(0,[z7,z3,z918,z4,z5,z6]),(0,[z195,z2,z234,z4,z5,z6])],[(0,[z7,z2,z3,z1233,z5,z6]),(0,[z7,z2,z3,z1234,z5,z6]),(0,[z33,z2,z3,z11,z5,z34]),(0,[z7,z2,z3,z120,z5,z6]),(0,[z7,z418,z3,z4,z5,z25]),(0,[z7,z2,z3,z1235,z5,z6])],[(0,[z7,z2,z3,z4,z109,z323]),(0,[z118,z66,z3,z24,z5,z6]),(0,[z7,z2,z17,z3,z31,z6]),(0,[z2,z3,z4,z1236,z5,z6])],[(0,[z7,z3,z24,z11,z5,z6])],[(0,[z7,z279,z3,z162,z5,z6]),(0,[z0,z2,z3,z4,z37,z6])],[(0,[z7,z2,z3,z1237,z5,z6]),(0,[z1,z2,z3,z4,z505,z6]),(0,[z7,z2,z17,z110,z5,z6]),(0,[z67,z2,z3,z24,z68,z6]),(0,[z7,z2,z3,z1238,z5,z6])],[(0,[z84,z3,z11,z5,z6,z36]),(0,[z118,z66,z3,z179,z5,z6]),(0,[z51,z2,z52,z22,z5,z6]),(0,[z7,z2,z3,z1239,z5,z6])],[(0,[z7,z2,z1240,z4,z5,z6]),(0,[z7,z2,z402,z4,z5,z6]),(0,[z7,z2,z24,z722,z5,z6])],[(0,[z65,z84,z3,z24,z5,z6]),(1,[z184,z217,z4,z5,z6]),(0,[z7,z224,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1241,z6]),(0,[z7,z2,z1242,z3,z5,z6])],[(0,[z531,z2,z3,z4,z5,z333]),(0,[z286,z2,z3,z216,z5,z6])]],
   [[(0,[z7,z2,z1243,z3,z5,z6]),(0,[z7,z2,z110,z4,z149,z6]),(0,[z7,z2,z3,z24,z86,z6]),(1,[z7,z234,z4,z116,z6]),(0,[z7,z2,z1244,z3,z5,z6])],[(0,[z7,z2,z3,z4,z1245,z6]),(0,[z200,z7,z103,z4,z5,z6]),(0,[z7,z3,z11,z5,z407,z6]),(0,[z7,z2,z1246,z3,z5,z6]),(0,[z7,z2,z3,z22,z5,z306]),(0,[z7,z2,z342,z4,z98,z6]),(0,[z7,z2,z3,z1247,z5,z6])],[(0,[z66,z84,z3,z11,z5,z6]),(0,[z7,z184,z17,z3,z5,z6]),(0,[z7,z1248,z3,z4,z5,z6]),(0,[z1249,z2,z3,z4,z5,z6]),(0,[z7,z3,z103,z4,z5,z333]),(0,[z7,z2,z3,z11,z5,z132]),(0,[z7,z2,z1250,z3,z5,z6]),(0,[z1251,z2,z3,z4,z5,z6]),(0,[z7,z2,z775,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1252]),(0,[z496,z2,z3,z4,z5,z34]),(0,[z7,z2,z22,z5,z641,z6]),(0,[z7,z2,z3,z433,z5,z6])],[(0,[z7,z1253,z3,z4,z5,z6]),(0,[z7,z2,z3,z45,z5,z268]),(0,[z620,z2,z3,z4,z5,z36]),(0,[z7,z2,z3,z736,z5,z6]),(1,[z7,z3,z800,z5,z6])],[(0,[z487,z84,z3,z4,z5,z6]),(0,[z7,z2,z3,z1254,z5,z6]),(0,[z7,z2,z300,z24,z5,z6]),(0,[z270,z2,z3,z513,z5,z6])],[(0,[z287,z7,z103,z4,z5,z6]),(0,[z46,z2,z136,z101,z5,z6]),(0,[z531,z3,z103,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z830]),(0,[z7,z2,z222,z22,z98,z6])],[(0,[z7,z2,z3,z4,z5,z1255]),(0,[z7,z2,z3,z5,z6,z804])],[(0,[z7,z2,z3,z4,z832,z6]),(0,[z7,z2,z3,z1256,z5,z6]),(0,[z7,z141,z17,z3,z5,z6]),(0,[z7,z2,z3,z11,z149,z6]),(0,[z642,z7,z2,z4,z5,z25]),(0,[z7,z2,z3,z11,z1216,z6]),(0,[z7,z1257,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1258]),(0,[z7,z2,z3,z978,z5,z6])],[],[(0,[z7,z184,z3,z4,z5,z268]),(0,[z7,z2,z1259,z4,z5,z6]),(0,[z370,z2,z3,z24,z5,z6])],[(0,[z7,z1260,z3,z4,z5,z6]),(0,[z51,z2,z210,z52,z5,z6]),(0,[z7,z2,z3,z4,z5,z1261]),(0,[z7,z2,z3,z795,z5,z6]),(0,[z7,z2,z3,z221,z5,z6]),(0,[z7,z2,z918,z4,z5,z6]),(0,[z270,z2,z3,z4,z5,z25])],[(0,[z7,z2,z3,z1262,z5,z6]),(0,[z7,z2,z3,z4,z5,z263]),(0,[z7,z2,z1263,z3,z5,z6]),(0,[z1,z2,z3,z4,z87,z390]),(0,[z7,z2,z3,z1264,z5,z6]),(0,[z7,z2,z1118,z3,z5,z6]),(0,[z92,z7,z3,z375,z5,z6]),(0,[z7,z2,z3,z433,z5,z43])],[(0,[z7,z2,z3,z4,z1265,z6]),(0,[z12,z7,z2,z24,z98,z6]),(0,[z415,z2,z3,z339,z5,z6])],[(0,[z7,z3,z295,z11,z5,z6])]],
   [[(0,[z7,z2,z17,z3,z37,z6]),(0,[z7,z2,z237,z5,z98,z6]),(0,[z7,z2,z1266,z3,z5,z6]),(0,[z7,z2,z62,z22,z5,z73]),(0,[z7,z2,z3,z1267,z5,z6]),(0,[z7,z83,z2,z3,z4,z32])],[(0,[z7,z2,z3,z1268,z5,z6]),(0,[z7,z40,z3,z4,z5,z264]),(0,[z7,z40,z69,z4,z5,z6])],[(0,[z7,z2,z3,z1269,z5,z6]),(0,[z7,z2,z3,z24,z388,z6]),(0,[z411,z2,z217,z4,z5,z6]),(0,[z7,z2,z3,z4,z96,z6]),(0,[z595,z2,z3,z254,z5,z6]),(0,[z1270,z2,z3,z4,z5,z6]),(0,[z7,z2,z493,z4,z5,z73])],[(0,[z7,z2,z3,z11,z5,z186]),(0,[z7,z3,z4,z734,z116,z6])],[(0,[z7,z2,z105,z3,z5,z752])],[(0,[z7,z84,z8,z3,z5,z6]),(0,[z7,z2,z3,z1271,z5,z6]),(1,[z2,z3,z4,z875,z6]),(0,[z473,z7,z103,z4,z5,z6]),(0,[z7,z2,z3,z1272,z5,z6]),(0,[z7,z628,z2,z3,z4,z32])],[(0,[z7,z2,z3,z4,z1273,z6]),(0,[z33,z2,z3,z4,z238,z34]),(0,[z195,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z254,z5,z6]),(0,[z7,z1274,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1275,z6]),(0,[z7,z3,z11,z19,z116,z6]),(0,[z7,z1276,z3,z4,z5,z6])],[(0,[z51,z2,z52,z4,z5,z6]),(0,[z7,z1277,z3,z4,z5,z6]),(0,[z7,z315,z2,z3,z5,z53]),(0,[z7,z2,z3,z1091,z5,z6])],[(0,[z7,z805,z3,z4,z5,z6]),(0,[z7,z2,z460,z22,z5,z6]),(1,[z7,z103,z4,z5,z333]),(0,[z7,z1278,z3,z22,z5,z6])],[(0,[z7,z2,z3,z1003,z5,z6]),(0,[z7,z2,z3,z1279,z5,z6])],[(0,[z7,z2,z3,z162,z388,z6]),(0,[z7,z1280,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1281,z6]),(0,[z7,z3,z69,z4,z5,z115]),(0,[z7,z2,z300,z4,z31,z6]),(0,[z7,z2,z1282,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1283]),(0,[z7,z2,z3,z4,z5,z1284]),(0,[z509,z7,z3,z11,z5,z6]),(0,[z7,z2,z3,z1285,z5,z6]),(0,[z412,z2,z3,z24,z5,z6]),(0,[z1286,z2,z3,z4,z5,z6])],[(0,[z7,z66,z3,z1196,z5,z6]),(0,[z7,z2,z3,z4,z5,z306]),(0,[z7,z2,z3,z1287,z5,z6]),(0,[z7,z2,z22,z5,z6,z688])],[(0,[z7,z2,z234,z4,z5,z306]),(0,[z7,z2,z62,z63,z5,z73])],[(0,[z7,z2,z3,z1288,z5,z6]),(0,[z531,z2,z3,z4,z5,z260]),(0,[z7,z2,z3,z4,z5,z752]),(0,[z7,z224,z3,z11,z5,z6])]],
   [[(0,[z7,z2,z3,z1289,z5,z6]),(0,[z7,z3,z470,z11,z116,z6]),(0,[z7,z2,z3,z24,z403,z6]),(0,[z1290,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1291]),(0,[z515,z2,z3,z4,z68,z6]),(0,[z439,z7,z2,z4,z5,z25]),(0,[z7,z209,z3,z24,z5,z6]),(0,[z7,z2,z3,z24,z18,z76]),(0,[z2,z17,z3,z611,z5,z6]),(0,[z7,z108,z2,z3,z5,z422])],[(0,[z7,z2,z3,z1292,z5,z6]),(0,[z7,z2,z3,z24,z238,z6])],[(0,[z7,z2,z793,z22,z5,z6]),(0,[z7,z39,z3,z4,z5,z333]),(0,[z431,z7,z2,z4,z98,z6])],[(0,[z7,z2,z3,z1293,z5,z6]),(0,[z7,z3,z375,z5,z116,z6]),(0,[z7,z2,z17,z3,z5,z132])],[(0,[z7,z2,z3,z430,z109,z6]),(0,[z1,z2,z3,z4,z619,z6]),(0,[z7,z209,z3,z179,z5,z6]),(0,[z51,z2,z17,z52,z5,z6]),(0,[z7,z124,z234,z4,z5,z6]),(0,[z7,z2,z1294,z4,z5,z6])],[(0,[z7,z141,z3,z4,z86,z6]),(0,[z286,z2,z3,z24,z5,z6]),(0,[z1295,z2,z3,z4,z5,z6]),(0,[z75,z2,z3,z254,z5,z6]),(0,[z1296,z2,z3,z4,z5,z6]),(0,[z412,z2,z3,z4,z491,z6])],[(0,[z7,z2,z3,z1297,z5,z6]),(0,[z7,z2,z136,z4,z86,z6]),(0,[z46,z2,z3,z101,z149,z6]),(0,[z531,z39,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1100]),(0,[z7,z2,z3,z1298,z5,z6]),(0,[z7,z2,z3,z1299,z5,z6]),(0,[z7,z2,z1158,z11,z5,z6]),(0,[z1300,z2,z3,z4,z5,z6]),(0,[z471,z2,z3,z484,z5,z6]),(0,[z7,z2,z3,z4,z1301,z6]),(0,[z384,z2,z3,z22,z5,z6]),(0,[z7,z108,z2,z3,z5,z804])],[(0,[z7,z2,z3,z4,z109,z6]),(0,[z7,z2,z1302,z3,z5,z6]),(0,[z7,z2,z736,z4,z5,z6]),(0,[z286,z2,z3,z4,z5,z333]),(0,[z7,z2,z775,z22,z5,z6]),(0,[z7,z2,z3,z1303,z5,z6])],[(0,[z44,z2,z3,z4,z5,z36]),(0,[z7,z2,z17,z3,z149,z6]),(0,[z7,z2,z3,z1304,z5,z6])],[(0,[z7,z2,z3,z45,z388,z6]),(0,[z7,z2,z217,z120,z5,z6]),(0,[z165,z2,z3,z433,z5,z6])],[(0,[z7,z2,z294,z22,z5,z6]),(0,[z7,z2,z3,z1305,z5,z6]),(0,[z7,z2,z3,z4,z1306,z6]),(0,[z519,z2,z634,z4,z5,z6])],[(0,[z7,z2,z3,z1307,z5,z6]),(0,[z2,z3,z946,z4,z5,z6]),(0,[z7,z2,z1308,z3,z5,z6]),(0,[z7,z1309,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z68,z263]),(0,[z7,z2,z3,z1310,z5,z6]),(0,[z7,z2,z3,z24,z5,z998])],[(0,[z7,z2,z3,z182,z5,z186]),(0,[z7,z1311,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z123]),(0,[z7,z2,z3,z11,z5,z263]),(0,[z7,z83,z2,z3,z4,z271]),(0,[z7,z8,z3,z24,z5,z6]),(0,[z7,z2,z69,z1028,z5,z6]),(0,[z61,z7,z3,z22,z5,z115])],[(0,[z7,z261,z2,z3,z5,z99])]],
   [[(0,[z7,z2,z3,z4,z5,z1312]),(0,[z7,z2,z3,z1313,z5,z6]),(0,[z1,z2,z3,z4,z87,z271]),(0,[z7,z2,z3,z1314,z5,z6]),(0,[z7,z281,z3,z1315,z5,z6])],[(0,[z7,z2,z3,z1316,z5,z6]),(0,[z7,z918,z103,z4,z5,z6]),(0,[z10,z7,z2,z3,z79,z6])],[(0,[z7,z184,z3,z4,z388,z6]),(0,[z7,z565,z3,z4,z5,z47]),(0,[z7,z2,z21,z4,z5,z333]),(0,[z7,z2,z300,z1170,z5,z6]),(0,[z114,z7,z2,z3,z79,z132])],[(0,[z7,z2,z1317,z3,z5,z6])],[(0,[z380,z7,z2,z3,z5,z6]),(0,[z113,z7,z3,z22,z116,z6]),(0,[z7,z1318,z3,z4,z5,z6]),(0,[z7,z2,z17,z70,z5,z6])],[(0,[z7,z2,z17,z3,z5,z186]),(0,[z7,z1319,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z1320,z6]),(0,[z7,z2,z3,z339,z5,z6]),(0,[z7,z1278,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1321,z6]),(0,[z7,z2,z3,z1322,z5,z6]),(0,[z531,z2,z21,z4,z5,z6]),(0,[z113,z7,z3,z4,z116,z148]),(0,[z7,z1323,z3,z4,z5,z6]),(0,[z7,z1324,z3,z4,z5,z6]),(0,[z7,z2,z3,z1325,z5,z6])],[(0,[z7,z2,z154,z1268,z5,z6]),(0,[z7,z2,z3,z4,z5,z1326])],[(0,[z195,z2,z17,z3,z5,z6]),(0,[z93,z412,z2,z4,z5,z25])],[(0,[z411,z2,z217,z22,z5,z6]),(0,[z7,z2,z3,z1327,z5,z6]),(0,[z51,z2,z52,z11,z5,z6]),(0,[z7,z2,z3,z1328,z5,z6]),(0,[z7,z2,z1329,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1330]),(0,[z7,z408,z3,z4,z5,z42]),(0,[z7,z69,z4,z5,z6,z115]),(0,[z153,z7,z2,z4,z5,z25]),(0,[z270,z2,z3,z22,z5,z6])],[(0,[z7,z2,z3,z4,z311,z186]),(0,[z2,z217,z22,z5,z6,z36]),(0,[z2,z436,z3,z4,z68,z6]),(0,[z7,z2,z3,z24,z5,z333]),(0,[z553,z7,z3,z11,z5,z6]),(0,[z7,z2,z3,z1331,z5,z6]),(0,[z7,z1332,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1333]),(0,[z7,z2,z3,z4,z238,z76]),(0,[z1022,z2,z3,z24,z5,z6])],[(0,[z7,z2,z52,z120,z5,z6]),(0,[z7,z2,z3,z1334,z5,z6]),(0,[z7,z2,z3,z4,z5,z710])],[(0,[z7,z2,z3,z5,z1335,z6]),(0,[z7,z2,z3,z4,z909,z6]),(0,[z161,z2,z3,z4,z5,z36]),(0,[z7,z2,z22,z68,z98,z6]),(0,[z7,z2,z3,z1336,z5,z6]),(0,[z7,z2,z3,z4,z5,z732]),(0,[z7,z2,z3,z4,z1337,z6]),(0,[z384,z2,z3,z4,z5,z34]),(0,[z7,z2,z3,z4,z1338,z6]),(0,[z7,z2,z105,z3,z5,z830]),(0,[z1339,z2,z3,z4,z5,z6]),(0,[z7,z39,z21,z22,z5,z6])],[(0,[z531,z2,z3,z24,z5,z6]),(0,[z7,z2,z1340,z3,z5,z6]),(0,[z541,z7,z3,z11,z5,z6]),(0,[z7,z2,z3,z1341,z5,z6]),(1,[z7,z2,z3,z5,z804])]],
   [[(0,[z7,z2,z3,z5,z1342,z6])],[(0,[z7,z2,z1343,z4,z5,z6]),(0,[z7,z1344,z3,z4,z5,z6]),(0,[z7,z2,z247,z22,z5,z6]),(0,[z7,z2,z3,z1345,z5,z6]),(0,[z7,z418,z3,z4,z5,z6]),(0,[z7,z224,z17,z3,z5,z6])],[(0,[z7,z2,z3,z4,z5,z271]),(0,[z7,z2,z3,z1346,z5,z6]),(0,[z7,z2,z105,z237,z5,z6]),(0,[z7,z2,z3,z24,z491,z6])],[(0,[z7,z2,z3,z1347,z5,z6]),(0,[z7,z2,z1198,z11,z5,z6])],[(0,[z7,z2,z294,z430,z5,z6]),(0,[z7,z2,z489,z22,z5,z6]),(0,[z384,z2,z3,z4,z5,z6]),(0,[z7,z1348,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1349]),(0,[z7,z94,z3,z11,z5,z6])],[(0,[z46,z2,z3,z795,z5,z6]),(0,[z7,z124,z3,z11,z5,z6]),(1,[z7,z342,z4,z98,z6])],[(0,[z7,z565,z3,z4,z5,z6]),(0,[z7,z2,z3,z1350,z5,z6]),(0,[z67,z2,z3,z4,z875,z6]),(0,[z7,z2,z3,z22,z5,z390]),(0,[z7,z2,z3,z1351,z5,z6]),(0,[z7,z2,z1036,z24,z5,z6]),(0,[z7,z2,z3,z1352,z5,z6])],[(0,[z7,z2,z3,z45,z5,z123]),(0,[z7,z2,z3,z4,z1353,z6]),(0,[z7,z773,z3,z5,z68,z6]),(0,[z7,z2,z1040,z24,z5,z6]),(0,[z595,z2,z3,z4,z5,z42])],[(0,[z7,z2,z294,z4,z5,z6]),(0,[z7,z3,z143,z11,z5,z6]),(0,[z7,z637,z3,z24,z5,z6]),(0,[z7,z2,z344,z22,z5,z6])],[(0,[z7,z2,z1354,z4,z5,z6]),(0,[z71,z7,z637,z3,z5,z6]),(0,[z0,z2,z3,z4,z68,z76]),(0,[z286,z2,z3,z4,z5,z260]),(0,[z93,z7,z2,z513,z5,z25]),(0,[z114,z7,z2,z3,z739,z6]),(0,[z7,z2,z3,z739,z79,z6]),(0,[z7,z2,z3,z203,z739,z6])],[(0,[z380,z7,z2,z3,z5,z806]),(0,[z7,z2,z3,z72,z203,z6]),(0,[z61,z7,z3,z4,z5,z115]),(0,[z7,z2,z3,z269,z5,z6])],[(0,[z95,z7,z103,z4,z5,z6]),(0,[z7,z103,z4,z5,z6,z333])],[(0,[z51,z2,z946,z4,z5,z6]),(0,[z519,z2,z3,z4,z5,z6]),(0,[z7,z1355,z3,z4,z5,z6]),(0,[z7,z494,z3,z11,z5,z6]),(0,[z7,z3,z197,z11,z5,z6]),(0,[z7,z3,z11,z116,z6,z32]),(0,[z7,z608,z3,z11,z5,z6]),(0,[z7,z2,z1356,z3,z5,z6])],[(0,[z7,z565,z3,z101,z5,z6]),(0,[z7,z2,z3,z4,z1357,z6]),(0,[z7,z2,z3,z4,z1358,z6]),(0,[z7,z2,z62,z11,z5,z73]),(0,[z575,z7,z2,z3,z117,z6]),(0,[z370,z2,z3,z4,z5,z132]),(0,[z519,z235,z3,z4,z5,z6])],[(0,[z7,z184,z3,z4,z5,z123]),(0,[z7,z2,z3,z4,z5,z1359]),(0,[z1360,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z31,z6]),(0,[z61,z7,z3,z56,z5,z115])],[(0,[z7,z2,z3,z4,z5,z323]),(0,[z7,z2,z154,z4,z109,z6]),(0,[z7,z2,z3,z4,z577,z76]),(0,[z7,z3,z11,z87,z116,z6]),(0,[z740,z2,z3,z4,z5,z6]),(0,[z741,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1361,z5,z6]),(0,[z1362,z2,z3,z4,z5,z6]),(0,[z7,z1260,z17,z3,z5,z6])]],
   [[(0,[z7,z2,z3,z22,z109,z6]),(0,[z7,z2,z210,z22,z5,z6]),(0,[z7,z2,z17,z3,z5,z263]),(0,[z152,z7,z2,z4,z5,z25]),(0,[z113,z7,z3,z4,z116,z6]),(0,[z7,z1363,z3,z4,z5,z6]),(0,[z802,z2,z3,z4,z5,z6]),(0,[z7,z85,z2,z3,z4,z32])],[(0,[z65,z84,z3,z4,z5,z186]),(0,[z482,z2,z3,z4,z68,z6]),(0,[z46,z370,z2,z3,z5,z6]),(0,[z7,z2,z3,z5,z6,z1364]),(0,[z7,z2,z1365,z4,z5,z6]),(0,[z7,z3,z11,z116,z98,z6]),(0,[z7,z2,z3,z4,z746,z6]),(0,[z113,z7,z234,z4,z116,z6])],[(0,[z308,z66,z3,z4,z5,z6]),(0,[z2,z946,z217,z4,z5,z6]),(0,[z7,z2,z22,z18,z98,z6])],[(0,[z7,z2,z3,z4,z149,z368]),(0,[z380,z67,z2,z3,z68,z6]),(0,[z7,z2,z69,z4,z403,z6]),(0,[z1366,z2,z3,z4,z5,z6])],[(0,[z405,z84,z3,z4,z5,z6]),(0,[z7,z2,z1367,z4,z5,z6]),(0,[z7,z1368,z3,z4,z5,z6]),(0,[z7,z2,z3,z1369,z5,z6]),(0,[z7,z2,z798,z222,z5,z6]),(0,[z7,z2,z3,z4,z5,z1370]),(0,[z114,z7,z2,z344,z79,z6])],[(0,[z7,z2,z3,z4,z1371,z6]),(0,[z7,z1372,z3,z4,z5,z6]),(0,[z0,z2,z3,z22,z5,z36]),(0,[z7,z2,z3,z1373,z5,z6]),(0,[z7,z2,z17,z3,z96,z6]),(0,[z7,z2,z1246,z234,z5,z6]),(0,[z1374,z2,z3,z4,z5,z6]),(0,[z114,z7,z2,z3,z475,z6])],[(0,[z7,z2,z3,z4,z5,z1375]),(0,[z84,z217,z103,z4,z5,z6]),(0,[z270,z2,z3,z4,z5,z6]),(0,[z1376,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z765,z5,z6])],[(0,[z7,z2,z440,z21,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1377]),(0,[z7,z582,z2,z3,z4,z32]),(0,[z7,z2,z3,z5,z739,z6])],[(0,[z415,z2,z3,z4,z5,z6]),(0,[z7,z1378,z3,z4,z5,z6])],[(1,[z2,z3,z795,z5,z6]),(1,[z7,z2,z736,z5,z6]),(0,[z415,z2,z234,z4,z5,z6])],[(0,[z7,z281,z3,z4,z5,z6]),(0,[z7,z2,z3,z24,z5,z260]),(0,[z7,z2,z8,z3,z5,z6]),(0,[z7,z2,z3,z1379,z5,z6]),(0,[z61,z595,z3,z4,z5,z115])],[(0,[z7,z2,z3,z221,z102,z6]),(0,[z7,z2,z1380,z3,z5,z6]),(0,[z7,z2,z3,z1381,z5,z6])],[(0,[z7,z2,z3,z4,z693,z76])],[(0,[z7,z141,z3,z24,z5,z6]),(0,[z7,z2,z3,z339,z5,z148]),(0,[z7,z2,z1382,z3,z5,z6]),(0,[z7,z2,z22,z5,z98,z6]),(0,[z187,z2,z199,z3,z5,z6]),(0,[z7,z17,z1146,z3,z5,z6])],[(0,[z7,z565,z110,z4,z5,z6]),(0,[z7,z2,z136,z24,z5,z6]),(0,[z71,z2,z3,z203,z68,z6]),(0,[z7,z2,z3,z1383,z5,z6]),(0,[z7,z2,z1384,z3,z5,z6])]],
   [[(0,[z7,z1385,z3,z4,z5,z6]),(0,[z7,z3,z11,z5,z629,z6]),(0,[z7,z2,z17,z3,z5,z306]),(0,[z7,z2,z626,z22,z5,z6]),(0,[z7,z2,z634,z4,z5,z6]),(0,[z2,z3,z4,z1386,z5,z6])],[(0,[z1387,z7,z2,z3,z5,z6]),(0,[z51,z2,z3,z4,z5,z123]),(0,[z7,z2,z3,z4,z5,z834]),(0,[z7,z2,z3,z4,z5,z1388]),(0,[z7,z2,z402,z11,z5,z6]),(0,[z7,z235,z634,z4,z5,z6])],[(0,[z7,z141,z3,z179,z5,z6]),(0,[z7,z2,z3,z4,z5,z390]),(0,[z7,z2,z3,z4,z5,z1389]),(0,[z7,z8,z3,z5,z42,z6]),(0,[z7,z2,z17,z3,z5,z752]),(0,[z7,z2,z3,z4,z1390,z6]),(0,[z7,z2,z1391,z4,z5,z6])],[(0,[z7,z2,z3,z1392,z5,z6]),(0,[z7,z29,z3,z11,z5,z6]),(0,[z7,z569,z3,z24,z5,z6]),(0,[z114,z7,z2,z634,z79,z6])],[(0,[z7,z279,z3,z1269,z5,z6]),(0,[z7,z3,z607,z5,z116,z6]),(0,[z7,z2,z344,z4,z5,z6]),(0,[z370,z2,z3,z4,z203,z6])],[(0,[z384,z2,z3,z11,z5,z6]),(0,[z7,z2,z3,z1393,z5,z6]),(0,[z1394,z7,z2,z3,z5,z6]),(0,[z7,z281,z3,z4,z5,z43]),(0,[z7,z235,z344,z4,z5,z6])],[(0,[z7,z2,z3,z24,z37,z6])],[(0,[z7,z2,z22,z5,z246,z6]),(0,[z7,z1395,z3,z4,z5,z6])],[(0,[z7,z565,z3,z530,z5,z6]),(0,[z7,z418,z3,z22,z5,z6])],[(0,[z7,z2,z294,z11,z5,z6]),(0,[z2,z3,z4,z87,z875,z6]),(0,[z7,z2,z3,z22,z5,z271]),(0,[z7,z2,z1396,z3,z5,z6]),(0,[z355,z7,z2,z3,z212,z6]),(0,[z7,z2,z17,z22,z5,z6])],[(0,[z7,z573,z3,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z1397]),(0,[z7,z2,z3,z4,z1398,z6])],[(0,[z7,z2,z3,z4,z5,z1399]),(0,[z7,z2,z3,z1400,z5,z6]),(0,[z61,z7,z3,z11,z5,z115]),(0,[z7,z2,z69,z24,z5,z6]),(0,[z7,z418,z3,z4,z174,z6]),(0,[z7,z83,z2,z3,z4,z467])],[(0,[z7,z2,z1401,z3,z5,z6]),(0,[z7,z2,z3,z1402,z5,z6]),(0,[z7,z701,z3,z24,z5,z6]),(0,[z7,z83,z2,z17,z3,z32]),(0,[z12,z7,z281,z4,z98,z6]),(0,[z7,z2,z4,z726,z98,z6]),(0,[z7,z418,z4,z5,z6,z25]),(0,[z7,z2,z3,z1403,z5,z6])],[(0,[z7,z2,z3,z1404,z5,z6]),(0,[z7,z565,z3,z22,z5,z6]),(0,[z46,z2,z199,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z1405]),(0,[z2,z3,z4,z5,z68,z88])],[(0,[z1,z2,z3,z4,z87,z6]),(0,[z7,z2,z3,z4,z5,z1406]),(0,[z412,z2,z3,z185,z5,z6])],[(0,[z33,z2,z3,z24,z5,z34]),(0,[z7,z2,z1407,z4,z5,z6]),(0,[z7,z2,z3,z1408,z5,z6])]],
   [[(0,[z7,z2,z730,z294,z5,z6]),(0,[z7,z2,z3,z1409,z5,z6]),(0,[z30,z7,z3,z800,z5,z6])],[(0,[z7,z2,z3,z1410,z5,z6]),(0,[z0,z2,z3,z4,z5,z36]),(0,[z1411,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1412]),(0,[z95,z7,z103,z22,z5,z6]),(0,[z7,z2,z3,z513,z5,z6]),(0,[z165,z2,z3,z4,z98,z6]),(0,[z12,z7,z2,z433,z98,z6])],[(0,[z7,z2,z3,z1413,z5,z6]),(0,[z528,z2,z3,z4,z68,z6]),(0,[z519,z2,z3,z22,z5,z6]),(0,[z7,z2,z3,z1414,z5,z6]),(0,[z7,z2,z3,z4,z491,z73])],[(0,[z7,z2,z3,z1415,z5,z6]),(0,[z7,z2,z3,z4,z1416,z6]),(0,[z75,z2,z3,z22,z5,z6])],[(0,[z7,z2,z154,z4,z5,z323]),(0,[z7,z2,z3,z4,z1417,z6]),(0,[z7,z2,z3,z1418,z5,z6]),(0,[z7,z2,z1419,z3,z5,z6]),(1,[z7,z69,z4,z5,z115]),(0,[z7,z2,z660,z22,z5,z6])],[(0,[z7,z2,z3,z22,z5,z323]),(0,[z7,z2,z1420,z4,z5,z6]),(0,[z7,z2,z3,z11,z96,z6]),(0,[z7,z2,z3,z1421,z5,z6]),(0,[z7,z2,z3,z4,z5,z1422]),(0,[z7,z550,z3,z24,z5,z6]),(0,[z7,z1423,z3,z4,z5,z6]),(0,[z7,z2,z3,z1424,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1425]),(0,[z7,z1363,z3,z22,z5,z6])],[(0,[z7,z2,z136,z203,z5,z6]),(0,[z7,z2,z3,z5,z523,z6]),(0,[z7,z2,z3,z4,z6,z1426]),(0,[z7,z342,z3,z433,z5,z6]),(0,[z83,z2,z3,z4,z611,z6])],[(0,[z7,z2,z234,z339,z5,z6])],[(0,[z84,z3,z11,z5,z68,z6]),(0,[z7,z2,z3,z162,z5,z123]),(0,[z7,z2,z1427,z4,z5,z6]),(0,[z7,z2,z3,z4,z476,z76])],[(0,[z95,z7,z105,z103,z5,z6]),(0,[z7,z39,z21,z11,z5,z6]),(0,[z412,z224,z3,z4,z5,z6])],[(0,[z595,z2,z3,z4,z5,z6]),(0,[z7,z342,z3,z4,z98,z6]),(0,[z7,z2,z3,z4,z1428,z6])],[(0,[z7,z2,z3,z4,z1429,z6]),(0,[z519,z2,z3,z4,z5,z177])],[(0,[z642,z2,z217,z4,z5,z6]),(0,[z93,z7,z2,z22,z5,z25]),(0,[z7,z2,z511,z22,z5,z6])],[(0,[z7,z3,z530,z11,z5,z6]),(0,[z71,z2,z3,z5,z648,z6]),(0,[z7,z2,z222,z22,z5,z6]),(0,[z2,z3,z4,z18,z611,z76])]],
   [[(0,[z415,z2,z3,z22,z5,z6]),(0,[z270,z2,z3,z4,z174,z6])],[(0,[z7,z2,z3,z11,z5,z306]),(0,[z7,z2,z69,z4,z31,z6])],[(0,[z7,z2,z910,z4,z5,z6]),(0,[z7,z2,z1430,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z1431]),(0,[z415,z2,z3,z4,z5,z148]),(0,[z7,z2,z1432,z4,z5,z6]),(0,[z7,z281,z3,z22,z5,z6]),(0,[z7,z2,z3,z4,z5,z1433])],[(0,[z7,z2,z17,z609,z5,z6]),(0,[z165,z281,z3,z4,z5,z6])],[(0,[z7,z2,z294,z182,z5,z6]),(0,[z7,z2,z3,z4,z238,z36]),(0,[z7,z2,z3,z216,z96,z6]),(0,[z7,z1344,z17,z3,z5,z6])],[(0,[z7,z141,z136,z4,z5,z6]),(0,[z7,z2,z1434,z3,z5,z6]),(0,[z7,z209,z3,z800,z5,z6]),(0,[z2,z3,z4,z611,z60,z6])],[(0,[z46,z565,z3,z101,z5,z6]),(0,[z7,z2,z375,z5,z98,z6])],[(0,[z118,z2,z3,z4,z109,z6]),(0,[z7,z2,z22,z5,z331,z6]),(0,[z369,z7,z2,z4,z98,z6]),(0,[z7,z2,z634,z22,z5,z6]),(0,[z384,z2,z17,z3,z5,z6])],[(0,[z118,z568,z3,z4,z5,z6]),(0,[z380,z7,z2,z1019,z5,z6]),(0,[z1435,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z725]),(0,[z7,z2,z533,z22,z5,z6]),(0,[z7,z2,z17,z775,z5,z6])],[(0,[z118,z593,z3,z4,z5,z6]),(0,[z2,z3,z11,z611,z5,z6]),(0,[z2,z3,z4,z611,z116,z6]),(0,[z7,z2,z276,z22,z5,z6]),(0,[z7,z2,z17,z344,z5,z6])],[(0,[z409,z2,z3,z28,z5,z6]),(0,[z7,z2,z3,z1436,z5,z6]),(0,[z7,z2,z3,z4,z5,z737]),(0,[z7,z637,z3,z4,z5,z132])],[(0,[z7,z2,z3,z24,z5,z186])],[(0,[z7,z1437,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z732]),(0,[z7,z2,z3,z1438,z5,z6]),(0,[z7,z2,z17,z3,z5,z830]),(0,[z7,z792,z3,z4,z5,z6])],[(0,[z7,z2,z1439,z4,z5,z6]),(0,[z7,z2,z3,z11,z109,z6]),(0,[z2,z84,z3,z4,z37,z6]),(0,[z2,z573,z3,z4,z5,z36]),(0,[z7,z584,z3,z11,z5,z6]),(0,[z61,z7,z17,z3,z5,z115]),(0,[z575,z7,z2,z22,z98,z6]),(0,[z7,z899,z3,z4,z5,z6]),(0,[z7,z2,z3,z1440,z5,z6])],[(0,[z7,z2,z3,z430,z5,z323]),(0,[z7,z568,z3,z11,z5,z6]),(0,[z1,z2,z3,z4,z875,z6]),(0,[z195,z2,z3,z24,z5,z6]),(0,[z7,z2,z22,z5,z362,z6])],[(0,[z0,z2,z3,z4,z5,z390]),(0,[z7,z593,z3,z11,z5,z6]),(0,[z7,z124,z440,z3,z5,z6]),(0,[z7,z2,z532,z375,z5,z6])]],
   [[(0,[z75,z2,z3,z4,z5,z6]),(0,[z1441,z2,z3,z4,z5,z6]),(0,[z1442,z2,z3,z4,z5,z6])],[(0,[z7,z2,z294,z4,z311,z6]),(0,[z7,z2,z3,z1443,z5,z6]),(0,[z7,z2,z440,z22,z5,z6]),(0,[z13,z2,z3,z433,z5,z6]),(0,[z7,z2,z3,z433,z5,z14]),(0,[z7,z2,z634,z4,z5,z177])],[(0,[z0,z2,z3,z11,z5,z36]),(0,[z309,z2,z3,z4,z5,z36]),(0,[z1444,z2,z3,z4,z5,z6])],[(0,[z51,z2,z330,z4,z5,z6]),(0,[z7,z2,z3,z22,z5,z47]),(0,[z113,z7,z17,z3,z116,z6]),(0,[z2,z3,z4,z1445,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1446]),(0,[z7,z2,z3,z1447,z5,z6]),(0,[z7,z2,z3,z4,z1448,z6]),(0,[z75,z2,z3,z56,z5,z6]),(0,[z7,z2,z3,z185,z491,z6]),(0,[z7,z2,z634,z104,z5,z6])],[(0,[z380,z7,z2,z3,z86,z6]),(0,[z1,z2,z3,z22,z87,z6]),(0,[z7,z2,z1137,z24,z5,z6]),(0,[z7,z2,z418,z4,z5,z25]),(0,[z7,z2,z344,z4,z5,z177])],[(0,[z7,z2,z3,z4,z5,z1449]),(0,[z7,z2,z3,z4,z280,z76])],[(0,[z7,z224,z3,z24,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1450]),(0,[z7,z2,z3,z4,z5,z1451]),(0,[z7,z2,z3,z470,z203,z6]),(0,[z7,z2,z17,z634,z5,z6]),(0,[z7,z2,z3,z1315,z5,z6])],[(0,[z7,z66,z8,z3,z5,z6]),(0,[z270,z2,z17,z3,z5,z6])],[(0,[z7,z3,z1196,z11,z5,z6]),(0,[z173,z2,z3,z4,z68,z6]),(0,[z7,z3,z103,z120,z5,z6]),(0,[z93,z7,z2,z4,z5,z25])],[(0,[z7,z184,z3,z24,z5,z6]),(0,[z7,z2,z3,z1452,z5,z6]),(0,[z95,z7,z103,z4,z102,z6]),(0,[z7,z230,z3,z24,z5,z6]),(0,[z7,z2,z426,z22,z5,z6])],[(0,[z7,z2,z3,z1453,z5,z6]),(0,[z7,z2,z3,z4,z5,z1454]),(0,[z7,z2,z3,z513,z174,z6])],[(0,[z33,z2,z3,z4,z37,z34]),(0,[z95,z286,z103,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1455]),(0,[z7,z2,z3,z1456,z5,z6]),(0,[z7,z827,z3,z4,z5,z6]),(0,[z7,z418,z62,z4,z5,z6])],[(0,[z7,z2,z3,z22,z435,z6]),(0,[z178,z2,z3,z4,z68,z6]),(0,[z7,z2,z4,z5,z868,z25]),(0,[z7,z2,z3,z1457,z5,z6])],[(0,[z7,z2,z3,z1458,z5,z6]),(0,[z7,z1459,z2,z3,z5,z6]),(0,[z759,z2,z3,z22,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 489).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 968).take 486) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1454).take 53) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1507)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [489, 479, 486, 53] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 87).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 87).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 187).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 290).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 396).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 500).take 12).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [87, 100, 103, 106, 104, 12] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_39589

theorem PEqualNP.Outside.L_meta_39589 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4278124168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4278124168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39589.solve