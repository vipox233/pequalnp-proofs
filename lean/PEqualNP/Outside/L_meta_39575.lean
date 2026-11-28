import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39575

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
  Nat.testBit (4294901482 * 2 ^ 32 + 4278124232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0812000048830620#64 ++ 0x0040900002441831#64 ++ 0xeed50084f9870e76#64 ++ 0xef76a80427cc3873#64 : BitVec 256),
   (0x11040109200810c8#64 ++ 0x8888200849004086#64 ++ 0xddb3031b221833ff#64 ++ 0xdeed9818d910c19f#64 : BitVec 256),
   (0x22180422c0a14301#64 ++ 0x1110c02116050a18#64 ++ 0xbb8f8c63c4e1c38d#64 ++ 0xbddc7c631e270e1c#64 : BitVec 256),
   (0xc02030540700a810#64 ++ 0x26010182a0380540#64 ++ 0x787ff07c0701fc1c#64 ++ 0x7bc3ff83e0380fe0#64 : BitVec 256),
   (0x84405a8007540002#64 ++ 0x042202d4003aa000#64 ++ 0x07ff7f8007fe0003#64 ++ 0xf83ffbfc003ff000#64 : BitVec 256),
   (0x07806fffb000001c#64 ++ 0x383c037ffd800000#64 ++ 0xffff7ffff8000000#64 ++ 0x07fffbffffc00000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000000 0x07fffbffffc00000

def z1 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9870e76 0xef76a80427cc3873

def z2 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b221833ff 0xdeed9818d910c19f

def z3 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x220c8c60c4e1c38d 0xb910646306270e1c

def z4 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e1c38d 0xbddc7c631e270e1c

def z5 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007fe0003 0xf83ffbfc003ff000

def z6 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0701fc1c 0x7bc3ff83e0380fe0

def z7 : W := mkw 0x0f924fabf883062c 0x187c927d5fc41831 0xefd50f87f9870e76 0xef7ea87c3fcc3873

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x4050000401000c10 0x4202800020080060

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0x06d5008001860002 0xe836a804000c3000

def z10 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb90a8c63c461c38d 0x15c854631e230e1c

def z11 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x5fff7f9807fe301f 0xfafffbfcc03ff180

def z12 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfbf0f1b26f833ff 0xfefdf878d937c19f

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed50084f8000000 0x0776a80427c00000

def z14 : W := mkw 0x0802000008020420 0x0040100000401021 0x4450008439060c72 0x4222800421c83063

def z15 : W := mkw 0x0000205400000010 0x20000102a0000000 0x787f707c00000000 0x03c3fb83e0000000

def z16 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1833ff 0xdffffbffffd0c19f

def z17 : W := mkw 0x04004a8000000000 0x0020025400000000 0x07ff7f8000000000 0x003ffbfc00000000

def z18 : W := mkw 0x87c07fffb754001e 0x3c3e03fffdbaa000 0xffff7ffffffe0003 0xfffffbfffffff000

def z19 : W := mkw 0x402020540000a810 0x22010102a0000540 0x787ff07c0001fc1c 0x03c3ff83e0000fe0

def z20 : W := mkw 0x8040100007540002 0x04020080003aa000 0x0000000007fe0003 0xf8000000003ff000

def z21 : W := mkw 0x2208042280204101 0x1110402114010208 0x110a8c630460c189 0x108854631823060c

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x05b3030002180003 0xd82d98180010c000

def z23 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff80033fc 0x07fffbffffc0019f

def z24 : W := mkw 0x0000000000000000 0x0000000000000000 0x038f0c0004e00001 0xb81c786000270000

def z25 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x224c7ce4d8000000 0x011263e726c00000

def z26 : W := mkw 0x402020540000a810 0x22010102a0000540 0x7800807c0001fc1c 0x03c00403e0000fe0

def z27 : W := mkw 0xc7a07fffb700a81c 0x3e3d03fffdb80540 0xffffffffff01fc1c 0x7ffffffffff80fe0

def z28 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0xfefff0fcff87fe7e 0xfff7ff87e7fc3ff3

def z29 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xffdf8ce7fde7cfff 0xfffefc673fef3e7f

def z30 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x204cf0640501cc00 0x2102678320280e60

def z31 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x7ffffffc07fffc1f 0xfbffffffe03fffe0

def z32 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbf8f8ce3fce7c3ef 0xbdfc7c671fe73e1f

def z33 : W := mkw 0x0812000048830620 0x0040900002441831 0x86800080f8860262 0x8434000407c43013

def z34 : W := mkw 0x2208042280204101 0x1110402114010208 0x390f8c630461c18d 0x39c87c6318230e0c

def z35 : W := mkw 0x11040109200810c8 0x8888200849004086 0x4430031822183072 0x42218018c110c183

def z36 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xffbf8f7be6f9f3ff 0xfffdfc7bdf37cf9f

def z37 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd800001b200033fc 0x06c00000d900019f

def z38 : W := mkw 0x402020540000a810 0x22010102a0000540 0x7833807c0201fc1c 0x5bc19c03e0100fe0

def z39 : W := mkw 0x0802000008020420 0x0040100000401021 0x46d5008439860c72 0xea36a80421cc3063

def z40 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x04707380031e0002 0x4023839c0018f000

def z41 : W := mkw 0x27986ffff0a1431d 0x393cc37fff850a18 0xffff7ffff8e00381 0x87fffbffffc7001c

def z42 : W := mkw 0x0812000048830620 0x0040900002441831 0x0000000000010e74 0x0000000000000873

def z43 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xfff7039ffb9f3fff 0xffffb81cffdcf9ff

def z44 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0xefd50f87f8000000 0x077ea87c3fc00000

def z45 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x9fff7f8307fe038f 0xfcfffbfc183ff01c

def z46 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa180003 0xdffffbffffd0c000

def z47 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07800f8000fe0003 0x803c007c0007f000

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0x380f80600401c00c 0x39c07c0300200e00

def z49 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdbf837b2619f3ff 0xffedfc1bd930cf9f

def z50 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb808c63c0e1c38d 0x85dc04631e070e1c

def z51 : W := mkw 0x8000100007000000 0x0400008000380000 0x007f700007000000 0x7803fb8000380000

def z52 : W := mkw 0x0100010920000008 0x0808000849000000 0x1122031b00000000 0x00891018d8000000

def z53 : W := mkw 0x0000205400000010 0x20000102a0000000 0x204c706400000000 0x0102638320000000

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x0680008000860002 0x8034000400043000

def z55 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x012a7f0006780001 0x100953f80033c000

def z56 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x102af0780600f008 0x10815783c0300780

def z57 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x97aa7ffbf8000000 0x04bd53ffdfc00000

def z58 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffce00001 0xbffffbffffe70000

def z59 : W := mkw 0x0812000048830620 0x0040900002441831 0xefdf0c84fde70e77 0xff7ef86427ef3873

def z60 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0xf87ff07fc701ff9c 0x7fc3ff83fe380ffc

def z61 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfff7039ffa1833ff 0xdfffb81cffd0c19f

def z62 : W := mkw 0x04004a8000000000 0x0020025400000000 0x07ff7f8001860002 0xe83ffbfc000c3000

def z63 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8005e60000 0x203ffbfc002f3000

def z64 : W := mkw 0x0812000048830620 0x0040900002441831 0x22440084d9870c00 0x2112200426cc3860

def z65 : W := mkw 0x0802000008020420 0x0040100000401021 0x0400008038060062 0x0020000401c03003

def z66 : W := mkw 0x86c07ef697540016 0x343603f7b4baa000 0x27ff7fe4dffe0003 0xf93ffbff26fff000

def z67 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0x87800f83f8000000 0x043c007c1fc00000

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x07f70380039e0003 0xf83fb81c001cf000

def z69 : W := mkw 0x0000000000000000 0x0000000000000000 0xdd930003200003ff 0xdeec98001900001f

def z70 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x024c7c8005e60000 0x201263e4002f3000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x5db303180218301f 0xdaed9818c010c180

def z72 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x112a7f7b00000000 0x008953fbd8000000

def z73 : W := mkw 0x0f926ffff883063c 0x387c937fffc41831 0xffff7ffff9870e76 0xeffffbffffcc3873

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc91000020000276 0xce64880001000013

def z75 : W := mkw 0x0812000048830620 0x0040900002441831 0x20000004d8010c00 0x0100000026c00860

def z76 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0xefff7f84ffff0e77 0xff7ffbfc27fff873

def z77 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x6875701c03013c14 0x6b43ab80e01809e0

def z78 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x067c7f8007fe0002 0x6033e3fc003ff000

def z79 : W := mkw 0x0200042280000000 0x1010002114000000 0xb8000063c0000000 0x05c000031e000000

def z80 : W := mkw 0x87c05fabb754000e 0x1c3e02fd5dbaa000 0x87ff7f83fffe0003 0xfc3ffbfc1ffff000

def z81 : W := mkw 0x885210004fd70622 0x04429080027eb831 0x0000000007ff0e77 0xf8000000003ff873

def z82 : W := mkw 0x11040109200810c8 0x8888200849004086 0x85800303201803e3 0x842c00181900c01f

def z83 : W := mkw 0x2008000000204101 0x0100400000010208 0x000080000460c189 0x100004000023060c

def z84 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0600f008 0x13c3ff83e0300780

def z85 : W := mkw 0x0000000000000000 0x0000000000000000 0x038f0c0000000000 0x001c786000000000

def z86 : W := mkw 0xc02010000700a800 0x0601008000380540 0x000080000701fc1c 0x7800040000380fe0

def z87 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdf7031f23193fff 0xffefb818f918c9ff

def z88 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff800038d 0x9ffffbffffc0001c

def z89 : W := mkw 0x11040109200810c8 0x8888200849004086 0x0400030020180062 0x002000180100c003

def z90 : W := mkw 0x0812000048830620 0x0040900002441831 0x86800080f9870e76 0xec34000407cc3873

def z91 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0x87ff7f80fffe0263 0xfc3ffbfc07fff013

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x998300030000038d 0x9ccc18001800001c

def z93 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0x87ff7f83f8000000 0x043ffbfc1fc00000

def z94 : W := mkw 0x11040109200810c8 0x8888200849004086 0x85b30303221803e3 0xdc2d98181910c01f

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0x4450008438000000 0x0222800421c00000

def z96 : W := mkw 0x0e926ef6d8830634 0x30749377b6c41831 0x224c7ce4d9870c00 0x211263e726cc3860

def z97 : W := mkw 0x0200042280000000 0x1010002114000000 0xbb8f0c63c0000000 0x05dc78631e000000

def z98 : W := mkw 0xa7d87ffff7f5431f 0x3d3ec3ffffbfaa18 0xffffffffffffc38f 0xfffffffffffffe1c

def z99 : W := mkw 0xc02010000700a800 0x0601008000380540 0x380f80600701fc1c 0x79c07c0300380fe0

def z100 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0x4470739c38000000 0x0223839ce1c00000

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x6855000401010c14 0x6b42a80020080860

def z102 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x938a8c63c4e0c389 0x949c54631e27061c

def z103 : W := mkw 0x0812000048830620 0x0040900002441831 0x0000000001870e76 0xe8000000000c3873

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x583300180200301c 0x5ac19800c0100180

def z105 : W := mkw 0x10040000000810c0 0x8080200000004086 0x00000000021833ff 0xd80000000010c19f

def z106 : W := mkw 0x0380052bb000000c 0x181c00295d800000 0x80000003f8000000 0x040000001fc00000

def z107 : W := mkw 0x0f926ffff883063c 0x387c937fffc41831 0xffff7ffff9870c00 0x27fffbffffcc3860

def z108 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb8008063c001c38c 0x05c004031e000e1c

def z109 : W := mkw 0x0812000048830620 0x0040900002441831 0xffd70087f9870fff 0xfffeb8043fcc387f

def z110 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xeef5039cfb9f3e76 0xef77a81ce7dcf9f3

def z111 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xddf3739f38000000 0x06ef9b9cf9c00000

def z112 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xefff7f84fffe0003 0xff7ffbfc27fff000

def z113 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x012a7f0007fe0003 0xf80953f8003ff000

def z114 : W := mkw 0x0200042280000000 0x1010002114000000 0x220c0c60c0000000 0x0110606306000000

def z115 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x07ffff8007fffc1f 0xf83ffffc003fffe0

def z116 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07ff7f8000fe0003 0x803ffbfc0007f000

def z117 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x306ef07c0701fc08 0x31837783e0380fe0

def z118 : W := mkw 0x0000000000000000 0x0000000000000000 0x0285000000800000 0xa814280000040000

def z119 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x0000800004e1c38d 0xb800040000270e1c

def z120 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xbbcf7ce7d8000000 0x05de7be73ec00000

def z121 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa00301c 0x5ffffbffffd00180

def z122 : W := mkw 0x8c425a800f560422 0x046212d4007ab021 0x447073843b1e0c72 0x4223839c21d8f063

def z123 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0xeed58084ff87fe7e 0xff76ac0427fc3ff3

def z124 : W := mkw 0x0010000040810200 0x0000800002040810 0xaa850000c0810204 0xad54280006040810

def z125 : W := mkw 0x27986ffff0a1431d 0x393cc37fff850a18 0xfffffffffce1c38d 0xbfffffffffe70e1c

def z126 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0x000080000787fe7e 0xf8000400003c3ff3

def z127 : W := mkw 0x15444b89205c10ca 0x88aa225c4902e086 0x87800f8320fe03e3 0x843c007c1907f01f

def z128 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xff800ffff8000000 0x07fc007fffc00000

def z129 : W := mkw 0x0000000000000000 0x0000000000000000 0x3b8f8c6004e1c00d 0xb9dc7c6300270e00

def z130 : W := mkw 0x04004a8000000000 0x0020025400000000 0x07ff7f8002180003 0xd83ffbfc0010c000

def z131 : W := mkw 0x0200042280000000 0x1010002114000000 0xbb8f0c63c4e00001 0xbddc78631e270000

def z132 : W := mkw 0x11040109200810c8 0x8888200849004086 0x1122031b02183189 0x10891018d810c18c

def z133 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0xfdfff37f2719ffff 0xffefff9bf938cfff

def z134 : W := mkw 0x0c524a8048d70622 0x006292540246b831 0xefd50f84f9ff0e77 0xef7ea87c27cff873

def z135 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x0000000000e00381 0x800000000007001c

def z136 : W := mkw 0x26584ea2c0f54303 0x1132c2751607aa18 0x87800f83c0fe0383 0x843c007c1e07f01c

def z137 : W := mkw 0x0100010920000008 0x0808000849000000 0xddb3031b20000000 0x06ed9818d9000000

def z138 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x036e7f8007fe0001 0x301b73fc003ff000

def z139 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0xdfff7f9b27fe33ff 0xfefffbfcd93ff19f

def z140 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfbbf8c7bc6e1f39d 0xffddfc63de370f9c

def z141 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdc30031b221833fe 0x46e18018d910c19f

def z142 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0xfbfffc7fc7e1ff9d 0xffdfffe3fe3f0ffc

def z143 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xf87f707ff8000000 0x07c3fb83ffc00000

def z144 : W := mkw 0xc02010000700a800 0x0601008000380540 0x000080000501cc00 0x2000040000280e60

def z145 : W := mkw 0x15846bdd300810dc 0xa8ac235ee9804086 0xddf3739f3a1833ff 0xdeef9b9cf9d0c19f

def z146 : W := mkw 0x10040000000810c0 0x8080200000004086 0x58330018021833ff 0xdac19800c010c19f

def z147 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x330e8c63c4e1c189 0x319874631e270e0c

def z148 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfcfff07c2701fe7e 0xffe7ff83e1380ff3

def z149 : W := mkw 0x11140109608912c8 0x8888a0084b044896 0xffb7031be29933ff 0xfffdb818df14c99f

def z150 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdc91001b200033fe 0xcee48800d900019f

def z151 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xba0c8c63c4e1c38c 0x25d064631e270e1c

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed50084f8000276 0xcf76a80427c00013

def z153 : W := mkw 0x11040109200810c8 0x8888200849004086 0xc5b0031b221833f3 0xc62d8018d910c19f

def z154 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07f07f8003fe0003 0xc03f83fc001ff000

def z155 : W := mkw 0xc7e07fffb754a81e 0x3e3f03fffdbaa540 0xfffffffffffffc1f 0xffffffffffffffe0

def z156 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x220c8c60c4e1c000 0x2110646306270e00

def z157 : W := mkw 0xc02010000700a800 0x0601008000380540 0x0000000003003c10 0x40000000001801e0

def z158 : W := mkw 0x0200042280000000 0x1010002114000000 0x110a0c6300000000 0x0088506318000000

def z159 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xfffffffffc60c189 0x17ffffffffe3060c

def z160 : W := mkw 0x0812000048830620 0x0040900002441831 0x66540084f9870c72 0x6332a00427cc3863

def z161 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0xbfffffe3c7ffc38f 0xfdffffff1e3ffe1c

def z162 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff81803e3 0x87fffbffffc0c01f

def z163 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xcfff7f8027fe0277 0xfe7ffbfc013ff013

def z164 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0x797ff37f0719fd9d 0x7bcbff9bf838cfec

def z165 : W := mkw 0x0812000048830620 0x0040900002441831 0xe8000004f8010e74 0x0740000027c00873

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x07bf0f0006f80003 0xf83df8780037c000

def z167 : W := mkw 0x90441000075c10c2 0x84822080003ae086 0x0000000007fe33ff 0xf8000000003ff19f

def z168 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0x787ff07c0787fe7e 0xfbc3ff83e03c3ff3

def z169 : W := mkw 0x04806ad410000014 0x20240356a0800000 0x0040708418000000 0x0002038420c00000

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x785f80640501cc1c 0x7bc2fc0320280e60

def z171 : W := mkw 0x2208042280204101 0x1110402114010208 0x00088c600460c000 0x0000446300230600

def z172 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfbdf8c67c5e1cf9d 0xffdefc633e2f0e7c

def z173 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x6fff7f8407ff0c17 0xfb7ffbfc203ff860

def z174 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07aa7f8006fe0003 0x903d53fc0037f000

def z175 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xfffffffff801fc1c 0x07ffffffffc00fe0

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001860002 0xe8000000000c3000

def z177 : W := mkw 0x0812000048830620 0x0040900002441831 0x22440084d9870e76 0xe912200426cc3873

def z178 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x83800c03c0e00381 0x841c00601e07001c

def z179 : W := mkw 0xc02010000700a800 0x0601008000380540 0x007ff0000701fc1c 0x7803ff8000380fe0

def z180 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfc7073fff8000000 0x07e3839fffc00000

def z181 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xf800007ff8000000 0x07c00003ffc00000

def z182 : W := mkw 0x04404a8000540002 0x002202540002a000 0x01000f0000780001 0x000800780003c000

def z183 : W := mkw 0x2f9a6ffff8a3473d 0x397cd37fffc51a39 0xfffffffffde7cfff 0xffffffffffef3e7f

def z184 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0x0000800005e7cfff 0xf8000400002f3e7f

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x010a0c0004600001 0x1008506000230000

def z186 : W := mkw 0x0000205400000010 0x20000102a0000000 0xfeff70fcf8000000 0x07f7fb87e7c00000

def z187 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0x01000f0300000000 0x0008007818000000

def z188 : W := mkw 0x04004a8000000000 0x0020025400000000 0x0470738000000000 0x0023839c00000000

def z189 : W := mkw 0x0812000048830620 0x0040900002441831 0xeff70384fb9f0e77 0xff7fb81c27dcf873

def z190 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x3fffffe007ffc00f 0xf9ffffff003ffe00

def z191 : W := mkw 0x1384257fb00810dc 0xb89c212bfd804086 0xf800007ff80033fc 0x07c00003ffc0019f

def z192 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f80031e0002 0x403ffbfc0018f000

def z193 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd922031b221833fd 0x16c91018d910c19f

def z194 : W := mkw 0x0f926ffff883063c 0x387c937fffc41831 0xffff7ffff8010e74 0x07fffbffffc00873

def z195 : W := mkw 0x330c052ba02851c9 0x999860295d01428e 0x112a8f7b0678f189 0x1089547bd833c78c

def z196 : W := mkw 0x87c07fffb754001e 0x3c3e03fffdbaa000 0xffff7ffffde60000 0x27fffbffffef3000

def z197 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd983001b200033fd 0x9ecc1800d900019f

def z198 : W := mkw 0xc7a07fffb700a81c 0x3e3d03fffdb80540 0x797fff7f0701fc1c 0x7bcbfffbf8380fe0

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000276 0xc800000000000013

def z200 : W := mkw 0x17844fabb00810cc 0x98bc227d5d804086 0x87800f83f81803e3 0x843c007c1fc0c01f

def z201 : W := mkw 0x06804ea290000004 0x1034027514800000 0x02000c80d8000000 0x0010006406c00000

def z202 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000276 0xcffffbffffc00013

def z203 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xddbb7f7b20000000 0x06eddbfbd9000000

def z204 : W := mkw 0x11040109200810c8 0x8888200849004086 0x99a3031b0218338d 0x9ccd1818d810c19c

def z205 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7bfffc7c07e1fc1d 0xfbdfffe3e03f0fe0

def z206 : W := mkw 0x0010000040810200 0x0000800002040810 0xa8000000c0010204 0x0540000006000810

def z207 : W := mkw 0x2208042280204101 0x1110402114010208 0x100080630000c188 0x008004031800060c

def z208 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x4070701c03003c10 0x42038380e01801e0

def z209 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xfdb3837be219f3ff 0xdfed9c1bdf10cf9f

def z210 : W := mkw 0x3b1e052be8ab57e9 0x99d8f0295f455abf 0xffff8fffffffffff 0xfffffc7fffffffff

def z211 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x9b830c03c0e0038d 0x9cdc18601e07001c

def z212 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffc01c00c 0x3fffffffffe00e00

def z213 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x9983800304e1c38d 0xbccc1c0018270e1c

def z214 : W := mkw 0x86405ea287540002 0x143202f5143aa000 0xbfff7fe3c7fe0003 0xfdfffbff1e3ff000

def z215 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x583bf0780600f01c 0x5ac1df83c0300780

def z216 : W := mkw 0x2318052be0a14309 0x1918c0295f050a18 0xffbf8f7be4e1c38d 0xbffdfc7bdf270e1c

def z217 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xeef5739cf8000000 0x0777ab9ce7c00000

def z218 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfa4c7cfff8000000 0x07d263e7ffc00000

def z219 : W := mkw 0x02100422c0810200 0x1010802116040810 0xbb8f0c63c0810204 0xaddc78631e040810

def z220 : W := mkw 0x04004a8000000000 0x0020025400000000 0x07ff7f8004e00001 0xb83ffbfc00270000

def z221 : W := mkw 0x0812000048830620 0x0040900002441831 0xaa850000c1870e76 0xed542800060c3873

def z222 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x83808c03c4e1c38d 0xbc1c04601e270e1c

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0x2044000401010c00 0x2102200020080860

def z224 : W := mkw 0x11040109200810c8 0x8888200849004086 0x0020031802183000 0x00010018c010c180

def z225 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0xeef57384fb9f0e76 0xef77ab9c27dcf873

def z226 : W := mkw 0x0e926ef6d8830634 0x30749377b6c41831 0xeedd7ce4f9870e76 0xef76ebe727cc3873

def z227 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xa7cc7fe7f8000000 0x053e63ff3fc00000

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0xb98f80630401c38d 0xbdcc7c0318200e1c

def z229 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x102af0780701fc1c 0x78815783c0380fe0

def z230 : W := mkw 0x8fd27fffffd7063e 0x3c7e93fffffeb831 0xffff7fffffff0e77 0xfffffbfffffff873

def z231 : W := mkw 0x0912010968830628 0x084890084b441831 0xfff7039ff9870e76 0xefffb81cffcc3873

def z232 : W := mkw 0xc03030544781aa10 0x26018182a23c0d50 0xfafff07cc781fe1c 0xffd7ff83e63c0ff0

def z233 : W := mkw 0x0100010920000008 0x0808000849000000 0x4430031820000000 0x02218018c1000000

def z234 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x204cf0640701fc1c 0x7902678320380fe0

def z235 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xeedd8ce4fde7ce76 0xef76ec6727ef3e73

def z236 : W := mkw 0x5124215d2008b8d8 0xaa89210ae90045c6 0xf800807f2001fffc 0x07c00403f9000fff

def z237 : W := mkw 0x8000100007000000 0x0400008000380000 0x0000000007000000 0x7800000000380000

def z238 : W := mkw 0x0010000040810200 0x0000800002040810 0xee950000e0810276 0xef74a80007040813

def z239 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbfbf8f63c6f9c38f 0xfdfdfc7b1e37ce1c

def z240 : W := mkw 0x62382476c0a1eb11 0x3311c123b6050f58 0xfb8f8c7fc4e1ff9d 0xbfdc7c63fe270ffc

def z241 : W := mkw 0x26184ea2c0a14301 0x1130c27516050a18 0xbfffffe3c4e1c38d 0xbdffffff1e270e1c

def z242 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa183072 0x47fffbffffd0c183

def z243 : W := mkw 0x0812000048830620 0x0040900002441831 0xe8550004f9010e74 0x6f42a80027c80873

def z244 : W := mkw 0x0000000000000000 0x0000000000000000 0x05b3030000000000 0x002d981800000000

def z245 : W := mkw 0x330c052ba02851c9 0x999860295d01428e 0xddbb8f7b2678f3ff 0xdeeddc7bd933c79f

def z246 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8c63c5e7cfff 0xfddc7c631e2f3e7f

def z247 : W := mkw 0x1104215d200810d8 0xa888210ae9004086 0xfdff737f221833ff 0xdfeffb9bf910c19f

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180000300000381 0x840c00001800001c

def z249 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9860002 0xeffffbffffcc3000

def z250 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xf92a7f7ff8000000 0x07c953fbffc00000

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000030000038c 0x04c000001800001c

def z252 : W := mkw 0x10040000000810c0 0x8080200000004086 0x0000000002183189 0x100000000010c18c

def z253 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x00087c6000000000 0x000043e300000000

def z254 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xeedd7ce4f8000000 0x0776ebe727c00000

def z255 : W := mkw 0x402020540000a810 0x22010102a0000540 0x7855807c0101fc1c 0x6bc2ac03e0080fe0

def z256 : W := mkw 0x04404a8000540002 0x002202540002a000 0x02000c8000e60000 0x0010006400073000

def z257 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffff8fe0003 0x87fffbffffc7f000

def z258 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b22183189 0x16ed9818d910c18c

def z259 : W := mkw 0x0100010920000008 0x0808000849000000 0xddb3031b2000038d 0x9eed9818d900001c

def z260 : W := mkw 0x26986ef6d0a14315 0x3134c377b6850a18 0x224cfce4dce1c000 0x211267e726e70e00

def z261 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x06f57380039e0002 0xe837ab9c001cf000

def z262 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0xeedd7c84fde70e76 0xef76ebe427ef3873

def z263 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfefff0fcff01fc1c 0x7ff7ff87e7f80fe0

def z264 : W := mkw 0x11040109200810c8 0x8888200849004086 0x95a2031b221833eb 0x94ad1018d910c19f

def z265 : W := mkw 0x0812000048830620 0x0040900002441831 0xfef7009cfb873e7e 0xfff7b804e7dc39f3

def z266 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xff9f8c63e4e1c3ff 0xfffcfc631f270e1f

def z267 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x03af7f0006f80001 0xb81d7bf80037c000

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0x100a80600400c008 0x1080540300200600

def z269 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x110a8c6304e1c38d 0xb888546318270e1c

def z270 : W := mkw 0x0802000008020420 0x0040100000401021 0x0000000001060c72 0x4000000000083063

def z271 : W := mkw 0x27986ffff0a1431d 0x393cc37fff850a18 0xbbafff7bc4e1c38d 0xbddd7ffbde270e1c

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x1102000300000189 0x108810001800000c

def z273 : W := mkw 0x27986ffff0a1431d 0x393cc37fff850a18 0xfffffffff801c38c 0x07ffffffffc00e1c

def z274 : W := mkw 0x17844fabb00810cc 0x98bc227d5d804086 0xdfb30f9bfa1833ff 0xdefd987cdfd0c19f

def z275 : W := mkw 0x379c6ffff0a953dd 0xb9bce37fff854a9e 0xfffffffffef9f3ff 0xfffffffffff7cf9f

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x4410000020000072 0x4220800001000003

def z277 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0xddbb7f1b267833ff 0xdeeddbf8d933c19f

def z278 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0xbbaffc7bc6e1f38d 0xbddd7fe3de370f9c

def z279 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9010c14 0x6ffffbffffc80860

def z280 : W := mkw 0x1f966ffff88b16fc 0xb8fcb37fffc458b7 0xffff7ffffb9f3fff 0xfffffbffffdcf9ff

def z281 : W := mkw 0x311c010960a953c9 0x8988e0084b054a9e 0xddb3831b26f9f3ff 0xfeed9c18d937cf9f

def z282 : W := mkw 0x0000000000000000 0x0000000000000000 0xcdb3030022180277 0xde6d98180110c013

def z283 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07d50f8001fe0003 0xe83ea87c000ff000

def z284 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x7a7f7cfcd8000000 0x03d3fbe7e6c00000

def z285 : W := mkw 0x0812000048830620 0x0040900002441831 0xc6d00084f9860e72 0xc636800427cc3073

def z286 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xddb3031b239f3fff 0xfeed9818d91cf9ff

def z287 : W := mkw 0x87c07fffb754001e 0x3c3e03fffdbaa000 0x17ff7ffb07fe0003 0xf8bffbffd83ff000

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x000080000401c00c 0x3800040000200e00

def z289 : W := mkw 0x0812000048830620 0x0040900002441831 0xe8000004f9870e76 0xef40000027cc3873

def z290 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xbbaf8f7bc6f9f38d 0xbddd7c7bde37cf9c

def z291 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xf9fff07f0701ff9d 0xffcfff83f8380ffc

def z292 : W := mkw 0x04004a8000000000 0x0020025400000000 0x024c7c8000000000 0x001263e400000000

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0x7877001c03013c1c 0x7bc3b800e01809e0

def z294 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x0020730002180000 0x000103980010c000

def z295 : W := mkw 0x11040109200810c8 0x8888200849004086 0x4000001820003070 0x02000000c1000183

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x4030001802003010 0x42018000c0100180

def z297 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x336e7fffd8000000 0x019b73fffec00000

def z298 : W := mkw 0x885210004fd70622 0x04429080027eb831 0xeed50084ffff0e77 0xff76a80427fff873

def z299 : W := mkw 0x8c425a800f560422 0x046212d4007ab021 0x47ff7f843ffe0c73 0xfa3ffbfc21fff063

def z300 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x47ff7f9c07fe3c13 0xfa3ffbfce03ff1e0

def z301 : W := mkw 0x2208042280204101 0x1110402114010208 0x01000c0300600181 0x000800601803000c

def z302 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfb8f8c67fce1cffd 0xbfdc7c633fe70e7f

def z303 : W := mkw 0x04404a8000540002 0x002202540002a000 0x04000380001e0002 0x0020001c0000f000

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x06d5008000000000 0x0036a80400000000

def z305 : W := mkw 0xe6787ef6c7f5eb13 0x3733c3f7b63faf58 0xffffffffc7ffff9f 0xfffffffffe3ffffc

def z306 : W := mkw 0x0010000040810200 0x0000800002040810 0xba8f8060c481c20c 0xbdd47c0306240e10

def z307 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0xbbcffce3c5e7c38d 0xbdde7fe71e2f3e1c

def z308 : W := mkw 0x0010000040810200 0x0000800002040810 0xaed50080c1870206 0xed76a804060c3810

def z309 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0x1000007b00000000 0x00800003d8000000

def z310 : W := mkw 0xc82230540f02ac30 0x26411182a0781561 0x7c7ff0fc3f07fc7e 0x7be3ff87e1f83fe3

def z311 : W := mkw 0x402020540000a810 0x22010102a0000540 0x4000001c00003c10 0x02000000e00001e0

def z312 : W := mkw 0x0812000048830620 0x0040900002441831 0xee800084f8870e76 0x8774000427c43873

def z313 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x224cfce405e7cc00 0x211267e7202f3e60

def z314 : W := mkw 0x26584ea2c0f54303 0x1132c2751607aa18 0xbf8f8fe3c4ffc38f 0xbdfc7c7f1e27fe1c

def z315 : W := mkw 0x0000205400000010 0x20000102a0000000 0x787ff07c0401c00c 0x3bc3ff83e0200e00

def z316 : W := mkw 0x85c07bdd3754001e 0x2c2e03dee9baa000 0x4470739c3b1e0002 0x4223839ce1d8f000

def z317 : W := mkw 0x8040100007540002 0x04020080003aa000 0x007f700007fe0003 0xf803fb80003ff000

def z318 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0x87800383f89e03e3 0x843c001c1fc4f01f

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0xced5008021860276 0xee76a804010c3013

def z320 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xfb8f8c7be4e1f3fd 0xbfdc7c63df270f9f

def z321 : W := mkw 0xcfb27fffff83ae3c 0x3e7d93fffffc1d71 0xffffffffff87fe7e 0xfffffffffffc3ff3

def z322 : W := mkw 0x0100010920000008 0x0808000849000000 0xd800001b20000000 0x06c00000d9000000

def z323 : W := mkw 0x0000000000000000 0x0000000000000000 0xd9b3001b0200339d 0xdecd9800d810019c

def z324 : W := mkw 0x10040000000810c0 0x8080200000004086 0x00000000000033fc 0x000000000000019f

def z325 : W := mkw 0xa6485ea287744103 0x153242f5143ba208 0x17ffffe307fec18b 0xf8bfffff183ff60c

def z326 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x27ff7fe4d8000000 0x013ffbff26c00000

def z327 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0x224cfce0c5e7c000 0x211267e7062f3e00

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x9983000300000000 0x04cc180018000000

def z329 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b200033fc 0x06ed9818d900019f

def z330 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdff7039b239e33ff 0xfeffb81cd91cf19f

def z331 : W := mkw 0x0812000048830620 0x0040900002441831 0x06d5008001870e76 0xe836a804000c3873

def z332 : W := mkw 0x0010000040810200 0x0000800002040810 0x82800000c0800200 0x8414000006040010

def z333 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0xbbafff63c6f9c38d 0xbddd7ffb1e37ce1c

def z334 : W := mkw 0x04404a8000540002 0x002202540002a000 0x078f0f8004fe0003 0xb83c787c0027f000

def z335 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x057a7f80077e0003 0x502bd3fc003bf000

def z336 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x112aff780678f009 0x108957fbc033c780

def z337 : W := mkw 0x0000205400000010 0x20000102a0000000 0x4070701c00000000 0x02038380e0000000

def z338 : W := mkw 0x402000000000a800 0x0201000000000540 0x000080000001fc1c 0x0000040000000fe0

def z339 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x05f37380031e0003 0xd82f9b9c0018f000

def z340 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x027f7c8007e60000 0x7813fbe4003f3000

def z341 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xeed58084fde7cfff 0xff76ac0427ef3e7f

def z342 : W := mkw 0x0812000048830620 0x0040900002441831 0x26d50084d9870c02 0xe936a80426cc3860

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000001010c14 0x6800000000080860

def z344 : W := mkw 0x97c47fffb75c10de 0xbcbe23fffdbae086 0xffff7ffffffe33ff 0xfffffbfffffff19f

def z345 : W := mkw 0x04004a8000000000 0x0020025400000000 0xefff7f84f8000000 0x077ffbfc27c00000

def z346 : W := mkw 0x11040109200810c8 0x8888200849004086 0x1122031b021833ff 0xd8891018d810c19f

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x0450008001060002 0x4022800400083000

def z348 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xf800807be001f3fc 0x07c00403df000f9f

def z349 : W := mkw 0x0802000008020420 0x0040100000401021 0xccd1008439060e76 0xce66880421c83073

def z350 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb80f8063c401c38c 0x3dc07c031e200e1c

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x86800080f8000000 0x0434000407c00000

def z352 : W := mkw 0x2208042280204101 0x1110402114010208 0xbb8f8c63c460c189 0x15dc7c631e23060c

def z353 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0x4470731c23183c72 0x42238398e118c1e3

def z354 : W := mkw 0x26986ef6d0a14315 0x3134c377b6850a18 0xbbcffce7dce1c38d 0xbdde7fe73ee70e1c

def z355 : W := mkw 0x1304052ba00810c8 0x989820295d004086 0xffbf0f7be21833ff 0xdffdf87bdf10c19f

def z356 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0x87800f03e0f803e3 0x843c00781f07c01f

def z357 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07cc7f8005fe0003 0xa03e63fc002ff000

def z358 : W := mkw 0x0010000040810200 0x0000800002040810 0x0000000000810204 0xa800000000040810

def z359 : W := mkw 0x11040109200810c8 0x8888200849004086 0x85800303221833ff 0xdc2c00181910c19f

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x22440084d8000000 0x0112200426c00000

def z361 : W := mkw 0xc5a07bdd3700a81c 0x2e2d03dee9b80540 0x4470739c3b003c10 0x4223839ce1d801e0

def z362 : W := mkw 0x0812000048830620 0x0040900002441831 0x6a550084d9870c14 0x6b52a80426cc3860

def z363 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0x224cfc64c5e1cc00 0x211267e3262f0e60

def z364 : W := mkw 0x8000100007000000 0x0400008000380000 0x03ff7c0007e00001 0xf81ffbe0003f0000

def z365 : W := mkw 0xd7a47fffb708b8dc 0xbebd23fffdb845c6 0xffffffffff19ffff 0xfffffffffff8cfff

def z366 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa183189 0x17fffbffffd0c18c

def z367 : W := mkw 0x87c07fffb754001e 0x3c3e03fffdbaa000 0xffff7ffffb1e0002 0x47fffbffffd8f000

def z368 : W := mkw 0x0000205400000010 0x20000102a0000000 0x787f707c01010c14 0x6bc3fb83e0080860

def z369 : W := mkw 0x0812000048830620 0x0040900002441831 0x0000000001870c00 0x20000000000c3860

def z370 : W := mkw 0x402020540000a810 0x22010102a0000540 0x100080780000f008 0x00800403c0000780

def z371 : W := mkw 0x881210004f830620 0x04409080027c1831 0xeeff7084ff870e76 0xff77fb8427fc3873

def z372 : W := mkw 0x0100010920000008 0x0808000849000000 0xddb3031b20000276 0xceed9818d9000013

def z373 : W := mkw 0x10040000000810c0 0x8080200000004086 0x00000000001803e3 0x800000000000c01f

def z374 : W := mkw 0x2208042280204101 0x1110402114010208 0x138f8c6304e0c189 0xb89c7c631827060c

def z375 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x667c7ffcf8000000 0x0333e3ffe7c00000

def z376 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b201803e3 0x86ed9818d900c01f

def z377 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0x27ff7f84dfff0c03 0xf93ffbfc26fff860

def z378 : W := mkw 0xea3a3476cfa3ef31 0x3751d1a3b67d1f79 0xfffffcffffe7ffff 0xffffffe7ffff3fff

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x0055000001000000 0x6802a80000080000

def z380 : W := mkw 0x0802000008020420 0x0040100000401021 0xeed50084f9060c72 0x4776a80427c83063

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x8881000000000204 0x8c44080000000010

def z382 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c80600401c000 0x2100640300200e00

def z383 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x017f7f0007780001 0x780bfbf8003bc000

def z384 : W := mkw 0x8040100007540002 0x04020080003aa000 0x0000000005e60000 0x20000000002f3000

def z385 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x0470738007fe0003 0xf823839c003ff000

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x1022001802003008 0x10811000c0100180

def z387 : W := mkw 0xe22834768720e911 0x371141a3b4390748 0x797ffc7f0761fd9d 0x7bcbffe3f83b0fec

def z388 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0501cc00 0x23c3ff83e0280e60

def z389 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x382ff0780601f00c 0x39c17f83c0300f80

def z390 : W := mkw 0x0812000048830620 0x0040900002441831 0xfedf80e4fd87ce7e 0xfff6fc0727ec3e73

def z391 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x0000800004e1c000 0x2000040000270e00

def z392 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x797f7f7f00000000 0x03cbfbfbf8000000

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002180003 0xd80000000010c000

def z394 : W := mkw 0x0812000048830620 0x0040900002441831 0x4450008439870e76 0xea22800421cc3873

def z395 : W := mkw 0x402020540000a810 0x22010102a0000540 0x200080640001cc00 0x0100040320000e60

def z396 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xefd50387f99f0ff7 0xef7ea81c3fccf87f

def z397 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787f707c03003c10 0x43c3fb83e01801e0

def z398 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x27ffffe407ffcc03 0xf93fffff203ffe60

def z399 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0xddf3739b231e33ff 0xdeef9b9cd918f19f

def z400 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0x224c8ce4dde7cc00 0x2112646726ef3e60

def z401 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f8860262 0x8776a80427c43013

def z402 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x0008f0600400c000 0x0000478300200600

def z403 : W := mkw 0x2208042280204101 0x1110402114010208 0x998b8c630460c38d 0x9ccc5c631823061c

def z404 : W := mkw 0xe038100047a1eb01 0x0701c080023d0f58 0x0000800007e1ff9d 0xf8000400003f0ffc

def z405 : W := mkw 0x04004a8000000000 0x0020025400000000 0x07800f8000000000 0x003c007c00000000

def z406 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xfdb3031ffa193fff 0xdfed9818ffd0c9ff

def z407 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0xbf8f0fe3f8000000 0x05fc787f1fc00000

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x0033000002000000 0x5801980000100000

def z409 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0x44707398231e3072 0x4223839cc118f183

def z410 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0x07ff7f8007ff0e77 0xf83ffbfc003ff873

def z411 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbfdf8ce3c5e7c38f 0xfdfefc671e2f3e1c

def z412 : W := mkw 0x0010000040810200 0x0000800002040810 0xab8f0c00c4e10205 0xbd5c786006270810

def z413 : W := mkw 0x0812000048830620 0x0040900002441831 0xaac50084d9870e04 0xad56280426cc3870

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x007f700000000000 0x0003fb8000000000

def z415 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x7c7ff3fc071ffc1e 0x7be3ff9fe038ffe0

def z416 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x047f7380071e0002 0x7823fb9c0038f000

def z417 : W := mkw 0x07c04fabb054000e 0x183e027d5d82a000 0x87800f83f8fe0003 0x843c007c1fc7f000

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f000004000000 0x3800780000200000

def z419 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0x112a7f7b02183189 0x108953fbd810c18c

def z420 : W := mkw 0x0812000048830620 0x0040900002441831 0xa6c40084f9870e62 0xa536200427cc3873

def z421 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x0020701802003000 0x00010380c0100180

def z422 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x17fffff807fef00b 0xf8bfffffc03ff780

def z423 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7870f07c0301fc1c 0x43c38783e0180fe0

def z424 : W := mkw 0x19060109280a14e8 0x88c83008494050a7 0x4470039c3b1e3c72 0x4223801ce1d8f1e3

def z425 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x05bb7f0006780003 0xd82ddbf80033c000

def z426 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0x7a7ff0fcdf87fc1c 0x7bd3ff87e6fc3fe0

def z427 : W := mkw 0x301c000040a953c1 0x8180e00002054a9e 0x0000800006f9f3ff 0xf80004000037cf9f

def z428 : W := mkw 0xe038305447a1eb11 0x2701c182a23d0f58 0x787ff07c07e1ff9d 0xfbc3ff83e03f0ffc

def z429 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x038f8c0004e1c38d 0xb81c7c6000270e1c

def z430 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xbbaf7f7bc0000000 0x05dd7bfbde000000

def z431 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x5873701c03003c1c 0x5ac39b80e01801e0

def z432 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x784cf07c0501fc1c 0x23c26783e0280fe0

def z433 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8ce7fce1c38d 0xbffefc673fe70e1c

def z434 : W := mkw 0x0812000048830620 0x0040900002441831 0xcc91000021870e76 0xee648800010c3873

def z435 : W := mkw 0x8040100007540002 0x04020080003aa000 0x038f0c0007fe0003 0xf81c7860003ff000

def z436 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f8010e74 0x0776a80427c00873

def z437 : W := mkw 0x9d565b896fdf16ea 0x8ceab2dc4b7ef8b7 0xffff7f9fffff3fff 0xfffffbfcfffff9ff

def z438 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0xddbbf37b2618f3ff 0xdeeddf9bd930c79f

def z439 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x03cf7c8005e60001 0xb81e7be4002f3000

def z440 : W := mkw 0xa2181422c7a14301 0x1510c0a1163d0a18 0xbbfffc63c7e1c38d 0xfddfffe31e3f0e1c

def z441 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd833001b220033fc 0x5ec19800d910019f

def z442 : W := mkw 0x0a120422c8830620 0x1050902116441831 0xffdf0ce7f9870e76 0xeffef8673fcc3873

def z443 : W := mkw 0x8000100007000000 0x0400008000380000 0x05ff730007180003 0xf82ffb980038c000

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc91000020000000 0x0664880001000000

def z445 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xf800001ff8013ffc 0x07c00000ffc009ff

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z447 : W := mkw 0x62382476c0a1eb11 0x3311c123b6050f58 0xf800807fc001ff9c 0x07c00403fe000ffc

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000200301c 0x5800000000100180

def z449 : W := mkw 0x91441109275c10ca 0x8c8a2088493ae086 0xddb3031b27fe33ff 0xfeed9818d93ff19f

def z450 : W := mkw 0x43a0257fb000a81c 0x3a1d012bfd800540 0xf800807ff801fc1c 0x07c00403ffc00fe0

def z451 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8006780001 0x103ffbfc0033c000

def z452 : W := mkw 0x0200042280000000 0x1010002114000000 0xbb8f0c63c000038d 0x9ddc78631e00001c

def z453 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x797fff7c0779fc1d 0x7bcbfffbe03bcfe0

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x783f80780601f01c 0x7bc1fc03c0300f80

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x9b8f0c0304e0038d 0xbcdc78601827001c

def z456 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xa38c8c63c4e1c381 0xa51c64631e270e1c

def z457 : W := mkw 0x11040109200810c8 0x8888200849004086 0x45b3031822183073 0xda2d9818c110c183

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x6855000400000000 0x0342a80020000000

def z459 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x782af07c0601fc1c 0x13c15783e0300fe0

def z460 : W := mkw 0x0802000008020420 0x0040100000401021 0x0040008419060c00 0x0002000420c83060

def z461 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbbcf8ce7dde7cf8d 0xbdde7c673eef3e7c

def z462 : W := mkw 0xd936315d6f8bbef8 0xaec9b18aeb7c5df7 0xfffff3ffff9fffff 0xffffff9ffffcffff

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000004e00001 0xb800000000270000

def z464 : W := mkw 0xae5a5ea2cff74723 0x1572d2f5167fba39 0xffffffe7ffffcfff 0xffffffff3ffffe7f

def z465 : W := mkw 0xc7a07fffb700a81c 0x3e3d03fffdb80540 0xfffffffffd01cc00 0x27ffffffffe80e60

def z466 : W := mkw 0x27984fabf0a1430d 0x193cc27d5f850a18 0xbf8f8fe3fce1c38d 0xbdfc7c7f1fe70e1c

def z467 : W := mkw 0x11040109200810c8 0x8888200849004086 0xccb1031822183276 0xce658818c110c193

def z468 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7dfff37c0719fc1f 0xfbefff9be038cfe0

def z469 : W := mkw 0x8000100007000000 0x0400008000380000 0x587f70180700301c 0x7ac3fb80c0380180

def z470 : W := mkw 0x402020540000a810 0x22010102a0000540 0x780f807c0401fc1c 0x3bc07c03e0200fe0

def z471 : W := mkw 0x1384257fb00810dc 0xb89c212bfd804086 0xfdb3037ffa1833ff 0xdfed981bffd0c19f

def z472 : W := mkw 0x0010000040810200 0x0000800002040810 0x22040000c0810000 0x2110200006040800

def z473 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0xeef5709cfb873e76 0xef77ab84e7dc39f3

def z474 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x0040708001060000 0x0002038400083000

def z475 : W := mkw 0xe22834768720e911 0x371141a3b4390748 0x112afc7b0660f189 0x108957e3d833078c

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x07df0c8005e60003 0xf83ef864002f3000

def z477 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfed580e7f987cffe 0xeff6ac073fcc3e7f

def z478 : W := mkw 0x10040000000810c0 0x8080200000004086 0x99830003021833ff 0xdccc18001810c19f

def z479 : W := mkw 0x10040000000810c0 0x8080200000004086 0x05b30300021833ff 0xd82d98180010c19f

def z480 : W := mkw 0x11040109200810c8 0x8888200849004086 0xcd910303201803f7 0xce6c88181900c01f

def z481 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x685df0640501cc14 0x6b42ef8320280e60

def z482 : W := mkw 0xc02010000700a800 0x0601008000380540 0x583380180701fc1c 0x7ac19c00c0380fe0

def z483 : W := mkw 0x0812000048830620 0x0040900002441831 0x6855000401870e76 0xeb42a800200c3873

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0xecd5000421010e76 0xef66a80021080873

def z485 : W := mkw 0x27984fabf0a1430d 0x193cc27d5f850a18 0x87800f83f8e00381 0x843c007c1fc7001c

def z486 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xc7f07f9ff8000000 0x063f83fcffc00000

def z487 : W := mkw 0x0010000040810200 0x0000800002040810 0xbb870003c081038d 0xbddc38001e04081c

def z488 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0x0020731800000000 0x00010398c0000000

def z489 : W := mkw 0x8000100007000000 0x0400008000380000 0x687f700407010c14 0x7b43fb8020380860

def z490 : W := mkw 0x0280247690000014 0x30140123b4800000 0x20000064d8000000 0x0100000326c00000

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x9db303030218038f 0xdced98181810c01c

def z492 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0xf87ff07f2701fffc 0x7fc3ff83f9380fff

def z493 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07b30f8002fe0003 0xd83d987c0017f000

def z494 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8000004f8000000 0x0740000027c00000

def z495 : W := mkw 0xa4585a8047f54303 0x0522c2d4023faa18 0x07ffff8007ffc38f 0xf83ffffc003ffe1c

def z496 : W := mkw 0xd12411092708b8c8 0x8e892088493845c6 0xddb3831b2719ffff 0xfeed9c18d938cfff

def z497 : W := mkw 0x2398257ff0a1431d 0x391cc12bff850a18 0xfb8f8c7ffce1c38d 0xbfdc7c63ffe70e1c

def z498 : W := mkw 0x0f926ffff883063c 0x387c937fffc41831 0xffff7ffff8860262 0x87fffbffffc43013

def z499 : W := mkw 0x0d826bdd3802043c 0x286c135ee9c01021 0x4470739c39060c72 0x4223839ce1c83063

def z500 : W := mkw 0x0812000048830620 0x0040900002441831 0x80000000f8000260 0x0400000007c00013

def z501 : W := mkw 0x0812000048830620 0x0040900002441831 0xec500084f9070e76 0x4762800427c83873

def z502 : W := mkw 0xc06010000754a802 0x06030080003aa540 0x0000800007fffc1f 0xf8000400003fffe0

def z503 : W := mkw 0x10040000000810c0 0x8080200000004086 0xcc910000221833ff 0xde6488000110c19f

def z504 : W := mkw 0x321c0422c0a953c1 0x9190e02116054a9e 0xbb8f8c63c6f9f3ff 0xfddc7c631e37cf9f

def z505 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07800f8007fe0003 0xf83c007c003ff000

def z506 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x20008060c001c000 0x0100040306000e00

def z507 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xbf8f8f63e4f9c3ef 0xbdfc7c7b1f27ce1f

def z508 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0x87ff7f8327fe03e3 0xfc3ffbfc193ff01f

def z509 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0xaa858000c4e1c38d 0xbd542c0006270e1c

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x5833001800000000 0x02c19800c0000000

def z511 : W := mkw 0x87c07fffb754001e 0x3c3e03fffdbaa000 0x112a7f7b06780001 0x108953fbd833c000

def z512 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xf8008067f801cffc 0x07c004033fc00e7f

def z513 : W := mkw 0x04004a8000000000 0x0020025400000000 0x012a7f0000000000 0x000953f800000000

def z514 : W := mkw 0xa2581422c7f54303 0x1512c0a1163faa18 0xbb8f8c63c7ffc38f 0xfddc7c631e3ffe1c

def z515 : W := mkw 0x0812205448830630 0x20409102a2441831 0xfeff70fcf9870e76 0xeff7fb87e7cc3873

def z516 : W := mkw 0x0812000048830620 0x0040900002441831 0xce910080f8860276 0xce74880407c43013

def z517 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0x87ff7f83c7fe0383 0xfc3ffbfc1e3ff01c

def z518 : W := mkw 0x0812000048830620 0x0040900002441831 0xea850004f8810e74 0xaf54280027c40873

def z519 : W := mkw 0x0b92257ff883063c 0x385c912bffc41831 0xfed500fff9870e76 0xeff6a807ffcc3873

def z520 : W := mkw 0x0100010920000008 0x0808000849000000 0xfff7039ff8000000 0x07ffb81cffc00000

def z521 : W := mkw 0x0802000008020420 0x0040100000401021 0x6c55008439070c76 0x6b62a80421c83863

def z522 : W := mkw 0x8000305407000010 0x24000182a0380000 0x787f707c07000000 0x7bc3fb83e0380000

def z523 : W := mkw 0xc6a07ef69700a814 0x363503f7b4b80540 0x224cfce4dd01cc00 0x211267e726e80e60

def z524 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x06dd7c8005e60002 0xe836ebe4002f3000

def z525 : W := mkw 0xc6a07ef69700a814 0x363503f7b4b80540 0x7a7ffcfcdf01fc1c 0x7bd3ffe7e6f80fe0

def z526 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0x7a7ffc7cc7e1fc1c 0x7bd3ffe3e63f0fe0

def z527 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x787ff07c07fffc1f 0xfbc3ff83e03fffe0

def z528 : W := mkw 0x0812000048830620 0x0040900002441831 0xea440084f9870e74 0x2752200427cc3873

def z529 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xfed5009ff9873ffe 0xeff6a804ffcc39ff

def z530 : W := mkw 0x05804b893000000c 0x082c025c49800000 0x0400038038000000 0x0020001c01c00000

def z531 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0xf87ff07cff01fe7c 0x7fc3ff83e7f80ff3

def z532 : W := mkw 0xc120315d2700a818 0x2e09018ae9380540 0xfdfff37f2701fc1c 0x7fefff9bf9380fe0

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x0244008001860000 0x20122004000c3000

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x580000180000301c 0x02c00000c0000180

def z535 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xfb8f0c7ff8000000 0x07dc7863ffc00000

def z536 : W := mkw 0x8000100007000000 0x0400008000380000 0x387ff0600701c00c 0x79c3ff8300380e00

def z537 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e1c000 0x25dc7c631e270e00

def z538 : W := mkw 0x18160000488b16e0 0x80c0b000024458b7 0x00000000039f3fff 0xf8000000001cf9ff

def z539 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0x112af37b0618f189 0x1089579bd830c78c

def z540 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0xbbcffc67c5e1cf8d 0xbdde7fe33e2f0e7c

def z541 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb8008063c4e1c38d 0xbdc004031e270e1c

def z542 : W := mkw 0x06004ea280000000 0x1030027514000000 0xbfff7fe3c0000000 0x05fffbff1e000000

def z543 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xefd50c87f9e70ff7 0xef7ea8643fcf387f

def z544 : W := mkw 0x87807fffb700001c 0x3c3c03fffdb80000 0xffff7fffff000000 0x7ffffbfffff80000

def z545 : W := mkw 0x483220544883ae30 0x22419102a2441d71 0xfed580fcf987fe7e 0xeff6ac07e7cc3ff3

def z546 : W := mkw 0x0100010920000008 0x0808000849000000 0xddb3031b22180003 0xdeed9818d910c000

def z547 : W := mkw 0x0802000008020420 0x0040100000401021 0x4000000438000c70 0x0200000021c00063

def z548 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x107ff0780700f008 0x7883ff83c0380780

def z549 : W := mkw 0xf33c357fe7a9fbd9 0xbf99e1abff3d4fde 0xffffff7fe7f9ffff 0xfffffffbff3fcfff

def z550 : W := mkw 0xd02410000708b8c0 0x86812080003845c6 0x000080000719ffff 0xf80004000038cfff

def z551 : W := mkw 0xc22034768700a810 0x361101a3b4380540 0xfbfffc7fc701fc1c 0x7fdfffe3fe380fe0

def z552 : W := mkw 0x11040109200810c8 0x8888200849004086 0x15b3031b0218318b 0xd8ad9818d810c18c

def z553 : W := mkw 0x10040000000810c0 0x8080200000004086 0x0000000002183072 0x400000000010c183

def z554 : W := mkw 0x0040000000540002 0x000200000002a000 0x0000000000fe0003 0x800000000007f000

def z555 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x00087c0004600000 0x000043e000230000

def z556 : W := mkw 0x19060109280a14e8 0x88c83008494050a7 0xddf3039f3b1e3fff 0xdeef981cf9d8f1ff

def z557 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0x7c7f73fc38000000 0x03e3fb9fe1c00000

def z558 : W := mkw 0xe7b87ffff7a1eb1d 0x3f3dc3ffffbd0f58 0xffffffffffe1ff9d 0xffffffffffff0ffc

def z559 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b22183072 0x46ed9818d910c183

def z560 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x4070f01c0701fc1c 0x7a038780e0380fe0

def z561 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c001c38c 0x05dc7c631e000e1c

def z562 : W := mkw 0x8000100007000000 0x0400008000380000 0x06ff708007860002 0xf837fb84003c3000

def z563 : W := mkw 0x8000100007000000 0x0400008000380000 0x0070700003000000 0x4003838000180000

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x4811000000000014 0x4a40880000000000

def z565 : W := mkw 0x85405b892754000a 0x0c2a02dc493aa000 0xdfff7f9b27fe0003 0xfefffbfcd93ff000

def z566 : W := mkw 0x91041109270810c8 0x8c88208849384086 0xddff731b271833ff 0xfeeffb98d938c19f

def z567 : W := mkw 0xc02010000700a800 0x0601008000380540 0x000080000600f008 0x1000040000300780

def z568 : W := mkw 0x8040100007540002 0x04020080003aa000 0x05b3030007fe0003 0xf82d9818003ff000

def z569 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x384ff0640501cc0c 0x39c27f8320280e60

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000038d 0x980000000000001c

def z571 : W := mkw 0x11040109200810c8 0x8888200849004086 0x1000001b00003188 0x00800000d800018c

def z572 : W := mkw 0xc7a07fffb700a81c 0x3e3d03fffdb80540 0xfffffffffe00f008 0x17fffffffff00780

def z573 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x80000003c0000380 0x040000001e00001c

def z574 : W := mkw 0xc7a07fffb700a81c 0x3e3d03fffdb80540 0x112aff7b0600f008 0x108957fbd8300780

def z575 : W := mkw 0xd02430540708b8d0 0xa6812182a03845c6 0x787ff07c0719ffff 0xfbc3ff83e038cfff

def z576 : W := mkw 0x0c124a8048830620 0x0060925402441831 0xefff7f84f9870e76 0xef7ffbfc27cc3873

def z577 : W := mkw 0xc4207ad40700a810 0x262103d6a0380540 0x7ffffffc0701fc1c 0x7bffffffe0380fe0

def z578 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x607cf07c0701fc10 0x6303e783e0380fe0

def z579 : W := mkw 0x11040109200810c8 0x8888200849004086 0x5c3303182218307e 0x5ae19818c110c183

def z580 : W := mkw 0x5124215d2008b8d8 0xaa89210ae90045c6 0xfdb3837f2219ffff 0xdfed9c1bf910cfff

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed50084f9860002 0xef76a80427cc3000

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800000400010c14 0x0340000020000860

def z583 : W := mkw 0x0200042280000000 0x1010002114000000 0xffdf0ce7f8000000 0x07fef8673fc00000

def z584 : W := mkw 0x483220544883ae30 0x22419102a2441d71 0xf800807cf801fe7c 0x07c00403e7c00ff3

def z585 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdd80031b201833ff 0x86ec0018d900c19f

def z586 : W := mkw 0x27986ffff0a1431d 0x393cc37fff850a18 0xfffffffffce1c000 0x27ffffffffe70e00

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x020c0c0004e00000 0x2010606000270000

def z588 : W := mkw 0x04006ad400000010 0x20200356a0000000 0x7fff7ffc00000000 0x03fffbffe0000000

def z589 : W := mkw 0x15846bdd300810dc 0xa8ac235ee9804086 0x4470739c3a183072 0x4223839ce1d0c183

def z590 : W := mkw 0x86c07ef697540016 0x343603f7b4baa000 0x224c7ce4dde60000 0x211263e726ef3000

def z591 : W := mkw 0x15444b89205c10ca 0x88aa225c4902e086 0xdfb30f9b22fe33ff 0xdefd987cd917f19f

def z592 : W := mkw 0x8000100007000000 0x0400008000380000 0x002a700006000000 0x1001538000300000

def z593 : W := mkw 0x0100010920000008 0x0808000849000000 0xddb3031b2200301c 0x5eed9818d9100180

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x0491000000000002 0xc824880000000000

def z595 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0x47ff7f9c38000000 0x023ffbfce1c00000

def z596 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x0040700401000c00 0x0002038020080060

def z597 : W := mkw 0x0b92257ff883063c 0x385c912bffc41831 0xf800007ff8010e74 0x07c00003ffc00873

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x380080600001c00c 0x01c0040300000e00

def z599 : W := mkw 0x0812000048830620 0x0040900002441831 0x02000080d8860000 0x0010000406c43000

def z600 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f0c63c0e00381 0x85dc78631e07001c

def z601 : W := mkw 0x0000205400000010 0x20000102a0000000 0x102a707800000000 0x00815383c0000000

def z602 : W := mkw 0x84005a8007000000 0x042002d400380000 0x07ff7f8007000000 0x783ffbfc00380000

def z603 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x207ff0640701cc00 0x7903ff8320380e60

def z604 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0xeeddf0e4fd87ce76 0xef76ef8727ec3e73

def z605 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x507af07c0700fc18 0x5283d783e03807e0

def z606 : W := mkw 0xa058100047f54303 0x0502c080023faa18 0x0000800007ffc38f 0xf8000400003ffe1c

def z607 : W := mkw 0x8040100007540002 0x04020080003aa000 0x00000000031e0002 0x400000000018f000

def z608 : W := mkw 0x85c07bdd3754001e 0x2c2e03dee9baa000 0x47ff7f9c3ffe0003 0xfa3ffbfce1fff000

def z609 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb9838063c001c38d 0x9dcc1c031e000e1c

def z610 : W := mkw 0x0000205400000010 0x20000102a0000000 0x787f707c0200301c 0x5bc3fb83e0100180

def z611 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xaa8d8c60c4e1c204 0xad546c6306270e10

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0xdcb300182200327e 0xdee59800c1100193

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x0430030002180002 0x402180180010c000

def z614 : W := mkw 0x11040109200810c8 0x8888200849004086 0x80000003200003e0 0x040000001900001f

def z615 : W := mkw 0xc3a0357fb700a81c 0x3e1d01abfdb80540 0xf87ff07fff01fc1c 0x7fc3ff83fff80fe0

def z616 : W := mkw 0x0200042280000000 0x1010002114000000 0xbb8f8c63c401c00c 0x3ddc7c631e200e00

def z617 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0x87800c83f8e603e3 0x843c00641fc7301f

def z618 : W := mkw 0xc02010000700a800 0x0601008000380540 0x685580040701fc1c 0x7b42ac0020380fe0

def z619 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x7a7ffcfc07e7fc1c 0x7bd3ffe7e03f3fe0

def z620 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xfdb3037ff8000000 0x07ed981bffc00000

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x0183000000000001 0x980c180000000000

def z622 : W := mkw 0x18160000488b16e0 0x80c0b000024458b7 0xeed50084fb9f3fff 0xff76a80427dcf9ff

def z623 : W := mkw 0xc82230540f02ac30 0x26411182a0781561 0x4470709c3b063c72 0x42238384e1d831e3

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x180300000000000c 0x18c0180000000000

def z625 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0xdfb30f9bf8000000 0x06fd987cdfc00000

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa850000c0000000 0x0554280006000000

def z627 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x238f8c60c4e1c001 0xb91c7c6306270e00

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x03800c0000e00001 0x801c006000070000

def z629 : W := mkw 0x0d926bdd7883063c 0x286c935eebc41831 0xeef5739cf9870e76 0xef77ab9ce7cc3873

def z630 : W := mkw 0x0000205400000010 0x20000102a0000000 0x7800007c00000000 0x03c00003e0000000

def z631 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7efff0fc0787fc1e 0xfbf7ff87e03c3fe0

def z632 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0x7c7ff37c2719fc7e 0x7be3ff9be138cfe3

def z633 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0x27ffffe0c7ffc003 0xf93fffff063ffe00

def z634 : W := mkw 0x0200042280000000 0x1010002114000000 0x83800c03c0000000 0x041c00601e000000

def z635 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0x17ff7f9b07fe318b 0xf8bffbfcd83ff18c

def z636 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0x112aff7b0460c189 0x108957fbd823060c

def z637 : W := mkw 0x8040100007540002 0x04020080003aa000 0x06d5008007fe0003 0xf836a804003ff000

def z638 : W := mkw 0xc5a07bdd3700a81c 0x2e2d03dee9b80540 0x7c7ff3fc3f01fc1c 0x7be3ff9fe1f80fe0

def z639 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xba858063c081c38c 0xadd42c031e040e1c

def z640 : W := mkw 0x0180215d3000001c 0x280c010ae9800000 0x4000001c38000000 0x02000000e1c00000

def z641 : W := mkw 0x84505a8047d50202 0x042282d4023ea810 0xafff7f80c7ff0207 0xfd7ffbfc063ff810

def z642 : W := mkw 0x11040109200810c8 0x8888200849004086 0x5933031b0218319d 0x5ac99818d810c18c

def z643 : W := mkw 0xd5647bdd275cb8da 0xaeab23dee93ae5c6 0xffffffff27ffffff 0xfffffffff93fffff

def z644 : W := mkw 0x0812000048830620 0x0040900002441831 0xec910004f8010e76 0xcf64880027c00873

def z645 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x3a0f8c60c4e1c00c 0x39d07c6306270e00

def z646 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9870c00 0x2776a80427cc3860

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x6ed5008401870c16 0xeb76a804200c3860

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x0122030002180001 0x100910180010c000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x2805000000010004 0x2940280000000800

def z650 : W := mkw 0x0200247680000010 0x30100123b4000000 0xfbff7c7fc0000000 0x07dffbe3fe000000

def z651 : W := mkw 0x0f924fabf883062c 0x187c927d5fc41831 0x87800f83f8860262 0x843c007c1fc43013

def z652 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7800807c0701fc1c 0x7bc00403e0380fe0

def z653 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0x224c7c84dde70c00 0x211263e426ef3860

def z654 : W := mkw 0x94445a80075c10c2 0x84a222d4003ae086 0x07ff7f8007fe33ff 0xf83ffbfc003ff19f

def z655 : W := mkw 0x2398257ff0a1431d 0x391cc12bff850a18 0xf800807ff801c38c 0x07c00403ffc00e1c

def z656 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000020000274 0x0640000001000013

def z657 : W := mkw 0x11040109200810c8 0x8888200849004086 0x9d830303201803ef 0x9cec18181900c01f

def z658 : W := mkw 0x11040109200810c8 0x8888200849004086 0x44300318221833ff 0xda218018c110c19f

def z659 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd800001b221833ff 0xdec00000d910c19f

def z660 : W := mkw 0x8040100007540002 0x04020080003aa000 0x0000000006780001 0x100000000033c000

def z661 : W := mkw 0x0100010920000008 0x0808000849000000 0x8580030320000000 0x042c001819000000

def z662 : W := mkw 0x11040109200810c8 0x8888200849004086 0x0100030300180181 0x000800181800c00c

def z663 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x407f701c07003c10 0x7a03fb80e03801e0

def z664 : W := mkw 0x15044b89200810c8 0x88a8225c49004086 0xdfff7f9b221833ff 0xdefffbfcd910c19f

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x0580030000180003 0x802c00180000c000

def z666 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0x112a7f1b06783189 0x108953f8d833c18c

def z667 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0xddf3731f23183fff 0xdeef9b98f918c1ff

def z668 : W := mkw 0x0812000048830620 0x0040900002441831 0x86d50080f9860262 0xec36a80407cc3013

def z669 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xfed500fff8000000 0x07f6a807ffc00000

def z670 : W := mkw 0xc7a07fffb700a81c 0x3e3d03fffdb80540 0xffff7ffffb003c10 0x47fffbffffd801e0

def z671 : W := mkw 0xb75c5fabe7fd53cb 0x9dbae2fd5f3fea9e 0xfffffffbe7fff3ff 0xffffffffdf3fff9f

def z672 : W := mkw 0x11040109200810c8 0x8888200849004086 0x5532031b221831fb 0x52a99018d910c18f

def z673 : W := mkw 0x84407ad407540012 0x242203d6a03aa000 0x7fff7ffc07fe0003 0xfbfffbffe03ff000

def z674 : W := mkw 0xcc727ad44fd7ae32 0x266393d6a27ebd71 0xfffffffcfffffe7f 0xffffffffe7fffff3

def z675 : W := mkw 0x0010000040810200 0x0000800002040810 0xead50004c1810e14 0xef56a800260c0870

def z676 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0xdfb30f1be2f833ff 0xdefd9878df17c19f

def z677 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x17ff7ffb00000000 0x00bffbffd8000000

def z678 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0x47ff7f9827fe3073 0xfa3ffbfcc13ff183

def z679 : W := mkw 0x0100215d20000018 0x2808010ae9000000 0xfdff737f20000000 0x07effb9bf9000000

def z680 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xddbb7f7b221833ff 0xdeeddbfbd910c19f

def z681 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x838f0c03c4e00381 0xbc1c78601e27001c

def z682 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x024c7c8007fe0003 0xf81263e4003ff000

def z683 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x557a7fff38000000 0x02abd3fff9c00000

def z684 : W := mkw 0x05004b8920000008 0x0828025c49000000 0xdfff7f9b20000000 0x06fffbfcd9000000

def z685 : W := mkw 0x0812000048830620 0x0040900002441831 0xae850080f8870266 0xad74280407c43813

def z686 : W := mkw 0x0812000048830620 0x0040900002441831 0x0000000000860262 0x8000000000043013

def z687 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x02000c00c0e00000 0x0010006006070000

def z688 : W := mkw 0xa6485ea287744103 0x153242f5143ba208 0x112aff630678c189 0x108957fb1833c60c

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x380f006000000000 0x01c0780300000000

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0x8480000020000262 0x8424000001000013

def z691 : W := mkw 0x0c524a8048d70622 0x006292540246b831 0x87800f80f8fe0263 0x843c007c07c7f013

def z692 : W := mkw 0x87c07fffb754001e 0x3c3e03fffdbaa000 0xffff7ffffe780001 0x17fffbfffff3c000

def z693 : W := mkw 0x0000000000000000 0x0000000000000000 0xeed50084f9010c14 0x6f76a80427c80860

def z694 : W := mkw 0x8000100007000000 0x0400008000380000 0x004c700005000000 0x2002638000280000

def z695 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0x224cf0e4dd87cc00 0x2112678726ec3e60

def z696 : W := mkw 0x07906ffff081021c 0x383c837fff840810 0xffff7ffff8810204 0xaffffbffffc40810

def z697 : W := mkw 0x0010000040810200 0x0000800002040810 0xeed50084f8810204 0xaf76a80427c40810

def z698 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x000080000001c38c 0x0000040000000e1c

def z699 : W := mkw 0x22182476c0a14311 0x3110c123b6050a18 0xfbfffc7fc4e1c38d 0xbfdfffe3fe270e1c

def z700 : W := mkw 0x2018000040a14301 0x0100c00002050a18 0x380f806004e1c38d 0xb9c07c0300270e1c

def z701 : W := mkw 0x0f826fffb802043c 0x387c137ffdc01021 0xffff7ffff9060c72 0x47fffbffffc83063

def z702 : W := mkw 0xc4607ad40754a812 0x262303d6a03aa540 0x4470739c031e3c12 0x4223839ce018f1e0

def z703 : W := mkw 0xe2381422c7a1eb01 0x1711c0a1163d0f58 0xbb8f8c63c7e1ff9d 0xfddc7c631e3f0ffc

def z704 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0xdfb3039bfa9e33ff 0xdefd981cdfd4f19f

def z705 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xab850c03c0e10385 0xad5c28601e07081c

def z706 : W := mkw 0x0300052ba0000008 0x181800295d000000 0xffbf0f7be0000000 0x07fdf87bdf000000

def z707 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007fe0001 0x303ffbfc003ff000

def z708 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07ff7f8004fe0003 0xb83ffbfc0027f000

def z709 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x334e7ce7d8000000 0x019a73e73ec00000

def z710 : W := mkw 0x885210004fd70622 0x04429080027eb831 0x0000000007fe0263 0xf8000000003ff013

def z711 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8c67e5e1cfff 0xfffefc633f2f0e7f

def z712 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xc470739ff8000000 0x0623839cffc00000

def z713 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xba0f8c63c4e1c38c 0x3dd07c631e270e1c

def z714 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xefff7f84fffe0277 0xff7ffbfc27fff013

def z715 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbf8f8ce3fde7cfff 0xfdfc7c671fef3e7f

def z716 : W := mkw 0x0200247680000010 0x30100123b4000000 0xffff7cfff8000000 0x07fffbe7ffc00000

def z717 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfb3039bfa1833ff 0xdefd981cdfd0c19f

def z718 : W := mkw 0x11040109200810c8 0x8888200849004086 0x1122031b021833eb 0x90891018d810c19f

def z719 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x264c7fe4f8000000 0x013263ff27c00000

def z720 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xa7cc7fe7f81803e3 0x853e63ff3fc0c01f

def z721 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x6fffff8407fffc1f 0xfb7ffffc203fffe0

def z722 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa183000 0x07fffbffffd0c180

def z723 : W := mkw 0x2a0a042288224521 0x1150502114411229 0x555a8ce73d66cdfb 0x52aad46739eb366f

def z724 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x23cf7ce4d8000000 0x011e7be726c00000

def z725 : W := mkw 0x0812000048830620 0x0040900002441831 0xe8400084f9070e74 0x0742000427c83873

def z726 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xa20c8c63c4e1c380 0x251064631e270e1c

def z727 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x27ff7fe4da180003 0xd93ffbff26d0c000

def z728 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x226c7ffcd8000000 0x011363ffe6c00000

def z729 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007ff0c17 0xf83ffbfc003ff860

def z730 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xeedd7ce4f8000276 0xcf76ebe727c00013

def z731 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xfff7739ff8000000 0x07ffbb9cffc00000

def z732 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0x6674739cf8000000 0x0333a39ce7c00000

def z733 : W := mkw 0x0812000048830620 0x0040900002441831 0xefd50087f9870ff7 0xef7ea8043fcc387f

def z734 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e1c381 0xa5dc7c631e270e1c

def z735 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8ce7c5e7cf9f 0xfffefc673e2f3e7c

def z736 : W := mkw 0x11040109200810c8 0x8888200849004086 0xffb7031be21833ff 0xdffdb818df10c19f

def z737 : W := mkw 0x2208042280204101 0x1110402114010208 0x10088c630460c188 0x008044631823060c

def z738 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0x87aa7f83f8000000 0x043d53fc1fc00000

def z739 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa003010 0x47fffbffffd00180

def z740 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddbf031b261833ff 0xfeedf818d930c19f

def z741 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbcf8c67c5e1cf8d 0xbdde7c633e2f0e7c

def z742 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x7a4c7cfcd8000000 0x03d263e7e6c00000

def z743 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x998b8c6304e1c38d 0xbccc5c6318270e1c

def z744 : W := mkw 0x26886ef690204115 0x31344377b4810208 0x334efce7dc60c189 0x119a77e73ee3060c

def z745 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x97ff7ffbf8000000 0x04bffbffdfc00000

def z746 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdb3031ffa1833ff 0xdfed9818ffd0c19f

def z747 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xbbcf7ce7d800038d 0x9dde7be73ec0001c

def z748 : W := mkw 0x95445b89275c10ca 0x8caa22dc493ae086 0xda4c7c9b25e633fc 0x26d263e4d92f319f

def z749 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x647073fcf8000000 0x0323839fe7c00000

def z750 : W := mkw 0x16846ef6900810d4 0xb0b42377b4804086 0x224c7ce4da1833ff 0xd91263e726d0c19f

def z751 : W := mkw 0x885210004fd70622 0x04429080027eb831 0x0000000005e70e76 0xe8000000002f3873

def z752 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xf8087c7ff8000000 0x07c043e3ffc00000

def z753 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x27ffffe007ffc003 0xf93fffff003ffe00

def z754 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbbf8c63c6e1c38d 0xfdddfc631e370e1c

def z755 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7afff07c0781fc1c 0xfbd7ff83e03c0fe0

def z756 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x2fff7f8007ff0007 0xf97ffbfc003ff800

def z757 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x034c7f8005fe0001 0x201a63fc002ff000

def z758 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfbcf8ce7fde7cffd 0xbfde7c673fef3e7f

def z759 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8e00001 0x87fffbffffc70000

def z760 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfb3039b229e33ff 0xdefd981cd914f19f

def z761 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xfeff70fff8000000 0x07f7fb87ffc00000

def z762 : W := mkw 0x0812000048830620 0x0040900002441831 0xecd10084f9070e76 0xcf66880427c83873

def z763 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e1c189 0x35dc7c631e270e0c

def z764 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xba0c8c63c4e1c38d 0xbdd064631e270e1c

def z765 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xff9f8c63e5e7cfff 0xfffcfc631f2f3e7f

def z766 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x386ff07c0701fc0c 0x39c37f83e0380fe0

def z767 : W := mkw 0x2208042280204101 0x1110402114010208 0x118b8c630460c189 0x988c5c631823060c

def z768 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x47ff7f8407fe0c13 0xfa3ffbfc203ff060

def z769 : W := mkw 0x46a06ef69000a814 0x32350377b4800540 0x7a4cfcfcd801fc1c 0x03d267e7e6c00fe0

def z770 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084fb873e7e 0xff76a80427dc39f3

def z771 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0xdfff7f9bf8000000 0x06fffbfcdfc00000

def z772 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x624c7cfcf8000000 0x031263e7e7c00000

def z773 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07ff7f8002fe0003 0xd83ffbfc0017f000

def z774 : W := mkw 0x11040109200810c8 0x8888200849004086 0x9da3031b221833ef 0x9ced1818d910c19f

def z775 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07fc7f8007fe0003 0xe03fe3fc003ff000

def z776 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfb8f8c67c4e1cf9d 0xbfdc7c633e270e7c

def z777 : W := mkw 0x2208042280204101 0x1110402114010208 0x190b8c630460c18d 0x18c85c631823060c

def z778 : W := mkw 0x2208042280204101 0x1110402114010208 0x138a8c6304e0c189 0x909c54631827060c

def z779 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b221833eb 0x96ed9818d910c19f

def z780 : W := mkw 0x0812000048830620 0x0040900002441831 0xffdf0c87fde70fff 0xfffef8643fef387f

def z781 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xf87ff07cff01fc1c 0x7fc3ff83e7f80fe0

def z782 : W := mkw 0xd124315d2708b8d8 0xae89218ae93845c6 0xa5ccf3672519cfe3 0xa52e679b3928ce7f

def z783 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x107ff0780701fc1c 0x7883ff83c0380fe0

def z784 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0x110a8c6305e7cfff 0xf8885463182f3e7f

def z785 : W := mkw 0x2208042280204101 0x1110402114010208 0x990a8c630460c38d 0x14c854631823061c

def z786 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfff7039ffb9e33ff 0xffffb81cffdcf19f

def z787 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084fde70e77 0xff76a80427ef3873

def z788 : W := mkw 0x2208042280204101 0x1110402114010208 0xdd9b8c632460c3ff 0xdeecdc631923061f

def z789 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa003008 0x17fffbffffd00180

def z790 : W := mkw 0x8c525a804fd70622 0x046292d4027eb831 0xe92a7f04fe790e75 0x174953f827f3c873

def z791 : W := mkw 0x402020540000a810 0x22010102a0000540 0x784cf07c0001fc1c 0x03c26783e0000fe0

def z792 : W := mkw 0x2208042280204101 0x1110402114010208 0x01088c630460c181 0x000844631823060c

def z793 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x236e7fe4d8000000 0x011b73ff26c00000

def z794 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x3fff7fe007fe0003 0xf9fffbff003ff000

def z795 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0x334e8ce7dde7cd89 0x319a74673eef3e6c

def z796 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0x87f07f83f8000000 0x043f83fc1fc00000

def z797 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8c63c5e7cf8d 0xbddc7c631e2f3e7c

def z798 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x87c07f87f8000000 0x043e03fc3fc00000

def z799 : W := mkw 0xa6585ea2c7f54303 0x1532c2f5163faa18 0xbc70f3e3c31fc38e 0x45e3879f1e18fe1c

def z800 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1833f3 0xc7fffbffffd0c19f

def z801 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa18307e 0x5ffffbffffd0c183

def z802 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x102af0780601fc1c 0x10815783c0300fe0

def z803 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xefdd8ce7fde7cff7 0xef7eec673fef3e7f

def z804 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x6fff7f8407fe0003 0xfb7ffbfc203ff000

def z805 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffff81e0002 0x07fffbffffc0f000

def z806 : W := mkw 0x2208042280204101 0x1110402114010208 0x795f8c670561cd9d 0x7bcafc63382b0e6c

def z807 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddbb0f1b267833ff 0xdeedd878d933c19f

def z808 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddf3039f3a1833ff 0xdeef981cf9d0c19f

def z809 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x47ff7f843ffe0003 0xfa3ffbfc21fff000

def z810 : W := mkw 0x04806ad410000014 0x20240356a0800000 0x22447084d8000000 0x0112238426c00000

def z811 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xeed58084fde7ce76 0xef76ac0427ef3e73

def z812 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1833eb 0x97fffbffffd0c19f

def z813 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfa7f7cfff8000000 0x07d3fbe7ffc00000

def z814 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0301fc1c 0x43c3ff83e0180fe0

def z815 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7a7ff0fcdf01fc1c 0x7bd3ff87e6f80fe0

def z816 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000072 0x47fffbffffc00003

def z817 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa180277 0xdffffbffffd0c013

def z818 : W := mkw 0x2208042280204101 0x1110402114010208 0x918a8c630460c389 0x948c54631823061c

def z819 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdc30031b221833ff 0xdee18018d910c19f

def z820 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfdfff37c2719fe7f 0xffefff9be138cff3

def z821 : W := mkw 0x44606ad40054a812 0x22230356a002a540 0x7f808ffc00fffc1f 0x83fc047fe007ffe0

def z822 : W := mkw 0x8040100007540002 0x04020080003aa000 0xeed50084fffe0003 0xff76a80427fff000

def z823 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07aa7f8000fe0003 0x803d53fc0007f000

def z824 : W := mkw 0x26886ef690204115 0x31344377b4810208 0x224cfce4dc60c000 0x011267e726e30600

def z825 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xfffffffff800c188 0x07ffffffffc0060c

def z826 : W := mkw 0x57a46fffb008b8dc 0xbabd237ffd8045c6 0xfffffffff801fffc 0x07ffffffffc00fff

def z827 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xa3cc7ce7d8000000 0x051e63e73ec00000

def z828 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xcfff7f8027fe0003 0xfe7ffbfc013ff000

def z829 : W := mkw 0x11040109200810c8 0x8888200849004086 0xc5b0031b221833ff 0xde2d8018d910c19f

def z830 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x26dd7ce4d8000000 0x0136ebe726c00000

def z831 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa18038f 0xdffffbffffd0c01c

def z832 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x390f8c6304e1c38d 0xb9c87c6318270e1c

def z833 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffde60003 0xfffffbffffef3000

def z834 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07cf7f8005fe0003 0xb83e7bfc002ff000

def z835 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x012a7f0007fe0001 0x300953f8003ff000

def z836 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfb8f8c67fde7cfff 0xffdc7c633fef3e7f

def z837 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c5e7c38f 0xfddc7c631e2f3e1c

def z838 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b221833fe 0x46ed9818d910c19f

def z839 : W := mkw 0x17c46fffb05c10de 0xb8be237ffd82e086 0xffff7ffffafe33ff 0xdffffbffffd7f19f

def z840 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0x000080000587ce76 0xe8000400002c3e73

def z841 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffb013c1c 0x7ffffbffffd809e0

def z842 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b23193fff 0xfeed9818d918c9ff

def z843 : W := mkw 0x0812000048830620 0x0040900002441831 0xea440084f9870e76 0xef52200427cc3873

def z844 : W := mkw 0x0802000008020420 0x0040100000401021 0x66540084f9060c72 0x4332a00427c83063

def z845 : W := mkw 0x0812000048830620 0x0040900002441831 0xefd50c84f9e70e77 0xef7ea86427cf3873

def z846 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x627c7cfcd8000000 0x0313e3e7e6c00000

def z847 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xdfff7f8327fe03ff 0xfefffbfc193ff01f

def z848 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfa4c8ce7fde7cffc 0x27d264673fef3e7f

def z849 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xbfaf7ffbf8000000 0x05fd7bffdfc00000

def z850 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xdfff7f9827fe327f 0xfefffbfcc13ff193

def z851 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x036e7f8007fe0003 0xf81b73fc003ff000

def z852 : W := mkw 0x0802000008020420 0x0040100000401021 0xeed50084f9860c72 0xef76a80427cc3063

def z853 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb98b8c63c461c38d 0x9dcc5c631e230e1c

def z854 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x938f8c63c4e0c389 0xbc9c7c631e27061c

def z855 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff81803f7 0xcffffbffffc0c01f

def z856 : W := mkw 0x11040109200810c8 0x8888200849004086 0x5532031b221833ff 0xdaa99018d910c19f

def z857 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1831fb 0x57fffbffffd0c18f

def z858 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffc01c38d 0xbfffffffffe00e1c

def z859 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xf97f7f7ff8000000 0x07cbfbfbffc00000

def z860 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xab8d8c63c4e1c385 0xad5c6c631e270e1c

def z861 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000189 0x17fffbffffc0000c

def z862 : W := mkw 0x995611096fdf16ea 0x8ccab0884b7ef8b7 0xddb3031b27ff3fff 0xfeed9818d93ff9ff

def z863 : W := mkw 0x11040109200810c8 0x8888200849004086 0x1122031b021833fd 0x10891018d810c19f

def z864 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfff0f9b27fe33ff 0xfefff87cd93ff19f

def z865 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa183276 0xcffffbffffd0c193

def z866 : W := mkw 0x1104215d200810d8 0xa888210ae9004086 0xffff73fffa1833ff 0xdffffb9fffd0c19f

def z867 : W := mkw 0x2208042280204101 0x1110402114010208 0x138f8c630460c189 0x109c7c631823060c

def z868 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7c7ff0fc0707fc1e 0x7be3ff87e0383fe0

def z869 : W := mkw 0x46a06ef69000a814 0x32350377b4800540 0x224cfce4d801cc00 0x011267e726c00e60

def z870 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x326e7cfcd8000000 0x019373e7e6c00000

def z871 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfedd8ce7fde7cffe 0xeff6ec673fef3e7f

def z872 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdb3837b2219f3ff 0xdfed9c1bd910cf9f

def z873 : W := mkw 0x0f926ffff883063c 0x387c937fffc41831 0x112a7f7b01870e76 0xe88953fbd80c3873

def z874 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1833fe 0x47fffbffffd0c19f

def z875 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xefff7f84ffff0c17 0xff7ffbfc27fff860

def z876 : W := mkw 0x2208042280204101 0x1110402114010208 0x3b8f8c6304e1c18d 0xb9dc7c6318270e0c

def z877 : W := mkw 0x83c0357fb754001e 0x3c1e01abfdbaa000 0xf800007ffffe0003 0xffc00003fffff000

def z878 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa0033fc 0x5ffffbffffd0019f

def z879 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffb193fff 0xfffffbffffd8c9ff

def z880 : W := mkw 0xd83610004f8bbee0 0x86c1b080027c5df7 0x00008000079fffff 0xf8000400003cffff

def z881 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbf8f8ce3fce1c38d 0xbdfc7c671fe70e1c

def z882 : W := mkw 0x25986bdd70a1431d 0x292cc35eeb850a18 0x4470f39c3ce1c38d 0xba23879ce1e70e1c

def z883 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xc7ff7f9ff8000000 0x063ffbfcffc00000

def z884 : W := mkw 0x0000205400000010 0x20000102a0000000 0xeef5709cf8000000 0x0777ab84e7c00000

def z885 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbf8f8c63e4e1c3ef 0xbdfc7c631f270e1f

def z886 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x110a8c6304e1c189 0x3088546318270e0c

def z887 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x3a4f7ce4d8000000 0x01d27be726c00000

def z888 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07f07f8000fe0003 0x803f83fc0007f000

def z889 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffce00000 0x27fffbffffe70000

def z890 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xffff7ffff8003c10 0x07fffbffffc001e0

def z891 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000014 0x4ffffbffffc00000

def z892 : W := mkw 0x0812000048830620 0x0040900002441831 0xefd70084f9870e77 0xff7eb80427cc3873

def z893 : W := mkw 0x06c06ef690540016 0x30360377b482a000 0x27cc7fe4d8fe0003 0x813e63ff26c7f000

def z894 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb8088c63c461c38c 0x05c044631e230e1c

def z895 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c461c38d 0x15dc7c631e230e1c

def z896 : W := mkw 0x0802000008020420 0x0040100000401021 0xec500084f9060c72 0x4762800427c83063

def z897 : W := mkw 0x885210004fd70622 0x04429080027eb831 0x0000000007ff0c03 0xf8000000003ff860

def z898 : W := mkw 0x331c052be0a953c9 0x9998e0295f054a9e 0x663c8f78e6f9f072 0x6331e47bc737cf83

def z899 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x5fff7f9807fe0003 0xfafffbfcc03ff000

def z900 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x665c7ce4f8000000 0x0332e3e727c00000

def z901 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa183073 0xdffffbffffd0c183

def z902 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfdbb7f7ff8000000 0x07eddbfbffc00000

def z903 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfb7031b229833ff 0xfefdb818d914c19f

def z904 : W := mkw 0xe2383476c7a1eb11 0x3711c1a3b63d0f58 0xc3f07c1fc3e03f91 0xc61f83e0fe1f01fc

def z905 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x267c7fe4d8000000 0x0133e3ff26c00000

def z906 : W := mkw 0x2208042280204101 0x1110402114010208 0xb90a8c63c460c189 0x15c854631e23060c

def z907 : W := mkw 0x06004ea280000000 0x1030027514000000 0xffff7fe7f8000000 0x07fffbff3fc00000

def z908 : W := mkw 0x0812000048830620 0x0040900002441831 0xffdf8ce4fde7ce7f 0xfffefc6727ef3e73

def z909 : W := mkw 0x2208042280204101 0x1110402114010208 0xb98f8c630461c38d 0xbdcc7c6318230e1c

def z910 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7dfff37c0701fc1c 0x7befff9be0380fe0

def z911 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xf820737ff8000000 0x07c1039bffc00000

def z912 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x130a8c63c4e0c189 0x109854631e27060c

def z913 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x138f8c6304e1c38d 0xb89c7c6318270e1c

def z914 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xffdf8ce7fde7cf8d 0xbffefc673fef3e7c

def z915 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xba8d8c63c4e1c38c 0xadd46c631e270e1c

def z916 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1833fd 0x17fffbffffd0c19f

def z917 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8010c14 0x07fffbffffc00860

def z918 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdff7039b221833ff 0xdeffb81cd910c19f

def z919 : W := mkw 0x06804ea290000004 0x1034027514800000 0x024c7c80d8000000 0x001263e406c00000

def z920 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x206cf07c0701fc00 0x21036783e0380fe0

def z921 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x797ff07f0701fd9d 0x7bcbff83f8380fec

def z922 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007fe301f 0xf83ffbfc003ff180

def z923 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x307ff07c0701fc08 0x7983ff83e0380fe0

def z924 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x67ff7ffcf8000000 0x033ffbffe7c00000

def z925 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfbfffc7f07e1ff9d 0xffdfffe3f83f0ffc

def z926 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xfdf373fffa1833ff 0xdfef9b9fffd0c19f

def z927 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xffd78087fde7cfff 0xfffebc043fef3e7f

def z928 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x304cf07c0501fc08 0x21826783e0280fe0

def z929 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xa6cc7ce4f8000000 0x053663e727c00000

def z930 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffcc7ffff8000000 0x07fe63ffffc00000

def z931 : W := mkw 0x04004a8000000000 0x0020025400000000 0xeedd7c84f8000000 0x0776ebe427c00000

def z932 : W := mkw 0x2208042280204101 0x1110402114010208 0x110a8c6304e0c189 0xb88854631827060c

def z933 : W := mkw 0x19160109688b16e8 0x88c8b0084b4458b7 0x3366039fdb9f3d89 0x319b301cfedcf9ec

def z934 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfbdf8c67fde1cffd 0xffdefc633fef0e7f

def z935 : W := mkw 0x0812000048830620 0x0040900002441831 0xeeff7084f9870e76 0xef77fb8427cc3873

def z936 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b221833fd 0x16ed9818d910c19f

def z937 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8800000 0xaffffbffffc40000

def z938 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbdf8c63c5e1c38d 0xfddefc631e2f0e1c

def z939 : W := mkw 0x2208042280204101 0x1110402114010208 0xbb8f8c63c4e0c189 0xbddc7c631e27060c

def z940 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd820031b221833fc 0x06c10018d910c19f

def z941 : W := mkw 0x17844fabb00810cc 0x98bc227d5d804086 0xdfff7f9bfa1833ff 0xdefffbfcdfd0c19f

def z942 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8010004 0x2ffffbffffc00800

def z943 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xff9f8c63e4e1c38d 0xbffcfc631f270e1c

def z944 : W := mkw 0x0812000048830620 0x0040900002441831 0xec500084f9870e76 0xef62800427cc3873

def z945 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07f07f8007fe0003 0xf83f83fc003ff000

def z946 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787af07c0701fc1c 0x53c3d783e0380fe0

def z947 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x302af07c0601fc08 0x11815783e0300fe0

def z948 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b221833f3 0xc6ed9818d910c19f

def z949 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7cfff07c0701fc1e 0xfbe7ff83e0380fe0

def z950 : W := mkw 0x0000205400000010 0x20000102a0000000 0xfeff70fcfa00327e 0xdff7fb87e7d00193

def z951 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x026c7f8007fe0000 0x201363fc003ff000

def z952 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8a8c63c4e1c38d 0x95dc54631e270e1c

def z953 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x46707f9cf8000000 0x023383fce7c00000

def z954 : W := mkw 0xc83230544f83ae30 0x26419182a27c1d71 0x96aaf0f8fe86f26a 0x94b55787c7f43793

def z955 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xfeff73fcf8000000 0x07f7fb9fe7c00000

def z956 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff800000c 0x1ffffbffffc00000

def z957 : W := mkw 0x0280247690000014 0x30140123b4800000 0x204c7064d8000000 0x0102638326c00000

def z958 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xf84070fff8000000 0x07c20387ffc00000

def z959 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfbdf8ce7dde7cf9d 0xffdefc673eef3e7c

def z960 : W := mkw 0x0812205448830630 0x20409102a2441831 0x787f707c01870e76 0xebc3fb83e00c3873

def z961 : W := mkw 0x17844fabb00810cc 0x98bc227d5d804086 0x87ff7f83fa1803e3 0xdc3ffbfc1fd0c01f

def z962 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8ce7fde7c38f 0xfffefc673fef3e1c

def z963 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbfdf8ce3c5e7cfff 0xfdfefc671e2f3e7f

def z964 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x37ff7fffd8000000 0x01bffbfffec00000

def z965 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffff801c00c 0x07ffffffffc00e00

def z966 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x910a8c63c460c389 0x148854631e23061c

def z967 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdf7031f221833ff 0xdfefb818f910c19f

def z968 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa18301f 0xdffffbffffd0c180

def z969 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x787ff07c07e7fc1c 0x7bc3ff83e03f3fe0

def z970 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xfffffffffce0c189 0xbfffffffffe7060c

def z971 : W := mkw 0x0812000048830620 0x0040900002441831 0x6e550084f9870c76 0x6b72a80427cc3863

def z972 : W := mkw 0x0812000048830620 0x0040900002441831 0xee800084f9870e76 0xef74000427cc3873

def z973 : W := mkw 0x378c6fffb02851dd 0xb9bc637ffd81428e 0xfffffffffe78f3ff 0xdffffffffff3c79f

def z974 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x782ff07c0601fc1c 0x3bc17f83e0300fe0

def z975 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0x000080000701fe7c 0x7800040000380ff3

def z976 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfefff0fc2787fe7e 0xfff7ff87e13c3ff3

def z977 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0701fc08 0x33c3ff83e0380fe0

def z978 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xf8fff07c0701fe1c 0xffc7ff83e0380ff0

def z979 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ffff8007ffc00f 0xf83ffffc003ffe00

def z980 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfb9f8c63c4e1c39d 0xffdcfc631e270e1c

def z981 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x23cf7ce4dce00001 0xb91e7be726e70000

def z982 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7875f07c0301fc1c 0x6bc3af83e0180fe0

def z983 : W := mkw 0x2208042280204101 0x1110402114010208 0x390a8c630461c18d 0x11c8546318230e0c

def z984 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7a7ffc7c07e1fc1c 0x7bd3ffe3e03f0fe0

def z985 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07a07f8002fe0003 0x803d03fc0017f000

def z986 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xeff57f9ff8000000 0x077fabfcffc00000

def z987 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbfcf8ce7fde7cfef 0xbdfe7c673fef3e7f

def z988 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xfffffffffc60c000 0x07ffffffffe30600

def z989 : W := mkw 0x0812000048830620 0x0040900002441831 0x46500084f9860c72 0x4232800427cc3063

def z990 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x787ff07c0779fc1d 0x7bc3ff83e03bcfe0

def z991 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xffdf8ce7fce1cffd 0xbffefc673fe70e7f

def z992 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xfffffffffc01fc1c 0x3fffffffffe00fe0

def z993 : W := mkw 0x0812000048830620 0x0040900002441831 0xeff70384f9870e76 0xef7fb81c27cc3873

def z994 : W := mkw 0x402020540000a810 0x22010102a0000540 0x787ff07c0401fc1c 0x3bc3ff83e0200fe0

def z995 : W := mkw 0xc3a0357fb700a81c 0x3e1d01abfdb80540 0xf800807fff01fc1c 0x7fc00403fff80fe0

def z996 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7820f07c0201fc1c 0x03c10783e0100fe0

def z997 : W := mkw 0x57a46fffb008b8dc 0xbabd237ffd8045c6 0xfffffffffa19ffff 0xdfffffffffd0cfff

def z998 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffb9e0003 0xfffffbffffdcf000

def z999 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdb7031b221933ff 0xffedb818d910c99f

def z1000 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xa7cc8ce7fde7cfe3 0xa53e64673fef3e7f

def z1001 : W := mkw 0x0812000048830620 0x0040900002441831 0x62440084f9870c70 0x2312200427cc3863

def z1002 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfb8f8c67fce1c38d 0xbfdc7c633fe70e1c

def z1003 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8c63c4e1cffd 0xbddc7c631e270e7f

def z1004 : W := mkw 0x0812000048830620 0x0040900002441831 0x66540084f9870e76 0xeb32a00427cc3873

def z1005 : W := mkw 0x11040109200810c8 0x8888200849004086 0x95b3031b221833eb 0xdcad9818d910c19f

def z1006 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdd32031b221833ff 0x56e99018d910c19f

def z1007 : W := mkw 0xd5647bdd275cb8da 0xaeab23dee93ae5c6 0x4470739c231e3c72 0x4223839ce118f1e3

def z1008 : W := mkw 0x2208042280204101 0x1110402114010208 0x110f8c630460c189 0x38887c631823060c

def z1009 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7bfffc7c0701fc1c 0x7bdfffe3e0380fe0

def z1010 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x7fff7ffcd8000000 0x03fffbffe6c00000

def z1011 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x05bb7f0007fe0003 0xf82ddbf8003ff000

def z1012 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9000000 0x6ffffbffffc80000

def z1013 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x110a8c630461c38d 0x1088546318230e1c

def z1014 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x7fff7f9c07ff3c1f 0xfbfffbfce03ff9e0

def z1015 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x067f7f8007fe0002 0x7833fbfc003ff000

def z1016 : W := mkw 0x402020540000a810 0x22010102a0000540 0x782af07c0001fc1c 0x03c15783e0000fe0

def z1017 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbbcf8ce7dde7cfff 0xfdde7c673eef3e7f

def z1018 : W := mkw 0x0802000008020420 0x0040100000401021 0xeed50084f9060e76 0xcf76a80427c83073

def z1019 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfbff8c7fc7e1ff9d 0xffdffc63fe3f0ffc

def z1020 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddf3039b231e33ff 0xdeef981cd918f19f

def z1021 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07cc7f8007fe0003 0xf83e63fc003ff000

def z1022 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x777e7ffff8000000 0x03bbf3ffffc00000

def z1023 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xe7fc7ffff8000000 0x073fe3ffffc00000

def z1024 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xff8f8ce7fce7cfff 0xbffc7c673fe73e7f

def z1025 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8ce7fce1c3ff 0xfffefc673fe70e1f

def z1026 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x87ff7f8027fe0263 0xfc3ffbfc013ff013

def z1027 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbf8f8ce3c4e7c38f 0xbdfc7c671e273e1c

def z1028 : W := mkw 0x0812000048830620 0x0040900002441831 0xffd70087f9870e76 0xeffeb8043fcc3873

def z1029 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa18318b 0xdffffbffffd0c18c

def z1030 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfb30f1b22f833ff 0xdefd9878d917c19f

def z1031 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x338f8c63c4e1c189 0xb99c7c631e270e0c

def z1032 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07887f8004fe0003 0x803c43fc0027f000

def z1033 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x224c7ce4dce00000 0x211263e726e70000

def z1034 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7ffffcfc07e7fc1f 0xfbffffe7e03f3fe0

def z1035 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07f57f8003fe0003 0xe83fabfc001ff000

def z1036 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e1c3ff 0xfddc7c631e270e1f

def z1037 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9010c00 0x27fffbffffc80860

def z1038 : W := mkw 0x885210004fd70622 0x04429080027eb831 0x0000000005e70c00 0x20000000002f3860

def z1039 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb90f8c63c461c38d 0x3dc87c631e230e1c

def z1040 : W := mkw 0x0812000048830620 0x0040900002441831 0x66d50084f9870c72 0xeb36a80427cc3863

def z1041 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000274 0x07fffbffffc00013

def z1042 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xb7ee7ffff8000000 0x05bf73ffffc00000

def z1043 : W := mkw 0x05004b8920000008 0x0828025c49000000 0xffff7f9ff8000000 0x07fffbfcffc00000

def z1044 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x382ff0780701fc1c 0x79c17f83c0380fe0

def z1045 : W := mkw 0x402020540000a810 0x22010102a0000540 0x787ff07c0201fc1c 0x5bc3ff83e0100fe0

def z1046 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xf870707ff8000000 0x07c38383ffc00000

def z1047 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfcfff07c2701fc1c 0x7fe7ff83e1380fe0

def z1048 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff800038c 0x07fffbffffc0001c

def z1049 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffffcfe0003 0xbffffbffffe7f000

def z1050 : W := mkw 0x2208042280204101 0x1110402114010208 0x110a8c630460c38d 0x988854631823061c

def z1051 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffe01f01c 0x7ffffffffff00f80

def z1052 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x583bf0780701fc1c 0x7ac1df83c0380fe0

def z1053 : W := mkw 0x2208042280204101 0x1110402114010208 0xbb8f8c63c460c38d 0x9ddc7c631e23061c

def z1054 : W := mkw 0x0000205400000010 0x20000102a0000000 0x7a7f70fcd8000000 0x03d3fb87e6c00000

def z1055 : W := mkw 0x2208042280204101 0x1110402114010208 0x593b8c7b0660f19d 0x5ac9dc63d833078c

def z1056 : W := mkw 0x1384257fb00810dc 0xb89c212bfd804086 0xfdff737ffa1833ff 0xdfeffb9bffd0c19f

def z1057 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb0031b221833ff 0xc6ed8018d910c19f

def z1058 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x17ffffe007fec00b 0xf8bfffff003ff600

def z1059 : W := mkw 0x04006ad400000010 0x20200356a0000000 0xffff7ffcf8000000 0x07fffbffe7c00000

def z1060 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbf8f8f63c4f9c38f 0xbdfc7c7b1e27ce1c

def z1061 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084fb9f0e77 0xff76a80427dcf873

def z1062 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xfbdf8c67c5e7cfff 0xffdefc633e2f3e7f

def z1063 : W := mkw 0x402020540000a810 0x22010102a0000540 0x787ff07c0101fc1c 0x6bc3ff83e0080fe0

def z1064 : W := mkw 0xc7a05fabb700a80c 0x1e3d02fd5db80540 0x87808f83ff01fc1c 0x7c3c047c1ff80fe0

def z1065 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffce1c00d 0xbfffffffffe70e00

def z1066 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xfffffffffe19f3ff 0xfffffffffff0cf9f

def z1067 : W := mkw 0x0812000048830620 0x0040900002441831 0xfef7009cf9870e76 0xeff7b804e7cc3873

def z1068 : W := mkw 0x11040109200810c8 0x8888200849004086 0x99a3031b021833ff 0xdccd1818d810c19f

def z1069 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xfedf80e4fde7cfff 0xfff6fc0727ef3e7f

def z1070 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xdfbb7ffbfa1833ff 0xdefddbffdfd0c19f

def z1071 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb90a8c63c4e1c38d 0xbdc854631e270e1c

def z1072 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdda2031b221833ff 0x96ed1018d910c19f

def z1073 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7efff0fc0701fc1c 0x7bf7ff87e0380fe0

def z1074 : W := mkw 0x1384257fb00810dc 0xb89c212bfd804086 0xf87f707ffa0033fc 0x5fc3fb83ffd0019f

def z1075 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x912a7f7bf8000000 0x048953fbdfc00000

def z1076 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfd7a7ffff8000000 0x07ebd3ffffc00000

def z1077 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfc7f73fff8000000 0x07e3fb9fffc00000

def z1078 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xfffffffffc60c38d 0x9fffffffffe3061c

def z1079 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x7a7f7cfcda00301c 0x5bd3fbe7e6d00180

def z1080 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0xdcb380182787fe7e 0xfee59c00c13c3ff3

def z1081 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07dd7f8005fe0003 0xe83eebfc002ff000

def z1082 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x20087c64d8000000 0x010043e326c00000

def z1083 : W := mkw 0x0812000048830620 0x0040900002441831 0x64500084f9070c72 0x4322800427c83863

def z1084 : W := mkw 0x2208042280204101 0x1110402114010208 0x130e8c6304e0c189 0x309874631827060c

def z1085 : W := mkw 0x0812000048830620 0x0040900002441831 0xaec50084f9870e66 0xad76280427cc3873

def z1086 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0x87cc7f83f8000000 0x043e63fc1fc00000

def z1087 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x032a7f8006fe0001 0x101953fc0037f000

def z1088 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfdfff37f0719ff9f 0xffefff9bf838cffc

def z1089 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c07e1fc1d 0xfbc3ff83e03f0fe0

def z1090 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfefff0fcff01fe7e 0xfff7ff87e7f80ff3

def z1091 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x6a5d7ce4d8000000 0x0352ebe726c00000

def z1092 : W := mkw 0x0812000048830620 0x0040900002441831 0xa2440084f9870e60 0x2512200427cc3873

def z1093 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xf82a707ff8000000 0x07c15383ffc00000

def z1094 : W := mkw 0x885210004fd70622 0x04429080027eb831 0xcdb3030027ff0e77 0xfe6d9818013ff873

def z1095 : W := mkw 0x15846bdd300810dc 0xa8ac235ee9804086 0xfff7739ffa1833ff 0xdfffbb9cffd0c19f

def z1096 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa00327e 0xdffffbffffd00193

def z1097 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff8003070 0x07fffbffffc00183

def z1098 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0701fe7e 0xfbc3ff83e0380ff3

def z1099 : W := mkw 0x2208042280204101 0x1110402114010208 0x938a8c63c460c189 0x149c54631e23060c

def z1100 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdfbf0f1b221833ff 0xdefdf878d910c19f

def z1101 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xffff8cffffe7ffff 0xfffffc67ffff3fff

def z1102 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbfdf8ce3c4e1c38d 0xbdfefc671e270e1c

def z1103 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9870fff 0xff76a80427cc387f

def z1104 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xfdbb7f7ffa1833ff 0xdfeddbfbffd0c19f

def z1105 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfbdf8c67c4e1c38d 0xbfdefc633e270e1c

def z1106 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9870e74 0x2776a80427cc3873

def z1107 : W := mkw 0x0000205400000010 0x20000102a0000000 0xeedd70e4f8000000 0x0776eb8727c00000

def z1108 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x47ff7f8027fe0073 0xfa3ffbfc013ff003

def z1109 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9000c10 0x47fffbffffc80060

def z1110 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9070e76 0x4776a80427c83873

def z1111 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd933031b221833fd 0x5ec99818d910c19f

def z1112 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbfffc63c4e1c38d 0xbddfffe31e270e1c

def z1113 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x3b0f8c63c4e1c18d 0x39d87c631e270e0c

def z1114 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xaacd7ce4d8000000 0x05566be726c00000

def z1115 : W := mkw 0x0812000048830620 0x0040900002441831 0x86c00084f9860e62 0x8436000427cc3073

def z1116 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffffafe0003 0xdffffbffffd7f000

def z1117 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x02087ce0d8000000 0x001043e706c00000

def z1118 : W := mkw 0x04004a8000000000 0x0020025400000000 0xeef57384f8000000 0x0777ab9c27c00000

def z1119 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b239e33ff 0xfeed9818d91cf19f

def z1120 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x79fff07c0701fc1d 0xfbcfff83e0380fe0

def z1121 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb0e8c63c4e1c38d 0x35d874631e270e1c

def z1122 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x1fff7f8007fe000f 0xf8fffbfc003ff000

def z1123 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x310a8c63c461c189 0x118854631e230e0c

def z1124 : W := mkw 0x985610004fdf16e2 0x84c2b080027ef8b7 0x0000000007ff3fff 0xf8000000003ff9ff

def z1125 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfbaf7f7ff8000000 0x07dd7bfbffc00000

def z1126 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa18338d 0x9ffffbffffd0c19c

def z1127 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffff8780001 0x07fffbffffc3c000

def z1128 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x230c8c63c4e1c181 0x211864631e270e0c

def z1129 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xa24c7ce7f8000000 0x051263e73fc00000

def z1130 : W := mkw 0x0812000048830620 0x0040900002441831 0xa6c40084f9870e76 0xed36200427cc3873

def z1131 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x4fff7f8007fe0017 0xfa7ffbfc003ff000

def z1132 : W := mkw 0x0812000048830620 0x0040900002441831 0xa6d50084f9870e62 0xed36a80427cc3873

def z1133 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xff9f8c67fce1cfff 0xfffcfc633fe70e7f

def z1134 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbf9f8c63c4e1c38f 0xfdfcfc631e270e1c

def z1135 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8180003 0x87fffbffffc0c000

def z1136 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa00339d 0xdffffbffffd0019c

def z1137 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x6a5d7ce4d9010c14 0x6b52ebe726c80860

def z1138 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7870f07c0701fc1c 0x7bc38783e0380fe0

def z1139 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdff837f2719ffff 0xffeffc1bf938cfff

def z1140 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x037f7f8007fe0001 0x781bfbfc003ff000

def z1141 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e1c38c 0x25dc7c631e270e1c

def z1142 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffb9e33ff 0xfffffbffffdcf19f

def z1143 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffbf8c7be6e1f3ff 0xfffdfc63df370f9f

def z1144 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xb38e8c63c4e1c389 0xb59c74631e270e1c

def z1145 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddf7031b231833ff 0xfeefb818d918c19f

def z1146 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07fa7f8007fe0003 0xd03fd3fc003ff000

def z1147 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x938a8c63c4e1c38d 0xbc9c54631e270e1c

def z1148 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbfdf8ce3fde7c3ef 0xfdfefc671fef3e1f

def z1149 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x8fff7f8007fe0207 0xfc7ffbfc003ff010

def z1150 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa18319d 0x5ffffbffffd0c18c

def z1151 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff800301c 0x07fffbffffc00180

def z1152 : W := mkw 0x0812000048830620 0x0040900002441831 0xeef50384fb9f0e76 0xef77a81c27dcf873

def z1153 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3831b2619f3ff 0xfeed9c18d930cf9f

def z1154 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0xbfff7fe3f8000000 0x05fffbff1fc00000

def z1155 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x07ff7f8007fe3c13 0xf83ffbfc003ff1e0

def z1156 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbcf8ce7dce1c38d 0xbdde7c673ee70e1c

def z1157 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07cc7f8000fe0003 0x803e63fc0007f000

def z1158 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xeed50084f9e70ff7 0xef76a80427cf387f

def z1159 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xfffffffffa01fc1c 0x5fffffffffd00fe0

def z1160 : W := mkw 0x06804ea290000004 0x1034027514800000 0x07ff7f80d8000000 0x003ffbfc06c00000

def z1161 : W := mkw 0x0812000048830620 0x0040900002441831 0xfeff80fcff87fe7e 0xfff7fc07e7fc3ff3

def z1162 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xdfbb7ffbf8000000 0x06fddbffdfc00000

def z1163 : W := mkw 0x2208042280204101 0x1110402114010208 0x310e8c630461c189 0x3188746318230e0c

def z1164 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffa1803e3 0xdffffbffffd0c01f

def z1165 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x27ff7f8407ff0c03 0xf93ffbfc203ff860

def z1166 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xea4c7ce4f8000000 0x075263e727c00000

def z1167 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x320c8c63c4e1c188 0x219064631e270e0c

def z1168 : W := mkw 0x2208042280204101 0x1110402114010208 0xbb8f8c63c461c18d 0x3ddc7c631e230e0c

def z1169 : W := mkw 0x885210004fd70622 0x04429080027eb831 0x00000000039f0e76 0xe8000000001cf873

def z1170 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x03ef7f8007fe0001 0xb81f7bfc003ff000

def z1171 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfdfff07f2701ffff 0xffefff83f9380fff

def z1172 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffc00c008 0x17ffffffffe00600

def z1173 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7ffff3fc079ffc1f 0xfbffff9fe03cffe0

def z1174 : W := mkw 0x11040109200810c8 0x8888200849004086 0xcdb1031b221833f7 0xce6d8818d910c19f

def z1175 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07c07f8001fe0003 0x803e03fc000ff000

def z1176 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xff9f8ce3fce7c3ff 0xfffcfc671fe73e1f

def z1177 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff8180062 0x07fffbffffc0c003

def z1178 : W := mkw 0x0000000000000000 0x0000000000000000 0xbb8f8c6304e1c38d 0xbddc7c6318270e1c

def z1179 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7c7ff0fc3f01fc1c 0x7be3ff87e1f80fe0

def z1180 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007fe0002 0x603ffbfc003ff000

def z1181 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xec70739cf8000000 0x0763839ce7c00000

def z1182 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfdf373fff8000000 0x07ef9b9fffc00000

def z1183 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8c63fce1c3ed 0xbddc7c631fe70e1f

def z1184 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9860000 0x27fffbffffcc3000

def z1185 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb808c63c4e1c38d 0xbddc04631e270e1c

def z1186 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x012a7f0006fe0003 0x900953f80037f000

def z1187 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x87a07f9bf8000000 0x043d03fcdfc00000

def z1188 : W := mkw 0xe83a10004fa3ef21 0x0741d080027d1f79 0x0000800007e7ffff 0xf8000400003f3fff

def z1189 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x057a7f8007fe0003 0xf82bd3fc003ff000

def z1190 : W := mkw 0x2208042280204101 0x1110402114010208 0x17df8ce305e6c18b 0xf8befc67182f360c

def z1191 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xfffffffff801cc00 0x07ffffffffc00e60

def z1192 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x7b7f7fffd8000000 0x03dbfbfffec00000

def z1193 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x227f7ce4d8000000 0x0113fbe726c00000

def z1194 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xba4c7ce7d8000000 0x05d263e73ec00000

def z1195 : W := mkw 0x0812000048830620 0x0040900002441831 0xfed5009cf9873e7e 0xeff6a804e7cc39f3

def z1196 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007fe038f 0xf83ffbfc003ff01c

def z1197 : W := mkw 0x0100215d20000018 0x2808010ae9000000 0xffff73fff8000000 0x07fffb9fffc00000

def z1198 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff8003188 0x07fffbffffc0018c

def z1199 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0x0000000003873e76 0xe8000000001c39f3

def z1200 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfbcf7cfff8000000 0x07de7be7ffc00000

def z1201 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8ce3dce7c38d 0xbddc7c671ee73e1c

def z1202 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xbbef7fffd8000000 0x05df7bfffec00000

def z1203 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xfffffffffc61c18d 0x3fffffffffe30e0c

def z1204 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8c63c4e7c3ef 0xbddc7c631e273e1f

def z1205 : W := mkw 0x0812000048830620 0x0040900002441831 0xeef5009cfb873e76 0xef77a804e7dc39f3

def z1206 : W := mkw 0xc02010000700a800 0x0601008000380540 0xeed58084ff01fc1c 0x7f76ac0427f80fe0

def z1207 : W := mkw 0x04004a8000000000 0x0020025400000000 0x87ff7f80f8000000 0x043ffbfc07c00000

def z1208 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x204070e4d8000000 0x0102038726c00000

def z1209 : W := mkw 0x27886fffb020411d 0x393c437ffd810208 0xffff7ffff8600181 0x07fffbffffc3000c

def z1210 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbfdf8ce7dde7cf8f 0xfdfefc673eef3e7c

def z1211 : W := mkw 0x2208042280204101 0x1110402114010208 0x112a8c7b0660f189 0x10895463d833078c

def z1212 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x784cf07c0701fc1c 0x7bc26783e0380fe0

def z1213 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xeefd7ffcf8000000 0x0777ebffe7c00000

def z1214 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffc600001 0x17fffbffffe30000

def z1215 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x06fd7f8007fe0002 0xe837ebfc003ff000

def z1216 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xd7fa7ffff8000000 0x06bfd3ffffc00000

def z1217 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x784ff07c0501fc1c 0x3bc27f83e0280fe0

def z1218 : W := mkw 0x0000000000000000 0x0000000000000000 0xeeff7084f8000000 0x0777fb8427c00000

def z1219 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000002 0xcffffbffffc00000

def z1220 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x02407c84d8000000 0x001203e426c00000

def z1221 : W := mkw 0x04404a8000540002 0x002202540002a000 0x07ff7f8001fe0003 0xe83ffbfc000ff000

def z1222 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x306ef07c0701fc1c 0x79837783e0380fe0

def z1223 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7c7ff37c0719fc1e 0x7be3ff9be038cfe0

def z1224 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff80003e0 0x07fffbffffc0001f

def z1225 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0x97aa7ffbfa1833eb 0x94bd53ffdfd0c19f

def z1226 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xefdd7fe7f8000000 0x077eebff3fc00000

def z1227 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xa38c8c63c4e1c38d 0xbd1c64631e270e1c

def z1228 : W := mkw 0x11040109200810c8 0x8888200849004086 0xc430031b221833f2 0x46218018d910c19f

def z1229 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x507af07c0701fc1c 0x7a83d783e0380fe0

def z1230 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x797ffc7c0761fc1d 0x7bcbffe3e03b0fe0

def z1231 : W := mkw 0x0812000048830620 0x0040900002441831 0xee540084f9870e76 0x6772a00427cc3873

def z1232 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x312a7f7fd8000000 0x018953fbfec00000

def z1233 : W := mkw 0xd93611096f8bbee8 0x8ec9b0884b7c5df7 0xddb3831b279fffff 0xfeed9c18d93cffff

def z1234 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff80003ff 0xdffffbffffc0001f

def z1235 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffce0038d 0xbffffbffffe7001c

def z1236 : W := mkw 0x11040109200810c8 0x8888200849004086 0x95a2031b221833ff 0xdcad1018d910c19f

def z1237 : W := mkw 0x0812000048830620 0x0040900002441831 0xfff7039cfb9f3e7f 0xffffb81ce7dcf9f3

def z1238 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xbb8f8c67dce1cf8d 0xbddc7c633ee70e7c

def z1239 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000262 0x87fffbffffc00013

def z1240 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x224c7ce4d9010c00 0x211263e726c80860

def z1241 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xbfcf7fe7f8000000 0x05fe7bff3fc00000

def z1242 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd5b2031b221833fb 0xd6ad9018d910c19f

def z1243 : W := mkw 0x04004a8000000000 0x0020025400000000 0x224c7c84d8000000 0x011263e426c00000

def z1244 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x07ffff8007ffcc03 0xf83ffffc003ffe60

def z1245 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0x000080000787fc1c 0x78000400003c3fe0

def z1246 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbaf8c7bc6e1f38d 0xbddd7c63de370f9c

def z1247 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xffdf7ce7f8000000 0x07fefbe73fc00000

def z1248 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff80033fe 0xcffffbffffc0019f

def z1249 : W := mkw 0x2208042280204101 0x1110402114010208 0x110a8c630461c18d 0x3888546318230e0c

def z1250 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfb6e7ffff8000000 0x07db73ffffc00000

def z1251 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x27ff7f84dffe0003 0xf93ffbfc26fff000

def z1252 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x26dd7ce4d9860002 0xe936ebe726cc3000

def z1253 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9870e62 0xa776a80427cc3873

def z1254 : W := mkw 0x0802000008020420 0x0040100000401021 0xeed50084f9070c76 0x6f76a80427c83863

def z1255 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7c7ff07c2701fc7e 0x7be3ff83e1380fe3

def z1256 : W := mkw 0x0812000048830620 0x0040900002441831 0xeec40084f9870e76 0xa776200427cc3873

def z1257 : W := mkw 0x04004a8000000000 0x0020025400000000 0xefff7f84fa180277 0xdf7ffbfc27d0c013

def z1258 : W := mkw 0x11040109200810c8 0x8888200849004086 0x9122031b221833e9 0x14891018d910c19f

def z1259 : W := mkw 0x0812000048830620 0x0040900002441831 0xfedf00e4f9870e76 0xeff6f80727cc3873

def z1260 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x786ef07c0701fc1c 0x33c37783e0380fe0

def z1261 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ee7f8007fe0003 0xb03f73fc003ff000

def z1262 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd9a3031b221833fd 0x9ecd1818d910c19f

def z1263 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9870c72 0x6776a80427cc3863

def z1264 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c6f9c38f 0xfddc7c631e37ce1c

def z1265 : W := mkw 0x0812000048830620 0x0040900002441831 0xeedd0c84fde70e76 0xef76e86427ef3873

def z1266 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfefff0fcff87fc1e 0xfff7ff87e7fc3fe0

def z1267 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x27cc7fe4d8000000 0x013e63ff26c00000

def z1268 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xafff7f80c7fe0003 0xfd7ffbfc063ff000

def z1269 : W := mkw 0x0812000048830620 0x0040900002441831 0xeedd80e4fd87ce76 0xef76ec0727ec3e73

def z1270 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8c8c63c4e1c38d 0xa5dc64631e270e1c

def z1271 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x87ff7f80fffe0003 0xfc3ffbfc07fff000

def z1272 : W := mkw 0x15846bdd300810dc 0xa8ac235ee9804086 0xeef5739cfa183276 0xcf77ab9ce7d0c193

def z1273 : W := mkw 0x2208042280204101 0x1110402114010208 0x330e8c63c460c189 0x119874631e23060c

def z1274 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xfbff7c7ff8000000 0x07dffbe3ffc00000

def z1275 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xfffffffff901fc1c 0x6fffffffffc80fe0

def z1276 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xf87ff07c2701fe7c 0x7fc3ff83e1380ff3

def z1277 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffff8e60000 0x07fffbffffc73000

def z1278 : W := mkw 0x0802000008020420 0x0040100000401021 0xc6d00084f9060c72 0x4636800427c83063

def z1279 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfedd7cfff8000000 0x07f6ebe7ffc00000

def z1280 : W := mkw 0x11040109200810c8 0x8888200849004086 0x85a0031b221833e3 0x842d0018d910c19f

def z1281 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa180002 0x47fffbffffd0c000

def z1282 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9010e76 0xeffffbffffc80873

def z1283 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0x336e7fffda183189 0x119b73fffed0c18c

def z1284 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddff731b221833ff 0xdeeffb98d910c19f

def z1285 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7873f07c0301fc1c 0x5bc39f83e0180fe0

def z1286 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffbf8f7bc6f9f39f 0xfffdfc7bde37cf9c

def z1287 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdbf037b221833ff 0xdfedf81bd910c19f

def z1288 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x787ff07c071ffc1e 0x7bc3ff83e038ffe0

def z1289 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddbb837b2618f3ff 0xdeeddc1bd930c79f

def z1290 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7840f07c0101fc1c 0x03c20783e0080fe0

def z1291 : W := mkw 0x2208042280204101 0x1110402114010208 0x998b8c630460c189 0x14cc5c631823060c

def z1292 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xf9fff07f0701fc1c 0x7fcfff83f8380fe0

def z1293 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xffdf8ce7fce7c3ef 0xbffefc673fe73e1f

def z1294 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8860002 0x87fffbffffc43000

def z1295 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000001 0x9ffffbffffc00000

def z1296 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x224c7ce4d9860000 0x211263e726cc3000

def z1297 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8006fe0003 0x903ffbfc0037f000

def z1298 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffc000000 0x3ffffbffffe00000

def z1299 : W := mkw 0x0812000048830620 0x0040900002441831 0xe6d40084f9870e72 0xe736a00427cc3873

def z1300 : W := mkw 0x17c46fffb05c10de 0xb8be237ffd82e086 0xffff7ffff8fe03e3 0x87fffbffffc7f01f

def z1301 : W := mkw 0x402020540000a810 0x22010102a0000540 0x7870f07c0001fc1c 0x03c38783e0000fe0

def z1302 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xbfff7fe7d8000000 0x05fffbff3ec00000

def z1303 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffffef833ff 0xfffffbfffff7c19f

def z1304 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xc7f07f9ffa1833f3 0xc63f83fcffd0c19f

def z1305 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000204 0x8ffffbffffc00010

def z1306 : W := mkw 0x0812000048830620 0x0040900002441831 0xfed50087f9870ffe 0xeff6a8043fcc387f

def z1307 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffc01c000 0x27ffffffffe00e00

def z1308 : W := mkw 0x0812000048830620 0x0040900002441831 0xeedf0084fd870e76 0xff76f80427ec3873

def z1309 : W := mkw 0x0000205400000010 0x20000102a0000000 0x224c70e4d8000000 0x0112638726c00000

def z1310 : W := mkw 0x0812000048830620 0x0040900002441831 0xc6d00084f9870e76 0xee36800427cc3873

def z1311 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfffffffffd01cc1c 0x7fffffffffe80e60

def z1312 : W := mkw 0x0c124a8048830620 0x0060925402441831 0x07ff7f8001870e76 0xe83ffbfc000c3873

def z1313 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7fffff7c07f9fc1f 0xfbfffffbe03fcfe0

def z1314 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8005fe0003 0xa03ffbfc002ff000

def z1315 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x06707f8003fe0002 0x403383fc001ff000

def z1316 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x330e8c63c4e1c38d 0xb99874631e270e1c

def z1317 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x077e7f8007fe0003 0x703bf3fc003ff000

def z1318 : W := mkw 0x11040109200810c8 0x8888200849004086 0xd922031b221833ff 0xdec91018d910c19f

def z1319 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0601fc1c 0x13c3ff83e0300fe0

def z1320 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xdfff7f9b07fe339f 0xfefffbfcd83ff19c

def z1321 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x017f7f0007fe0003 0xf80bfbf8003ff000

def z1322 : W := mkw 0x0812000048830620 0x0040900002441831 0xc6d50084f9860e72 0xee36a80427cc3073

def z1323 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff81833ff 0x87fffbffffc0c19f

def z1324 : W := mkw 0x2208042280204101 0x1110402114010208 0xffdf8ce7fc60c189 0x17fefc673fe3060c

def z1325 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0x667c7ffcfa183072 0x4333e3ffe7d0c183

def z1326 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xa7ff7fe7f8000000 0x053ffbff3fc00000

def z1327 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff80033fd 0x9ffffbffffc0019f

def z1328 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdcb1031b221833fe 0xcee58818d910c19f

def z1329 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9870c16 0xeffffbffffcc3860

def z1330 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xdff37f9ff8000000 0x06ff9bfcffc00000

def z1331 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x604cf07c0501fc10 0x23026783e0280fe0

def z1332 : W := mkw 0x0812000048830620 0x0040900002441831 0x26440084f9870c62 0x2132200427cc3863

def z1333 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x102af0780701fc08 0x30815783c0380fe0

def z1334 : W := mkw 0x378c6fffb02851dd 0xb9bc637ffd81428e 0xfffffffffe78f189 0x17fffffffff3c78c

def z1335 : W := mkw 0x0812000048830620 0x0040900002441831 0xec550084f9070e76 0x6f62a80427c83873

def z1336 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x687df07c0701fc14 0x6b43ef83e0380fe0

def z1337 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfe7c7ffff8000000 0x07f3e3ffffc00000

def z1338 : W := mkw 0x0812000048830620 0x0040900002441831 0xefdf0c84f9870e76 0xef7ef86427cc3873

def z1339 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07bb7f8006fe0003 0xd83ddbfc0037f000

def z1340 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x5fffff9807fffc1f 0xfafffffcc03fffe0

def z1341 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbfbf8f63c4e1c38d 0xbdfdfc7b1e270e1c

def z1342 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xfbff7cffd8000000 0x07dffbe7fec00000

def z1343 : W := mkw 0x07804fabb000000c 0x183c027d5d800000 0xefff7f87f8000000 0x077ffbfc3fc00000

def z1344 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfff7039ffb193fff 0xffffb81cffd8c9ff

def z1345 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa180001 0x17fffbffffd0c000

def z1346 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x3a4ffce4dc01c00c 0x39d27fe726e00e00

def z1347 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed00084f9870e76 0xc776800427cc3873

def z1348 : W := mkw 0x0812000048830620 0x0040900002441831 0xfff70387fb9f0fff 0xffffb81c3fdcf87f

def z1349 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xf90a8c67fc61cffd 0x17c854633fe30e7f

def z1350 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfdb3031f22193fff 0xdfed9818f910c9ff

def z1351 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffa000000 0x5ffffbffffd00000

def z1352 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xefdf8c84fde7cfff 0xff7efc6427ef3e7f

def z1353 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x7e7f7ffcf8000000 0x03f3fbffe7c00000

def z1354 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8003fe0003 0xc03ffbfc001ff000

def z1355 : W := mkw 0xa85a10004ff74723 0x0542d080027fba39 0x0000800007ffcfff 0xf8000400003ffe7f

def z1356 : W := mkw 0x0812000048830620 0x0040900002441831 0xefd50384f99f0e77 0xef7ea81c27ccf873

def z1357 : W := mkw 0x0812000048830620 0x0040900002441831 0xc4500084f9060e72 0x4622800427c83073

def z1358 : W := mkw 0x04004a8000000000 0x0020025400000000 0x27ff7f84d8000000 0x013ffbfc26c00000

def z1359 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffbf8f63e6f9c3ff 0xfffdfc7b1f37ce1f

def z1360 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x132a7ffbd8000000 0x009953ffdec00000

def z1361 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed50084f9860e72 0xc776a80427cc3073

def z1362 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xefff7fe4f8000000 0x077ffbff27c00000

def z1363 : W := mkw 0x11040109200810c8 0x8888200849004086 0x15b3031b021833ff 0xd8ad9818d810c19f

def z1364 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0787fc1e 0xfbc3ff83e03c3fe0

def z1365 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07ff7f8007fe0277 0xf83ffbfc003ff013

def z1366 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff8000381 0x87fffbffffc0001c

def z1367 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xbfffffe307ffc38f 0xfdffffff183ffe1c

def z1368 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xf84c707ff8000000 0x07c26383ffc00000

def z1369 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x797ff37c0719fc1d 0x7bcbff9be038cfe0

def z1370 : W := mkw 0x881210004f830620 0x04409080027c1831 0x0000000007870e76 0xf8000000003c3873

def z1371 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x9fff7f8307fe0003 0xfcfffbfc183ff000

def z1372 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x707ef07c0701fc18 0x7383f783e0380fe0

def z1373 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x17ff7f8307fe018b 0xf8bffbfc183ff00c

def z1374 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x7dfff37c07fffc1f 0xfbefff9be03fffe0

def z1375 : W := mkw 0x11040109200810c8 0x8888200849004086 0xfff7039f239f3fff 0xffffb81cf91cf9ff

def z1376 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xefff7f9cf8000000 0x077ffbfce7c00000

def z1377 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0xefff7f8427ff0e77 0xff7ffbfc213ff873

def z1378 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x3fffffe007fffc1f 0xf9ffffff003fffe0

def z1379 : W := mkw 0x281a000048a34721 0x0140d00002451a39 0xeed58084f987cffe 0xef76ac0427cc3e7f

def z1380 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x785df07c0501fc1c 0x6bc2ef83e0280fe0

def z1381 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffaa7ffff8000000 0x07fd53ffffc00000

def z1382 : W := mkw 0x06c06ef690540016 0x30360377b482a000 0x224c7ce4d8e60000 0x011263e726c73000

def z1383 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfef573fff8000000 0x07f7ab9fffc00000

def z1384 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0719fc1f 0xfbc3ff83e038cfe0

def z1385 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0x978a8ce3fce6c3eb 0x94bc54671fe7361f

def z1386 : W := mkw 0x0812000048830620 0x0040900002441831 0xfed580e4f987ce7e 0xeff6ac0727cc3e73

def z1387 : W := mkw 0x47a06fffb000a81c 0x3a3d037ffd800540 0xfffffffff800f008 0x07ffffffffc00780

def z1388 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x6070f07c0301fc10 0x43038783e0180fe0

def z1389 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x783bf07c0601fc1c 0x5bc1df83e0300fe0

def z1390 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7808f07c0401fc1c 0x03c04783e0200fe0

def z1391 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x067c7f8007fe0003 0xf833e3fc003ff000

def z1392 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xfc7073fffa1833fe 0x47e3839fffd0c19f

def z1393 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x7ffffff807fff01f 0xfbffffffc03fff80

def z1394 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07aa7f8007fe0003 0xf83d53fc003ff000

def z1395 : W := mkw 0x0812000048830620 0x0040900002441831 0xfff7009ffb873fff 0xffffb804ffdc39ff

def z1396 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0701fc10 0x63c3ff83e0380fe0

def z1397 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8ce7fde1cf9d 0xfffefc673fef0e7c

def z1398 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x87887fe3f8000000 0x043c43ff1fc00000

def z1399 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0701ff9d 0xfbc3ff83e0380ffc

def z1400 : W := mkw 0x0812000048830620 0x0040900002441831 0xefff0f84ffff0e77 0xff7ff87c27fff873

def z1401 : W := mkw 0x06806ef690000014 0x30340377b4800000 0x224cfce4dc01c000 0x211267e726e00e00

def z1402 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c5e1cf9d 0xfddc7c631e2f0e7c

def z1403 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xfa4c7cfff80033fc 0x07d263e7ffc0019f

def z1404 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdc33031b221833fe 0x5ee19818d910c19f

def z1405 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfb8f8c7bc4e1f39d 0xbfdc7c63de270f9c

def z1406 : W := mkw 0x06806ef690000014 0x30340377b4800000 0xfeff7cfcf8000000 0x07f7fbe7e7c00000

def z1407 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9860276 0xeffffbffffcc3013

def z1408 : W := mkw 0xc87210004fd7ae22 0x06439080027ebd71 0x0000800007fffe7f 0xf8000400003ffff3

def z1409 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x7efff0fc07fffc1f 0xfbf7ff87e03fffe0

def z1410 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x7fffffe407ffcc1f 0xfbffffff203ffe60

def z1411 : W := mkw 0x04806ad410000014 0x20240356a0800000 0xeed57084f8000000 0x0776ab8427c00000

def z1412 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x607ff07c0701fc10 0x7b03ff83e0380fe0

def z1413 : W := mkw 0x0812000048830620 0x0040900002441831 0xfed70084f9870e7e 0xfff6b80427cc3873

def z1414 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787cf07c0701fc1c 0x63c3e783e0380fe0

def z1415 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x234c7fe7d8000000 0x011a63ff3ec00000

def z1416 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x064c7f8005fe0002 0x203263fc002ff000

def z1417 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x782af07c0701fc1c 0x7bc15783e0380fe0

def z1418 : W := mkw 0x0812000048830620 0x0040900002441831 0xeed58084fd87ce7e 0xff76ac0427ec3e73

def z1419 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x110a8c6304e0c389 0x908854631827061c

def z1420 : W := mkw 0x0812000048830620 0x0040900002441831 0xeef70084fb870e76 0xff77b80427dc3873

def z1421 : W := mkw 0xc4605a800754a802 0x062302d4003aa540 0x07ffff8007fef00b 0xf83ffffc003ff780

def z1422 : W := mkw 0x2208042280204101 0x1110402114010208 0x112a8f630678c189 0x1089547b1833c60c

def z1423 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xfff07ffff8000000 0x07ff83ffffc00000

def z1424 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c4e0c389 0x95dc7c631e27061c

def z1425 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x787ff07c0501fc1c 0x23c3ff83e0280fe0

def z1426 : W := mkw 0x05806bdd3000001c 0x282c035ee9800000 0xc6f0739cf8000000 0x0637839ce7c00000

def z1427 : W := mkw 0x0280247690000014 0x30140123b4800000 0x787f707cd8000000 0x03c3fb83e6c00000

def z1428 : W := mkw 0x2a1a0422c8a34721 0x1150d02116451a39 0xffff8fe7ffffcfff 0xfffffc7f3ffffe7f

def z1429 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xf92a7f7ffa1833fd 0x17c953fbffd0c19f

def z1430 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x9b8b8c63c4e0c38d 0x9cdc5c631e27061c

def z1431 : W := mkw 0x11040109200810c8 0x8888200849004086 0xffbf8f7b26f9f3ff 0xfffdfc7bd937cf9f

def z1432 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbfff8fe3c7ffc38f 0xfdfffc7f1e3ffe1c

def z1433 : W := mkw 0x11040109200810c8 0x8888200849004086 0x5933031b021833ff 0xdac99818d810c19f

def z1434 : W := mkw 0x15044b89200810c8 0x88a8225c49004086 0xffff7f9ffa1833ff 0xdffffbfcffd0c19f

def z1435 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x03af7f0007fe0003 0xf81d7bf8003ff000

def z1436 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffff9060002 0x47fffbffffc83000

def z1437 : W := mkw 0x11040109200810c8 0x8888200849004086 0xdd80031b221833ff 0xdeec0018d910c19f

def z1438 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x607cf07c0701fc1c 0x7b03e783e0380fe0

def z1439 : W := mkw 0x2208042280204101 0x1110402114010208 0x15bb8f630678c18b 0xd8addc7b1833c60c

def z1440 : W := mkw 0x0812000048830620 0x0040900002441831 0xea550084f9870e74 0x6f52a80427cc3873

def z1441 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0x83888c63c4e0c381 0x841c44631e27061c

def z1442 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xffdf8ce3e5e7c3ff 0xfffefc671f2f3e1f

def z1443 : W := mkw 0xc06030540754a812 0x26030182a03aa540 0x7bfffc7c07fffc1f 0xfbdfffe3e03fffe0

def z1444 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x87ff7f8307fe0383 0xfc3ffbfc183ff01c

def z1445 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff8180181 0x07fffbffffc0c00c

def z1446 : W := mkw 0x2208042280204101 0x1110402114010208 0x390f8c630460c189 0x11c87c631823060c

def z1447 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddb3031b26f833ff 0xfeed9818d937c19f

def z1448 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xfafff07cc701fc1c 0x7fd7ff83e6380fe0

def z1449 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07af7f8006fe0003 0xb83d7bfc0037f000

def z1450 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfbbf8c7bc4e1c38d 0xbfddfc63de270e1c

def z1451 : W := mkw 0x0812000048830620 0x0040900002441831 0xced10084f9860e76 0xce76880427cc3073

def z1452 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0xffff7ffffef80003 0xfffffbfffff7c000

def z1453 : W := mkw 0x0812000048830620 0x0040900002441831 0xffdf80e7fd87cfff 0xfffefc073fec3e7f

def z1454 : W := mkw 0x0812000048830620 0x0040900002441831 0xeac50084f9870e74 0xaf56280427cc3873

def z1455 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x07f37f8003fe0003 0xd83f9bfc001ff000

def z1456 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x17ff7f9807fe300b 0xf8bffbfcc03ff180

def z1457 : W := mkw 0x11040109200810c8 0x8888200849004086 0xddf3031f23183fff 0xdeef9818f918c1ff

def z1458 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xa38f8c63c4e1c381 0xbd1c7c631e270e1c

def z1459 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xdff37f9ffa1833ff 0xdeff9bfcffd0c19f

def z1460 : W := mkw 0xc02030540700a810 0x26010182a0380540 0x7a7ff0fc0787fc1c 0x7bd3ff87e03c3fe0

def z1461 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbaf8f63c6f9c38d 0xbddd7c7b1e37ce1c

def z1462 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbbcf8ce3c5e7c38d 0xbdde7c671e2f3e1c

def z1463 : W := mkw 0x07806fffb000001c 0x383c037ffd800000 0x324c7cffd8000000 0x019263e7fec00000

def z1464 : W := mkw 0x0380257fb000001c 0x381c012bfd800000 0xfdff737ff8000000 0x07effb9bffc00000

def z1465 : W := mkw 0x2208042280204101 0x1110402114010208 0x9b8f8c6304e0c38d 0xbcdc7c631827061c

def z1466 : W := mkw 0x0000205400000010 0x20000102a0000000 0xf87f707cf8000000 0x07c3fb83e7c00000

def z1467 : W := mkw 0x84405a8007540002 0x042202d4003aa000 0x47ff7f9807fe3013 0xfa3ffbfcc03ff180

def z1468 : W := mkw 0xc83210004f83ae20 0x06419080027c1d71 0x000080000587cc00 0x20000400002c3e60

def z1469 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xbb8f8c63c6e1f39d 0xfddc7c631e370f9c

def z1470 : W := mkw 0xc02030540700a810 0x26010182a0380540 0xf87ff07f0701ff9c 0x7fc3ff83f8380ffc

def z1471 : W := mkw 0x07c06fffb054001e 0x383e037ffd82a000 0xffff7ffff9fe0003 0xeffffbffffcff000

def z1472 : W := mkw 0x17846fffb00810dc 0xb8bc237ffd804086 0xffff7ffff81803ef 0x9ffffbffffc0c01f

def z1473 : W := mkw 0x22180422c0a14301 0x1110c02116050a18 0xfb8f8c63e4e1c3fd 0xbfdc7c631f270e1f

def z1474 : W := mkw 0x11040109200810c8 0x8888200849004086 0xc5b3031b221833f3 0xde2d9818d910c19f

def z1475 : W := mkw 0x87c05fabb754000e 0x1c3e02fd5dbaa000 0x87800f83fffe0003 0xfc3c007c1ffff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z2,z4,z5,z6]),(0,[z8,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z11,z6]),(0,[z0,z1,z2,z12,z4,z5,z6])],[(0,[z13,z0,z14,z2,z4,z5,z6]),(0,[z15,z1,z2,z16,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z18,z6]),(0,[z0,z1,z2,z4,z19,z20,z5]),(0,[z0,z1,z2,z21,z4,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z6]),(1,[z1,z2,z23,z4,z5,z6])],[(0,[z24,z1,z2,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z26,z5,z6]),(0,[z0,z1,z2,z4,z5,z27,z28]),(0,[z0,z1,z2,z29,z5,z30,z6]),(0,[z0,z1,z2,z4,z5,z31,z28]),(1,[z0,z1,z2,z32,z5,z6]),(0,[z0,z33,z1,z2,z34,z5,z6]),(0,[z0,z1,z35,z2,z36,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z38,z5,z6]),(0,[z0,z39,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z40,z6,z31]),(0,[z0,z1,z2,z4,z41,z5,z6])],[(0,[z0,z42,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z43,z4,z5,z6]),(0,[z44,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z45,z6]),(1,[z46,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z40,z6]),(0,[z48,z0,z1,z49,z4,z5,z6]),(0,[z0,z1,z2,z50,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z5,z31])],[(0,[z52,z0,z1,z2,z4,z5,z6]),(0,[z53,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z6,z31]),(0,[z54,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z55,z6,z31])],[(0,[z1,z2,z16,z4,z5,z56,z6]),(0,[z57,z0,z1,z2,z4,z5,z6]),(1,[z58,z1,z2,z4,z5,z6]),(0,[z0,z1,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z60])],[(1,[z0,z1,z61,z4,z5,z6]),(0,[z62,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z63,z5,z6]),(0,[z0,z64,z1,z43,z4,z5,z6]),(0,[z0,z65,z1,z2,z4,z5,z6])],[(0,[z25,z1,z2,z4,z5,z66,z6]),(0,[z67,z0,z1,z2,z4,z26,z5]),(0,[z68,z0,z1,z2,z4,z5,z6]),(0,[z69,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z70,z5,z6]),(0,[z71,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z13,z72,z1,z2,z4,z5,z6]),(0,[z67,z1,z73,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z6]),(0,[z74,z0,z2,z43,z4,z5,z6]),(0,[z0,z75,z1,z2,z4,z5,z6]),(1,[z0,z2,z29,z5,z76,z6]),(0,[z0,z1,z2,z21,z5,z77,z6]),(0,[z0,z1,z2,z4,z76,z6,z31]),(1,[z0,z1,z2,z4,z78,z6])],[(0,[z0,z1,z2,z4,z5,z76,z6])],[(0,[z72,z0,z14,z2,z4,z5,z6]),(0,[z79,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z80,z6]),(0,[z1,z2,z4,z5,z81,z76,z6]),(0,[z0,z1,z82,z2,z4,z5,z30])],[(0,[z0,z1,z2,z83,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z84,z6]),(0,[z85,z0,z1,z2,z4,z5,z6]),(0,[z67,z1,z2,z4,z5,z86,z6]),(1,[z0,z1,z87,z4,z5,z6]),(0,[z0,z88,z1,z2,z4,z5,z6]),(0,[z0,z1,z89,z2,z4,z5,z6])],[(0,[z0,z90,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z91,z6]),(0,[z0,z1,z2,z4,z5,z56,z30]),(0,[z92,z0,z1,z2,z36,z5,z6]),(0,[z93,z1,z2,z4,z26,z5,z6]),(0,[z0,z1,z94,z2,z4,z5,z6])],[(0,[z95,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z96,z2,z4,z5,z6]),(1,[z25,z1,z16,z4,z5,z6]),(0,[z97,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z98,z6]),(0,[z0,z1,z2,z4,z5,z99,z6]),(0,[z100,z1,z2,z4,z5,z18,z6]),(0,[z101,z0,z1,z2,z102,z5,z6])],[(0,[z13,z0,z103,z2,z4,z5,z6]),(0,[z1,z2,z16,z4,z70,z5,z6]),(0,[z104,z25,z1,z2,z4,z5,z6]),(0,[z25,z0,z1,z105,z4,z5,z6]),(0,[z106,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z107,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z108,z5,z6]),(1,[z0,z109,z2,z4,z5,z6]),(0,[z0,z1,z2,z110,z4,z5,z6]),(0,[z111,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z112,z6]),(0,[z0,z1,z2,z4,z113,z5,z6]),(1,[z25,z1,z2,z4,z5,z6]),(0,[z114,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z86,z6,z115]),(1,[z116,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z117,z6]),(0,[z118,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z100,z1,z2,z119,z4,z5,z6]),(1,[z120,z1,z2,z4,z5,z6]),(0,[z104,z121,z1,z2,z4,z5,z6])],[(0,[z0,z103,z1,z2,z4,z5,z6]),(0,[z0,z1,z73,z2,z4,z5,z6]),(1,[z72,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z122,z6]),(0,[z101,z0,z1,z2,z4,z5,z56]),(1,[z121,z1,z2,z4,z5,z6])],[(0,[z22,z1,z2,z16,z4,z5,z6]),(0,[z67,z0,z1,z2,z4,z5,z27]),(0,[z0,z1,z2,z4,z5,z6,z123]),(0,[z124,z0,z14,z2,z4,z5,z6]),(0,[z0,z1,z2,z108,z4,z5,z6])],[(0,[z47,z25,z1,z2,z4,z5,z6]),(1,[z97,z1,z2,z125,z5,z6]),(0,[z100,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z4,z5,z6,z126]),(0,[z0,z2,z4,z5,z56,z6,z28]),(0,[z0,z1,z2,z127,z4,z5,z6]),(0,[z128,z0,z1,z2,z4,z5,z6]),(0,[z129,z0,z1,z2,z4,z5,z6])],[(0,[z130,z0,z1,z2,z4,z5,z6]),(1,[z17,z1,z2,z4,z18,z6]),(0,[z131,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z132,z4,z5,z6,z133]),(0,[z0,z1,z2,z4,z26,z5,z56]),(0,[z0,z1,z134,z2,z4,z5,z6])],[(0,[z0,z1,z2,z135,z4,z5,z6]),(0,[z0,z1,z2,z4,z136,z5,z6])],[(1,[z137,z1,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z26,z51,z5])],[(0,[z72,z0,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z138,z5,z6]),(1,[z0,z2,z29,z5,z6,z28]),(0,[z22,z0,z1,z2,z4,z139,z6]),(1,[z0,z1,z2,z140,z5,z6]),(0,[z0,z1,z141,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z26,z5,z142]),(0,[z143,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z144,z6]),(0,[z0,z1,z2,z145,z4,z5,z6]),(0,[z0,z1,z146,z2,z4,z5,z6]),(1,[z0,z1,z2,z147,z5,z6]),(1,[z0,z1,z2,z4,z5,z148]),(0,[z0,z1,z2,z29,z5,z76,z6]),(0,[z0,z1,z2,z4,z5,z6,z28]),(0,[z0,z1,z37,z2,z4,z139,z6])],[(0,[z74,z1,z2,z16,z4,z5,z6]),(0,[z1,z82,z2,z16,z4,z5,z6]),(0,[z97,z0,z1,z2,z125,z5,z6]),(0,[z15,z0,z1,z2,z4,z26,z5]),(0,[z0,z1,z2,z149,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z5,z6]),(0,[z22,z0,z1,z2,z151,z5,z6])],[(0,[z152,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z16,z21,z5,z6]),(0,[z0,z1,z2,z4,z70,z40,z6]),(0,[z48,z0,z1,z153,z4,z5,z6]),(0,[z0,z1,z2,z4,z154,z5,z6])],[(0,[z25,z14,z1,z2,z4,z5,z6]),(0,[z0,z1,z105,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z155]),(0,[z0,z33,z1,z2,z4,z5,z28]),(0,[z0,z1,z2,z156,z4,z5,z6])],[(0,[z14,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z157,z6]),(0,[z17,z0,z1,z2,z4,z6,z31]),(1,[z0,z14,z2,z21,z5,z6]),(0,[z158,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z159,z5,z6]),(0,[z92,z0,z160,z2,z4,z5,z6]),(0,[z0,z1,z2,z36,z5,z161,z6]),(0,[z0,z1,z2,z162,z4,z5,z6])],[(0,[z9,z1,z2,z16,z4,z5,z6]),(1,[z0,z1,z2,z4,z163,z6]),(0,[z0,z1,z2,z4,z5,z6,z164]),(0,[z0,z165,z1,z2,z29,z5,z6]),(0,[z101,z0,z1,z2,z21,z5,z6]),(0,[z166,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z167,z6])],[(0,[z0,z1,z2,z4,z5,z6,z168]),(0,[z0,z1,z2,z16,z29,z5,z6]),(0,[z169,z25,z1,z2,z4,z5,z6]),(0,[z170,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z171,z21,z5,z6]),(1,[z0,z1,z2,z172,z5,z6]),(0,[z0,z1,z2,z4,z5,z173,z6]),(0,[z101,z0,z1,z2,z4,z174,z6]),(0,[z0,z1,z109,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z175,z5,z6])],[(0,[z176,z0,z1,z2,z4,z5,z6]),(0,[z0,z177,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z178,z4,z5,z6]),(0,[z0,z1,z105,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z179,z6]),(1,[z180,z1,z2,z4,z5,z6])]],
   [[(0,[z13,z0,z1,z2,z21,z5,z6]),(0,[z25,z1,z35,z2,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z161,z6])],[(0,[z181,z17,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z2,z4,z29,z5,z76,z6]),(1,[z1,z2,z21,z159,z5,z6]),(0,[z182,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z183,z5,z6]),(0,[z181,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z184,z29,z5,z6]),(0,[z185,z0,z1,z2,z21,z5,z6]),(0,[z101,z0,z33,z2,z4,z5,z6]),(1,[z186,z1,z2,z4,z5,z6])],[(0,[z187,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z156,z178,z5,z6])],[(0,[z13,z0,z1,z2,z29,z5,z6]),(0,[z188,z0,z1,z2,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z5,z27]),(1,[z104,z0,z1,z4,z5,z133])],[(0,[z22,z0,z189,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z190,z6])],[(0,[z1,z2,z191,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z192,z5,z6]),(0,[z181,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z193,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z76,z6]),(0,[z0,z1,z194,z2,z4,z5,z6]),(0,[z143,z47,z1,z2,z4,z5,z6])],[(0,[z17,z0,z1,z2,z21,z5,z6]),(0,[z67,z0,z1,z2,z4,z5,z31]),(0,[z0,z1,z2,z29,z5,z6,z28]),(0,[z0,z1,z2,z21,z5,z6,z133]),(0,[z0,z1,z2,z4,z195,z5,z6])]],
   [[(0,[z1,z2,z16,z4,z5,z6,z31]),(0,[z0,z1,z2,z4,z5,z196,z6]),(0,[z0,z1,z197,z2,z4,z5,z6])],[(0,[z13,z0,z2,z4,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z198]),(0,[z72,z0,z1,z2,z21,z5,z6]),(0,[z199,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z200,z16,z4,z5,z6]),(0,[z201,z25,z1,z2,z4,z5,z6]),(1,[z202,z1,z2,z4,z5,z6]),(0,[z203,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z204,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z51,z5,z6]),(0,[z0,z1,z2,z4,z174,z5,z6]),(0,[z0,z1,z2,z4,z70,z6,z31]),(0,[z0,z1,z2,z4,z5,z6,z205])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z181,z1,z73,z2,z4,z5,z6]),(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z207,z21,z5,z6]),(0,[z0,z1,z2,z21,z5,z208,z6]),(0,[z0,z1,z2,z4,z209,z5,z6])],[(0,[z0,z1,z2,z4,z210,z5,z6]),(0,[z0,z1,z2,z156,z5,z161,z6]),(0,[z0,z1,z2,z211,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z5,z205]),(1,[z212,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z213,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z214,z6]),(0,[z0,z1,z2,z4,z5,z215,z6]),(0,[z0,z1,z2,z4,z140,z5,z6])],[(0,[z72,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z216,z5,z6]),(1,[z1,z132,z16,z4,z5,z6]),(0,[z217,z0,z1,z2,z21,z5,z6]),(1,[z218,z1,z2,z4,z5,z6])],[(0,[z13,z15,z1,z2,z4,z5,z6]),(0,[z219,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z4,z5,z6,z133]),(0,[z48,z25,z1,z2,z4,z5,z6]),(0,[z220,z0,z1,z2,z4,z5,z6]),(0,[z0,z221,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z222,z4,z5,z6]),(0,[z223,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z224,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z225,z6])],[(0,[z25,z1,z226,z2,z4,z5,z6]),(1,[z227,z1,z2,z4,z5,z6]),(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z4,z5,z208])]],
   [[(0,[z0,z1,z2,z4,z5,z229,z6]),(0,[z0,z1,z2,z4,z5,z230,z6]),(0,[z0,z1,z231,z2,z4,z5,z6]),(0,[z1,z2,z16,z4,z51,z5,z6]),(0,[z0,z2,z4,z29,z5,z6,z28]),(0,[z0,z1,z2,z4,z55,z5,z6]),(1,[z0,z160,z2,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z208,z6]),(0,[z67,z1,z2,z4,z125,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z232]),(0,[z0,z1,z2,z29,z183,z5,z6])],[(0,[z72,z0,z2,z4,z29,z5,z6]),(0,[z233,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z234,z6]),(0,[z25,z1,z2,z4,z40,z5,z6]),(1,[z25,z1,z105,z4,z5,z6]),(0,[z0,z1,z2,z4,z235,z5,z6]),(0,[z0,z1,z2,z4,z236,z5,z6])],[(0,[z0,z1,z2,z4,z237,z5,z6]),(0,[z238,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z5,z6]),(0,[z0,z1,z2,z4,z240,z5,z6])],[(0,[z25,z64,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z241,z5,z6]),(0,[z0,z1,z2,z4,z18,z76,z6]),(0,[z0,z33,z1,z2,z32,z5,z6]),(1,[z0,z33,z2,z4,z5,z56]),(0,[z1,z35,z2,z242,z4,z5,z6]),(0,[z0,z243,z1,z2,z4,z5,z6])],[(0,[z13,z0,z1,z2,z4,z113,z6]),(0,[z244,z0,z1,z2,z4,z5,z6]),(0,[z92,z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z2,z4,z36,z5,z6])],[(0,[z25,z1,z2,z4,z29,z5,z6]),(0,[z25,z1,z2,z4,z5,z6,z133]),(0,[z0,z1,z2,z4,z245,z5,z6]),(0,[z24,z58,z1,z2,z4,z5,z6]),(1,[z48,z0,z1,z2,z5,z142])],[(0,[z0,z1,z2,z4,z246,z5,z6]),(0,[z0,z1,z2,z247,z4,z5,z6]),(0,[z248,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z249,z1,z2,z4,z5,z6]),(1,[z250,z1,z2,z4,z5,z6]),(0,[z251,z0,z1,z2,z4,z5,z6]),(1,[z0,z59,z2,z4,z5,z6])],[(0,[z0,z1,z252,z2,z4,z5,z6]),(0,[z253,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z20,z5,z6]),(0,[z254,z1,z132,z2,z4,z5,z6]),(0,[z0,z14,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z255,z5,z6]),(0,[z256,z0,z1,z2,z4,z5,z6]),(0,[z0,z257,z1,z2,z4,z5,z6])],[(0,[z0,z1,z258,z2,z4,z5,z6]),(0,[z25,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z125,z5,z6]),(0,[z259,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z260,z5,z6]),(0,[z1,z2,z4,z20,z5,z18,z6]),(0,[z0,z165,z2,z43,z4,z5,z6]),(1,[z254,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z210,z5,z6]),(0,[z0,z1,z2,z4,z261,z5,z6]),(0,[z0,z1,z2,z4,z5,z262,z6])],[(0,[z13,z0,z1,z2,z4,z5,z263]),(0,[z0,z1,z2,z16,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z18,z6]),(0,[z170,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z264,z2,z4,z5,z6]),(0,[z101,z0,z1,z2,z4,z173,z6]),(0,[z0,z1,z265,z2,z4,z5,z6])],[(0,[z13,z0,z1,z2,z4,z5,z229]),(0,[z0,z1,z105,z2,z4,z5,z6]),(0,[z100,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z266,z5,z6]),(0,[z0,z1,z2,z4,z267,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z6]),(0,[z0,z1,z4,z70,z5,z139,z6]),(0,[z104,z0,z1,z2,z4,z5,z30]),(0,[z0,z1,z2,z4,z5,z30,z31])],[(0,[z158,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z268,z0,z1,z2,z21,z5,z6]),(0,[z250,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z70,z76,z6]),(0,[z0,z1,z35,z156,z4,z5,z6])],[(0,[z13,z0,z1,z2,z269,z5,z6]),(0,[z0,z270,z1,z2,z4,z5,z6]),(0,[z0,z14,z33,z2,z4,z5,z6]),(0,[z0,z1,z35,z2,z21,z5,z6]),(0,[z101,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z190,z6])],[(0,[z0,z1,z2,z4,z271,z5,z6]),(0,[z15,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z171,z4,z5,z6]),(0,[z272,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z36,z5,z6,z142]),(0,[z0,z1,z2,z4,z273,z5,z6])]],
   [[(0,[z24,z25,z1,z2,z4,z5,z6]),(0,[z100,z0,z1,z2,z29,z5,z6]),(1,[z0,z1,z12,z4,z5,z6])],[(0,[z13,z0,z1,z2,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z274,z4,z5,z6]),(0,[z0,z1,z2,z156,z29,z5,z6]),(0,[z0,z1,z2,z4,z26,z5,z6])],[(0,[z0,z1,z2,z4,z275,z5,z6]),(0,[z276,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z35,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z277,z6]),(0,[z0,z1,z82,z4,z36,z5,z6])],[(0,[z72,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z16,z43,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z6,z142]),(0,[z181,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z278]),(0,[z0,z1,z82,z4,z5,z30,z6])],[(0,[z100,z103,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z36,z5,z6]),(1,[z1,z2,z4,z5,z81,z6]),(0,[z0,z279,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z280,z4,z5,z6]),(0,[z0,z1,z2,z4,z281,z5,z6]),(1,[z0,z1,z2,z4,z5,z117]),(0,[z9,z0,z2,z4,z5,z76,z6]),(0,[z0,z2,z4,z55,z5,z76,z6])],[(0,[z103,z1,z73,z2,z4,z5,z6]),(0,[z1,z73,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z66,z6]),(0,[z282,z0,z1,z2,z4,z5,z6]),(0,[z283,z0,z1,z2,z4,z5,z6]),(0,[z284,z1,z82,z2,z4,z5,z6]),(0,[z0,z285,z1,z2,z4,z5,z6])],[(1,[z72,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z286,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z148])]],
   [[(0,[z0,z1,z2,z4,z5,z287,z6]),(0,[z25,z1,z2,z4,z20,z5,z6]),(0,[z100,z0,z1,z2,z125,z5,z6]),(0,[z288,z0,z1,z2,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z5,z6]),(0,[z0,z289,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z290,z5,z6]),(0,[z92,z0,z1,z2,z21,z5,z6]),(0,[z92,z0,z1,z2,z4,z5,z291]),(0,[z0,z1,z4,z5,z30,z6,z133])],[(0,[z137,z0,z1,z105,z4,z5,z6]),(0,[z292,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z18,z6]),(0,[z293,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z294,z5,z6])],[(0,[z72,z0,z1,z2,z4,z5,z6]),(0,[z1,z105,z2,z16,z4,z5,z6]),(0,[z92,z88,z1,z2,z4,z5,z6]),(0,[z0,z1,z295,z2,z4,z5,z6]),(0,[z296,z0,z1,z2,z4,z5,z6])],[(0,[z297,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z224,z2,z4,z5,z6]),(0,[z0,z1,z2,z207,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z6,z31])],[(0,[z0,z1,z2,z4,z5,z298,z6]),(0,[z92,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z299,z6]),(0,[z0,z165,z1,z2,z4,z55,z6]),(1,[z0,z1,z2,z102,z5,z6]),(0,[z0,z1,z2,z178,z36,z5,z6]),(1,[z0,z1,z82,z4,z5,z30]),(0,[z0,z1,z2,z4,z5,z6,z300])],[(0,[z0,z1,z2,z301,z21,z5,z6]),(0,[z0,z1,z2,z4,z302,z5,z6]),(0,[z0,z1,z2,z4,z26,z5,z133]),(0,[z303,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z154,z6])],[(0,[z304,z0,z1,z2,z4,z5,z6]),(0,[z25,z1,z2,z43,z4,z5,z6]),(0,[z25,z1,z82,z2,z4,z5,z6]),(0,[z0,z1,z2,z156,z5,z6,z142]),(0,[z0,z1,z2,z4,z5,z6,z305]),(0,[z0,z1,z2,z5,z208,z6,z142])],[(0,[z0,z1,z2,z21,z5,z6,z27]),(0,[z306,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z307,z6]),(0,[z308,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z309,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z4,z5,z18,z6]),(0,[z0,z1,z2,z200,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z56,z6]),(0,[z22,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z26,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z310]),(0,[z24,z180,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z108,z4,z161,z6]),(0,[z0,z1,z2,z4,z311,z5,z6]),(0,[z0,z312,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z313]),(0,[z0,z1,z2,z4,z314,z5,z6])],[(0,[z315,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z316,z6]),(0,[z0,z1,z2,z4,z317,z5,z6]),(0,[z0,z1,z2,z318,z4,z5,z6]),(0,[z319,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z320,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z321]),(0,[z322,z0,z1,z2,z4,z5,z6]),(1,[z297,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z138,z6]),(0,[z0,z1,z37,z43,z4,z5,z6]),(0,[z0,z64,z1,z2,z21,z5,z6]),(0,[z0,z1,z4,z36,z5,z139,z6]),(0,[z323,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z119,z4,z5,z6]),(0,[z1,z2,z4,z5,z86,z6,z27]),(0,[z0,z1,z2,z4,z5,z6,z115])],[(0,[z181,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z324,z2,z4,z5,z6]),(0,[z97,z0,z1,z2,z119,z5,z6]),(0,[z97,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z5,z325,z6]),(0,[z326,z1,z37,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z327,z6]),(0,[z47,z0,z1,z2,z4,z51,z6])],[(0,[z328,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z329,z2,z4,z5,z6]),(0,[z0,z1,z2,z330,z4,z5,z6]),(0,[z1,z37,z2,z23,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z6,z27]),(0,[z0,z331,z1,z2,z4,z5,z6]),(0,[z0,z2,z43,z4,z29,z5,z6]),(0,[z186,z1,z2,z4,z5,z6,z28]),(0,[z0,z1,z2,z242,z4,z5,z6]),(0,[z218,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z86,z6]),(0,[z332,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z333,z6]),(0,[z0,z1,z2,z34,z4,z5,z6]),(0,[z334,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z25,z1,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z125,z29,z5,z6]),(0,[z74,z0,z1,z43,z4,z5,z6]),(0,[z0,z1,z2,z4,z335,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z336])],[(0,[z25,z1,z2,z4,z70,z5,z6]),(0,[z337,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z338,z5,z6]),(0,[z0,z1,z2,z21,z156,z5,z6]),(0,[z120,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z339,z5,z6]),(0,[z104,z0,z1,z2,z140,z5,z6]),(0,[z0,z1,z2,z4,z340,z5,z6])],[(0,[z0,z14,z1,z2,z4,z5,z6])],[(0,[z9,z25,z1,z2,z4,z5,z6]),(0,[z25,z1,z2,z119,z4,z5,z6]),(0,[z0,z1,z2,z4,z341,z5,z6]),(0,[z0,z64,z2,z4,z29,z5,z6]),(0,[z104,z0,z1,z2,z21,z5,z6]),(0,[z0,z342,z1,z2,z4,z5,z6]),(0,[z104,z0,z1,z2,z4,z11,z6])],[(0,[z343,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z344,z6]),(1,[z0,z1,z2,z21,z5,z6]),(1,[z0,z1,z2,z4,z5,z291]),(1,[z0,z1,z2,z4,z11,z6])],[(0,[z100,z0,z1,z2,z4,z5,z6]),(0,[z15,z1,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z184,z5,z6]),(0,[z345,z1,z2,z4,z5,z76,z6]),(1,[z0,z1,z2,z4,z174,z6]),(0,[z0,z1,z37,z4,z70,z5,z6]),(1,[z284,z1,z2,z4,z5,z6])],[(0,[z13,z0,z1,z346,z4,z5,z6]),(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z268,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z348,z5,z6]),(0,[z0,z349,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z350,z4,z5,z6])],[(0,[z351,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z352,z5,z6]),(0,[z0,z1,z2,z4,z5,z30,z28]),(0,[z0,z1,z35,z2,z4,z5,z6]),(1,[z326,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z353]),(0,[z0,z1,z2,z4,z5,z161,z6])]],
   [[(0,[z25,z1,z2,z4,z354,z5,z6]),(0,[z0,z1,z2,z355,z4,z5,z6]),(1,[z0,z1,z2,z29,z5,z6]),(0,[z47,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z356,z5,z6]),(0,[z0,z1,z2,z4,z357,z5,z6])],[(0,[z358,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z359,z2,z4,z5,z6]),(0,[z0,z132,z2,z43,z4,z5,z6]),(0,[z92,z0,z1,z4,z36,z5,z6]),(1,[z0,z1,z2,z239,z5,z6]),(0,[z0,z1,z2,z49,z4,z5,z6])],[(0,[z360,z0,z1,z2,z4,z5,z6]),(0,[z13,z17,z1,z2,z4,z5,z6]),(0,[z67,z72,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z361]),(0,[z0,z1,z2,z21,z5,z30,z6]),(0,[z0,z362,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z263]),(0,[z0,z1,z2,z4,z5,z6,z363]),(0,[z0,z1,z2,z4,z364,z5,z6])],[(0,[z1,z2,z16,z4,z5,z6,z365]),(1,[z1,z2,z366,z4,z5,z6]),(0,[z101,z0,z1,z2,z29,z5,z6]),(0,[z47,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z5,z6,z31]),(0,[z0,z1,z2,z4,z5,z367,z6])],[(0,[z368,z0,z1,z2,z4,z5,z6]),(0,[z0,z369,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z246,z5,z6]),(1,[z22,z0,z1,z4,z139,z6]),(0,[z48,z0,z1,z2,z4,z5,z208])],[(0,[z0,z1,z2,z29,z5,z86,z6]),(0,[z0,z64,z1,z132,z4,z5,z6])],[(0,[z0,z1,z2,z4,z370,z5,z6]),(0,[z0,z1,z2,z4,z5,z371,z6])]],
   [[(0,[z372,z0,z1,z2,z4,z5,z6]),(0,[z130,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z373,z2,z4,z5,z6]),(0,[z217,z1,z2,z21,z4,z5,z6]),(1,[z0,z1,z2,z374,z5,z6]),(0,[z186,z0,z1,z2,z4,z5,z6]),(0,[z92,z375,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z30,z6]),(0,[z0,z1,z376,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z377,z6]),(0,[z0,z1,z2,z4,z5,z6,z378]),(0,[z379,z0,z1,z2,z4,z5,z6]),(0,[z92,z0,z1,z2,z4,z5,z6]),(0,[z24,z0,z59,z2,z4,z5,z6])],[(0,[z25,z1,z2,z178,z4,z5,z6]),(1,[z0,z380,z2,z4,z5,z6]),(0,[z381,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z266,z5,z6]),(0,[z382,z0,z1,z2,z4,z5,z6])],[(0,[z13,z1,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z383,z5,z6]),(0,[z0,z1,z2,z156,z108,z5,z6])],[(0,[z0,z1,z2,z4,z384,z5,z6]),(0,[z0,z1,z2,z4,z385,z5,z6]),(0,[z0,z1,z2,z43,z21,z5,z6]),(0,[z386,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z1,z2,z21,z5,z6]),(0,[z0,z1,z82,z2,z21,z5,z6]),(0,[z0,z1,z2,z21,z5,z6,z387]),(0,[z48,z0,z1,z2,z4,z154,z6])],[(0,[z0,z1,z2,z4,z5,z388,z6]),(0,[z0,z1,z2,z4,z5,z389,z6]),(0,[z0,z1,z35,z37,z4,z5,z6]),(0,[z104,z0,z265,z2,z4,z5,z6]),(0,[z0,z1,z390,z2,z4,z5,z6])],[(0,[z13,z1,z2,z4,z5,z86,z6]),(0,[z1,z2,z16,z391,z4,z5,z6]),(0,[z100,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z226,z2,z4,z5,z6]),(0,[z17,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z5,z161,z6]),(0,[z0,z1,z2,z301,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z76,z6]),(1,[z0,z265,z2,z4,z5,z6])],[(0,[z25,z72,z1,z2,z4,z5,z6]),(0,[z103,z1,z2,z4,z125,z5,z6]),(0,[z0,z1,z2,z4,z20,z76,z6]),(0,[z392,z0,z1,z2,z4,z5,z6]),(0,[z0,z58,z1,z2,z4,z5,z6])]],
   [[(0,[z103,z1,z2,z16,z4,z5,z6]),(0,[z25,z33,z1,z2,z4,z5,z6]),(0,[z393,z0,z1,z2,z4,z5,z6]),(0,[z0,z394,z1,z2,z4,z5,z6]),(0,[z181,z1,z2,z4,z5,z86,z6]),(0,[z0,z1,z2,z43,z29,z5,z6]),(0,[z0,z1,z1,z2,z29,z5,z6]),(0,[z0,z1,z82,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z395,z5,z6]),(0,[z0,z1,z2,z396,z4,z5,z6])],[(1,[z0,z1,z2,z4,z113,z6]),(0,[z97,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z397,z6]),(0,[z104,z227,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z398]),(0,[z24,z0,z1,z12,z4,z5,z6]),(0,[z0,z1,z2,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z399,z6])],[(0,[z17,z103,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z400,z29,z5,z6]),(1,[z0,z1,z193,z4,z5,z6]),(0,[z0,z1,z156,z4,z36,z5,z6])],[(0,[z33,z1,z2,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z6,z31]),(0,[z0,z401,z1,z2,z4,z5,z6]),(0,[z0,z64,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z402,z6]),(0,[z0,z1,z2,z403,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z40,z6]),(0,[z0,z1,z2,z4,z5,z6,z404])],[(0,[z72,z103,z1,z2,z4,z5,z6]),(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z139,z6,z31])],[(0,[z137,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z29,z5,z6]),(0,[z0,z1,z2,z406,z4,z5,z6]),(0,[z407,z0,z1,z2,z4,z5,z6])],[(0,[z408,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z409,z6])],[(1,[z0,z1,z2,z4,z5,z263]),(0,[z0,z1,z2,z4,z5,z410,z6]),(0,[z1,z2,z16,z21,z4,z5,z6]),(0,[z0,z380,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z411,z5,z6]),(0,[z412,z0,z1,z2,z4,z5,z6]),(0,[z0,z413,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z229]),(0,[z414,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z5,z6,z378]),(0,[z0,z1,z2,z21,z5,z76,z6]),(0,[z0,z1,z2,z40,z5,z161,z6]),(0,[z0,z1,z2,z4,z5,z6,z415]),(0,[z0,z1,z2,z4,z416,z5,z6])],[(0,[z0,z1,z2,z119,z21,z5,z6]),(0,[z0,z417,z1,z2,z4,z5,z6]),(0,[z375,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z30,z208])],[(0,[z181,z0,z1,z2,z4,z20,z6]),(1,[z0,z1,z2,z4,z173,z6]),(0,[z0,z1,z2,z4,z5,z139,z6]),(0,[z418,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z419,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z51,z5,z6]),(0,[z48,z0,z1,z2,z21,z5,z6]),(0,[z9,z0,z1,z193,z4,z5,z6]),(1,[z0,z1,z2,z302,z5,z6]),(0,[z0,z121,z1,z2,z4,z5,z6]),(1,[z0,z420,z2,z4,z5,z6])],[(0,[z25,z1,z2,z4,z5,z208,z6]),(0,[z0,z1,z2,z4,z5,z421,z6]),(0,[z0,z1,z2,z4,z5,z6,z422]),(1,[z375,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z78,z5,z6]),(0,[z22,z0,z1,z2,z4,z70,z6]),(0,[z326,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z423,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z424,z4,z5,z6]),(0,[z0,z1,z2,z4,z425,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z426]),(0,[z124,z0,z2,z4,z29,z5,z6]),(0,[z0,z1,z2,z4,z427,z5,z6]),(0,[z0,z1,z37,z2,z4,z70,z6])],[(0,[z0,z1,z2,z4,z5,z6,z428]),(0,[z0,z1,z2,z429,z4,z5,z6]),(0,[z67,z1,z2,z4,z20,z5,z6]),(0,[z430,z0,z1,z2,z4,z5,z6]),(0,[z345,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z431,z6]),(1,[z0,z1,z2,z4,z5,z432])],[(0,[z13,z0,z1,z2,z433,z5,z6]),(0,[z1,z2,z16,z4,z5,z76,z6]),(0,[z25,z1,z2,z21,z4,z5,z6]),(0,[z0,z434,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z435,z5,z6]),(0,[z17,z0,z1,z2,z4,z20,z6]),(0,[z0,z436,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z437,z6]),(0,[z0,z14,z165,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z4,z5,z142])]],
   [[(0,[z13,z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z86,z28]),(0,[z0,z14,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z438]),(0,[z0,z1,z2,z4,z439,z5,z6]),(0,[z0,z1,z2,z4,z5,z440,z6])],[(0,[z97,z1,z2,z4,z125,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z441,z2,z4,z5,z6])],[(0,[z97,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z442,z2,z4,z5,z6]),(0,[z181,z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z55,z5,z6]),(0,[z0,z33,z1,z2,z4,z5,z56]),(0,[z0,z1,z2,z4,z443,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z142])],[(0,[z444,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z61,z4,z5,z6]),(0,[z100,z0,z1,z2,z119,z5,z6]),(0,[z1,z2,z4,z20,z5,z6,z27]),(0,[z0,z1,z2,z445,z4,z5,z6]),(0,[z446,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z447,z5,z6])],[(0,[z448,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z449,z6]),(0,[z0,z1,z2,z4,z450,z5,z6]),(0,[z0,z1,z2,z29,z29,z5,z6]),(0,[z9,z250,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z451,z5,z6]),(0,[z452,z0,z1,z2,z4,z5,z6]),(1,[z0,z165,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z453]),(0,[z454,z0,z1,z2,z4,z5,z6]),(0,[z455,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z456,z5,z6]),(0,[z0,z1,z457,z2,z4,z5,z6])],[(0,[z458,z0,z1,z2,z4,z5,z6]),(0,[z185,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z459])],[(0,[z13,z0,z1,z61,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z76,z6]),(0,[z25,z0,z1,z2,z21,z5,z6]),(0,[z0,z460,z1,z2,z4,z5,z6]),(0,[z254,z0,z1,z2,z4,z5,z6]),(0,[z446,z0,z1,z2,z29,z5,z6]),(1,[z0,z33,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z5,z6,z28]),(0,[z22,z46,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z40,z139,z6])]],
   [[(0,[z1,z2,z16,z108,z4,z5,z6]),(0,[z17,z67,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z461,z5,z6]),(0,[z104,z0,z1,z2,z4,z5,z133])],[(0,[z0,z1,z2,z4,z5,z6,z462]),(0,[z0,z1,z2,z29,z5,z139,z6]),(0,[z0,z1,z2,z4,z55,z139,z6]),(0,[z0,z160,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z86,z6]),(0,[z463,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z464,z6]),(0,[z0,z1,z2,z4,z5,z6,z465])],[(0,[z25,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z466,z5,z6]),(0,[z116,z0,z1,z2,z4,z86,z6]),(0,[z0,z1,z2,z29,z5,z421,z6]),(0,[z0,z1,z2,z21,z159,z5,z6]),(0,[z0,z1,z467,z2,z21,z5,z6]),(1,[z249,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z291]),(0,[z0,z1,z2,z4,z5,z6,z468]),(0,[z0,z1,z2,z4,z469,z5,z6]),(0,[z0,z1,z2,z4,z470,z5,z6])],[(0,[z103,z1,z2,z4,z5,z86,z6]),(0,[z169,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z105,z43,z4,z5,z6]),(0,[z0,z1,z2,z471,z4,z5,z6]),(0,[z15,z0,z1,z2,z21,z5,z6]),(0,[z472,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z459,z6]),(0,[z0,z1,z2,z4,z5,z6,z473])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z433,z5,z6]),(0,[z0,z1,z2,z43,z4,z5,z6]),(0,[z24,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z76,z139,z6]),(0,[z0,z1,z2,z4,z474,z5,z6]),(0,[z0,z1,z82,z2,z4,z5,z6]),(0,[z48,z212,z1,z2,z4,z5,z6]),(1,[z0,z285,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z475])],[(0,[z1,z2,z16,z4,z5,z6,z28]),(0,[z1,z2,z16,z4,z5,z144,z6]),(1,[z0,z2,z4,z341,z5,z6]),(0,[z476,z0,z1,z2,z29,z5,z6]),(0,[z0,z33,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z477,z5,z6])],[(0,[z1,z73,z2,z4,z5,z6,z27]),(0,[z0,z1,z478,z2,z4,z5,z6]),(0,[z0,z1,z479,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z56,z6]),(0,[z0,z1,z480,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z269,z4,z5,z6]),(0,[z13,z0,z1,z2,z4,z112,z6]),(0,[z15,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z481,z6])],[(0,[z1,z2,z16,z156,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z6,z142]),(0,[z217,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z26,z175,z5,z6])],[(0,[z101,z1,z2,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z482,z6]),(0,[z181,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z483,z1,z2,z4,z5,z6]),(1,[z345,z1,z2,z4,z5,z6]),(0,[z484,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z485,z5,z6]),(0,[z0,z202,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z55,z6]),(0,[z486,z0,z1,z2,z4,z5,z6])],[(0,[z13,z1,z2,z4,z125,z5,z6]),(0,[z487,z0,z1,z2,z4,z5,z6]),(0,[z488,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z489,z5,z6]),(0,[z0,z1,z2,z108,z4,z40,z6])],[(0,[z13,z1,z2,z16,z4,z5,z6]),(0,[z490,z0,z1,z2,z4,z5,z6]),(0,[z124,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z330,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z56,z31]),(0,[z491,z0,z1,z2,z4,z5,z6])],[(0,[z452,z1,z2,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z6,z28]),(0,[z181,z1,z2,z4,z125,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z492]),(0,[z493,z0,z1,z2,z4,z5,z6])],[(0,[z494,z0,z1,z2,z4,z5,z6]),(0,[z201,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z495,z6]),(0,[z0,z1,z2,z4,z5,z6,z496]),(1,[z279,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z139,z6])]],
   [[(0,[z1,z2,z4,z125,z5,z18,z6]),(0,[z0,z1,z2,z4,z497,z5,z6]),(0,[z116,z0,z1,z2,z4,z5,z6]),(0,[z0,z64,z165,z2,z4,z5,z6]),(0,[z0,z1,z498,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z70,z5,z6])],[(0,[z0,z1,z499,z2,z4,z5,z6]),(0,[z0,z64,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z5,z464,z6]),(0,[z0,z1,z2,z4,z5,z77,z6]),(0,[z0,z500,z1,z2,z4,z5,z6]),(0,[z0,z1,z82,z2,z4,z5,z133]),(1,[z0,z501,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z51,z31]),(0,[z0,z1,z2,z4,z5,z6,z502])],[(1,[z0,z1,z346,z4,z5,z6]),(0,[z0,z1,z503,z2,z4,z5,z6]),(0,[z0,z1,z2,z191,z4,z5,z6]),(0,[z74,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z504,z5,z6]),(0,[z0,z1,z2,z4,z505,z5,z6]),(0,[z0,z64,z33,z2,z4,z5,z6])],[(0,[z0,z1,z2,z29,z294,z5,z6]),(0,[z101,z279,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z56,z133]),(0,[z0,z1,z2,z506,z4,z5,z6]),(0,[z0,z1,z2,z4,z507,z5,z6]),(0,[z0,z1,z2,z4,z5,z508,z6])],[(0,[z0,z1,z2,z509,z4,z5,z6]),(0,[z510,z0,z1,z2,z4,z5,z6]),(0,[z17,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z139,z6]),(0,[z48,z0,z1,z2,z4,z5,z6])],[(0,[z25,z1,z132,z2,z4,z5,z6]),(0,[z100,z67,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z511,z6]),(0,[z0,z14,z2,z43,z4,z5,z6]),(1,[z124,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z512,z5,z6])],[(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z72,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z514,z6]),(0,[z0,z1,z515,z2,z4,z5,z6]),(1,[z15,z1,z2,z4,z5,z27]),(0,[z0,z1,z2,z29,z5,z56,z6]),(0,[z0,z420,z1,z2,z4,z5,z6]),(0,[z0,z516,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z517,z6])],[(0,[z0,z1,z2,z4,z354,z5,z6]),(1,[z0,z1,z2,z4,z5,z468]),(0,[z0,z518,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z390,z2,z4,z5,z6]),(0,[z48,z0,z1,z2,z4,z190,z6])],[(0,[z25,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z519,z2,z4,z5,z6]),(0,[z520,z0,z1,z2,z4,z5,z6]),(1,[z88,z1,z2,z4,z5,z6]),(1,[z0,z1,z35,z156,z5,z6]),(0,[z0,z521,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z522,z5,z6]),(0,[z15,z0,z1,z2,z4,z5,z86]),(0,[z0,z1,z2,z4,z5,z6,z523]),(0,[z0,z1,z2,z4,z524,z5,z6]),(0,[z104,z0,z1,z2,z29,z5,z6]),(0,[z104,z0,z1,z2,z4,z357,z6])],[(0,[z25,z1,z2,z4,z5,z6,z525]),(0,[z74,z0,z1,z2,z147,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z148]),(1,[z0,z2,z43,z29,z5,z6]),(0,[z272,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z526]),(1,[z0,z1,z2,z4,z357,z6]),(1,[z47,z0,z1,z2,z4,z26])],[(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z527]),(0,[z0,z1,z2,z21,z36,z5,z6]),(0,[z48,z0,z1,z2,z178,z5,z6])],[(0,[z0,z1,z2,z419,z4,z5,z6]),(0,[z0,z1,z2,z21,z245,z5,z6]),(1,[z0,z1,z2,z411,z5,z6]),(0,[z0,z528,z1,z2,z4,z5,z6])],[(0,[z124,z1,z2,z16,z4,z5,z6]),(0,[z1,z2,z16,z4,z55,z5,z6]),(0,[z25,z0,z1,z16,z4,z5,z6]),(0,[z15,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z529,z4,z5,z6])],[(0,[z1,z73,z2,z16,z4,z5,z6]),(0,[z74,z0,z64,z2,z4,z5,z6]),(0,[z0,z1,z132,z37,z4,z5,z6]),(0,[z0,z1,z2,z29,z70,z5,z6]),(0,[z0,z1,z2,z4,z5,z45,z6]),(0,[z0,z1,z2,z4,z5,z133,z142])]],
   [[(0,[z25,z0,z1,z2,z4,z5,z6]),(0,[z530,z0,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z163,z6]),(0,[z9,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z531])],[(0,[z64,z1,z2,z16,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z126]),(1,[z0,z528,z2,z4,z5,z6]),(0,[z0,z1,z2,z178,z4,z5,z6])],[(1,[z13,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z532]),(0,[z533,z0,z1,z2,z4,z5,z6]),(0,[z101,z0,z1,z2,z4,z5,z28]),(0,[z534,z0,z1,z2,z4,z5,z6]),(0,[z535,z0,z1,z2,z4,z5,z6]),(1,[z143,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z26,z5])],[(0,[z1,z2,z16,z4,z36,z5,z6]),(0,[z0,z1,z2,z512,z29,z5,z6]),(0,[z476,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z165,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z536,z5,z6])],[(0,[z100,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z64,z1,z2,z461,z5,z6]),(0,[z9,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z467,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z423]),(1,[z486,z1,z2,z4,z5,z6]),(0,[z48,z0,z285,z2,z4,z5,z6])],[(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z538,z4,z5,z6]),(0,[z101,z0,z1,z264,z4,z5,z6]),(0,[z0,z1,z2,z4,z26,z5,z28]),(0,[z0,z1,z2,z4,z5,z6,z539]),(0,[z0,z1,z2,z4,z5,z6,z540])],[(0,[z0,z1,z2,z541,z4,z5,z6]),(0,[z9,z0,z1,z2,z411,z5,z6]),(0,[z0,z1,z2,z4,z5,z81,z6]),(0,[z0,z1,z2,z23,z4,z5,z6]),(0,[z24,z0,z1,z2,z4,z5,z6]),(0,[z542,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z543,z5,z6]),(0,[z0,z1,z2,z4,z5,z544,z6]),(0,[z0,z1,z2,z4,z545,z5,z6])],[(0,[z546,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z6,z115]),(0,[z0,z547,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z548,z6]),(0,[z0,z1,z2,z4,z5,z6,z549]),(0,[z0,z1,z2,z4,z5,z6,z550]),(0,[z0,z1,z2,z4,z5,z31,z142])]],
   [[(1,[z1,z2,z16,z21,z5,z6]),(0,[z1,z2,z16,z4,z125,z5,z6]),(0,[z97,z100,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z551]),(0,[z0,z1,z43,z4,z5,z139,z6]),(0,[z0,z1,z2,z21,z26,z5,z6]),(0,[z0,z1,z552,z2,z4,z5,z6]),(0,[z0,z46,z1,z2,z4,z5,z6])],[(0,[z488,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z16,z4,z5,z6]),(0,[z0,z1,z553,z2,z4,z5,z6]),(0,[z554,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z19,z5]),(0,[z0,z1,z2,z4,z555,z5,z6]),(0,[z0,z1,z2,z556,z4,z5,z6]),(0,[z0,z33,z2,z4,z5,z56,z6]),(0,[z0,z1,z35,z82,z4,z5,z6]),(0,[z22,z218,z1,z2,z4,z5,z6]),(0,[z0,z1,z189,z2,z4,z5,z6]),(0,[z557,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z558]),(0,[z0,z1,z559,z2,z4,z5,z6]),(1,[z67,z1,z2,z4,z5,z86]),(1,[z1,z2,z4,z159,z5,z6]),(1,[z1,z2,z162,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z31]),(0,[z93,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z112,z6]),(0,[z25,z1,z2,z4,z36,z5,z6]),(0,[z0,z1,z2,z4,z5,z560,z6]),(0,[z0,z1,z2,z561,z4,z5,z6]),(0,[z0,z1,z2,z4,z562,z5,z6]),(0,[z0,z1,z2,z4,z563,z5,z6])],[(1,[z1,z2,z16,z29,z5,z6]),(0,[z25,z1,z2,z4,z5,z30,z6]),(0,[z181,z47,z0,z1,z2,z4,z6]),(0,[z74,z202,z1,z2,z4,z5,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z10,z5,z6]),(1,[z1,z2,z4,z175,z5,z6])],[(0,[z0,z1,z2,z4,z5,z565,z6]),(0,[z446,z1,z2,z16,z4,z5,z6]),(0,[z53,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z108,z36,z5,z6]),(0,[z48,z0,z1,z2,z4,z5,z142]),(0,[z0,z1,z2,z4,z5,z566,z6])],[(0,[z0,z1,z2,z4,z5,z567,z6]),(0,[z25,z1,z2,z4,z568,z5,z6]),(1,[z0,z1,z2,z461,z5,z6]),(0,[z0,z1,z2,z4,z5,z569,z6])],[(0,[z1,z2,z16,z4,z26,z5,z6]),(0,[z292,z0,z1,z2,z4,z5,z6]),(0,[z0,z64,z1,z2,z403,z5,z6]),(0,[z1,z132,z2,z366,z4,z5,z6]),(0,[z1,z2,z21,z4,z159,z5,z6]),(0,[z0,z1,z35,z2,z156,z5,z6])]],
   [[(0,[z1,z2,z16,z4,z275,z5,z6]),(0,[z25,z165,z1,z2,z4,z5,z6]),(0,[z570,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z527]),(0,[z74,z0,z1,z132,z4,z5,z6]),(0,[z0,z1,z571,z2,z4,z5,z6]),(1,[z217,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z572]),(0,[z0,z1,z2,z4,z5,z6,z133]),(0,[z0,z1,z2,z573,z4,z5,z6])],[(0,[z17,z47,z0,z1,z2,z4,z6]),(0,[z181,z0,z1,z2,z4,z18,z6]),(0,[z15,z181,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z574])],[(0,[z0,z1,z2,z4,z5,z6,z575]),(0,[z0,z1,z576,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z577]),(0,[z0,z1,z2,z4,z51,z5,z6])],[(1,[z0,z1,z2,z433,z5,z6]),(0,[z1,z2,z16,z280,z4,z5,z6]),(0,[z0,z1,z132,z2,z21,z5,z6]),(0,[z92,z0,z1,z2,z4,z5,z578]),(0,[z0,z1,z2,z4,z5,z208,z6]),(0,[z0,z1,z579,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z580,z5,z6])],[(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z582,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z269,z5,z6]),(0,[z92,z1,z2,z16,z4,z5,z6]),(0,[z67,z0,z1,z2,z21,z5,z6]),(0,[z583,z0,z1,z2,z29,z5,z6]),(0,[z101,z57,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z584,z5,z6]),(0,[z104,z0,z420,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z26,z5,z30]),(0,[z24,z0,z1,z2,z5,z161,z6]),(0,[z0,z1,z585,z2,z4,z5,z6])],[(0,[z0,z1,z132,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z586,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z432]),(0,[z104,z0,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z161,z6]),(0,[z48,z0,z390,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z352,z4,z5,z6]),(0,[z114,z0,z1,z2,z4,z5,z6]),(0,[z97,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z119,z29,z5,z6]),(1,[z181,z1,z2,z4,z20,z6]),(0,[z587,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z141,z4,z5,z6]),(0,[z588,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z589,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z590,z6]),(0,[z67,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z163,z6]),(1,[z0,z1,z2,z403,z5,z6]),(0,[z92,z0,z1,z2,z156,z5,z6]),(0,[z0,z1,z2,z4,z5,z208,z31]),(0,[z0,z1,z2,z591,z4,z5,z6])],[(0,[z137,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z20,z5,z527]),(0,[z0,z64,z132,z2,z4,z5,z6]),(0,[z48,z0,z1,z2,z29,z5,z6]),(1,[z9,z0,z2,z4,z76,z6]),(0,[z0,z1,z2,z4,z592,z5,z6]),(1,[z24,z0,z1,z2,z161,z6])],[(0,[z25,z1,z37,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z56,z27]),(0,[z593,z0,z1,z2,z4,z5,z6]),(0,[z594,z0,z1,z2,z4,z5,z6]),(0,[z180,z0,z1,z2,z4,z5,z6])],[(0,[z595,z0,z1,z2,z4,z5,z6])],[(0,[z13,z0,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z596,z6])],[(0,[z0,z1,z597,z2,z4,z5,z6]),(0,[z137,z0,z1,z2,z29,z5,z6]),(0,[z152,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z86,z6]),(0,[z0,z1,z2,z21,z178,z5,z6]),(0,[z598,z0,z1,z2,z4,z5,z6])],[(0,[z181,z72,z1,z2,z4,z5,z6]),(0,[z0,z380,z2,z119,z4,z5,z6]),(1,[z0,z1,z2,z4,z138,z6]),(0,[z0,z599,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z6,z133]),(0,[z104,z0,z1,z2,z456,z5,z6]),(0,[z0,z1,z2,z4,z5,z208,z133]),(0,[z0,z1,z2,z4,z26,z5,z208])]],
   [[(0,[z0,z1,z2,z4,z19,z5,z6]),(0,[z0,z1,z2,z10,z4,z5,z6])],[(0,[z0,z1,z2,z29,z51,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z6]),(0,[z101,z0,z2,z4,z5,z6,z28]),(0,[z0,z1,z2,z4,z5,z30,z142])],[(0,[z0,z1,z2,z4,z20,z5,z6]),(0,[z0,z1,z2,z600,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z208,z6]),(0,[z24,z0,z501,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z31])],[(0,[z601,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z374,z4,z5,z6]),(0,[z0,z1,z2,z87,z4,z5,z6]),(0,[z48,z486,z1,z2,z4,z5,z6])],[(0,[z101,z0,z1,z87,z4,z5,z6]),(0,[z22,z0,z1,z37,z4,z5,z6])],[(0,[z0,z1,z2,z4,z602,z5,z6]),(0,[z0,z1,z2,z4,z5,z603,z6]),(0,[z0,z1,z2,z456,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z604])],[(0,[z72,z0,z73,z2,z4,z5,z6]),(0,[z0,z1,z2,z366,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z605,z6]),(0,[z0,z14,z2,z21,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z161,z6]),(0,[z104,z0,z1,z82,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z606,z6])],[(0,[z0,z1,z2,z4,z607,z5,z6]),(0,[z0,z1,z2,z4,z5,z608,z6]),(1,[z0,z1,z2,z4,z5,z578]),(0,[z0,z1,z2,z609,z4,z5,z6]),(0,[z48,z0,z1,z2,z5,z6,z142]),(1,[z257,z1,z2,z4,z5,z6])]],
   [[(0,[z104,z1,z2,z16,z4,z5,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z101,z25,z1,z2,z4,z5,z6]),(0,[z74,z0,z1,z2,z4,z5,z117]),(0,[z0,z1,z2,z611,z4,z5,z6]),(0,[z612,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z34,z5,z6]),(0,[z613,z0,z1,z2,z4,z5,z6])],[(1,[z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z482,z6]),(1,[z101,z0,z2,z4,z5,z28]),(0,[z120,z1,z35,z2,z4,z5,z6]),(0,[z0,z1,z614,z2,z4,z5,z6])],[(0,[z25,z1,z73,z2,z4,z5,z6]),(0,[z25,z103,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z4,z5,z344,z6]),(0,[z0,z1,z2,z4,z5,z6,z615]),(0,[z616,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z617,z29,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z459]),(0,[z0,z1,z2,z4,z5,z432,z6]),(0,[z0,z1,z2,z178,z5,z208,z6]),(0,[z0,z1,z2,z4,z26,z6,z31])],[(0,[z13,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z618,z6]),(0,[z25,z1,z2,z108,z4,z5,z6]),(0,[z67,z0,z1,z2,z4,z5,z86]),(0,[z0,z1,z4,z36,z5,z6,z133]),(0,[z0,z1,z2,z4,z5,z6,z619]),(0,[z47,z257,z1,z2,z4,z5,z6])],[(0,[z181,z0,z1,z2,z4,z6,z31]),(1,[z0,z2,z21,z29,z5,z6]),(0,[z24,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z6]),(0,[z620,z0,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z161,z6]),(0,[z47,z1,z2,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z86,z6]),(0,[z0,z33,z1,z2,z29,z5,z6]),(0,[z621,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z151,z4,z5,z6])],[(0,[z1,z35,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z622,z4,z5,z6]),(0,[z0,z1,z132,z4,z5,z139,z6]),(0,[z0,z14,z2,z4,z5,z76,z6]),(0,[z0,z165,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z623]),(0,[z624,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z70,z161,z6]),(0,[z625,z0,z1,z2,z4,z5,z6])],[(0,[z15,z103,z1,z2,z4,z5,z6]),(0,[z9,z249,z1,z2,z4,z5,z6])]],
   [[(0,[z626,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z627,z4,z5,z6]),(0,[z628,z0,z1,z2,z4,z5,z6]),(0,[z0,z212,z1,z2,z4,z5,z6])],[(1,[z1,z16,z43,z4,z5,z6]),(0,[z0,z1,z629,z2,z4,z5,z6]),(0,[z630,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z20,z5,z6]),(1,[z217,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z631]),(0,[z0,z1,z2,z4,z5,z6,z632]),(0,[z0,z1,z2,z4,z5,z633,z6])],[(0,[z0,z1,z132,z16,z4,z5,z6]),(0,[z17,z25,z1,z2,z4,z5,z6]),(0,[z634,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z635,z6]),(0,[z583,z0,z1,z2,z4,z5,z6]),(0,[z0,z33,z2,z4,z29,z5,z6]),(0,[z0,z1,z35,z4,z5,z6,z133])],[(0,[z0,z1,z2,z4,z636,z5,z6]),(0,[z9,z0,z1,z2,z4,z55,z6])],[(0,[z0,z1,z2,z4,z637,z5,z6]),(0,[z25,z1,z2,z156,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z638]),(0,[z0,z1,z2,z4,z20,z55,z6]),(0,[z0,z1,z132,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z617,z5,z6]),(0,[z0,z1,z2,z639,z4,z5,z6])],[(0,[z0,z1,z2,z119,z4,z5,z6]),(0,[z640,z0,z1,z2,z4,z5,z6]),(0,[z74,z297,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z147,z4,z5,z6]),(0,[z0,z1,z82,z43,z4,z5,z6]),(0,[z0,z165,z2,z4,z55,z5,z6]),(0,[z24,z0,z1,z2,z4,z5,z423])],[(0,[z67,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z641,z6]),(0,[z0,z1,z642,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z139,z161,z6]),(1,[z93,z1,z2,z4,z5,z6])],[(0,[z0,z1,z346,z2,z4,z5,z6]),(0,[z0,z165,z2,z4,z29,z5,z6]),(0,[z0,z165,z1,z2,z4,z76,z6]),(0,[z101,z0,z1,z2,z172,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z643]),(0,[z0,z644,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z27]),(0,[z0,z1,z2,z4,z400,z5,z6]),(0,[z0,z1,z2,z21,z21,z5,z6]),(0,[z22,z0,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z21,z40,z5,z6]),(0,[z22,z0,z1,z2,z4,z5,z468]),(0,[z0,z1,z2,z645,z4,z5,z6])],[(0,[z13,z1,z2,z4,z20,z5,z6]),(0,[z137,z0,z1,z16,z4,z5,z6]),(0,[z1,z132,z2,z16,z4,z5,z6]),(0,[z610,z1,z2,z16,z4,z5,z6]),(0,[z0,z646,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z125,z5,z6,z27]),(0,[z0,z1,z37,z2,z21,z5,z6]),(0,[z9,z0,z1,z330,z4,z5,z6]),(0,[z0,z1,z153,z2,z4,z5,z6]),(0,[z647,z0,z1,z2,z4,z5,z6])],[(0,[z1,z37,z2,z16,z4,z5,z6]),(0,[z1,z2,z16,z4,z384,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z525]),(1,[z100,z1,z2,z119,z5,z6]),(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z55,z5,z6]),(0,[z0,z165,z1,z2,z374,z5,z6])],[(0,[z137,z0,z1,z2,z4,z5,z6]),(0,[z181,z1,z2,z4,z20,z5,z6]),(0,[z284,z0,z1,z2,z4,z5,z6]),(0,[z650,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z651,z2,z4,z5,z6]),(0,[z0,z1,z2,z589,z4,z5,z6]),(0,[z490,z25,z1,z2,z4,z5,z6]),(0,[z124,z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z652,z6]),(0,[z0,z1,z2,z21,z29,z5,z6]),(0,[z22,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z653,z6]),(1,[z0,z189,z2,z4,z5,z6]),(1,[z0,z1,z49,z4,z5,z6])],[(0,[z0,z1,z37,z2,z29,z5,z6]),(0,[z0,z14,z2,z4,z5,z6,z28]),(0,[z0,z1,z2,z4,z5,z325,z6]),(0,[z22,z0,z1,z2,z239,z5,z6]),(0,[z0,z1,z2,z4,z5,z31,z133]),(0,[z0,z501,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z161,z6,z31])],[(1,[z13,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z654,z6])],[(0,[z1,z2,z16,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z86,z56]),(0,[z74,z0,z1,z2,z21,z5,z6])]],
   [[(0,[z165,z1,z2,z16,z4,z5,z6]),(0,[z25,z67,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z655,z5,z6])],[(0,[z0,z1,z2,z29,z5,z18,z6]),(0,[z0,z1,z2,z4,z55,z18,z6]),(0,[z656,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z139,z6]),(0,[z0,z1,z2,z4,z5,z578,z6]),(0,[z0,z1,z657,z2,z4,z5,z6])],[(0,[z253,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z658,z2,z4,z5,z6]),(0,[z0,z1,z659,z2,z4,z5,z6]),(0,[z0,z2,z43,z4,z5,z76,z6]),(0,[z69,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z83,z21,z5,z6]),(0,[z22,z0,z528,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z660,z5,z6]),(0,[z661,z0,z1,z2,z4,z5,z6]),(0,[z369,z1,z2,z16,z4,z5,z6]),(0,[z1,z2,z16,z4,z29,z5,z6]),(0,[z74,z0,z1,z2,z29,z5,z6]),(0,[z0,z1,z662,z2,z4,z5,z6]),(0,[z0,z1,z132,z82,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z28,z133]),(0,[z0,z1,z2,z4,z5,z663,z6]),(0,[z47,z0,z1,z2,z4,z26,z6])],[(0,[z0,z1,z105,z132,z4,z5,z6]),(0,[z0,z1,z2,z21,z125,z5,z6]),(0,[z0,z1,z2,z664,z4,z5,z6]),(0,[z0,z1,z2,z21,z261,z5,z6]),(1,[z0,z1,z264,z4,z5,z6]),(1,[z1,z2,z242,z4,z5,z6]),(0,[z665,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z666,z6]),(0,[z24,z0,z1,z2,z4,z161,z6]),(0,[z0,z1,z2,z4,z5,z6,z667]),(0,[z0,z668,z1,z2,z4,z5,z6])],[(0,[z25,z1,z2,z213,z4,z5,z6]),(0,[z15,z67,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z631]),(0,[z669,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z365]),(1,[z25,z1,z2,z21,z5,z6]),(0,[z0,z1,z43,z4,z5,z6,z133]),(0,[z0,z1,z2,z4,z55,z70,z6]),(0,[z0,z1,z2,z4,z5,z6,z670])],[(0,[z67,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z6,z27]),(0,[z0,z64,z2,z4,z5,z76,z6]),(0,[z92,z0,z1,z2,z4,z45,z6]),(0,[z0,z1,z2,z4,z5,z671,z6]),(0,[z227,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z73,z2,z21,z5,z6]),(0,[z0,z103,z1,z2,z21,z5,z6]),(0,[z1,z2,z16,z4,z5,z139,z6]),(0,[z48,z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z672,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z172,z5,z6])],[(0,[z25,z1,z2,z4,z55,z5,z6]),(0,[z0,z1,z2,z4,z5,z673,z6]),(1,[z74,z0,z43,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z6,z142]),(0,[z0,z1,z2,z4,z5,z6,z674]),(0,[z24,z0,z1,z141,z4,z5,z6]),(0,[z0,z1,z2,z108,z40,z5,z6]),(0,[z675,z0,z1,z2,z4,z5,z6])],[(1,[z25,z1,z2,z29,z5,z6]),(0,[z0,z33,z2,z43,z4,z5,z6]),(0,[z0,z33,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z676,z5,z6])],[(0,[z0,z103,z1,z2,z352,z5,z6]),(0,[z446,z25,z1,z2,z4,z5,z6]),(0,[z1,z2,z119,z4,z125,z5,z6]),(0,[z0,z1,z2,z4,z5,z30,z6])],[(0,[z0,z1,z73,z2,z29,z5,z6]),(0,[z0,z103,z1,z2,z29,z5,z6]),(0,[z137,z1,z2,z16,z4,z5,z6]),(0,[z360,z25,z1,z2,z4,z5,z6]),(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z92,z0,z1,z2,z4,z78,z6]),(0,[z0,z1,z2,z4,z5,z678,z6]),(0,[z679,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z680,z4,z5,z6]),(0,[z0,z1,z2,z4,z568,z5,z6]),(0,[z74,z0,z1,z2,z266,z5,z6]),(0,[z0,z1,z2,z108,z29,z5,z6]),(0,[z0,z165,z1,z2,z302,z5,z6]),(0,[z0,z1,z2,z681,z4,z5,z6])],[(0,[z0,z1,z2,z4,z682,z5,z6]),(0,[z1,z2,z4,z5,z18,z86,z6]),(0,[z15,z0,z1,z2,z4,z5,z31]),(0,[z683,z0,z1,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z631]),(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z0,z685,z1,z2,z4,z5,z6])],[(0,[z0,z686,z1,z2,z4,z5,z6]),(0,[z0,z165,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z687,z4,z5,z6]),(0,[z104,z0,z1,z4,z5,z6,z133]),(0,[z0,z1,z2,z4,z5,z688,z6])]],
   [[(0,[z1,z2,z16,z4,z5,z6,z142]),(0,[z0,z1,z2,z391,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z139,z6]),(0,[z689,z0,z1,z2,z4,z5,z6]),(0,[z690,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z691,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z692,z6])],[(0,[z0,z103,z1,z2,z246,z5,z6]),(0,[z693,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z43,z4,z5,z6,z28]),(0,[z0,z14,z64,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z126,z28]),(0,[z0,z1,z2,z4,z694,z5,z6])],[(0,[z72,z1,z2,z4,z5,z18,z6]),(0,[z0,z1,z2,z4,z5,z6,z695]),(0,[z92,z0,z109,z2,z4,z5,z6]),(0,[z0,z1,z37,z4,z36,z5,z6]),(0,[z1,z82,z2,z162,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z205])],[(0,[z1,z2,z2,z16,z4,z5,z6]),(0,[z92,z25,z1,z2,z4,z5,z6]),(0,[z25,z1,z2,z4,z125,z5,z6]),(0,[z0,z2,z21,z4,z29,z5,z6]),(0,[z22,z0,z1,z4,z5,z139,z6]),(1,[z0,z1,z153,z4,z5,z6])],[(0,[z25,z1,z2,z16,z4,z5,z6]),(1,[z57,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z70,z6])],[(0,[z1,z2,z16,z4,z20,z5,z6]),(0,[z25,z434,z1,z2,z4,z5,z6]),(0,[z25,z1,z105,z2,z4,z5,z6]),(0,[z0,z696,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z387])],[(0,[z25,z1,z2,z2,z4,z5,z6]),(0,[z697,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z698,z4,z5,z6]),(0,[z0,z1,z2,z4,z699,z5,z6]),(0,[z0,z1,z2,z700,z4,z5,z6]),(0,[z0,z64,z2,z4,z5,z6,z28]),(0,[z0,z1,z701,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z56,z6]),(1,[z92,z0,z1,z36,z5,z6]),(0,[z24,z0,z1,z2,z108,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z702])],[(0,[z103,z1,z2,z4,z20,z5,z6]),(0,[z0,z2,z119,z4,z341,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z703]),(1,[z0,z64,z2,z29,z5,z6]),(0,[z0,z1,z2,z704,z4,z5,z6]),(0,[z0,z1,z2,z705,z4,z5,z6]),(0,[z706,z0,z1,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z217,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z707,z6]),(0,[z1,z16,z43,z4,z5,z6]),(0,[z708,z0,z1,z2,z4,z6]),(0,[z202,z1,z132,z4,z5,z6]),(0,[z0,z14,z2,z21,z5,z6]),(0,[z709,z1,z2,z4,z5,z6])],[(0,[z533,z0,z2,z4,z76,z6]),(0,[z24,z0,z1,z141,z161,z6])],[(0,[z2,z16,z21,z29,z5,z6]),(0,[z2,z16,z29,z5,z6,z28]),(0,[z57,z1,z2,z21,z5,z6]),(0,[z1,z2,z4,z5,z710,z6]),(0,[z0,z1,z36,z139,z161,z6]),(0,[z0,z1,z2,z711,z5,z6]),(0,[z712,z1,z2,z4,z5,z6])],[(0,[z25,z285,z2,z4,z5,z6]),(0,[z217,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z239,z70,z6]),(0,[z0,z1,z2,z713,z5,z6])],[(0,[z1,z2,z16,z4,z112,z6]),(0,[z1,z2,z16,z4,z714,z6]),(0,[z25,z2,z4,z341,z5,z6]),(0,[z0,z1,z2,z715,z5,z6]),(0,[z0,z1,z2,z29,z5,z205]),(0,[z716,z1,z2,z4,z5,z6]),(0,[z227,z265,z2,z4,z5,z6])],[(0,[z0,z1,z717,z4,z5,z6]),(0,[z93,z1,z2,z4,z5,z6]),(0,[z1,z2,z21,z159,z5,z6]),(0,[z0,z189,z4,z5,z139,z6]),(0,[z58,z501,z2,z4,z5,z6])],[(0,[z0,z1,z718,z4,z5,z6]),(0,[z57,z1,z2,z29,z5,z6]),(0,[z719,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z578]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z104,z25,z1,z4,z5,z133]),(0,[z1,z2,z23,z21,z5,z6])],[(0,[z13,z0,z2,z29,z5,z229]),(0,[z0,z1,z2,z21,z5,z117]),(0,[z0,z2,z110,z29,z5,z6]),(0,[z0,z312,z2,z29,z5,z6]),(0,[z257,z1,z2,z4,z55,z6])],[(0,[z0,z1,z2,z4,z6,z721]),(0,[z420,z2,z16,z4,z5,z6]),(0,[z1,z2,z589,z391,z5,z6]),(0,[z100,z1,z2,z119,z5,z6]),(0,[z1,z2,z722,z4,z5,z6]),(0,[z2,z29,z5,z81,z76,z6]),(0,[z46,z1,z2,z4,z5,z468]),(0,[z0,z1,z2,z4,z440,z31])],[(0,[z1,z16,z4,z5,z6,z496]),(0,[z0,z2,z723,z29,z5,z6]),(0,[z724,z1,z2,z4,z5,z6])],[(0,[z25,z1,z330,z4,z5,z6]),(0,[z0,z2,z29,z5,z325,z6]),(0,[z1,z2,z23,z29,z5,z6]),(0,[z0,z2,z87,z4,z5,z28]),(0,[z88,z1,z2,z4,z45,z6]),(0,[z0,z725,z2,z4,z5,z6]),(0,[z0,z1,z2,z726,z5,z6])],[(0,[z727,z1,z2,z4,z5,z6]),(0,[z728,z1,z2,z29,z5,z6]),(0,[z0,z14,z2,z374,z5,z6]),(0,[z587,z0,z1,z2,z161,z6])],[(0,[z0,z1,z2,z4,z729,z6]),(0,[z730,z1,z2,z4,z5,z6]),(0,[z731,z1,z2,z4,z5,z6]),(0,[z732,z1,z2,z403,z5,z6]),(0,[z0,z1,z189,z4,z139,z6]),(0,[z71,z0,z1,z4,z139,z6])],[(0,[z0,z436,z2,z4,z55,z6]),(0,[z0,z43,z4,z5,z163,z6]),(0,[z0,z165,z2,z29,z76,z6]),(0,[z647,z0,z2,z4,z5,z28]),(0,[z0,z733,z2,z4,z5,z6]),(0,[z486,z1,z153,z4,z5,z6])],[(0,[z25,z501,z2,z4,z5,z6]),(0,[z0,z1,z2,z734,z5,z6]),(0,[z100,z0,z2,z341,z5,z6]),(0,[z58,z1,z2,z29,z5,z6])]],
   [[(0,[z0,z1,z346,z4,z112,z6]),(0,[z25,z1,z346,z4,z5,z6]),(0,[z528,z2,z16,z4,z5,z6]),(0,[z88,z1,z2,z4,z78,z6]),(0,[z0,z1,z2,z735,z5,z6])],[(0,[z0,z1,z736,z4,z5,z6]),(0,[z92,z1,z16,z36,z5,z6]),(0,[z0,z1,z2,z737,z5,z6]),(0,[z738,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z12,z161,z6])],[(0,[z0,z394,z2,z21,z5,z6]),(0,[z101,z0,z2,z172,z5,z28]),(0,[z212,z1,z2,z4,z190,z6])],[(0,[z1,z73,z61,z4,z5,z6]),(0,[z17,z1,z2,z4,z112,z6]),(0,[z0,z43,z29,z5,z6,z133]),(0,[z0,z109,z2,z21,z5,z6]),(0,[z0,z2,z21,z477,z5,z6]),(0,[z0,z109,z2,z4,z5,z291]),(0,[z739,z1,z2,z4,z5,z6]),(0,[z0,z59,z2,z207,z5,z6]),(0,[z0,z1,z740,z4,z5,z6])],[(0,[z297,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z741,z5,z6]),(0,[z742,z1,z2,z4,z5,z6])],[(0,[z13,z499,z2,z4,z5,z6]),(0,[z25,z390,z2,z4,z5,z6]),(0,[z0,z629,z2,z29,z5,z6]),(0,[z0,z1,z2,z266,z5,z117]),(0,[z0,z33,z87,z4,z5,z6])],[(0,[z25,z1,z2,z743,z5,z6]),(0,[z1,z2,z4,z744,z5,z6]),(0,[z25,z1,z35,z156,z5,z6]),(0,[z745,z1,z2,z4,z5,z6])],[(0,[z0,z1,z746,z4,z5,z6]),(0,[z747,z1,z2,z4,z5,z6]),(0,[z74,z0,z43,z4,z5,z6]),(0,[z0,z109,z2,z29,z5,z6]),(0,[z1,z23,z43,z4,z5,z6]),(0,[z675,z0,z2,z29,z5,z6]),(0,[z0,z33,z2,z4,z5,z56]),(0,[z58,z1,z2,z4,z5,z423])],[(0,[z1,z61,z4,z20,z5,z6]),(0,[z25,z2,z43,z29,z5,z6]),(0,[z48,z25,z1,z2,z5,z142]),(0,[z116,z0,z1,z2,z21,z6]),(0,[z0,z1,z4,z5,z748,z6]),(0,[z749,z1,z2,z4,z5,z6])],[(0,[z1,z105,z750,z4,z5,z6]),(0,[z17,z1,z2,z21,z18,z6]),(0,[z68,z0,z2,z4,z76,z6]),(0,[z1,z2,z4,z5,z751,z6])],[(0,[z0,z14,z2,z4,z5,z263]),(0,[z1,z2,z750,z4,z5,z6]),(0,[z25,z1,z2,z411,z5,z6]),(0,[z581,z0,z2,z29,z5,z6]),(0,[z319,z0,z2,z4,z76,z6]),(0,[z121,z1,z2,z4,z357,z6])],[(0,[z206,z0,z2,z29,z5,z6]),(0,[z0,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z161,z205])],[],[(0,[z259,z1,z16,z4,z5,z6]),(0,[z17,z1,z2,z29,z18,z6]),(0,[z752,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z753,z6]),(0,[z0,z1,z2,z754,z5,z6]),(0,[z48,z0,z1,z2,z190,z142])],[(0,[z25,z528,z2,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z527]),(0,[z0,z1,z2,z4,z5,z755]),(0,[z0,z1,z2,z4,z756,z6]),(0,[z0,z1,z2,z4,z757,z6]),(0,[z0,z528,z2,z758,z5,z6]),(0,[z24,z0,z501,z2,z161,z6]),(0,[z759,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z760,z4,z5,z6])],[(0,[z0,z1,z2,z4,z26,z505]),(0,[z0,z1,z2,z4,z5,z205])],[(0,[z33,z16,z43,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z423]),(0,[z0,z1,z2,z29,z5,z148]),(0,[z326,z1,z2,z21,z5,z6]),(0,[z761,z1,z2,z4,z5,z6]),(0,[z0,z762,z2,z4,z5,z6])],[(0,[z57,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z763,z5,z6]),(0,[z0,z1,z2,z764,z5,z6]),(0,[z452,z1,z2,z275,z5,z6]),(0,[z0,z1,z2,z765,z5,z6]),(0,[z297,z1,z2,z266,z5,z6]),(0,[z0,z1,z224,z400,z5,z6]),(0,[z24,z0,z1,z2,z161,z205])],[(0,[z0,z1,z2,z4,z5,z766])],[(0,[z1,z2,z352,z125,z5,z6]),(0,[z0,z528,z2,z767,z5,z6]),(0,[z104,z0,z265,z4,z5,z133])],[(0,[z217,z1,z2,z119,z5,z6]),(0,[z0,z1,z2,z4,z768,z6]),(0,[z92,z0,z1,z245,z5,z6]),(0,[z0,z1,z2,z36,z5,z291])],[(0,[z1,z2,z4,z769,z5,z6]),(0,[z0,z770,z2,z4,z5,z6]),(0,[z0,z90,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z163,z6]),(0,[z771,z1,z2,z4,z5,z6]),(0,[z772,z1,z2,z4,z5,z6])],[(0,[z1,z16,z4,z5,z566,z6]),(0,[z1,z2,z23,z4,z5,z6]),(0,[z773,z0,z1,z2,z4,z6]),(0,[z0,z2,z29,z5,z27,z28]),(0,[z0,z362,z2,z29,z5,z6]),(0,[z0,z1,z774,z4,z5,z6]),(0,[z22,z0,z1,z21,z139,z6]),(0,[z0,z1,z2,z4,z775,z6])],[(0,[z0,z177,z2,z29,z5,z6]),(0,[z690,z0,z43,z4,z5,z6]),(0,[z0,z2,z43,z32,z5,z6]),(0,[z728,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z32,z5,z6]),(0,[z375,z1,z2,z4,z45,z6])],[(0,[z0,z231,z2,z29,z5,z6]),(0,[z1,z559,z16,z4,z5,z6]),(0,[z25,z1,z2,z10,z5,z6]),(0,[z716,z1,z2,z29,z5,z6]),(0,[z279,z1,z2,z4,z5,z28])],[(0,[z253,z1,z61,z4,z5,z6]),(1,[z0,z2,z29,z112,z6]),(0,[z419,z16,z43,z4,z5,z6]),(0,[z0,z1,z2,z776,z5,z6]),(0,[z0,z1,z2,z777,z5,z6]),(0,[z0,z1,z2,z778,z5,z6])],[(0,[z0,z1,z779,z4,z5,z6]),(0,[z25,z1,z2,z461,z5,z6]),(0,[z58,z1,z2,z4,z5,z6]),(0,[z0,z780,z2,z4,z5,z6]),(0,[z104,z227,z1,z4,z5,z133])],[(0,[z0,z1,z2,z4,z5,z781]),(0,[z9,z2,z4,z81,z76,z6]),(0,[z0,z1,z2,z102,z173,z6]),(0,[z22,z0,z1,z239,z139,z6]),(0,[z0,z1,z2,z4,z5,z782])],[(0,[z0,z1,z2,z4,z5,z783]),(0,[z0,z2,z29,z76,z6,z31]),(0,[z104,z0,z1,z29,z5,z133]),(0,[z375,z1,z2,z4,z78,z6]),(0,[z455,z0,z1,z36,z5,z6])],[(0,[z0,z2,z784,z29,z5,z6]),(0,[z1,z2,z722,z29,z5,z6]),(0,[z0,z1,z2,z785,z5,z6])]],
   [[(0,[z390,z2,z16,z4,z5,z6]),(0,[z0,z1,z786,z4,z5,z6]),(0,[z656,z0,z43,z4,z5,z6])],[(0,[z25,z1,z2,z433,z5,z6]),(0,[z0,z1,z2,z433,z112,z6]),(0,[z0,z787,z2,z4,z5,z6]),(0,[z0,z64,z2,z788,z5,z6]),(0,[z69,z0,z1,z210,z5,z6]),(0,[z0,z14,z2,z34,z5,z6]),(0,[z212,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z173,z56]),(0,[z22,z46,z1,z4,z139,z6])],[(0,[z100,z1,z2,z4,z112,z6]),(0,[z1,z2,z16,z4,z5,z205]),(0,[z789,z1,z2,z4,z5,z6]),(0,[z0,z2,z29,z5,z91,z6]),(0,[z0,z2,z4,z5,z790,z6]),(0,[z212,z390,z2,z4,z5,z6])],[(0,[z25,z1,z2,z269,z5,z6]),(0,[z25,z1,z2,z4,z791,z5]),(0,[z202,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z792,z5,z6]),(0,[z612,z0,z1,z4,z5,z133]),(0,[z296,z0,z1,z4,z5,z133]),(0,[z218,z1,z2,z4,z5,z468])],[(0,[z1,z16,z4,z5,z590,z6]),(0,[z0,z2,z21,z543,z5,z6]),(0,[z250,z1,z330,z4,z5,z6]),(0,[z793,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z5,z161,z6])],[(0,[z158,z0,z2,z29,z5,z6]),(0,[z116,z25,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z794,z6]),(0,[z0,z1,z2,z795,z5,z6]),(0,[z0,z109,z2,z4,z5,z6]),(0,[z1,z132,z162,z4,z5,z6]),(0,[z212,z1,z2,z29,z5,z6]),(0,[z0,z1,z193,z21,z5,z6]),(0,[z227,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z748,z6]),(0,[z796,z1,z2,z4,z5,z6])],[(0,[z297,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z116,z0,z1,z2,z4,z6]),(0,[z0,z160,z2,z21,z5,z6]),(0,[z0,z160,z2,z4,z5,z291]),(0,[z798,z1,z2,z4,z5,z6]),(0,[z121,z420,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z799,z6]),(0,[z1,z153,z800,z4,z5,z6]),(0,[z1,z2,z801,z4,z5,z6])],[(0,[z13,z576,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z802]),(0,[z0,z1,z2,z803,z5,z6])],[(0,[z0,z1,z2,z4,z804,z6]),(0,[z1,z37,z16,z4,z70,z6]),(0,[z25,z1,z105,z21,z5,z6]),(0,[z67,z1,z2,z4,z5,z652]),(0,[z805,z1,z2,z4,z5,z6])],[(0,[z0,z2,z171,z29,z5,z6]),(0,[z0,z1,z193,z29,z5,z6]),(0,[z0,z33,z2,z806,z5,z6]),(0,[z227,z1,z2,z29,z5,z6]),(0,[z0,z1,z807,z21,z5,z6]),(0,[z22,z218,z1,z4,z139,z6]),(0,[z0,z1,z265,z4,z5,z133])],[(0,[z0,z1,z808,z4,z5,z6]),(0,[z152,z73,z2,z4,z5,z6]),(0,[z1,z2,z16,z32,z5,z6]),(0,[z97,z1,z2,z125,z5,z6]),(0,[z0,z160,z2,z29,z5,z6]),(0,[z47,z257,z1,z2,z4,z26])],[(0,[z0,z1,z2,z4,z809,z6]),(0,[z0,z1,z2,z21,z5,z229]),(0,[z810,z1,z2,z21,z5,z6]),(0,[z17,z1,z2,z4,z18,z6]),(0,[z0,z165,z2,z4,z267,z6]),(0,[z0,z1,z193,z411,z5,z6])],[(0,[z25,z1,z503,z4,z5,z6]),(0,[z2,z16,z4,z811,z5,z6]),(0,[z25,z1,z105,z29,z5,z6]),(0,[z0,z2,z704,z29,z5,z6])],[(0,[z0,z1,z2,z21,z173,z6]),(0,[z1,z2,z812,z4,z5,z6]),(0,[z813,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z814]),(0,[z583,z1,z2,z183,z5,z6]),(0,[z0,z2,z29,z5,z6,z28]),(0,[z0,z33,z2,z29,z5,z56]),(0,[z0,z1,z2,z140,z5,z6]),(0,[z0,z420,z2,z4,z11,z6])],[(0,[z0,z1,z2,z147,z5,z6]),(0,[z0,z1,z2,z4,z5,z148]),(0,[z0,z2,z43,z4,z5,z148]),(0,[z306,z0,z2,z29,z5,z6]),(0,[z375,z1,z2,z21,z5,z6]),(0,[z375,z1,z2,z4,z5,z291])]],
   [[(0,[z0,z1,z2,z4,z5,z815]),(0,[z816,z1,z2,z4,z5,z6]),(0,[z817,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z818,z5,z6])],[(0,[z0,z1,z819,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z820]),(0,[z0,z1,z2,z4,z821,z31])],[(0,[z1,z2,z4,z822,z5,z6]),(0,[z823,z0,z1,z2,z4,z6]),(0,[z250,z1,z2,z29,z5,z6]),(0,[z0,z59,z2,z29,z5,z6]),(0,[z101,z186,z2,z4,z5,z28])],[(0,[z101,z2,z16,z4,z5,z28]),(0,[z130,z1,z2,z4,z344,z6]),(0,[z1,z2,z159,z29,z5,z6]),(0,[z1,z2,z21,z824,z5,z6]),(0,[z1,z2,z21,z825,z5,z6]),(0,[z101,z0,z87,z4,z5,z28]),(0,[z0,z189,z2,z4,z70,z6]),(0,[z1,z2,z4,z826,z5,z6]),(0,[z827,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z828,z6]),(0,[z601,z1,z2,z4,z5,z27]),(0,[z0,z1,z2,z4,z163,z6]),(0,[z0,z2,z43,z4,z163,z6]),(0,[z345,z2,z29,z5,z76,z6]),(0,[z250,z1,z2,z411,z5,z6])],[(0,[z25,z1,z2,z4,z5,z578]),(0,[z0,z1,z829,z4,z5,z6]),(0,[z830,z1,z2,z4,z5,z6]),(0,[z382,z0,z1,z2,z5,z142]),(0,[z831,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z125,z112,z6]),(0,[z0,z1,z2,z832,z5,z6]),(0,[z25,z1,z2,z34,z5,z6]),(0,[z833,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z834,z6]),(0,[z180,z1,z141,z4,z5,z6])],[(0,[z647,z0,z2,z4,z76,z6])],[(0,[z15,z1,z2,z4,z5,z263]),(0,[z1,z2,z16,z4,z835,z6]),(0,[z22,z25,z1,z4,z139,z6]),(0,[z0,z1,z2,z836,z5,z6]),(0,[z0,z1,z4,z5,z782,z133])],[(0,[z282,z0,z43,z4,z5,z6]),(0,[z0,z33,z2,z4,z5,z389]),(0,[z0,z87,z4,z5,z6,z28])],[(0,[z0,z1,z2,z837,z5,z6]),(0,[z25,z2,z21,z29,z5,z6]),(0,[z0,z1,z838,z4,z5,z6]),(0,[z345,z1,z2,z4,z6,z31]),(0,[z0,z1,z579,z156,z5,z6]),(0,[z22,z0,z1,z4,z139,z432])],[(0,[z1,z2,z839,z4,z5,z6]),(0,[z1,z2,z191,z4,z20,z6]),(0,[z520,z1,z16,z4,z5,z6]),(0,[z0,z2,z318,z29,z5,z6]),(0,[z0,z2,z788,z29,z5,z6]),(0,[z104,z0,z1,z4,z5,z133]),(0,[z1,z2,z4,z5,z6,z840]),(0,[z0,z59,z2,z4,z5,z423])],[(0,[z841,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z11,z133])],[(0,[z0,z1,z842,z4,z5,z6]),(0,[z0,z843,z2,z4,z5,z6]),(0,[z0,z844,z2,z4,z5,z6]),(0,[z0,z2,z29,z195,z5,z6]),(0,[z0,z845,z2,z4,z5,z6]),(0,[z48,z212,z1,z2,z5,z142]),(0,[z846,z1,z2,z4,z5,z6])],[(0,[z25,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z29,z847,z6]),(0,[z0,z1,z2,z848,z5,z6]),(0,[z849,z1,z2,z4,z5,z6]),(0,[z268,z0,z1,z2,z5,z387]),(0,[z0,z1,z2,z4,z850,z6]),(0,[z0,z1,z49,z4,z5,z208]),(0,[z47,z93,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z851,z6]),(0,[z1,z2,z16,z140,z5,z6]),(0,[z0,z852,z2,z4,z5,z6]),(0,[z0,z1,z2,z29,z5,z117]),(0,[z57,z1,z264,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z113,z229]),(0,[z202,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z147,z5,z6]),(0,[z1,z2,z16,z4,z5,z148]),(0,[z501,z2,z16,z4,z5,z6])],[(0,[z0,z1,z2,z853,z5,z6]),(0,[z0,z134,z2,z29,z5,z6]),(0,[z0,z1,z2,z854,z5,z6]),(0,[z1,z2,z855,z4,z5,z6]),(0,[z486,z1,z2,z4,z190,z6])],[(0,[z0,z1,z856,z4,z5,z6]),(0,[z212,z1,z2,z4,z5,z6]),(0,[z1,z2,z857,z4,z5,z6]),(0,[z858,z1,z2,z4,z5,z6])],[(0,[z13,z0,z61,z29,z5,z6]),(0,[z0,z1,z2,z21,z154,z6]),(0,[z250,z1,z2,z10,z5,z6]),(0,[z859,z1,z2,z4,z5,z6]),(0,[z104,z0,z1,z456,z5,z133])],[(0,[z0,z289,z2,z29,z5,z6]),(0,[z0,z1,z2,z860,z5,z6]),(0,[z0,z2,z29,z5,z225,z6]),(0,[z861,z1,z2,z21,z5,z6]),(0,[z1,z2,z4,z5,z862,z6]),(0,[z0,z390,z2,z4,z154,z6])],[(0,[z1,z2,z16,z4,z163,z6]),(0,[z0,z1,z863,z4,z5,z6]),(0,[z0,z2,z617,z29,z5,z28]),(0,[z0,z1,z864,z29,z5,z6]),(0,[z170,z0,z1,z2,z5,z378]),(0,[z1,z2,z865,z21,z5,z6]),(0,[z1,z2,z866,z4,z5,z6])],[(0,[z227,z1,z2,z4,z5,z6]),(0,[z1,z642,z16,z4,z5,z6]),(0,[z0,z1,z2,z867,z5,z6]),(0,[z0,z1,z193,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z868]),(0,[z1,z2,z4,z869,z5,z6])],[(0,[z1,z346,z16,z4,z5,z6]),(0,[z292,z1,z2,z4,z66,z6]),(0,[z0,z160,z2,z4,z5,z6]),(0,[z0,z2,z29,z5,z6,z232]),(0,[z217,z2,z21,z29,z5,z6]),(0,[z0,z1,z2,z29,z154,z6])],[(0,[z870,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z871,z5,z6]),(0,[z323,z0,z1,z4,z5,z133]),(0,[z0,z1,z872,z4,z5,z6])],[(0,[z25,z1,z105,z4,z5,z6])],[(0,[z25,z189,z2,z4,z5,z6]),(0,[z414,z0,z1,z2,z4,z31]),(0,[z0,z2,z29,z18,z76,z6]),(0,[z0,z1,z807,z4,z5,z6])],[(0,[z13,z873,z2,z4,z5,z6]),(0,[z0,z685,z2,z29,z5,z6]),(0,[z1,z2,z874,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z229]),(0,[z810,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z875,z6]),(0,[z297,z1,z2,z29,z5,z6]),(0,[z386,z0,z1,z4,z5,z133]),(0,[z217,z14,z2,z21,z5,z6]),(0,[z0,z1,z2,z21,z51,z31]),(0,[z0,z1,z2,z876,z5,z6]),(0,[z0,z1,z2,z4,z469,z31]),(0,[z0,z1,z4,z140,z5,z133]),(0,[z24,z0,z59,z2,z161,z6])],[(0,[z181,z1,z2,z4,z877,z6]),(0,[z0,z1,z2,z4,z592,z31]),(0,[z48,z0,z1,z49,z5,z142]),(0,[z48,z0,z1,z2,z5,z142]),(0,[z1,z2,z878,z4,z5,z6])],[(0,[z74,z16,z43,z4,z5,z6]),(0,[z1,z2,z879,z4,z5,z6]),(0,[z158,z0,z2,z341,z5,z6]),(0,[z1,z2,z4,z5,z6,z880]),(0,[z227,z1,z2,z456,z5,z6]),(0,[z0,z265,z2,z4,z5,z133])],[(0,[z250,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z881,z5,z6]),(0,[z254,z1,z16,z4,z5,z6]),(0,[z0,z1,z193,z4,z5,z459]),(0,[z0,z1,z37,z4,z439,z6])]],
   [[(0,[z97,z1,z2,z882,z5,z6]),(0,[z1,z2,z4,z19,z175,z5]),(0,[z0,z2,z461,z5,z6,z28]),(0,[z0,z2,z29,z5,z262,z6]),(0,[z883,z1,z2,z4,z5,z6]),(0,[z884,z1,z2,z4,z5,z6])],[(0,[z0,z14,z2,z269,z5,z6]),(0,[z0,z1,z2,z885,z5,z6]),(0,[z0,z1,z330,z4,z76,z6])],[(0,[z25,z1,z264,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z468]),(1,[z0,z189,z4,z139,z6]),(0,[z212,z285,z2,z4,z5,z6])],[(0,[z0,z1,z2,z886,z5,z6]),(0,[z833,z1,z2,z4,z5,z6])],[(0,[z88,z1,z2,z21,z5,z6]),(0,[z88,z1,z2,z4,z5,z291])],[(0,[z887,z1,z153,z4,z5,z6]),(0,[z48,z0,z1,z153,z5,z142])],[(0,[z888,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z29,z5,z468]),(0,[z0,z1,z2,z21,z357,z6]),(0,[z889,z1,z2,z4,z5,z6]),(0,[z58,z1,z2,z4,z5,z205]),(0,[z1,z2,z4,z890,z5,z6])],[(0,[z610,z1,z2,z4,z5,z365]),(0,[z891,z1,z2,z4,z5,z6]),(0,[z0,z2,z512,z29,z76,z6]),(0,[z0,z1,z2,z239,z5,z468])],[(0,[z1,z672,z16,z4,z5,z6]),(0,[z88,z1,z2,z29,z5,z6]),(0,[z250,z1,z2,z4,z5,z459]),(0,[z0,z892,z2,z4,z5,z6]),(0,[z92,z0,z1,z36,z45,z6])],[(0,[z893,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z652]),(0,[z0,z1,z2,z894,z5,z6]),(0,[z326,z1,z2,z29,z5,z6])],[(0,[z1,z16,z4,z260,z5,z6]),(0,[z228,z0,z1,z2,z5,z142])],[(0,[z1,z2,z4,z5,z81,z6]),(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z896,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z897,z6]),(0,[z0,z33,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z847,z6]),(0,[z0,z33,z2,z34,z5,z56]),(0,[z1,z2,z4,z175,z5,z56]),(0,[z0,z1,z35,z898,z5,z6])],[(0,[z0,z1,z2,z4,z5,z117]),(0,[z0,z59,z2,z108,z5,z6])],[(0,[z0,z1,z2,z4,z899,z6]),(0,[z900,z1,z2,z4,z5,z6]),(0,[z92,z88,z1,z36,z5,z6]),(0,[z92,z0,z1,z36,z78,z6]),(0,[z1,z2,z901,z4,z5,z6])],[(0,[z72,z1,z61,z4,z5,z6]),(0,[z0,z2,z29,z5,z287,z6]),(0,[z285,z2,z16,z4,z5,z6]),(0,[z902,z1,z2,z4,z5,z6]),(0,[z0,z1,z903,z4,z5,z6]),(0,[z0,z1,z2,z5,z904,z142])],[(0,[z22,z0,z1,z29,z139,z6]),(0,[z308,z0,z2,z29,z5,z6]),(0,[z486,z1,z2,z21,z5,z6]),(0,[z905,z1,z2,z4,z5,z6]),(0,[z47,z1,z2,z4,z26,z175])]],
   [[(0,[z25,z1,z2,z4,z5,z205]),(0,[z0,z1,z2,z906,z5,z6]),(0,[z74,z0,z43,z4,z5,z148]),(0,[z907,z1,z2,z29,z5,z6]),(0,[z92,z0,z160,z36,z5,z6]),(0,[z486,z390,z2,z4,z5,z6]),(0,[z0,z908,z2,z4,z5,z6])],[(0,[z0,z1,z2,z909,z5,z6]),(0,[z101,z279,z2,z4,z5,z28])],[(0,[z0,z1,z2,z4,z5,z910]),(0,[z1,z16,z704,z4,z5,z6]),(0,[z1,z35,z16,z156,z5,z6]),(0,[z0,z2,z29,z5,z298,z6]),(0,[z911,z1,z2,z29,z5,z6]),(0,[z0,z1,z864,z4,z5,z6])],[(0,[z315,z1,z2,z4,z5,z27]),(0,[z0,z413,z2,z29,z5,z6]),(0,[z486,z1,z2,z29,z5,z6]),(0,[z9,z250,z2,z4,z76,z6]),(1,[z0,z330,z4,z76,z6]),(0,[z0,z1,z2,z912,z5,z6])],[(0,[z0,z1,z2,z913,z5,z6]),(0,[z1,z2,z16,z886,z5,z6]),(0,[z0,z1,z2,z914,z5,z6]),(0,[z0,z2,z636,z29,z5,z6]),(0,[z15,z1,z2,z4,z5,z615]),(0,[z0,z1,z2,z21,z19,z5]),(0,[z0,z1,z2,z4,z154,z6])],[(0,[z74,z0,z43,z4,z163,z6]),(0,[z0,z1,z2,z915,z5,z6]),(0,[z1,z2,z162,z21,z5,z6]),(0,[z1,z193,z916,z4,z5,z6]),(0,[z917,z1,z2,z4,z5,z6])],[(0,[z0,z1,z918,z4,z5,z6]),(0,[z919,z1,z2,z4,z5,z6]),(0,[z0,z64,z43,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z920]),(0,[z0,z1,z2,z21,z5,z921]),(0,[z1,z2,z865,z4,z5,z6])],[(0,[z1,z16,z286,z4,z5,z6]),(0,[z0,z1,z2,z4,z922,z6]),(0,[z116,z67,z1,z2,z4,z86]),(0,[z74,z297,z43,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z923]),(0,[z924,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z925]),(0,[z104,z0,z420,z4,z5,z133]),(0,[z1,z2,z926,z4,z5,z6])],[(0,[z16,z43,z4,z29,z5,z6]),(0,[z0,z2,z4,z811,z5,z6]),(0,[z25,z1,z2,z32,z5,z6]),(0,[z0,z2,z4,z927,z5,z6]),(0,[z0,z1,z2,z29,z19,z5]),(0,[z0,z1,z2,z4,z5,z928]),(0,[z1,z87,z879,z4,z5,z6]),(0,[z929,z1,z2,z4,z5,z6]),(0,[z0,z189,z2,z737,z5,z6]),(0,[z930,z1,z2,z4,z5,z6]),(0,[z931,z1,z2,z4,z5,z6]),(0,[z0,z265,z2,z4,z357,z6])],[(0,[z0,z1,z346,z4,z5,z229]),(0,[z72,z873,z2,z4,z5,z6]),(0,[z53,z1,z2,z4,z5,z525]),(0,[z0,z1,z2,z932,z5,z6]),(0,[z0,z933,z43,z4,z5,z6]),(0,[z0,z2,z411,z5,z76,z6]),(0,[z0,z1,z2,z934,z5,z6])],[(0,[z0,z935,z2,z4,z5,z6]),(0,[z1,z2,z29,z5,z81,z6])],[(0,[z0,z1,z936,z4,z5,z6]),(0,[z97,z0,z2,z341,z5,z6]),(0,[z0,z1,z2,z21,z5,z527]),(0,[z0,z43,z4,z5,z28,z133]),(0,[z937,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z938,z5,z6]),(0,[z282,z0,z1,z4,z139,z6])],[(0,[z0,z1,z2,z939,z5,z6]),(0,[z0,z1,z940,z29,z5,z6]),(0,[z1,z2,z941,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z117]),(0,[z186,z1,z2,z4,z5,z27]),(0,[z942,z1,z2,z4,z5,z6]),(0,[z332,z0,z2,z29,z5,z6]),(0,[z217,z14,z2,z4,z5,z6]),(0,[z0,z1,z467,z156,z5,z6]),(0,[z48,z486,z1,z2,z5,z142]),(0,[z0,z1,z2,z4,z51,z31])],[(0,[z0,z1,z2,z943,z5,z6]),(0,[z0,z944,z2,z4,z5,z6]),(0,[z0,z33,z2,z461,z5,z6])],[(0,[z0,z1,z2,z4,z945,z6]),(0,[z0,z1,z2,z29,z5,z527]),(0,[z0,z1,z82,z4,z5,z782])]],
   [[(0,[z0,z1,z2,z4,z5,z946]),(0,[z0,z1,z2,z4,z5,z947])],[(0,[z0,z1,z948,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z949]),(0,[z0,z420,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z536,z31])],[(0,[z0,z1,z2,z29,z5,z229]),(0,[z1,z82,z16,z4,z5,z30]),(0,[z181,z257,z1,z2,z4,z6]),(0,[z116,z67,z1,z2,z4,z6])],[(0,[z950,z1,z2,z4,z5,z6]),(0,[z319,z0,z43,z4,z5,z6]),(0,[z0,z1,z2,z29,z951,z6]),(0,[z0,z1,z2,z952,z5,z6]),(0,[z0,z1,z2,z4,z5,z468]),(0,[z953,z1,z2,z4,z5,z6])],[(0,[z72,z2,z29,z5,z18,z6]),(0,[z1,z2,z589,z119,z5,z6]),(0,[z25,z109,z2,z4,z5,z6]),(0,[z0,z646,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z173,z6]),(0,[z101,z0,z2,z102,z5,z28]),(0,[z0,z33,z2,z4,z5,z954]),(0,[z0,z285,z2,z4,z154,z6])],[(0,[z25,z1,z2,z4,z112,z6]),(0,[z1,z73,z2,z4,z5,z263]),(0,[z1,z96,z16,z4,z5,z6]),(0,[z1,z2,z16,z4,z154,z6]),(0,[z88,z1,z2,z4,z5,z6]),(0,[z25,z1,z471,z4,z5,z6]),(1,[z345,z2,z29,z5,z6]),(0,[z0,z420,z2,z29,z5,z6]),(0,[z955,z1,z2,z21,z5,z6]),(0,[z956,z1,z2,z4,z5,z6]),(0,[z0,z1,z457,z156,z5,z6])],[(0,[z326,z1,z2,z4,z5,z6]),(0,[z169,z1,z2,z213,z5,z6]),(0,[z1,z2,z21,z744,z5,z6]),(0,[z375,z1,z2,z29,z5,z6])],[(0,[z957,z1,z2,z4,z5,z6]),(0,[z0,z109,z2,z4,z5,z578]),(0,[z958,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z357,z6]),(0,[z0,z1,z2,z959,z5,z6])],[(0,[z1,z2,z4,z5,z86,z263]),(0,[z1,z960,z2,z4,z5,z6]),(0,[z1,z2,z961,z4,z5,z6]),(0,[z0,z1,z2,z962,z5,z6]),(0,[z0,z1,z2,z963,z5,z6]),(0,[z964,z1,z2,z4,z5,z6]),(0,[z101,z0,z2,z4,z5,z954]),(0,[z965,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z966,z5,z6])],[(0,[z0,z1,z967,z4,z5,z6]),(0,[z13,z73,z2,z4,z5,z229]),(0,[z0,z1,z49,z4,z190,z6]),(0,[z968,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z797,z5,z6])],[(0,[z0,z1,z2,z4,z5,z969])],[(0,[z1,z2,z916,z4,z5,z6]),(0,[z1,z2,z4,z970,z5,z6]),(0,[z0,z971,z2,z4,z5,z6]),(0,[z22,z0,z1,z4,z139,z6])],[(0,[z1,z2,z4,z5,z6,z126]),(0,[z103,z2,z4,z5,z298,z6]),(0,[z25,z2,z29,z5,z6,z28]),(0,[z25,z1,z2,z140,z5,z6]),(0,[z0,z972,z2,z4,z5,z6]),(0,[z0,z2,z29,z5,z371,z6]),(0,[z907,z1,z2,z4,z5,z6]),(0,[z0,z1,z193,z10,z5,z6]),(0,[z0,z109,z2,z156,z5,z6])],[(0,[z1,z2,z21,z973,z5,z6]),(0,[z593,z1,z16,z4,z5,z6]),(0,[z25,z1,z2,z147,z5,z6]),(0,[z25,z1,z2,z4,z5,z148]),(0,[z0,z1,z2,z4,z5,z974]),(0,[z1,z2,z4,z5,z6,z975]),(1,[z0,z265,z4,z5,z133])],[(0,[z1,z141,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z815]),(0,[z0,z2,z29,z5,z377,z6]),(0,[z911,z1,z2,z4,z5,z6]),(0,[z92,z375,z1,z36,z5,z6]),(0,[z0,z1,z2,z4,z5,z976])]],
   [[(0,[z0,z1,z2,z4,z5,z977]),(0,[z486,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z0,z1,z87,z172,z5,z6]),(0,[z0,z1,z82,z140,z5,z6])],[(0,[z0,z1,z2,z4,z979,z6]),(0,[z0,z1,z2,z980,z5,z6]),(0,[z249,z1,z2,z21,z5,z6]),(0,[z9,z249,z2,z4,z76,z6]),(0,[z491,z0,z1,z4,z139,z6])],[(0,[z25,z14,z2,z21,z5,z6]),(0,[z981,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z788,z5,z6]),(0,[z257,z1,z2,z21,z5,z6]),(0,[z9,z345,z2,z4,z76,z6]),(0,[z1,z2,z800,z4,z5,z6])],[(0,[z1,z2,z4,z20,z112,z6]),(0,[z25,z1,z2,z4,z163,z6]),(0,[z0,z1,z2,z21,z5,z982]),(0,[z0,z1,z2,z983,z5,z6])],[(0,[z476,z0,z1,z2,z161,z6]),(0,[z101,z0,z2,z21,z5,z28]),(0,[z0,z1,z4,z748,z139,z6])],[(0,[z0,z1,z2,z4,z19,z5]),(0,[z0,z2,z29,z20,z76,z6]),(0,[z249,z1,z2,z29,z5,z6]),(0,[z101,z0,z2,z4,z174,z28]),(0,[z24,z180,z1,z2,z161,z6])],[(0,[z0,z2,z509,z29,z5,z6])],[(0,[z0,z1,z2,z4,z5,z921]),(0,[z249,z1,z2,z411,z5,z6])],[(0,[z1,z2,z4,z175,z5,z6]),(0,[z101,z0,z2,z29,z5,z28]),(0,[z345,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z984])],[(0,[z583,z1,z2,z125,z5,z6]),(0,[z203,z0,z2,z29,z5,z6]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z0,z1,z2,z4,z139,z468]),(0,[z0,z59,z2,z4,z5,z205])],[(0,[z0,z1,z2,z433,z5,z229]),(0,[z1,z2,z4,z20,z410,z6]),(0,[z0,z1,z2,z29,z985,z6]),(0,[z986,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z987,z5,z6])],[(0,[z13,z2,z16,z29,z5,z6]),(0,[z9,z0,z193,z4,z76,z6])],[(0,[z0,z1,z2,z269,z5,z229]),(0,[z581,z73,z2,z4,z5,z6]),(0,[z490,z1,z2,z4,z568,z6]),(0,[z0,z1,z2,z4,z5,z527]),(0,[z0,z436,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z163,z148]),(0,[z1,z2,z4,z988,z5,z6]),(0,[z345,z1,z2,z29,z5,z6]),(0,[z1,z2,z29,z5,z6,z126]),(0,[z0,z1,z2,z29,z5,z920]),(0,[z0,z989,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z990]),(0,[z74,z0,z43,z4,z5,z117]),(0,[z0,z33,z2,z32,z5,z56])],[(0,[z0,z1,z2,z991,z5,z6]),(0,[z1,z2,z4,z992,z5,z6]),(0,[z0,z1,z49,z4,z5,z142])],[(0,[z13,z2,z4,z183,z5,z6]),(0,[z97,z1,z2,z354,z5,z6]),(0,[z0,z1,z2,z898,z5,z6])]],
   [[(0,[z0,z993,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z994,z5]),(0,[z1,z2,z4,z5,z6,z995]),(0,[z0,z1,z2,z29,z5,z996]),(0,[z0,z1,z2,z4,z951,z6]),(0,[z486,z285,z2,z4,z5,z6])],[(0,[z1,z204,z16,z4,z5,z6]),(0,[z1,z2,z4,z997,z5,z6]),(0,[z345,z2,z4,z29,z5,z6]),(0,[z0,z1,z2,z4,z173,z6])],[(0,[z25,z1,z664,z4,z5,z6]),(0,[z0,z420,z2,z4,z5,z6]),(0,[z998,z1,z2,z4,z5,z6]),(0,[z0,z1,z999,z4,z5,z6]),(0,[z0,z1,z2,z1000,z5,z6]),(0,[z0,z2,z4,z5,z56,z954]),(0,[z0,z1001,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1002,z5,z6]),(0,[z0,z1,z2,z1003,z5,z6]),(0,[z375,z1,z2,z4,z5,z6]),(0,[z0,z1004,z2,z4,z5,z6]),(0,[z201,z1,z2,z4,z5,z482]),(0,[z15,z1,z2,z4,z450,z5]),(0,[z0,z1,z2,z29,z51,z31]),(0,[z0,z1,z1005,z4,z5,z6]),(1,[z0,z1,z898,z5,z6])],[(0,[z14,z2,z16,z21,z5,z6]),(0,[z25,z1,z658,z4,z5,z6]),(0,[z0,z1,z933,z4,z5,z6]),(0,[z648,z0,z1,z4,z139,z6]),(0,[z0,z1,z1006,z4,z5,z6]),(0,[z92,z0,z109,z36,z5,z6]),(0,[z22,z0,z1,z151,z139,z6]),(0,[z0,z1,z2,z5,z6,z1007]),(0,[z58,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z1008,z5,z6])],[(0,[z0,z2,z341,z29,z5,z6]),(0,[z0,z2,z29,z5,z437,z6])],[(0,[z1,z61,z4,z5,z86,z6]),(0,[z25,z160,z2,z4,z5,z6]),(0,[z0,z2,z29,z5,z86,z28]),(0,[z955,z1,z2,z4,z5,z6]),(0,[z249,z1,z2,z10,z5,z6])],[(0,[z17,z1,z2,z4,z66,z6]),(0,[z1,z2,z29,z175,z5,z6]),(0,[z0,z1,z49,z21,z5,z6]),(0,[z0,z189,z2,z4,z5,z468])],[(0,[z265,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1009]),(0,[z0,z1,z2,z4,z179,z31]),(0,[z202,z1,z2,z4,z5,z148]),(0,[z1010,z1,z2,z4,z5,z6]),(0,[z0,z390,z49,z4,z5,z6])],[(0,[z0,z160,z2,z4,z5,z578])],[(0,[z0,z1,z2,z4,z1011,z6]),(0,[z25,z33,z2,z4,z5,z56]),(0,[z1012,z1,z2,z4,z5,z6]),(0,[z0,z420,z2,z456,z5,z6])],[(0,[z0,z1,z2,z1013,z5,z6]),(0,[z0,z1,z2,z4,z1014,z6]),(0,[z0,z1,z82,z4,z5,z481]),(0,[z0,z1,z49,z29,z5,z6]),(0,[z0,z1,z2,z4,z1015,z6])],[(0,[z392,z0,z2,z29,z5,z6])],[(0,[z0,z1,z2,z4,z1016,z5]),(0,[z0,z1,z2,z1017,z5,z6]),(0,[z202,z1,z2,z4,z163,z6]),(0,[z0,z1,z2,z29,z357,z6]),(0,[z48,z0,z390,z2,z5,z142])],[(0,[z626,z0,z2,z29,z5,z6]),(0,[z13,z2,z29,z183,z5,z6]),(0,[z25,z59,z2,z4,z5,z6])],[(0,[z1018,z2,z16,z4,z5,z6]),(0,[z0,z2,z29,z5,z6,z462]),(0,[z0,z1,z2,z1019,z5,z6]),(0,[z0,z1,z1020,z4,z5,z6]),(0,[z0,z1,z36,z5,z6,z291]),(0,[z613,z0,z1,z4,z139,z6]),(0,[z0,z528,z2,z4,z5,z468])]],
   [[(0,[z1,z2,z16,z4,z5,z229]),(0,[z0,z1,z2,z4,z1021,z6]),(0,[z1022,z1,z2,z4,z5,z6]),(0,[z0,z2,z403,z29,z5,z6]),(0,[z0,z1,z2,z21,z5,z631]),(0,[z143,z1,z2,z21,z5,z6]),(0,[z1023,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z239,z139,z6]),(0,[z0,z1,z2,z1024,z5,z6])],[(0,[z170,z0,z1,z2,z5,z142]),(0,[z0,z1,z2,z799,z161,z6]),(0,[z0,z1,z2,z4,z821,z51])],[(0,[z249,z1,z2,z4,z5,z6]),(0,[z1,z258,z16,z4,z5,z6]),(0,[z1,z2,z16,z4,z173,z6]),(0,[z0,z1,z2,z1025,z5,z6]),(0,[z0,z1,z2,z4,z1026,z6]),(0,[z0,z1,z2,z1027,z5,z6])],[(0,[z0,z14,z2,z4,z112,z6]),(0,[z0,z1028,z2,z4,z5,z6]),(0,[z1,z264,z16,z4,z5,z6]),(0,[z257,z1,z2,z4,z5,z6]),(0,[z74,z0,z43,z147,z5,z6]),(0,[z0,z2,z29,z76,z139,z6]),(0,[z677,z0,z2,z29,z5,z6]),(0,[z0,z2,z29,z5,z6,z475])],[(0,[z67,z72,z2,z29,z5,z6]),(0,[z101,z25,z2,z4,z5,z28]),(0,[z0,z1,z2,z29,z5,z631]),(0,[z143,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z982]),(0,[z1,z2,z1029,z4,z5,z6]),(0,[z0,z1,z1030,z4,z5,z6])],[(0,[z25,z1,z2,z765,z5,z6]),(0,[z0,z1,z2,z21,z6,z115]),(0,[z0,z1,z2,z1031,z5,z6]),(0,[z0,z1,z2,z4,z1032,z6]),(0,[z2,z29,z5,z6,z126,z28]),(0,[z101,z0,z2,z4,z5,z28]),(0,[z1033,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z29,z5,z1034]),(0,[z0,z1,z2,z21,z1035,z6]),(0,[z0,z1,z2,z411,z5,z631])],[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z0,z1,z2,z4,z985,z6])],[(0,[z1037,z1,z2,z4,z5,z6]),(0,[z861,z1,z2,z4,z5,z6])],[(0,[z345,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1038,z6]),(0,[z1,z2,z4,z19,z5,z27]),(0,[z0,z1,z2,z29,z6,z115]),(0,[z0,z1,z2,z1039,z5,z6]),(0,[z0,z1040,z2,z4,z5,z6])],[(0,[z1041,z1,z2,z4,z5,z6])],[(0,[z25,z1,z2,z4,z5,z117]),(0,[z1042,z1,z2,z4,z5,z6]),(0,[z1043,z1,z2,z4,z5,z6]),(0,[z986,z1,z2,z4,z5,z6]),(0,[z249,z1,z2,z4,z5,z459]),(0,[z279,z1,z2,z4,z173,z6])],[(0,[z345,z0,z2,z29,z5,z6]),(0,[z1,z2,z162,z29,z5,z6])],[(0,[z1,z2,z4,z112,z86,z6]),(0,[z15,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z5,z996])],[(0,[z0,z1,z2,z4,z5,z1044]),(0,[z0,z1,z2,z4,z1045,z5]),(0,[z25,z1,z479,z4,z5,z6]),(0,[z100,z1,z2,z429,z5,z6]),(0,[z0,z1,z153,z21,z5,z6]),(0,[z0,z1,z87,z102,z5,z6]),(0,[z1046,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1047]),(0,[z103,z1,z2,z4,z19,z5]),(0,[z67,z1,z2,z4,z175,z5]),(0,[z1048,z1,z2,z4,z5,z6])]],
   [[(0,[z472,z0,z2,z29,z5,z6]),(0,[z1049,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1050,z5,z6]),(0,[z92,z0,z1,z36,z5,z291])],[(0,[z131,z1,z2,z125,z5,z6]),(0,[z0,z1,z87,z4,z5,z56]),(0,[z1051,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1052]),(0,[z25,z72,z2,z29,z5,z6]),(0,[z546,z1,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z154,z6]),(0,[z67,z1,z2,z4,z5,z482]),(0,[z220,z1,z2,z4,z18,z6])],[(0,[z0,z1,z2,z1053,z5,z6]),(0,[z1054,z1,z2,z4,z5,z6]),(0,[z283,z0,z1,z2,z4,z26])],[(0,[z0,z1,z750,z4,z5,z6]),(0,[z0,z1,z2,z1055,z5,z6]),(0,[z1,z2,z374,z970,z5,z6])],[(0,[z223,z0,z2,z4,z5,z28]),(0,[z0,z1,z141,z21,z5,z6]),(0,[z180,z1,z12,z4,z5,z6])],[(0,[z13,z15,z2,z29,z5,z6]),(0,[z0,z342,z132,z4,z5,z6]),(0,[z1,z2,z1056,z4,z5,z6])],[(0,[z730,z1,z16,z4,z5,z6]),(0,[z0,z1,z49,z4,z5,z6]),(0,[z0,z1,z1057,z4,z5,z6])],[(0,[z0,z1,z61,z21,z5,z6]),(0,[z0,z1,z2,z4,z163,z117]),(0,[z0,z1,z2,z21,z1058,z6]),(0,[z0,z1,z2,z4,z26,z821])],[(0,[z0,z1,z141,z29,z5,z6]),(0,[z249,z1,z330,z4,z5,z6]),(0,[z0,z1,z2,z4,z173,z28])],[(0,[z1059,z1,z2,z4,z5,z6]),(0,[z0,z1,z36,z5,z45,z6]),(0,[z0,z1,z2,z1060,z5,z6])],[(0,[z13,z0,z2,z784,z5,z6]),(0,[z0,z1061,z2,z4,z5,z6]),(0,[z0,z1,z2,z1062,z5,z6])],[(0,[z0,z1,z61,z29,z5,z6]),(0,[z0,z1,z2,z4,z1063,z5]),(0,[z72,z2,z29,z5,z6,z27]),(0,[z14,z16,z43,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1064]),(0,[z0,z1,z2,z21,z138,z6]),(0,[z0,z1,z264,z4,z173,z6]),(0,[z1065,z1,z2,z4,z5,z6])],[(0,[z0,z2,z29,z5,z6,z531]),(0,[z0,z1,z87,z21,z5,z6]),(0,[z0,z1,z330,z4,z55,z6]),(0,[z1,z49,z1066,z4,z5,z6])],[(0,[z13,z0,z2,z246,z5,z6]),(0,[z0,z1067,z2,z4,z5,z6]),(0,[z0,z1,z87,z4,z174,z6]),(0,[z228,z0,z1,z36,z5,z6])]],
   [[(0,[z0,z1,z1068,z4,z5,z6]),(0,[z25,z1,z16,z21,z5,z6]),(0,[z0,z2,z4,z1069,z5,z6]),(0,[z1,z2,z1070,z4,z5,z6]),(0,[z0,z1,z49,z178,z5,z6])],[(0,[z0,z1,z2,z1071,z5,z6]),(0,[z1,z2,z16,z4,z51,z31]),(0,[z143,z1,z2,z4,z5,z6]),(0,[z67,z1,z2,z4,z5,z502]),(0,[z297,z1,z2,z147,z5,z6]),(0,[z297,z1,z2,z4,z5,z148]),(0,[z0,z1,z2,z29,z138,z6]),(0,[z0,z1,z2,z4,z5,z631]),(0,[z0,z1,z1072,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1073]),(0,[z1,z16,z4,z5,z6,z523]),(0,[z1,z2,z1074,z4,z5,z6]),(0,[z0,z1,z2,z456,z357,z6]),(0,[z1075,z1,z2,z4,z5,z6])],[(0,[z1076,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1034]),(0,[z120,z1,z2,z21,z5,z6]),(0,[z0,z1,z141,z4,z5,z423]),(0,[z1077,z1,z2,z4,z5,z6])],[(0,[z13,z73,z61,z4,z5,z6]),(0,[z25,z1,z16,z29,z5,z6]),(0,[z1,z2,z4,z1078,z5,z6]),(0,[z121,z1,z2,z21,z5,z6]),(0,[z121,z1,z2,z4,z11,z6])],[(0,[z13,z2,z125,z29,z5,z6]),(0,[z1,z2,z16,z1053,z5,z6]),(0,[z1079,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1080]),(0,[z67,z1,z2,z4,z19,z5]),(0,[z202,z1,z2,z4,z5,z117]),(0,[z0,z1,z2,z4,z1081,z6]),(0,[z1082,z1,z330,z4,z5,z6]),(0,[z0,z1083,z2,z4,z5,z6])],[(0,[z109,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z115]),(0,[z297,z1,z2,z4,z163,z6]),(0,[z0,z64,z132,z29,z5,z6]),(0,[z0,z1,z2,z1084,z5,z6])],[(0,[z1,z2,z16,z4,z5,z468]),(0,[z0,z82,z43,z29,z5,z6]),(0,[z0,z33,z2,z29,z5,z28]),(0,[z0,z1,z2,z4,z1035,z6]),(0,[z88,z1,z2,z4,z5,z578]),(0,[z0,z1085,z2,z4,z5,z6]),(0,[z143,z1,z2,z4,z5,z31])],[(0,[z16,z43,z4,z5,z6,z28]),(0,[z0,z109,z2,z36,z5,z6]),(0,[z0,z285,z49,z4,z5,z6])],[(0,[z0,z2,z29,z5,z112,z6]),(0,[z137,z1,z16,z21,z5,z6]),(0,[z1,z2,z162,z4,z5,z6]),(0,[z257,z1,z2,z29,z5,z6]),(0,[z1086,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1087,z6]),(0,[z0,z1,z2,z4,z5,z1088])],[(0,[z0,z1,z2,z4,z5,z1089]),(0,[z0,z1,z2,z147,z5,z148]),(0,[z238,z0,z2,z29,z5,z6]),(0,[z1,z2,z21,z5,z81,z6])],[(0,[z1,z2,z16,z4,z357,z6]),(0,[z0,z1,z2,z4,z5,z1090]),(0,[z0,z1,z2,z266,z138,z6])],[(0,[z1,z2,z191,z4,z384,z6]),(0,[z0,z75,z2,z29,z5,z6]),(0,[z1091,z1,z2,z4,z5,z6]),(0,[z104,z121,z1,z4,z5,z133]),(0,[z0,z1092,z2,z4,z5,z6])],[(0,[z581,z0,z2,z4,z76,z6]),(0,[z1093,z1,z2,z4,z5,z6])],[(0,[z0,z1,z61,z4,z113,z6]),(0,[z67,z1,z2,z4,z5,z618]),(0,[z1,z2,z4,z5,z1094,z6]),(0,[z1,z2,z1095,z21,z5,z6]),(0,[z1096,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z151,z5,z468])],[(0,[z1,z2,z16,z4,z5,z969]),(0,[z25,z844,z2,z4,z5,z6]),(0,[z181,z1,z2,z4,z20,z527]),(0,[z0,z2,z29,z5,z6,z574]),(0,[z0,z1,z2,z147,z163,z6]),(0,[z0,z1,z4,z36,z45,z6]),(0,[z0,z1,z153,z4,z5,z6])]],
   [[(0,[z15,z1,z2,z4,z112,z6]),(0,[z484,z0,z2,z4,z5,z28]),(0,[z1,z2,z1097,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1098]),(0,[z1,z16,z556,z4,z5,z6]),(0,[z1,z376,z16,z4,z5,z6]),(0,[z92,z25,z1,z36,z5,z6]),(0,[z380,z2,z4,z125,z5,z6]),(0,[z0,z1,z2,z1099,z5,z6])],[(0,[z1,z2,z16,z4,z5,z631]),(0,[z380,z2,z16,z4,z5,z6]),(0,[z0,z1,z1100,z4,z5,z6]),(0,[z180,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z172,z174,z6]),(0,[z92,z0,z1,z36,z5,z6]),(0,[z0,z1,z898,z36,z5,z6]),(0,[z0,z265,z2,z1101,z5,z6])],[(0,[z0,z1,z2,z1102,z5,z6]),(0,[z116,z103,z1,z2,z4,z6]),(0,[z0,z1103,z2,z4,z5,z6]),(0,[z0,z2,z529,z29,z5,z6]),(0,[z1,z2,z1104,z4,z5,z6]),(0,[z0,z1,z4,z5,z30,z782]),(0,[z0,z1,z153,z4,z190,z6])],[(0,[z0,z1,z61,z4,z5,z263]),(0,[z0,z1,z2,z1105,z5,z6]),(0,[z0,z1106,z2,z4,z5,z6]),(0,[z1107,z1,z2,z4,z5,z6])],[(0,[z181,z1,z2,z4,z6,z502]),(0,[z0,z1,z2,z4,z1108,z6]),(0,[z487,z0,z2,z29,z5,z6]),(0,[z1109,z1,z2,z4,z5,z6]),(0,[z104,z0,z1,z140,z5,z133])],[(0,[z1,z226,z16,z4,z5,z6]),(0,[z0,z1110,z2,z4,z5,z6]),(0,[z180,z1,z2,z29,z5,z6]),(0,[z0,z1,z1111,z4,z5,z6]),(0,[z121,z265,z2,z4,z5,z6])],[(0,[z0,z1,z61,z269,z5,z6]),(0,[z1,z2,z16,z4,z6,z115]),(0,[z253,z25,z2,z29,z5,z6]),(0,[z0,z1,z2,z1112,z5,z6]),(0,[z181,z1,z2,z4,z19,z20]),(0,[z0,z1,z2,z1113,z5,z6]),(0,[z1114,z1,z2,z4,z5,z6]),(0,[z0,z1,z141,z4,z5,z6]),(0,[z0,z1115,z2,z4,z5,z6]),(0,[z887,z1,z2,z4,z5,z6])],[(0,[z253,z0,z2,z29,z5,z6]),(0,[z25,z1,z193,z4,z5,z6]),(0,[z616,z1,z2,z125,z5,z6]),(0,[z417,z1,z2,z4,z5,z86]),(0,[z0,z1,z2,z403,z5,z6]),(0,[z0,z243,z2,z29,z5,z6]),(0,[z46,z1,z2,z4,z5,z432]),(0,[z1116,z1,z2,z4,z5,z6]),(0,[z493,z0,z1,z2,z4,z26])],[(0,[z1,z2,z16,z4,z19,z5]),(0,[z116,z257,z1,z2,z4,z6]),(0,[z0,z1,z330,z4,z5,z631]),(0,[z1117,z1,z87,z4,z5,z6]),(0,[z0,z1,z12,z4,z40,z6]),(0,[z1118,z1,z2,z4,z5,z6])],[(0,[z0,z1,z61,z4,z5,z6]),(0,[z0,z1,z1119,z4,z5,z6]),(0,[z0,z1,z2,z4,z1058,z6]),(0,[z0,z1,z2,z4,z5,z1120]),(0,[z0,z1,z197,z4,z70,z6])],[(0,[z13,z226,z2,z4,z5,z6]),(0,[z202,z1,z2,z147,z5,z6]),(0,[z0,z1,z2,z1121,z5,z6]),(0,[z0,z1,z2,z4,z1122,z6]),(0,[z0,z1,z2,z4,z190,z208]),(0,[z128,z0,z1,z2,z4,z31])],[(0,[z873,z73,z2,z4,z5,z6]),(0,[z187,z0,z2,z29,z5,z6]),(0,[z1,z2,z16,z4,z5,z1090]),(0,[z0,z1,z2,z1123,z5,z6])],[(0,[z25,z1,z247,z4,z5,z6]),(0,[z67,z0,z1,z2,z4,z115]),(0,[z0,z64,z2,z266,z5,z6]),(0,[z1,z2,z4,z5,z1124,z6]),(0,[z1125,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z112,z229]),(0,[z25,z1,z2,z4,z5,z229]),(0,[z0,z1,z2,z4,z138,z6]),(0,[z1,z2,z1126,z4,z5,z6]),(0,[z1127,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z1128,z5,z6]),(0,[z1129,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z16,z4,z5,z527]),(0,[z25,z1,z2,z4,z173,z6]),(0,[z218,z1,z2,z21,z5,z6]),(0,[z227,z1,z2,z140,z5,z6])],[(0,[z25,z1,z16,z4,z5,z6]),(0,[z25,z420,z2,z4,z5,z6])],[(0,[z1,z2,z242,z21,z5,z6])],[(0,[z0,z1130,z2,z4,z5,z6]),(0,[z2,z16,z29,z5,z76,z6]),(0,[z100,z1,z2,z213,z5,z6]),(0,[z0,z1,z2,z4,z1131,z6]),(0,[z0,z2,z29,z5,z6,z604]),(0,[z0,z1132,z2,z4,z5,z6]),(0,[z0,z1,z2,z1133,z5,z6])],[(0,[z120,z1,z2,z4,z5,z6]),(0,[z160,z2,z16,z4,z5,z6])],[(0,[z0,z873,z2,z4,z5,z6]),(0,[z0,z1,z2,z1134,z5,z6]),(0,[z375,z1,z2,z4,z5,z578]),(0,[z218,z1,z2,z239,z5,z6]),(0,[z1135,z1,z2,z4,z5,z6]),(0,[z1136,z1,z2,z4,z5,z6])],[(0,[z513,z1,z2,z4,z18,z6]),(0,[z1137,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1138]),(0,[z69,z0,z43,z4,z5,z6]),(0,[z1,z2,z242,z29,z5,z6]),(0,[z0,z1,z35,z4,z45,z6]),(1,[z0,z1,z2,z4,z821])],[(0,[z0,z576,z2,z29,z5,z6]),(0,[z68,z0,z1,z4,z139,z6]),(0,[z830,z1,z193,z4,z5,z6])],[(0,[z72,z2,z4,z184,z5,z6]),(0,[z47,z1,z2,z16,z4,z26]),(0,[z0,z1,z1139,z29,z5,z6])],[(0,[z1,z2,z16,z403,z5,z6]),(0,[z0,z1,z2,z4,z1140,z6])],[(1,[z1,z750,z4,z5,z6]),(0,[z0,z1,z2,z1141,z5,z6]),(0,[z0,z342,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z821,z5]),(0,[z143,z1,z2,z4,z26,z5])],[(0,[z1,z2,z1142,z4,z5,z6]),(0,[z9,z0,z2,z4,z790,z6]),(0,[z0,z1,z2,z1143,z5,z6]),(0,[z0,z1,z49,z5,z6,z142])],[(0,[z72,z2,z16,z29,z5,z6]),(0,[z0,z1,z2,z1144,z5,z6]),(0,[z1,z2,z21,z5,z6,z126])],[(0,[z25,z33,z2,z29,z5,z6]),(0,[z47,z0,z1,z2,z29,z26]),(0,[z0,z1,z1145,z4,z5,z6])],[(0,[z297,z1,z2,z4,z5,z117]),(0,[z0,z64,z2,z302,z5,z6]),(0,[z0,z1,z2,z4,z1146,z6]),(0,[z0,z1,z2,z4,z70,z468])],[(0,[z0,z1,z2,z1147,z5,z6]),(0,[z1,z2,z16,z4,z138,z6])]],
   [[(0,[z186,z1,z2,z4,z5,z263]),(0,[z72,z2,z184,z29,z5,z6]),(0,[z1082,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z11,z30]),(0,[z0,z1,z2,z4,z5,z904]),(0,[z0,z1,z2,z1148,z5,z6])],[(0,[z13,z0,z2,z29,z113,z6])],[(0,[z1,z2,z200,z4,z5,z86]),(1,[z1,z2,z4,z5,z1064]),(0,[z0,z43,z400,z29,z5,z6]),(0,[z476,z0,z1,z2,z464,z6]),(0,[z0,z1,z2,z172,z5,z6]),(0,[z1,z330,z1142,z4,z5,z6]),(0,[z0,z390,z153,z4,z5,z6])],[(0,[z180,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1149,z6]),(0,[z0,z1,z12,z21,z5,z6]),(0,[z1,z2,z1150,z4,z5,z6]),(0,[z1151,z1,z2,z4,z5,z6]),(0,[z71,z0,z1,z4,z5,z133]),(0,[z0,z501,z141,z4,z5,z6])],[(0,[z0,z2,z29,z5,z641,z6]),(0,[z1,z2,z4,z175,z5,z28]),(0,[z0,z1,z480,z4,z5,z30]),(0,[z0,z1152,z2,z4,z5,z6])],[(0,[z0,z1,z153,z29,z5,z6]),(0,[z251,z0,z1,z36,z5,z6])],[(0,[z1,z2,z16,z1025,z5,z6]),(0,[z2,z419,z16,z29,z5,z6]),(0,[z0,z1,z1153,z4,z5,z6]),(0,[z1154,z1,z2,z4,z5,z6])],[(0,[z13,z0,z2,z29,z5,z263]),(0,[z0,z1,z2,z4,z6,z1155]),(0,[z0,z1,z2,z147,z5,z117]),(0,[z22,z0,z1,z4,z748,z6]),(0,[z48,z0,z285,z2,z5,z142])],[(0,[z0,z1,z2,z1156,z5,z6]),(0,[z345,z1,z2,z4,z112,z6]),(0,[z0,z1,z2,z10,z5,z631]),(0,[z0,z1,z140,z5,z6,z133])],[(0,[z1157,z25,z1,z2,z4,z6]),(0,[z0,z2,z4,z1158,z5,z6]),(0,[z46,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z21,z45,z6]),(0,[z0,z1,z2,z4,z45,z291]),(0,[z1,z2,z4,z1159,z5,z6]),(0,[z1160,z1,z2,z4,z5,z6])],[(0,[z25,z2,z4,z927,z5,z6]),(0,[z1157,z0,z1,z2,z4,z6]),(0,[z181,z0,z1,z2,z4,z527]),(0,[z0,z2,z29,z5,z653,z6])],[(0,[z17,z1,z61,z4,z5,z6]),(0,[z612,z0,z43,z4,z5,z6]),(0,[z1,z2,z21,z988,z5,z6]),(0,[z0,z1161,z2,z4,z5,z6]),(1,[z0,z1,z140,z5,z133])],[(0,[z13,z25,z2,z29,z5,z6]),(0,[z1,z2,z4,z19,z5,z18]),(0,[z732,z1,z2,z4,z5,z6]),(0,[z1162,z1,z2,z4,z5,z6]),(0,[z0,z599,z2,z29,z5,z6]),(0,[z0,z1,z35,z4,z5,z291]),(0,[z0,z1,z2,z1163,z5,z6])],[(0,[z13,z0,z2,z29,z5,z6]),(0,[z67,z1,z2,z4,z5,z1064]),(0,[z46,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z29,z45,z6]),(0,[z248,z0,z1,z36,z5,z6])],[(0,[z0,z1,z2,z21,z78,z6]),(0,[z0,z1,z2,z4,z78,z291]),(0,[z46,z1,z2,z239,z5,z6]),(0,[z1,z2,z1164,z4,z5,z6])],[(0,[z25,z1,z2,z4,z51,z31]),(0,[z0,z1,z2,z4,z1165,z6]),(0,[z1166,z1,z2,z4,z5,z6])]],
   [[(0,[z253,z434,z2,z4,z5,z6]),(0,[z0,z1,z2,z1167,z5,z6]),(0,[z0,z1,z2,z102,z174,z6]),(0,[z284,z1,z82,z4,z5,z30])],[(0,[z218,z1,z2,z4,z5,z6]),(0,[z250,z1,z193,z4,z5,z6]),(0,[z0,z2,z330,z4,z76,z6])],[(0,[z0,z1,z2,z1168,z5,z6]),(0,[z1,z2,z16,z4,z1045,z5]),(0,[z25,z1,z2,z4,z5,z1052]),(0,[z0,z1,z2,z806,z5,z6]),(0,[z0,z1,z2,z29,z78,z6]),(0,[z218,z1,z2,z4,z5,z432]),(0,[z0,z265,z2,z4,z5,z30]),(0,[z1,z2,z4,z5,z1169,z6])],[(0,[z1,z2,z242,z4,z5,z6]),(0,[z0,z2,z149,z29,z5,z6]),(0,[z170,z0,z2,z29,z5,z28]),(0,[z46,z528,z2,z4,z5,z6])],[],[(0,[z25,z1,z2,z4,z5,z468]),(0,[z0,z1,z2,z4,z1170,z6]),(0,[z0,z1,z87,z29,z5,z6]),(0,[z0,z1,z2,z29,z5,z1171]),(0,[z0,z1,z1139,z4,z5,z6]),(0,[z14,z2,z21,z159,z5,z6]),(0,[z1172,z1,z2,z21,z5,z6])],[(0,[z610,z1,z2,z4,z5,z27]),(0,[z0,z1,z2,z4,z5,z1173]),(0,[z0,z1,z1174,z21,z5,z6]),(0,[z9,z0,z2,z4,z76,z631]),(0,[z88,z109,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1175,z6]),(0,[z0,z1,z239,z5,z139,z6]),(0,[z0,z1,z2,z1176,z5,z6])],[(0,[z24,z1,z2,z16,z161,z6]),(0,[z1,z2,z1066,z4,z5,z6]),(0,[z0,z2,z29,z5,z6,z674]),(0,[z1,z2,z1177,z4,z5,z6]),(0,[z1178,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1179])],[(0,[z25,z1,z2,z4,z357,z6]),(0,[z0,z1,z2,z4,z1180,z6])],[(0,[z0,z2,z806,z29,z5,z6]),(0,[z120,z1,z2,z29,z5,z6]),(0,[z1181,z1,z2,z374,z5,z6]),(0,[z0,z516,z2,z4,z5,z56]),(0,[z1182,z1,z2,z4,z5,z6])],[(0,[z13,z515,z2,z4,z5,z6]),(0,[z452,z1,z2,z125,z5,z6]),(0,[z74,z202,z43,z4,z5,z6]),(0,[z121,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z1183,z5,z6]),(0,[z0,z1,z2,z609,z40,z6])],[(0,[z103,z2,z4,z636,z5,z6]),(0,[z69,z0,z43,z29,z5,z6]),(0,[z1184,z1,z2,z4,z5,z6]),(0,[z279,z1,z2,z172,z5,z6])],[(0,[z1,z73,z2,z4,z112,z6]),(0,[z0,z1,z2,z1185,z5,z6]),(0,[z0,z1,z2,z4,z1186,z6]),(0,[z0,z2,z29,z5,z688,z6]),(0,[z1187,z1,z2,z29,z5,z6]),(0,[z1,z2,z4,z5,z6,z1188])],[(0,[z0,z1,z2,z4,z1189,z6]),(0,[z67,z1,z2,z4,z5,z99]),(0,[z0,z2,z1190,z29,z5,z6]),(0,[z491,z0,z1,z36,z5,z6]),(0,[z1,z2,z4,z1191,z5,z6])],[(0,[z103,z873,z2,z4,z5,z6]),(0,[z74,z0,z43,z4,z138,z6]),(0,[z1192,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z11,z6]),(0,[z0,z1,z2,z21,z5,z291]),(0,[z180,z501,z2,z4,z5,z6]),(0,[z1193,z1,z2,z4,z5,z6])]],
   [[(0,[z137,z1,z16,z29,z5,z6]),(0,[z0,z2,z29,z5,z6,z695]),(0,[z0,z1,z2,z21,z174,z6]),(0,[z284,z1,z2,z21,z5,z6]),(0,[z57,z1,z2,z4,z173,z6]),(0,[z1194,z1,z2,z4,z5,z6])],[(0,[z25,z1,z359,z4,z5,z6]),(0,[z0,z1,z82,z4,z5,z569])],[(0,[z72,z1,z2,z4,z5,z263]),(1,[z0,z61,z29,z5,z6]),(0,[z212,z1,z2,z4,z154,z6])],[(0,[z0,z2,z29,z5,z6,z387]),(0,[z0,z1,z2,z29,z11,z6])],[(0,[z101,z0,z264,z4,z5,z28]),(0,[z0,z1,z12,z4,z5,z6]),(0,[z0,z1195,z2,z4,z5,z6])],[(0,[z25,z1,z2,z4,z6,z115]),(0,[z1,z2,z882,z125,z5,z6])],[(0,[z152,z0,z43,z4,z5,z6]),(0,[z0,z64,z2,z29,z5,z6])],[(0,[z25,z1,z2,z4,z19,z5]),(0,[z0,z1,z2,z4,z1196,z6]),(0,[z693,z0,z2,z29,z5,z6]),(0,[z1197,z1,z2,z4,z5,z6]),(0,[z1,z2,z1198,z4,z5,z6]),(0,[z0,z330,z4,z5,z76,z6]),(0,[z454,z0,z1,z2,z5,z142]),(0,[z1,z2,z4,z5,z6,z1199])],[(0,[z0,z1,z61,z433,z5,z6]),(0,[z72,z331,z2,z4,z5,z6]),(0,[z186,z1,z2,z21,z5,z6]),(0,[z1200,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z443,z31])],[(0,[z100,z1,z61,z4,z5,z6]),(0,[z0,z1,z2,z1201,z5,z6]),(0,[z0,z420,z2,z777,z5,z6])],[(0,[z13,z0,z346,z29,z5,z6]),(1,[z873,z2,z4,z5,z6]),(0,[z46,z1,z2,z4,z5,z6]),(0,[z1202,z1,z2,z4,z5,z6]),(0,[z1,z2,z34,z1203,z5,z6]),(0,[z0,z1,z2,z4,z45,z6])],[(0,[z72,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z1204,z5,z6]),(0,[z25,z1,z146,z4,z5,z6]),(0,[z181,z116,z1,z2,z4,z6]),(0,[z0,z1205,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z1206,z6]),(0,[z669,z1,z2,z4,z20,z6]),(0,[z1,z162,z43,z4,z5,z6]),(0,[z186,z1,z2,z29,z5,z6]),(0,[z1,z2,z29,z5,z6,z1188]),(0,[z24,z0,z1,z2,z325,z6]),(0,[z1207,z1,z2,z4,z5,z6]),(0,[z0,z59,z2,z5,z161,z6]),(0,[z1208,z1,z12,z4,z5,z6])],[(0,[z1,z2,z4,z1209,z5,z6]),(0,[z0,z1,z94,z4,z5,z30]),(0,[z48,z0,z1,z2,z154,z142])],[(0,[z1,z12,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z527]),(0,[z0,z1,z2,z1210,z5,z6]),(0,[z104,z0,z1,z4,z357,z133])],[(0,[z345,z1,z2,z4,z18,z6]),(0,[z0,z2,z29,z5,z76,z6]),(0,[z1181,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z78,z6])]],
   [[(0,[z72,z0,z2,z246,z5,z6]),(0,[z0,z1,z2,z102,z5,z6]),(0,[z170,z0,z2,z4,z5,z28]),(0,[z22,z0,z189,z4,z139,z6]),(0,[z0,z1,z2,z1211,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1212]),(0,[z0,z1,z2,z1190,z5,z6]),(0,[z186,z2,z4,z29,z5,z6]),(0,[z0,z265,z2,z21,z5,z6]),(0,[z0,z265,z2,z4,z11,z6])],[(0,[z0,z1,z87,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1171]),(0,[z180,z1,z2,z4,z5,z423]),(0,[z0,z285,z153,z4,z5,z6])],[(0,[z1,z132,z16,z21,z5,z6]),(0,[z1213,z1,z2,z21,z5,z6])],[(0,[z0,z1,z2,z21,z113,z6]),(0,[z0,z1,z2,z1101,z5,z6]),(0,[z1214,z1,z2,z21,z5,z6]),(0,[z375,z109,z2,z4,z5,z6]),(0,[z92,z0,z1,z36,z5,z578]),(0,[z24,z58,z1,z2,z161,z6])],[(0,[z0,z691,z2,z29,z5,z6]),(0,[z0,z265,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z1215,z6]),(0,[z1,z141,z874,z4,z5,z6])],[(0,[z59,z2,z16,z4,z5,z6]),(0,[z1,z585,z16,z4,z5,z6]),(0,[z25,z1,z141,z4,z5,z6]),(0,[z1216,z1,z2,z4,z5,z6]),(0,[z345,z14,z2,z4,z5,z6])],[(0,[z1,z132,z16,z29,z5,z6]),(0,[z25,z1,z2,z403,z5,z6]),(0,[z218,z1,z2,z29,z5,z6]),(0,[z0,z1,z1174,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1217]),(0,[z1218,z1,z2,z4,z5,z6])],[(0,[z121,z1,z2,z4,z5,z6]),(0,[z0,z2,z29,z5,z6,z123]),(0,[z88,z160,z2,z4,z5,z6]),(0,[z0,z1,z4,z36,z5,z291])],[(0,[z0,z1,z61,z4,z112,z6]),(0,[z227,z1,z2,z4,z357,z6])],[(0,[z0,z1,z2,z21,z5,z263]),(0,[z369,z2,z419,z4,z5,z6]),(0,[z1219,z1,z2,z4,z5,z6]),(0,[z1187,z1,z2,z4,z5,z6]),(0,[z1220,z1,z49,z4,z5,z6])],[(0,[z254,z1,z346,z4,z5,z6]),(0,[z1,z2,z16,z4,z45,z6]),(0,[z1,z264,z812,z4,z5,z6]),(0,[z0,z1,z2,z4,z190,z142])],[(0,[z1221,z0,z1,z2,z4,z6]),(0,[z25,z1,z2,z4,z1011,z6]),(0,[z0,z420,z2,z140,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1222]),(0,[z137,z1,z16,z4,z5,z6]),(0,[z25,z1,z2,z4,z138,z6]),(0,[z0,z1,z2,z4,z5,z1223]),(0,[z218,z528,z2,z4,z5,z6])],[(0,[z186,z1,z2,z4,z5,z86]),(0,[z22,z0,z528,z4,z139,z6]),(0,[z1,z2,z1224,z4,z5,z6]),(0,[z0,z1,z2,z4,z566,z31])],[(0,[z1,z2,z1225,z4,z5,z6]),(0,[z100,z2,z119,z341,z5,z6]),(0,[z1226,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z16,z4,z78,z6]),(0,[z254,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z11,z6]),(0,[z121,z1,z2,z456,z5,z6]),(0,[z0,z501,z12,z4,z5,z6])],[(0,[z0,z1,z2,z1227,z5,z6]),(0,[z284,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z76,z527]),(0,[z0,z1,z2,z21,z5,z432]),(0,[z0,z1,z1228,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1229]),(0,[z0,z1,z2,z21,z5,z1230]),(0,[z1,z2,z1095,z4,z5,z6]),(0,[z0,z2,z4,z790,z76,z6]),(0,[z0,z1231,z2,z4,z5,z6]),(0,[z46,z1,z2,z151,z5,z6])],[(0,[z0,z1,z2,z352,z5,z6]),(0,[z0,z2,z4,z29,z5,z263]),(0,[z1,z2,z4,z5,z86,z168]),(0,[z1232,z1,z2,z4,z5,z6])],[(0,[z254,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z190,z6])],[(0,[z165,z2,z16,z29,z5,z6]),(0,[z0,z2,z207,z29,z5,z6]),(0,[z0,z1,z2,z29,z5,z432]),(0,[z412,z0,z2,z29,z5,z6]),(0,[z0,z2,z4,z5,z954,z28]),(0,[z0,z1,z2,z239,z5,z6]),(0,[z0,z390,z2,z4,z190,z6])],[(0,[z1,z2,z4,z5,z6,z1233]),(0,[z0,z1,z2,z239,z5,z432])],[(0,[z152,z2,z16,z29,z5,z6]),(0,[z1234,z1,z2,z29,z5,z6]),(0,[z1235,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1236,z4,z5,z6]),(0,[z0,z1,z2,z29,z190,z6]),(0,[z0,z1,z2,z456,z11,z6]),(0,[z0,z1237,z2,z4,z5,z6])],[(0,[z0,z1,z2,z246,z5,z6]),(0,[z186,z1,z2,z4,z5,z6]),(0,[z62,z1,z2,z4,z18,z6]),(0,[z0,z1,z2,z1238,z5,z6])],[(0,[z116,z1,z2,z4,z18,z6]),(0,[z1239,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z29,z5,z6]),(0,[z1,z2,z21,z175,z5,z6]),(0,[z1240,z1,z2,z4,z5,z6]),(0,[z1241,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z140,z5,z133])],[(0,[z1091,z1,z264,z4,z5,z6]),(0,[z0,z1,z2,z4,z562,z31])],[(0,[z0,z37,z43,z29,z5,z6]),(0,[z0,z1,z2,z374,z5,z6]),(0,[z0,z1,z1242,z4,z5,z6]),(0,[z186,z0,z2,z29,z5,z6]),(0,[z279,z1,z87,z4,z5,z6])],[(0,[z1243,z1,z2,z4,z5,z6]),(0,[z476,z0,z2,z29,z76,z6]),(0,[z0,z518,z2,z29,z5,z6]),(0,[z0,z349,z2,z21,z5,z6]),(0,[z724,z1,z141,z4,z5,z6])],[(0,[z46,z189,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z113,z263]),(0,[z0,z2,z29,z5,z6,z198]),(0,[z0,z1,z2,z4,z6,z1244]),(0,[z1,z2,z4,z5,z6,z1064]),(0,[z488,z1,z2,z184,z5,z6]),(0,[z186,z1,z2,z4,z5,z31])]],
   [[(0,[z520,z0,z2,z29,z5,z6]),(0,[z1,z2,z4,z5,z6,z1245])],[(0,[z0,z1,z2,z4,z877,z6]),(0,[z0,z1,z2,z1246,z5,z6]),(0,[z1247,z1,z2,z29,z5,z6]),(0,[z0,z2,z34,z29,z5,z6]),(0,[z1,z2,z1248,z4,z5,z6])],[(0,[z124,z2,z16,z29,z5,z6]),(0,[z0,z1,z2,z1249,z5,z6]),(0,[z1250,z1,z2,z4,z5,z6]),(0,[z0,z265,z2,z4,z5,z6]),(0,[z0,z1,z82,z21,z5,z30])],[(0,[z0,z1,z2,z4,z1251,z6]),(0,[z72,z434,z2,z4,z5,z6]),(0,[z103,z2,z4,z5,z6,z123]),(0,[z1252,z1,z2,z4,z5,z6]),(0,[z0,z1253,z2,z4,z5,z6]),(0,[z0,z1254,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1255]),(0,[z0,z1,z37,z239,z5,z6]),(0,[z0,z1256,z2,z4,z5,z6]),(0,[z0,z1,z12,z4,z5,z423])],[(0,[z1,z132,z16,z4,z5,z6]),(0,[z0,z2,z933,z4,z5,z6]),(0,[z0,z2,z29,z5,z28,z133]),(0,[z227,z420,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z113,z6]),(0,[z72,z483,z2,z4,z5,z6]),(0,[z1257,z1,z2,z4,z5,z6]),(0,[z1214,z1,z2,z4,z5,z6]),(0,[z101,z57,z2,z4,z5,z28]),(0,[z0,z1,z1258,z4,z5,z6])],[(0,[z13,z629,z2,z4,z5,z6]),(0,[z13,z2,z29,z20,z5,z6]),(0,[z1,z2,z16,z172,z5,z6]),(0,[z0,z1259,z2,z4,z5,z6]),(0,[z15,z181,z1,z2,z4,z31]),(0,[z0,z1,z2,z4,z5,z1260]),(0,[z0,z1,z2,z4,z1261,z6]),(0,[z0,z1,z2,z4,z1215,z6]),(0,[z0,z165,z2,z1190,z5,z6]),(0,[z0,z1,z82,z29,z5,z30]),(0,[z0,z1,z1262,z4,z5,z6]),(0,[z375,z160,z2,z4,z5,z6])],[(0,[z25,z1,z2,z1156,z5,z6]),(0,[z25,z1,z750,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z115]),(0,[z249,z1,z2,z4,z76,z6]),(0,[z143,z47,z1,z2,z4,z26])],[(0,[z1,z873,z2,z4,z5,z6]),(0,[z0,z1263,z2,z4,z5,z6]),(0,[z0,z1,z2,z1264,z5,z6]),(0,[z0,z1,z330,z21,z5,z6]),(0,[z0,z1265,z2,z4,z5,z6])],[(0,[z1,z153,z16,z4,z5,z6]),(0,[z25,z1,z355,z4,z5,z6])],[(0,[z25,z1,z49,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1266]),(0,[z44,z1,z2,z4,z5,z86]),(0,[z0,z265,z2,z456,z5,z6]),(0,[z1267,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z263]),(0,[z1117,z1,z2,z4,z5,z6]),(0,[z47,z0,z2,z29,z76,z6]),(0,[z0,z1,z2,z4,z790,z6]),(0,[z0,z1,z87,z4,z5,z28]),(0,[z120,z1,z35,z156,z5,z6])],[(0,[z0,z1,z2,z4,z1268,z6]),(0,[z13,z0,z2,z29,z112,z6]),(0,[z0,z2,z29,z245,z5,z6]),(0,[z0,z501,z2,z21,z5,z6])],[(0,[z0,z1,z346,z21,z5,z6]),(0,[z0,z1269,z2,z4,z5,z6]),(0,[z0,z1,z2,z1270,z5,z6]),(0,[z0,z1,z2,z5,z6,z904])],[],[(0,[z0,z1,z2,z4,z1271,z6]),(0,[z1,z2,z1272,z21,z5,z6]),(0,[z0,z1,z2,z1273,z5,z6]),(1,[z0,z1,z239,z139,z6]),(0,[z0,z59,z141,z4,z5,z6]),(0,[z1274,z1,z2,z4,z5,z6])]],
   [[(0,[z137,z1,z750,z4,z5,z6]),(0,[z1,z2,z16,z4,z6,z1244]),(0,[z124,z0,z2,z723,z5,z6]),(0,[z1,z2,z4,z1275,z5,z6]),(0,[z486,z1,z2,z4,z154,z6])],[(0,[z0,z61,z4,z29,z5,z6]),(0,[z254,z1,z2,z4,z5,z6]),(0,[z15,z1,z2,z21,z5,z27])],[(0,[z0,z1,z2,z4,z5,z1276]),(0,[z0,z1,z2,z4,z5,z432]),(0,[z1277,z1,z2,z4,z5,z6]),(0,[z0,z1,z12,z4,z161,z6])],[(0,[z25,z1,z2,z4,z5,z631]),(0,[z0,z1278,z2,z4,z5,z6]),(0,[z1279,z1,z2,z4,z5,z6]),(0,[z0,z2,z29,z70,z76,z6]),(0,[z0,z1,z1280,z4,z5,z6]),(0,[z0,z390,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z1230])],[(0,[z1234,z1,z2,z4,z5,z6]),(0,[z249,z1,z193,z4,z5,z6]),(0,[z1281,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z140,z357,z6]),(0,[z1282,z1,z2,z4,z5,z6]),(0,[z0,z1,z141,z4,z5,z205]),(0,[z0,z1,z2,z4,z799,z6]),(0,[z334,z0,z1,z2,z4,z26])],[(0,[z1,z2,z1283,z4,z5,z6]),(0,[z0,z1,z1284,z4,z5,z6]),(0,[z0,z14,z2,z403,z5,z6]),(0,[z272,z0,z1,z245,z5,z6]),(0,[z1,z2,z4,z1203,z5,z6]),(0,[z0,z1,z2,z4,z5,z1285]),(0,[z0,z1,z2,z4,z190,z6]),(0,[z0,z1,z2,z1286,z5,z6])],[(0,[z0,z1,z1287,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1288]),(0,[z0,z1,z2,z723,z5,z6]),(0,[z0,z1,z2,z29,z5,z291]),(0,[z0,z1,z1289,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z1290])],[(0,[z0,z1,z2,z1291,z5,z6]),(0,[z0,z1,z2,z29,z174,z6]),(0,[z0,z390,z2,z29,z5,z6]),(0,[z284,z1,z2,z29,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1292]),(0,[z1,z2,z119,z882,z5,z6]),(0,[z0,z2,z301,z29,z5,z6]),(0,[z0,z501,z2,z374,z5,z6])],[(0,[z1,z2,z200,z4,z5,z144]),(0,[z1208,z1,z2,z4,z5,z6]),(0,[z116,z0,z1,z2,z29,z6]),(0,[z0,z1,z2,z1293,z5,z6]),(0,[z0,z165,z2,z29,z5,z6]),(1,[z186,z2,z29,z5,z6]),(0,[z1294,z1,z2,z4,z5,z6])],[(0,[z1,z750,z16,z4,z5,z6]),(0,[z165,z16,z43,z4,z5,z6]),(0,[z1,z2,z366,z21,z5,z6]),(0,[z476,z0,z2,z4,z76,z6]),(0,[z47,z0,z1,z2,z21,z26]),(0,[z1295,z1,z2,z4,z5,z6])],[(0,[z1,z552,z16,z4,z5,z6]),(0,[z0,z2,z4,z723,z5,z6]),(0,[z0,z2,z29,z5,z31,z28]),(0,[z1296,z1,z2,z4,z5,z6]),(0,[z0,z165,z2,z411,z5,z6]),(0,[z22,z0,z1,z4,z139,z468]),(0,[z24,z0,z1,z2,z799,z6])],[(0,[z0,z1,z2,z4,z1297,z6]),(0,[z152,z16,z43,z4,z5,z6]),(0,[z1,z49,z16,z4,z5,z6]),(0,[z15,z1,z2,z4,z175,z5]),(0,[z0,z528,z2,z21,z5,z6]),(0,[z218,z1,z2,z151,z5,z6])],[(0,[z13,z73,z2,z21,z5,z6]),(0,[z100,z1,z2,z159,z5,z6]),(0,[z0,z516,z2,z29,z5,z6])],[(0,[z152,z2,z280,z4,z5,z6]),(0,[z1,z2,z366,z29,z5,z6]),(0,[z1247,z1,z2,z4,z5,z6]),(0,[z57,z1,z87,z4,z5,z6]),(0,[z1298,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z877,z5,z6]),(0,[z0,z1,z2,z21,z5,z423]),(0,[z0,z1299,z2,z4,z5,z6]),(0,[z1,z2,z1300,z4,z5,z6]),(0,[z58,z1,z141,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z1301,z5]),(0,[z0,z380,z2,z21,z5,z6]),(0,[z0,z528,z2,z29,z5,z6]),(0,[z1302,z1,z2,z4,z5,z6]),(0,[z1,z12,z1303,z4,z5,z6])],[(0,[z13,z73,z2,z29,z5,z6]),(0,[z1,z2,z1304,z4,z5,z6]),(0,[z25,z1,z153,z4,z5,z6]),(0,[z1305,z1,z2,z4,z5,z6]),(0,[z0,z1,z264,z172,z5,z6]),(0,[z0,z1306,z2,z4,z5,z6]),(0,[z1307,z1,z2,z4,z5,z6]),(0,[z0,z528,z2,z239,z5,z6])],[(0,[z0,z1,z346,z4,z113,z6]),(0,[z0,z2,z4,z341,z5,z6]),(1,[z16,z43,z29,z5,z6]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z17,z1,z2,z4,z877,z6]),(0,[z186,z1,z2,z4,z26,z5])],[(0,[z0,z1,z82,z4,z5,z30]),(0,[z0,z1308,z2,z4,z5,z6])],[(0,[z0,z380,z2,z29,z5,z6]),(0,[z0,z1,z12,z108,z5,z6])],[(0,[z25,z64,z2,z29,z5,z6]),(0,[z67,z1,z2,z21,z5,z86]),(0,[z0,z285,z2,z4,z190,z6])],[(0,[z1,z2,z16,z4,z190,z6]),(0,[z1309,z1,z2,z4,z5,z6]),(0,[z0,z1310,z2,z4,z5,z6]),(0,[z1311,z1,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z76,z631]),(0,[z212,z1,z49,z4,z5,z6])],[(0,[z72,z1,z2,z4,z112,z6]),(0,[z1,z1312,z2,z4,z5,z6]),(0,[z9,z2,z16,z4,z76,z6]),(0,[z0,z1,z2,z4,z5,z1313])],[(0,[z0,z1,z346,z4,z5,z263]),(0,[z0,z442,z2,z21,z5,z6]),(0,[z1,z2,z4,z450,z20,z6]),(0,[z218,z189,z2,z4,z5,z6])],[(0,[z2,z16,z4,z341,z5,z6]),(0,[z25,z1,z2,z4,z45,z6]),(0,[z17,z67,z1,z2,z4,z31]),(0,[z0,z1,z330,z4,z5,z6]),(0,[z1172,z1,z2,z4,z5,z6])],[(0,[z104,z1,z16,z4,z5,z133]),(0,[z0,z1,z2,z4,z489,z31]),(0,[z0,z1,z2,z151,z5,z432])],[(0,[z0,z1,z2,z29,z113,z6]),(0,[z13,z701,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1314,z6]),(0,[z0,z1,z2,z4,z1315,z6])],[(0,[z25,z1,z61,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z263]),(0,[z309,z0,z2,z29,z5,z6]),(0,[z17,z1,z2,z4,z6,z155]),(0,[z0,z165,z2,z461,z5,z6]),(0,[z0,z1,z2,z4,z45,z578])],[(0,[z0,z1,z2,z1316,z5,z6]),(0,[z0,z1,z2,z4,z1317,z6]),(0,[z0,z2,z445,z29,z5,z6]),(0,[z92,z0,z1,z898,z5,z6]),(0,[z0,z1,z156,z898,z5,z6])],[(0,[z0,z1,z346,z4,z5,z6]),(0,[z583,z72,z2,z29,z5,z6]),(0,[z25,z2,z29,z5,z76,z6]),(0,[z25,z1,z2,z4,z78,z6]),(0,[z67,z1,z2,z4,z86,z115]),(0,[z0,z1,z467,z171,z5,z6]),(0,[z47,z0,z1,z2,z4,z255])],[(0,[z0,z1,z1318,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1319]),(0,[z0,z1,z2,z4,z1320,z6])]],
   [[(0,[z0,z1,z2,z4,z1321,z6]),(0,[z181,z72,z2,z29,z5,z6]),(0,[z1,z2,z1272,z4,z5,z6]),(0,[z0,z16,z43,z29,z5,z6]),(0,[z297,z1,z2,z4,z138,z6]),(0,[z0,z644,z2,z29,z5,z6]),(0,[z180,z1,z2,z4,z5,z205]),(0,[z0,z1322,z2,z4,z5,z6]),(0,[z1,z2,z1323,z4,z5,z6])],[(0,[z0,z1,z2,z29,z5,z263]),(0,[z0,z1,z2,z1324,z5,z6]),(0,[z1,z2,z1325,z4,z5,z6]),(0,[z25,z1,z87,z4,z5,z6]),(0,[z0,z221,z2,z29,z5,z6]),(0,[z57,z1,z2,z172,z5,z6]),(0,[z0,z1,z2,z4,z78,z578])],[(0,[z13,z73,z2,z4,z113,z6]),(0,[z100,z1,z2,z352,z5,z6]),(0,[z0,z1,z2,z156,z45,z6]),(0,[z1326,z1,z2,z4,z5,z6]),(0,[z1,z2,z1327,z4,z5,z6])],[(0,[z0,z1,z2,z21,z5,z6]),(0,[z181,z1,z2,z21,z20,z6]),(0,[z0,z1,z1328,z21,z5,z6]),(0,[z0,z1,z193,z4,z5,z631]),(0,[z0,z1,z2,z4,z5,z291]),(0,[z1329,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z102,z5,z6]),(0,[z254,z1,z105,z4,z5,z6]),(0,[z0,z390,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z174,z6]),(0,[z1330,z1,z2,z4,z5,z6])],[(0,[z0,z64,z2,z32,z5,z6]),(0,[z0,z2,z29,z5,z30,z28]),(0,[z9,z0,z2,z21,z76,z6])],[(0,[z47,z25,z1,z2,z4,z26]),(0,[z0,z105,z43,z29,z5,z6]),(1,[z1,z2,z4,z877,z6]),(0,[z0,z189,z2,z4,z5,z432])],[(0,[z0,z1,z2,z29,z5,z6]),(0,[z0,z2,z43,z29,z5,z6]),(0,[z0,z1,z1289,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z26])],[(0,[z13,z73,z2,z4,z5,z263]),(0,[z0,z1,z36,z5,z133,z142])],[(0,[z0,z1,z2,z784,z5,z6]),(0,[z0,z1,z2,z147,z138,z6]),(0,[z0,z1,z2,z4,z138,z148]),(0,[z0,z1,z1280,z29,z5,z6]),(0,[z0,z1,z2,z411,z5,z6]),(0,[z0,z1,z2,z4,z5,z1331])],[(0,[z1,z61,z16,z4,z5,z6]),(0,[z683,z0,z2,z29,z5,z6]),(0,[z217,z1,z2,z159,z5,z6]),(0,[z345,z47,z1,z2,z4,z6]),(0,[z0,z1332,z2,z4,z5,z6])],[(0,[z13,z73,z2,z269,z5,z6]),(0,[z1,z2,z366,z4,z5,z6]),(0,[z48,z1,z2,z16,z5,z142]),(0,[z0,z1,z2,z4,z5,z1333]),(0,[z1,z2,z4,z1334,z5,z6])],[(0,[z351,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z5,z459]),(0,[z250,z1,z2,z4,z5,z631]),(0,[z0,z1335,z2,z4,z5,z6]),(0,[z0,z390,z2,z178,z5,z6])],[(0,[z0,z528,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z5,z1336]),(0,[z279,z1,z2,z102,z5,z6]),(0,[z1337,z1,z2,z4,z5,z6]),(0,[z1,z35,z242,z156,z5,z6])],[(0,[z13,z73,z2,z4,z5,z6]),(0,[z0,z380,z2,z269,z5,z6]),(0,[z2,z16,z43,z29,z5,z6]),(0,[z25,z1,z659,z4,z5,z6]),(1,[z0,z1,z36,z45,z6]),(0,[z0,z528,z2,z4,z5,z432])],[(0,[z0,z1338,z2,z4,z5,z6]),(0,[z1,z515,z2,z4,z5,z27]),(0,[z0,z1,z43,z4,z5,z148]),(0,[z0,z1,z2,z4,z1339,z6])]],
   [[(0,[z0,z1,z2,z4,z6,z1340]),(0,[z0,z1,z2,z29,z5,z459]),(0,[z0,z1,z2,z4,z5,z423]),(0,[z0,z1,z2,z4,z563,z31])],[(0,[z0,z380,z2,z4,z5,z6]),(0,[z0,z1,z2,z1341,z5,z6]),(0,[z0,z1,z2,z266,z5,z6]),(0,[z0,z2,z43,z266,z5,z6]),(0,[z279,z1,z2,z4,z5,z56]),(0,[z1342,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z411,z5,z459]),(0,[z1343,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z433,z113,z6]),(1,[z0,z2,z29,z5,z263]),(0,[z116,z1,z2,z4,z6,z27]),(0,[z0,z1,z1344,z4,z5,z6]),(0,[z0,z33,z2,z4,z5,z215]),(0,[z1311,z1,z2,z4,z5,z6]),(0,[z0,z285,z2,z21,z5,z6])],[(0,[z1,z2,z16,z21,z5,z6]),(0,[z1,z2,z16,z4,z5,z291]),(0,[z1,z2,z16,z4,z11,z6]),(0,[z25,z1,z2,z172,z5,z6]),(0,[z0,z1,z43,z4,z163,z6]),(0,[z0,z43,z4,z5,z6,z148]),(0,[z0,z2,z461,z5,z76,z6]),(0,[z1345,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z269,z113,z6]),(0,[z1,z2,z16,z4,z174,z6]),(0,[z1346,z1,z2,z4,z5,z6]),(0,[z48,z0,z1,z2,z5,z387]),(0,[z166,z0,z1,z4,z139,z6]),(0,[z0,z1347,z2,z4,z5,z6]),(0,[z0,z1348,z2,z4,z5,z6])],[(0,[z1,z2,z4,z159,z5,z6]),(0,[z0,z1,z2,z1349,z5,z6]),(0,[z0,z1,z1350,z4,z5,z6]),(0,[z1351,z1,z2,z4,z5,z6]),(0,[z93,z1,z2,z4,z6,z31])],[(0,[z1,z2,z16,z352,z5,z6]),(0,[z17,z257,z1,z2,z4,z6]),(0,[z0,z2,z4,z1352,z5,z6]),(0,[z1213,z1,z2,z4,z5,z6]),(0,[z0,z285,z2,z29,z5,z6]),(0,[z0,z668,z2,z4,z5,z56]),(0,[z1353,z1,z2,z4,z5,z6])],[(0,[z1,z2,z16,z29,z5,z6]),(0,[z0,z515,z2,z29,z5,z6]),(0,[z0,z1,z2,z10,z5,z6]),(0,[z0,z420,z2,z987,z5,z6]),(0,[z0,z1,z49,z4,z154,z6])],[(0,[z0,z1,z2,z433,z5,z263]),(0,[z1,z2,z16,z239,z5,z6]),(0,[z773,z1,z2,z16,z4,z6]),(0,[z0,z1,z2,z4,z1354,z6]),(0,[z1,z2,z4,z5,z1355,z6])],[(0,[z72,z103,z2,z246,z5,z6]),(0,[z0,z1018,z2,z4,z5,z6]),(0,[z202,z1,z2,z4,z138,z6]),(0,[z0,z1,z2,z461,z5,z6]),(0,[z0,z1356,z2,z4,z5,z6])],[(0,[z0,z1,z2,z269,z5,z263]),(0,[z0,z64,z2,z4,z5,z148]),(0,[z0,z160,z2,z403,z5,z6]),(0,[z257,z1,z2,z4,z76,z6]),(0,[z47,z0,z1,z2,z4,z470])],[(0,[z1,z16,z43,z21,z5,z6]),(0,[z1,z2,z16,z4,z5,z1333]),(0,[z1,z2,z21,z1209,z5,z6]),(0,[z0,z1,z4,z5,z6,z782]),(0,[z0,z390,z2,z301,z5,z6]),(0,[z0,z1357,z2,z4,z5,z6])],[(0,[z1,z2,z16,z246,z5,z6]),(0,[z1358,z1,z2,z4,z5,z6]),(0,[z279,z1,z2,z21,z5,z6])],[(0,[z360,z25,z2,z29,z5,z6]),(0,[z114,z1,z2,z354,z5,z6]),(0,[z0,z165,z330,z4,z5,z6]),(0,[z0,z1,z2,z1359,z5,z6]),(0,[z279,z1,z2,z4,z174,z6]),(0,[z0,z1,z2,z239,z139,z6]),(0,[z1360,z1,z2,z4,z5,z6])],[(0,[z360,z0,z2,z29,z5,z6]),(0,[z0,z2,z419,z29,z5,z6]),(0,[z0,z1361,z2,z4,z5,z6]),(0,[z0,z1,z330,z29,z5,z6]),(0,[z0,z1,z264,z102,z5,z6])]],
   [[(0,[z1,z2,z16,z374,z5,z6]),(0,[z202,z1,z43,z4,z5,z6]),(0,[z0,z64,z2,z4,z163,z6]),(0,[z0,z1,z2,z4,z5,z954])],[(0,[z0,z1,z2,z269,z5,z6]),(0,[z181,z1,z2,z4,z19,z5]),(1,[z0,z43,z4,z5,z148]),(0,[z279,z1,z2,z29,z5,z6]),(0,[z0,z1,z330,z411,z5,z6]),(0,[z0,z1,z2,z10,z5,z459]),(0,[z0,z1,z12,z4,z5,z205])],[(0,[z13,z488,z2,z29,z5,z6]),(0,[z1,z2,z16,z266,z5,z6]),(0,[z0,z2,z43,z302,z5,z6]),(0,[z1362,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z302,z5,z6])],[(0,[z0,z1,z1363,z4,z5,z6]),(0,[z103,z2,z419,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1364]),(0,[z0,z2,z29,z5,z6,z426]),(0,[z0,z501,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z694,z31]),(0,[z0,z1,z2,z4,z40,z205]),(1,[z0,z1,z49,z5,z142])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z346,z29,z5,z6]),(0,[z0,z1,z2,z4,z1365,z6]),(0,[z181,z1,z2,z4,z20,z6]),(1,[z217,z2,z29,z5,z6]),(0,[z0,z1,z1328,z4,z5,z6]),(0,[z1366,z1,z2,z4,z5,z6]),(0,[z0,z265,z82,z4,z5,z6]),(0,[z0,z1,z2,z4,z1367,z6])],[(0,[z24,z25,z1,z2,z161,z6]),(0,[z181,z1,z2,z4,z505,z6]),(0,[z0,z528,z2,z151,z5,z6]),(0,[z1368,z1,z2,z4,z5,z6])],[(0,[z372,z1,z16,z4,z5,z6]),(1,[z0,z43,z4,z163,z6]),(0,[z0,z1,z2,z4,z5,z1369]),(0,[z1,z82,z162,z4,z5,z30]),(0,[z1,z2,z4,z5,z1370,z6])],[(0,[z0,z1,z2,z4,z1371,z6]),(0,[z116,z1,z2,z16,z4,z6]),(1,[z1,z2,z882,z5,z6]),(0,[z0,z189,z2,z21,z5,z6])],[(0,[z13,z100,z2,z29,z5,z6]),(0,[z693,z73,z2,z4,z5,z6]),(0,[z1,z231,z16,z4,z5,z6]),(0,[z15,z1,z2,z29,z5,z27]),(0,[z293,z0,z2,z4,z5,z28]),(0,[z0,z1,z2,z108,z339,z6])],[(0,[z1,z2,z16,z4,z113,z6]),(0,[z0,z1,z2,z4,z317,z31]),(0,[z0,z1,z2,z4,z5,z1372]),(0,[z129,z0,z1,z2,z5,z142])],[(0,[z0,z14,z61,z4,z5,z6]),(0,[z33,z2,z16,z4,z5,z56]),(0,[z0,z1,z2,z21,z1373,z6])],[(0,[z13,z73,z346,z4,z5,z6]),(0,[z25,z1,z680,z4,z5,z6]),(0,[z0,z189,z2,z29,z5,z6])],[(0,[z181,z1,z2,z4,z435,z6]),(0,[z0,z1,z2,z456,z5,z6]),(0,[z0,z189,z2,z239,z5,z6]),(0,[z58,z1,z12,z4,z5,z6]),(0,[z0,z501,z2,z4,z5,z423])],[(0,[z0,z1,z2,z4,z5,z1374]),(0,[z0,z2,z396,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z459])],[(0,[z1,z2,z4,z125,z5,z263]),(0,[z25,z1,z2,z1273,z5,z6]),(0,[z100,z1,z2,z184,z5,z6]),(0,[z17,z1,z2,z4,z80,z6]),(0,[z0,z1,z1375,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z263]),(0,[z0,z1,z264,z21,z5,z6]),(0,[z1376,z1,z2,z21,z5,z6]),(0,[z57,z1,z2,z102,z5,z6]),(0,[z0,z1,z2,z4,z1377,z6])]],
   [[(0,[z0,z1,z2,z4,z6,z1378]),(0,[z0,z2,z4,z1379,z5,z6]),(0,[z693,z0,z2,z4,z5,z28]),(0,[z0,z1,z2,z4,z5,z1380]),(0,[z0,z1,z330,z10,z5,z6]),(0,[z1381,z1,z2,z4,z5,z6]),(1,[z0,z87,z4,z5,z28]),(0,[z0,z1,z264,z4,z174,z6]),(0,[z0,z1,z35,z627,z5,z6])],[(0,[z24,z0,z1,z12,z161,z6]),(0,[z1382,z1,z2,z4,z5,z6])],[(0,[z0,z2,z406,z29,z5,z6]),(0,[z0,z2,z29,z5,z6,z473]),(0,[z101,z0,z2,z4,z173,z28])],[(0,[z1,z2,z16,z302,z5,z6]),(0,[z0,z1,z264,z29,z5,z6]),(0,[z1383,z1,z2,z21,z5,z6]),(0,[z101,z2,z4,z5,z126,z28])],[(0,[z1,z16,z4,z5,z449,z6]),(0,[z25,z1,z2,z4,z190,z6]),(0,[z74,z0,z43,z21,z5,z6]),(0,[z0,z285,z2,z4,z5,z6]),(0,[z0,z1,z2,z34,z5,z6]),(0,[z486,z1,z49,z4,z5,z6])],[(0,[z1,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1384]),(0,[z0,z1,z2,z1385,z5,z6]),(0,[z0,z1386,z2,z4,z5,z6])],[(0,[z13,z17,z2,z29,z5,z6]),(0,[z1,z2,z16,z4,z5,z432]),(0,[z25,z1,z12,z4,z5,z6]),(0,[z0,z1,z2,z4,z138,z117]),(0,[z0,z1,z2,z29,z5,z423]),(0,[z1,z2,z4,z1387,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1388]),(0,[z0,z390,z2,z5,z6,z142])],[(0,[z1,z16,z4,z281,z5,z6]),(0,[z0,z1,z2,z4,z5,z1389]),(0,[z0,z2,z21,z235,z5,z6])],[(0,[z152,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z56,z115]),(0,[z0,z1,z2,z4,z5,z1390])],[(0,[z0,z1,z2,z4,z1391,z6]),(0,[z1,z2,z1392,z4,z5,z6]),(0,[z181,z1,z2,z4,z568,z6]),(0,[z15,z1,z2,z4,z5,z1064]),(0,[z0,z1,z2,z4,z1393,z6])],[(0,[z22,z1,z16,z4,z139,z6]),(0,[z0,z401,z2,z4,z5,z56]),(1,[z0,z2,z723,z5,z6]),(0,[z0,z109,z2,z4,z45,z6]),(0,[z0,z1,z2,z140,z5,z30])],[(0,[z0,z1,z346,z433,z5,z6]),(0,[z0,z1,z2,z4,z1394,z6]),(0,[z1,z330,z16,z4,z5,z6]),(0,[z67,z1,z2,z29,z5,z86]),(0,[z158,z1,z2,z159,z5,z6]),(0,[z0,z1,z2,z151,z5,z6]),(0,[z0,z1395,z2,z4,z5,z6])],[(0,[z730,z1,z132,z4,z5,z6]),(0,[z1,z2,z16,z456,z5,z6]),(0,[z0,z1,z2,z4,z5,z1396]),(0,[z0,z1,z2,z1397,z5,z6]),(0,[z0,z1,z2,z21,z5,z205])],[(0,[z0,z1,z346,z269,z5,z6]),(0,[z279,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z4,z5,z459]),(0,[z1398,z1,z2,z4,z5,z6]),(0,[z0,z1,z35,z400,z5,z6]),(0,[z9,z0,z330,z4,z76,z6]),(0,[z180,z59,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1399]),(0,[z0,z2,z4,z5,z6,z954]),(0,[z0,z1400,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z61,z29,z5,z6]),(0,[z360,z226,z2,z4,z5,z6]),(0,[z0,z501,z2,z4,z5,z6]),(0,[z57,z1,z2,z4,z174,z6]),(0,[z0,z109,z2,z4,z78,z6]),(0,[z0,z1,z35,z645,z5,z6]),(0,[z1401,z1,z2,z4,z5,z6]),(0,[z47,z93,z1,z2,z4,z26])],[(0,[z64,z2,z16,z29,z5,z6]),(0,[z130,z1,z2,z4,z18,z6])],[(0,[z0,z1,z2,z1402,z5,z6]),(0,[z25,z1,z2,z102,z5,z6]),(0,[z25,z1,z82,z4,z5,z30]),(0,[z74,z0,z43,z266,z5,z6])],[(0,[z1,z2,z1403,z4,z5,z6]),(0,[z124,z25,z2,z29,z5,z6]),(0,[z0,z2,z29,z5,z511,z6]),(0,[z0,z1,z1404,z4,z5,z6])],[(0,[z1,z2,z352,z159,z5,z6]),(0,[z484,z0,z43,z4,z5,z6]),(0,[z124,z0,z2,z29,z5,z6]),(0,[z249,z1,z2,z4,z55,z6]),(0,[z0,z285,z2,z34,z5,z6]),(0,[z0,z1,z2,z1405,z5,z6])],[(0,[z1,z2,z16,z34,z5,z6]),(0,[z15,z1,z2,z4,z5,z27]),(0,[z0,z2,z374,z29,z5,z6]),(0,[z217,z1,z2,z83,z5,z6]),(0,[z0,z1,z330,z4,z5,z459])],[(0,[z1406,z1,z2,z4,z5,z6]),(0,[z186,z14,z2,z4,z5,z6])],[(0,[z15,z1,z2,z4,z5,z525]),(0,[z1,z132,z23,z4,z5,z6]),(0,[z185,z0,z1,z2,z325,z6])],[(0,[z0,z1,z2,z743,z5,z6]),(0,[z494,z0,z2,z29,z5,z6]),(0,[z13,z116,z1,z2,z4,z6]),(0,[z74,z0,z933,z4,z5,z6]),(0,[z0,z189,z2,z4,z5,z6]),(0,[z58,z1,z2,z21,z5,z6]),(0,[z0,z1,z35,z156,z5,z6]),(0,[z1407,z1,z2,z4,z5,z6]),(0,[z0,z420,z2,z4,z357,z6]),(0,[z104,z0,z1,z4,z5,z782])],[(0,[z16,z43,z4,z5,z76,z6]),(0,[z100,z1,z2,z700,z5,z6]),(0,[z2,z21,z159,z29,z5,z6]),(0,[z1,z2,z4,z5,z6,z1408]),(0,[z47,z0,z1,z2,z4,z38])],[(0,[z0,z1,z2,z4,z5,z1409]),(0,[z181,z1,z2,z29,z20,z6]),(0,[z0,z1,z2,z29,z1410,z6]),(0,[z1411,z1,z2,z4,z5,z6])],[(0,[z0,z401,z2,z29,z5,z6]),(0,[z0,z1,z2,z4,z1373,z6]),(0,[z0,z1,z2,z4,z5,z1412]),(0,[z0,z1413,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z364,z31])],[(0,[z1,z61,z4,z125,z5,z6]),(0,[z13,z73,z2,z433,z5,z6]),(0,[z0,z2,z29,z5,z6,z263]),(0,[z9,z0,z2,z29,z76,z6]),(0,[z0,z500,z2,z29,z5,z6])],[(0,[z0,z2,z269,z29,z5,z6]),(0,[z1,z2,z16,z151,z5,z6]),(0,[z1,z329,z16,z4,z5,z6]),(0,[z0,z1,z2,z36,z45,z6]),(0,[z0,z265,z4,z5,z6,z133])],[(0,[z25,z1,z145,z4,z5,z6]),(0,[z9,z0,z2,z411,z76,z6]),(0,[z129,z0,z1,z2,z161,z6])],[(0,[z52,z1,z16,z4,z5,z6]),(0,[z1,z87,z16,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1414])]],
   [[(0,[z0,z2,z622,z29,z5,z6]),(0,[z100,z380,z2,z4,z5,z6]),(0,[z0,z1,z264,z4,z5,z6]),(0,[z1376,z1,z2,z4,z5,z6]),(0,[z212,z1,z153,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z821])],[(0,[z1415,z1,z2,z4,z5,z6]),(0,[z0,z109,z2,z171,z5,z6]),(0,[z0,z1,z2,z4,z1416,z6])],[(0,[z0,z1,z2,z4,z5,z1417]),(0,[z0,z1,z2,z21,z112,z6]),(0,[z25,z1,z2,z21,z5,z6]),(0,[z25,z1,z2,z4,z5,z291]),(0,[z25,z1,z2,z4,z11,z6]),(0,[z0,z1418,z2,z4,z5,z6]),(0,[z0,z1,z2,z1419,z5,z6]),(0,[z0,z1420,z2,z4,z5,z6]),(0,[z121,z1,z2,z140,z5,z6])],[(0,[z0,z1,z2,z4,z6,z1421]),(0,[z25,z1,z2,z4,z174,z6]),(0,[z1220,z1,z2,z4,z5,z6]),(0,[z0,z2,z29,z26,z5,z28]),(0,[z0,z1,z2,z1422,z5,z6]),(1,[z0,z1,z12,z161,z6])],[(0,[z72,z103,z2,z21,z5,z6]),(0,[z132,z16,z43,z4,z5,z6]),(0,[z74,z25,z43,z4,z5,z6]),(0,[z0,z2,z29,z545,z5,z6]),(0,[z1,z2,z4,z824,z5,z6]),(0,[z1383,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z825,z5,z6]),(0,[z1423,z1,z2,z4,z5,z6])],[(0,[z25,z1,z2,z352,z5,z6]),(0,[z0,z1,z2,z1424,z5,z6]),(0,[z0,z1,z2,z4,z5,z1425]),(0,[z0,z1,z2,z21,z5,z578]),(0,[z1426,z1,z2,z4,z5,z6]),(0,[z1427,z1,z2,z4,z5,z6]),(0,[z24,z0,z1,z2,z161,z423])],[(0,[z0,z1,z2,z29,z112,z6]),(0,[z25,z1,z2,z29,z5,z6]),(0,[z0,z43,z29,z5,z139,z6]),(0,[z0,z189,z37,z4,z5,z6])],[(0,[z15,z1,z61,z4,z5,z6]),(0,[z72,z103,z2,z352,z5,z6]),(0,[z25,z1,z2,z239,z5,z6]),(0,[z0,z1,z2,z1428,z5,z6])],[(0,[z72,z103,z2,z29,z5,z6]),(0,[z1,z2,z1429,z4,z5,z6]),(0,[z0,z1,z2,z1430,z5,z6]),(0,[z0,z1,z1431,z4,z5,z6])],[(0,[z97,z1,z2,z159,z5,z6]),(0,[z67,z1,z2,z4,z5,z86]),(0,[z0,z1,z2,z1432,z5,z6]),(0,[z0,z1,z2,z29,z5,z578])],[(0,[z13,z72,z2,z29,z5,z6]),(0,[z0,z1,z1433,z4,z5,z6]),(0,[z1,z2,z4,z882,z5,z6]),(0,[z0,z43,z4,z76,z139,z6]),(0,[z0,z2,z21,z723,z5,z6]),(0,[z1,z2,z1434,z4,z5,z6]),(0,[z0,z1,z2,z140,z11,z6])],[(0,[z0,z1,z2,z4,z1435,z6]),(0,[z0,z2,z4,z29,z112,z6]),(0,[z25,z1,z2,z246,z5,z6]),(0,[z0,z1,z2,z21,z5,z148]),(0,[z1436,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z156,z5,z291])],[(0,[z1,z2,z4,z973,z5,z6]),(0,[z0,z1,z1437,z4,z5,z6])],[(0,[z13,z73,z2,z4,z112,z6]),(0,[z100,z1,z2,z4,z5,z263]),(0,[z0,z1,z2,z4,z5,z1438]),(0,[z1,z2,z16,z411,z5,z6]),(0,[z0,z1,z2,z1439,z5,z6]),(0,[z9,z0,z2,z10,z76,z6]),(0,[z0,z160,z2,z4,z45,z6])],[(0,[z25,z1,z2,z374,z5,z6]),(0,[z0,z189,z2,z4,z139,z6]),(0,[z0,z1440,z2,z4,z5,z6])],[(0,[z368,z1,z2,z4,z5,z27]),(0,[z25,z1,z2,z4,z6,z1340]),(0,[z217,z1,z2,z21,z5,z6]),(0,[z709,z1,z2,z21,z5,z6]),(0,[z249,z1,z2,z4,z5,z631]),(0,[z0,z59,z12,z4,z5,z6])]],
   [[(0,[z100,z1,z2,z269,z5,z6]),(0,[z25,z1,z2,z266,z5,z6]),(0,[z25,z380,z2,z4,z5,z6]),(0,[z697,z0,z2,z29,z5,z6]),(0,[z0,z1,z2,z21,z163,z6]),(0,[z0,z1,z2,z1441,z5,z6]),(0,[z0,z189,z2,z151,z5,z6])],[(0,[z1,z193,z16,z4,z5,z6]),(0,[z0,z2,z21,z341,z5,z6]),(0,[z0,z265,z2,z792,z5,z6])],[(0,[z0,z1,z2,z433,z5,z6]),(0,[z0,z160,z2,z4,z78,z6]),(0,[z166,z0,z1,z2,z161,z6]),(0,[z0,z1,z2,z1442,z5,z6]),(0,[z0,z1,z2,z49,z5,z142])],[(0,[z13,z2,z29,z5,z86,z6]),(0,[z253,z1,z16,z4,z5,z6]),(0,[z1,z16,z43,z29,z5,z6]),(0,[z0,z1,z2,z4,z5,z1443]),(0,[z17,z417,z1,z2,z4,z6]),(0,[z217,z1,z2,z29,z5,z6]),(0,[z186,z2,z29,z5,z6,z28]),(0,[z0,z2,z29,z584,z5,z6]),(0,[z0,z14,z2,z723,z5,z6]),(0,[z0,z1,z2,z4,z55,z631]),(0,[z0,z1,z2,z4,z1444,z6]),(0,[z48,z0,z1,z2,z5,z904])],[(0,[z1,z2,z16,z4,z5,z423]),(0,[z25,z265,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z791,z5]),(0,[z1,z2,z1445,z4,z5,z6]),(0,[z93,z1,z2,z21,z5,z6]),(0,[z0,z39,z2,z21,z5,z6])],[(0,[z0,z1,z61,z4,z5,z229]),(0,[z25,z1,z2,z4,z1251,z6]),(0,[z1,z2,z4,z877,z18,z6]),(0,[z0,z1,z2,z1446,z5,z6]),(0,[z1426,z1,z2,z34,z5,z6])],[(0,[z189,z2,z16,z4,z5,z6]),(0,[z0,z1,z1447,z4,z5,z6]),(0,[z0,z33,z2,z172,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1448]),(0,[z25,z1,z2,z4,z113,z6]),(0,[z0,z1,z2,z4,z1410,z6]),(0,[z0,z1,z2,z4,z1449,z6]),(0,[z104,z0,z1,z21,z5,z133]),(1,[z0,z1,z36,z5,z291]),(0,[z104,z0,z1,z4,z11,z133])],[(0,[z0,z1,z2,z1450,z5,z6]),(0,[z1,z16,z406,z4,z5,z6]),(0,[z9,z25,z2,z4,z76,z6]),(0,[z93,z1,z2,z29,z5,z6]),(0,[z217,z2,z4,z29,z5,z6])],[(0,[z0,z1,z2,z266,z5,z148]),(0,[z9,z0,z2,z4,z76,z6]),(0,[z0,z1451,z2,z4,z5,z6]),(0,[z24,z0,z1,z2,z161,z6])],[(0,[z0,z668,z2,z29,z5,z6]),(0,[z279,z1,z264,z4,z5,z6])],[(0,[z1,z149,z16,z4,z5,z6]),(0,[z25,z1,z478,z4,z5,z6]),(0,[z217,z1,z2,z125,z5,z6]),(0,[z1,z2,z29,z5,z1355,z6])],[(0,[z1,z2,z16,z10,z5,z6]),(0,[z202,z1,z2,z21,z5,z6]),(0,[z731,z1,z2,z21,z5,z6]),(0,[z0,z1,z87,z4,z173,z6]),(0,[z1452,z1,z2,z4,z5,z6]),(0,[z0,z265,z2,z140,z5,z6])],[(0,[z0,z1,z2,z4,z112,z263]),(0,[z25,z1,z2,z4,z5,z263]),(0,[z1,z576,z2,z4,z18,z6])],[(0,[z1,z2,z16,z461,z5,z6]),(0,[z0,z1,z2,z266,z163,z6]),(0,[z455,z0,z1,z2,z161,z6]),(1,[z0,z1,z4,z5,z782]),(0,[z0,z1453,z2,z4,z5,z6])],[(0,[z0,z2,z680,z29,z5,z6]),(0,[z1,z2,z4,z5,z1064,z27]),(0,[z0,z1,z132,z4,z5,z148]),(0,[z323,z0,z1,z36,z5,z6]),(0,[z0,z1454,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z269,z112,z6]),(0,[z345,z1,z2,z4,z20,z6]),(0,[z0,z521,z2,z21,z5,z6]),(0,[z0,z1,z2,z4,z1455,z6]),(0,[z0,z1,z2,z4,z371,z31])],[(0,[z25,z1,z2,z302,z5,z6]),(0,[z1,z2,z4,z20,z877,z6]),(0,[z0,z1,z2,z4,z55,z527]),(0,[z0,z1,z2,z4,z5,z1336]),(0,[z0,z1,z2,z4,z1456,z6]),(0,[z0,z1,z1457,z4,z5,z6])],[(0,[z9,z0,z2,z4,z76,z459]),(0,[z227,z1,z2,z4,z11,z6]),(0,[z0,z1,z153,z4,z154,z6])],[(0,[z0,z1,z2,z4,z112,z6]),(0,[z25,z1,z2,z4,z5,z6]),(0,[z1,z2,z16,z433,z5,z6]),(0,[z181,z1,z2,z4,z637,z6]),(0,[z0,z1,z2,z4,z714,z6]),(0,[z0,z1,z2,z758,z5,z6]),(0,[z0,z1,z2,z1458,z5,z6]),(0,[z1,z2,z1459,z4,z5,z6])],[(0,[z0,z1,z2,z4,z835,z6]),(0,[z25,z1,z2,z4,z5,z432]),(0,[z100,z1,z2,z882,z5,z6]),(0,[z0,z1,z132,z4,z163,z6]),(0,[z0,z1,z2,z4,z5,z1460]),(0,[z0,z1,z2,z1461,z5,z6]),(0,[z0,z1,z4,z898,z5,z6])],[(0,[z72,z103,z2,z4,z5,z6]),(0,[z1,z2,z16,z269,z5,z6]),(0,[z1,z2,z269,z125,z5,z6]),(0,[z0,z1,z2,z1462,z5,z6]),(0,[z1463,z1,z2,z4,z5,z6]),(1,[z0,z2,z4,z5,z954]),(0,[z454,z0,z1,z4,z5,z133]),(0,[z1464,z1,z2,z4,z5,z6]),(0,[z0,z1,z657,z4,z5,z30])],[(0,[z100,z380,z2,z119,z5,z6]),(0,[z0,z1,z2,z4,z5,z578])],[(0,[z1,z2,z1303,z4,z5,z6]),(0,[z25,z1,z274,z4,z5,z6]),(0,[z293,z0,z1,z4,z5,z133]),(0,[z0,z33,z2,z21,z5,z56])],[(0,[z0,z1,z2,z4,z115,z28]),(0,[z1,z2,z403,z1078,z5,z6]),(0,[z0,z1,z2,z1465,z5,z6]),(0,[z69,z0,z1,z36,z5,z6]),(0,[z1466,z1,z2,z4,z5,z6]),(0,[z0,z2,z172,z5,z6,z28]),(0,[z0,z1,z2,z4,z821,z6])],[(0,[z0,z1,z2,z4,z1467,z6]),(0,[z0,z1,z2,z767,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1468]),(0,[z0,z1,z2,z1469,z5,z6]),(0,[z1,z2,z4,z5,z86,z1064]),(0,[z202,z1,z2,z266,z5,z6]),(0,[z0,z1,z2,z4,z5,z1470]),(0,[z0,z501,z2,z4,z5,z205])],[(0,[z1,z2,z4,z20,z5,z263]),(0,[z13,z1,z2,z4,z19,z5]),(0,[z25,z165,z2,z29,z5,z6]),(0,[z25,z1,z2,z456,z5,z6]),(0,[z74,z0,z43,z29,z5,z6]),(0,[z0,z2,z21,z29,z5,z6]),(0,[z250,z1,z2,z21,z5,z6]),(0,[z0,z59,z2,z21,z5,z6]),(0,[z0,z189,z2,z1428,z5,z6])],[(0,[z25,z1,z2,z4,z5,z1374]),(0,[z25,z1,z2,z4,z5,z459]),(0,[z1471,z1,z2,z4,z5,z6]),(0,[z1,z2,z1472,z4,z5,z6])],[(0,[z217,z1,z2,z269,z5,z6]),(0,[z33,z2,z16,z29,z5,z6]),(0,[z0,z1,z2,z1473,z5,z6])],[(0,[z0,z64,z552,z4,z5,z6]),(0,[z0,z1,z1474,z4,z5,z6])],[(0,[z1,z2,z4,z5,z1475,z6]),(0,[z0,z1,z2,z172,z173,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 478) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 478).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 960).take 475) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1435).take 94) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1529)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [478, 482, 475, 94] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 79).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 161).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 255).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 343).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 424).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 500).take 12).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [79, 82, 94, 88, 81, 76, 12] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

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

end PEqualNP.Outside.L_meta_39575

theorem PEqualNP.Outside.L_meta_39575 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901482 * 2 ^ 32 + 4278124232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901482 * 2 ^ 32 + 4278124232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39575.solve