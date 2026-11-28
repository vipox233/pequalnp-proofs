import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42518

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4240500864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0454085718c06d92#64 ++ 0x0008a810ae3180db#64 ++ 0x0cfd18ff18c0fffd#64 ++ 0x3419fa31fe3181ff#64 : BitVec 256),
   (0x113063300b5b16a4#64 ++ 0x042260c66016b62d#64 ++ 0x3332e7301fff1ffb#64 ++ 0xfc6665ce603ffe3f#64 : BitVec 256),
   (0xc2c305c160ada338#64 ++ 0x0985860b82c15b46#64 ++ 0xc3c307c3e0ffe3f7#64 ++ 0x9f87860f87c1ffc7#64 : BitVec 256),
   (0x6c03b802b506d840#64 ++ 0x22d80770056a0db0#64 ++ 0xfc03f803ff07fc6f#64 ++ 0xeff807f007fe0ff8#64 : BitVec 256),
   (0xbffc0003def00000#64 ++ 0x437ff80007bde000#64 ++ 0xfffc0003fff8005f#64 ++ 0x4bfff80007fff000#64 : BitVec 256),
   (0xfbabd6a800000000#64 ++ 0x13f757ad50000000#64 ++ 0xfffffffc0000003f#64 ++ 0xf3fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [11, 8]⟩, ⟨.and, [12, 6]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff18c0fffd 0x3419fa31fe3181ff

def z1 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7301fff1ffb 0xfc6665ce603ffe3f

def z2 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f803ff07fc6f 0xeff807f007fe0ff8

def z3 : W := mkw 0x82c005c140a92338 0x0905800b82815246 0x03c007c000f80390 0x1007800f8001f007

def z4 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffd18fffff8ffff 0x7ffffa31fffff1ff

def z5 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c307c3e0ffe3f7 0x9f87860f87c1ffc7

def z6 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc0000003f 0xf3fffffff8000000

def z7 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3000000e7380002 0x4be6000001ce7000

def z8 : W := mkw 0xfbabd6a8c6300000 0x53f757ad518c6000 0xfffffffce738003f 0xfbfffffff9ce7000

def z9 : W := mkw 0x113062300b521484 0x042260c46016a429 0x3030e0301f001c08 0x606061c0603e0038

def z10 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0003fff8005f 0x4bfff80007fff000

def z11 : W := mkw 0x1120422000000000 0x0022408440000000 0x3332e7300000003b 0xf06665ce60000000

def z12 : W := mkw 0xfbbbf7b80b5b16a4 0x17f777ef7016b62d 0xfffffffc1fff1fff 0xfffffffff83ffe3f

def z13 : W := mkw 0x4003d6a800000000 0x108007ad50000000 0x0003fffc00000020 0xb00007fff8000000

def z14 : W := mkw 0xffffdeffdef06d92 0x53ffffbdffbde0db 0xfffffffffff8ffff 0xfffffffffffff1ff

def z15 : W := mkw 0xbba8000000000000 0x0377500000000000 0xfffd18fc0000003f 0x73fffa31f8000000

def z16 : W := mkw 0x04540003def00000 0x4008a80007bde000 0x00000003fff80040 0x0800000007fff000

def z17 : W := mkw 0xfbabd7a8602d8228 0x1bf757af50c05b04 0xfffffffce03f003f 0xfbfffffff9c07e00

def z18 : W := mkw 0x0454084718c06912 0x0008a8108e3180d2 0x0cfd18cf18c0e05d 0x0019fa319e3181c0

def z19 : W := mkw 0xaecc0003d4a00000 0x435d980007a94000 0xcfcc0003e0f80057 0x0b9f980007c1f000

def z20 : W := mkw 0x82c0000140a00000 0x0105800002814000 0x03c0000000f80010 0x000780000001f000

def z21 : W := mkw 0x2c00b80295025840 0x22580170052a04b0 0x3c00f8001f001c08 0x607801f0003e0038

def z22 : W := mkw 0xeec3bdc3f5affb78 0x2bdd877b87eb5ff6 0xffc3ffc3ffffffff 0xffff87ff87ffffff

def z23 : W := mkw 0x0010001008400480 0x0000200020108009 0x0030003000c00390 0x1000600060018007

def z24 : W := mkw 0xfbbbd6b808400480 0x13f777ad70108009 0xfffffffc18c01fff 0xf7fffffff831803f

def z25 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0000000318c0ffc0 0x04000000063181ff

def z26 : W := mkw 0x0000085400006d92 0x00000010a80000db 0x000000000000ff80 0x04000000000001ff

def z27 : W := mkw 0xc283048000000000 0x0185060900000000 0xc302070000000002 0x8386040e00000000

def z28 : W := mkw 0x6c13b912bf5fdee4 0x26d82772257ebfbd 0xfc03f803ffffffef 0xeff807f007ffffff

def z29 : W := mkw 0x6c039802b404c840 0x22d8073005680990 0xcc011803e000e004 0x0398023007c001c0

def z30 : W := mkw 0xbbb86330cf7b16a4 0x477770c6619ef62d 0xf332e730ffff1ffb 0xffe665ce61fffe3f

def z31 : W := mkw 0xd3f367f16bffb7bc 0x0da7e6cfe2d7ff6f 0xf3f3e7f3ffffffff 0xffe7e7cfe7ffffff

def z32 : W := mkw 0x04540857def06d92 0x4008a810afbde0db 0x0cfd18fffff8fffd 0x3c19fa31fffff1ff

def z33 : W := mkw 0x0414081618404c82 0x000828102c308099 0x0cfd18fc18001c3d 0x3019fa31f8300038

def z34 : W := mkw 0x0414000218400000 0x0008280004308000 0x0c3c000018000008 0x0018780000300000

def z35 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0x3ffc00001ff80018 0x407ff800003ff000

def z36 : W := mkw 0xbffc0013def00480 0x437ff80027bde009 0xfffc0033fff81fff 0x7ffff80067fff03f

def z37 : W := mkw 0x3928000086100000 0x42725000010c2000 0x3000000007000000 0x40600000000e0000

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x0302070000000033 0x9006040e00000000

def z39 : W := mkw 0x8280000000000000 0x0105000000000000 0xc3c0000000000017 0x0387800000000000

def z40 : W := mkw 0x113062300b521484 0x042260c46016a429 0x3330e0301ff81c5b 0x686661c0603ff038

def z41 : W := mkw 0x6c43b943f5affb78 0x2ad8877287eb5ff6 0xfc03f803ffffffef 0xeff807f007ffffff

def z42 : W := mkw 0x157400031ad00000 0x002ae8000635a000 0x3ffc00031ff8005f 0x487ff800063ff000

def z43 : W := mkw 0x157463331bdb16a4 0x042ae8c66637b62d 0x3ffee7331fff1fff 0xfc7ffdce663ffe3f

def z44 : W := mkw 0x113043300a5906a4 0x042260866014b20d 0x0330073000f80390 0x1006600e6001f007

def z45 : W := mkw 0x7d33fb32bf5fdee4 0x26fa67f6657ebfbd 0xff33ff33ffffffff 0xfffe67fe67ffffff

def z46 : W := mkw 0xeac3b5c1e5afb378 0x2bd5876b83cb5f66 0xf3c3e7c3e7ffe3f7 0xdfe787cf87cfffc7

def z47 : W := mkw 0x00000000c6300000 0x40000000018c6000 0x00000000e7380000 0x0800000001ce7000

def z48 : W := mkw 0xbbe80001c6b00000 0x4377d000038d6000 0xf3c00003e7f80057 0x4be7800007cff000

def z49 : W := mkw 0x3d3c62329f521484 0x467a78c4653ea429 0x3c3ce0301f001c08 0x607879c0603e0038

def z50 : W := mkw 0xee8bbc8ab506d840 0x33dd1779156a0db0 0xfccff8cfff07fc6f 0xeff99ff19ffe0ff8

def z51 : W := mkw 0xbba8d6a800000000 0x137751ad50000000 0x3ffcfffc00000018 0x707ff9fff8000000

def z52 : W := mkw 0x113043300a5906a4 0x042260866014b20d 0x3332e73000f803bb 0xf06665ce6001f007

def z53 : W := mkw 0x15744a7718c06d92 0x002ae894ee3180db 0x3fffffff18c0ffff 0xf47ffffffe3181ff

def z54 : W := mkw 0x4003d6a800000000 0x108007ad50000000 0x0cfffffc0000003d 0xb019fffff8000000

def z55 : W := mkw 0x0040004100802110 0x0000800082010042 0x00c100c300c0e3f5 0x14018201860181c7

def z56 : W := mkw 0x0414081618404c82 0x000828102c308099 0x0c3c183c18001c08 0x2018783078300038

def z57 : W := mkw 0x0000200001021000 0x0000004000020420 0x3002e0001f071c6b 0xec6005c0003e0e38

def z58 : W := mkw 0x00006330010b16a4 0x040000c66002162d 0x0002e73000071fa0 0xb40005ce60000e3f

def z59 : W := mkw 0x400305c0200da338 0x0880060b80401b46 0x000307c00007e3a0 0x9400060f80000fc7

def z60 : W := mkw 0x4003b8002106d840 0x2080077000420db0 0x0003f8000007fc20 0xa40007f000000ff8

def z61 : W := mkw 0xffffd6abdef00000 0x53ffffad57bde000 0xfffffffffff8007f 0xfbfffffffffff000

def z62 : W := mkw 0xffebffebf5affb78 0x3bffd7ffd7eb5ff6 0xffffffffffffffff 0xffffffffffffffff

def z63 : W := mkw 0x0010001008400480 0x0000200020108009 0x0030003018c01ff9 0x340060006031803f

def z64 : W := mkw 0x15746b771bdb7fb6 0x042ae8d6ee37b6ff 0x3fffffff1fffffff 0xfc7ffffffe3fffff

def z65 : W := mkw 0x0000004000002110 0x0000000080000042 0x000100c00000e3a0 0x14000201800001c7

def z66 : W := mkw 0xffabdeaab404c840 0x33ff57bd55680990 0xffffffffe000e03f 0xf3ffffffffc001c0

def z67 : W := mkw 0xaedc0003def00000 0x435db80007bde000 0xcccc0003fff80044 0x0b99980007fff000

def z68 : W := mkw 0x2800900000000000 0x0250012000000000 0x3c00f80000000008 0x607801f000000000

def z69 : W := mkw 0x0054005508c02592 0x0000a800aa11804b 0x00fc00fc00c00390 0x1001f801f8018007

def z70 : W := mkw 0x6803b000a5069040 0x22d00760014a0d20 0xf002e000e7070002 0xcbe005c001ce0e00

def z71 : W := mkw 0x6c57b857bdc6fdd2 0x22d8af70af7b8dfb 0xfcfff8ffffc7ffff 0xfff9fff1ffff8fff

def z72 : W := mkw 0xfbebd7e960ada338 0x1bf7d7afd2c15b46 0xffffffffe0ffe3ff 0xffffffffffc1ffc7

def z73 : W := mkw 0xfbebd6e900802110 0x13f7d7add2010042 0xffffffff00c0e3ff 0xf7fffffffe0181c7

def z74 : W := mkw 0x6803900000000000 0x02d0072000000000 0xcc01180000000004 0x0398023000000000

def z75 : W := mkw 0x11206320031b1224 0x042240c640063624 0x3302e700073f0002 0xc86605ce000e7e00

def z76 : W := mkw 0x93fc00014af00000 0x4127f8000295e000 0x03fc000000f80010 0x0007f8000001f000

def z77 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xf302e70000000002 0xc3e605ce00000000

def z78 : W := mkw 0xc2d305d168eda7b8 0x0985a60ba2d1db4f 0xc3f307f3f8ffffff 0xbf87e60fe7f1ffff

def z79 : W := mkw 0xc2830580602d8228 0x0985060b00c05b04 0xc3020700e0ff03f3 0x9f86040e01c1fe07

def z80 : W := mkw 0xc2830580602d8228 0x0985060b00c05b04 0xc3020700e03f0002 0x8b86040e01c07e00

def z81 : W := mkw 0xffffdfff78edefba 0x1bffffbffef1dbdf 0xfffffffff8ffffff 0xfffffffffff1ffff

def z82 : W := mkw 0x4003000000000000 0x0080060000000000 0xc003000000000027 0x8380060000000000

def z83 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f803e707e006 0xcbf807f007ce0fc0

def z84 : W := mkw 0x40030100200d8220 0x0080060200401b04 0xc3030703e0ffe3f7 0x9f86060e07c1ffc7

def z85 : W := mkw 0x113c00000a500000 0x402278000014a000 0x003c000000000000 0x0000780000000000

def z86 : W := mkw 0x0000010000090220 0x0000000200001204 0x03020700003f0002 0x8806040e00007e00

def z87 : W := mkw 0x6c57b803bdc6d840 0x22d8af70077b8db0 0xfcfff803ffc7fc7f 0xeff9fff007ff8ff8

def z88 : W := mkw 0x6c03b002b5069040 0x22d80760056a0d20 0xfc02e003ff07004f 0xcbf805c007fe0e00

def z89 : W := mkw 0x04002802b506d840 0x20080050056a0db0 0x3002e003ff07fc6b 0xec6005c007fe0ff8

def z90 : W := mkw 0xd3eb47e960ada338 0x19a7d68fd2c15b46 0xc3ff07ffe0ffe3f7 0x9f87fe0fffc1ffc7

def z91 : W := mkw 0x0444084710806912 0x000888108e2100d2 0x0ccd18cf0000e004 0x00199a319e0001c0

def z92 : W := mkw 0x113063200b5b1224 0x042260c64016b624 0x3332e7001fff005b 0xc86665ce003ffe00

def z93 : W := mkw 0x93fc43314af906a4 0x4527f8866295f20d 0x03fc073000f80390 0x1007f80e6001f007

def z94 : W := mkw 0x04002802b506d840 0x20080050056a0db0 0x00000003ff07fc40 0x0c00000007fe0ff8

def z95 : W := mkw 0xffff05c3fefda338 0x4bfffe0b87fdfb46 0xffff07c3ffffe3ff 0xdffffe0f87ffffc7

def z96 : W := mkw 0xfbabd7a8602d8228 0x1bf757af50c05b04 0xf302e700e03f0002 0xcbe605ce01c07e00

def z97 : W := mkw 0x3928d22800000000 0x127251a450000000 0x3c3cf83c00000008 0x607879f078000000

def z98 : W := mkw 0x86d40003def00000 0x410da80007bde000 0xc3c00003fff80057 0x0b87800007fff000

def z99 : W := mkw 0xbfec0003d6b00000 0x437fd80007ad6000 0xffcc0003e7380006 0x4bff980007ce7000

def z100 : W := mkw 0x0400080210004800 0x0008001004200090 0x0c0118031800fc6d 0x24180230063001f8

def z101 : W := mkw 0x6c039802b404c840 0x22d8073005680990 0xcc031803e007e067 0x8f98063007c00fc0

def z102 : W := mkw 0x6803900000000000 0x02d0072000000000 0xfc03f8000000002f 0xe3f807f000000000

def z103 : W := mkw 0xffabfeaab506d840 0x33ff57fd556a0db0 0xffffffffff07fc7f 0xfffffffffffe0ff8

def z104 : W := mkw 0x6c03fb32b50fdee4 0x26d807f6656a1fbd 0xfc03ff33ff07ffef 0xfff807fe67fe0fff

def z105 : W := mkw 0x001021100b5b16a4 0x040020422016b62d 0x030207001fff1ff3 0x9c06040e003ffe3f

def z106 : W := mkw 0x400304c02004a118 0x0880060980400942 0x000100c00000e000 0x00000201800001c0

def z107 : W := mkw 0x400367f0210fb7bc 0x0c8006cfe0421f6f 0x0003e7f00007ffa0 0xb40007cfe0000fff

def z108 : W := mkw 0x0000080000004800 0x0000001000000090 0x000118000000fc20 0x24000230000001f8

def z109 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cfd18fc0000003d 0x3019fa31f8000000

def z110 : W := mkw 0xffffdeff18c06d92 0x13ffffbdfe3180db 0xffffffff18c0ffff 0xf7fffffffe3181ff

def z111 : W := mkw 0xc2c304c160a4a118 0x0985860982c14942 0xc0c100c3e000e004 0x0381820187c001c0

def z112 : W := mkw 0x0000010000090220 0x0000000200001204 0x0302070000ff03f3 0x9c06040e0001fe07

def z113 : W := mkw 0x93b847b80a5906a4 0x1527708f7014b20d 0x03fc07fc00f80390 0x1007f80ff801f007

def z114 : W := mkw 0xc2c3000160a48000 0x0185860002c14900 0xc3c30003e0ffe077 0x8f87860007c1ffc0

def z115 : W := mkw 0x7d3fb802bf56d840 0x62fa7f70057eadb0 0xfc3ff803ff07fc6f 0xeff87ff007fe0ff8

def z116 : W := mkw 0xfbffd6fd08c02592 0x13f7ffadfa11804b 0xfffffffc00c003bf 0xf3fffffff8018007

def z117 : W := mkw 0x3d3c00029e500000 0x427a7800053ca000 0x3c3c00001f000008 0x40787800003e0000

def z118 : W := mkw 0x82c0000140a00000 0x0105800002814000 0xc3c00003e0f80057 0x0b87800007c1f000

def z119 : W := mkw 0x0000200001021000 0x0000004000020420 0x3000e0001f001c08 0x606001c0003e0038

def z120 : W := mkw 0x93fc00014af00000 0x4127f8000295e000 0x33fc00001ff8005b 0x4867f800003ff000

def z121 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3330e7301ff81f98 0x706661ce603ff03f

def z122 : W := mkw 0x4003fea82106d840 0x308007fd50420db0 0x0003fffc0007fc20 0xb40007fff8000ff8

def z123 : W := mkw 0xbffc6323dffb1224 0x477ff8c647bff624 0xfffee703ffff005f 0xcbfffdce07fffe00

def z124 : W := mkw 0x2c00080294004800 0x0258001005280090 0xfc011803ff00fc6f 0x6ff8023007fe01f8

def z125 : W := mkw 0x3938f2380b521484 0x167271e47016a429 0x3c3cf83c1f001c08 0x607879f0783e0038

def z126 : W := mkw 0x4003000020048000 0x0080060000400900 0xc0030003e007e067 0x8f80060007c00fc0

def z127 : W := mkw 0x113043300a5906a4 0x042260866014b20d 0x0332073000ff03f3 0x9c06640e6001fe07

def z128 : W := mkw 0x93e847e940a92338 0x1927d08fd2815246 0x03fc07fc00f80390 0x1007f80ff801f007

def z129 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xffcfffcc00000006 0xc3ff9fff98000000

def z130 : W := mkw 0x0000085400006d92 0x00000010a80000db 0x000118fc0000ffa0 0x34000231f80001ff

def z131 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffd18fffff8007f 0x7bfffa31fffff000

def z132 : W := mkw 0x7923f320a71f9264 0x26f247e6414e3f24 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z133 : W := mkw 0x113000000a500000 0x002260000014a000 0x333000001ff8005b 0x48666000003ff000

def z134 : W := mkw 0x113001000a590220 0x002260020014b204 0x333207001fff03fb 0xdc66640e003ffe07

def z135 : W := mkw 0xbffc6233dff21484 0x477ff8c467bfe429 0xfffce033fff81c5f 0x6bfff9c067fff038

def z136 : W := mkw 0x0040014160ada338 0x0800800282c15b46 0x00000003e0ffe3c0 0x0c00000007c1ffc7

def z137 : W := mkw 0xc6d70dd778edefba 0x098dae1baef1dbdf 0xcfff1ffff8ffffff 0xbf9ffe3ffff1ffff

def z138 : W := mkw 0x2c00000294000000 0x0258000005280000 0xfc000003ff00004f 0x4bf8000007fe0000

def z139 : W := mkw 0xffffb803fff6d840 0x63ffff7007ffedb0 0xfffff803fffffc7f 0xeffffff007fffff8

def z140 : W := mkw 0xc2c305c140a92338 0x0985860b82815246 0xc3c307c000f803b7 0x9387860f8001f007

def z141 : W := mkw 0xbffc6b77dffb7fb6 0x477ff8d6efbff6ff 0xffffffffffffffff 0xffffffffffffffff

def z142 : W := mkw 0xbffc0847def06912 0x437ff8108fbde0d2 0xfffd18cffff8e05f 0x4bfffa319ffff1c0

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x00fc00fc00000010 0x1001f801f8000000

def z144 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xf3c3e7c000000037 0xd3e787cf80000000

def z145 : W := mkw 0x1120422000000000 0x0022408440000000 0x3030e03000000008 0x606061c060000000

def z146 : W := mkw 0xea8b948800000000 0x13d5172910000000 0xcfcf1fcc00000037 0x939f9e3f98000000

def z147 : W := mkw 0xd3e367e163bfb33c 0x0da7c6cfc2c77f66 0xf3c3e7c3e7ffe3f7 0xdfe787cf87cfffc7

def z148 : W := mkw 0x00000100602d8228 0x0800000200c05b04 0x00000000e03f0000 0x0800000001c07e00

def z149 : W := mkw 0x0410081218404c80 0x0008201024308099 0x0c31183318c0fffd 0x34186230663181ff

def z150 : W := mkw 0x3d30fa329f525cc4 0x267a61f4653ea4b9 0x3c30f8301f001c08 0x607861f0603e0038

def z151 : W := mkw 0x2800000084000000 0x0250000001080000 0xf0000000e7000002 0x4be0000001ce0000

def z152 : W := mkw 0xbffc6333dffb16a4 0x477ff8c667bff62d 0xfffee733ffff1fff 0xfffffdce67fffe3f

def z153 : W := mkw 0x0050005108c02590 0x0000a000a211804b 0x00f100f318c0fffd 0x3401e201e63181ff

def z154 : W := mkw 0x7d33fa32bf56dcc4 0x26fa67f4657eadb9 0xfc33f833ff07fc6f 0xeff867f067fe0ff8

def z155 : W := mkw 0xeed7bdd7fdeffffa 0x2bddaf7baffbdfff 0xffffffffffffffff 0xffffffffffffffff

def z156 : W := mkw 0x93a846a800000000 0x1127508d50000000 0x03fc07fc00000010 0x1007f80ff8000000

def z157 : W := mkw 0x0000010000090220 0x0000000200001204 0x00020700000703a0 0x9400040e00000e07

def z158 : W := mkw 0xfbabb000e7369040 0x63f7576001ce6d20 0xf302e000e73f0002 0xcbe605c001ce7e00

def z159 : W := mkw 0xbffc0057def02592 0x437ff800afbde04b 0xfffc00fffff803df 0x5bfff801fffff007

def z160 : W := mkw 0x001021100b5b16a4 0x040020422016b62d 0x000000001fff1fc0 0x0c000000003ffe3f

def z161 : W := mkw 0xea8b948800000000 0x13d5172910000000 0xcccd18cc00000004 0x03999a3198000000

def z162 : W := mkw 0xfbebd6e960a4a118 0x1bf7d7add2c14942 0xffffffffe000e03f 0xf3ffffffffc001c0

def z163 : W := mkw 0xffff0dd7fefdefba 0x4bfffe1baffdfbdf 0xffff1fffffffffff 0xfffffe3fffffffff

def z164 : W := mkw 0x04102912bf5fdee4 0x24082052257ebfbd 0x00000003ffffffc0 0x0c00000007ffffff

def z165 : W := mkw 0x00106330094b16a4 0x040020c66012962d 0x0032e73018c71ff9 0xb40065ce60318e3f

def z166 : W := mkw 0x6c03980210004800 0x02d8073004200090 0xfc03f8031800fc6f 0xe7f807f0063001f8

def z167 : W := mkw 0x93a846a800000000 0x1127508d50000000 0x0300070000000000 0x0006000e00000000

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c100c000000035 0x1001820180000000

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300000000f80053 0x080600000001f000

def z170 : W := mkw 0x3d3c00029e500000 0x427a7800053ca000 0xfc3c0003ff00004f 0x4bf8780007fe0000

def z171 : W := mkw 0x6c03b80295025840 0x22d80770052a04b0 0xfc03f8001f001c2f 0xe3f807f0003e0038

def z172 : W := mkw 0x3d3cb8029f525840 0x627a7970053ea4b0 0x3c3cf8001f001c08 0x607879f0003e0038

def z173 : W := mkw 0xfbabd6a820048000 0x13f757ad50400900 0xffffffffe007e07f 0xffffffffffc00fc0

def z174 : W := mkw 0xfbabd7e8200da338 0x1bf757afd0401b46 0xfffffffc0007e3bf 0xf7fffffff8000fc7

def z175 : W := mkw 0x3d3cd22a9e500000 0x527a79a4553ca000 0x3c3cf83c1f000008 0x607879f0783e0000

def z176 : W := mkw 0x4457085738c4ed92 0x0088ae10ae7189db 0xccff18fff8c7ffff 0xbf99fe31fff18fff

def z177 : W := mkw 0x93fc46a94af00000 0x5127f88d5295e000 0x03fc07fc00f80010 0x1007f80ff801f000

def z178 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c307c3e03fe006 0x8b87860f87c07fc0

def z179 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c207c0e0ff0392 0x9b87840f81c1fe07

def z180 : W := mkw 0x4003d6a800000000 0x108007ad50000000 0x0002e70000000000 0x800005ce00000000

def z181 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xf002e003ff07fc42 0xcfe005c007fe0ff8

def z182 : W := mkw 0x00000140200da338 0x0800000280401b46 0x000000000007e380 0x0400000000000fc7

def z183 : W := mkw 0x000028002106d840 0x2000005000420db0 0x000000000007fc00 0x0400000000000ff8

def z184 : W := mkw 0x6c03feaab506d840 0x32d807fd556a0db0 0xfc03ffffff07fc6f 0xfff807fffffe0ff8

def z185 : W := mkw 0x0000200001021000 0x0000004000020420 0x000000001f071c40 0x0c000000003e0e38

def z186 : W := mkw 0x113020000b521000 0x002260400016a420 0x3332e0001fff1c7b 0xec6665c0003ffe38

def z187 : W := mkw 0x6c47b847b586f952 0x22d88f708f6b0df2 0xfccff8cfff07fc6f 0xeff99ff19ffe0ff8

def z188 : W := mkw 0xfbabf6a8a5069040 0x33f757ed514a0d20 0xfffffffce707003f 0xfbfffffff9ce0e00

def z189 : W := mkw 0xbba8422000000000 0x0377508440000000 0xfffee7300000003f 0xf3fffdce60000000

def z190 : W := mkw 0x15346b361b5b5ea6 0x042a68d66c36b6bd 0x3f3eff3c1fff1ffb 0xfc7e7dfe783ffe3f

def z191 : W := mkw 0x6c039802b404c840 0x22d8073005680990 0xfc011803ff00e04f 0x4bf8023007fe01c0

def z192 : W := mkw 0x7933f330af5f96e4 0x26f267e6615ebf2d 0xf332e730ffff1ffb 0xffe665ce61fffe3f

def z193 : W := mkw 0x3928d22800000000 0x127251a450000000 0x3cfdf8fc0000003d 0x7079fbf1f8000000

def z194 : W := mkw 0x3d3000029e500000 0x027a6000053ca000 0xff300003fff8005f 0x4bfe600007fff000

def z195 : W := mkw 0xeecf05c3f4ada338 0x4bdd9e0b87e95b46 0xcfcf07c3e0ffe3f7 0x9f9f9e0f87c1ffc7

def z196 : W := mkw 0x00002100010b1220 0x0000004200021624 0x3302e7001fff1ffb 0xfc6605ce003ffe3f

def z197 : W := mkw 0x0400000210000000 0x0008000004200000 0x0c0000031800004d 0x0018000006300000

def z198 : W := mkw 0x40030580200d8228 0x0880060b00401b04 0x0002070000070000 0x8000040e00000e00

def z199 : W := mkw 0xeec39cc3f4a4e958 0x2bdd873987e949d2 0xccc118c3e000e004 0x0399823187c001c0

def z200 : W := mkw 0x1120422000000000 0x0022408440000000 0x3ffffffc0000003f 0xf07ffffff8000000

def z201 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030003000000039 0x3000600060000000

def z202 : W := mkw 0x86d4000358e00000 0x010da80006b1c000 0xcffc0003f8f8005f 0x0b9ff80007f1f000

def z203 : W := mkw 0x400305c0200da338 0x0880060b80401b46 0xc00307c3e007e3e7 0x9f80060f87c00fc7

def z204 : W := mkw 0x4003bdc0210ffb78 0x2880077b80421ff6 0x0003ffc00007ffa0 0xb40007ff80000fff

def z205 : W := mkw 0xeac395c160ada338 0x0bd5872b82c15b46 0xffc3ffc3e0ffe3ff 0xffff87ff87c1ffc7

def z206 : W := mkw 0x4003d7e8200da338 0x188007afd0401b46 0x0003fffc0007e3a0 0xb40007fff8000fc7

def z207 : W := mkw 0xbffc0817def04c82 0x437ff8102fbde099 0xfffc183ffff81c5f 0x6bfff8307ffff038

def z208 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffc0003fff8ffdf 0x4ffff80007fff1ff

def z209 : W := mkw 0xfbbbd6a80a500000 0x13f777ad5014a000 0xfffffffc1ff8007f 0xfbfffffff83ff000

def z210 : W := mkw 0xea8bd6a800000000 0x13d517ad50000000 0xcccffffc00000024 0xb3999ffff8000000

def z211 : W := mkw 0xffabd6aa94000000 0x13ff57ad55280000 0xffffffffff00007f 0xfbfffffffffe0000

def z212 : W := mkw 0x1128422800000000 0x1022508450000000 0x003c003c00000000 0x0000780078000000

def z213 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xff03ff000000002f 0xe3fe07fe00000000

def z214 : W := mkw 0xbffc2003dff21000 0x437ff84007bfe420 0xfffee003ffff1c7f 0xeffffdc007fffe38

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000c003f1 0x1400000000018007

def z216 : W := mkw 0x2c54b8579dc27dd2 0x2258a970af3b84fb 0x3cfdf8ff1fc0fffd 0x7479fbf1fe3f81ff

def z217 : W := mkw 0x1120622001021000 0x002240c440020420 0x3332e7301f071c7b 0xfc6665ce603e0e38

def z218 : W := mkw 0xc2c3048140a00000 0x0185860902814000 0xc3c307c3e0f80077 0x9b87860f87c1f000

def z219 : W := mkw 0xd7f76ff77bffffbe 0x0dafeedfeef7ffff 0xffffffffffffffff 0xffffffffffffffff

def z220 : W := mkw 0x93f000014af00000 0x0127e0000295e000 0xf3f00003fff8005f 0x4be7e00007fff000

def z221 : W := mkw 0xaedc0003dce00000 0x435db80007b9c000 0xccfc0003f8c0005d 0x0399f80007f18000

def z222 : W := mkw 0xfffffeffbdc6fdd2 0x33fffffdff7b8dfb 0xffffffffffc7ffff 0xffffffffffff8fff

def z223 : W := mkw 0x4003b00021069040 0x2080076000420d20 0x0002e00000070000 0x800005c000000e00

def z224 : W := mkw 0xeecfb803f5a6d840 0x63dd9f7007eb4db0 0xfccff803ff07fc6f 0xeff99ff007fe0ff8

def z225 : W := mkw 0x4457b85739c6fdd2 0x2088af70ae738dfb 0x0cfff8ff18c7fffd 0xb419fff1fe318fff

def z226 : W := mkw 0x0000010000090220 0x0000000200001204 0x0300070000f80390 0x1006000e0001f007

def z227 : W := mkw 0xaa88000000000000 0x0355100000000000 0xcccc000000000004 0x0399980000000000

def z228 : W := mkw 0xbbb863300b5b16a4 0x077770c66016b62d 0xfffee7301fff1fff 0xfffffdce603ffe3f

def z229 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xf303fffc00000022 0xf3e607fff8000000

def z230 : W := mkw 0x6c13b812bd46dcc0 0x22d82770257a8db9 0xfc33f833ffc7ffff 0xfff867f067ff8fff

def z231 : W := mkw 0x82d405d548e927ba 0x0905a80baa91d24f 0x03fc07fc00f80390 0x1007f80ff801f007

def z232 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x0332e73000ff1fb0 0xb40665ce6001fe3f

def z233 : W := mkw 0xfbabf6a8a5069040 0x33f757ed514a0d20 0xf302e700e7070002 0xcbe605ce01ce0e00

def z234 : W := mkw 0x3d28fa2a95025840 0x327a51f4552a04b0 0x3c3cf83c1f001c08 0x607879f0783e0038

def z235 : W := mkw 0x0040004100802110 0x0000800082010042 0x00c000c000c00390 0x1001800180018007

def z236 : W := mkw 0x0014001408400482 0x0000280028108009 0x003c003c00000000 0x0000780078000000

def z237 : W := mkw 0x2c0c000294000000 0x4258180005280000 0x0c0c000000000000 0x0018180000000000

def z238 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7301f3f1c0a 0xe86665ce603e7e38

def z239 : W := mkw 0x04542113dffb16a4 0x4408a84227bff62d 0x00000003ffff1fc0 0x0c00000007fffe3f

def z240 : W := mkw 0xfbabfea82106d840 0x33f757fd50420db0 0xfffffffc0007fc3f 0xf7fffffff8000ff8

def z241 : W := mkw 0xc283048000000000 0x0185060900000000 0xc3c307c000000037 0x9387860f80000000

def z242 : W := mkw 0x0400080210004800 0x0008001004200090 0x0c00180018001c08 0x2018003000300038

def z243 : W := mkw 0xc283048000000000 0x0185060900000000 0xc0c100c000000004 0x0381820180000000

def z244 : W := mkw 0x04542803fff6d840 0x6008a85007ffedb0 0x00000003fffffc40 0x0c00000007fffff8

def z245 : W := mkw 0xbffc46abdef00000 0x537ff88d57bde000 0xfffc07fffff8005f 0x5bfff80ffffff000

def z246 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3ffffffc1fff1fff 0xfc7ffffff83ffe3f

def z247 : W := mkw 0xffefd6abd4a00000 0x53ffdfad57a94000 0xffffffffe000003f 0xf3ffffffffc00000

def z248 : W := mkw 0xfbffd6a94af00000 0x53f7ffad5295e000 0xfffffffc00f8003f 0xf3fffffff801f000

def z249 : W := mkw 0xffff0003fef48000 0x43fffe0007fde900 0xffff0003ffffe07f 0xcffffe0007ffffc0

def z250 : W := mkw 0xc2c3d7e960ada338 0x198587afd2c15b46 0xc3c3ffffe0ffe3f7 0xbf8787ffffc1ffc7

def z251 : W := mkw 0x0010085408406d92 0x00002010a81080db 0x003118fc18c0fff9 0x34006231f83181ff

def z252 : W := mkw 0x6c039802b404c840 0x22d8073005680990 0xfc03f803e000e02f 0xe3f807f007c001c0

def z253 : W := mkw 0x68039000a4048040 0x22d0072001480900 0xc0000000e0000000 0x0380000001c00000

def z254 : W := mkw 0xaecc0003d4a00000 0x435d980007a94000 0xcccc0003e0000004 0x0399980007c00000

def z255 : W := mkw 0x93a8000000000000 0x0127500000000000 0x03fc000000000010 0x0007f80000000000

def z256 : W := mkw 0xffffb003fff69040 0x63ffff6007ffed20 0xfffee003ffff005f 0xcbfffdc007fffe00

def z257 : W := mkw 0xbffc2113dffb16a4 0x477ff84227bff62d 0xfffc0003ffff1fdf 0x4ffff80007fffe3f

def z258 : W := mkw 0x2c00b802b506d840 0x22580170056a0db0 0x3c00f803ff07fc48 0x6c7801f007fe0ff8

def z259 : W := mkw 0xffabb802f736d840 0x63ff577005ee6db0 0xff03f803ff3ffc6f 0xeffe07f007fe7ff8

def z260 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c107c3e0f8e394 0x1387820f87c1f1c7

def z261 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xcc011803ff07fc44 0x0f98023007fe0ff8

def z262 : W := mkw 0xffabb802b506d840 0x23ff5770056a0db0 0xfffff803ff07fc7f 0xeffffff007fe0ff8

def z263 : W := mkw 0xea8b948800000000 0x13d5172910000000 0xc000000000000000 0x0380000000000000

def z264 : W := mkw 0x82c0010140a90220 0x0105800202815204 0xc3c20703e0ff03f7 0x9f87840e07c1fe07

def z265 : W := mkw 0x0000623001021484 0x040000c460020429 0x0000e03000001c00 0x200001c060000038

def z266 : W := mkw 0xd3b367b00b5b16a4 0x05a766cf6016b62d 0xf3f3e7f01fff1fff 0xffe7e7cfe03ffe3f

def z267 : W := mkw 0xbffcd22bdef00000 0x537ff9a457bde000 0xfffcf83ffff8005f 0x6bfff9f07ffff000

def z268 : W := mkw 0x0010001008400480 0x0000200020108009 0x0030003018001c08 0x2000600060300038

def z269 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e73007ff0392 0xd86665ce600ffe07

def z270 : W := mkw 0xffabdeaa10004800 0x13ff57bd54200090 0xffffffff1800fc7f 0xf7fffffffe3001f8

def z271 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfcfff8ffff07fc7f 0xfff9fff1fffe0ff8

def z272 : W := mkw 0xffff9003def00000 0x43ffff2007bde000 0xfffff803fff8007f 0xebfffff007fff000

def z273 : W := mkw 0x44032802b506d840 0x20880650056a0db0 0xc0030003ff07fc67 0x8f80060007fe0ff8

def z274 : W := mkw 0x3d7c08579ed06d92 0x427af810af3da0db 0x3cfd18ff1fc0fffd 0x7479fa31fe3f81ff

def z275 : W := mkw 0x93a8000042300000 0x4127500000846000 0x0300000000380000 0x0006000000007000

def z276 : W := mkw 0x404305c1208da338 0x0880860b82411b46 0x00c307c300c7e3f5 0x9401860f86018fc7

def z277 : W := mkw 0x1130423008400480 0x0022608460108009 0x3332e73018c01ffb 0xf46665ce6031803f

def z278 : W := mkw 0x0454285719c27d92 0x0008a850ae3384fb 0x3cfff8ff1fc7ffff 0xfc79fff1fe3f8fff

def z279 : W := mkw 0xd3f305c16afda338 0x09a7e60b82d5fb46 0xf3f307c3ffffe3ff 0xdfe7e60f87ffffc7

def z280 : W := mkw 0xbbb80000ce700000 0x43777000019ce000 0xf3300000fff8005b 0x4be6600001fff000

def z281 : W := mkw 0xc6c70dc770adeb3a 0x098d8e1b8ee15bd6 0xcfcf1fcfe0ffe3f7 0x9f9f9e3f9fc1ffc7

def z282 : W := mkw 0x11206320031b1224 0x042240c640063624 0x3302e7001f3f1c6b 0xec6605ce003e7e38

def z283 : W := mkw 0xbfa80002d6300000 0x437f500005ac6000 0xff000003ff38004f 0x4bfe000007fe7000

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x0cfc00000000001d 0x0019f80000000000

def z285 : W := mkw 0xaecc0847d4a06912 0x435d98108fa940d2 0xcccd18cfe000e004 0x03999a319fc001c0

def z286 : W := mkw 0x15746a771bd27d96 0x042ae8d4ee37a4fb 0x3cfdf8ff1fc0fffd 0x7479fbf1fe3f81ff

def z287 : W := mkw 0xd3abd6a800000000 0x11a757ad50000000 0x03fffffc00000030 0xb007fffff8000000

def z288 : W := mkw 0x6803900000000000 0x02d0072000000000 0xfcfff8fc0000003f 0xf3f9fff1f8000000

def z289 : W := mkw 0x0010001008400480 0x0000200020108009 0x0000000018c01fc0 0x040000000031803f

def z290 : W := mkw 0xc2c304c100802110 0x0185860982010042 0xc3c307c300c0e3f7 0x9787860f860181c7

def z291 : W := mkw 0xfff3fff3fffffffc 0x2fffe7ffe7ffffff 0xfff3fff3ffffffff 0xffffe7ffe7ffffff

def z292 : W := mkw 0xfbbbd7b80a5906a4 0x17f777af7014b20d 0xfffffffc00f803bf 0xf3fffffff801f007

def z293 : W := mkw 0xc2c3bdc161affb78 0x2985877b82c35ff6 0xc3c3ffc3e0fffff7 0xbf8787ff87c1ffff

def z294 : W := mkw 0xffffd7ebfefda338 0x5bffffafd7fdfb46 0xffffffffffffe3ff 0xffffffffffffffc7

def z295 : W := mkw 0x93f047f14af927bc 0x0d27e08fe295f24f 0x03f007f000f80390 0x1007e00fe001f007

def z296 : W := mkw 0x045429571bdb7fb6 0x0408a852ae37b6ff 0x000000031fffffc0 0x0c000000063fffff

def z297 : W := mkw 0xffabfeaa95025840 0x33ff57fd552a04b0 0xfffffffc1f001c3f 0xf3fffffff83e0038

def z298 : W := mkw 0xc2830580602d8228 0x0985060b00c05b04 0xc3030703e03fe067 0x8f86060e07c07fc0

def z299 : W := mkw 0xfbeb05c1e6bda338 0x4bf7d60b83cd7b46 0xf3c307c3e7ffe3f7 0xdfe7860f87cfffc7

def z300 : W := mkw 0xffffd6abdef00000 0x53ffffad57bde000 0xfffee703fff8005f 0xcbfffdce07fff000

def z301 : W := mkw 0x2808900800000000 0x1250112010000000 0x0c0c180c00000000 0x0018183018000000

def z302 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x000118ff18c0ffe0 0x34000231fe3181ff

def z303 : W := mkw 0x1120422000000000 0x0022408440000000 0x3302e70000000002 0xc06605ce00000000

def z304 : W := mkw 0x82c0004140a02110 0x0105800082814042 0xc3c100c3e0f8e3f7 0x1f87820187c1f1c7

def z305 : W := mkw 0x113000100a500480 0x002260002014a009 0x333000301ff81ffb 0x7c666000603ff03f

def z306 : W := mkw 0x0400080210004800 0x0008001004200090 0x000000031800fc40 0x04000000063001f8

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000001f00004b 0x48600000003e0000

def z308 : W := mkw 0x4003fb30210fdee4 0x248007f660421fbd 0x0003ff300007ffa0 0xb40007fe60000fff

def z309 : W := mkw 0x113042300a500484 0x042260846014a009 0x0030003000000000 0x0000600060000000

def z310 : W := mkw 0xffbfdebe18404c82 0x13ff7fbd7c308099 0xfffffffc18001c3f 0xf3fffffff8300038

def z311 : W := mkw 0x113000000a500000 0x002260000014a000 0x303000001f000008 0x40606000003e0000

def z312 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc0c307c3e007e3a4 0x9781860f87c00fc7

def z313 : W := mkw 0x0454000318c00000 0x0008a80006318000 0x0cfc000318c0005d 0x0019f80006318000

def z314 : W := mkw 0x0040014140a92338 0x0800800282815246 0x0000000000f80380 0x000000000001f007

def z315 : W := mkw 0xffff9803fef4c840 0x63ffff3007fde990 0xfffd1803fff8e05f 0x4bfffa3007fff1c0

def z316 : W := mkw 0xeacb95c960ada338 0x1bd5972b92c15b46 0xcfcf1fcfe0ffe3f7 0x9f9f9e3f9fc1ffc7

def z317 : W := mkw 0xbba86320c73b1224 0x477750c6418e7624 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z318 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfcfc0003ff00000c 0x43f9f80007fe0000

def z319 : W := mkw 0xd3f347f16afda7bc 0x0da7e68fe2d5fb4f 0xc3f307f3e0ffe3f7 0x9f87e60fe7c1ffc7

def z320 : W := mkw 0x513367f02b5fb7bc 0x0ca266cfe056bf6f 0x3333e7f01ffffffb 0xfc6667cfe03fffff

def z321 : W := mkw 0x0444000310800000 0x0008880006210000 0x0ccc000300000004 0x0019980006000000

def z322 : W := mkw 0x1120000002100000 0x0022400000042000 0x3300000007380002 0x48660000000e7000

def z323 : W := mkw 0xc2c304c160a4a118 0x0985860982c14942 0xc3c307c3e000e037 0x9387860f87c001c0

def z324 : W := mkw 0x04000802b404c840 0x2008001005680990 0x00000003e000e000 0x0000000007c001c0

def z325 : W := mkw 0xeec3b803f5a6d840 0x23dd877007eb4db0 0xffc3f803fffffc7f 0xefff87f007fffff8

def z326 : W := mkw 0x400398002004c840 0x2080073000400990 0x000118000000e000 0x00000230000001c0

def z327 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xcc03f803e007fc24 0xa79807f007c00ff8

def z328 : W := mkw 0x0400000294000000 0x0008000005280000 0x00000003ff000040 0x0800000007fe0000

def z329 : W := mkw 0x5133fb302b5fdee4 0x24a267f66056bfbd 0x3333ff301ffffffb 0xfc6667fe603fffff

def z330 : W := mkw 0x0054005508c02592 0x0000a800aa11804b 0x00fd00ff00c0e3f5 0x1401fa01fe0181c7

def z331 : W := mkw 0x2c540003def00000 0x4258a80007bde000 0xfc000003fff8004f 0x4bf8000007fff000

def z332 : W := mkw 0xbffc2803fff6d840 0x637ff85007ffedb0 0xfffc0003fffffc5f 0x4ffff80007fffff8

def z333 : W := mkw 0x113062300b521484 0x042260c46016a429 0x3332e7301f001c3b 0xf06665ce603e0038

def z334 : W := mkw 0xffefdeef10806912 0x13ffdfbdde2100d2 0xffffffff0000e03f 0xf3fffffffe0001c0

def z335 : W := mkw 0xbffc0043def02110 0x437ff80087bde042 0xfffd00c3fff8e3ff 0x5ffffa0187fff1c7

def z336 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xfffc0000e738001f 0x4bfff80001ce7000

def z337 : W := mkw 0x0440084310806910 0x00088010862100d2 0x0cc118c318c0fffd 0x34198231863181ff

def z338 : W := mkw 0x2c14b8169d425cc2 0x225829702d3a84b9 0x3c3cf83c1f001c08 0x607879f0783e0038

def z339 : W := mkw 0xc2c30dd560adefba 0x0985861baac15bdf 0xc3c31fffe0fffff7 0xbf87863fffc1ffff

def z340 : W := mkw 0x440308023004c800 0x0088061004600990 0xcc031803f807fc6f 0xaf98063007f00ff8

def z341 : W := mkw 0x4003000020048000 0x0080060000400900 0xc0010003e000e004 0x0380020007c001c0

def z342 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3020703e0ffe3c2 0x8f86040e07c1ffc7

def z343 : W := mkw 0x0054005508c02592 0x0000a800aa11804b 0x0000000000c00380 0x0000000000018007

def z344 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff00c0e394 0x1019fa31fe0181c7

def z345 : W := mkw 0xbba8d22800000000 0x137751a450000000 0xfffcf83c0000001f 0x63fff9f078000000

def z346 : W := mkw 0x0000200001021000 0x0000004000020420 0x3002e00007070002 0xc86005c0000e0e00

def z347 : W := mkw 0xaedc0857dce06d92 0x435db810afb9c0db 0xccfd18fff8c0fffd 0x3799fa31fff181ff

def z348 : W := mkw 0xee8b9c8ab404c840 0x33dd173915680990 0xcccd18cfe000e004 0x03999a319fc001c0

def z349 : W := mkw 0x0000000020048000 0x0000000000400900 0x00000003e007e040 0x0c00000007c00fc0

def z350 : W := mkw 0xbba8000000000000 0x0377500000000000 0xf300000000000002 0x43e6000000000000

def z351 : W := mkw 0x0400280295025840 0x20080050052a04b0 0x000000001f001c00 0x00000000003e0038

def z352 : W := mkw 0xbffc0143fefda338 0x4b7ff80287fdfb46 0xfffc0003ffffe3df 0x4ffff80007ffffc7

def z353 : W := mkw 0x0444084710806912 0x000888108e2100d2 0x000000030000e000 0x00000000060001c0

def z354 : W := mkw 0x2c00980294004840 0x2258013005280090 0x0c00180000000000 0x0018003000000000

def z355 : W := mkw 0xfbab948800000000 0x13f7572910000000 0xfffd18cc0000001f 0x43fffa3198000000

def z356 : W := mkw 0x00006330010b16a4 0x040000c66002162d 0x0302e73000ff1ff3 0xbc0605ce6001fe3f

def z357 : W := mkw 0x00100110084906a0 0x000020022010920d 0x0332073018ff1ffb 0xbc06640e6031fe3f

def z358 : W := mkw 0xfffffeabfff6d840 0x73fffffd57ffedb0 0xfffffffffffffc7f 0xfffffffffffffff8

def z359 : W := mkw 0xaec00003d4a00000 0x035d800007a94000 0xffc00003fff8005f 0x4bff800007fff000

def z360 : W := mkw 0x117443750ad927b6 0x0422e886ea15b24f 0x03fc07fc00f80390 0x1007f80ff801f007

def z361 : W := mkw 0x6c57b857bdc6fdd2 0x22d8af70af7b8dfb 0xfc03f803ffc7ffef 0xeff807f007ff8fff

def z362 : W := mkw 0xeecf9ccf10806912 0x13dd9f399e2100d2 0xcccd18cf0000e004 0x03999a319e0001c0

def z363 : W := mkw 0x0454095718c96fb2 0x0008a812ae3192df 0x0fff1fff18ffffff 0xbc1ffe3ffe31ffff

def z364 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0ccd18cf18c0ffc4 0x04199a319e3181ff

def z365 : W := mkw 0x6803b8002106d840 0x22d0077000420db0 0xfc03f8000007fc2f 0xe7f807f000000ff8

def z366 : W := mkw 0xbfbc0002de700000 0x437f780005bce000 0xff3c0000ff38000a 0x4bfe780001fe7000

def z367 : W := mkw 0x2c00000294000000 0x0258000005280000 0xcc000003e0000004 0x0398000007c00000

def z368 : W := mkw 0x93a846a800000000 0x1127508d50000000 0x33fee7fc0000003b 0xf067fdcff8000000

def z369 : W := mkw 0x0054085508c06d92 0x0000a810aa1180db 0x00fd18fc00c0ffb0 0x3401fa31f80181ff

def z370 : W := mkw 0xfffffb33ffffdee4 0x67fffff667ffffbd 0xffffff33ffffffff 0xfffffffe67ffffff

def z371 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x033007301fff1fd0 0x1c06600e603ffe3f

def z372 : W := mkw 0xfbabf6a801021000 0x13f757ed50020420 0xfffffffc1f071c7f 0xfffffffff83e0e38

def z373 : W := mkw 0xea83b580e52f9268 0x2bd5076b01ca5f24 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z374 : W := mkw 0x2c00b80295025840 0x22580170052a04b0 0xfc00f803ff001c4f 0x6bf801f007fe0038

def z375 : W := mkw 0x4457deff18c06d92 0x1088afbdfe3180db 0x0cffffff18c0fffd 0xb419fffffe3181ff

def z376 : W := mkw 0x00006b74010b7fb6 0x040000d6e80216ff 0x0003fffc0007ffa0 0xb40007fff8000fff

def z377 : W := mkw 0x2c00b80295025840 0x22580170052a04b0 0x3c01f8031f00fc6d 0x647803f0063e01f8

def z378 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xf3000003fff80042 0x4be6000007fff000

def z379 : W := mkw 0x3d3c08169e504c82 0x427a78102d3ca099 0x3c3c183c1f001c08 0x60787830783e0038

def z380 : W := mkw 0xbffc0803def04800 0x437ff81007bde090 0xfffd1803fff8fc7f 0x6ffffa3007fff1f8

def z381 : W := mkw 0xfbabdefc00006d92 0x13f757bdf80000db 0xfffffffc0000ffbf 0xf7fffffff80001ff

def z382 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xcffc0003e0f80014 0x039ff80007c1f000

def z383 : W := mkw 0xc6c32dc3f5affb78 0x298d865b87eb5ff6 0xc3c307c3fffffff7 0x9f87860f87ffffff

def z384 : W := mkw 0x15346a361b525c86 0x042a68d46c36a4b9 0x3c3cf83c1f001c08 0x607879f0783e0038

def z385 : W := mkw 0x4403b8023106d840 0x2088077004620db0 0x0c03f8031807fc6d 0xa41807f006300ff8

def z386 : W := mkw 0xffbbffbabf5fdee4 0x37ff77ff757ebfbd 0xffffffffffffffff 0xffffffffffffffff

def z387 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0x03c307c000ffe3b0 0x9407860f8001ffc7

def z388 : W := mkw 0x4003048000000000 0x0080060900000000 0x000307c000000020 0x9000060f80000000

def z389 : W := mkw 0x00002110010b16a4 0x040000422002162d 0x0000000000071f80 0x0400000000000e3f

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z391 : W := mkw 0xd3a346a000000000 0x01a7468d40000000 0xf3f3e7f00000003f 0xf3e7e7cfe0000000

def z392 : W := mkw 0xfbabf7a8031b1224 0x17f757ef50063624 0xfffffffc073f003f 0xfbfffffff80e7e00

def z393 : W := mkw 0x82cc000140a00000 0x4105980002814000 0x00cc000000000000 0x0001980000000000

def z394 : W := mkw 0x93fc63314bfb16a4 0x4527f8c66297f62d 0x33fee7301fff1ffb 0xfc67fdce603ffe3f

def z395 : W := mkw 0x00002000a5069040 0x20000040014a0d20 0x00000000e7070000 0x0800000001ce0e00

def z396 : W := mkw 0x44570dd738cdefba 0x0888ae1bae719bdf 0x0cff1fff18c7fffd 0xb419fe3ffe318fff

def z397 : W := mkw 0x6c03900294000000 0x02d8072005280000 0xfc03f803ff00006f 0xebf807f007fe0000

def z398 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0c3c183f18c0ffc8 0x241878307e3181ff

def z399 : W := mkw 0x7d23fb22b71fda64 0x26fa47f6456e3fb4 0xff03ff03ff3ffc6f 0xeffe07fe07fe7ff8

def z400 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc01f803ff00fc0c 0x63f803f007fe01f8

def z401 : W := mkw 0x2800000000000000 0x0250000000000000 0xfc0000000000000f 0x43f8000000000000

def z402 : W := mkw 0x8288048800000000 0x1105100910000000 0x00cc00cc00000000 0x0001980198000000

def z403 : W := mkw 0x93b867b80b5b16a4 0x152770cf7016b62d 0x33fee7fc1fff1ffb 0xfc67fdcff83ffe3f

def z404 : W := mkw 0x04540143fefda338 0x4808a80287fdfb46 0x00000003ffffe3c0 0x0c00000007ffffc7

def z405 : W := mkw 0x0010001008400480 0x0000200020108009 0x0cfd18fc18c01ffd 0x3419fa31f831803f

def z406 : W := mkw 0x93fc46fd08c02592 0x1127f88dfa11804b 0x03fc07fc00c00390 0x1007f80ff8018007

def z407 : W := mkw 0xc6d705c3fefda338 0x498dae0b87fdfb46 0xc3c307c3ffffe3f7 0x9f87860f87ffffc7

def z408 : W := mkw 0x0404080610004802 0x000808100c200090 0x0c0c180c00000000 0x0018183018000000

def z409 : W := mkw 0x0044004500802112 0x000088008a010042 0x00cc00cc00000000 0x0001980198000000

def z410 : W := mkw 0x40030dd4200defba 0x0880061ba8401bdf 0x00031ffc0007ffa0 0xb400063ff8000fff

def z411 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfcfdf8fc0000000c 0x63f9fbf1f8000000

def z412 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0c01180318c0ffed 0x24180230063181ff

def z413 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000018001c69 0x2400000000300038

def z414 : W := mkw 0x0400080210004800 0x0008001004200090 0x0cfd18ff1800fc7d 0x3419fa31fe3001f8

def z415 : W := mkw 0xffabfeaab506d840 0x33ff57fd556a0db0 0xff03ff03ff07fc6f 0xeffe07fe07fe0ff8

def z416 : W := mkw 0x3928d22800000000 0x127251a450000000 0x3f3eff3c0000003b 0xf07e7dfe78000000

def z417 : W := mkw 0x001021100b5b16a4 0x040020422016b62d 0x3002e0001fff1feb 0xec6005c0003ffe3f

def z418 : W := mkw 0x15740003def00000 0x402ae80007bde000 0x33300003fff8005b 0x4866600007fff000

def z419 : W := mkw 0x15746333dffb16a4 0x442ae8c667bff62d 0x3332e733ffff1ffb 0xfc6665ce67fffe3f

def z420 : W := mkw 0xea8b948800000000 0x13d5172910000000 0xccfd18fc0000003d 0x3399fa31f8000000

def z421 : W := mkw 0x001000000a500000 0x000020000014a000 0x000000001ff80040 0x08000000003ff000

def z422 : W := mkw 0x3d3c00029e500000 0x427a7800053ca000 0x3f3c00001ff8005b 0x487e7800003ff000

def z423 : W := mkw 0xc2d325d16bffb7bc 0x0d85a64ba2d7ff6f 0xc3c307c3fffffff7 0x9f87860f87ffffff

def z424 : W := mkw 0x3d3c63329f5b16a4 0x467a78c6653eb62d 0x3f3ee7301fff1ffb 0xfc7e7dce603ffe3f

def z425 : W := mkw 0xc2c3058160ad8228 0x0985860b02c15b04 0xc3c20703e0ff0057 0x8b87840e07c1fe00

def z426 : W := mkw 0xfbabf7b8010b16a4 0x17f757ef7002162d 0xfffffffc00071fbf 0xf7fffffff8000e3f

def z427 : W := mkw 0x4003200021069000 0x0080064000420d20 0xf003e003ff07fc6f 0xefe007c007fe0ff8

def z428 : W := mkw 0x005021516bffb7bc 0x0c00a042a2d7ff6f 0x00000003ffffffc0 0x0c00000007ffffff

def z429 : W := mkw 0x6c57985718c06d92 0x02d8af30ae3180db 0xfcfff8ff18c0ffff 0xf7f9fff1fe3181ff

def z430 : W := mkw 0x93fc05c14af92338 0x4927f80b8295f246 0x03fc07c000f80390 0x1007f80f8001f007

def z431 : W := mkw 0xbffcb803dff25840 0x637ff97007bfe4b0 0xfffcf803fff81c5f 0x6bfff9f007fff038

def z432 : W := mkw 0x11206330010b16a4 0x042240c66002162d 0x3332e73000071fbb 0xf46665ce60000e3f

def z433 : W := mkw 0x4003b8542106fdd2 0x20800770a8420dfb 0x0003f8fc0007ffa0 0xb40007f1f8000fff

def z434 : W := mkw 0xd3a367a0633f922c 0x0da746cf40c67f24 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z435 : W := mkw 0x6c03bdc2b50ffb78 0x2ad8077b856a1ff6 0xfc03ffc3ff07ffef 0xfff807ff87fe0fff

def z436 : W := mkw 0xfbab048000000000 0x03f7560900000000 0xffff07c00000003f 0xd3fffe0f80000000

def z437 : W := mkw 0xc283058000090220 0x0185060b00001204 0xc3c307c000ff03f7 0x9f87860f8001fe07

def z438 : W := mkw 0xbffc05c3def92338 0x4b7ff80b87bdf246 0xfffc07c3fff803df 0x5bfff80f87fff007

def z439 : W := mkw 0x0000d22800000000 0x100001a450000000 0x0000f83c00000000 0x200001f078000000

def z440 : W := mkw 0x4003b8002106d840 0x2080077000420db0 0xc003f803e007fc67 0xaf8007f007c00ff8

def z441 : W := mkw 0x117063710bdb37b4 0x0422e0c6e217b66f 0x33f3e7f31fffffff 0xfc67e7cfe63fffff

def z442 : W := mkw 0xbffc4223def00000 0x437ff88447bde000 0xfffee733fff8007f 0xfbfffdce67fff000

def z443 : W := mkw 0x04542857bdc6fdd2 0x2008a850af7b8dfb 0x0cfd18ffffc7fffd 0x3c19fa31ffff8fff

def z444 : W := mkw 0xfbfbf7f96bffb7bc 0x1ff7f7eff2d7ff6f 0xffffffffffffffff 0xffffffffffffffff

def z445 : W := mkw 0xc283d6a800000000 0x118507ad50000000 0xc3c3fffc00000037 0xb38787fff8000000

def z446 : W := mkw 0x00006320010b1224 0x040000c640021624 0x0002e70000070000 0x800005ce00000e00

def z447 : W := mkw 0x82c005c140a92338 0x0905800b82815246 0x03c107c300f8e3f5 0x1407820f8601f1c7

def z448 : W := mkw 0x0054005508c02592 0x0000a800aa11804b 0x0cfd18fc00c003bd 0x3019fa31f8018007

def z449 : W := mkw 0x1120622003121004 0x042240c440062420 0x3000e00007000000 0x406001c0000e0000

def z450 : W := mkw 0x0000200001021000 0x0000004000020420 0x0002e00000071c20 0xa40005c000000e38

def z451 : W := mkw 0x82c005c160ada338 0x0905800b82c15b46 0x03c007c3e0ffe3d0 0x1c07800f87c1ffc7

def z452 : W := mkw 0xbbfc0001cef00000 0x4377f800039de000 0xf3fc0000e7f80012 0x4be7f80001cff000

def z453 : W := mkw 0x0040000140a00000 0x0000800002814000 0x00000003e0f80040 0x0800000007c1f000

def z454 : W := mkw 0x3928d22800000000 0x127251a450000000 0x3000e00000000000 0x406001c000000000

def z455 : W := mkw 0xee83bd82f52fda68 0x2bdd077b05ea5fb4 0xff03ff03ff3ffc6f 0xeffe07fe07fe7ff8

def z456 : W := mkw 0x400305c0200da338 0x0880060b80401b46 0x030307c000ffe3f3 0x9c06060f8001ffc7

def z457 : W := mkw 0x792bd6a800000000 0x12f257ad50000000 0x3c3ffffc00000028 0xf0787ffff8000000

def z458 : W := mkw 0x0444084710806912 0x000888108e2100d2 0x0cfd18ff0000e03d 0x3019fa31fe0001c0

def z459 : W := mkw 0x00006330010b16a4 0x040000c66002162d 0x3002e7301f071feb 0xfc6005ce603e0e3f

def z460 : W := mkw 0xc2830580602d8228 0x0985060b00c05b04 0xc3c307c0e03f0037 0x9b87860f81c07e00

def z461 : W := mkw 0x04002802b506d840 0x20080050056a0db0 0x0c011803ff07fc6d 0x2c18023007fe0ff8

def z462 : W := mkw 0xffff948bdef00000 0x53ffff2917bde000 0xfffd18cffff8005f 0x4bfffa319ffff000

def z463 : W := mkw 0xeecf04c3f4a4a118 0x4bdd9e0987e94942 0xcccd00c3e000e004 0x03999a0187c001c0

def z464 : W := mkw 0x3938f3380b5b16a4 0x167271e67016b62d 0x3f3eff3c1fff1ffb 0xfc7e7dfe783ffe3f

def z465 : W := mkw 0x157408571ad06d92 0x002ae810ae35a0db 0x3ffd18ff1ff8ffff 0x7c7ffa31fe3ff1ff

def z466 : W := mkw 0x6c03b902b50fda60 0x22d80772056a1fb4 0xff03ff03ffffffff 0xfffe07fe07ffffff

def z467 : W := mkw 0xd3ab46a800000000 0x11a7568d50000000 0xc3ff07fc00000037 0x9387fe0ff8000000

def z468 : W := mkw 0x11206320031b1224 0x042240c640063624 0x3302e70007ff03f3 0xdc6605ce000ffe07

def z469 : W := mkw 0x82c0000140a00000 0x0105800002814000 0xc0c00003e0000004 0x0381800007c00000

def z470 : W := mkw 0x5123d6a800000000 0x10a247ad50000000 0x3333fffc0000003b 0xf06667fff8000000

def z471 : W := mkw 0x0444084710806912 0x000888108e2100d2 0x0ccd18cf00c0e3f5 0x14199a319e0181c7

def z472 : W := mkw 0x93f063314bfb16a4 0x0527e0c66297f62d 0xf3f2e733ffff1fff 0xffe7e5ce67fffe3f

def z473 : W := mkw 0x2c5400039cc00000 0x0258a80007398000 0xfcfc0003ffc0005f 0x4bf9f80007ff8000

def z474 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffee7000000001f 0xc3fffdce00000000

def z475 : W := mkw 0xbffc4333def906a4 0x477ff88667bdf20d 0xfffc0733fff803df 0x5bfff80e67fff007

def z476 : W := mkw 0x0040085500806d92 0x00008010aa0100db 0x00c118ff00c0fff5 0x34018231fe0181ff

def z477 : W := mkw 0x3928000000000000 0x0272500000000000 0x3c3c000000000008 0x4078780000000000

def z478 : W := mkw 0x0444084710806912 0x000888108e2100d2 0x0ccd18cf1800fc6d 0x24199a319e3001f8

def z479 : W := mkw 0xeec305c3f4ada338 0x0bdd860b87e95b46 0xffc307c3ffffe3ff 0xdfff860f87ffffc7

def z480 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xcfff1fffe0ffe3ff 0xbf9ffe3fffc1ffc7

def z481 : W := mkw 0x04540003def00000 0x4008a80007bde000 0x0cfc0003fff8005d 0x0819f80007fff000

def z482 : W := mkw 0x6803b00001021000 0x02d0076000020420 0xfc03f8001f071c6f 0xeff807f0003e0e38

def z483 : W := mkw 0xfbabd6a8c6300000 0x53f757ad518c6000 0xf302e700e7380002 0xcbe605ce01ce7000

def z484 : W := mkw 0xc6c30dc370adeb38 0x098d861b86e15bd6 0xcfc31fc3f8ffffff 0xbf9f863f87f1ffff

def z485 : W := mkw 0x6c43b843b586f950 0x22d88770876b0df2 0xfcc3f8c3ffc7ffff 0xfff987f187ff8fff

def z486 : W := mkw 0x86d40dd758e96fba 0x090da81baeb1d2df 0x0ffd1fff18f8fffd 0x341ffa3ffe31f1ff

def z487 : W := mkw 0x93fc00554af02592 0x4127f800aa95e04b 0x03fc00fc00f80390 0x1007f801f801f007

def z488 : W := mkw 0x86d4085758e06d92 0x010da810aeb1c0db 0xcffd18fff8f8ffff 0x3f9ffa31fff1f1ff

def z489 : W := mkw 0x0414081618404c82 0x000828102c308099 0x0c3d183f1800fc6d 0x24187a307e3001f8

def z490 : W := mkw 0x6c03b856b506fdd2 0x22d80770ad6a0dfb 0xfc03f8ffff07ffef 0xfff807f1fffe0fff

def z491 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc0c100c3e0ffe3c4 0x0f81820187c1ffc7

def z492 : W := mkw 0x4003900000000000 0x0080072000000000 0x0003f80000000020 0xa00007f000000000

def z493 : W := mkw 0x97fc0003def00000 0x412ff80007bde000 0x03fc0003fff80050 0x0807f80007fff000

def z494 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3302e7001fff1fc2 0xcc6605ce003ffe3f

def z495 : W := mkw 0x513363302b5f96a4 0x04a266c66056bf2d 0xf333e733ffffffff 0xffe667ce67ffffff

def z496 : W := mkw 0xbba8000000000000 0x0377500000000000 0xfffc00000000001f 0x43fff80000000000

def z497 : W := mkw 0x82c005c140a92338 0x0905800b82815246 0x03c207c000ff03f3 0x9c07840f8001fe07

def z498 : W := mkw 0xfbebd6a940a00000 0x13f7d7ad52814000 0xffffffffe0f8007f 0xfbffffffffc1f000

def z499 : W := mkw 0x0010000008400000 0x0000200000108000 0x0030000018c00059 0x0000600000318000

def z500 : W := mkw 0x0414085618406d92 0x00082810ac3080db 0x0c3d18fc1800ffa8 0x34187a31f83001ff

def z501 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff1800fc0c 0x2019fa31fe3001f8

def z502 : W := mkw 0x113021100b5b16a4 0x042260422016b62d 0x333000001fff1fdb 0x4c666000003ffe3f

def z503 : W := mkw 0x00002100031b1224 0x0400004200063624 0x00000000073f0000 0x08000000000e7e00

def z504 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x00fc00ff18c0ffd0 0x1401f801fe3181ff

def z505 : W := mkw 0x4043014160ada338 0x0880860282c15b46 0xc0030003e0ffe3e7 0x8f80060007c1ffc7

def z506 : W := mkw 0x041400029e500000 0x40082800053ca000 0x000000001f000000 0x00000000003e0000

def z507 : W := mkw 0xc28305c0200da338 0x0985060b80401b46 0xc3c307c00007e3b7 0x9787860f80000fc7

def z508 : W := mkw 0x04542857bdc6fdd2 0x2008a850af7b8dfb 0x00000003ffc7ffc0 0x0c00000007ff8fff

def z509 : W := mkw 0x3d30fb329f5b5ee4 0x267a61f6653eb6bd 0x3f32ff301fff1ffb 0xfc7e65fe603ffe3f

def z510 : W := mkw 0x8280000040200000 0x0105000000804000 0xc3000000e0380002 0x0b86000001c07000

def z511 : W := mkw 0xfffff7bbdffb16a4 0x57ffffef77bff62d 0xffffffffffff1fff 0xfffffffffffffe3f

def z512 : W := mkw 0xc6d70cd718c06d92 0x018dae19ae3180db 0xcfff1fff18c0ffff 0xb79ffe3ffe3181ff

def z513 : W := mkw 0x4003948800000000 0x1080072910000000 0x000118cc00000000 0x0000023198000000

def z514 : W := mkw 0xd3e347e160ada338 0x09a7c68fc2c15b46 0xf3f3e7f3e0ffe3ff 0xffe7e7cfe7c1ffc7

def z515 : W := mkw 0x4003f7b8010b16a4 0x148007ef7002162d 0x0003fffc00071fa0 0xb40007fff8000e3f

def z516 : W := mkw 0x7d2bfa2ab506d840 0x32fa57f4556a0db0 0xfc3ff83fff07fc6f 0xeff87ff07ffe0ff8

def z517 : W := mkw 0x3d3063329f5b16a4 0x067a60c6653eb62d 0xff32e733ffff1fff 0xfffe65ce67fffe3f

def z518 : W := mkw 0xc283048000000000 0x0185060900000000 0xcfff1ffc0000003f 0xb39ffe3ff8000000

def z519 : W := mkw 0xc6c70cc770a4e91a 0x098d8e198ee149d2 0xcccd18cfe000e004 0x03999a319fc001c0

def z520 : W := mkw 0xc6d70dd778edefba 0x098dae1baef1dbdf 0xc3c307c3f8fffff7 0x9f87860f87f1ffff

def z521 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3030e0301fff1fc8 0x6c6061c0603ffe3f

def z522 : W := mkw 0xffff0483def00000 0x43fffe0907bde000 0xffff07c3fff8007f 0xdbfffe0f87fff000

def z523 : W := mkw 0x0454001318c00480 0x0008a80026318009 0x0cfc003318c01ffd 0x3419f8006631803f

def z524 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x00c100c318c0fff5 0x14018201863181ff

def z525 : W := mkw 0xaa880000c4200000 0x4355100001884000 0xc0000000e0000000 0x0380000001c00000

def z526 : W := mkw 0x0454000318c00000 0x0008a80006318000 0x0000000318c00040 0x0000000006318000

def z527 : W := mkw 0x11306b740b5b7fb6 0x042260d6e816b6ff 0x3333fffc1ffffffb 0xfc6667fff83fffff

def z528 : W := mkw 0x0000b80001025840 0x20000170000204b0 0x0000f80000001c00 0x200001f000000038

def z529 : W := mkw 0x2c002802b506d840 0x22580050056a0db0 0xfc000003ff07fc4f 0x4ff8000007fe0ff8

def z530 : W := mkw 0xc28305c0602da338 0x0985060b80c05b46 0xc30307c0e03fe3a2 0x9f86060f81c07fc7

def z531 : W := mkw 0x0000085400006d92 0x00000010a80000db 0x0cfd18fc0000ffbd 0x3419fa31f80001ff

def z532 : W := mkw 0x0000005400002592 0x00000000a800004b 0x000000fc00000380 0x10000001f8000007

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x3002e0000000002b 0xe06005c000000000

def z534 : W := mkw 0xbffc0103def90220 0x437ff80207bdf204 0xfffe0703ffff03ff 0xdffffc0e07fffe07

def z535 : W := mkw 0x4003defc00006d92 0x108007bdf80000db 0x0003fffc0000ffa0 0xb40007fff80001ff

def z536 : W := mkw 0xbfa8000294000000 0x037f500005280000 0xfffc0003ff00005f 0x4bfff80007fe0000

def z537 : W := mkw 0x6803900020048000 0x02d0072000400900 0xfc03f803e007e06f 0xeff807f007c00fc0

def z538 : W := mkw 0x6803b000a5069040 0x22d00760014a0d20 0xfc03f800e707002f 0xebf807f001ce0e00

def z539 : W := mkw 0x0040004160a4a118 0x0800800082c14942 0x00000003e000e000 0x0000000007c001c0

def z540 : W := mkw 0xeedf9cdf18c06d92 0x13ddbf39be3180db 0xccfd18ff18c0fffd 0x3799fa31fe3181ff

def z541 : W := mkw 0xeacb94c960a4a118 0x1bd5972992c14942 0xcccd18cfe000e004 0x03999a319fc001c0

def z542 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xcffd1ffc00000014 0x139ffa3ff8000000

def z543 : W := mkw 0x6c030002b4048000 0x02d8060005680900 0xfc030003ff07e06f 0xcff8060007fe0fc0

def z544 : W := mkw 0x3d7c00039ed00000 0x427af800073da000 0x3cfc00031fc0005d 0x4079f800063f8000

def z545 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0x3c03f8001f07fc28 0xe47807f0003e0ff8

def z546 : W := mkw 0x113042200a500000 0x002260844014a000 0x3332e7301ff8007b 0xf86665ce603ff000

def z547 : W := mkw 0x3d7c0003def00000 0x427af80007bde000 0x3c3c0003fff80048 0x4878780007fff000

def z548 : W := mkw 0xc2d705d568eda7ba 0x0985ae0baad1db4f 0xc3ff07ffe0ffe3f7 0x9f87fe0fffc1ffc7

def z549 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0030003318c0fff9 0x34006000663181ff

def z550 : W := mkw 0x6c039802b404c840 0x22d8073005680990 0xcc011803f800fc6d 0x2798023007f001f8

def z551 : W := mkw 0x404300412084a110 0x0080860082410942 0xc0c300c3e0c7e3f7 0x9f81860187c18fc7

def z552 : W := mkw 0xfbbbf7b80b5b16a4 0x17f777ef7016b62d 0xf332e7301fff1ffb 0xffe665ce603ffe3f

def z553 : W := mkw 0xfbab900000000000 0x03f7572000000000 0xfffff8000000003f 0xe3fffff000000000

def z554 : W := mkw 0x0000081400004c82 0x0000001028000099 0x0000183c00001c00 0x2000003078000038

def z555 : W := mkw 0xbfec0003d4a00000 0x437fd80007a94000 0xfffc0003e000001f 0x43fff80007c00000

def z556 : W := mkw 0x0400280211025800 0x00080050042204b0 0x3c03f8031f07fc6f 0xec7807f0063e0ff8

def z557 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3032e7301f071fa8 0xf46065ce603e0e3f

def z558 : W := mkw 0x001063300b5b16a4 0x040020c66016b62d 0x0002e7301fff1fe0 0xbc0005ce603ffe3f

def z559 : W := mkw 0x15306b321b5b5ea4 0x042a60d66436b6bd 0x3f33ff331fffffff 0xfc7e67fe663fffff

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x000100030000e065 0x04000200060001c0

def z561 : W := mkw 0xc283048020048000 0x0185060900400900 0xc3c307c3e007e077 0x9f87860f87c00fc0

def z562 : W := mkw 0xffffffff1bdb7fb6 0x17fffffffe37b6ff 0xffffffff1fffffff 0xfffffffffe3fffff

def z563 : W := mkw 0x93a846a800000000 0x1127508d50000000 0x0ffd1ffc0000003d 0x301ffa3ff8000000

def z564 : W := mkw 0xfbebd7e960ada338 0x1bf7d7afd2c15b46 0xf3c3e7c3e0ffe3f7 0xdfe787cf87c1ffc7

def z565 : W := mkw 0xffff04c3fef4a118 0x4bfffe0987fde942 0xfffd00c3fff8e05f 0x4bfffa0187fff1c0

def z566 : W := mkw 0x8280048000000000 0x0105000900000000 0x03c007c000000010 0x1007800f80000000

def z567 : W := mkw 0xbffc085718c06d92 0x037ff810ae3180db 0xfffd18ff18c0ffff 0x77fffa31fe3181ff

def z568 : W := mkw 0x0040004100802110 0x0000800082010042 0x0cfd18ff00c0e3fd 0x3419fa31fe0181c7

def z569 : W := mkw 0xbfbc00029e500000 0x437f7800053ca000 0xfffc00001f00001f 0x43fff800003e0000

def z570 : W := mkw 0x11206330031b16a4 0x042240c66006362d 0x3302e730073f1fa2 0xfc6605ce600e7e3f

def z571 : W := mkw 0x93fc00014af00000 0x4127f8000295e000 0xc3fc0003e0f80057 0x0b87f80007c1f000

def z572 : W := mkw 0xc283048060248008 0x0985060900c04900 0xc0000000e0000000 0x0380000001c00000

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x000118fc00000020 0x30000231f8000000

def z574 : W := mkw 0xfbabf7a8031b1224 0x17f757ef50063624 0xf302e700073f0002 0xcbe605ce000e7e00

def z575 : W := mkw 0x0400080210004800 0x0008001004200090 0x0c0118030000e004 0x00180230060001c0

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002000000070063 0x8c00040000000e00

def z577 : W := mkw 0x404305c160ada338 0x0880860b82c15b46 0x000307c3e0ffe3e0 0x9c00060f87c1ffc7

def z578 : W := mkw 0x0040004100802110 0x0000800082010042 0x00c100c30000e004 0x00018201860001c0

def z579 : W := mkw 0x113062300b521484 0x042260c46016a429 0x3030e0301fc01ff9 0x746061c0603f803f

def z580 : W := mkw 0x001001100a5906a4 0x040020022014b20d 0x0000000000f80380 0x000000000001f007

def z581 : W := mkw 0xffffbdc3fffffb78 0x6bffff7b87fffff6 0xffffffc3ffffffff 0xffffffff87ffffff

def z582 : W := mkw 0x0454005718c02592 0x0008a800ae31804b 0x0cfc00ff18c003dd 0x1019f801fe318007

def z583 : W := mkw 0x0054000108c00000 0x0000a80002118000 0x00fc000000c00010 0x0001f80000018000

def z584 : W := mkw 0x2c00000294000000 0x0258000005280000 0x3c0000001f000008 0x40780000003e0000

def z585 : W := mkw 0x7d77fb77bfdffff6 0x26faeff6ef7fbfff 0xffffffffffffffff 0xffffffffffffffff

def z586 : W := mkw 0x6c479847b484e952 0x22d88f308f6909d2 0xcccd18cfe000e004 0x03999a319fc001c0

def z587 : W := mkw 0x000046a800000000 0x1000008d50000000 0x000007fc00000000 0x1000000ff8000000

def z588 : W := mkw 0xffffb857fff6fdd2 0x63ffff70afffedfb 0xfffff8ffffffffff 0xfffffff1ffffffff

def z589 : W := mkw 0xeec39dc3f4adeb78 0x2bdd873b87e95bd6 0xcfc31fc3e0ffe3f7 0x9f9f863f87c1ffc7

def z590 : W := mkw 0x82c0014160ada338 0x0905800282c15b46 0xc3c00003e0ffe3d7 0x0f87800007c1ffc7

def z591 : W := mkw 0xc2c304c160a4a118 0x0985860982c14942 0xc0c100c3e0c0e3f5 0x1781820187c181c7

def z592 : W := mkw 0x6c17b816bd46dcc2 0x22d82f702d7a8db9 0xfc3ff83fff07fc6f 0xeff87ff07ffe0ff8

def z593 : W := mkw 0x113000000a500000 0x002260000014a000 0x0330000000f80010 0x000660000001f000

def z594 : W := mkw 0xfbbbf6b80b521484 0x17f777ed7016a429 0xfffffffc1f001c3f 0xf3fffffff83e0038

def z595 : W := mkw 0x792bd22800000000 0x12f257a450000000 0xfc3ff83c0000002f 0xe3f87ff078000000

def z596 : W := mkw 0x0400085610006d92 0x00080010ac2000db 0x0c0118ff1800ffed 0x34180231fe3001ff

def z597 : W := mkw 0x6803b800a506d840 0x22d00770014a0db0 0xf003f800e707fc22 0xefe007f001ce0ff8

def z598 : W := mkw 0x0414081618404c82 0x000828102c308099 0x0c3c183c18c01ff9 0x341878307831803f

def z599 : W := mkw 0x6c57b803fff6d840 0x62d8af7007ffedb0 0xfc03f803fffffc6f 0xeff807f007fffff8

def z600 : W := mkw 0x6803b000a5069040 0x22d00760014a0d20 0xf002e000ff071c6b 0xefe005c001fe0e38

def z601 : W := mkw 0x0054005508c02592 0x0000a800aa11804b 0x00fc00fc18c01ff9 0x3401f801f831803f

def z602 : W := mkw 0x1120000000000000 0x0022400000000000 0x333000000000001b 0x4066600000000000

def z603 : W := mkw 0x3d7cda7f18c06d92 0x127af9b4fe3180db 0x3cfdf8ff18c0fffd 0x7479fbf1fe3181ff

def z604 : W := mkw 0x97fc00035af00000 0x412ff80006b5e000 0x0ffc000318f8005d 0x001ff8000631f000

def z605 : W := mkw 0x0454081718c04c82 0x0008a8102e318099 0x0cfc183f18c01c5d 0x2019f8307e318038

def z606 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfc000318c0ffdd 0x0419f800063181ff

def z607 : W := mkw 0xd3b367b06b7f96ac 0x0da766cf60d6ff2d 0xf332e730ffff1ffb 0xffe665ce61fffe3f

def z608 : W := mkw 0xc2c325c161afb338 0x0985864b82c35f66 0xf3c3e7c3ffffffff 0xffe787cf87ffffff

def z609 : W := mkw 0xeec3bcc3f5a6f958 0x2bdd877987eb4df2 0xfcc3f8c3ff07fc6f 0xeff987f187fe0ff8

def z610 : W := mkw 0x0040014160ada338 0x0800800282c15b46 0x03020703e0ffe3f3 0x9c06040e07c1ffc7

def z611 : W := mkw 0xffbfd6aa9e500000 0x53ff7fad553ca000 0xfffffffc1f00003f 0xf3fffffff83e0000

def z612 : W := mkw 0x0454095778edefba 0x0808a812aef1dbdf 0x00000003f8ffffc0 0x0c00000007f1ffff

def z613 : W := mkw 0x0414081618404c82 0x000828102c308099 0x0000000018001c00 0x0000000000300038

def z614 : W := mkw 0xeecf9803f4a4c840 0x63dd9f3007e94990 0xcccd1803e000e004 0x03999a3007c001c0

def z615 : W := mkw 0x97fc4eff18c06d92 0x112ff89dfe3180db 0x0ffd1fff18c0fffd 0x341ffa3ffe3181ff

def z616 : W := mkw 0x7923d22000000000 0x02f247a440000000 0xff33ff300000003f 0xf3fe67fe60000000

def z617 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfc18fc18c01f98 0x3019f831f831803f

def z618 : W := mkw 0xbbe8000140a00000 0x0377d00002814000 0xfffc0003e0f8005f 0x4bfff80007c1f000

def z619 : W := mkw 0xffff67f3ffffb7bc 0x4ffffecfe7ffff6f 0xffffe7f3ffffffff 0xffffffcfe7ffffff

def z620 : W := mkw 0x0040004100802110 0x0000800082010042 0x0000000300c0e3c0 0x04000000060181c7

def z621 : W := mkw 0x00004330000906a4 0x040000866000120d 0x0000073000000380 0x1000000e60000007

def z622 : W := mkw 0x1120422000000000 0x0022408440000000 0x0330073000000010 0x1006600e60000000

def z623 : W := mkw 0x005400014af00000 0x4000a8000295e000 0x0000000000f80000 0x000000000001f000

def z624 : W := mkw 0x4403b802b506d840 0x20880770056a0db0 0x0003f803ff07fc60 0xac0007f007fe0ff8

def z625 : W := mkw 0x0454004318c02110 0x0008a80086318042 0x0cfd00c318c0e3fd 0x1419fa01863181c7

def z626 : W := mkw 0x0454000318c00000 0x0008a80006318000 0x0cfd18ff18c0007d 0x3019fa31fe318000

def z627 : W := mkw 0x0000001000000480 0x0000000020000009 0x0000003000001fa0 0x340000006000003f

def z628 : W := mkw 0xffff0583fefd8228 0x4bfffe0b07fdfb04 0xfffe0703ffff005f 0xcbfffc0e07fffe00

def z629 : W := mkw 0xee83bc82b506d840 0x23dd0779056a0db0 0xffc3ffc3ff07fc7f 0xffff87ff87fe0ff8

def z630 : W := mkw 0x0000000000000000 0x0000000000000000 0x0ccd18cc00000004 0x00199a3198000000

def z631 : W := mkw 0x04540857def06d92 0x4008a810afbde0db 0x00000003fff8ffc0 0x0c00000007fff1ff

def z632 : W := mkw 0xbbb800000a500000 0x037770000014a000 0xfffc00001ff8005f 0x4bfff800003ff000

def z633 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xf3fee7fc00000012 0xd3e7fdcff8000000

def z634 : W := mkw 0x04546b7719cb7fb6 0x0408a8d6ee3396ff 0x0cffffff18c7fffd 0xb419fffffe318fff

def z635 : W := mkw 0x15744b771ad96fb6 0x042ae896ee35b2df 0x0ffd1fff18f8fffd 0x341ffa3ffe31f1ff

def z636 : W := mkw 0xd3ff05c16afda338 0x49a7fe0b82d5fb46 0xc3ff07c3e0ffe3f7 0x9f87fe0f87c1ffc7

def z637 : W := mkw 0xea8b948800000000 0x13d5172910000000 0xfccff8cc0000002f 0xe3f99ff198000000

def z638 : W := mkw 0x6c579857bcc4edd2 0x22d8af30af7989db 0xccfd18fff8c0fffd 0x3799fa31fff181ff

def z639 : W := mkw 0xc2c367f161afb7bc 0x0d8586cfe2c35f6f 0xc3c3e7f3e0fffff7 0xbf8787cfe7c1ffff

def z640 : W := mkw 0x2c5408579cc06d92 0x0258a810af3980db 0xfcfd18ffffc0ffff 0x7ff9fa31ffff81ff

def z641 : W := mkw 0x4003000020048000 0x0080060000400900 0xc0020000e0070002 0x8b80040001c00e00

def z642 : W := mkw 0x6803b000a5069040 0x22d00760014a0d20 0xf003e003e707e067 0xcfe007c007ce0fc0

def z643 : W := mkw 0x1120432000090220 0x0022408640001204 0x3332e73000ff03fb 0xfc6665ce6001fe07

def z644 : W := mkw 0x7d33b802bf56d840 0x22fa6770057eadb0 0xff33f803fffffc7f 0xeffe67f007fffff8

def z645 : W := mkw 0x4003000020048000 0x0080060000400900 0x000300000007e020 0x8400060000000fc0

def z646 : W := mkw 0xfbebd7e940a92338 0x1bf7d7afd2815246 0xfffffffc00f803bf 0xf3fffffff801f007

def z647 : W := mkw 0xfbab0580e63d8228 0x4bf7560b01cc7b04 0xf3020700e73f0002 0xcbe6040e01ce7e00

def z648 : W := mkw 0x0040014100892330 0x0000800282011246 0x03c307c300ffe3f7 0x9c07860f8601ffc7

def z649 : W := mkw 0x113043300a5906a4 0x042260866014b20d 0x0330073018f81ff9 0x3406600e6031f03f

def z650 : W := mkw 0xaecc0003d4a00000 0x435d980007a94000 0xfccc0003ff00004f 0x4bf9980007fe0000

def z651 : W := mkw 0x045429571bdb7fb6 0x0408a852ae37b6ff 0x0cfd18ff1ffffffd 0x3c19fa31fe3fffff

def z652 : W := mkw 0x0454080318c04800 0x0008a81006318090 0x0cfd180318c0fc7d 0x2419fa30063181f8

def z653 : W := mkw 0x7933f3300b5b16a4 0x06f267e66016b62d 0xff33ff301fff1fff 0xfffe67fe603ffe3f

def z654 : W := mkw 0xbbfc00014af00000 0x4377f8000295e000 0xfffc000000f8001f 0x43fff8000001f000

def z655 : W := mkw 0xc2c304c160a4a118 0x0985860982c14942 0xc3c100c3e0f8e057 0x0b87820187c1f1c0

def z656 : W := mkw 0x4003b8002106d840 0x2080077000420db0 0x3003f8001f07fc6b 0xec6007f0003e0ff8

def z657 : W := mkw 0xfbabd7a800090220 0x13f757af50001204 0xfffffffc00ff03ff 0xfffffffff801fe07

def z658 : W := mkw 0x8280058040290228 0x0905000b00805204 0x0300070000380000 0x0006000e00007000

def z659 : W := mkw 0x0000084400006912 0x00000010880000d2 0x000118cc0000e000 0x00000231980001c0

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c3c183c00000008 0x2018783078000000

def z661 : W := mkw 0x5133f7b80b5b16a4 0x14a267ef7016b62d 0x3333fffc1fff1ffb 0xfc6667fff83ffe3f

def z662 : W := mkw 0x1120432002190224 0x0422408640043204 0x0300070000380000 0x0006000e00007000

def z663 : W := mkw 0x6803900000000000 0x02d0072000000000 0xf002e00000000002 0xc3e005c000000000

def z664 : W := mkw 0xffffd6ab18c00000 0x13ffffad56318000 0xffffffff18c0007f 0xf3fffffffe318000

def z665 : W := mkw 0xbffc000318c00000 0x037ff80006318000 0xfffc000318c0005f 0x43fff80006318000

def z666 : W := mkw 0x82c004c140a02118 0x0905800982814042 0x00c000c000000000 0x0001800180000000

def z667 : W := mkw 0x113043300a5906a4 0x042260866014b20d 0x333007301ff803db 0x5866600e603ff007

def z668 : W := mkw 0x93f067f14bfb37bc 0x0d27e0cfe297f66f 0x33f2e7f01fff1ffb 0xfc67e5cfe03ffe3f

def z669 : W := mkw 0x04402943f5affb78 0x2808805287eb5ff6 0x00000003ffffffc0 0x0c00000007ffffff

def z670 : W := mkw 0x113062300b521484 0x042260c46016a429 0x3032e0301f071c6b 0xec6065c0603e0e38

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000003e0000047 0x0b80000007c00000

def z672 : W := mkw 0x82c005c140a92338 0x0905800b82815246 0xc3c007c3e0f803d7 0x1b87800f87c1f007

def z673 : W := mkw 0xeecf948bd4a00000 0x53dd9f2917a94000 0xcccd18cfe0000004 0x03999a319fc00000

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c0118000000002d 0x2018023000000000

def z675 : W := mkw 0x2800b00085021040 0x22500160010a0420 0x3000e00007000000 0x406001c0000e0000

def z676 : W := mkw 0x2c00b80295025840 0x22580170052a04b0 0x3c02f8001f071c6b 0xec7805f0003e0e38

def z677 : W := mkw 0x6803d6a800000000 0x12d007ad50000000 0xfc03fffc0000002f 0xf3f807fff8000000

def z678 : W := mkw 0x11206320031b1224 0x042240c640063624 0x3332e730073f003b 0xf86665ce600e7e00

def z679 : W := mkw 0xc2c304c160a4a118 0x0985860982c14942 0xc0c300c3e007e067 0x8f81860187c00fc0

def z680 : W := mkw 0x001020100b521484 0x040020402016a429 0x000000001f001c00 0x00000000003e0038

def z681 : W := mkw 0x117463750bdb37b6 0x0422e8c6ea17b66f 0x33fee7fc1fff1ffb 0xfc67fdcff83ffe3f

def z682 : W := mkw 0x0000422000000000 0x0000008440000000 0x0002e73000000020 0xb00005ce60000000

def z683 : W := mkw 0x04440003d4a00000 0x4008880007a94000 0x00000003e0000000 0x0000000007c00000

def z684 : W := mkw 0x7d23fa22b506d840 0x22fa47f4456a0db0 0xff33ff33ff07fc7f 0xfffe67fe67fe0ff8

def z685 : W := mkw 0x000005c000092338 0x0800000b80001246 0x000007c000000380 0x1000000f80000007

def z686 : W := mkw 0x0040000100800000 0x0000800002010000 0x00c0000300c00055 0x0001800006018000

def z687 : W := mkw 0x0040014160ada338 0x0800800282c15b46 0x00c100c3e0ffe3f5 0x1c01820187c1ffc7

def z688 : W := mkw 0x0444085710806d92 0x00088810ae2100db 0x0ccd18ff0000ffa4 0x34199a31fe0001ff

def z689 : W := mkw 0x2c00200295021000 0x02580040052a0420 0xfc02e003ff071c6f 0xeff805c007fe0e38

def z690 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xff3eff3c0000000a 0xe3fe7dfe78000000

def z691 : W := mkw 0x3d3cda3e18404c82 0x127a79b47c308099 0x3c3cf83c18001c08 0x607879f078300038

def z692 : W := mkw 0xc6d705c378eda338 0x098dae0b86f1db46 0xcfff07c3f8ffe3ff 0x9f9ffe0f87f1ffc7

def z693 : W := mkw 0x0010201009421480 0x0000204020128429 0x3032e0301fc71ffb 0xfc6065c0603f8e3f

def z694 : W := mkw 0x15306b32bf5fdee4 0x242a60d6657ebfbd 0x3332e733fffffffb 0xfc6665ce67ffffff

def z695 : W := mkw 0x0454095778edefba 0x0808a812aef1dbdf 0x0cfd18fff8fffffd 0x3c19fa31fff1ffff

def z696 : W := mkw 0x117063716bffb7bc 0x0c22e0c6e2d7ff6f 0x3332e733fffffffb 0xfc6665ce67ffffff

def z697 : W := mkw 0x15746b771bdb7fb6 0x042ae8d6ee37b6ff 0x3332e7331ffffffb 0xfc6665ce663fffff

def z698 : W := mkw 0xbba846a800000000 0x1377508d50000000 0xfffc07fc0000001f 0x53fff80ff8000000

def z699 : W := mkw 0x97fc08575af06d92 0x412ff810aeb5e0db 0x0ffd18ff18f8fffd 0x341ffa31fe31f1ff

def z700 : W := mkw 0xea83948000000000 0x03d5072900000000 0xffc3ffc00000003f 0xf3ff87ff80000000

def z701 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc02f800ff071c0a 0xebf805f001fe0e38

def z702 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xf332e7300000003b 0xf3e665ce60000000

def z703 : W := mkw 0x001021100b5b16a4 0x040020422016b62d 0x003000301fff1ff9 0x3c006000603ffe3f

def z704 : W := mkw 0xc6d70cd778e4ed9a 0x098dae19aef1c9db 0xccfd18fff8c0fffd 0x3799fa31fff181ff

def z705 : W := mkw 0x0000010000090220 0x0000000200001204 0x0000000000ff03c0 0x0c0000000001fe07

def z706 : W := mkw 0xfbeb05c160ada338 0x0bf7d60b82c15b46 0xffff07c3e0ffe3ff 0xdffffe0f87c1ffc7

def z707 : W := mkw 0xfbabf7a8e52f9268 0x3bf757ef51ca5f24 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z708 : W := mkw 0x2c400003d4a00000 0x0258800007a94000 0xfc000003fff8004f 0x4bf8000007fff000

def z709 : W := mkw 0x15646b67139b7b36 0x042ac8d6ce2736f6 0x3fcfffcf073fe006 0xc87f9fff9e0e7fc0

def z710 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffefffc0000001a 0xf3fffdfff8000000

def z711 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc00fffff8005f 0x5bfff801fffff000

def z712 : W := mkw 0xbba80854c6306d92 0x43775010a98c60db 0xf30118fce738ffa2 0x7fe60231f9ce71ff

def z713 : W := mkw 0xbffc0043def02110 0x437ff80087bde042 0xfffd18fffff8e3ff 0x7ffffa31fffff1c7

def z714 : W := mkw 0xbffc0817def04c82 0x437ff8102fbde099 0xfffc183ffff81fff 0x7ffff8307ffff03f

def z715 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffd00c3fff8ffff 0x5ffffa0187fff1ff

def z716 : W := mkw 0xbffc048bdef00000 0x537ff80917bde000 0xfffc00cffff8005f 0x4bfff8019ffff000

def z717 : W := mkw 0xd3f366f16bf6b59c 0x0da7e6cde2d7ed6b 0xf0f1e0f3ff00fc0c 0x63e1e3c1e7fe01f8

def z718 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f803ff07fc0e 0xebf807f007fe0ff8

def z719 : W := mkw 0xbbec0001c6b00000 0x4377d800038d6000 0xf3cc0000e7380002 0x4be7980001ce7000

def z720 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff18c0ffcc 0x2419fa31fe3181ff

def z721 : W := mkw 0xbfec0003d6b00000 0x437fd80007ad6000 0xffcc0003ff38004f 0x4bff980007fe7000

def z722 : W := mkw 0x6857b055adc6b5d2 0x22d0af60ab5b8d6b 0xf0fee0fce7c70392 0xdbe1fdc1f9cf8e07

def z723 : W := mkw 0xbffc0057def02592 0x437ff800afbde04b 0xfffc0003fff803df 0x4bfff80007fff007

def z724 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c31fffe0ffe3f7 0xbf87863fffc1ffc7

def z725 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc02f803ff07fc4a 0xeff805f007fe0ff8

def z726 : W := mkw 0xbffc46ffdef02592 0x537ff88dffbde04b 0xfffc07fffff803df 0x5bfff80ffffff007

def z727 : W := mkw 0x6803b00021069000 0x02d0076000420d20 0xfc03f803ff07fc6f 0xeff807f007fe0ff8

def z728 : W := mkw 0xc2cf05c160ada338 0x49859e0b82c15b46 0xc3cf07c3e0ffe3f7 0x9f879e0f87c1ffc7

def z729 : W := mkw 0x3d34fa369f525cc6 0x267a69f46d3ea4b9 0x3c3cf83c1f001c08 0x607879f0783e0038

def z730 : W := mkw 0xfbabd6a8a4048040 0x33f757ad51480900 0xfffffffce000003f 0xf3fffffff9c00000

def z731 : W := mkw 0x04542957dffb7fb6 0x4408a852afbff6ff 0x00000003ffffffc0 0x0c00000007ffffff

def z732 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffe0703fff8007f 0xdbfffc0e07fff000

def z733 : W := mkw 0xaec0bdc3d5ab7b78 0x2b5d817b87ab56f6 0x3fc0ffc01ff81f98 0x707f81ff803ff03f

def z734 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f803ffc7ffff 0xfff807f007ff8fff

def z735 : W := mkw 0x40036ff4210fffbe 0x0c8006dfe8421fff 0x0003fffc0007ffa0 0xb40007fff8000fff

def z736 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc3ff83fff07fc6f 0xeff87ff07ffe0ff8

def z737 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfcfc0003fff8004c 0x4bf9f80007fff000

def z738 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xffffffff0000e07f 0xf7fffffffe0001c0

def z739 : W := mkw 0x6803d6a800000000 0x12d007ad50000000 0xfcfffffc0000003f 0xf3f9fffff8000000

def z740 : W := mkw 0xaedc0003def00000 0x435db80007bde000 0xc0000003fff80040 0x0b80000007fff000

def z741 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xf3300003fff8005b 0x4be6600007fff000

def z742 : W := mkw 0x2c540003def00000 0x4258a80007bde000 0xfcfc0003fff8005f 0x4bf9f80007fff000

def z743 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffd18cffff8ffdf 0x4ffffa319ffff1ff

def z744 : W := mkw 0xbffcd6abdef00000 0x537ff9ad57bde000 0xfffcfffffff8005f 0x7bfff9fffffff000

def z745 : W := mkw 0x3968d36960ada338 0x1a72d1a6d2c15b46 0x3c3cf83fe0ffe3c8 0x6c7879f07fc1ffc7

def z746 : W := mkw 0xbbfc0001cef00000 0x4377f800039de000 0xf3fc0003e7f80057 0x4be7f80007cff000

def z747 : W := mkw 0xbbe80001c6b00000 0x4377d000038d6000 0xf3c00003e7380006 0x4be7800007ce7000

def z748 : W := mkw 0xd3abd6a800000000 0x11a757ad50000000 0x0ffffffc0000003d 0xb01ffffff8000000

def z749 : W := mkw 0xbfa80002d6300000 0x437f500005ac6000 0xff000000ff38000a 0x4bfe000001fe7000

def z750 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc00c003ff 0xf7fffffff8018007

def z751 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3302e7301fff1fe2 0xfc6605ce603ffe3f

def z752 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffc0033fff8ffff 0x7ffff80067fff1ff

def z753 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xffcc0000e7380006 0x4bff980001ce7000

def z754 : W := mkw 0xbffcd22bdef00000 0x537ff9a457bde000 0xfffdf8fffff8007f 0x7bfffbf1fffff000

def z755 : W := mkw 0x0454295719cb7fb6 0x0408a852ae3396ff 0x0000000318c7ffc0 0x0400000006318fff

def z756 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0003fff803ff 0x5ffff80007fff007

def z757 : W := mkw 0xbba8422000000000 0x0377508440000000 0xfffffffc0000003f 0xf3fffffff8000000

def z758 : W := mkw 0x3d3c6a369f525c86 0x467a78d46d3ea4b9 0x3c3cf83c1f001c08 0x607879f0783e0038

def z759 : W := mkw 0x4443bdc3318ffb78 0x2888877b86631ff6 0x0cc3ffc318c7fffd 0xb41987ff86318fff

def z760 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0003fff8001c 0x43fff80007fff000

def z761 : W := mkw 0xbffc0847def06912 0x437ff8108fbde0d2 0xfffd18cffff8fc7f 0x6ffffa319ffff1f8

def z762 : W := mkw 0xc2c395c960ada338 0x1985872b92c15b46 0xc3c31fcfe0ffe3f7 0x9f87863f9fc1ffc7

def z763 : W := mkw 0x0454085758e06d92 0x0008a810aeb1c0db 0x0cfd18fff8f8fffd 0x3c19fa31fff1f1ff

def z764 : W := mkw 0x7d3f05c2be5da338 0x4afa7e0b857cbb46 0x3c3f07c01f07e3a8 0xd4787e0f803e0fc7

def z765 : W := mkw 0x93fc00014af00000 0x4127f8000295e000 0xf3fc0003fff8005f 0x4be7f80007fff000

def z766 : W := mkw 0xbfb80002de700000 0x437f700005bce000 0xff300003fff8005f 0x4bfe600007fff000

def z767 : W := mkw 0x5123d6a800000000 0x10a247ad50000000 0x3ffffffc0000003f 0xf07ffffff8000000

def z768 : W := mkw 0x400367b0210f96ac 0x0c8006cf60421f2d 0x0002e73000071fa0 0xb40005ce60000e3f

def z769 : W := mkw 0xbba8d6a800000000 0x137751ad50000000 0x3ffefffc0000003b 0xf07ffdfff8000000

def z770 : W := mkw 0x97a86eaab506d840 0x312f50dd556a0db0 0x03fc07ffff07fc50 0x1c07f80ffffe0ff8

def z771 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffd18fffff8e3df 0x5bfffa31fffff1c7

def z772 : W := mkw 0x7d33db32be5dcee4 0x26fa67b6657cbb9d 0xcf311f33e0f8e394 0x139e623e67c1f1c7

def z773 : W := mkw 0xfbabd6a840200000 0x13f757ad50804000 0xfffffffce038003f 0xfbfffffff9c07000

def z774 : W := mkw 0xfbabd6a820048000 0x13f757ad50400900 0xffffffffe000e03f 0xf3ffffffffc001c0

def z775 : W := mkw 0x82d000014af00000 0x0105a0000295e000 0xc3c00003fff80057 0x0b87800007fff000

def z776 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7301fff1fb8 0xf46665ce603ffe3f

def z777 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffc183ffff8ffdf 0x6ffff8307ffff1ff

def z778 : W := mkw 0x3d3cfa329f525cc4 0x667a79f4653ea4b9 0x3c3cf8301f001c08 0x607879f0603e0038

def z779 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xff03ff03ff07fc7f 0xfffe07fe07fe0ff8

def z780 : W := mkw 0xea83948000000000 0x03d5072900000000 0xfffffffc0000003f 0xf3fffffff8000000

def z781 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0xccfd18fff8c0ffff 0x3f99fa31fff181ff

def z782 : W := mkw 0x0414085618406d92 0x00082810ac3080db 0x0cfd18fc1800ffbd 0x3419fa31f83001ff

def z783 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff00c0ffb4 0x3419fa31fe0181ff

def z784 : W := mkw 0xbffc4223def00000 0x437ff88447bde000 0xfffc0733fff8005f 0x5bfff80e67fff000

def z785 : W := mkw 0x045408579cc06d92 0x0008a810af3980db 0x0cfd18ffffc0fffd 0x3c19fa31ffff81ff

def z786 : W := mkw 0xbbbc0000ce700000 0x43777800019ce000 0xf33c0000e7380002 0x4be6780001ce7000

def z787 : W := mkw 0xbfbc0002de700000 0x437f780005bce000 0xff3c0003ff38004f 0x4bfe780007fe7000

def z788 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7001fff1fdb 0xcc6665ce003ffe3f

def z789 : W := mkw 0xbffc0847def06912 0x437ff8108fbde0d2 0xfffd18fffff8e07f 0x7bfffa31fffff1c0

def z790 : W := mkw 0xbffc46abdef00000 0x537ff88d57bde000 0xfffc0703fff8005f 0x4bfff80e07fff000

def z791 : W := mkw 0x93f000514af02590 0x0127e000a295e04b 0xf3f100f3fff8ffff 0x7fe7e201e7fff1ff

def z792 : W := mkw 0x045408571ad06d92 0x0008a810ae35a0db 0x0cfd18ff1ff8fffd 0x3c19fa31fe3ff1ff

def z793 : W := mkw 0x0040085500806d92 0x00008010aa0100db 0x0cfd18ff00c0fffd 0x3419fa31fe0181ff

def z794 : W := mkw 0x04542957fdeffffa 0x2808a852affbdfff 0x00000003ffffffc0 0x0c00000007ffffff

def z795 : W := mkw 0xfbabd6a860248008 0x1bf757ad50c04900 0xfffffffce000003f 0xf3fffffff9c00000

def z796 : W := mkw 0x6c032002b5069000 0x02d80640056a0d20 0xfc03e003ff07fc6f 0xeff807c007fe0ff8

def z797 : W := mkw 0xd3ffb8016bf6d840 0x61a7ff7002d7edb0 0x03fff80000fffc30 0xa407fff00001fff8

def z798 : W := mkw 0x82c005c160ada338 0x0905800b82c15b46 0xc3c007c3e0ffe3d7 0x1f87800f87c1ffc7

def z799 : W := mkw 0xc283d6a800000000 0x118507ad50000000 0xcffffffc0000003f 0xb39ffffff8000000

def z800 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c307c3e0ffe3c6 0x8f87860f87c1ffc7

def z801 : W := mkw 0xbffc4effdef06d92 0x537ff89dffbde0db 0xfffd1ffffff8ffff 0x7ffffa3ffffff1ff

def z802 : W := mkw 0xaa880000c6300000 0x43551000018c6000 0xc0000000e7380000 0x0b80000001ce7000

def z803 : W := mkw 0xea9bb5980b5b16a4 0x17d5376b3016b62d 0xcccd18cc1fff1fc4 0x0f999a31983ffe3f

def z804 : W := mkw 0x113463340b5b16a6 0x042268c66816b62d 0x333ee73c1fff1ffb 0xfc667dce783ffe3f

def z805 : W := mkw 0xaecc0003d6b00000 0x435d980007ad6000 0xcccc0003e7380004 0x0b99980007ce7000

def z806 : W := mkw 0xbffcda3fdef04c82 0x537ff9b47fbde099 0xfffcf83ffff81c5f 0x6bfff9f07ffff038

def z807 : W := mkw 0xaecc6333d5ab16a4 0x475d98c667ab562d 0xcccee733e0071fa4 0xb7999dce67c00e3f

def z808 : W := mkw 0x4003ffe8210ffb78 0x388007ffd0421ff6 0x0003fffc0007ffa0 0xb40007fff8000fff

def z809 : W := mkw 0xbffc0817def04c82 0x437ff8102fbde099 0xfffd183ffff8fc7f 0x6ffffa307ffff1f8

def z810 : W := mkw 0x4457d6abdef00000 0x5088afad57bde000 0x0003fffffff80060 0xb80007fffffff000

def z811 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7301fff1f9a 0xf86665ce603ffe3f

def z812 : W := mkw 0xeecf9cc3f4a4e958 0x6bdd9f3987e949d2 0xcccd18c3e000e004 0x03999a3187c001c0

def z813 : W := mkw 0xfbabd6a820048000 0x13f757ad50400900 0xfffffffc0007e03f 0xf7fffffff8000fc0

def z814 : W := mkw 0x0410081218404c80 0x0008201024308099 0x0cfd18ff18c0fffd 0x3419fa31fe3181ff

def z815 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3f3eff3c1fff1ffb 0xfc7e7dfe783ffe3f

def z816 : W := mkw 0xbba8d228c6300000 0x537751a4518c6000 0xff3cf83ce738000a 0x6bfe79f079ce7000

def z817 : W := mkw 0x2c540857def06d92 0x4258a810afbde0db 0xfcfd18fffff8ffff 0x7ff9fa31fffff1ff

def z818 : W := mkw 0x440328023106d800 0x0088065004620db0 0xfc03f803ff07fc6f 0xeff807f007fe0ff8

def z819 : W := mkw 0xbffc0047def02112 0x437ff8008fbde042 0xfffc00cffff8005f 0x4bfff8019ffff000

def z820 : W := mkw 0xbffc0803def04800 0x437ff81007bde090 0xfffd1803fff8e05f 0x4bfffa3007fff1c0

def z821 : W := mkw 0x4457fb7739cffff6 0x2488aff6ee739fff 0x0cffffff18c7fffd 0xb419fffffe318fff

def z822 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc30307c3e0ffe3e2 0x9f86060f87c1ffc7

def z823 : W := mkw 0x7923d22000000000 0x02f247a440000000 0xfffffffc0000003f 0xf3fffffff8000000

def z824 : W := mkw 0xeecb9ccbf4a4e958 0x3bdd973997e949d2 0xcccd18cfe000e004 0x03999a319fc001c0

def z825 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3f307f3e0ffe3ff 0xbf87e60fe7c1ffc7

def z826 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3ff07ffe0ffe3f7 0x9f87fe0fffc1ffc7

def z827 : W := mkw 0x4003f7f8210fb7bc 0x1c8007eff0421f6f 0x0003fffc0007ffa0 0xb40007fff8000fff

def z828 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfcfff803ff07fc7f 0xeff9fff007fe0ff8

def z829 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff18c0ff9c 0x3019fa31fe3181ff

def z830 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c107c3e0ffe3d4 0x1f87820f87c1ffc7

def z831 : W := mkw 0xaedc0003def00000 0x435db80007bde000 0xfccc0003fff8004f 0x4bf9980007fff000

def z832 : W := mkw 0xbbe80001c6b00000 0x4377d000038d6000 0xf3c00000e7f80012 0x4be7800001cff000

def z833 : W := mkw 0xbffc0013def00480 0x437ff80027bde009 0xfffc0033fff81c5f 0x6bfff80067fff038

def z834 : W := mkw 0x393000008e500000 0x02726000011ca000 0xf3300000fff8005b 0x4be6600001fff000

def z835 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xff03f803fffffc7f 0xeffe07f007fffff8

def z836 : W := mkw 0x4003b910210fdee4 0x2480077220421fbd 0x0003f8000007ffa0 0xa40007f000000fff

def z837 : W := mkw 0x3d38fa3a9f525cc4 0x367a71f4753ea4b9 0x3c3cf83c1f001c08 0x607879f0783e0038

def z838 : W := mkw 0xc2830580200d8220 0x0185060b00401b04 0xc3c307c3e0ffe3f7 0x9f87860f87c1ffc7

def z839 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc02e003ff07fc4f 0xcff805c007fe0ff8

def z840 : W := mkw 0xbffc04c3def02118 0x4b7ff80987bde042 0xfffc00c3fff8005f 0x4bfff80187fff000

def z841 : W := mkw 0x0440084310806910 0x00088010862100d2 0x0cfd18ff18c0fffd 0x3419fa31fe3181ff

def z842 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xf3000003fff8ffc2 0x4fe6000007fff1ff

def z843 : W := mkw 0x792bd6a800000000 0x12f257ad50000000 0x3cfffffc0000003d 0xf079fffff8000000

def z844 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc18001c7f 0xf7fffffff8300038

def z845 : W := mkw 0xbffc0807def04802 0x437ff8100fbde090 0xfffc180ffff8005f 0x4bfff8301ffff000

def z846 : W := mkw 0x3d740003def00000 0x427ae80007bde000 0xff300003fff8005f 0x4bfe600007fff000

def z847 : W := mkw 0xffffdeff18c06d92 0x13ffffbdfe3180db 0xf302e70318c0ffc2 0xc7e605ce063181ff

def z848 : W := mkw 0x0000422000000000 0x0000008440000000 0x0cfffffc0000003d 0xb019fffff8000000

def z849 : W := mkw 0x113000000a500000 0x002260000014a000 0xf3300003fff8005f 0x4be6600007fff000

def z850 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3030703e0ffe3e7 0x8f86060e07c1ffc7

def z851 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc0000000e 0xe3fffffff8000000

def z852 : W := mkw 0x93e0000142b00000 0x0127c00002856000 0xf3c00003e7f80057 0x4be7800007cff000

def z853 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffee003fff8007f 0xebfffdc007fff000

def z854 : W := mkw 0xbffcda7fdef06d92 0x537ff9b4ffbde0db 0xfffdf8fffff8ffff 0x7ffffbf1fffff1ff

def z855 : W := mkw 0xbffc4233def00480 0x437ff88467bde009 0xfffee733fff81fff 0xfffffdce67fff03f

def z856 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3f33ff301fff1fff 0xfc7e67fe603ffe3f

def z857 : W := mkw 0xbffc0017def00482 0x437ff8002fbde009 0xfffc003ffff8005f 0x4bfff8007ffff000

def z858 : W := mkw 0x0050005108c02590 0x0000a000a211804b 0x0cfd18ff18c0fffd 0x3419fa31fe3181ff

def z859 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3000003e7380047 0x4be6000007ce7000

def z860 : W := mkw 0xc2c705c560ada33a 0x09858e0b8ac15b46 0xc3cf07cfe0ffe3f7 0x9f879e0f9fc1ffc7

def z861 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff1800ffac 0x3419fa31fe3001ff

def z862 : W := mkw 0x3928d22800000000 0x127251a450000000 0x3ffffffc0000003f 0xf07ffffff8000000

def z863 : W := mkw 0xfbabd6a884000000 0x13f757ad51080000 0xfffffffce700003f 0xfbfffffff9ce0000

def z864 : W := mkw 0xc2830580602d8228 0x0985060b00c05b04 0xc3030703e0ffe3f7 0x9f86060e07c1ffc7

def z865 : W := mkw 0xbfbc0002de700000 0x437f780005bce000 0xff3c0000fff8005b 0x4bfe780001fff000

def z866 : W := mkw 0x3d3c00029e500000 0x427a7800053ca000 0xff3c0003fff8005f 0x4bfe780007fff000

def z867 : W := mkw 0x00006330010b16a4 0x040000c66002162d 0x3302e7301fff1ffb 0xfc6605ce603ffe3f

def z868 : W := mkw 0x86d40003def00000 0x410da80007bde000 0xcffc0003fff8005f 0x0b9ff80007fff000

def z869 : W := mkw 0x3d7408579ed06d92 0x027ae810af3da0db 0xfffd18fffff8ffff 0x7ffffa31fffff1ff

def z870 : W := mkw 0xbffc4233def00484 0x477ff88467bde009 0xfffc0033fff8005f 0x4bfff80067fff000

def z871 : W := mkw 0xbffcd22bdef00000 0x537ff9a457bde000 0xfffeff3ffff8007f 0xfbfffdfe7ffff000

def z872 : W := mkw 0xbffc0803def04800 0x437ff81007bde090 0xfffc0003fff8fc5f 0x4ffff80007fff1f8

def z873 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0ffd18ff18f8ffff 0x3c1ffa31fe31f1ff

def z874 : W := mkw 0x045408575af06d92 0x4008a810aeb5e0db 0x0cfd18ff18f8fffd 0x3419fa31fe31f1ff

def z875 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3302e7001fff1ff3 0xdc6605ce003ffe3f

def z876 : W := mkw 0x113021000b5b1220 0x002260420016b624 0x3332e7001fff1ffb 0xfc6665ce003ffe3f

def z877 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xfffd18fce738003f 0x7bfffa31f9ce7000

def z878 : W := mkw 0xfbabd6a8c4200000 0x53f757ad51884000 0xfffffffce000003f 0xf3fffffff9c00000

def z879 : W := mkw 0x86d40857def06d92 0x410da810afbde0db 0xcffd18fffff8ffff 0x3f9ffa31fffff1ff

def z880 : W := mkw 0x40036330210f96a4 0x048006c660421f2d 0x0003e7300007ffa0 0xb40007ce60000fff

def z881 : W := mkw 0x93f447f54af927be 0x0d27e88fea95f24f 0x03fc07fc00f80390 0x1007f80ff801f007

def z882 : W := mkw 0xbbb80000ce700000 0x43777000019ce000 0xf3300000e7f80012 0x4be6600001cff000

def z883 : W := mkw 0x4457bdd739cffffa 0x2888af7bae739fff 0x0cffffff18c7fffd 0xb419fffffe318fff

def z884 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0003e7f80016 0x4bfff80007cff000

def z885 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffc18fffff81fdf 0x7bfff831fffff03f

def z886 : W := mkw 0x3920000086100000 0x02724000010c2000 0xf3000000e7380002 0x4be6000001ce7000

def z887 : W := mkw 0x93a0000042300000 0x0127400000846000 0xf3000000e7380002 0x4be6000001ce7000

def z888 : W := mkw 0xc6970d96786dceaa 0x098d2e1b2cf0db9d 0xcf3e1f3cf83f1c0a 0xab9e7c3e79f07e38

def z889 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xcffc0003fff80054 0x0b9ff80007fff000

def z890 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0fff1fff18c0ffff 0xb41ffe3ffe3181ff

def z891 : W := mkw 0xbffc422bdef00000 0x537ff88457bde000 0xfffc003ffff8005f 0x4bfff8007ffff000

def z892 : W := mkw 0xbffc4223def00000 0x437ff88447bde000 0xfffffffffff8007f 0xfbfffffffffff000

def z893 : W := mkw 0x4003fff0210ffffc 0x2c8007ffe0421fff 0x0003fff00007ffa0 0xb40007ffe0000fff

def z894 : W := mkw 0x113863380b5b16a4 0x142270c67016b62d 0x333ee73c1fff1ffb 0xfc667dce783ffe3f

def z895 : W := mkw 0xbffc4223def00000 0x437ff88447bde000 0xfffce033fff8005f 0x6bfff9c067fff000

def z896 : W := mkw 0xbba846a8c6300000 0x5377508d518c6000 0xf3000700e7380002 0x4be6000e01ce7000

def z897 : W := mkw 0xfbabf7a8a71f9264 0x37f757ef514e3f24 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z898 : W := mkw 0x4003b580210f9268 0x2880076b00421f24 0x0002e70000070000 0x800005ce00000e00

def z899 : W := mkw 0xaecc0003d4a00000 0x435d980007a94000 0xffcc0003fff8005f 0x4bff980007fff000

def z900 : W := mkw 0x6c03bc8ab506d840 0x32d80779156a0db0 0xfc03f8cfff07fc6f 0xeff807f19ffe0ff8

def z901 : W := mkw 0xfbabd6a802100000 0x13f757ad50042000 0xfffffffc0738003f 0xfbfffffff80e7000

def z902 : W := mkw 0xbfbc0002de700000 0x437f780005bce000 0xfffc0000ff38001f 0x4bfff80001fe7000

def z903 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xf3fc0003fff80052 0x4be7f80007fff000

def z904 : W := mkw 0xbfbc0816de704c82 0x437f78102dbce099 0xff3c183cff381c0a 0x6bfe783079fe7038

def z905 : W := mkw 0xaec00843d4a06910 0x035d801087a940d2 0xffc118c3fff8ffff 0x7fff823187fff1ff

def z906 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3300000e738001b 0x4be6600001ce7000

def z907 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x3cfff8ff18c0ffff 0xf479fff1fe3181ff

def z908 : W := mkw 0x82c0014160ada338 0x0905800282c15b46 0xc3c20703e0ffe3f7 0x9f87840e07c1ffc7

def z909 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18fc18c0ffb8 0x3419fa31f83181ff

def z910 : W := mkw 0xbffc0817def04c82 0x437ff8102fbde099 0xfffd18fffff81c7f 0x7bfffa31fffff038

def z911 : W := mkw 0xfbabd6a842300000 0x53f757ad50846000 0xfffffffc0038003f 0xf3fffffff8007000

def z912 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffe0003ffff007f 0xcffffc0007fffe00

def z913 : W := mkw 0x93fc47f14af927bc 0x4d27f88fe295f24f 0x03fc07f000f80390 0x1007f80fe001f007

def z914 : W := mkw 0x40032dc0210ffb78 0x2880065b80421ff6 0x000307c00007ffa0 0x9400060f80000fff

def z915 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xf3c307c3ffffe3ff 0xdfe7860f87ffffc7

def z916 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xf002e003ff07fc6b 0xefe005c007fe0ff8

def z917 : W := mkw 0xbbf800014af00000 0x0377f0000295e000 0xfffc0003fff8005f 0x4bfff80007fff000

def z918 : W := mkw 0xbffc0043def02110 0x437ff80087bde042 0xfffc0003fff8e3df 0x4ffff80007fff1c7

def z919 : W := mkw 0x86d40003def00000 0x410da80007bde000 0xc3000003fff80042 0x0b86000007fff000

def z920 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc00f8007f 0xfbfffffff801f000

def z921 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xf3c00003fff80057 0x4be7800007fff000

def z922 : W := mkw 0x2c540857def06d92 0x4258a810afbde0db 0xfc011803fff8ffef 0x6ff8023007fff1ff

def z923 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffc00fffff8ffdf 0x5ffff801fffff1ff

def z924 : W := mkw 0xea8bd6a800000000 0x13d517ad50000000 0xccfffffc0000003d 0xb399fffff8000000

def z925 : W := mkw 0xbffc0803def04800 0x437ff81007bde090 0xfffc1803fff81c5f 0x6bfff83007fff038

def z926 : W := mkw 0xc2c3010160ad8220 0x0185860202c15b04 0xc3c30703e0ffe3f7 0x9f87860e07c1ffc7

def z927 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3000000e7f80053 0x4be6000001cff000

def z928 : W := mkw 0x04540003def00000 0x4008a80007bde000 0xc0000003fff80047 0x0b80000007fff000

def z929 : W := mkw 0x86c00003d4a00000 0x010d800007a94000 0xc3c00003fff80057 0x0b87800007fff000

def z930 : W := mkw 0x82c00001c6b00000 0x41058000038d6000 0xc3c00003e7f80057 0x0b87800007cff000

def z931 : W := mkw 0x04542957bfdffff6 0x2408a852af7fbfff 0x00000003ffffffc0 0x0c00000007ffffff

def z932 : W := mkw 0xbba8d6a800000000 0x137751ad50000000 0x3ffdfffc0000003d 0x707ffbfff8000000

def z933 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc01f803ff07fc4c 0x6ff803f007fe0ff8

def z934 : W := mkw 0xbbfc0001cef00000 0x4377f800039de000 0xf3fc0000fff8005b 0x4be7f80001fff000

def z935 : W := mkw 0xbfec0847d6b06912 0x437fd8108fad60d2 0xffcd18cfe738e006 0x4bff9a319fce71c0

def z936 : W := mkw 0x28000000c6300000 0x42500000018c6000 0xf0000000e7380002 0x4be0000001ce7000

def z937 : W := mkw 0xfbabf7a8633f922c 0x1ff757ef50c67f24 0xf302e700e73f0002 0xcbe605ce01ce7e00

def z938 : W := mkw 0x3d7c0003def00000 0x427af80007bde000 0xfc3c0003fff8004f 0x4bf8780007fff000

def z939 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x33fee7fc1fff1ffb 0xfc67fdcff83ffe3f

def z940 : W := mkw 0x4003f320210f9264 0x248007e640421f24 0x0002e70000070000 0x800005ce00000e00

def z941 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3fc0000e7380012 0x4be7f80001ce7000

def z942 : W := mkw 0x2c00b802b506d840 0x22580170056a0db0 0xfc00f803ff07fc4f 0x6ff801f007fe0ff8

def z943 : W := mkw 0xbfa80002d6300000 0x437f500005ac6000 0xfffc0003ff38005f 0x4bfff80007fe7000

def z944 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffd0003fff8e07f 0x4ffffa0007fff1c0

def z945 : W := mkw 0xbffcd22bdef00000 0x537ff9a457bde000 0xfffce003fff8005f 0x4bfff9c007fff000

def z946 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xff3c0003fff8004a 0x4bfe780007fff000

def z947 : W := mkw 0x2c000002d6300000 0x4258000005ac6000 0xfc000003ff38004f 0x4bf8000007fe7000

def z948 : W := mkw 0xbfbc0002de700000 0x437f780005bce000 0xf3000000ff380002 0x4be6000001fe7000

def z949 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f803ff07fc46 0xcff807f007fe0ff8

def z950 : W := mkw 0xbbf80001cef00000 0x4377f000039de000 0xf3f00003fff8005f 0x4be7e00007fff000

def z951 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3302e7001fff1feb 0xec6605ce003ffe3f

def z952 : W := mkw 0x0400085610006d92 0x00080010ac2000db 0x0cfd18ff1800fffd 0x3419fa31fe3001ff

def z953 : W := mkw 0xbbb80000ce700000 0x43777000019ce000 0xfffc0000fff8005f 0x4bfff80001fff000

def z954 : W := mkw 0x2c540003def00000 0x4258a80007bde000 0xf0000003fff80042 0x4be0000007fff000

def z955 : W := mkw 0xbffc0013def00480 0x437ff80027bde009 0xfffd18fffff81fff 0x7ffffa31fffff03f

def z956 : W := mkw 0xbffc46abdef00000 0x537ff88d57bde000 0xfffee7fffff8007f 0xfbfffdcffffff000

def z957 : W := mkw 0x2c1000029e500000 0x02582000053ca000 0xfc000003fff8004f 0x4bf8000007fff000

def z958 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc00000016 0xd3fffffff8000000

def z959 : W := mkw 0xbfa80802d6304800 0x437f501005ac6090 0xff011803ff38fc6f 0x6ffe023007fe71f8

def z960 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfcc3f8c3ff07fc7f 0xfff987f187fe0ff8

def z961 : W := mkw 0xbfec0003d6b00000 0x437fd80007ad6000 0xf3000003e7380002 0x4be6000007ce7000

def z962 : W := mkw 0xbffc0057def02592 0x437ff800afbde04b 0xfffd18fffff803ff 0x7bfffa31fffff007

def z963 : W := mkw 0x82800000c6300000 0x41050000018c6000 0xc3000000e7380002 0x0b86000001ce7000

def z964 : W := mkw 0xbff00003def00000 0x037fe00007bde000 0xfff00003fff8005f 0x4bffe00007fff000

def z965 : W := mkw 0xaedc0003def00000 0x435db80007bde000 0xcfcc0003fff80057 0x0b9f980007fff000

def z966 : W := mkw 0xbffc4223def00000 0x437ff88447bde000 0xfffee703fff8005f 0xcbfffdce07fff000

def z967 : W := mkw 0xbbfc0055cef02592 0x4377f800ab9de04b 0xf3fc00fce7f80392 0x5be7f801f9cff007

def z968 : W := mkw 0x04540857dce06d92 0x4008a810afb9c0db 0x0cfd18fff8c0fffd 0x3419fa31fff181ff

def z969 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3c00000e7380017 0x4be7800001ce7000

def z970 : W := mkw 0x44576ff739cfffbe 0x0c88aedfee739fff 0x0cffffff18c7fffd 0xb419fffffe318fff

def z971 : W := mkw 0x4413fb32394fdee4 0x248827f664729fbd 0x0c33ff3318c7fffd 0xb41867fe66318fff

def z972 : W := mkw 0xbffc0843def06910 0x437ff81087bde0d2 0xfffd18c3fff8ffff 0x7ffffa3187fff1ff

def z973 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f803ff07fc2c 0xe7f807f007fe0ff8

def z974 : W := mkw 0x4003b900210fda60 0x2080077200421fb4 0x0003ff000007ffa0 0xb40007fe00000fff

def z975 : W := mkw 0x82c0014140a92330 0x0105800282815246 0xc3c307c3e0ffe3f7 0x9f87860f87c1ffc7

def z976 : W := mkw 0xbffc4a77def06d92 0x437ff894efbde0db 0xfffffffffff8ffff 0xfffffffffffff1ff

def z977 : W := mkw 0x4003ffb8210fdee4 0x348007ff70421fbd 0x0003fffc0007ffa0 0xb40007fff8000fff

def z978 : W := mkw 0xbffc0847def06912 0x437ff8108fbde0d2 0xfffc0003fff8e05f 0x4bfff80007fff1c0

def z979 : W := mkw 0x4003fb20210fda64 0x248007f640421fb4 0x0003ff000007fc20 0xa40007fe00000ff8

def z980 : W := mkw 0x6c07b806b506d842 0x22d80f700d6a0db0 0xfc0ff80fff07fc6f 0xeff81ff01ffe0ff8

def z981 : W := mkw 0x2c00280295025800 0x02580050052a04b0 0xfc03f803ff07fc6f 0xeff807f007fe0ff8

def z982 : W := mkw 0xbfa80002d6300000 0x437f500005ac6000 0xff000003e7380006 0x4bfe000007ce7000

def z983 : W := mkw 0xbffc0053def02590 0x437ff800a7bde04b 0xfffd00f3fff8ffff 0x7ffffa01e7fff1ff

def z984 : W := mkw 0x2c540003def00000 0x4258a80007bde000 0xcc000003fff80044 0x0b98000007fff000

def z985 : W := mkw 0xbbb80000ce700000 0x43777000019ce000 0xf3300000ff38000a 0x4be6600001fe7000

def z986 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c307c3f8ffffff 0xbf87860f87f1ffff

def z987 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc03f8ffff07fc6f 0xfff807f1fffe0ff8

def z988 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xcffffffc00000034 0xb39ffffff8000000

def z989 : W := mkw 0x0444085710806d92 0x00088810ae2100db 0x0cfd18ff0000ffbd 0x3419fa31fe0001ff

def z990 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x33f3e7f01fff1fff 0xfc67e7cfe03ffe3f

def z991 : W := mkw 0x045408579ed06d92 0x4008a810af3da0db 0x0cfd18ff1fc0fffd 0x3419fa31fe3f81ff

def z992 : W := mkw 0x0010085408406d92 0x00002010a81080db 0x0cfd18fc18c0fffd 0x3419fa31f83181ff

def z993 : W := mkw 0x00102110094b16a0 0x000020422012962d 0x3332e7301fff1ffb 0xfc6665ce603ffe3f

def z994 : W := mkw 0xfbabd6a886100000 0x53f757ad510c2000 0xfffffffc0700003f 0xf3fffffff80e0000

def z995 : W := mkw 0xbffc0847def06912 0x437ff8108fbde0d2 0xfffd18cffff8e3ff 0x5ffffa319ffff1c7

def z996 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0x3ffffffc00000038 0xf07ffffff8000000

def z997 : W := mkw 0x97fc0003def00000 0x412ff80007bde000 0xc3fc0003fff80057 0x0b87f80007fff000

def z998 : W := mkw 0xc2c395c160ada338 0x0985872b82c15b46 0xc3c3ffc3e0ffe3f7 0xbf8787ff87c1ffc7

def z999 : W := mkw 0x3d20000296100000 0x027a4000052c2000 0xff000003ff38004f 0x4bfe000007fe7000

def z1000 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7301fff1fd2 0xdc6665ce603ffe3f

def z1001 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c207c3e0ffe3d2 0x9f87840f87c1ffc7

def z1002 : W := mkw 0xaedc0003def00000 0x435db80007bde000 0xccfc0003fff8005d 0x0b99f80007fff000

def z1003 : W := mkw 0x86d40857def06d92 0x410da810afbde0db 0xc3c100c3fff8fff7 0x1f87820187fff1ff

def z1004 : W := mkw 0xbfa80002d6300000 0x437f500005ac6000 0xf3000003ff380042 0x4be6000007fe7000

def z1005 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc1f00007f 0xfbfffffff83e0000

def z1006 : W := mkw 0x82c0000140a00000 0x0105800002814000 0xf3c00003fff8005f 0x4be7800007fff000

def z1007 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfc33f833ff07fc7f 0xfff867f067fe0ff8

def z1008 : W := mkw 0xd3a346a000000000 0x01a7468d40000000 0xfffffffc0000003f 0xf3fffffff8000000

def z1009 : W := mkw 0x11206320031b1224 0x042240c640063624 0x3302e7001fff1ffb 0xfc6605ce003ffe3f

def z1010 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xf3c3e7c3e0ffe3ff 0xffe787cf87c1ffc7

def z1011 : W := mkw 0xbffc0057def02592 0x437ff800afbde04b 0xfffd00fffff8e3ff 0x5ffffa01fffff1c7

def z1012 : W := mkw 0x4003fb74210ffff6 0x248007f6e8421fff 0x0003fffc0007ffa0 0xb40007fff8000fff

def z1013 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffd1803fff8007f 0x6bfffa3007fff000

def z1014 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xcfc31fc3e0ffe3ff 0xbf9f863f87c1ffc7

def z1015 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c307c3e0ffe3b4 0x9787860f87c1ffc7

def z1016 : W := mkw 0xbffc0813def04c80 0x437ff81027bde099 0xfffd1833fff8ffff 0x7ffffa3067fff1ff

def z1017 : W := mkw 0xbffc46abdef00000 0x537ff88d57bde000 0xfffd1ffffff8007f 0x7bfffa3ffffff000

def z1018 : W := mkw 0xaedc0857def06d92 0x435db810afbde0db 0xccfd18fffff8fffd 0x3f99fa31fffff1ff

def z1019 : W := mkw 0xbbb80000ce700000 0x43777000019ce000 0xf3000000fff80042 0x4be6000001fff000

def z1020 : W := mkw 0xbfec0003d6b00000 0x437fd80007ad6000 0xfffc0003e738001f 0x4bfff80007ce7000

def z1021 : W := mkw 0x3d3008129e504c80 0x027a6010253ca099 0xff311833fff8ffff 0x7ffe623067fff1ff

def z1022 : W := mkw 0x6c0fb802b506d840 0x62d81f70056a0db0 0xfc0ff803ff07fc6f 0xeff81ff007fe0ff8

def z1023 : W := mkw 0x86d40003def00000 0x410da80007bde000 0xc0c00003fff80044 0x0b81800007fff000

def z1024 : W := mkw 0xbffc0043def02110 0x437ff80087bde042 0xfffc00c3fff803df 0x5bfff80187fff007

def z1025 : W := mkw 0xbbfc0001cef00000 0x4377f800039de000 0xfffc0000e7f8001f 0x4bfff80001cff000

def z1026 : W := mkw 0x4003b5c0210fb378 0x2880076b80421f66 0x0003e7c00007e3a0 0x940007cf80000fc7

def z1027 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c20703e0ffe3d7 0x8f87840e07c1ffc7

def z1028 : W := mkw 0x0054085508c06d92 0x0000a810aa1180db 0x0cfd18fc00c0ffbd 0x3419fa31f80181ff

def z1029 : W := mkw 0xeec79cc7f4a4e95a 0x2bdd8f398fe949d2 0xcccd18cfe000e004 0x03999a319fc001c0

def z1030 : W := mkw 0xaed40003dce00000 0x035da80007b9c000 0xfffc0003fff8005f 0x4bfff80007fff000

def z1031 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xf003f803ff07fc62 0xefe007f007fe0ff8

def z1032 : W := mkw 0x4003f330210f96e4 0x248007e660421f2d 0x0002e73000071fa0 0xb40005ce60000e3f

def z1033 : W := mkw 0x4003bd80210fda68 0x2880077b00421fb4 0x0003ff000007fc20 0xa40007fe00000ff8

def z1034 : W := mkw 0xbffc9803def04840 0x637ff93007bde090 0xfffc1803fff8005f 0x4bfff83007fff000

def z1035 : W := mkw 0x93fc43754af927b6 0x4527f886ea95f24f 0x03fc07fc00f80390 0x1007f80ff801f007

def z1036 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3333e7331fffffff 0xfc6667ce663fffff

def z1037 : W := mkw 0x400325d0210fb7bc 0x0c80064ba0421f6f 0x000307c00007ffa0 0x9400060f80000fff

def z1038 : W := mkw 0xbffc0013def00480 0x437ff80027bde009 0xfffc0003fff81fdf 0x4ffff80007fff03f

def z1039 : W := mkw 0xaed40857dce06d92 0x035da810afb9c0db 0xfffd18fffff8ffff 0x7ffffa31fffff1ff

def z1040 : W := mkw 0xbfec0003d6b00000 0x437fd80007ad6000 0xffcc0003e7f80057 0x4bff980007cff000

def z1041 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xf3000000ff38004b 0x4be6000001fe7000

def z1042 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffffffc0007007f 0xfffffffff8000e00

def z1043 : W := mkw 0x113c63300b5b16a4 0x442278c66016b62d 0x333ee7301fff1ffb 0xfc667dce603ffe3f

def z1044 : W := mkw 0xbffc0483def00000 0x437ff80907bde000 0xfffc07c3fff8005f 0x5bfff80f87fff000

def z1045 : W := mkw 0x40430141208da330 0x0080860282411b46 0xc3c307c3e0ffe3f7 0x9f87860f87c1ffc7

def z1046 : W := mkw 0xbba8d6a800000000 0x137751ad50000000 0xfffcfffc0000001f 0x73fff9fff8000000

def z1047 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3020703e0ffe3f3 0x9f86040e07c1ffc7

def z1048 : W := mkw 0xbffc900bdef00000 0x537ff92017bde000 0xfffc180ffff8005f 0x4bfff8301ffff000

def z1049 : W := mkw 0xbba8d228c6300000 0x537751a4518c6000 0xf300e000e7380002 0x4be601c001ce7000

def z1050 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffd00c3fff8007f 0x5bfffa0187fff000

def z1051 : W := mkw 0x045429577bffffbe 0x0c08a852aef7ffff 0x00000003ffffffc0 0x0c00000007ffffff

def z1052 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfffdfffc0000001c 0x73fffbfff8000000

def z1053 : W := mkw 0x2c00000294000000 0x0258000005280000 0xff000003fff8005f 0x4bfe000007fff000

def z1054 : W := mkw 0xbffc9003def00000 0x437ff92007bde000 0xfffcf803fff8005f 0x6bfff9f007fff000

def z1055 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0003fff81c7f 0x6ffff80007fff038

def z1056 : W := mkw 0xbba846a8c6300000 0x5377508d518c6000 0xf3fc07fce7380012 0x5be7f80ff9ce7000

def z1057 : W := mkw 0x2c002802b506d840 0x22580050056a0db0 0xfc02e003ff07fc6f 0xeff805c007fe0ff8

def z1058 : W := mkw 0xaedc0857def06d92 0x435db810afbde0db 0xcccd18cffff8ffc4 0x0f999a319ffff1ff

def z1059 : W := mkw 0x400305c0200da338 0x0880060b80401b46 0xc30307c3e0ffe3f7 0x9f86060f87c1ffc7

def z1060 : W := mkw 0x44032802b506d840 0x20880650056a0db0 0xf003e003ff07fc6f 0xefe007c007fe0ff8

def z1061 : W := mkw 0x93a846a800000000 0x1127508d50000000 0x3ffffffc0000003f 0xf07ffffff8000000

def z1062 : W := mkw 0x400325c0210fb338 0x0880064b80421f66 0x0003e7c00007ffa0 0xb40007cf80000fff

def z1063 : W := mkw 0xbffc0013def00480 0x437ff80027bde009 0xfffc0033fff803df 0x5bfff80067fff007

def z1064 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffd18fffff8fc5f 0x6bfffa31fffff1f8

def z1065 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0000fff8001a 0x4bfff80001fff000

def z1066 : W := mkw 0xc2cb05c960ada338 0x1985960b92c15b46 0xc3cf07cfe0ffe3f7 0x9f879e0f9fc1ffc7

def z1067 : W := mkw 0xfbabd6a820048000 0x13f757ad50400900 0xfffffffce007003f 0xfbfffffff9c00e00

def z1068 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cfd18ff18c0ffd4 0x1419fa31fe3181ff

def z1069 : W := mkw 0x4003bdd4210ffffa 0x2880077ba8421fff 0x0003fffc0007ffa0 0xb40007fff8000fff

def z1070 : W := mkw 0x6c0bb80ab506d840 0x32d81770156a0db0 0xfc0ff80fff07fc6f 0xeff81ff01ffe0ff8

def z1071 : W := mkw 0xbba84220c6300000 0x43775084418c6000 0xf302e700e7380002 0xcbe605ce01ce7000

def z1072 : W := mkw 0x11206320010b1220 0x002240c640021624 0x3332e7301fff1ffb 0xfc6665ce603ffe3f

def z1073 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffd18cffff8005f 0x4bfffa319ffff000

def z1074 : W := mkw 0x93f847f94af927bc 0x1d27f08ff295f24f 0x03fc07fc00f80390 0x1007f80ff801f007

def z1075 : W := mkw 0x4003b940210ffb78 0x2880077280421ff6 0x0003f8000007ffa0 0xa40007f000000fff

def z1076 : W := mkw 0xbfac0002d6300000 0x437f580005ac6000 0xff0c0000e7380002 0x4bfe180001ce7000

def z1077 : W := mkw 0xbfe80003d4a00000 0x037fd00007a94000 0xfffc0003fff8005f 0x4bfff80007fff000

def z1078 : W := mkw 0xbbe80001c6b00000 0x4377d000038d6000 0xfffc0003e7f8005f 0x4bfff80007cff000

def z1079 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0033fff8007f 0x7bfff80067fff000

def z1080 : W := mkw 0x405367f129cfb7bc 0x0c80a6cfe2539f6f 0x00f3e7f318c7fffd 0xb401e7cfe6318fff

def z1081 : W := mkw 0xbbfc0001cef00000 0x4377f800039de000 0xf3000000e7f80002 0x4be6000001cff000

def z1082 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xff000003fff8004f 0x4bfe000007fff000

def z1083 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3ffee7301fff1fff 0xfc7ffdce603ffe3f

def z1084 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3332e7301fff1fca 0xec6665ce603ffe3f

def z1085 : W := mkw 0x93b000004a700000 0x012760000094e000 0xf3300000fff8005b 0x4be6600001fff000

def z1086 : W := mkw 0x001021100b5b16a4 0x040020422016b62d 0x3302e7001fff1ffb 0xfc6605ce003ffe3f

def z1087 : W := mkw 0x97f400035af00000 0x012fe80006b5e000 0xfffc0003fff8005f 0x4bfff80007fff000

def z1088 : W := mkw 0xbffc0803def04800 0x437ff81007bde090 0xfffd18fffff8fc7f 0x7ffffa31fffff1f8

def z1089 : W := mkw 0x6803b000a5069040 0x22d00760014a0d20 0xf003e003ff07fc6f 0xefe007c007fe0ff8

def z1090 : W := mkw 0xaed40003def00000 0x435da80007bde000 0xffc00003fff8005f 0x4bff800007fff000

def z1091 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xcfff07c3e0ffe3ff 0x9f9ffe0f87c1ffc7

def z1092 : W := mkw 0x400367a0210f922c 0x0c8006cf40421f24 0x0002e70000070000 0x800005ce00000e00

def z1093 : W := mkw 0x97f408575af06d92 0x012fe810aeb5e0db 0xfffd18fffff8ffff 0x7ffffa31fffff1ff

def z1094 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc0003ff38000e 0x4bfff80007fe7000

def z1095 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xfffc183ffff8005f 0x6bfff8307ffff000

def z1096 : W := mkw 0xbbb80010ce700480 0x43777000219ce009 0xf3300030fff81ffb 0x7fe6600061fff03f

def z1097 : W := mkw 0xbffc0043def02110 0x437ff80087bde042 0xfffd00c3fff8e05f 0x4bfffa0187fff1c0

def z1098 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xc3c307c3e0ffe396 0x9b87860f87c1ffc7

def z1099 : W := mkw 0xaac00001c4a00000 0x0355800003894000 0xf3c00003e7f80057 0x4be7800007cff000

def z1100 : W := mkw 0xbffc0817def04c82 0x437ff8102fbde099 0xfffc0003fff81c5f 0x4bfff80007fff038

def z1101 : W := mkw 0xbffc0857def06d92 0x437ff810afbde0db 0xfffd1803fff8ffff 0x6ffffa3007fff1ff

def z1102 : W := mkw 0x3d7400039ed00000 0x027ae800073da000 0xfffc0003fff8005f 0x4bfff80007fff000

def z1103 : W := mkw 0x4043014160ada338 0x0880860282c15b46 0xc3030703e0ffe3f7 0x9f86060e07c1ffc7

def z1104 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xff3c0000e738000a 0x4bfe780001ce7000

def z1105 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x3cfd18ff1fc0ffff 0x7c79fa31fe3f81ff

def z1106 : W := mkw 0x0454085718c06d92 0x0008a810ae3180db 0x0cff18ff18c7ffff 0xbc19fe31fe318fff

def z1107 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xfccff8cfff07fc6f 0xeff99ff19ffe0ff8

def z1108 : W := mkw 0x4003b8002106d840 0x2080077000420db0 0xf003f803ff07fc6f 0xefe007f007fe0ff8

def z1109 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0xf332e733ffff1fff 0xffe665ce67fffe3f

def z1110 : W := mkw 0xbffc0057def02592 0x437ff800afbde04b 0xfffc00fffff81fff 0x7ffff801fffff03f

def z1111 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xffffffffe000007f 0xfbffffffffc00000

def z1112 : W := mkw 0x400367e0210fb33c 0x0c8006cfc0421f66 0x0003e7c00007e3a0 0x940007cf80000fc7

def z1113 : W := mkw 0xc2c305c160ada338 0x0985860b82c15b46 0xcfcf1fcfe0ffe3f7 0x9f9f9e3f9fc1ffc7

def z1114 : W := mkw 0x6c03bc82b506d840 0x22d80779056a0db0 0xfc03ffc3ff07fc6f 0xfff807ff87fe0ff8

def z1115 : W := mkw 0xbffc0003def00000 0x437ff80007bde000 0xffcc0003fff80046 0x4bff980007fff000

def z1116 : W := mkw 0x97f40003def00000 0x412fe80007bde000 0xf3f00003fff8005f 0x4be7e00007fff000

def z1117 : W := mkw 0x6c03b802b506d840 0x22d80770056a0db0 0xf003e003ff07fc67 0xcfe007c007fe0ff8

def z1118 : W := mkw 0xbba80000c6300000 0x43775000018c6000 0xff000000e738000f 0x4bfe000001ce7000

def z1119 : W := mkw 0xfbabd6a800000000 0x13f757ad50000000 0xfcfffffc0000002c 0xf3f9fffff8000000

def z1120 : W := mkw 0xbbe80001c6b00000 0x4377d000038d6000 0xf3000003e7f80042 0x4be6000007cff000

def z1121 : W := mkw 0xbbe80041c6b02110 0x4377d000838d6042 0xf3c100c3e7f8e3f7 0x5fe7820187cff1c7

def z1122 : W := mkw 0xbba84220c6300000 0x43775084418c6000 0xf332e730e738003b 0xfbe665ce61ce7000

def z1123 : W := mkw 0xaa800000c4200000 0x0355000001884000 0xf3000000e7380002 0x4be6000001ce7000

def z1124 : W := mkw 0xbfb800029e500000 0x037f7000053ca000 0xfffc0003fff8005f 0x4bfff80007fff000

def z1125 : W := mkw 0x113063300b5b16a4 0x042260c66016b62d 0x3333fffc1fff1ffb 0xfc6667fff83ffe3f

def z1126 : W := mkw 0xae800002d4200000 0x035d000005a84000 0xff000003ff38004f 0x4bfe000007fe7000

def z1127 : W := mkw 0xbfe80003d6b00000 0x437fd00007ad6000 0xffc00003fff8005f 0x4bff800007fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z6,z8]),(0,[z0,z9,z1,z2,z10,z5,z6]),(0,[z0,z11,z2,z10,z5,z6,z12]),(0,[z0,z1,z13,z2,z10,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z14]),(0,[z0,z1,z2,z15,z10,z5,z6]),(0,[z16,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z17]),(0,[z18,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z19,z10,z5,z6]),(0,[z0,z1,z2,z20,z10,z5,z6]),(0,[z0,z1,z21,z2,z10,z22,z6])],[(0,[z23,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z24]),(0,[z25,z0,z1,z2,z4,z5,z6]),(0,[z26,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z27,z5,z6]),(0,[z0,z1,z2,z28,z10,z5,z6])],[(0,[z0,z1,z29,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z4,z5,z6]),(0,[z0,z1,z2,z7,z30,z5,z6]),(0,[z0,z1,z2,z7,z5,z31,z6]),(0,[z0,z32,z1,z2,z10,z5,z6]),(0,[z33,z0,z1,z2,z10,z5,z6])],[(0,[z34,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z35,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z22,z6])],[(1,[z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z37,z2,z10,z5,z6]),(0,[z38,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z39,z10,z5,z6]),(0,[z0,z40,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z41,z10,z5,z6])],[(0,[z0,z1,z42,z2,z10,z5,z6]),(0,[z0,z1,z43,z2,z10,z5,z6]),(0,[z0,z9,z1,z2,z4,z5,z6]),(0,[z0,z1,z13,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z6,z12]),(0,[z0,z44,z1,z45,z10,z5,z6]),(0,[z0,z44,z1,z29,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z46,z6]),(0,[z0,z1,z2,z15,z4,z5,z6]),(0,[z47,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z48,z10,z5,z6]),(0,[z0,z1,z49,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z50,z6]),(1,[z0,z1,z2,z51,z10,z5]),(0,[z0,z1,z3,z10,z5,z22,z6]),(0,[z0,z52,z1,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z53,z2,z10,z5,z6])],[(0,[z0,z1,z1,z2,z10,z5,z6]),(0,[z0,z1,z54,z2,z7,z5,z6]),(0,[z55,z56,z1,z2,z10,z5,z6]),(0,[z57,z0,z1,z29,z10,z5,z6]),(0,[z57,z0,z1,z45,z10,z5,z6]),(0,[z58,z0,z1,z59,z2,z5,z6]),(0,[z0,z1,z60,z2,z5,z6,z61]),(0,[z0,z1,z2,z10,z5,z6,z62])],[(1,[z63,z64,z2,z10,z5,z6]),(0,[z65,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z66]),(1,[z0,z1,z2,z67,z5,z6]),(0,[z0,z1,z68,z2,z10,z5,z6])],[(0,[z69,z0,z1,z2,z10,z5,z6]),(0,[z1,z70,z2,z71,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z72]),(0,[z0,z1,z2,z10,z5,z6,z73]),(0,[z0,z1,z74,z2,z10,z5,z6])],[(0,[z0,z75,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z76,z7,z5,z6]),(0,[z25,z0,z1,z2,z10,z5,z77])],[(0,[z0,z1,z2,z10,z5,z78,z6]),(0,[z0,z1,z2,z10,z79,z5,z6]),(0,[z0,z1,z2,z7,z80,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z81]),(0,[z0,z1,z82,z2,z10,z5,z6])],[(0,[z0,z1,z83,z2,z10,z5,z6]),(0,[z0,z1,z84,z2,z45,z10,z6]),(0,[z0,z1,z85,z2,z10,z5,z6])],[(0,[z86,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z87,z10,z5,z6]),(0,[z0,z1,z88,z2,z10,z5,z6]),(0,[z89,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z90,z6])]],
   [[(0,[z91,z0,z1,z2,z7,z5,z6]),(0,[z0,z92,z1,z2,z10,z5,z6])],[(0,[z69,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z93,z10,z5,z6]),(0,[z94,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z59,z2,z5,z6,z95]),(0,[z0,z1,z2,z10,z5,z6,z96]),(0,[z0,z1,z97,z2,z98,z5,z6])],[(1,[z0,z1,z2,z99,z5,z6]),(0,[z0,z1,z70,z2,z10,z5,z6]),(0,[z100,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z101,z2,z10,z5,z6]),(0,[z0,z1,z102,z10,z5,z6,z103])],[(0,[z0,z1,z2,z104,z10,z5,z6]),(0,[z105,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z106,z2,z10,z5,z6]),(0,[z0,z1,z107,z2,z10,z5,z6])],[(0,[z108,z0,z1,z2,z10,z5,z6]),(1,[z109,z1,z2,z10,z5,z110]),(0,[z0,z29,z2,z10,z111,z5,z6]),(0,[z112,z0,z2,z10,z5,z31,z6]),(0,[z0,z1,z2,z113,z10,z5,z6]),(0,[z0,z1,z2,z10,z114,z5,z6]),(0,[z0,z1,z2,z115,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z116]),(0,[z0,z1,z2,z4,z5,z77,z6]),(0,[z112,z0,z9,z2,z10,z5,z6]),(0,[z0,z1,z117,z2,z118,z5,z6])],[(0,[z0,z1,z71,z10,z5,z6,z103]),(0,[z94,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z95]),(0,[z25,z0,z1,z13,z2,z10,z5]),(0,[z119,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z120,z10,z5,z6]),(0,[z0,z121,z1,z2,z10,z5,z6]),(0,[z0,z1,z122,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z10,z123,z5,z6]),(0,[z0,z1,z70,z2,z4,z5,z6]),(0,[z0,z1,z124,z2,z10,z5,z6]),(0,[z0,z1,z125,z2,z10,z5,z6]),(0,[z0,z1,z21,z126,z10,z5,z6]),(0,[z0,z127,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z128,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z129,z6]),(0,[z130,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z131,z5,z6]),(0,[z0,z1,z2,z132,z10,z5,z6]),(0,[z0,z133,z1,z2,z118,z5,z6]),(0,[z0,z134,z1,z2,z10,z5,z6]),(0,[z16,z0,z1,z59,z2,z5,z6])],[(0,[z0,z1,z2,z10,z135,z5,z6])],[(0,[z136,z0,z1,z2,z10,z137,z6]),(1,[z0,z1,z138,z5,z6,z139])],[(0,[z0,z9,z1,z21,z2,z10,z6])],[(0,[z0,z1,z2,z10,z140,z5,z6])],[(0,[z0,z1,z2,z10,z141,z5,z6]),(0,[z91,z0,z1,z2,z142,z5,z6]),(0,[z143,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z124,z2,z4,z5,z6]),(0,[z0,z1,z21,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z144,z6]),(0,[z0,z145,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z146,z6])],[(0,[z0,z1,z2,z10,z5,z147,z6]),(0,[z148,z0,z1,z2,z10,z5,z6]),(0,[z149,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z150,z2,z45,z10,z6]),(0,[z0,z1,z2,z51,z10,z5,z6])]],
   [[(0,[z0,z1,z151,z2,z7,z5,z6]),(0,[z0,z133,z2,z10,z152,z5,z6]),(0,[z153,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z154,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z155,z6]),(0,[z0,z1,z2,z156,z7,z5,z6]),(0,[z157,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z158,z6])],[(0,[z0,z1,z2,z10,z159,z5,z6]),(0,[z0,z1,z2,z7,z5,z6,z95]),(0,[z25,z0,z1,z2,z10,z5,z61]),(1,[z160,z0,z2,z10,z5,z161])],[(0,[z0,z1,z2,z71,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z162])],[(0,[z0,z1,z2,z4,z5,z137,z6]),(0,[z0,z1,z2,z10,z5,z6,z163]),(0,[z164,z0,z1,z2,z10,z5,z6]),(0,[z94,z0,z1,z156,z10,z5,z6])],[(0,[z165,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z166,z2,z10,z5,z6]),(0,[z112,z0,z1,z126,z2,z10,z6])],[(0,[z160,z0,z75,z2,z10,z5,z6]),(0,[z0,z1,z2,z167,z10,z5,z6]),(1,[z130,z1,z2,z7,z5,z6]),(0,[z168,z0,z1,z2,z10,z5,z6]),(0,[z169,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z170,z2,z10,z5,z6]),(0,[z0,z1,z171,z2,z10,z5,z6])],[(0,[z100,z0,z1,z71,z10,z5,z6]),(0,[z56,z0,z1,z2,z10,z137,z6]),(0,[z0,z1,z172,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z173]),(0,[z0,z1,z2,z10,z5,z6,z174]),(0,[z0,z1,z175,z2,z10,z5,z6]),(1,[z32,z1,z2,z10,z5,z6])]],
   [[(0,[z0,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z138,z60,z10,z5,z6]),(0,[z0,z1,z176,z2,z10,z5,z6]),(0,[z0,z1,z2,z177,z10,z5,z6])],[(0,[z0,z1,z2,z10,z178,z5,z6]),(0,[z0,z1,z2,z10,z179,z5,z6]),(0,[z0,z1,z180,z2,z10,z5,z6]),(0,[z0,z1,z181,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z6]),(0,[z0,z1,z2,z45,z10,z5,z6]),(0,[z182,z0,z1,z2,z10,z5,z6])],[(0,[z160,z0,z11,z2,z10,z5,z6]),(0,[z183,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z184,z10,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z185,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z138,z10,z5,z6,z139])],[(1,[z0,z1,z84,z2,z10,z6]),(0,[z0,z133,z1,z2,z152,z5,z6])],[(0,[z0,z186,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z187,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z188]),(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z189,z10,z5,z6])],[(0,[z0,z1,z2,z45,z4,z5,z6]),(0,[z0,z1,z180,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z137,z6]),(1,[z0,z1,z2,z7,z5,z8]),(0,[z0,z1,z190,z2,z10,z5,z6]),(0,[z0,z1,z191,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z192,z10,z5,z6]),(0,[z0,z1,z193,z2,z10,z5,z6]),(1,[z0,z1,z194,z2,z5,z6]),(0,[z0,z1,z2,z10,z5,z195,z6]),(0,[z196,z0,z2,z10,z5,z22,z6])],[(0,[z0,z1,z64,z2,z7,z5,z6]),(0,[z197,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z198,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z199,z6])],[(0,[z0,z200,z1,z2,z10,z5,z6]),(0,[z100,z0,z1,z70,z10,z5,z6])],[(0,[z201,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z202,z10,z5,z6]),(0,[z0,z1,z203,z2,z10,z5,z6]),(1,[z0,z1,z204,z2,z5,z6]),(0,[z0,z1,z2,z10,z5,z205,z6])],[(1,[z69,z1,z70,z10,z5,z6]),(0,[z58,z0,z1,z2,z7,z5,z6]),(1,[z0,z9,z2,z10,z111,z6]),(0,[z0,z1,z204,z2,z10,z5,z6]),(0,[z0,z1,z206,z2,z10,z5,z6])],[(0,[z196,z0,z1,z2,z10,z5,z6]),(0,[z94,z0,z1,z2,z10,z5,z103]),(1,[z136,z0,z1,z97,z2,z10])],[(1,[z100,z1,z71,z10,z5,z6]),(1,[z0,z1,z2,z207,z5,z6]),(0,[z0,z1,z2,z10,z208,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z209]),(0,[z0,z1,z2,z10,z5,z210,z6]),(0,[z0,z11,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z211]),(0,[z0,z212,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z213,z6]),(0,[z0,z1,z198,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z214,z5,z6]),(0,[z94,z0,z1,z102,z10,z5,z6]),(1,[z0,z1,z2,z98,z5,z6])]],
   [[(0,[z215,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z216,z2,z10,z5,z6]),(0,[z0,z217,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z218,z5,z6])],[(0,[z0,z1,z2,z10,z5,z219,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z0,z1,z2,z220,z10,z5,z6])],[(0,[z0,z1,z2,z221,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z222]),(0,[z0,z1,z223,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z224,z6])],[(0,[z25,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z225,z2,z10,z5,z6]),(0,[z0,z1,z204,z2,z5,z22,z6])],[(0,[z0,z11,z1,z2,z4,z5,z6]),(0,[z0,z1,z29,z2,z7,z5,z6]),(0,[z226,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z227,z10,z5,z6]),(0,[z0,z1,z2,z228,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z229,z6]),(0,[z0,z1,z2,z118,z10,z5,z6])],[(0,[z0,z1,z2,z230,z10,z5,z6]),(0,[z0,z1,z2,z231,z10,z5,z6]),(0,[z0,z232,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z233]),(0,[z0,z1,z234,z2,z10,z5,z6])],[(0,[z235,z0,z1,z2,z10,z5,z6]),(0,[z236,z0,z1,z2,z10,z5,z6]),(0,[z0,z9,z1,z2,z7,z5,z6]),(0,[z0,z1,z237,z2,z10,z5,z6])]],
   [[(0,[z0,z238,z1,z2,z10,z5,z6]),(0,[z0,z239,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z240]),(0,[z0,z1,z2,z10,z241,z5,z6])],[(0,[z242,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z243,z5,z6]),(0,[z0,z244,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z245,z5,z6]),(0,[z0,z1,z2,z10,z241,z6,z72])],[(1,[z0,z246,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z247]),(0,[z0,z1,z2,z10,z5,z6,z248]),(0,[z0,z1,z2,z10,z5,z6,z249]),(0,[z0,z1,z2,z10,z5,z250,z6])],[(0,[z0,z1,z2,z118,z4,z5,z6]),(0,[z251,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z252,z2,z10,z5,z6])],[(0,[z0,z1,z253,z2,z10,z5,z6]),(0,[z0,z1,z37,z2,z7,z5,z6]),(0,[z0,z133,z1,z2,z254,z5,z6]),(0,[z0,z1,z2,z255,z10,z5,z6]),(0,[z136,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z256]),(0,[z0,z1,z2,z10,z257,z5,z6]),(0,[z0,z1,z258,z2,z10,z5,z6])],[(0,[z0,z1,z2,z7,z5,z6,z259]),(0,[z0,z1,z2,z10,z260,z5,z6]),(0,[z0,z133,z1,z60,z2,z5,z6]),(0,[z58,z0,z2,z254,z10,z5,z6]),(0,[z0,z1,z261,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z262])],[(0,[z0,z1,z2,z10,z5,z263,z6]),(0,[z0,z1,z2,z7,z152,z5,z6]),(0,[z0,z1,z2,z264,z10,z5,z6]),(0,[z265,z0,z1,z2,z10,z5,z6]),(0,[z16,z0,z1,z13,z2,z5,z6]),(0,[z0,z1,z2,z10,z5,z266,z6]),(0,[z0,z1,z2,z10,z267,z5,z6])]],
   [[(0,[z268,z0,z1,z2,z10,z5,z6]),(0,[z0,z269,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z270]),(0,[z0,z1,z2,z271,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z272]),(0,[z0,z1,z273,z2,z10,z5,z6])],[(0,[z0,z1,z274,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z142,z5,z6]),(0,[z0,z1,z2,z275,z10,z5,z6]),(0,[z69,z0,z1,z2,z7,z5,z6]),(0,[z136,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z276,z2,z7,z5,z6]),(0,[z0,z277,z1,z2,z10,z5,z6]),(0,[z0,z278,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z279,z6]),(0,[z0,z2,z254,z10,z152,z5,z6]),(0,[z0,z1,z2,z118,z10,z6,z95])],[(1,[z0,z1,z2,z280,z5,z6]),(0,[z0,z1,z2,z10,z5,z281,z6]),(0,[z0,z282,z1,z2,z10,z5,z6]),(0,[z69,z0,z1,z2,z283,z5,z6]),(0,[z284,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z285,z10,z5,z6]),(1,[z0,z1,z271,z10,z5,z6]),(0,[z25,z0,z1,z2,z10,z5,z110]),(0,[z0,z1,z286,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z287,z6])],[(0,[z63,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z288,z2,z10,z5,z6])],[(0,[z63,z0,z1,z2,z99,z5,z6]),(0,[z289,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z290,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z291]),(0,[z0,z1,z2,z10,z5,z6,z292]),(0,[z16,z0,z1,z138,z2,z5,z6]),(0,[z0,z1,z2,z10,z5,z293,z6]),(0,[z0,z1,z21,z3,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z103]),(0,[z0,z1,z2,z10,z5,z6,z294])],[(1,[z0,z1,z295,z10,z5,z6])],[(0,[z0,z296,z1,z64,z2,z10,z5]),(0,[z160,z25,z0,z1,z2,z10,z5]),(0,[z0,z1,z2,z10,z5,z6,z297]),(0,[z0,z1,z2,z10,z5,z6,z61])]],
   [[(0,[z0,z1,z2,z10,z298,z5,z6]),(0,[z94,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z7,z5,z6,z299]),(0,[z56,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z300]),(0,[z0,z1,z301,z2,z10,z5,z6]),(0,[z0,z1,z59,z60,z2,z5,z6]),(0,[z302,z0,z1,z2,z10,z5,z6])],[(0,[z0,z303,z1,z2,z10,z5,z6]),(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z285,z4,z5,z6]),(0,[z0,z1,z2,z304,z4,z5,z6]),(0,[z0,z305,z1,z2,z10,z5,z6]),(0,[z0,z1,z102,z2,z10,z5,z6])],[(0,[z306,z0,z1,z2,z10,z5,z6]),(0,[z109,z0,z246,z2,z10,z5,z6]),(0,[z307,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z308,z2,z45,z5,z6]),(0,[z0,z309,z1,z2,z10,z5,z6]),(0,[z0,z1,z13,z2,z5,z6,z61])],[(0,[z0,z1,z2,z280,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z310]),(0,[z0,z311,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z312,z5,z6])],[(0,[z130,z313,z1,z2,z10,z5,z6]),(0,[z314,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z315]),(0,[z0,z1,z2,z10,z5,z316,z6]),(0,[z0,z1,z117,z2,z10,z5,z6])],[(0,[z130,z0,z1,z2,z10,z5,z6]),(0,[z56,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z317,z10,z5,z6]),(0,[z0,z1,z2,z318,z10,z5,z6]),(1,[z16,z0,z1,z13,z2,z5])],[(0,[z0,z305,z1,z2,z4,z5,z6]),(0,[z0,z1,z102,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z5,z319,z6]),(0,[z0,z1,z138,z2,z76,z5,z6]),(0,[z0,z1,z320,z2,z10,z5,z6])]],
   [[(0,[z321,z0,z1,z2,z10,z5,z6]),(0,[z0,z322,z1,z2,z10,z5,z6]),(0,[z0,z133,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z323,z5,z6])],[(0,[z0,z1,z2,z7,z5,z6,z72]),(0,[z324,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z111,z5,z6]),(0,[z0,z1,z2,z156,z10,z5,z72]),(0,[z0,z1,z2,z10,z5,z325,z6])],[(0,[z0,z1,z308,z2,z10,z5,z6]),(1,[z0,z44,z29,z10,z5,z6]),(0,[z0,z1,z326,z2,z10,z5,z6]),(0,[z0,z1,z327,z2,z10,z5,z6]),(0,[z0,z1,z2,z254,z10,z5,z6]),(0,[z328,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z329,z2,z10,z5,z6]),(0,[z330,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z331,z2,z156,z5,z6])],[(0,[z0,z1,z117,z2,z4,z5,z6]),(0,[z109,z0,z1,z271,z10,z5,z6]),(0,[z0,z1,z2,z10,z332,z5,z6]),(0,[z0,z333,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z334]),(0,[z0,z1,z2,z10,z335,z5,z6]),(0,[z25,z0,z1,z2,z336,z5,z6]),(0,[z0,z1,z138,z2,z118,z5,z6]),(0,[z337,z0,z1,z2,z10,z5,z6])],[(0,[z0,z44,z29,z2,z10,z5,z6]),(1,[z0,z1,z2,z118,z6,z95])],[(0,[z69,z100,z1,z2,z10,z5,z6]),(0,[z0,z1,z338,z2,z10,z5,z6]),(0,[z0,z133,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z5,z339,z6]),(0,[z130,z1,z2,z7,z10,z5,z6]),(0,[z0,z1,z340,z2,z10,z5,z6]),(0,[z0,z1,z341,z2,z10,z5,z6])],[(0,[z69,z0,z1,z71,z10,z5,z6]),(0,[z0,z1,z2,z10,z137,z6,z72]),(1,[z0,z1,z2,z10,z342,z6]),(0,[z0,z1,z2,z10,z5,z6,z139])]],
   [[(0,[z0,z1,z2,z99,z10,z5,z6]),(0,[z343,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z254,z4,z5,z6]),(0,[z344,z0,z1,z2,z10,z5,z6]),(1,[z0,z1,z331,z2,z5,z6]),(0,[z0,z1,z59,z2,z118,z10,z6]),(0,[z0,z1,z2,z345,z10,z5,z6])],[(0,[z346,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z107,z2,z5,z31,z6]),(0,[z0,z1,z2,z98,z10,z5,z6])],[(0,[z0,z1,z2,z71,z7,z5,z6]),(0,[z0,z1,z2,z347,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z348,z6]),(0,[z0,z1,z59,z2,z10,z5,z6]),(0,[z0,z1,z117,z2,z10,z6,z95])],[(0,[z313,z1,z2,z10,z4,z5,z6]),(1,[z0,z133,z2,z152,z5,z6]),(0,[z0,z9,z1,z2,z10,z111,z6]),(0,[z349,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z7,z5,z77,z6]),(0,[z165,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z350,z10,z5,z6]),(0,[z351,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z352,z5,z6])],[(0,[z353,z0,z1,z2,z10,z5,z6]),(0,[z94,z0,z1,z71,z10,z5,z6]),(0,[z55,z0,z1,z2,z10,z137,z6]),(0,[z0,z1,z354,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z355,z6]),(0,[z356,z0,z1,z2,z10,z5,z6])],[(0,[z357,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z358]),(1,[z0,z1,z2,z359,z5,z6]),(0,[z94,z0,z1,z2,z156,z10,z5])],[(0,[z75,z1,z64,z2,z10,z5,z6]),(0,[z0,z1,z360,z2,z10,z5,z6]),(0,[z0,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z361,z10,z5,z6]),(1,[z0,z1,z21,z3,z10,z6])]],
   [[(0,[z0,z1,z2,z4,z241,z5,z6]),(0,[z0,z1,z59,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z362,z6]),(0,[z0,z363,z1,z2,z10,z5,z6]),(0,[z364,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z365,z2,z10,z5,z6])],[(0,[z0,z1,z2,z366,z10,z5,z6]),(0,[z0,z44,z1,z2,z10,z5,z6]),(0,[z0,z1,z367,z2,z10,z5,z6]),(0,[z0,z1,z97,z2,z10,z5,z6])],[(0,[z160,z0,z64,z2,z10,z5,z6]),(0,[z0,z1,z2,z368,z10,z5,z6]),(0,[z369,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z97,z2,z10,z6,z72])],[(1,[z0,z1,z181,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z370]),(0,[z0,z371,z1,z2,z10,z5,z6])],[(0,[z109,z0,z1,z2,z131,z5,z6]),(0,[z57,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z372])],[(0,[z0,z1,z2,z10,z5,z373,z6]),(0,[z0,z1,z374,z2,z10,z5,z6]),(0,[z0,z1,z375,z2,z10,z5,z6])],[(0,[z376,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z377,z2,z10,z5,z6]),(1,[z0,z1,z2,z378,z5,z6])],[(0,[z63,z0,z75,z2,z10,z5,z6]),(0,[z0,z44,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z22,z6]),(0,[z0,z1,z97,z2,z4,z5,z6]),(0,[z0,z1,z379,z2,z10,z5,z6]),(0,[z109,z0,z1,z2,z10,z342,z6])]],
   [[(1,[z0,z1,z2,z380,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z381]),(1,[z56,z1,z2,z10,z80,z6]),(0,[z0,z1,z2,z382,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z383,z6])],[(0,[z0,z1,z384,z2,z10,z5,z6]),(1,[z0,z1,z2,z159,z5,z6]),(0,[z0,z1,z385,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z386]),(0,[z0,z1,z2,z10,z387,z5,z6]),(0,[z0,z1,z126,z2,z10,z5,z173]),(0,[z0,z1,z388,z2,z10,z5,z6])],[(0,[z57,z0,z1,z2,z4,z5,z6]),(0,[z389,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z161,z6])],[(0,[z390,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z7,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z391,z6]),(0,[z0,z1,z60,z2,z76,z5,z6]),(0,[z0,z1,z126,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z392]),(0,[z0,z1,z2,z393,z10,z5,z6]),(0,[z0,z1,z2,z394,z10,z5,z6]),(0,[z0,z1,z2,z359,z10,z5,z6])],[(0,[z395,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z103]),(0,[z0,z1,z379,z2,z4,z5,z6]),(0,[z0,z11,z1,z2,z7,z5,z6]),(0,[z0,z1,z102,z2,z10,z5,z103]),(0,[z0,z1,z396,z2,z10,z5,z6]),(0,[z0,z1,z397,z2,z10,z5,z6]),(0,[z398,z0,z1,z2,z10,z5,z6])],[(0,[z91,z0,z75,z2,z10,z5,z6]),(0,[z91,z75,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z399,z10,z5,z6]),(0,[z0,z1,z400,z2,z10,z5,z6]),(0,[z0,z1,z401,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z10,z5,z6,z110]),(0,[z25,z0,z1,z2,z208,z5,z6]),(0,[z0,z1,z2,z402,z10,z5,z6]),(0,[z0,z1,z60,z2,z118,z5,z6]),(0,[z0,z1,z2,z403,z10,z5,z6]),(0,[z404,z0,z1,z2,z10,z5,z6])],[(0,[z390,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z126,z2,z4,z5,z6]),(0,[z405,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z283,z10,z5,z6]),(0,[z109,z1,z2,z10,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z22,z6]),(0,[z0,z1,z2,z406,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z407,z6])],[(0,[z408,z0,z1,z2,z10,z5,z6]),(0,[z56,z0,z1,z2,z48,z5,z6]),(1,[z25,z1,z2,z10,z5,z77]),(0,[z0,z1,z2,z359,z5,z22,z6]),(0,[z0,z1,z156,z10,z5,z6,z103])],[(0,[z409,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z118,z7,z5,z6]),(0,[z0,z1,z410,z2,z10,z5,z6]),(0,[z109,z0,z11,z1,z2,z10,z5])],[(1,[z1,z2,z4,z5,z77,z6]),(0,[z0,z1,z2,z10,z5,z411,z6]),(0,[z412,z0,z1,z2,z10,z5,z6])],[(0,[z413,z0,z1,z2,z10,z5,z6]),(0,[z414,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z415]),(0,[z112,z0,z1,z2,z10,z31,z6]),(0,[z0,z1,z416,z2,z10,z5,z6]),(0,[z417,z0,z1,z2,z10,z5,z6])]],
   [[(0,[z58,z0,z1,z138,z2,z5,z6]),(0,[z0,z1,z418,z2,z10,z5,z6]),(0,[z0,z1,z419,z2,z10,z5,z6])],[(0,[z160,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z420,z6]),(1,[z0,z1,z54,z2,z7,z5]),(0,[z0,z1,z13,z2,z7,z5,z6]),(0,[z421,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z422,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z423,z6]),(0,[z0,z1,z424,z2,z10,z5,z6])],[(0,[z63,z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z10,z425,z5,z6]),(0,[z136,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z426]),(1,[z58,z0,z2,z254,z5,z6]),(1,[z0,z1,z427,z10,z5,z6]),(0,[z428,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z429,z10,z5,z6]),(0,[z0,z1,z2,z430,z10,z5,z6])],[(1,[z55,z1,z2,z10,z137,z6]),(0,[z0,z1,z2,z10,z431,z5,z6]),(0,[z0,z432,z1,z2,z10,z5,z6])],[(0,[z0,z1,z433,z2,z10,z5,z6]),(0,[z47,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z434,z6]),(0,[z0,z1,z2,z435,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z436,z6])],[(1,[z0,z296,z1,z2,z10,z5]),(0,[z160,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z139]),(0,[z0,z1,z2,z10,z437,z5,z6]),(0,[z0,z1,z2,z10,z438,z5,z6]),(0,[z439,z0,z1,z2,z10,z5,z6])]],
   [[(0,[z313,z0,z1,z2,z10,z5,z6]),(0,[z112,z57,z0,z2,z10,z5,z6]),(0,[z0,z1,z440,z2,z10,z5,z6])],[(0,[z0,z1,z2,z4,z141,z5,z6]),(0,[z0,z1,z2,z275,z7,z5,z6]),(0,[z0,z1,z441,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z442,z5,z6]),(0,[z0,z443,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z8]),(0,[z0,z1,z2,z10,z5,z6,z444]),(0,[z0,z1,z2,z76,z10,z5,z6]),(0,[z0,z1,z126,z2,z3,z10,z6]),(0,[z0,z1,z2,z10,z445,z5,z6])],[(0,[z446,z0,z1,z2,z10,z5,z6]),(0,[z100,z1,z2,z71,z10,z5,z6]),(0,[z0,z1,z97,z2,z10,z241,z5])],[(0,[z0,z1,z2,z2,z10,z5,z6]),(0,[z0,z1,z2,z447,z10,z5,z6]),(0,[z57,z0,z2,z45,z10,z5,z6]),(0,[z448,z0,z1,z2,z10,z5,z6])],[(0,[z91,z0,z1,z2,z280,z5,z6]),(0,[z0,z449,z1,z2,z10,z5,z6]),(0,[z450,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z31,z6]),(1,[z0,z1,z2,z10,z5,z173]),(0,[z0,z1,z2,z451,z10,z5,z6]),(0,[z0,z1,z97,z2,z10,z5,z103])],[(1,[z0,z1,z2,z452,z5,z6]),(0,[z313,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z304,z10,z5,z6]),(0,[z55,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z295,z10,z5,z6]),(0,[z453,z0,z1,z2,z10,z5,z6])],[(1,[z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z163]),(0,[z56,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z454,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z455,z6]),(0,[z0,z1,z456,z2,z10,z5,z6]),(0,[z0,z1,z2,z457,z10,z5,z6]),(0,[z0,z1,z2,z118,z5,z6,z61])]],
   [[(0,[z100,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z76,z4,z5,z6]),(0,[z0,z1,z102,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z12]),(1,[z0,z1,z2,z245,z5,z6]),(0,[z136,z0,z1,z97,z2,z10,z5])],[(0,[z446,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z10,z5,z77,z6,z110]),(0,[z112,z0,z1,z2,z10,z5,z6]),(0,[z458,z0,z1,z2,z10,z5,z6]),(0,[z459,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z460,z5,z6]),(0,[z461,z0,z1,z2,z10,z5,z6])],[(1,[z313,z1,z2,z4,z5,z6]),(0,[z0,z9,z2,z10,z111,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z462]),(0,[z0,z1,z2,z10,z5,z463,z6]),(0,[z0,z1,z464,z2,z10,z5,z6])],[(0,[z63,z1,z64,z2,z10,z5,z6]),(0,[z0,z1,z70,z2,z7,z5,z6]),(0,[z0,z1,z117,z2,z7,z5,z6]),(0,[z0,z1,z465,z2,z10,z5,z6]),(0,[z0,z9,z1,z126,z2,z10,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z130,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z466,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z467,z6])],[(0,[z100,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z14]),(0,[z0,z468,z1,z2,z10,z5,z6]),(0,[z16,z0,z1,z2,z152,z5,z6]),(0,[z0,z1,z2,z469,z10,z5,z6]),(0,[z0,z1,z470,z2,z10,z5,z6]),(0,[z471,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z472,z10,z5,z6])],[(0,[z0,z75,z2,z10,z5,z6,z12]),(0,[z0,z1,z473,z2,z10,z5,z6]),(0,[z112,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z10,z5,z474,z6]),(0,[z0,z322,z1,z2,z7,z5,z6]),(0,[z0,z133,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z80,z5,z6]),(0,[z0,z1,z2,z10,z475,z5,z6]),(0,[z476,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z477,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z10,z80,z6,z72]),(0,[z0,z1,z2,z67,z10,z5,z6])],[(0,[z0,z1,z2,z254,z7,z5,z6]),(0,[z478,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z479,z6])],[(1,[z0,z1,z2,z10,z480,z6]),(0,[z481,z0,z1,z2,z10,z5,z6]),(1,[z112,z0,z2,z10,z31,z6]),(0,[z0,z1,z482,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z483])],[(0,[z0,z1,z295,z10,z5,z31,z6]),(0,[z0,z1,z138,z2,z10,z5,z6]),(0,[z0,z1,z331,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z484,z6]),(0,[z0,z1,z2,z485,z10,z5,z6]),(0,[z0,z1,z2,z486,z10,z5,z6])],[(1,[z196,z0,z2,z10,z5,z6]),(0,[z16,z32,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z487,z10,z5,z6]),(0,[z0,z2,z10,z5,z199,z22,z6]),(0,[z0,z1,z2,z488,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z5,z6]),(0,[z109,z0,z1,z2,z10,z5,z6]),(0,[z0,z11,z1,z2,z10,z5,z161]),(0,[z489,z0,z1,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z110]),(0,[z0,z1,z2,z490,z10,z5,z6]),(0,[z58,z0,z1,z60,z2,z5,z6]),(0,[z0,z1,z2,z10,z491,z5,z6]),(0,[z0,z1,z492,z2,z10,z5,z6]),(0,[z0,z1,z2,z493,z10,z5,z6])],[(0,[z0,z1,z138,z2,z4,z5,z6]),(0,[z0,z1,z59,z2,z7,z5,z6]),(1,[z0,z494,z2,z10,z5,z6]),(0,[z0,z1,z495,z2,z10,z5,z6]),(0,[z0,z1,z2,z496,z10,z5,z6])],[(0,[z55,z0,z1,z2,z366,z5,z6]),(0,[z0,z29,z2,z45,z10,z5,z6]),(0,[z0,z44,z1,z126,z10,z5,z6]),(0,[z0,z1,z2,z497,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z498])],[(0,[z499,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z350,z7,z5,z6]),(1,[z0,z1,z2,z366,z5,z6])],[(0,[z0,z1,z2,z487,z4,z5,z6]),(0,[z0,z1,z2,z10,z207,z5,z6]),(0,[z0,z1,z2,z10,z342,z5,z6]),(0,[z0,z1,z194,z2,z45,z5,z6]),(0,[z500,z0,z1,z2,z10,z5,z6])],[(0,[z109,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z156,z4,z5,z6]),(0,[z57,z0,z1,z126,z10,z5,z6])],[(0,[z501,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z102,z2,z156,z10,z5]),(0,[z0,z1,z117,z59,z2,z10,z6]),(0,[z0,z502,z1,z2,z10,z5,z6])],[(0,[z503,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z496,z4,z5,z6]),(0,[z504,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z505,z2,z10,z5,z6]),(0,[z506,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z507,z5,z6])]],
   [[(0,[z0,z508,z1,z2,z10,z5,z6]),(0,[z0,z44,z1,z2,z7,z5,z6]),(0,[z0,z1,z97,z2,z7,z5,z6]),(0,[z0,z1,z509,z2,z10,z5,z6])],[(0,[z0,z1,z2,z510,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z511]),(1,[z94,z0,z1,z156,z10,z5]),(0,[z0,z1,z2,z10,z5,z512,z6])],[(0,[z55,z0,z1,z2,z335,z5,z6]),(0,[z136,z0,z1,z2,z10,z80,z6]),(0,[z109,z0,z1,z2,z10,z480,z6]),(0,[z0,z1,z513,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z514,z6]),(0,[z0,z1,z515,z2,z10,z5,z6]),(0,[z0,z1,z2,z516,z10,z5,z6])],[(0,[z57,z0,z1,z2,z7,z5,z6]),(1,[z0,z1,z2,z335,z5,z6])],[(1,[z0,z1,z2,z336,z5,z6]),(0,[z0,z1,z194,z2,z10,z5,z6]),(0,[z0,z1,z2,z152,z5,z6,z61]),(0,[z0,z1,z2,z254,z5,z6,z61]),(0,[z0,z1,z517,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z95]),(0,[z0,z1,z117,z59,z2,z5,z6])],[(0,[z69,z0,z1,z70,z10,z5,z6]),(0,[z0,z1,z2,z10,z518,z5,z6]),(0,[z112,z0,z1,z21,z2,z10,z6])],[(0,[z0,z1,z2,z10,z5,z519,z6]),(0,[z0,z1,z2,z10,z5,z520,z6]),(0,[z16,z0,z1,z2,z254,z5,z6]),(0,[z0,z521,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z522])],[(0,[z0,z1,z64,z2,z10,z5,z6]),(0,[z109,z0,z1,z2,z10,z5,z77]),(0,[z0,z133,z1,z59,z2,z5,z6]),(0,[z523,z0,z1,z2,z10,z5,z6]),(0,[z524,z0,z1,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z525,z10,z5,z6]),(0,[z526,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z30,z10,z5,z6]),(0,[z0,z1,z2,z336,z10,z5,z6]),(0,[z16,z0,z1,z60,z2,z5,z6])],[],[(0,[z0,z1,z527,z2,z10,z5,z6]),(0,[z390,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z7,z7,z5,z6]),(0,[z528,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z529,z2,z10,z5,z6])],[(0,[z63,z0,z64,z2,z10,z5,z6]),(0,[z94,z0,z1,z70,z10,z5,z6]),(0,[z0,z1,z2,z10,z530,z5,z6]),(1,[z531,z1,z2,z10,z5,z6]),(0,[z0,z1,z97,z2,z267,z5,z6])],[(0,[z100,z0,z1,z2,z380,z5,z6]),(0,[z532,z0,z1,z2,z10,z5,z6]),(0,[z533,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z534,z5,z6]),(0,[z0,z1,z59,z2,z5,z6,z61])],[(0,[z0,z1,z64,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z31,z6]),(0,[z0,z1,z60,z76,z10,z5,z6])],[(0,[z0,z1,z2,z10,z36,z5,z6]),(0,[z0,z1,z2,z7,z241,z5,z6]),(0,[z56,z0,z1,z2,z10,z80,z6]),(0,[z58,z0,z1,z2,z118,z5,z6])],[(0,[z0,z1,z535,z2,z10,z5,z6]),(0,[z0,z1,z60,z2,z10,z5,z6]),(1,[z0,z2,z10,z5,z199,z6]),(0,[z0,z1,z2,z536,z10,z5,z6]),(0,[z0,z1,z2,z10,z241,z5,z72]),(0,[z0,z1,z537,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z538,z2,z10,z5,z6]),(0,[z539,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z540,z6]),(0,[z0,z1,z2,z10,z5,z541,z6])],[(0,[z0,z1,z2,z10,z5,z137,z6]),(0,[z0,z1,z2,z10,z5,z542,z6])],[(0,[z91,z0,z64,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z61]),(1,[z0,z1,z2,z48,z5,z6]),(0,[z109,z160,z0,z1,z2,z10,z5]),(0,[z109,z0,z1,z13,z2,z10,z5]),(0,[z0,z2,z10,z5,z161,z6,z12]),(0,[z0,z1,z543,z2,z10,z5,z6])],[(0,[z0,z1,z544,z2,z10,z5,z6]),(0,[z0,z1,z545,z2,z10,z5,z6]),(0,[z0,z546,z1,z2,z10,z5,z6]),(0,[z0,z1,z547,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z548,z6]),(0,[z0,z1,z246,z2,z10,z5,z6]),(0,[z549,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z60,z2,z4,z5,z6])],[(0,[z0,z200,z1,z64,z2,z10,z5]),(0,[z0,z1,z550,z2,z10,z5,z6]),(0,[z0,z1,z551,z2,z10,z5,z6]),(0,[z109,z25,z1,z2,z10,z5,z6]),(0,[z109,z0,z1,z181,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z552]),(0,[z0,z1,z2,z10,z5,z553,z6]),(0,[z0,z1,z97,z2,z156,z10,z5])],[(0,[z0,z1,z2,z4,z80,z5,z6]),(0,[z554,z0,z1,z2,z10,z5,z6]),(0,[z56,z1,z2,z10,z80,z5,z6]),(0,[z0,z1,z2,z555,z10,z5,z6])]],
   [[(0,[z160,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z378,z10,z5,z6])],[(0,[z556,z0,z1,z2,z10,z5,z6]),(0,[z109,z0,z1,z2,z378,z5,z6]),(1,[z0,z1,z308,z2,z5,z6]),(0,[z0,z557,z1,z2,z10,z5,z6]),(0,[z558,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z559,z2,z10,z5,z6]),(0,[z560,z0,z1,z2,z10,z5,z6]),(0,[z25,z1,z2,z10,z5,z77,z6]),(0,[z0,z11,z1,z2,z442,z5,z6]),(0,[z0,z1,z2,z10,z561,z5,z6]),(0,[z16,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z562]),(0,[z0,z296,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z563,z10,z5,z6]),(0,[z0,z1,z2,z7,z5,z6,z103]),(0,[z0,z1,z2,z10,z5,z6,z564])],[(0,[z0,z1,z2,z4,z111,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z565]),(0,[z0,z1,z2,z566,z10,z5,z6]),(0,[z0,z1,z2,z10,z567,z5,z6]),(0,[z568,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z7,z5,z6,z61]),(0,[z109,z0,z1,z2,z10,z5,z61]),(0,[z0,z1,z2,z569,z10,z5,z6])],[(0,[z0,z570,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z571,z10,z5,z6]),(0,[z16,z0,z1,z2,z118,z5,z6])],[(0,[z0,z1,z2,z10,z572,z5,z6]),(0,[z313,z0,z1,z2,z7,z5,z6]),(0,[z573,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z574]),(0,[z0,z1,z2,z10,z5,z72,z103]),(0,[z0,z1,z2,z496,z10,z5,z61])]],
   [[(0,[z575,z0,z1,z2,z10,z5,z6]),(0,[z16,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z276,z2,z10,z5,z6]),(1,[z0,z1,z2,z208,z5,z6]),(0,[z576,z0,z1,z2,z10,z5,z6]),(0,[z112,z0,z29,z2,z10,z5,z6]),(0,[z0,z1,z577,z2,z10,z5,z6])],[(0,[z578,z0,z1,z2,z10,z5,z6]),(0,[z0,z579,z1,z2,z10,z5,z6]),(0,[z580,z0,z1,z2,z10,z5,z6]),(0,[z58,z0,z1,z2,z152,z5,z6]),(0,[z0,z1,z2,z220,z5,z31,z6]),(0,[z0,z1,z2,z10,z5,z6,z581]),(0,[z582,z0,z1,z2,z10,z5,z6])],[(0,[z63,z0,z1,z2,z10,z5,z6]),(0,[z583,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z54,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z131,z5,z6]),(0,[z0,z1,z584,z2,z10,z5,z6]),(0,[z136,z0,z1,z2,z10,z241,z6])],[(0,[z0,z1,z2,z585,z10,z5,z6]),(0,[z0,z1,z2,z586,z10,z5,z6])],[(1,[z109,z1,z2,z4,z5,z6]),(0,[z587,z0,z1,z2,z10,z5,z6]),(1,[z0,z1,z117,z59,z2,z6])],[(0,[z0,z75,z1,z2,z10,z5,z6]),(0,[z55,z0,z1,z2,z7,z5,z6])],[(0,[z0,z1,z2,z10,z5,z6,z588]),(1,[z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z589,z6]),(0,[z0,z1,z2,z590,z10,z5,z6])],[(0,[z0,z1,z2,z10,z591,z5,z6]),(1,[z0,z1,z2,z283,z5,z6]),(0,[z0,z1,z2,z7,z111,z5,z6]),(1,[z0,z1,z2,z10,z241,z72])]],
   [[(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z112,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z259]),(0,[z0,z1,z2,z592,z10,z5,z6]),(0,[z0,z593,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z594]),(0,[z0,z1,z2,z595,z10,z5,z6])],[(0,[z63,z91,z1,z2,z10,z5,z6]),(0,[z91,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z152,z5,z6]),(0,[z596,z0,z1,z2,z10,z5,z6])],[(0,[z100,z0,z1,z2,z452,z5,z6]),(0,[z0,z1,z597,z2,z10,z5,z6]),(0,[z598,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z599,z10,z5,z6])],[(0,[z0,z1,z600,z2,z10,z5,z6]),(0,[z0,z75,z1,z2,z4,z5,z6]),(0,[z0,z1,z70,z10,z5,z6,z103]),(0,[z601,z0,z1,z2,z10,z5,z6]),(0,[z0,z602,z1,z2,z10,z5,z6]),(0,[z0,z1,z603,z2,z10,z5,z6])],[(0,[z0,z1,z2,z604,z10,z5,z6]),(0,[z0,z1,z2,z7,z10,z5,z8]),(0,[z0,z2,z10,z111,z5,z31,z6]),(0,[z605,z0,z1,z2,z10,z5,z6]),(0,[z606,z0,z1,z2,z10,z5,z6])],[(0,[z1,z2,z7,z10,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z6,z139]),(0,[z0,z1,z2,z10,z5,z607,z6]),(0,[z0,z1,z2,z10,z5,z608,z6]),(1,[z0,z1,z2,z220,z5,z6])],[(0,[z0,z1,z2,z10,z5,z609,z6]),(0,[z610,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z60,z2,z5,z6,z139]),(0,[z0,z1,z2,z10,z5,z6,z611]),(1,[z0,z1,z2,z496,z5,z61])],[(0,[z91,z0,z1,z2,z4,z5,z6]),(0,[z0,z612,z1,z2,z10,z5,z6]),(0,[z613,z0,z1,z2,z10,z5,z6]),(0,[z0,z44,z1,z3,z10,z5,z6])]],
   [[(1,[z0,z1,z2,z442,z5,z6]),(0,[z0,z1,z2,z10,z5,z614,z6]),(1,[z0,z1,z60,z76,z5,z6]),(0,[z0,z1,z126,z2,z10,z22,z6]),(0,[z0,z1,z2,z615,z10,z5,z6])],[(0,[z130,z1,z2,z10,z5,z77,z6]),(0,[z25,z0,z11,z1,z2,z10,z5]),(0,[z0,z1,z84,z2,z10,z5,z6]),(0,[z0,z1,z2,z616,z10,z5,z6]),(0,[z617,z0,z1,z2,z10,z5,z6]),(1,[z0,z1,z102,z10,z5,z103]),(0,[z0,z1,z2,z618,z10,z5,z6]),(1,[z0,z1,z2,z267,z5,z6])],[(0,[z0,z1,z138,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z299]),(0,[z57,z0,z1,z3,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z619])],[(0,[z620,z0,z1,z2,z10,z5,z6]),(0,[z1,z2,z10,z80,z5,z137,z6]),(0,[z621,z0,z1,z2,z10,z5,z6]),(0,[z0,z622,z1,z2,z10,z5,z6]),(0,[z623,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z624,z2,z10,z5,z6])],[(1,[z0,z200,z1,z2,z10,z5]),(1,[z0,z1,z2,z142,z5,z6]),(0,[z55,z1,z2,z10,z5,z137,z6]),(0,[z625,z0,z1,z2,z10,z5,z6]),(0,[z626,z0,z1,z2,z10,z5,z6])],[(0,[z627,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z161,z6]),(0,[z57,z0,z44,z2,z10,z5,z6]),(0,[z16,z0,z1,z13,z2,z10,z5])],[(0,[z0,z1,z2,z10,z380,z5,z6]),(0,[z109,z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z628]),(0,[z0,z1,z2,z10,z5,z629,z6])],[(0,[z630,z0,z1,z2,z10,z5,z6]),(0,[z0,z631,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z632,z10,z5,z6]),(0,[z0,z1,z21,z2,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z10,z5,z633,z6]),(1,[z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z496,z7,z5,z6]),(1,[z57,z0,z45,z10,z5,z6]),(0,[z0,z634,z1,z2,z10,z5,z6]),(0,[z0,z11,z1,z2,z10,z5,z12])],[(0,[z0,z1,z151,z2,z10,z5,z6]),(0,[z1,z2,z10,z4,z5,z77,z6]),(0,[z0,z494,z1,z2,z10,z5,z6]),(0,[z0,z1,z635,z2,z10,z5,z6]),(0,[z58,z0,z1,z2,z254,z5,z6]),(0,[z0,z1,z2,z10,z5,z636,z6])],[(0,[z0,z1,z54,z2,z7,z10,z5]),(0,[z0,z1,z2,z10,z5,z637,z6]),(0,[z0,z1,z2,z638,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z639,z6]),(1,[z0,z11,z2,z10,z5,z12]),(0,[z0,z1,z640,z2,z10,z5,z6]),(0,[z0,z1,z2,z156,z10,z5,z6])],[(0,[z0,z133,z1,z138,z2,z5,z6]),(0,[z0,z1,z2,z156,z245,z5,z6]),(0,[z16,z0,z1,z2,z496,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z72])],[(0,[z0,z1,z641,z2,z10,z5,z6]),(0,[z0,z1,z642,z2,z10,z5,z6]),(0,[z0,z643,z1,z2,z10,z5,z6])],[(0,[z0,z1,z21,z2,z4,z5,z6]),(0,[z0,z631,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z644,z10,z5,z6]),(0,[z0,z1,z645,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z646])],[(0,[z0,z1,z2,z71,z4,z5,z6]),(0,[z0,z1,z2,z10,z5,z647,z6])],[(0,[z648,z0,z1,z2,z10,z5,z6]),(0,[z0,z649,z1,z2,z10,z5,z6]),(1,[z0,z1,z54,z2,z10,z5]),(0,[z0,z1,z2,z650,z10,z5,z6]),(0,[z0,z651,z1,z2,z10,z5,z6]),(0,[z652,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z653,z10,z5,z6]),(0,[z0,z1,z2,z654,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z7,z5,z161,z6]),(0,[z0,z1,z2,z510,z7,z5,z6]),(0,[z0,z1,z2,z10,z655,z5,z6]),(0,[z160,z0,z1,z2,z10,z5,z12]),(0,[z16,z0,z1,z2,z10,z5,z61])],[(0,[z0,z1,z656,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z657])],[(0,[z0,z1,z2,z658,z10,z5,z6]),(0,[z0,z1,z150,z2,z10,z5,z6]),(0,[z160,z0,z1,z2,z10,z5,z161]),(0,[z160,z0,z2,z10,z5,z161,z6]),(0,[z0,z1,z76,z10,z5,z6,z139]),(1,[z0,z1,z126,z10,z22,z6])],[(0,[z0,z1,z126,z2,z51,z10,z5]),(0,[z0,z1,z126,z10,z5,z22,z6]),(0,[z531,z0,z1,z2,z10,z5,z6])],[(0,[z659,z0,z1,z2,z10,z5,z6]),(0,[z660,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z118,z5,z6,z95])],[(0,[z69,z0,z1,z2,z159,z5,z6]),(0,[z0,z1,z2,z10,z5,z480,z6]),(0,[z0,z1,z427,z2,z10,z5,z6]),(0,[z0,z1,z138,z2,z5,z6,z61]),(0,[z0,z1,z661,z2,z10,z5,z6])],[(0,[z0,z662,z1,z2,z10,z5,z6]),(0,[z0,z1,z663,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z664]),(0,[z0,z1,z2,z7,z5,z6,z110]),(0,[z0,z1,z2,z10,z5,z77,z6]),(0,[z109,z0,z1,z2,z10,z5,z110]),(0,[z0,z1,z2,z665,z10,z5,z6]),(0,[z0,z9,z1,z2,z10,z31,z6]),(0,[z0,z1,z427,z10,z5,z31,z6])],[(0,[z0,z1,z2,z525,z7,z5,z6]),(0,[z109,z1,z2,z10,z5,z6,z110])]],
   [[(1,[z0,z1,z2,z10,z5,z8])],[(0,[z0,z1,z2,z666,z10,z5,z6]),(0,[z0,z667,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z668,z10,z5,z6])],[(0,[z0,z1,z138,z59,z2,z5,z6]),(0,[z669,z0,z1,z2,z10,z5,z6]),(0,[z0,z670,z1,z2,z10,z5,z6])],[(0,[z0,z1,z385,z2,z7,z5,z6]),(0,[z671,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z672,z10,z5,z6]),(0,[z0,z1,z2,z496,z5,z6,z61]),(0,[z0,z1,z2,z10,z5,z673,z6])],[(0,[z674,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z675,z2,z10,z5,z6]),(0,[z55,z0,z1,z2,z10,z80,z6]),(0,[z109,z0,z494,z2,z10,z5,z6]),(0,[z112,z0,z1,z2,z10,z111,z6]),(0,[z0,z1,z676,z2,z10,z5,z6]),(0,[z0,z11,z1,z2,z67,z5,z6]),(0,[z0,z1,z677,z2,z10,z5,z6]),(0,[z136,z0,z1,z97,z2,z10,z6])],[(0,[z69,z1,z70,z2,z10,z5,z6]),(0,[z0,z1,z126,z2,z7,z5,z6]),(0,[z0,z678,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z679,z5,z6]),(0,[z58,z0,z133,z2,z10,z5,z6]),(0,[z58,z0,z1,z2,z10,z5,z6]),(0,[z680,z0,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z452,z10,z5,z6]),(0,[z0,z1,z681,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z588]),(0,[z0,z1,z60,z2,z7,z5,z6]),(0,[z682,z0,z1,z2,z10,z5,z6]),(0,[z683,z0,z1,z2,z10,z5,z6]),(1,[z0,z1,z107,z2,z5,z6]),(0,[z0,z1,z2,z684,z10,z5,z6]),(0,[z685,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z21,z2,z3,z10,z6])],[(0,[z686,z0,z1,z2,z10,z5,z6]),(0,[z109,z130,z1,z2,z10,z5,z6]),(0,[z56,z0,z1,z2,z207,z5,z6]),(0,[z687,z0,z1,z2,z10,z5,z6])]],
   [[(1,[z91,z75,z2,z10,z5,z6]),(0,[z688,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z689,z2,z10,z5,z6]),(0,[z531,z16,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z4,z152,z5,z6]),(0,[z0,z1,z2,z10,z5,z690,z6]),(0,[z0,z1,z691,z2,z10,z5,z6])],[(0,[z0,z1,z2,z10,z5,z692,z6]),(0,[z0,z1,z2,z3,z10,z5,z6]),(0,[z0,z1,z13,z2,z496,z10,z5])],[(0,[z693,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z12]),(0,[z58,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z694,z2,z10,z5,z6]),(0,[z0,z695,z1,z2,z10,z5,z6]),(0,[z0,z1,z696,z2,z10,z5,z6])],[(0,[z25,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z697,z2,z10,z5,z6]),(1,[z0,z1,z150,z2,z10,z6]),(0,[z0,z1,z2,z698,z10,z5,z6]),(0,[z0,z1,z2,z699,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z700,z6])],[(0,[z0,z1,z2,z10,z10,z5,z6]),(0,[z0,z1,z223,z2,z4,z5,z6]),(0,[z0,z1,z701,z2,z10,z5,z6]),(0,[z0,z1,z29,z2,z10,z5,z6]),(0,[z0,z1,z138,z2,z5,z6,z139])],[(0,[z0,z64,z2,z10,z5,z6,z12]),(0,[z0,z1,z2,z10,z5,z702,z6]),(0,[z703,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z704,z6]),(0,[z136,z0,z1,z2,z10,z5,z72])],[(0,[z57,z0,z2,z10,z111,z5,z6]),(0,[z705,z0,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z7,z480,z6]),(0,[z112,z0,z2,z7,z31,z6]),(0,[z0,z1,z60,z177,z5,z6]),(0,[z1,z2,z10,z5,z6,z707]),(0,[z531,z1,z2,z10,z5,z61]),(0,[z0,z1,z708,z2,z5,z6])],[(0,[z0,z709,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z710]),(0,[z0,z1,z2,z711,z5,z6]),(0,[z130,z1,z54,z2,z7,z5]),(0,[z0,z1,z2,z10,z518,z72])],[(0,[z448,z1,z70,z10,z5,z6])],[(0,[z0,z1,z2,z142,z5,z6]),(0,[z0,z200,z1,z2,z10,z5]),(0,[z109,z1,z2,z4,z5,z77]),(0,[z1,z2,z7,z712,z5,z6]),(0,[z0,z133,z2,z30,z5,z6]),(0,[z25,z1,z2,z10,z5,z483]),(0,[z0,z1,z2,z713,z5,z6])],[(0,[z617,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z714,z5,z6]),(0,[z0,z1,z2,z345,z5,z61])],[(0,[z109,z494,z2,z4,z5,z6]),(0,[z0,z11,z2,z7,z5,z12]),(0,[z25,z0,z1,z2,z442,z5]),(0,[z0,z1,z2,z715,z5,z6])],[(0,[z0,z296,z1,z2,z7,z5]),(0,[z0,z2,z4,z5,z199,z6]),(0,[z414,z1,z2,z4,z5,z6]),(0,[z0,z1,z385,z76,z5,z6]),(0,[z0,z1,z2,z716,z5,z6]),(0,[z0,z9,z2,z10,z717,z6]),(0,[z160,z0,z2,z10,z5,z161])],[(0,[z0,z1,z718,z10,z5,z6]),(0,[z405,z1,z2,z4,z5,z6]),(0,[z0,z631,z1,z13,z2,z5]),(0,[z0,z494,z2,z7,z5,z6]),(0,[z57,z0,z45,z10,z5,z6]),(0,[z57,z0,z84,z2,z10,z6]),(0,[z112,z0,z2,z220,z31,z6]),(0,[z0,z1,z2,z10,z561,z72])]],
   [[(0,[z91,z709,z2,z10,z5,z6]),(0,[z0,z1,z2,z719,z5,z6]),(0,[z720,z1,z2,z10,z5,z6])],[(0,[z0,z1,z2,z721,z5,z6]),(0,[z112,z0,z2,z10,z608,z6])],[(1,[z1,z722,z10,z5,z6]),(0,[z0,z1,z2,z723,z5,z6]),(0,[z130,z1,z2,z7,z5,z6])],[(0,[z0,z1,z2,z10,z724,z6]),(0,[z0,z1,z725,z10,z5,z6]),(0,[z0,z1,z2,z726,z5,z6]),(0,[z0,z1,z727,z10,z5,z6])],[(0,[z109,z1,z2,z10,z342,z110]),(0,[z0,z1,z2,z10,z728,z6])],[(0,[z0,z1,z729,z2,z10,z6]),(0,[z0,z1,z2,z10,z5,z730]),(0,[z0,z731,z1,z2,z10,z5]),(0,[z57,z0,z45,z4,z5,z6]),(0,[z0,z1,z379,z59,z2,z6]),(0,[z0,z1,z59,z2,z639,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z0,z1,z733,z10,z22,z6])],[(0,[z0,z1,z734,z10,z5,z6]),(0,[z0,z1,z735,z2,z5,z6]),(0,[z0,z1,z54,z2,z10,z5]),(0,[z0,z1,z736,z10,z5,z6]),(0,[z0,z1,z2,z737,z5,z6])],[(0,[z0,z200,z1,z2,z4,z5]),(0,[z57,z0,z1,z84,z10,z6]),(0,[z0,z1,z126,z10,z22,z173]),(0,[z32,z1,z2,z118,z5,z6]),(0,[z0,z1,z2,z118,z407,z6])]],
   [[(0,[z0,z1,z2,z10,z5,z738]),(0,[z130,z1,z2,z712,z5,z6]),(0,[z0,z1,z739,z2,z7,z5]),(0,[z0,z1,z2,z131,z342,z6]),(0,[z0,z1,z84,z2,z10,z6])],[(0,[z0,z200,z1,z2,z740,z5]),(0,[z0,z1,z2,z741,z5,z6]),(0,[z0,z1,z742,z2,z5,z6]),(0,[z1,z2,z378,z4,z5,z6]),(0,[z0,z1,z2,z743,z5,z6]),(0,[z0,z1,z126,z10,z22,z6]),(0,[z0,z1,z2,z744,z5,z6]),(0,[z0,z1,z745,z2,z10,z241])],[(0,[z0,z1,z2,z746,z5,z6]),(0,[z0,z1,z84,z308,z2,z6]),(0,[z0,z1,z2,z747,z5,z6])],[(0,[z0,z1,z2,z10,z5,z748]),(0,[z0,z1,z2,z7,z5,z8]),(0,[z109,z1,z535,z2,z10,z5]),(0,[z0,z1,z2,z749,z5,z6])],[(0,[z0,z1,z2,z10,z5,z750]),(0,[z0,z751,z2,z10,z5,z6]),(0,[z109,z1,z13,z2,z4,z5]),(0,[z136,z0,z1,z193,z2,z10]),(0,[z0,z1,z2,z752,z5,z6]),(0,[z0,z1,z2,z753,z5,z6])],[(0,[z94,z0,z1,z563,z10,z5]),(0,[z0,z1,z13,z2,z336,z5]),(0,[z196,z0,z126,z2,z10,z6]),(0,[z0,z204,z2,z5,z199,z6])],[(0,[z0,z1,z2,z754,z5,z6]),(0,[z0,z9,z509,z2,z10,z6])],[(0,[z0,z1,z126,z4,z22,z6]),(0,[z0,z1,z2,z350,z5,z8])]],
   [[(0,[z69,z1,z70,z10,z5,z6]),(0,[z0,z1,z2,z304,z6,z163]),(0,[z109,z1,z181,z10,z5,z110]),(0,[z0,z755,z1,z2,z10,z5])],[(0,[z109,z1,z2,z4,z5,z61]),(0,[z531,z1,z2,z7,z5,z6]),(0,[z136,z0,z1,z97,z2,z10])],[(0,[z0,z1,z2,z756,z5,z6]),(0,[z0,z1,z54,z2,z4,z5])],[(0,[z0,z1,z2,z757,z10,z5]),(0,[z1,z54,z2,z4,z5,z6]),(0,[z0,z1,z758,z2,z4,z6]),(0,[z0,z1,z759,z2,z5,z6]),(0,[z109,z1,z2,z378,z5,z110]),(0,[z0,z1,z2,z760,z5,z6]),(0,[z0,z1,z2,z761,z5,z6]),(0,[z0,z1,z2,z10,z762,z6]),(0,[z763,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z98,z5,z6]),(0,[z0,z1,z117,z2,z764,z6])],[(0,[z0,z1,z84,z2,z4,z6]),(0,[z0,z1,z181,z131,z5,z6]),(0,[z0,z1,z2,z765,z5,z6])],[(0,[z0,z1,z2,z766,z5,z6]),(0,[z0,z1,z767,z2,z7,z5]),(0,[z0,z1,z768,z2,z5,z6]),(0,[z0,z1,z2,z769,z10,z5]),(0,[z0,z1,z107,z2,z5,z6]),(1,[z0,z1,z770,z10,z5])],[(0,[z69,z1,z70,z4,z5,z6]),(0,[z1,z465,z2,z7,z5,z6]),(0,[z0,z1,z2,z771,z5,z6]),(0,[z0,z44,z772,z10,z5,z6])],[(0,[z91,z75,z2,z10,z5,z6]),(0,[z0,z1,z2,z7,z5,z773]),(0,[z0,z1,z2,z10,z5,z774]),(0,[z0,z1,z2,z775,z5,z6]),(0,[z196,z0,z126,z10,z22,z6])]],
   [[(0,[z0,z776,z2,z10,z5,z6]),(0,[z0,z1,z2,z777,z5,z6])],[],[(0,[z0,z1,z54,z2,z378,z5]),(0,[z0,z1,z194,z150,z2,z6]),(0,[z0,z1,z778,z2,z10,z6]),(0,[z32,z1,z2,z152,z5,z6]),(0,[z0,z1,z779,z10,z5,z6]),(0,[z112,z0,z427,z2,z10,z6])],[(0,[z0,z1,z2,z10,z5,z780]),(1,[z0,z2,z10,z717,z6]),(0,[z781,z1,z2,z10,z5,z6]),(0,[z782,z1,z2,z10,z5,z6])],[(0,[z160,z0,z2,z10,z5,z420]),(0,[z783,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z784,z5,z6])],[(0,[z91,z75,z2,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z8]),(0,[z785,z1,z2,z10,z5,z6]),(0,[z196,z0,z204,z2,z5,z6])],[(0,[z0,z246,z2,z10,z5,z6]),(0,[z109,z1,z2,z208,z5,z6]),(0,[z0,z1,z2,z786,z5,z6])],[(0,[z1,z722,z2,z10,z5,z6]),(0,[z0,z1,z2,z787,z5,z6]),(0,[z0,z1,z2,z757,z4,z5]),(0,[z0,z788,z2,z10,z5,z6]),(0,[z0,z1,z2,z733,z10,z6])]],
   [[(0,[z94,z0,z1,z156,z7,z5]),(0,[z1,z2,z488,z7,z5,z6]),(0,[z500,z1,z2,z7,z5,z6]),(0,[z57,z0,z194,z45,z5,z6]),(0,[z112,z0,z107,z2,z31,z6]),(0,[z0,z1,z2,z789,z5,z6])],[(0,[z0,z1,z2,z790,z5,z6]),(0,[z1,z2,z712,z10,z5,z6])],[(0,[z0,z1,z2,z791,z5,z6]),(0,[z792,z1,z2,z10,z5,z6]),(0,[z0,z1,z220,z295,z5,z6]),(0,[z793,z1,z2,z10,z5,z6])],[(0,[z0,z794,z1,z2,z10,z5]),(0,[z0,z1,z59,z2,z5,z8]),(0,[z25,z651,z1,z2,z10,z5])],[(0,[z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z10,z5,z795]),(0,[z0,z246,z2,z4,z5,z6]),(0,[z0,z305,z2,z152,z5,z6]),(0,[z0,z1,z796,z10,z5,z6]),(0,[z0,z1,z138,z5,z797,z6]),(0,[z0,z1,z2,z798,z10,z6]),(0,[z32,z1,z2,z496,z5,z6])],[(0,[z63,z64,z2,z7,z5,z6]),(0,[z0,z1,z2,z7,z799,z5])],[(0,[z0,z1,z2,z118,z479,z6])],[(0,[z0,z1,z2,z280,z5,z6]),(0,[z0,z1,z2,z10,z800,z6]),(0,[z0,z1,z271,z10,z5,z6]),(0,[z1,z2,z712,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z6]),(0,[z0,z1,z2,z801,z5,z6]),(0,[z625,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z802,z5,z6]),(0,[z0,z11,z2,z10,z5,z803])]],
   [[(0,[z63,z200,z64,z2,z10,z5]),(0,[z0,z804,z2,z10,z5,z6]),(0,[z0,z1,z2,z805,z5,z6]),(0,[z0,z2,z772,z10,z5,z6]),(0,[z0,z1,z10,z5,z797,z6])],[(0,[z634,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z67,z5,z6])],[],[(0,[z0,z1,z2,z806,z5,z6]),(0,[z0,z133,z2,z807,z5,z6]),(0,[z0,z1,z2,z807,z5,z6]),(0,[z0,z1,z808,z2,z5,z6]),(0,[z0,z1,z2,z809,z5,z6]),(1,[z0,z1,z810,z2,z5])],[(0,[z0,z811,z2,z10,z5,z6]),(0,[z109,z1,z2,z10,z5,z381]),(0,[z0,z1,z2,z336,z5,z8]),(0,[z0,z2,z10,z5,z812,z6]),(0,[z0,z1,z2,z10,z5,z813])],[(0,[z0,z1,z271,z4,z5,z6]),(0,[z0,z1,z2,z7,z241,z72]),(0,[z814,z1,z2,z10,z5,z6]),(0,[z0,z2,z10,z111,z589,z6]),(0,[z0,z1,z59,z2,z293,z6])],[(0,[z0,z815,z2,z10,z5,z6]),(0,[z0,z309,z1,z126,z10,z6]),(0,[z94,z0,z1,z331,z156,z5])],[(0,[z0,z1,z5,z797,z6,z139])]],
   [[(0,[z651,z1,z2,z4,z5,z6]),(0,[z652,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z816,z5,z6])],[(0,[z1,z54,z2,z7,z4,z5]),(0,[z0,z246,z2,z10,z342,z6]),(0,[z196,z0,z1,z126,z10,z6]),(0,[z0,z1,z817,z2,z5,z6])],[(0,[z0,z1,z818,z10,z5,z6]),(0,[z0,z1,z2,z819,z5,z6]),(0,[z1,z2,z4,z5,z6,z574]),(0,[z631,z1,z2,z10,z5,z77]),(0,[z0,z1,z271,z10,z480,z6]),(0,[z32,z1,z2,z254,z5,z6]),(0,[z0,z126,z10,z199,z22,z6])],[(0,[z0,z84,z29,z2,z10,z6]),(0,[z58,z0,z2,z807,z5,z6]),(0,[z94,z0,z1,z156,z245,z5])],[(0,[z0,z1,z2,z820,z5,z6]),(0,[z109,z1,z2,z10,z5,z110]),(0,[z0,z1,z821,z2,z5,z6]),(0,[z0,z1,z138,z5,z325,z6])],[(0,[z69,z1,z70,z159,z5,z6]),(0,[z0,z1,z2,z10,z822,z6]),(0,[z0,z1,z97,z745,z2,z10])],[(0,[z160,z0,z200,z2,z10,z5]),(0,[z0,z1,z2,z823,z10,z5]),(0,[z100,z1,z71,z380,z5,z6]),(0,[z56,z1,z2,z207,z80,z6]),(0,[z0,z1,z138,z644,z5,z6]),(0,[z0,z2,z10,z5,z824,z6])],[(0,[z0,z1,z2,z10,z825,z6]),(0,[z0,z1,z2,z10,z826,z6]),(0,[z0,z1,z827,z2,z5,z6])]],
   [[(0,[z0,z1,z828,z10,z5,z6]),(0,[z631,z1,z2,z4,z5,z77]),(0,[z0,z1,z2,z131,z5,z6]),(0,[z829,z1,z2,z10,z5,z6]),(0,[z112,z0,z1,z427,z10,z6])],[(0,[z0,z1,z2,z10,z830,z6]),(0,[z0,z1,z2,z831,z5,z6]),(0,[z0,z1,z2,z832,z5,z6]),(0,[z0,z1,z2,z118,z6,z95])],[(0,[z0,z1,z2,z833,z5,z6]),(0,[z0,z1,z834,z2,z5,z6]),(0,[z109,z1,z2,z4,z5,z110]),(0,[z0,z1,z835,z10,z5,z6]),(0,[z0,z1,z836,z2,z5,z6])],[(0,[z0,z1,z2,z10,z342,z6]),(0,[z0,z1,z837,z2,z10,z6])],[(0,[z1,z2,z208,z5,z77,z6]),(0,[z0,z1,z2,z10,z838,z6]),(0,[z0,z1,z331,z2,z5,z6])],[(0,[z0,z1,z839,z10,z5,z6]),(0,[z0,z246,z181,z10,z5,z6])],[(0,[z57,z0,z45,z7,z5,z6]),(0,[z0,z1,z385,z275,z5,z6]),(0,[z596,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z189,z5,z61])],[(0,[z458,z75,z2,z10,z5,z6]),(0,[z109,z1,z2,z10,z480,z110]),(0,[z0,z1,z2,z840,z5,z6]),(0,[z0,z133,z2,z152,z5,z6]),(0,[z841,z1,z2,z10,z5,z6])]],
   [[(0,[z109,z1,z2,z842,z5,z6]),(0,[z0,z246,z2,z378,z5,z6])],[(0,[z0,z1,z2,z4,z342,z6]),(0,[z0,z1,z2,z843,z10,z5]),(0,[z0,z44,z668,z10,z5,z6])],[(0,[z0,z1,z2,z359,z5,z6])],[(0,[z0,z1,z2,z10,z5,z844]),(0,[z0,z1,z2,z845,z5,z6]),(0,[z0,z1,z2,z131,z480,z6]),(0,[z0,z1,z846,z2,z5,z6]),(0,[z0,z1,z21,z3,z10,z6])],[(0,[z695,z1,z2,z4,z5,z6]),(0,[z160,z0,z246,z2,z10,z5]),(0,[z109,z1,z2,z10,z5,z847]),(0,[z848,z0,z1,z2,z10,z5]),(0,[z0,z1,z60,z5,z797,z6]),(0,[z0,z849,z1,z2,z5,z6])],[(0,[z0,z1,z2,z10,z850,z6]),(0,[z251,z1,z2,z7,z5,z6]),(0,[z0,z1,z194,z84,z2,z6])],[(0,[z0,z1,z2,z10,z5,z851]),(0,[z0,z1,z2,z852,z5,z6]),(0,[z32,z1,z2,z10,z5,z6]),(0,[z109,z494,z2,z10,z5,z110]),(0,[z0,z1,z2,z853,z5,z6]),(0,[z32,z1,z2,z350,z5,z6])],[(0,[z0,z1,z2,z854,z5,z6]),(1,[z0,z772,z10,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z6,z483]),(0,[z0,z1,z126,z7,z22,z6]),(0,[z0,z1,z2,z855,z5,z6]),(0,[z58,z0,z329,z2,z5,z6]),(0,[z0,z1,z537,z10,z5,z103])],[(0,[z0,z1,z271,z378,z5,z6])],[(0,[z0,z856,z2,z10,z5,z6]),(0,[z0,z1,z2,z857,z5,z6]),(0,[z481,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z748]),(0,[z0,z494,z2,z131,z5,z6]),(0,[z858,z1,z2,z10,z5,z6]),(0,[z0,z11,z2,z442,z5,z12]),(0,[z0,z1,z2,z859,z5,z6])],[(0,[z0,z1,z2,z10,z860,z6]),(0,[z1,z70,z722,z10,z5,z6]),(0,[z861,z1,z2,z10,z5,z6]),(0,[z0,z2,z10,z717,z31,z6])],[(0,[z0,z1,z2,z380,z5,z6]),(0,[z32,z1,z2,z4,z5,z6]),(0,[z0,z2,z7,z5,z199,z6]),(0,[z0,z1,z810,z2,z5,z6])],[(0,[z0,z1,z862,z2,z10,z5]),(0,[z0,z1,z2,z7,z5,z863]),(0,[z0,z2,z359,z5,z199,z6])],[(0,[z0,z1,z2,z10,z864,z6]),(0,[z0,z1,z2,z865,z5,z6]),(0,[z0,z1,z124,z5,z6,z139]),(0,[z0,z1,z866,z2,z5,z6]),(0,[z867,z0,z2,z10,z5,z6])],[(0,[z69,z1,z70,z7,z5,z6]),(0,[z0,z1,z21,z3,z4,z6]),(0,[z0,z1,z2,z868,z5,z6]),(0,[z0,z1,z194,z2,z5,z6]),(0,[z0,z1,z869,z2,z5,z6]),(0,[z0,z1,z2,z870,z5,z6]),(0,[z0,z2,z10,z111,z717,z6]),(0,[z0,z1,z2,z871,z5,z6]),(0,[z0,z1,z59,z2,z764,z6])]],
   [[(0,[z0,z1,z2,z872,z5,z6]),(0,[z69,z1,z70,z283,z5,z6]),(0,[z0,z1,z151,z2,z5,z8]),(0,[z873,z1,z2,z10,z5,z6]),(0,[z196,z0,z2,z359,z5,z6])],[(1,[z1,z2,z712,z5,z6]),(0,[z0,z1,z13,z2,z5,z8]),(0,[z874,z1,z2,z10,z5,z6])],[(0,[z56,z1,z2,z4,z80,z6]),(0,[z0,z2,z10,z5,z803,z12]),(0,[z0,z1,z204,z2,z5,z6])],[(0,[z16,z0,z1,z54,z2,z5]),(0,[z0,z9,z2,z10,z111,z6]),(1,[z0,z1,z5,z797,z6])],[(0,[z100,z1,z71,z452,z5,z6]),(0,[z0,z731,z1,z2,z4,z5]),(0,[z0,z875,z2,z10,z5,z6]),(0,[z0,z876,z2,z10,z5,z6]),(0,[z16,z0,z1,z810,z2,z5])],[(0,[z100,z1,z71,z10,z5,z6]),(0,[z0,z1,z2,z877,z5,z6]),(0,[z0,z1,z2,z207,z5,z6]),(0,[z0,z1,z2,z7,z5,z878]),(0,[z0,z1,z2,z879,z5,z6])],[(0,[z91,z75,z2,z7,z5,z6]),(0,[z0,z1,z880,z2,z5,z6])],[(0,[z0,z1,z881,z10,z5,z6]),(0,[z136,z0,z1,z97,z2,z4]),(0,[z0,z1,z138,z2,z5,z8]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z0,z1,z883,z2,z5,z6])]],
   [[(0,[z0,z1,z2,z884,z5,z6]),(0,[z109,z1,z2,z4,z5,z14]),(0,[z109,z0,z1,z2,z442,z5]),(0,[z0,z1,z2,z885,z5,z6]),(0,[z0,z1,z126,z733,z10,z6])],[(0,[z1,z2,z4,z5,z77,z6]),(0,[z0,z9,z2,z4,z111,z6])],[(0,[z1,z2,z15,z4,z5,z77]),(0,[z0,z1,z886,z2,z5,z6]),(0,[z0,z1,z2,z887,z5,z6]),(0,[z1,z2,z10,z80,z888,z6]),(0,[z0,z1,z181,z10,z342,z6]),(0,[z32,z1,z59,z2,z5,z6])],[(0,[z100,z1,z71,z4,z5,z6]),(0,[z136,z0,z1,z97,z2,z7]),(0,[z0,z1,z2,z889,z5,z6]),(0,[z890,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z891,z5,z6])],[(0,[z0,z1,z2,z892,z5,z6]),(0,[z606,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z30,z5,z8]),(0,[z0,z1,z893,z2,z5,z6]),(0,[z0,z2,z807,z10,z5,z6]),(0,[z0,z894,z2,z10,z5,z6])],[(0,[z458,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z378,z342,z6]),(0,[z0,z9,z1,z427,z10,z6]),(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z1,z126,z51,z10,z22])],[(0,[z448,z1,z2,z4,z5,z6]),(0,[z130,z1,z54,z2,z10,z5]),(0,[z165,z0,z2,z525,z5,z6])],[(0,[z0,z1,z427,z10,z5,z6]),(0,[z58,z0,z2,z254,z5,z6]),(0,[z0,z427,z10,z111,z5,z6])]],
   [[(0,[z55,z1,z2,z10,z137,z6]),(0,[z0,z1,z2,z896,z5,z6])],[(0,[z0,z1,z722,z10,z5,z6]),(0,[z1,z2,z10,z5,z6,z897])],[(0,[z0,z1,z898,z2,z5,z6]),(0,[z1,z2,z10,z5,z888,z6]),(0,[z0,z1,z2,z899,z5,z6])],[(0,[z0,z296,z1,z2,z10,z5]),(0,[z130,z1,z2,z7,z5,z8]),(0,[z160,z0,z697,z2,z10,z5]),(0,[z0,z1,z900,z10,z5,z6])],[(0,[z91,z75,z2,z142,z5,z6]),(0,[z0,z1,z2,z10,z5,z901]),(0,[z69,z1,z722,z10,z5,z6]),(0,[z0,z1,z2,z902,z5,z6])],[(0,[z0,z1,z2,z903,z5,z6]),(0,[z0,z1,z427,z4,z5,z6]),(0,[z33,z1,z2,z10,z80,z6]),(0,[z160,z0,z2,z10,z5,z803])],[(0,[z55,z1,z2,z4,z137,z6]),(0,[z0,z1,z271,z7,z5,z6]),(0,[z56,z1,z2,z10,z888,z6])],[(0,[z709,z64,z2,z10,z5,z6]),(0,[z0,z1,z2,z118,z6,z299]),(0,[z0,z1,z175,z59,z2,z6])]],
   [[(0,[z523,z1,z2,z4,z5,z6])],[(0,[z63,z64,z2,z99,z5,z6]),(0,[z0,z1,z2,z904,z5,z6]),(0,[z0,z1,z2,z905,z5,z6]),(0,[z0,z1,z2,z906,z5,z6]),(0,[z0,z1,z2,z10,z5,z173])],[(0,[z0,z1,z2,z452,z5,z6]),(0,[z907,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z908,z10,z6]),(0,[z909,z1,z2,z10,z5,z6]),(0,[z16,z32,z1,z13,z2,z5])],[(0,[z0,z1,z2,z10,z5,z6]),(0,[z568,z1,z2,z10,z137,z6]),(1,[z1,z2,z10,z5,z847]),(0,[z57,z0,z466,z10,z5,z6]),(1,[z196,z0,z126,z10,z6]),(0,[z0,z1,z2,z910,z5,z6])],[(0,[z0,z1,z2,z10,z5,z911]),(0,[z0,z246,z2,z10,z480,z6]),(0,[z0,z1,z2,z912,z5,z6]),(0,[z0,z1,z913,z10,z5,z6]),(0,[z0,z1,z914,z2,z5,z6])],[(0,[z0,z1,z2,z10,z915,z6]),(0,[z0,z1,z295,z10,z5,z6]),(0,[z0,z1,z126,z204,z22,z6])],[(0,[z0,z1,z916,z10,z5,z6]),(0,[z57,z0,z308,z45,z5,z6])],[(0,[z313,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z173]),(0,[z0,z1,z2,z917,z5,z6])]],
   [[(0,[z1,z2,z10,z888,z137,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z200,z2,z10,z5,z12]),(0,[z0,z1,z288,z10,z5,z103]),(0,[z0,z305,z2,z141,z5,z6]),(0,[z1,z176,z2,z4,z5,z6]),(0,[z0,z1,z2,z918,z5,z6]),(0,[z0,z1,z2,z919,z5,z6]),(0,[z0,z1,z2,z10,z5,z920])],[(0,[z0,z1,z2,z921,z5,z6]),(0,[z0,z1,z810,z2,z5,z61])],[(0,[z0,z1,z295,z4,z5,z6]),(0,[z109,z1,z2,z7,z5,z110]),(0,[z0,z1,z150,z2,z7,z6])],[(0,[z0,z1,z2,z525,z5,z8]),(0,[z55,z1,z2,z366,z137,z6]),(0,[z0,z1,z21,z154,z10,z6]),(0,[z16,z0,z1,z2,z5,z287])],[(0,[z0,z1,z922,z2,z5,z6]),(0,[z0,z631,z1,z180,z2,z5]),(0,[z0,z1,z2,z923,z5,z6]),(0,[z16,z0,z1,z13,z2,z5])],[(0,[z0,z1,z2,z10,z5,z924]),(0,[z0,z1,z2,z925,z5,z6]),(0,[z0,z1,z2,z10,z480,z6]),(0,[z112,z0,z2,z10,z31,z6])],[]],
   [[(0,[z18,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z51,z5]),(0,[z112,z0,z295,z10,z31,z6]),(1,[z0,z1,z733,z10,z6])],[(0,[z0,z44,z29,z10,z5,z6]),(0,[z196,z0,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z926,z6]),(0,[z0,z1,z2,z927,z5,z6]),(0,[z928,z0,z1,z2,z51,z5]),(0,[z0,z1,z2,z929,z5,z6])],[(0,[z0,z1,z767,z2,z10,z5]),(0,[z0,z1,z2,z930,z5,z6]),(0,[z0,z1,z138,z599,z5,z6])],[(0,[z0,z931,z1,z2,z10,z5]),(0,[z0,z1,z2,z932,z10,z5]),(0,[z0,z1,z2,z510,z6,z299])],[(0,[z0,z1,z2,z4,z480,z6]),(0,[z112,z0,z2,z4,z31,z6]),(0,[z1,z2,z4,z5,z6,z96]),(0,[z0,z494,z271,z10,z5,z6]),(0,[z0,z1,z933,z10,z5,z6]),(0,[z0,z11,z2,z67,z5,z12]),(1,[z0,z1,z745,z2,z10])],[(0,[z0,z1,z2,z934,z5,z6]),(0,[z1,z2,z7,z567,z5,z6]),(0,[z58,z0,z320,z2,z5,z6])],[(0,[z0,z1,z2,z935,z5,z6]),(0,[z0,z1,z2,z10,z5,z803])],[(0,[z0,z1,z2,z366,z5,z6]),(0,[z0,z44,z29,z4,z5,z6]),(0,[z196,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z15,z5,z61]),(0,[z0,z1,z936,z2,z5,z6])]],
   [[(0,[z1,z2,z10,z5,z6,z937]),(0,[z0,z1,z745,z2,z10,z5])],[(0,[z0,z44,z1,z84,z10,z6]),(0,[z0,z1,z938,z2,z5,z6]),(0,[z94,z0,z1,z770,z10,z5])],[(0,[z0,z939,z2,z10,z5,z6]),(0,[z0,z1,z940,z2,z5,z6]),(0,[z0,z1,z223,z487,z5,z6]),(0,[z0,z1,z2,z941,z5,z6]),(0,[z0,z1,z942,z10,z5,z6])],[(0,[z0,z1,z2,z943,z5,z6]),(0,[z0,z1,z273,z156,z10,z5])],[(0,[z0,z1,z2,z944,z5,z6]),(0,[z1,z225,z2,z4,z5,z6]),(0,[z626,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z945,z5,z6])],[(0,[z0,z322,z2,z30,z5,z6]),(0,[z32,z1,z2,z7,z5,z6]),(0,[z94,z0,z1,z156,z10,z5])],[(0,[z0,z1,z2,z946,z5,z6]),(0,[z0,z1,z947,z2,z5,z6]),(0,[z0,z1,z2,z51,z744,z5]),(0,[z0,z1,z2,z948,z5,z6])],[(0,[z0,z1,z949,z10,z5,z6]),(0,[z0,z1,z2,z950,z5,z6]),(0,[z0,z951,z2,z10,z5,z6])]],
   [[(0,[z952,z1,z2,z10,z5,z6]),(0,[z32,z1,z13,z2,z5,z6])],[(0,[z0,z1,z2,z953,z5,z6]),(0,[z0,z1,z954,z2,z5,z6]),(0,[z0,z1,z2,z955,z5,z6])],[(0,[z0,z1,z181,z10,z5,z6]),(0,[z0,z1,z2,z956,z5,z6])],[(0,[z63,z709,z2,z10,z5,z6]),(0,[z0,z1,z957,z2,z5,z6])],[(0,[z0,z1,z2,z10,z5,z958]),(0,[z0,z1,z2,z959,z5,z6]),(0,[z0,z1,z960,z10,z5,z6]),(1,[z1,z2,z10,z888,z6]),(0,[z0,z1,z2,z961,z5,z6]),(0,[z0,z1,z2,z962,z5,z6])],[(0,[z0,z1,z2,z378,z5,z6]),(0,[z0,z1,z2,z118,z5,z8]),(0,[z0,z1,z3,z733,z10,z6])],[(0,[z0,z1,z54,z2,z5,z8]),(0,[z0,z1,z2,z963,z5,z6]),(0,[z0,z1,z2,z964,z5,z6]),(0,[z0,z1,z2,z965,z5,z6])],[(0,[z0,z1,z2,z966,z5,z6]),(0,[z0,z1,z2,z967,z5,z6]),(0,[z414,z1,z71,z10,z5,z6]),(0,[z56,z1,z2,z10,z80,z6]),(0,[z968,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z969,z5,z6])]],
   [[(0,[z0,z1,z2,z159,z5,z6]),(0,[z0,z1,z181,z4,z5,z6]),(0,[z0,z494,z2,z10,z342,z6]),(0,[z1,z2,z10,z5,z77,z847]),(0,[z0,z1,z970,z2,z5,z6])],[(0,[z0,z1,z3,z10,z319,z6])],[(0,[z0,z1,z971,z2,z5,z6]),(0,[z0,z9,z2,z7,z111,z6]),(0,[z0,z1,z2,z972,z5,z6])],[(0,[z278,z1,z2,z4,z5,z6]),(0,[z0,z1,z973,z10,z5,z6]),(0,[z0,z1,z974,z2,z5,z6])],[(0,[z100,z1,z71,z7,z5,z6]),(0,[z1,z2,z4,z5,z647,z6]),(0,[z0,z1,z2,z764,z6,z95])],[(0,[z0,z1,z2,z975,z10,z6]),(0,[z0,z1,z2,z976,z5,z6]),(0,[z109,z1,z2,z10,z5,z14]),(0,[z531,z1,z2,z4,z5,z6]),(0,[z0,z1,z181,z10,z480,z6]),(0,[z109,z1,z375,z2,z10,z5]),(0,[z0,z1,z977,z2,z5,z6]),(0,[z0,z2,z10,z5,z717,z6]),(0,[z196,z0,z21,z2,z10,z6])],[(0,[z0,z200,z1,z2,z7,z5]),(0,[z0,z1,z2,z978,z5,z6]),(0,[z0,z1,z979,z2,z5,z6]),(0,[z0,z1,z2,z48,z5,z6]),(0,[z0,z1,z54,z2,z5,z61]),(0,[z0,z1,z97,z505,z2,z10])],[]],
   [[(0,[z0,z1,z980,z10,z5,z6]),(0,[z0,z1,z981,z4,z5,z6]),(0,[z0,z1,z2,z304,z6,z95]),(0,[z0,z1,z2,z378,z480,z6]),(0,[z0,z1,z2,z982,z5,z6])],[(0,[z0,z29,z772,z10,z5,z6]),(0,[z0,z1,z2,z983,z5,z6])],[(1,[z709,z2,z10,z5,z6]),(0,[z568,z1,z2,z4,z5,z6]),(0,[z25,z1,z2,z10,z5,z77])],[(0,[z109,z1,z53,z2,z10,z5]),(0,[z0,z1,z984,z2,z5,z6]),(0,[z0,z1,z2,z985,z5,z6]),(0,[z0,z1,z770,z10,z5,z6])],[(0,[z0,z1,z2,z10,z986,z6]),(0,[z0,z494,z181,z10,z5,z6]),(0,[z57,z0,z772,z10,z5,z6]),(0,[z0,z1,z427,z107,z5,z6])],[(0,[z0,z1,z987,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z988]),(0,[z0,z1,z308,z2,z5,z6]),(0,[z989,z1,z2,z10,z5,z6])],[(0,[z75,z709,z2,z10,z5,z6]),(0,[z109,z246,z2,z4,z5,z6]),(0,[z0,z990,z2,z10,z5,z6]),(0,[z991,z1,z2,z10,z5,z6]),(0,[z0,z1,z745,z2,z10,z72])],[(0,[z63,z64,z2,z36,z5,z6]),(0,[z1,z2,z317,z4,z5,z6]),(0,[z55,z1,z2,z7,z137,z6]),(0,[z0,z494,z2,z378,z5,z6]),(0,[z0,z1,z102,z770,z10,z5])]],
   [[(0,[z25,z1,z2,z4,z5,z77]),(0,[z0,z246,z2,z7,z5,z6]),(0,[z0,z1,z2,z152,z5,z8]),(0,[z992,z1,z2,z10,z5,z6]),(0,[z0,z1,z733,z10,z5,z6])],[(0,[z993,z0,z2,z10,z5,z6]),(0,[z0,z1,z54,z2,z7,z5]),(0,[z0,z1,z2,z510,z5,z8])],[(0,[z165,z0,z2,z254,z5,z6]),(0,[z0,z1,z2,z10,z5,z994]),(0,[z0,z1,z2,z995,z5,z6]),(0,[z0,z1,z2,z10,z5,z996]),(0,[z0,z1,z2,z997,z5,z6])],[(0,[z0,z1,z84,z2,z7,z6]),(0,[z0,z1,z2,z7,z5,z901]),(0,[z0,z1,z2,z10,z799,z5]),(0,[z0,z1,z2,z10,z998,z6])],[(0,[z0,z1,z999,z2,z5,z6]),(0,[z0,z1000,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z1001,z6]),(0,[z0,z1,z151,z5,z6,z259]),(0,[z57,z0,z84,z10,z5,z6])],[(0,[z0,z1,z2,z1002,z5,z6]),(0,[z0,z1,z2,z1003,z5,z6]),(0,[z0,z1,z772,z10,z5,z6]),(0,[z0,z1,z2,z1004,z5,z6])],[(0,[z0,z1,z379,z198,z2,z6]),(0,[z0,z1,z2,z10,z5,z1005]),(1,[z112,z0,z427,z10,z6])],[(0,[z109,z1,z271,z4,z5,z6]),(0,[z1,z640,z2,z7,z5,z6])]],
   [[(0,[z501,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1006,z5,z6])],[(0,[z0,z1,z1007,z10,z5,z6]),(0,[z0,z1,z2,z10,z5,z1008]),(0,[z0,z1009,z2,z10,z5,z6]),(0,[z0,z1,z2,z10,z1010,z6]),(0,[z57,z0,z150,z45,z10,z6]),(0,[z0,z29,z10,z5,z609,z6]),(0,[z0,z1,z2,z1011,z5,z6])],[(0,[z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z1012,z2,z5,z6]),(0,[z0,z1,z2,z1013,z5,z6]),(0,[z0,z1,z2,z10,z1014,z6]),(0,[z688,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z10,z1015,z6]),(0,[z0,z1,z2,z1016,z5,z6]),(0,[z0,z432,z2,z254,z5,z6])],[(0,[z0,z1,z2,z283,z5,z6]),(0,[z0,z1,z2,z1017,z5,z6]),(0,[z0,z1,z2,z7,z5,z911]),(0,[z0,z1,z138,z5,z6,z259]),(0,[z0,z1,z2,z1018,z5,z6]),(0,[z0,z1,z2,z1019,z5,z6]),(0,[z0,z1,z2,z10,z241,z72])],[(0,[z0,z1,z295,z7,z5,z6]),(0,[z0,z1,z181,z378,z5,z6]),(0,[z0,z133,z517,z2,z5,z6])],[(0,[z0,z1,z2,z1020,z5,z6]),(0,[z1,z2,z350,z4,z5,z6]),(0,[z0,z1,z1021,z2,z5,z6]),(0,[z0,z1,z1022,z10,z5,z6]),(0,[z112,z0,z427,z10,z31,z6])],[(0,[z0,z1,z2,z1023,z5,z6])],[(0,[z0,z1,z2,z245,z5,z6]),(0,[z531,z16,z1,z13,z2,z5])]],
   [[(0,[z0,z1,z739,z2,z10,z5]),(0,[z0,z1,z2,z712,z5,z6]),(0,[z582,z1,z2,z4,z5,z6]),(0,[z0,z772,z45,z10,z5,z6])],[(0,[z0,z1,z2,z1024,z5,z6]),(0,[z363,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z241,z72]),(0,[z369,z1,z2,z7,z5,z6]),(0,[z531,z1,z2,z378,z5,z6])],[(0,[z0,z296,z1,z2,z4,z5]),(0,[z196,z0,z126,z10,z5,z6]),(0,[z0,z1,z2,z496,z5,z61]),(0,[z136,z0,z1,z97,z2,z267])],[(0,[z0,z1,z2,z1025,z5,z6]),(0,[z0,z1,z1026,z2,z5,z6]),(1,[z1,z54,z2,z4,z5]),(0,[z446,z0,z2,z285,z5,z6]),(0,[z0,z1,z2,z378,z5,z61]),(0,[z0,z1,z13,z810,z2,z5]),(0,[z136,z0,z1,z745,z2,z10])],[(0,[z0,z1,z2,z10,z1027,z6])],[(0,[z0,z1,z2,z7,z5,z924]),(0,[z1028,z1,z2,z10,z5,z6]),(0,[z0,z1,z76,z5,z797,z6]),(0,[z0,z1,z102,z10,z5,z103]),(0,[z0,z1,z2,z267,z5,z6])],[(0,[z1,z722,z71,z10,z5,z6]),(0,[z0,z2,z10,z5,z1029,z6]),(0,[z0,z1,z2,z1030,z5,z6]),(0,[z1,z375,z2,z4,z5,z6]),(0,[z1,z2,z10,z5,z847,z110]),(0,[z0,z1,z810,z2,z496,z5])],[(0,[z0,z1,z276,z2,z5,z8]),(0,[z25,z1,z2,z336,z5,z77]),(0,[z16,z0,z1,z470,z2,z5]),(0,[z112,z0,z495,z2,z10,z6]),(0,[z0,z1,z2,z5,z797,z6])]],
   [[(0,[z0,z1,z1031,z10,z5,z6]),(0,[z0,z44,z29,z7,z5,z6]),(0,[z196,z0,z2,z7,z5,z6]),(0,[z0,z1,z2,z254,z5,z8])],[(0,[z0,z200,z246,z2,z10,z5]),(0,[z0,z1,z1032,z2,z5,z6]),(0,[z605,z1,z2,z4,z5,z6]),(0,[z0,z1,z1033,z2,z5,z6]),(0,[z0,z1,z2,z1034,z5,z6])],[(0,[z0,z1,z1035,z10,z5,z6]),(0,[z47,z0,z1,z54,z2,z5]),(0,[z0,z1,z60,z2,z5,z8]),(0,[z56,z1,z2,z48,z80,z6])],[(0,[z0,z1036,z2,z10,z5,z6]),(0,[z109,z1,z2,z4,z342,z6]),(0,[z0,z1,z102,z4,z5,z103]),(0,[z0,z1,z1037,z2,z5,z6])],[(0,[z0,z1,z2,z1038,z5,z6]),(0,[z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z10,z717,z6]),(0,[z0,z1,z2,z1039,z5,z6]),(0,[z0,z1,z2,z770,z10,z5])],[(0,[z0,z1,z2,z1040,z5,z6]),(0,[z0,z1,z124,z5,z6,z588]),(0,[z0,z1,z2,z7,z342,z6]),(0,[z0,z1,z2,z1041,z5,z6]),(0,[z0,z1,z2,z10,z5,z1042])],[(0,[z1,z396,z2,z4,z5,z6]),(0,[z109,z1,z2,z131,z5,z110]),(0,[z0,z1,z107,z295,z5,z6]),(0,[z0,z11,z2,z10,z5,z12])],[(0,[z55,z1,z2,z335,z137,z6]),(0,[z0,z2,z254,z807,z5,z6]),(0,[z112,z0,z427,z10,z5,z6]),(0,[z0,z1043,z2,z10,z5,z6]),(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z770,z10,z5,z103])]],
   [[(0,[z0,z494,z2,z10,z5,z6]),(0,[z0,z1,z1045,z2,z10,z6]),(0,[z0,z1,z1035,z4,z5,z6]),(0,[z0,z1,z2,z1046,z10,z5])],[(0,[z0,z1,z385,z2,z5,z8]),(0,[z1,z2,z699,z7,z5,z6])],[(0,[z0,z1,z2,z10,z1047,z6]),(0,[z33,z1,z2,z4,z5,z6])],[(0,[z0,z11,z246,z2,z10,z5]),(0,[z112,z57,z0,z126,z10,z6]),(0,[z0,z1,z2,z1048,z5,z6]),(0,[z0,z1,z2,z1049,z5,z6])],[(0,[z0,z1,z758,z2,z10,z6]),(0,[z0,z11,z2,z4,z5,z12]),(0,[z0,z1,z2,z1050,z5,z6]),(0,[z0,z1,z2,z764,z10,z6])],[(0,[z0,z1051,z1,z2,z10,z5]),(0,[z0,z1,z2,z10,z5,z1052]),(0,[z0,z1,z1053,z2,z5,z6]),(0,[z0,z1,z2,z1054,z5,z6])],[(0,[z0,z1,z2,z1055,z5,z6]),(0,[z0,z494,z2,z4,z5,z6]),(0,[z0,z1,z2,z842,z5,z6]),(0,[z0,z1,z2,z15,z5,z14]),(0,[z0,z1,z2,z1056,z5,z6]),(0,[z55,z1,z2,z10,z888,z6]),(0,[z0,z1,z1057,z10,z5,z6])],[(0,[z0,z1,z2,z740,z5,z6]),(0,[z109,z1,z181,z4,z5,z6]),(0,[z0,z1,z2,z1058,z5,z6]),(0,[z57,z0,z666,z10,z5,z6]),(0,[z0,z1,z1059,z2,z10,z6]),(0,[z0,z1,z1060,z10,z5,z6])]],
   [[(0,[z0,z1,z2,z1061,z10,z5]),(0,[z0,z1,z1062,z2,z5,z6]),(0,[z0,z133,z2,z472,z5,z6])],[(0,[z0,z1,z2,z1063,z5,z6]),(0,[z0,z1,z181,z7,z5,z6])],[(0,[z0,z1,z2,z335,z5,z6]),(0,[z0,z1,z2,z10,z5,z847]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z0,z1,z2,z764,z5,z6])],[(0,[z0,z1,z2,z1065,z5,z6]),(0,[z0,z1,z2,z10,z5,z863]),(0,[z0,z1,z2,z336,z5,z6]),(0,[z1,z274,z2,z7,z5,z6]),(0,[z0,z494,z2,z10,z480,z6]),(0,[z1,z2,z10,z5,z6,z847]),(0,[z0,z1,z2,z10,z1066,z6]),(0,[z0,z1,z2,z764,z118,z6])],[(0,[z0,z1,z2,z10,z5,z1067]),(0,[z0,z1,z2,z10,z5,z8]),(0,[z1068,z1,z2,z10,z5,z6])],[(0,[z0,z1,z1069,z2,z5,z6]),(1,[z0,z2,z807,z5,z6])],[(0,[z109,z11,z1,z2,z4,z5]),(0,[z56,z1,z2,z7,z80,z6]),(0,[z0,z1,z1070,z10,z5,z6]),(0,[z0,z1,z2,z1071,z5,z6]),(0,[z0,z1072,z2,z10,z5,z6])],[(0,[z1,z2,z4,z5,z158,z6]),(0,[z476,z1,z2,z7,z5,z6]),(0,[z0,z1,z156,z770,z10,z5])]],
   [[(0,[z0,z1,z2,z1073,z5,z6]),(0,[z0,z1,z1074,z10,z5,z6]),(0,[z0,z1,z1075,z2,z5,z6])],[(0,[z1,z2,z842,z4,z5,z6]),(0,[z0,z1,z2,z1076,z5,z6]),(0,[z32,z1,z138,z2,z5,z6]),(0,[z0,z1,z2,z1077,z5,z6])],[(0,[z531,z1,z2,z10,z5,z6]),(0,[z0,z1,z2,z4,z5,z8]),(0,[z443,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1078,z5,z6])],[(0,[z0,z1,z2,z1079,z5,z6]),(0,[z63,z296,z64,z2,z10,z5]),(0,[z0,z1,z2,z10,z5,z878]),(0,[z91,z75,z2,z280,z5,z6]),(0,[z0,z1,z1080,z2,z5,z6]),(0,[z25,z1,z2,z208,z5,z77])],[(0,[z94,z0,z1,z156,z4,z5])],[(0,[z0,z1,z981,z10,z5,z6]),(0,[z0,z1,z2,z1081,z5,z6])],[(0,[z0,z1,z2,z1082,z5,z6]),(0,[z0,z1083,z2,z10,z5,z6]),(0,[z284,z1,z2,z4,z5,z6]),(0,[z0,z2,z10,z5,z199,z6])],[(0,[z0,z1,z117,z276,z2,z6]),(0,[z0,z1084,z2,z10,z5,z6]),(0,[z0,z1,z2,z1085,z5,z6]),(0,[z0,z1,z2,z118,z279,z6]),(0,[z1086,z0,z2,z10,z5,z6]),(0,[z136,z0,z1,z97,z2,z98])]],
   [[(0,[z0,z1,z2,z1087,z5,z6]),(0,[z0,z1,z2,z10,z5,z773]),(0,[z0,z1,z150,z2,z10,z6]),(0,[z0,z546,z2,z152,z5,z6])],[(0,[z0,z1,z60,z487,z5,z6]),(0,[z25,z1,z2,z7,z5,z77]),(0,[z57,z0,z84,z45,z10,z6]),(0,[z112,z0,z2,z10,z717,z6])],[(0,[z1,z709,z2,z10,z5,z6]),(0,[z0,z246,z271,z10,z5,z6]),(0,[z0,z1,z126,z10,z608,z6]),(0,[z0,z1,z150,z308,z2,z6]),(0,[z0,z1,z2,z1088,z5,z6])],[(0,[z0,z1,z1089,z10,z5,z6])],[(0,[z0,z1,z2,z843,z7,z5]),(0,[z0,z1,z2,z1090,z5,z6])],[(0,[z0,z1,z13,z2,z378,z5]),(1,[z0,z2,z10,z5,z803])],[(0,[z0,z1,z2,z10,z1091,z6]),(0,[z0,z1,z1092,z2,z5,z6]),(0,[z0,z1,z21,z3,z7,z6]),(0,[z302,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z1093,z5,z6])],[(0,[z0,z1,z2,z1094,z5,z6]),(0,[z0,z1,z2,z1095,z5,z6]),(0,[z16,z0,z1,z2,z457,z5])]],
   [[(0,[z0,z1,z2,z1096,z5,z6]),(0,[z0,z1,z2,z1097,z5,z6]),(0,[z0,z1,z126,z359,z22,z6]),(0,[z0,z1,z21,z733,z10,z6])],[(0,[z0,z1,z2,z10,z1098,z6]),(0,[z0,z1,z2,z1099,z5,z6]),(0,[z0,z1,z427,z7,z5,z6]),(0,[z0,z1,z2,z7,z5,z994]),(0,[z0,z1,z37,z276,z2,z6]),(0,[z0,z1,z2,z1100,z5,z6])],[(0,[z405,z64,z2,z10,z5,z6]),(0,[z0,z1,z810,z2,z10,z5])],[(0,[z0,z1,z60,z435,z5,z6]),(0,[z0,z1,z2,z51,z10,z5]),(0,[z0,z1,z2,z1101,z5,z6])],[(0,[z0,z1,z1102,z2,z5,z6]),(0,[z0,z1,z2,z975,z4,z6]),(0,[z1,z2,z347,z7,z5,z6]),(0,[z0,z1,z1103,z2,z10,z6]),(0,[z0,z1,z745,z2,z10,z6])],[(0,[z130,z1,z2,z378,z5,z6])],[(0,[z63,z64,z2,z10,z5,z6]),(0,[z0,z1,z2,z1104,z5,z6])],[(0,[z0,z1,z2,z208,z5,z6]),(0,[z109,z246,z2,z10,z5,z110]),(0,[z1105,z1,z2,z10,z5,z6]),(0,[z1106,z1,z2,z10,z5,z6]),(0,[z0,z2,z10,z5,z161,z803]),(0,[z196,z0,z3,z10,z5,z6])]],
   [[(0,[z0,z1,z427,z220,z5,z6])],[(0,[z0,z1,z1107,z10,z5,z6]),(0,[z25,z1,z2,z10,z5,z847]),(0,[z112,z0,z354,z2,z10,z6]),(0,[z0,z1,z1108,z10,z5,z6]),(0,[z0,z1109,z2,z10,z5,z6])],[],[(0,[z0,z200,z1,z2,z892,z5]),(0,[z1,z2,z4,z5,z229,z6]),(0,[z109,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z5,z173]),(0,[z0,z1,z2,z10,z888,z6]),(0,[z0,z246,z2,z131,z5,z6]),(0,[z0,z1,z2,z1110,z5,z6]),(0,[z0,z2,z10,z5,z803,z6]),(0,[z0,z1,z2,z10,z5,z1111]),(0,[z0,z1,z117,z59,z2,z6])],[(0,[z63,z64,z2,z4,z5,z6]),(0,[z0,z1,z1112,z2,z5,z6]),(0,[z1,z2,z4,z5,z6,z233]),(0,[z0,z1,z126,z466,z10,z6])],[(0,[z0,z1,z2,z10,z1113,z6]),(0,[z0,z1,z2,z496,z5,z8]),(0,[z0,z2,z807,z152,z5,z6]),(0,[z0,z1,z1114,z10,z5,z6]),(0,[z531,z1,z13,z2,z10,z5])],[(0,[z0,z1,z2,z99,z5,z6]),(0,[z928,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z1115,z5,z6]),(0,[z109,z1,z180,z2,z4,z5]),(0,[z0,z1,z2,z51,z4,z5]),(0,[z58,z0,z2,z285,z5,z6])]],
   [[(0,[z109,z1,z271,z10,z5,z110]),(0,[z0,z1,z2,z1116,z5,z6])],[(0,[z313,z1,z2,z712,z5,z6]),(0,[z0,z1,z2,z336,z5,z61]),(0,[z32,z1,z60,z2,z5,z6])],[(0,[z1,z54,z2,z10,z4,z5]),(0,[z0,z1,z1117,z10,z5,z6]),(1,[z57,z0,z84,z10,z6])],[(0,[z344,z1,z2,z4,z5,z6]),(0,[z57,z0,z495,z10,z5,z6]),(0,[z0,z1,z60,z104,z5,z6]),(0,[z0,z1,z2,z1118,z5,z6])],[(0,[z0,z1,z102,z7,z5,z103]),(0,[z0,z1,z271,z131,z5,z6]),(0,[z0,z1,z2,z10,z5,z1119]),(0,[z0,z1,z2,z220,z5,z6]),(0,[z0,z1,z2,z1120,z5,z6])],[(0,[z0,z1,z2,z1121,z5,z6]),(0,[z0,z1,z2,z1122,z5,z6]),(0,[z0,z1,z2,z1123,z5,z6]),(0,[z0,z1,z2,z1124,z5,z6]),(1,[z0,z1,z2,z764,z6])],[(0,[z109,z1,z2,z4,z480,z6]),(0,[z109,z160,z1,z2,z4,z5]),(0,[z0,z1125,z2,z10,z5,z6]),(0,[z0,z1,z2,z1126,z5,z6]),(0,[z0,z1,z2,z698,z5,z61])],[(0,[z100,z1,z722,z10,z5,z6]),(0,[z0,z1,z2,z1127,z5,z6]),(0,[z0,z1,z271,z10,z342,z6]),(0,[z0,z1,z2,z442,z5,z6]),(0,[z0,z1,z138,z5,z6,z139]),(0,[z0,z1,z60,z76,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 538) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 538).take 532) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1070).take 106) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1176)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [538, 532, 106] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 121).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 254).take 2).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [121, 133, 2] = true :=
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

end PEqualNP.Outside.L_meta_42518

theorem PEqualNP.Outside.L_meta_42518 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4240500864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4240500864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42518.solve