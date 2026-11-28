import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36390

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
  Nat.testBit (4278124266 * 2 ^ 32 + 4276944608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01100100509c2310#64 ++ 0x001100100509c231#64 ++ 0xeee88309f1bc273b#64 ++ 0xdeee88309f1bc273#64 : BitVec 256),
   (0x80200412c0052940#64 ++ 0x080200412c005294#64 ++ 0xddd90c36c24f39c7#64 ++ 0xbddd90c36c24f39c#64 : BitVec 256),
   (0x0a403045046040a2#64 ++ 0x90a403045046040a#64 ++ 0xbbbe70c70c70c1ff#64 ++ 0x7bbbe70c70c70c1f#64 : BitVec 256),
   (0x100380a80b009404#64 ++ 0x2100380a80b00940#64 ++ 0x787f80f80f80fe0e#64 ++ 0xf787f80f80f80fe0#64 : BitVec 256),
   (0x2383db000ffa0008#64 ++ 0xc2383db000ffa000#64 ++ 0x07fbff000fff0001#64 ++ 0xf07fbff000fff000#64 : BitVec 256),
   (0x3c03eeffa000000f#64 ++ 0x03c03eeffa000000#64 ++ 0xfffbfffff0000000#64 ++ 0x0fffbfffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x686880080180260a 0xd686880080180260

def z1 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f1bc273b 0xdeee88309f1bc273

def z2 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70c70c1ff 0x7bbbe70c70c70c1f

def z3 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80f80fe0e 0xf787f80f80f80fe0

def z4 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fff0001 0xf07fbff000fff000

def z5 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0000000 0x0fffbfffff000000

def z6 : W := mkw 0x80200412c0052940 0x080200412c005294 0x95910c36c24f19c5 0x295910c36c24f19c

def z7 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x83807007007001f1 0x083807007007001f

def z8 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x4041803803803e00 0x84041803803803e0

def z9 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c24f39c7 0xbddd90c36c24f39c

def z10 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfaff80f90fb0ff3f 0xffaff80f90fb0ff3

def z11 : W := mkw 0x01100100509c2310 0x001100100509c231 0x44408308f18c2600 0x844408308f18c260

def z12 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07807f00007f0001 0x007807f00007f000

def z13 : W := mkw 0x80200412c0052940 0x080200412c005294 0x45d90c30c24f3801 0xb45d90c30c24f380

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x99980006004001c7 0x399980006004001c

def z15 : W := mkw 0x01100100509c2310 0x001100100509c231 0x66608309f1bc2638 0xc66608309f1bc263

def z16 : W := mkw 0x83a01512cfff2940 0xc83a01512cfff294 0xddd90c36cfff39c7 0xfddd90c36cfff39c

def z17 : W := mkw 0xa2a3de128f630848 0xca2a3de128f63084 0x11137c360e4318c4 0x211137c360e4318c

def z18 : W := mkw 0x011001005b9cb710 0x2011001005b9cb71 0x000400000fbcff3f 0xf000400000fbcff3

def z19 : W := mkw 0x2393db005ffe2318 0xc2393db005ffe231 0xeffbff09ffff273b 0xfeffbff09ffff273

def z20 : W := mkw 0x3f83ffffaffa000f 0xc3f83ffffaffa000 0xfffbffffffff0001 0xffffbffffffff000

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88309f0000000 0x0eee88309f000000

def z22 : W := mkw 0x01100100509c2310 0x001100100509c231 0x0000000001bc273b 0xd0000000001bc273

def z23 : W := mkw 0x03c011000ffa40a0 0xd03c011000ffa40a 0x000400000fffc1ff 0xf000400000fffc1f

def z24 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7ffffff80ffffe0f 0xf7ffffff80ffffe0

def z25 : W := mkw 0x3f83ffffaffa940f 0xe3f83ffffaffa940 0xfffffffffffffe0f 0xffffffffffffffe0

def z26 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0xfffef3cffdfce7ff 0xffffef3cffdfce7f

def z27 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x11137cf600000000 0x011137cf60000000

def z28 : W := mkw 0x0110010010980210 0x0011001001098021 0x2220830931b00638 0x42220830931b0063

def z29 : W := mkw 0x8020041280010840 0x0802004128001084 0x11110c36024318c4 0x211110c36024318c

def z30 : W := mkw 0x80200412c0052940 0x080200412c005294 0x85800c06c04f01c1 0x085800c06c04f01c

def z31 : W := mkw 0x100380a800000004 0x0100380a80000000 0x202280c800000000 0x0202280c80000000

def z32 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0222f3000db00000 0x40222f3000db0000

def z33 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87807f07f0000000 0x087807f07f000000

def z34 : W := mkw 0x2383df128ffa0008 0xc2383df128ffa000 0xdffbff36cfff0001 0xfdffbff36cfff000

def z35 : W := mkw 0x0800204500000002 0x0080020450000000 0xfffaf3cff0000000 0x0fffaf3cff000000

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x7879803803803e0e 0xf7879803803803e0

def z37 : W := mkw 0x0b50314514f842b2 0x90b50314514f842b 0xbbbef3cf3df0c7ff 0x7bbbef3cf3df0c7f

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x383e00c00c00c00e 0x7383e00c00c00c00

def z39 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xc7c1ff3ff0000000 0x0c7c1ff3ff000000

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0xeae8800901b0273b 0xdeae8800901b0273

def z41 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd9980036c04039c7 0x3d9980036c04039c

def z42 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0x87fbff07f0000000 0x087fbff07f000000

def z43 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x202680c80d80c608 0x4202680c80d80c60

def z44 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffff80fe0e 0xfffffffffff80fe0

def z45 : W := mkw 0x01100100509c2310 0x001100100509c231 0xea208309f1b0273a 0x4ea208309f1b0273

def z46 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x207f80c80f80c608 0xf207f80c80f80c60

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa800010030013b 0x5aaa800010030013

def z48 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x111670c60c40c0c4 0x2111670c60c40c0c

def z49 : W := mkw 0xa2a3de12cf672948 0xca2a3de12cf67294 0xdddb7c36ce4f39c7 0xbdddb7c36ce4f39c

def z50 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x101700f00f80fe0e 0xf101700f00f80fe0

def z51 : W := mkw 0x2bc3fb450ffa40aa 0xd2bc3fb450ffa40a 0xbfffffc70fffc1ff 0xfbfffffc70fffc1f

def z52 : W := mkw 0x08402045000040a2 0x108402045000040a 0xb80400c70000c1fe 0x0b80400c70000c1f

def z53 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x07fbff0000000000 0x007fbff000000000

def z54 : W := mkw 0x000380000b000000 0x0000380000b00000 0x001300000e000000 0x2001300000e00000

def z55 : W := mkw 0x3d13efffb098021f 0x03d13efffb098021 0xfffbfffff1b00638 0x4fffbfffff1b0063

def z56 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x3fffffc00fffc00f 0xf3fffffc00fffc00

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x81800006004001c1 0x081800006004001c

def z58 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xbbbaf3cf30000000 0x0bbbaf3cf3000000

def z59 : W := mkw 0x0000041280000000 0x0000004128000000 0xddd90c36c0000000 0x0ddd90c36c000000

def z60 : W := mkw 0x100380a800000004 0x0100380a80000000 0x787b80f802003806 0xb787b80f80200380

def z61 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80e00d804 0x2787f80f80e00d80

def z62 : W := mkw 0x80200412c0052940 0x080200412c005294 0xc5c10c36c24f39c1 0x8c5c10c36c24f39c

def z63 : W := mkw 0x000380000b000000 0x0000380000b00000 0x0041800003800000 0x8004180000380000

def z64 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0xddd98c3ec3cf3fc7 0xbddd98c3ec3cf3fc

def z65 : W := mkw 0x3e43faed246040af 0x93e43faed246040a 0x2226f3c93c30c038 0x42226f3c93c30c03

def z66 : W := mkw 0xa3a3df12cfff2948 0xca3a3df12cfff294 0xdffbff36cfff39c7 0xfdffbff36cfff39c

def z67 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x01137c000e430000 0x201137c000e43000

def z68 : W := mkw 0x0200100004600000 0x8020010000460000 0x03ba70000c700001 0x703ba70000c70000

def z69 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x404580380f80fe0e 0xf404580380f80fe0

def z70 : W := mkw 0x0000041280000000 0x0000004128000000 0x85800c06c0000000 0x085800c06c000000

def z71 : W := mkw 0x0010000050042310 0x0001000005004231 0x80000001f0000130 0x080000001f000013

def z72 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0xbbbef0cf0df0c7ff 0x7bbbef0cf0df0c7f

def z73 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff180260a 0xdfffbfffff180260

def z74 : W := mkw 0x0a403045446461a2 0x90a403045446461a 0xfffe70c7cc7ce1ff 0xffffe70c7cc7ce1f

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0x03ba700000000000 0x003ba70000000000

def z76 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0xfddd0cf7c24ff9ff 0xbfddd0cf7c24ff9f

def z77 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x04418f00038f0000 0x804418f00038f000

def z78 : W := mkw 0x3e03feffa460000f 0x83e03feffa460000 0xfffbfffffc700001 0x7fffbfffffc70000

def z79 : W := mkw 0x3283daa80f62940c 0xe3283daa80f62940 0x11177cf00e43d804 0x211177cf00e43d80

def z80 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000db00000 0x407fbff000db0000

def z81 : W := mkw 0x01100100509c2310 0x001100100509c231 0xa6a08309f1bc0739 0x4a6a08309f1bc073

def z82 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07ba7f000c7f0001 0x707ba7f000c7f000

def z83 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0xffff7cf7ce7ff9ff 0xfffff7cf7ce7ff9f

def z84 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd8590036c20039c6 0xbd8590036c20039c

def z85 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0x2222f3c930000000 0x02222f3c93000000

def z86 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0x11137cf6024318c4 0x211137cf6024318c

def z87 : W := mkw 0x0200100004600000 0x8020010000460000 0x011270000c400000 0x2011270000c40000

def z88 : W := mkw 0x3393dba85ffeb71c 0xe3393dba85ffeb71 0xfffffff9ffffff3f 0xffffffff9ffffff3

def z89 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x101700f00e00d804 0x2101700f00e00d80

def z90 : W := mkw 0x3d13effff09c231f 0x03d13effff09c231 0xfffbfffff1bc273b 0xdfffbfffff1bc273

def z91 : W := mkw 0x02401000046040a0 0x902401000046040a 0x000400000c70c1ff 0x7000400000c70c1f

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x5dd90c30024f3807 0xb5dd90c30024f380

def z93 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbbe70c70c00c00e 0x7bbbe70c70c00c00

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x05d90c00024f0001 0xb05d90c00024f000

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0x06e8830000000000 0x006e883000000000

def z96 : W := mkw 0x0000041280000000 0x0000004128000000 0xddd90c36c2003806 0xbddd90c36c200380

def z97 : W := mkw 0x01000100409c2100 0x001000100409c210 0xcee88300c1bc2103 0xdcee88300c1bc210

def z98 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x939670c70c70c1f5 0x2939670c70c70c1f

def z99 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xefe8ff0ff0000000 0x0efe8ff0ff000000

def z100 : W := mkw 0x0000041280000000 0x0000004128000000 0x44410c30c0000000 0x044410c30c000000

def z101 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x03baf3000df00001 0x703baf3000df0000

def z102 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0x7a7bf3f930000000 0x07a7bf3f93000000

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x44408308f0000000 0x044408308f000000

def z104 : W := mkw 0x8020000000010840 0x0802000000001084 0x00000000024318c4 0x200000000024318c

def z105 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x44418f38f0000000 0x044418f38f000000

def z106 : W := mkw 0x9c2024ffe0052947 0x09c2024ffe005294 0xfdd90cfff24f39c7 0xbfdd90cfff24f39c

def z107 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd9110c36c24339c6 0x2d9110c36c24339c

def z108 : W := mkw 0x902004bac005bd44 0x2902004bac005bd4 0xf80400fec000ffce 0x0f80400fec000ffc

def z109 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x07fbff00024f0001 0xb07fbff00024f000

def z110 : W := mkw 0x0110010010980210 0x0011001001098021 0xeee88309f1b00638 0x4eee88309f1b0063

def z111 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0x7c7f8cf8cf8ffe0e 0xf7c7f8cf8cf8ffe0

def z112 : W := mkw 0x000380000b000000 0x0000380000b00000 0x007b80000f800000 0xf007b80000f80000

def z113 : W := mkw 0x0200100004600000 0x8020010000460000 0x3bbe70c00c70c00f 0x73bbe70c00c70c00

def z114 : W := mkw 0x100380a800000004 0x0100380a80000000 0x787b80f800000000 0x0787b80f80000000

def z115 : W := mkw 0x000000000b009400 0x2000000000b00940 0x585d00300f80fe0e 0xf585d00300f80fe0

def z116 : W := mkw 0x0100010000980000 0x0010001000098000 0x06e8830001bc0001 0xd06e8830001bc000

def z117 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0xbbbe70c70dfce7ff 0xfbbbe70c70dfce7f

def z118 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xeeeaf3c9f0000000 0x0eeeaf3c9f000000

def z119 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x782680f80d80fe0e 0x4782680f80d80fe0

def z120 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0xfeff83f9ffbcff3f 0xffeff83f9ffbcff3

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0x000400000c00c00e 0x7000400000c00c00

def z122 : W := mkw 0x01100100509c2310 0x001100100509c231 0xec408309f18c273a 0x8ec408309f18c273

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z124 : W := mkw 0x2113cb00509c2318 0x02113cb00509c231 0xeffbff09f1bc273b 0xdeffbff09f1bc273

def z125 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x05db7c000e4f0001 0xb05db7c000e4f000

def z126 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfefe83c9fdbce73f 0xffefe83c9fdbce73

def z127 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x7c7b8ff8f0000000 0x07c7b8ff8f000000

def z128 : W := mkw 0x3283daa80f62940c 0xe3283daa80f62940 0x797ffcf80fc3fe0e 0xf797ffcf80fc3fe0

def z129 : W := mkw 0x038011000ffa0000 0xc038011000ffa000 0x000000000fff0001 0xf000000000fff000

def z130 : W := mkw 0x3f83ffffaffa000f 0xc3f83ffffaffa000 0xfffbfffffdb00000 0x4fffbfffffdb0000

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x4040800801802600 0x8404080080180260

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x98000006000001c6 0x098000006000001c

def z133 : W := mkw 0x0000041280000000 0x0000004128000000 0xddd90c36c04001c7 0x3ddd90c36c04001c

def z134 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x606780f80f80fe08 0xc606780f80f80fe0

def z135 : W := mkw 0x0000000040042100 0x0000000004004210 0xccc80000c00c2103 0x9ccc80000c00c210

def z136 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xfff98f3ff3ff3fff 0xffff98f3ff3ff3ff

def z137 : W := mkw 0x01100100509c2310 0x001100100509c231 0xaea80301f03c013b 0x5aea80301f03c013

def z138 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffffffff000fe0e 0x0fffffffff000fe0

def z139 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x027bf3000fb00000 0xf027bf3000fb0000

def z140 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07e8ff0001ff0001 0xd07e8ff0001ff000

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x003a00000c000000 0x7003a00000c00000

def z142 : W := mkw 0x100000a800000004 0x0100000a80000000 0x780000f800000000 0x0780000f80000000

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x5859003002003806 0xb585900300200380

def z144 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xa7a2ffcff0000000 0x0a7a2ffcff000000

def z145 : W := mkw 0x1c0024ffa0000007 0x01c0024ffa000000 0xf80000fff0000000 0x0f80000fff000000

def z146 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x17fffff00fffd805 0xf17fffff00fffd80

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0x01110c0002430000 0x201110c000243000

def z148 : W := mkw 0x000000000b009400 0x2000000000b00940 0x000400000f80fe0e 0xf000400000f80fe0

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x86800301f0000000 0x086800301f000000

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x02a8000000300001 0x502a800000030000

def z151 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0xfdff8cfecfcfffcf 0xffdff8cfecfcfffc

def z152 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x784580f80380fe0e 0x8784580f80380fe0

def z153 : W := mkw 0x018001000b9a0000 0x4018001000b9a000 0x00000000038f0000 0x800000000038f000

def z154 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xaffbff010fff013b 0xfaffbff010fff013

def z155 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xefe88f0ff1ff27fb 0xdefe88f0ff1ff27f

def z156 : W := mkw 0x2ac3fa450f6240aa 0xd2ac3fa450f6240a 0x11177cc60e43c0c4 0x211177cc60e43c0c

def z157 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xbbbb7cf700000000 0x0bbbb7cf70000000

def z158 : W := mkw 0x0000000040042100 0x0000000004004210 0x00000000000c2103 0x900000000000c210

def z159 : W := mkw 0xb423cebae005294d 0x0b423cebae005294 0xddd98f3ef24f39c7 0xbddd98f3ef24f39c

def z160 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff04001c7 0x3fffbfffff04001c

def z161 : W := mkw 0x08402045000040a2 0x108402045000040a 0x100400c60000c0c4 0x0100400c60000c0c

def z162 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0xbbbf70f70e70d9ff 0x7bbbf70f70e70d9f

def z163 : W := mkw 0x100000a800009404 0x2100000a80000940 0x780400f80000fe0e 0x0780400f80000fe0

def z164 : W := mkw 0x2bd3fb455ffe63ba 0xd2bd3fb455ffe63b 0xffffffcfffffe7ff 0xfffffffcfffffe7f

def z165 : W := mkw 0x2083ca000b020008 0x42083ca000b02000 0x00010c0002030000 0x000010c000203000

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x1011003002001804 0x2101100300200180

def z167 : W := mkw 0x0010000050042310 0x0001000005004231 0xe8000009f000273a 0x0e8000009f000273

def z168 : W := mkw 0x3e83feffaf62000f 0xc3e83feffaf62000 0xfffbfffffe430000 0x2fffbfffffe43000

def z169 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x222670c10c30c038 0x4222670c10c30c03

def z170 : W := mkw 0x000380000b000000 0x0000380000b00000 0x05fb8c000fcf0001 0xf05fb8c000fcf000

def z171 : W := mkw 0xbc23eeffe005294f 0x0bc23eeffe005294 0xfffbfffff24f39c7 0xbfffbfffff24f39c

def z172 : W := mkw 0x8020041280010840 0x0802004128001084 0x15d90c36024f18c5 0xb15d90c36024f18c

def z173 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0xfbfff0ff0ff0ffff 0xffbfff0ff0ff0fff

def z174 : W := mkw 0x138391a80ffa9404 0xe138391a80ffa940 0x787f80f80ffffe0f 0xf787f80f80ffffe0

def z175 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c00039c6 0x0ddd90c36c00039c

def z176 : W := mkw 0x3c03eaed2b00940f 0x23c03eaed2b00940 0x7a7ff3f93f80fe0e 0xf7a7ff3f93f80fe0

def z177 : W := mkw 0x3f83fbed2ffa000f 0xc3f83fbed2ffa000 0x27fbffc93fff0001 0xf27fbffc93fff000

def z178 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x97937ff7f0000000 0x097937ff7f000000

def z179 : W := mkw 0x3e43feffa46040af 0x93e43feffa46040a 0xfffffffffc70c1ff 0x7fffffffffc70c1f

def z180 : W := mkw 0x0000041280000000 0x0000004128000000 0xd8000036c0000000 0x0d8000036c000000

def z181 : W := mkw 0x000380000b000000 0x0000380000b00000 0x587b80300f803806 0xf587b80300f80380

def z182 : W := mkw 0x01100100509c2310 0x001100100509c231 0x86800301f03c0131 0x086800301f03c013

def z183 : W := mkw 0x000380000b000000 0x0000380000b00000 0x687b80080f80260a 0xf687b80080f80260

def z184 : W := mkw 0x3183cba80b9a940c 0x63183cba80b9a940 0x7c7f8ff80f8ffe0e 0xf7c7f8ff80f8ffe0

def z185 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x7ffbfff80fff0001 0xf7ffbfff80fff000

def z186 : W := mkw 0x0010000010000210 0x0001000001000021 0x2000000930000638 0x0200000093000063

def z187 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x407b80380f803e00 0xf407b80380f803e0

def z188 : W := mkw 0x8a603457846148e2 0x98a603457846148e 0x11177cf60e43d8c4 0x211177cf60e43d8c

def z189 : W := mkw 0xb3a3dfbacfffbd4c 0xeb3a3dfbacfffbd4 0xfffffffecfffffcf 0xffffffffecfffffc

def z190 : W := mkw 0x3c03eaed2b00940f 0x23c03eaed2b00940 0x2226f3c93d80c608 0x42226f3c93d80c60

def z191 : W := mkw 0x01100100509c2310 0x001100100509c231 0xe8000009f1bc273b 0xde8000009f1bc273

def z192 : W := mkw 0x0200100004600000 0x8020010000460000 0x0380700000700001 0x0038070000070000

def z193 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x0000800801800600 0x0000080080180060

def z194 : W := mkw 0x80200412c0052940 0x080200412c005294 0x44410c30c20f3800 0x844410c30c20f380

def z195 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x27ffffc80fffc609 0xf27ffffc80fffc60

def z196 : W := mkw 0x100380a800000004 0x0100380a80000000 0x787b80f80180260a 0xd787b80f80180260

def z197 : W := mkw 0x0000041280000000 0x0000004128000000 0x11110c3600000000 0x011110c360000000

def z198 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0x27fbff093fff0639 0xf27fbff093fff063

def z199 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0x7a7ff0f90fb0fe3e 0xf7a7ff0f90fb0fe3

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0xccc80000c0000000 0x0ccc80000c000000

def z201 : W := mkw 0x000000000b000000 0x0000000000b00000 0x000000000f800000 0xf000000000f80000

def z202 : W := mkw 0x21804b00009a0008 0x421804b00009a000 0x04000f00000f0000 0x004000f00000f000

def z203 : W := mkw 0x8020041280010840 0x0802004128001084 0x10000036000018c4 0x010000036000018c

def z204 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x3333ffff30000000 0x03333ffff3000000

def z205 : W := mkw 0x3403cebaab00940d 0x23403cebaab00940 0x7c7f8ff8ff80fe0e 0xf7c7f8ff8ff80fe0

def z206 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x5859803803803e06 0xb5859803803803e0

def z207 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbffffff800000 0xffffbffffff80000

def z208 : W := mkw 0x0bc031450ffa40a2 0xd0bc031450ffa40a 0xbbbe70c70fffc1ff 0xfbbbe70c70fffc1f

def z209 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0x87807307f07c01f1 0x087807307f07c01f

def z210 : W := mkw 0x8020041280010840 0x0802004128001084 0x59590c36024338c6 0xb59590c36024338c

def z211 : W := mkw 0xa3b3df12dfff2b58 0xca3b3df12dfff2b5 0xfffbff3fffff3fff 0xffffbff3fffff3ff

def z212 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x9ffbff060fff01c7 0xf9ffbff060fff01c

def z213 : W := mkw 0xbc23eeffeb05bd4f 0x2bc23eeffeb05bd4 0xffffffffffcfffcf 0xfffffffffffcfffc

def z214 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0x000400000dfce7ff 0xf000400000dfce7f

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x05d90c0000000000 0x005d90c000000000

def z216 : W := mkw 0x01100100509c2310 0x001100100509c231 0xc6c08309f1bc2731 0x8c6c08309f1bc273

def z217 : W := mkw 0x88202457c0052942 0x088202457c005294 0xfffb7cf7c24f39c7 0xbfffb7cf7c24f39c

def z218 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd8000036c00039c6 0x0d8000036c00039c

def z219 : W := mkw 0x8020000040052940 0x0802000004005294 0x05d90c00024f39c7 0xb05d90c00024f39c

def z220 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x222670c10c70c1ff 0x7222670c10c70c1f

def z221 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x5553fffef0000000 0x05553fffef000000

def z222 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0x2226f0c90db0c638 0x42226f0c90db0c63

def z223 : W := mkw 0x2803ea450000000a 0x02803ea450000000 0xbffbffc700000000 0x0bffbffc70000000

def z224 : W := mkw 0xbc23eeffe005294f 0x0bc23eeffe005294 0xfffbfffff20f3800 0x8fffbfffff20f380

def z225 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffd80c608 0x4fffffffffd80c60

def z226 : W := mkw 0x8020000040052940 0x0802000004005294 0x00000000024f39c7 0xb00000000024f39c

def z227 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x797ffcfe0f80fe0e 0xf797ffcfe0f80fe0

def z228 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x0200730000300000 0x0020073000030000

def z229 : W := mkw 0x01100100509c2310 0x001100100509c231 0x04000300f00c0000 0x004000300f00c000

def z230 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x797bfcfe00000000 0x0797bfcfe0000000

def z231 : W := mkw 0xa3a3df12cfff2948 0xca3a3df12cfff294 0x87fbff06cfff01c1 0xf87fbff06cfff01c

def z232 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xeffbff09ffff0001 0xfeffbff09ffff000

def z233 : W := mkw 0x020390000f600000 0x8020390000f60000 0x03fbf0000ff00001 0xf03fbf0000ff0000

def z234 : W := mkw 0x80200412cb05bd40 0x280200412cb05bd4 0xdddd0c36cfcfffcf 0xfdddd0c36cfcfffc

def z235 : W := mkw 0x0000000040042100 0x0000000004004210 0xeee88309f00c2103 0x9eee88309f00c210

def z236 : W := mkw 0x08402045000040a2 0x108402045000040a 0x80000007000001f0 0x080000007000001f

def z237 : W := mkw 0x80200412c0052940 0x080200412c005294 0x11110c36024f39c7 0xb11110c36024f39c

def z238 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07c1ff0003ff0001 0x807c1ff0003ff000

def z239 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbba70c700000000 0x0bbba70c70000000

def z240 : W := mkw 0x3003caa80000000c 0x03003caa80000000 0x7ffbfff800000000 0x07ffbfff80000000

def z241 : W := mkw 0x000000000b009400 0x2000000000b00940 0x000400000d80c608 0x4000400000d80c60

def z242 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07a2ff000dff0001 0x407a2ff000dff000

def z243 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xb80400c70c70c1ff 0x7b80400c70c70c1f

def z244 : W := mkw 0x010381000b980000 0x0010381000b98000 0x06fb83000fbc0001 0xf06fb83000fbc000

def z245 : W := mkw 0x81200512c09d2940 0x081200512c09d294 0xdff98f36c3ff39c7 0xfdff98f36c3ff39c

def z246 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfffef3cffc70c1ff 0x7fffef3cffc70c1f

def z247 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xa3a670c70c70c1f9 0x4a3a670c70c70c1f

def z248 : W := mkw 0x02401000046040a0 0x902401000046040a 0x03be70000c70c1ff 0x703be70000c70c1f

def z249 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07937f000e7f0001 0x207937f000e7f000

def z250 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xdddb7cf6c0000000 0x0dddb7cf6c000000

def z251 : W := mkw 0x9a63b4ffcf65fde6 0xb9a63b4ffcf65fde 0xfffffcffcfffffff 0xffffffcffcffffff

def z252 : W := mkw 0x80200412c0052940 0x080200412c005294 0xcdc80c06c04f21c3 0x9cdc80c06c04f21c

def z253 : W := mkw 0xbd33effff09d2b5f 0x0bd33effff09d2b5 0xfffbfffff3ff3fff 0xffffbfffff3ff3ff

def z254 : W := mkw 0x0003800000000000 0x0000380000000000 0x007b800000000000 0x0007b80000000000

def z255 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbff70f70e70f9ff 0xffbff70f70e70f9f

def z256 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xeee88309f3ff3fff 0xfeee88309f3ff3ff

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x2220000100300038 0x4222000010030003

def z258 : W := mkw 0x0000041280000000 0x0000004128000000 0xfff98f3ff0000000 0x0fff98f3ff000000

def z259 : W := mkw 0x8020000040052940 0x0802000004005294 0x00000000004f01c1 0x000000000004f01c

def z260 : W := mkw 0xa023ce12c0052948 0x0a023ce12c005294 0xdffbff36c24f39c7 0xbdffbff36c24f39c

def z261 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffc00c00e 0x7fffffffffc00c00

def z262 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xff807ffff0000000 0x0ff807ffff000000

def z263 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfff98f3ff24f39c7 0xbfff98f3ff24f39c

def z264 : W := mkw 0xa3a3df128ffb0848 0xca3a3df128ffb084 0x17fbff360fff18c5 0xf17fbff360fff18c

def z265 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffbfffff3803e00 0x8fffbfffff3803e0

def z266 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787b80f803803e00 0x8787b80f803803e0

def z267 : W := mkw 0x80200412c0052940 0x080200412c005294 0x55510c36c24f38c4 0xa55510c36c24f38c

def z268 : W := mkw 0x000380000b009400 0x2000380000b00940 0x007f80000f80fe0e 0xf007f80000f80fe0

def z269 : W := mkw 0x02401000046040a0 0x902401000046040a 0x999c00060c70c1ff 0x7999c00060c70c1f

def z270 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x000600c00c00c000 0x0000600c00c00c00

def z271 : W := mkw 0x100380a84b04b504 0x2100380a84b04b50 0xfcff80f8cf8cff0f 0xffcff80f8cf8cff0

def z272 : W := mkw 0x902384ba8b019c44 0x2902384ba8b019c4 0x797f8cfe0fc3fece 0xf797f8cfe0fc3fec

def z273 : W := mkw 0x80200412c0052940 0x080200412c005294 0x9d980c06c04f01c7 0x39d980c06c04f01c

def z274 : W := mkw 0x038011000ffa0000 0xc038011000ffa000 0x05d90c000fff0001 0xf05d90c000fff000

def z275 : W := mkw 0x2103cb0000980008 0x02103cb000098000 0x07fbff0001bc0001 0xd07fbff0001bc000

def z276 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff2003806 0xbfffbfffff200380

def z277 : W := mkw 0x1c03a4ffab009407 0x21c03a4ffab00940 0xf87f80ffff80fe0e 0xff87f80ffff80fe0

def z278 : W := mkw 0x0110010010980210 0x0011001001098021 0x0000000001b00638 0x40000000001b0063

def z279 : W := mkw 0xa1a3cf12cb9f2948 0x4a1a3cf12cb9f294 0x44418f30c38f3800 0x844418f30c38f380

def z280 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x585f00f00e00f806 0xb585f00f00e00f80

def z281 : W := mkw 0x0000000000000000 0x0000000000000000 0x9998000600000000 0x0999800060000000

def z282 : W := mkw 0x100380a800000004 0x0100380a80000000 0x4041803800000000 0x0404180380000000

def z283 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x017bfc000fc30000 0xf017bfc000fc3000

def z284 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0x07ffff000fffc1ff 0xf07ffff000fffc1f

def z285 : W := mkw 0x100000a800009404 0x2100000a80000940 0x786c80f80180fe0e 0xd786c80f80180fe0

def z286 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c20f3800 0x8ddd90c36c20f380

def z287 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07807f000fff0001 0xf07807f000fff000

def z288 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff24f0001 0xbfffbfffff24f000

def z289 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x6ffbff080fff260b 0xf6ffbff080fff260

def z290 : W := mkw 0x3e43feffa46040af 0x93e43feffa46040a 0xbbbf7cf70c70c1ff 0x7bbbf7cf70c70c1f

def z291 : W := mkw 0x0000000000000000 0x0000000000000000 0xbbb80007007001ff 0x7bbb80007007001f

def z292 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0x0000000003ff3fff 0xf0000000003ff3ff

def z293 : W := mkw 0x80200412c0052940 0x080200412c005294 0x40000030c0003800 0x040000030c000380

def z294 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x07fbff00038f0000 0x807fbff00038f000

def z295 : W := mkw 0x8020000040052940 0x0802000004005294 0x58590030024f39c7 0xb58590030024f39c

def z296 : W := mkw 0x0010000050042310 0x0001000005004231 0x000000000000273a 0x0000000000000273

def z297 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x2226f3c80db0c608 0x42226f3c80db0c60

def z298 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0xfbbe70f7cc70f9ff 0x7fbbe70f7cc70f9f

def z299 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xbfba7fc7f0000000 0x0bfba7fc7f000000

def z300 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffffffff000c1fe 0x0fffffffff000c1f

def z301 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0663ff000fbf0000 0xc0663ff000fbf000

def z302 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbfff7cc70e7fc1ff 0xfbfff7cc70e7fc1f

def z303 : W := mkw 0x9c2024ffe0052947 0x09c2024ffe005294 0xf80000fff00039c6 0x0f80000fff00039c

def z304 : W := mkw 0x2ac3fa450f6240aa 0xd2ac3fa450f6240a 0xbbbf7cc70e73c1ff 0x7bbbf7cc70e73c1f

def z305 : W := mkw 0x100000a80b009404 0x2100000a80b00940 0x780400f80f80fe0e 0xf780400f80f80fe0

def z306 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x00010c3000000000 0x000010c300000000

def z307 : W := mkw 0x0800204500000002 0x0080020450000000 0x222270c100000000 0x0222270c10000000

def z308 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07fbff00007f0001 0x007fbff00007f000

def z309 : W := mkw 0x0a403457846040a2 0x90a403457846040a 0xffff7cf7cc70c1ff 0x7ffff7cf7cc70c1f

def z310 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x0001003002001800 0x0000100300200180

def z311 : W := mkw 0x3bc3fbed0ffad4ae 0xf3bc3fbed0ffad4a 0xffffffff0fffffff 0xfffffffff0ffffff

def z312 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f18c2600 0x8eee88309f18c260

def z313 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x11177cf60e00d804 0x211177cf60e00d80

def z314 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfa22f3fff0000000 0x0fa22f3fff000000

def z315 : W := mkw 0x01100100509c2310 0x001100100509c231 0x2220830931bc273b 0xd2220830931bc273

def z316 : W := mkw 0x3583cfbaab9a000d 0x43583cfbaab9a000 0x44418f38f38f0000 0x844418f38f38f000

def z317 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeff98f09f3ff273b 0xfeff98f09f3ff273

def z318 : W := mkw 0x3f93fffffffe231f 0xc3f93fffffffe231 0xfffbffffffff273b 0xffffbffffffff273

def z319 : W := mkw 0x08402045000040a2 0x108402045000040a 0x200400c10000c038 0x0200400c10000c03

def z320 : W := mkw 0x3513cfbaf09c231d 0x03513cfbaf09c231 0xeee98f39f1bc273b 0xdeee98f39f1bc273

def z321 : W := mkw 0x0a43b0450f6040a2 0x90a43b0450f6040a 0xbbfff0c70ff0c1ff 0xfbbfff0c70ff0c1f

def z322 : W := mkw 0x039011005ffe2310 0xc039011005ffe231 0x000000000fff273b 0xf000000000fff273

def z323 : W := mkw 0x0100010000980000 0x0010001000098000 0x07f98f0003ff0001 0xf07f98f0003ff000

def z324 : W := mkw 0x100000a800009404 0x2100000a80000940 0x200400c80000c608 0x0200400c80000c60

def z325 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7dff8cf80fcffe0f 0xf7dff8cf80fcffe0

def z326 : W := mkw 0x01100512d09c2310 0x001100512d09c231 0xfff98f3ff1bc273b 0xdfff98f3ff1bc273

def z327 : W := mkw 0x100384ba8b009404 0x2100384ba8b00940 0xfdff8cfecf80fe0e 0xffdff8cfecf80fe0

def z328 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x03bb7c000e730001 0x703bb7c000e73000

def z329 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0xeffbff09f0000000 0x0effbff09f000000

def z330 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xdfd97f37f0000000 0x0dfd97f37f000000

def z331 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbfef0cf0df0e7ff 0xffbfef0cf0df0e7f

def z332 : W := mkw 0x0a503045546463b2 0x90a503045546463b 0xfbbe70cffc70e7ff 0x7fbbe70cffc70e7f

def z333 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x47fbff38f0000000 0x047fbff38f000000

def z334 : W := mkw 0x038011000ffa9400 0xe038011000ffa940 0x000400000ffffe0f 0xf000400000ffffe0

def z335 : W := mkw 0x100000a800009404 0x2100000a80000940 0x785d00f80200fe0e 0xb785d00f80200fe0

def z336 : W := mkw 0x8b703557d4fd6bf2 0x98b703557d4fd6bf 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0333ff000ff30000 0x60333ff000ff3000

def z338 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xaaae70c10c30c13b 0x5aaae70c10c30c13

def z339 : W := mkw 0x01100100509c2310 0x001100100509c231 0x6c688308f18c260a 0xd6c688308f18c260

def z340 : W := mkw 0xbe63feffe46569ef 0x9be63feffe46569e 0xfffffffffe7ff9ff 0xffffffffffe7ff9f

def z341 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xba2670c70c30c1fe 0x4ba2670c70c30c1f

def z342 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbba70c70030013b 0x5bbba70c70030013

def z343 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xddd90c36c3ff3fff 0xfddd90c36c3ff3ff

def z344 : W := mkw 0x8020000040052940 0x0802000004005294 0x99980006024f39c7 0xb99980006024f39c

def z345 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff030013b 0x5fffbfffff030013

def z346 : W := mkw 0x3d13effff09c231f 0x03d13effff09c231 0xfffbfffff18c2600 0x8fffbfffff18c260

def z347 : W := mkw 0x3d03efffa098000f 0x03d03efffa098000 0xfffbfffff1bc0001 0xdfffbfffff1bc000

def z348 : W := mkw 0x0300110004f80000 0x80300110004f8000 0x07faf3000dfc0001 0xf07faf3000dfc000

def z349 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xdfd90f37f27f39f7 0xbdfd90f37f27f39f

def z350 : W := mkw 0x1843a0ed0b00d4a6 0x31843a0ed0b00d4a 0xf87f80ff0f80fffe 0xff87f80ff0f80fff

def z351 : W := mkw 0x902004bac005bd44 0x2902004bac005bd4 0xfddd0cfec24fffcf 0xbfddd0cfec24fffc

def z352 : W := mkw 0x3d13ebed3098021f 0x03d13ebed3098021 0x2222f3c931b00638 0x42222f3c931b0063

def z353 : W := mkw 0x024010000f60d4a0 0xb024010000f60d4a 0x000400000ff0ffff 0xf000400000ff0fff

def z354 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0xf80400f7c000f9fe 0x0f80400f7c000f9f

def z355 : W := mkw 0x1c0024ffa0009407 0x21c0024ffa000940 0xf80400fff000fe0e 0x0f80400fff000fe0

def z356 : W := mkw 0x0c002457a0000003 0x00c002457a000000 0x80000007f0000000 0x080000007f000000

def z357 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0xbfbe7cc7cc7fc1ff 0x7bfbe7cc7cc7fc1f

def z358 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xfee8833ff1bc3fff 0xdfee8833ff1bc3ff

def z359 : W := mkw 0x028010000f620000 0xc028010000f62000 0x000000000e430000 0x2000000000e43000

def z360 : W := mkw 0x09102145509c2312 0x009102145509c231 0xfffaf3cff1bc273b 0xdfffaf3cff1bc273

def z361 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xeee98f39f3bf3f3b 0xdeee98f39f3bf3f3

def z362 : W := mkw 0x0110010010980210 0x0011001001098021 0x26e8830931bc0639 0xd26e8830931bc063

def z363 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0x797ff0fe0fc0fece 0xf797ff0fe0fc0fec

def z364 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xf800003ff0003ffe 0x0f800003ff0003ff

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x8888000000000103 0x1888800000000010

def z366 : W := mkw 0x22805a0004620008 0xc22805a000462000 0x01007c0000430000 0x001007c000043000

def z367 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xfdd90c3ff24f3fff 0xbfdd90c3ff24f3ff

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x787f00f00e00f80e 0xf787f00f00e00f80

def z369 : W := mkw 0x011381005b9c2310 0x0011381005b9c231 0xeefb8309ffbc273b 0xfeefb8309ffbc273

def z370 : W := mkw 0x0010000050042310 0x0001000005004231 0xeee88309f000273a 0x0eee88309f000273

def z371 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0553ff000fcf0000 0xa0553ff000fcf000

def z372 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x04418f0000000000 0x004418f000000000

def z373 : W := mkw 0x80200412c0052940 0x080200412c005294 0x85800c06c24f39c7 0xb85800c06c24f39c

def z374 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0x7c7f83f8ff8cfe0e 0xf7c7f83f8ff8cfe0

def z375 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x999e70c60c40c1c7 0x3999e70c60c40c1c

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x380400c00000c00e 0x0380400c00000c00

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x11100006004000c4 0x211100006004000c

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x0068800001800000 0xd006880000180000

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000024f0001 0xb00000000024f000

def z380 : W := mkw 0xa1a3cf12cb9f2948 0x4a1a3cf12cb9f294 0xddd98f36c3cf39c7 0xbddd98f36c3cf39c

def z381 : W := mkw 0x100380a800009404 0x2100380a80000940 0x787f80f80000fe0e 0x0787f80f80000fe0

def z382 : W := mkw 0x0200100004600000 0x8020010000460000 0x07fb7c000e7f0001 0xf07fb7c000e7f000

def z383 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xf9ff80fe0fc0ffcf 0xff9ff80fe0fc0ffc

def z384 : W := mkw 0x82601000446569e0 0x982601000446569e 0x000400000e7ff9ff 0xf000400000e7ff9f

def z385 : W := mkw 0x111381a8509c2314 0x0111381a8509c231 0xfefb83f9f1bc273b 0xdfefb83f9f1bc273

def z386 : W := mkw 0x2f83ff57affa000b 0xc2f83ff57affa000 0x87fbff07ffff0001 0xf87fbff07ffff000

def z387 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x5ffbff300fff3807 0xf5ffbff300fff380

def z388 : W := mkw 0x3f53fffff4fc63bf 0x93f53fffff4fc63b 0xfffffffffdfce7ff 0xffffffffffdfce7f

def z389 : W := mkw 0x20004a0000000008 0x020004a000000000 0x07807f0000000000 0x007807f000000000

def z390 : W := mkw 0x1c0020ed20000007 0x01c0020ed2000000 0x200000c930000000 0x0200000c93000000

def z391 : W := mkw 0x01100100509c2310 0x001100100509c231 0xaaa8000101bc273b 0xdaaa8000101bc273

def z392 : W := mkw 0x08402045000040a2 0x108402045000040a 0xb83e00c70c00c1fe 0x7b83e00c70c00c1f

def z393 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff24318c4 0x2fffbfffff24318c

def z394 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfff8830ff1fc27ff 0xffff8830ff1fc27f

def z395 : W := mkw 0x0100010000980000 0x0010001000098000 0x6ee8830801bc260b 0xd6ee8830801bc260

def z396 : W := mkw 0x2e407e57a46040ab 0x92e407e57a46040a 0xbfbe7fc7fc70c1ff 0x7bfbe7fc7fc70c1f

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x2020800801800608 0x4202080080180060

def z398 : W := mkw 0x3513cfbaf09c231d 0x03513cfbaf09c231 0x44418f38f18c2600 0x844418f38f18c260

def z399 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x303780f80f80de0c 0x6303780f80f80de0

def z400 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x6663fff9f0000000 0x06663fff9f000000

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000180260a 0xd000000000180260

def z402 : W := mkw 0x110381a80b989404 0x2110381a80b98940 0x7eff83f80fbcfe0f 0xf7eff83f80fbcfe0

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88309f180260a 0xdeee88309f180260

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x6868800800000000 0x0686880080000000

def z405 : W := mkw 0x0200100004600000 0x8020010000460000 0xabba70010c70013b 0x7abba70010c70013

def z406 : W := mkw 0x80200412c0052940 0x080200412c005294 0x44410c30c24f39c7 0xb44410c30c24f39c

def z407 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0x000270c000000000 0x0000270c00000000

def z408 : W := mkw 0xac206e57e005294b 0x0ac206e57e005294 0xdfd97f37f24f39c7 0xbdfd97f37f24f39c

def z409 : W := mkw 0x802000004b05bd40 0x2802000004b05bd4 0x000400000fcfffcf 0xf000400000fcfffc

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x4848000000002002 0x9484800000000200

def z411 : W := mkw 0x0010000050042310 0x0001000005004231 0xeaa80009f030273b 0x5eaa80009f030273

def z412 : W := mkw 0x011001005b9cb710 0x2011001005b9cb71 0xeeec8309ffbcff3f 0xfeeec8309ffbcff3

def z413 : W := mkw 0x2f807f57a4fa000b 0xc2f807f57a4fa000 0x87807f07f07f0001 0x087807f07f07f000

def z414 : W := mkw 0x2383db004ffe2108 0xc2383db004ffe210 0xcffbff00cfff2103 0xfcffbff00cfff210

def z415 : W := mkw 0x111001a8509cb714 0x2111001a8509cb71 0xfeec83f9f1bcff3f 0xdfeec83f9f1bcff3

def z416 : W := mkw 0x3f83fbed2ffa000f 0xc3f83fbed2ffa000 0x2222f3c93db00000 0x42222f3c93db0000

def z417 : W := mkw 0x184020ed0000d4a6 0x3184020ed0000d4a 0xf80400ff0000fffe 0x0f80400ff0000fff

def z418 : W := mkw 0x0310110054fc2310 0x80310110054fc231 0xeffaf309fdfc273b 0xfeffaf309fdfc273

def z419 : W := mkw 0x3d83efffab9a000f 0x43d83efffab9a000 0xfffbfffff38f0000 0x8fffbfffff38f000

def z420 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0xf87f80fecf80ffce 0xff87f80fecf80ffc

def z421 : W := mkw 0x0000000000000000 0x0000000000000000 0x04c80000000c0001 0x904c80000000c000

def z422 : W := mkw 0x3403cebaab00940d 0x23403cebaab00940 0x44418f38f3803e00 0x844418f38f3803e0

def z423 : W := mkw 0x80200412c0052940 0x080200412c005294 0xccc90c30c20f3903 0x9ccc90c30c20f390

def z424 : W := mkw 0x0000000040042100 0x0000000004004210 0xcdd90c00c24f2103 0xbcdd90c00c24f210

def z425 : W := mkw 0x3403caa82000000d 0x03403caa82000000 0x0000830830000000 0x0000083083000000

def z426 : W := mkw 0x2d106f57f09c231b 0x02d106f57f09c231 0xefe8ff0ff1bc273b 0xdefe8ff0ff1bc273

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x680000080000260a 0x0680000080000260

def z428 : W := mkw 0x3c13eefff004231f 0x03c13eefff004231 0xfffbfffff000273a 0x0fffbfffff000273

def z429 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x111670c60c70c1ff 0x7111670c60c70c1f

def z430 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfef98339f3bc3f3f 0xffef98339f3bc3f3

def z431 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7a7ff3f80fb0fe0e 0xf7a7ff3f80fb0fe0

def z432 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfeff83f9ff80fe0e 0xffeff83f9ff80fe0

def z433 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70c40c0c4 0x2bbbe70c70c40c0c

def z434 : W := mkw 0x100000a800009404 0x2100000a80000940 0x4000003800003e00 0x04000003800003e0

def z435 : W := mkw 0x2003ca000b000008 0x02003ca000b00000 0x07fbff000f800000 0xf07fbff000f80000

def z436 : W := mkw 0x3003caa80b00940c 0x23003caa80b00940 0x7ffffff80f80fe0e 0xf7ffffff80f80fe0

def z437 : W := mkw 0x0110010010980210 0x0011001001098021 0x0200030130300030 0x0020003013030003

def z438 : W := mkw 0x1803a0ed0b009406 0x21803a0ed0b00940 0xfbfff0ff0f80fe0e 0xffbfff0ff0f80fe0

def z439 : W := mkw 0x0000000040042100 0x0000000004004210 0xdcd90030c20c3907 0xbdcd90030c20c390

def z440 : W := mkw 0x2bc3fb450ffa40aa 0xd2bc3fb450ffa40a 0x27ffffc10fffc039 0xf27ffffc10fffc03

def z441 : W := mkw 0x8020000040052940 0x0802000004005294 0x00000000000039c6 0x000000000000039c

def z442 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x01007006004000c0 0x001007006004000c

def z443 : W := mkw 0x3e43feffa46040af 0x93e43feffa46040a 0xfffffffffc40c0c4 0x2fffffffffc40c0c

def z444 : W := mkw 0x02401000046040a0 0x902401000046040a 0x000400000c40c0c4 0x2000400000c40c0c

def z445 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x05d98f0003cf0001 0xb05d98f0003cf000

def z446 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x0222f30000000000 0x00222f3000000000

def z447 : W := mkw 0x2bc3fb450ffa40aa 0xd2bc3fb450ffa40a 0xbbbef3c70df0c1ff 0x7bbbef3c70df0c1f

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0xa80000010000013a 0x0a80000010000013

def z449 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdf98c3ec3cf3fcf 0xffdf98c3ec3cf3fc

def z450 : W := mkw 0x100380a800000004 0x0100380a80000000 0xfefb83f9f0000000 0x0fefb83f9f000000

def z451 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x47fbff380fff3e01 0xf47fbff380fff3e0

def z452 : W := mkw 0x08502045500463b2 0x108502045500463b 0xf80400cff000e7fe 0x0f80400cff000e7f

def z453 : W := mkw 0x01100100509c2310 0x001100100509c231 0x00000000018c2600 0x800000000018c260

def z454 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x838470070c70c1ff 0x7838470070c70c1f

def z455 : W := mkw 0x01100100509c2310 0x001100100509c231 0x06e8830001bc273b 0xd06e8830001bc273

def z456 : W := mkw 0x0010000050042310 0x0001000005004231 0xecc80009f00c273b 0x9ecc80009f00c273

def z457 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0xdddf0cf6ce4ff9c7 0xbdddf0cf6ce4ff9c

def z458 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x000270000c000000 0x0000270000c00000

def z459 : W := mkw 0x00000412c0042100 0x000000412c004210 0xddd90c36c00c2103 0x9ddd90c36c00c210

def z460 : W := mkw 0x8a603457846148e2 0x98a603457846148e 0xbbbf7cf70e73d9ff 0x7bbbf7cf70e73d9f

def z461 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07d97f00027f0001 0xb07d97f00027f000

def z462 : W := mkw 0x08402045000040a2 0x108402045000040a 0xbaac00c70030c1ff 0x5baac00c70030c1f

def z463 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x06eaf3000dbc0001 0xd06eaf3000dbc000

def z464 : W := mkw 0x3183cba80b9a940c 0x63183cba80b9a940 0x44418f38038f3e00 0x844418f38038f3e0

def z465 : W := mkw 0x0200100004600000 0x8020010000460000 0x9bba70060c7001c7 0x79bba70060c7001c

def z466 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0xeeeef3c9fdbce73b 0xdeeeef3c9fdbce73

def z467 : W := mkw 0x0a4030450f60d4a2 0xb0a4030450f60d4a 0xbbbe70c70ff0ffff 0xfbbbe70c70ff0fff

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000002003806 0xb000000000200380

def z469 : W := mkw 0x01100100509c2310 0x001100100509c231 0x44408308f1bc273b 0xd44408308f1bc273

def z470 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x01137c0000000000 0x001137c000000000

def z471 : W := mkw 0x3e43feffa46040af 0x93e43feffa46040a 0xfffbfffff07001f1 0x0fffbfffff07001f

def z472 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0xddd98f3ef0000000 0x0ddd98f3ef000000

def z473 : W := mkw 0x0010000050042310 0x0001000005004231 0x40000008f0002600 0x040000008f000260

def z474 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x686e80c80d80e60a 0xd686e80c80d80e60

def z475 : W := mkw 0x09502145509c63b2 0x109502145509c63b 0xfeec83cff1bce7ff 0xdfeec83cff1bce7f

def z476 : W := mkw 0x80200412c0052940 0x080200412c005294 0x85d90c06c24f01c1 0xb85d90c06c24f01c

def z477 : W := mkw 0x0100010000980000 0x0010001000098000 0x06800300003c0001 0x006800300003c000

def z478 : W := mkw 0x124390a80f60d4a4 0xb124390a80f60d4a 0x787f80f80ff0ffff 0xf787f80f80ff0fff

def z479 : W := mkw 0xac206e57e005294b 0x0ac206e57e005294 0x87807f07f04f01c1 0x087807f07f04f01c

def z480 : W := mkw 0x80200412c0052940 0x080200412c005294 0x04000c00c00f0000 0x004000c00c00f000

def z481 : W := mkw 0x3e83feffaf62000f 0xc3e83feffaf62000 0x11137cf60e430000 0x211137cf60e43000

def z482 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x17fbfff600000000 0x017fbfff60000000

def z483 : W := mkw 0x1c0024ffa0000007 0x01c0024ffa000000 0xfee883fff0000000 0x0fee883fff000000

def z484 : W := mkw 0x8020000040052940 0x0802000004005294 0xccc80000c24f39c7 0xbccc80000c24f39c

def z485 : W := mkw 0x0110010010980210 0x0011001001098021 0xaaa8830931b0073b 0x5aaa8830931b0073

def z486 : W := mkw 0x000380000b000000 0x0000380000b00000 0x002280000d800000 0x4002280000d80000

def z487 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0x787f80f80fbcff3f 0xf787f80f80fbcff3

def z488 : W := mkw 0x1c4024ffa00040a7 0x11c4024ffa00040a 0xf80400fff000c1fe 0x0f80400fff000c1f

def z489 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xb91670c70c40c1fe 0x2b91670c70c40c1f

def z490 : W := mkw 0x2203da0004600008 0x82203da000460000 0x07fbff000c700001 0x707fbff000c70000

def z491 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x07ffff000ffffe0f 0xf07ffff000ffffe0

def z492 : W := mkw 0x038391000ffa0000 0xc038391000ffa000 0x007b80000fff0001 0xf007b80000fff000

def z493 : W := mkw 0x3d13ebed709c231f 0x03d13ebed709c231 0xeeeaf3c9f1bc273b 0xdeeeaf3c9f1bc273

def z494 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0x44418338f38c3e00 0x844418338f38c3e0

def z495 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x0200700100300030 0x0020070010030003

def z496 : W := mkw 0x2b83fb450ffa000a 0xc2b83fb450ffa000 0xbffbffc70fff0001 0xfbffbffc70fff000

def z497 : W := mkw 0x1d1025fff09c2317 0x01d1025fff09c231 0xfee883fff1bc273b 0xdfee883fff1bc273

def z498 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x6869803803803e0a 0xd6869803803803e0

def z499 : W := mkw 0x2393db005ffe2318 0xc2393db005ffe231 0x87fbff01ffff0131 0xf87fbff01ffff013

def z500 : W := mkw 0x000000000b009400 0x2000000000b00940 0x000400000e00d804 0x2000400000e00d80

def z501 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd8000036c24f39c7 0xbd8000036c24f39c

def z502 : W := mkw 0x0000000040042100 0x0000000004004210 0xeee80001c03c213b 0xdeee80001c03c213

def z503 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0xeee98339f3bc3f3b 0xdeee98339f3bc3f3

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x4041003002003800 0x8404100300200380

def z505 : W := mkw 0xabe3ff57cfff69ea 0xdabe3ff57cfff69e 0xfffffff7cffff9ff 0xffffffff7cffff9f

def z506 : W := mkw 0xa3a05f12c4ff2948 0xca3a05f12c4ff294 0xdfd97f36c27f39c7 0xbdfd97f36c27f39c

def z507 : W := mkw 0x2bc3fb450ffa40aa 0xd2bc3fb450ffa40a 0x17ffffc60fffc0c5 0xf17ffffc60fffc0c

def z508 : W := mkw 0x101380a85b04b714 0x2101380a85b04b71 0xf87f80f9ff80ff3e 0xff87f80f9ff80ff3

def z509 : W := mkw 0x0800204500000002 0x0080020450000000 0xb80000c700000000 0x0b80000c70000000

def z510 : W := mkw 0x01100100509c2310 0x001100100509c231 0xccc80000c1bc273b 0xdccc80000c1bc273

def z511 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0x87800f07f07f01f1 0x087800f07f07f01f

def z512 : W := mkw 0x0110010010980210 0x0011001001098021 0x6a68830931b0263a 0xd6a68830931b0263

def z513 : W := mkw 0x0000000040042100 0x0000000004004210 0x84800000c00c0101 0x084800000c00c010

def z514 : W := mkw 0x0800204500000002 0x0080020450000000 0x8380700700000000 0x0838070070000000

def z515 : W := mkw 0xbc23eeffe005294f 0x0bc23eeffe005294 0xfffbfffff00039c6 0x0fffbfffff00039c

def z516 : W := mkw 0x23905b0054fe2318 0xc23905b0054fe231 0x87807f01f07f0131 0x087807f01f07f013

def z517 : W := mkw 0x8020000040052940 0x0802000004005294 0x00000000020f3800 0x800000000020f380

def z518 : W := mkw 0xbc23eeffe005294f 0x0bc23eeffe005294 0xfffbfffff04f01c1 0x0fffbfffff04f01c

def z519 : W := mkw 0x2393db005ffe2318 0xc2393db005ffe231 0x07fbff000fff273b 0xf07fbff000fff273

def z520 : W := mkw 0x1a4030ed0460d4a6 0xb1a4030ed0460d4a 0xfbbe70ff0c70ffff 0x7fbbe70ff0c70fff

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0xd9d90036024039c7 0xbd9d90036024039c

def z522 : W := mkw 0x0110010010980210 0x0011001001098021 0x0000830831800600 0x0000083083180060

def z523 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdcc80036c00c39c7 0x9dcc80036c00c39c

def z524 : W := mkw 0x0000000000000000 0x0000000000000000 0x0198000000400001 0x3019800000040000

def z525 : W := mkw 0x3f83ffffaffa000f 0xc3f83ffffaffa000 0x17fbfff60fff0001 0xf17fbfff60fff000

def z526 : W := mkw 0x3d13effff09c231f 0x03d13effff09c231 0xfffbfffff03c0131 0x0fffbfffff03c013

def z527 : W := mkw 0x038011000ffa0000 0xc038011000ffa000 0x06e883000fff0001 0xf06e883000fff000

def z528 : W := mkw 0x120390a80f609404 0xa120390a80f60940 0x7bfff0f80ff0fe0f 0xf7bfff0f80ff0fe0

def z529 : W := mkw 0x80238412cb052940 0x080238412cb05294 0xddfb8c36cfcf39c7 0xfddfb8c36cfcf39c

def z530 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffe00d804 0x2fffffffffe00d80

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x383a00c000000000 0x0383a00c00000000

def z532 : W := mkw 0x0000000000000000 0x0000000000000000 0x04410c00020f0000 0x804410c00020f000

def z533 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbb8470c70070c1ff 0x0bb8470c70070c1f

def z534 : W := mkw 0x2003ce1280000008 0x02003ce128000000 0xdffbff36c0000000 0x0dffbff36c000000

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0xbabe00c10c30c13f 0x7babe00c10c30c13

def z536 : W := mkw 0x0000000040042100 0x0000000004004210 0x44400000c00c2000 0x844400000c00c200

def z537 : W := mkw 0x23905b0054fe2318 0xc23905b0054fe231 0xefe8ff09f1ff273b 0xdefe8ff09f1ff273

def z538 : W := mkw 0x100380a800000004 0x0100380a80000000 0x787f80f80c00c00e 0x7787f80f80c00c00

def z539 : W := mkw 0x80200412c0052940 0x080200412c005294 0x5c590c30c20f3806 0xb5c590c30c20f380

def z540 : W := mkw 0x000000000b009400 0x2000000000b00940 0x383e00c00f80fe0e 0xf383e00c00f80fe0

def z541 : W := mkw 0x1c03a4ffa0000007 0x01c03a4ffa000000 0xf87b80fff0000000 0x0f87b80fff000000

def z542 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0x2222f3093db00638 0x42222f3093db0063

def z543 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x333670c70c70c0fc 0x6333670c70c70c0f

def z544 : W := mkw 0x1c0024ffa0000007 0x01c0024ffa000000 0xfbba70fff0000000 0x0fbba70fff000000

def z545 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x23be70c10c70c039 0x723be70c10c70c03

def z546 : W := mkw 0x101000a85004b714 0x2101000a85004b71 0xf80400f9f000ff3e 0x0f80400f9f000ff3

def z547 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x04418f000fff0001 0xf04418f000fff000

def z548 : W := mkw 0x0010000050042310 0x0001000005004231 0xe8688009f180273a 0xde8688009f180273

def z549 : W := mkw 0x0100010000980000 0x0010001000098000 0xaee8830101bc013b 0xdaee8830101bc013

def z550 : W := mkw 0x3e43feffa46040af 0x93e43feffa46040a 0xfffffffffc30c038 0x4fffffffffc30c03

def z551 : W := mkw 0x2a43fa45046040aa 0x92a43fa45046040a 0xbfffffc70c70c1ff 0x7bfffffc70c70c1f

def z552 : W := mkw 0x1b53b1ed5ffcf7b6 0xb1b53b1ed5ffcf7b 0xfffff3fffffcffff 0xffffff3fffffcfff

def z553 : W := mkw 0x2193cb005b9e2318 0x42193cb005b9e231 0x44418f08f38f2600 0x844418f08f38f260

def z554 : W := mkw 0x3e43feffaf60d4af 0xb3e43feffaf60d4a 0xfffffffffff0ffff 0xffffffffffff0fff

def z555 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x505780f80f80fe04 0xa505780f80f80fe0

def z556 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0xefe8f30ff1fc27fb 0xdefe8f30ff1fc27f

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0x9dd90c06024f01c7 0xb9dd90c06024f01c

def z558 : W := mkw 0x2c006a452000000b 0x02c006a452000000 0x0200730130000000 0x0020073013000000

def z559 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x781700f80e00fe0e 0x2781700f80e00fe0

def z560 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x107f80f00f80d804 0xf107f80f00f80d80

def z561 : W := mkw 0x000000000b009400 0x2000000000b00940 0x686c80080f80fe0e 0xf686c80080f80fe0

def z562 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdc410c36c20f39c6 0x8dc410c36c20f39c

def z563 : W := mkw 0x82601412c46569e0 0x982601412c46569e 0xdddd0c36ce7ff9ff 0xfdddd0c36ce7ff9f

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x05800c00004f0001 0x005800c00004f000

def z565 : W := mkw 0x038011000ffa0000 0xc038011000ffa000 0x000000000db00000 0x4000000000db0000

def z566 : W := mkw 0x8020041280010840 0x0802004128001084 0x99990c36024319c7 0x399990c36024319c

def z567 : W := mkw 0x3783dfbaaffa000d 0xc3783dfbaaffa000 0x47fbff38ffff0001 0xf47fbff38ffff000

def z568 : W := mkw 0x0000000040042100 0x0000000004004210 0xddd80006c04c21c7 0xbddd80006c04c21c

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x5800003000003806 0x0580000300000380

def z570 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0xeeee83c9fdbce73b 0xdeeee83c9fdbce73

def z571 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfff90c37c27f39ff 0xffff90c37c27f39f

def z572 : W := mkw 0x0b40314504f840a2 0x90b40314504f840a 0xbffef3c70dfcc1ff 0xfbffef3c70dfcc1f

def z573 : W := mkw 0x2193cb005b9e2318 0x42193cb005b9e231 0xeee98f09f3bf273b 0xdeee98f09f3bf273

def z574 : W := mkw 0x0100010000980000 0x0010001000098000 0x0220830001b00000 0x40220830001b0000

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8000009f0000000 0x0e8000009f000000

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88309f030013b 0x5eee88309f030013

def z577 : W := mkw 0x08402045000040a2 0x108402045000040a 0xb99c00c70040c1ff 0x3b99c00c70040c1f

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x1818000000000006 0x3181800000000000

def z579 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfc418ffff0000000 0x0fc418ffff000000

def z580 : W := mkw 0x01100100509c2310 0x001100100509c231 0x46e88308f1bc2601 0xd46e88308f1bc260

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x282800000000000a 0x5282800000000000

def z582 : W := mkw 0x1c0024ffa0000007 0x01c0024ffa000000 0x100000f600000000 0x0100000f60000000

def z583 : W := mkw 0x24004e12a0000009 0x024004e12a000000 0x04000f00f0000000 0x004000f00f000000

def z584 : W := mkw 0x2393db005ffe2318 0xc2393db005ffe231 0x47fbff08ffff2601 0xf47fbff08ffff260

def z585 : W := mkw 0x1e4034ffa46040a7 0x91e4034ffa46040a 0xfbbe70fffc70c1ff 0x7fbbe70fffc70c1f

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000004001c7 0x300000000004001c

def z587 : W := mkw 0x902384ba8b019c44 0x2902384ba8b019c4 0x11170cf60e43d8c4 0x211170cf60e43d8c

def z588 : W := mkw 0x100384ba80000004 0x0100384ba8000000 0xfdfb8cfec0000000 0x0fdfb8cfec000000

def z589 : W := mkw 0xa3a3db004fff2948 0xca3a3db004fff294 0x07fbff000fff39c7 0xf07fbff000fff39c

def z590 : W := mkw 0x00400000000040a0 0x100400000000040a 0x000400000000c1fe 0x0000400000000c1f

def z591 : W := mkw 0x0000000040042100 0x0000000004004210 0xece88008c18c270b 0xdece88008c18c270

def z592 : W := mkw 0x8020041280010840 0x0802004128001084 0xddd90c36c24318c4 0x2ddd90c36c24318c

def z593 : W := mkw 0x0380110004fa0000 0xc0380110004fa000 0x00000000007f0001 0x000000000007f000

def z594 : W := mkw 0x0000041280000000 0x0000004128000000 0xddd90c36c24f0001 0xbddd90c36c24f000

def z595 : W := mkw 0x039011005ffe2310 0xc039011005ffe231 0xeee88309ffff273b 0xfeee88309ffff273

def z596 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x01137c000fff0001 0xf01137c000fff000

def z597 : W := mkw 0x038011000ffa0000 0xc038011000ffa000 0x03ba70000fff0001 0xf03ba70000fff000

def z598 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbba70c7007001f1 0x0bbba70c7007001f

def z599 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x3a3e70c10c30c03e 0x73a3e70c10c30c03

def z600 : W := mkw 0x3e43faed246040af 0x93e43faed246040a 0xbbbef3cf3c70c1ff 0x7bbbef3cf3c70c1f

def z601 : W := mkw 0x100000a800009404 0x2100000a80000940 0x100400f00000d804 0x0100400f00000d80

def z602 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0x44418f38f38f3e00 0x844418f38f38f3e0

def z603 : W := mkw 0x111381a81b989614 0x2111381a81b98961 0x7a7f83f93fb0fe3e 0xf7a7f83f93fb0fe3

def z604 : W := mkw 0x3fc3ffffaffa40af 0xd3fc3ffffaffa40a 0xffffffffffffc1ff 0xfffffffffffffc1f

def z605 : W := mkw 0xb423cebae005294d 0x0b423cebae005294 0x44418f38f20f3800 0x844418f38f20f380

def z606 : W := mkw 0x0000000000000000 0x0000000000000000 0x101600c00c00c004 0x2101600c00c00c00

def z607 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdd800c36c04f39c7 0x0dd800c36c04f39c

def z608 : W := mkw 0x01100100509c2310 0x001100100509c231 0x86e88301f1bc0131 0xd86e88301f1bc013

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0x202600c00c00c008 0x4202600c00c00c00

def z610 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x202680c80f80fe0e 0xf202680c80f80fe0

def z611 : W := mkw 0x8020041280010840 0x0802004128001084 0x01000c06004300c0 0x001000c06004300c

def z612 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x13be70c60c70c0c5 0x713be70c60c70c0c

def z613 : W := mkw 0x02401000046040a0 0x902401000046040a 0x00000000007001f1 0x000000000007001f

def z614 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x047b8f000f8f0000 0xf047b8f000f8f000

def z615 : W := mkw 0x2bc07b4504fa40aa 0xd2bc07b4504fa40a 0xbfbe7fc70c7fc1ff 0x7bfbe7fc70c7fc1f

def z616 : W := mkw 0x0b50314514f842b2 0x90b50314514f842b 0x2226f3c93db0c638 0x42226f3c93db0c63

def z617 : W := mkw 0x111381a81b989614 0x2111381a81b98961 0x222683c93db0c638 0x4222683c93db0c63

def z618 : W := mkw 0x3c03eeffe004210f 0x03c03eeffe004210 0xfffbfffff00c2103 0x9fffbfffff00c210

def z619 : W := mkw 0x0100010000980000 0x0010001000098000 0x04408300018c0000 0x804408300018c000

def z620 : W := mkw 0xa3a3df12cfff2948 0xca3a3df12cfff294 0x47fbff30cfff3801 0xf47fbff30cfff380

def z621 : W := mkw 0x3f83ffffa4fa000f 0xc3f83ffffa4fa000 0xfffbfffff07f0001 0x0fffbfffff07f000

def z622 : W := mkw 0x2393db005ffe2318 0xc2393db005ffe231 0xeeeaf309fdbc273b 0xdeeeaf309fdbc273

def z623 : W := mkw 0x2d106f57f09c231b 0x02d106f57f09c231 0x87807f07f03c0131 0x087807f07f03c013

def z624 : W := mkw 0x902384bac0052944 0x0902384bac005294 0xfdfb8cfec24f39c7 0xbfdfb8cfec24f39c

def z625 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0xeee98f39f0000000 0x0eee98f39f000000

def z626 : W := mkw 0x01100100509c2310 0x001100100509c231 0x86800301f1bc273b 0xd86800301f1bc273

def z627 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0222f3000fff0001 0xf0222f3000fff000

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x5859003000000000 0x0585900300000000

def z629 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f03c0131 0x0eee88309f03c013

def z630 : W := mkw 0x0000000000000000 0x0000000000000000 0xb9be00c60c40c1cf 0x7b9be00c60c40c1c

def z631 : W := mkw 0x100380a80b000004 0x0100380a80b00000 0x787b80f80f800000 0xf787b80f80f80000

def z632 : W := mkw 0xbc23eeffe005294f 0x0bc23eeffe005294 0xdddb7cf6c24f39c7 0xbdddb7cf6c24f39c

def z633 : W := mkw 0x000380000b000000 0x0000380000b00000 0x387f80c00f80c00e 0xf387f80c00f80c00

def z634 : W := mkw 0x01100100509c2310 0x001100100509c231 0xcec80301f03c2133 0x9cec80301f03c213

def z635 : W := mkw 0x80200412c0052940 0x080200412c005294 0x80000006c00001c0 0x080000006c00001c

def z636 : W := mkw 0x0000000000009400 0x2000000000000940 0x000400000000fe0e 0x0000400000000fe0

def z637 : W := mkw 0x1c1024fff0042317 0x01c1024fff004231 0xf80000fff000273a 0x0f80000fff000273

def z638 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x383e80c80d80c60e 0x7383e80c80d80c60

def z639 : W := mkw 0x2bc3fb450ffa40aa 0xd2bc3fb450ffa40a 0x87fbff070fff01f1 0xf87fbff070fff01f

def z640 : W := mkw 0x8a603045446569e2 0x98a603045446569e 0xbbbe70c70e7ff9ff 0xfbbbe70c70e7ff9f

def z641 : W := mkw 0x3d13effffb9cb71f 0x23d13effffb9cb71 0xffffffffffbcff3f 0xfffffffffffbcff3

def z642 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70c30c038 0x4bbbe70c70c30c03

def z643 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x01007c0600000000 0x001007c060000000

def z644 : W := mkw 0x0200100004600000 0x8020010000460000 0x022270000c300000 0x4022270000c30000

def z645 : W := mkw 0x01100100509c2310 0x001100100509c231 0xee800309f03c273b 0x0ee800309f03c273

def z646 : W := mkw 0x1c0024ffa0000007 0x01c0024ffa000000 0xfdd90cfff0000000 0x0fdd90cfff000000

def z647 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0xbfbe73c7fc7cc1ff 0x7bfbe73c7fc7cc1f

def z648 : W := mkw 0x08402045000040a2 0x108402045000040a 0xbbbe70c70000c1fe 0x0bbbe70c70000c1f

def z649 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x83ba70070c7001f1 0x783ba70070c7001f

def z650 : W := mkw 0xa3a05f12c4ff2948 0xca3a05f12c4ff294 0x87807f06c07f01c1 0x087807f06c07f01c

def z651 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xaba87007007001fb 0x5aba87007007001f

def z652 : W := mkw 0x0100010000980000 0x0010001000098000 0x0000000001bc0001 0xd0000000001bc000

def z653 : W := mkw 0x02401000046040a0 0x902401000046040a 0xaaac00010c70c1ff 0x7aaac00010c70c1f

def z654 : W := mkw 0x02401000046040a0 0x902401000046040a 0x000400000c30c038 0x4000400000c30c03

def z655 : W := mkw 0x0000000040042100 0x0000000004004210 0xc8000000c0002102 0x0c8000000c000210

def z656 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0x111770f60e40d8c4 0x2111770f60e40d8c

def z657 : W := mkw 0x82201412c4652940 0x882201412c465294 0xdffb7c36ce7f39c7 0xfdffb7c36ce7f39c

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x0059000002000000 0xb005900000200000

def z659 : W := mkw 0x01100100509c2310 0x001100100509c231 0x6868800801bc273b 0xd6868800801bc273

def z660 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xf9137cfff0000000 0x0f9137cfff000000

def z661 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x07fbff000e430000 0x207fbff000e43000

def z662 : W := mkw 0x140004baa0000005 0x0140004baa000000 0x40000038f0000000 0x040000038f000000

def z663 : W := mkw 0x2bc07b4504fa40aa 0xd2bc07b4504fa40a 0x87807f07007f01f1 0x087807f07007f01f

def z664 : W := mkw 0x2bc3fb450ffa40aa 0xd2bc3fb450ffa40a 0x2226f3c10db0c038 0x42226f3c10db0c03

def z665 : W := mkw 0x100000a800009404 0x2100000a80000940 0x783e00f80c00fe0e 0x7783e00f80c00fe0

def z666 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0xeeec8309fdfce7ff 0xfeeec8309fdfce7f

def z667 : W := mkw 0x81300512d09d2b50 0x081300512d09d2b5 0xddd98f3ef3cf3fc7 0xbddd98f3ef3cf3fc

def z668 : W := mkw 0x3e43feffa46040af 0x93e43feffa46040a 0x11177cf60c40c0c4 0x211177cf60c40c0c

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x2220830930000000 0x0222083093000000

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0x8280000100300131 0x0828000010030013

def z671 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x0000830001800000 0x0000083000180000

def z672 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x06e98f0003bf0001 0xd06e98f0003bf000

def z673 : W := mkw 0x2e407e57a46040ab 0x92e407e57a46040a 0x87807f07f07001f1 0x087807f07f07001f

def z674 : W := mkw 0xbfa3ffffefff294f 0xcbfa3ffffefff294 0xfffbffffffff39c7 0xffffbffffffff39c

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x787e80c80d80e60e 0xf787e80c80d80e60

def z676 : W := mkw 0x1803a0ed00000006 0x01803a0ed0000000 0xfbfbf0ff00000000 0x0fbfbf0ff0000000

def z677 : W := mkw 0x000000000b009400 0x2000000000b00940 0x0000000003803e00 0x80000000003803e0

def z678 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0x27fbffc930000000 0x027fbffc93000000

def z679 : W := mkw 0x100380a800000004 0x0100380a80000000 0x101300f000000000 0x0101300f00000000

def z680 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdff0cf6ce4ff9cf 0xffdff0cf6ce4ff9c

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000030013b 0x5000000000030013

def z682 : W := mkw 0x01100100509c2310 0x001100100509c231 0x00000000003c0131 0x000000000003c013

def z683 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0x44418c38c38f3e00 0x844418c38c38f3e0

def z684 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80d80c608 0x4787f80f80d80c60

def z685 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c04f01c1 0x0ddd90c36c04f01c

def z686 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0xdddf7cf6ce4ff9c7 0xbdddf7cf6ce4ff9c

def z687 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0x87807c07c07f01f1 0x087807c07c07f01f

def z688 : W := mkw 0x0800245780000002 0x0080024578000000 0xfffb7cf7c0000000 0x0fffb7cf7c000000

def z689 : W := mkw 0x913385badb9dbf54 0x2913385badb9dbf5 0xffff8fffffffffff 0xfffff8ffffffffff

def z690 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0xdfd97c37c27f39f7 0xbdfd97c37c27f39f

def z691 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x393e70c60c40c0ce 0x7393e70c60c40c0c

def z692 : W := mkw 0x0100010000980000 0x0010001000098000 0xeee88309f1bc0001 0xdeee88309f1bc000

def z693 : W := mkw 0x1a43b0ed046040a6 0x91a43b0ed046040a 0xfbfff0ff0c70c1ff 0x7fbfff0ff0c70c1f

def z694 : W := mkw 0x83a011004fff2940 0xc83a011004fff294 0x000000000fff39c7 0xf000000000fff39c

def z695 : W := mkw 0x02401000046040a0 0x902401000046040a 0x383e00c00c70c1ff 0x7383e00c00c70c1f

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0xaaa8000100000000 0x0aaa800010000000

def z697 : W := mkw 0x0a00304504600002 0x80a0030450460000 0xbbba70c70c700001 0x7bbba70c70c70000

def z698 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x000670c00c00c000 0x0000670c00c00c00

def z699 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x383f00f00e00d80e 0x7383f00f00e00d80

def z700 : W := mkw 0x0800204500000002 0x0080020450000000 0x111270c600000000 0x0111270c60000000

def z701 : W := mkw 0x01100100509c2310 0x001100100509c231 0xccc88308f18c2703 0x9ccc88308f18c270

def z702 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x9b987007007001f7 0x39b987007007001f

def z703 : W := mkw 0x0800204500000002 0x0080020450000000 0xbbba70c7004001c7 0x3bbba70c7004001c

def z704 : W := mkw 0x0200100004600000 0x8020010000460000 0x000000000c700001 0x7000000000c70000

def z705 : W := mkw 0x8020041280010840 0x0802004128001084 0x00010c3002031800 0x000010c300203180

def z706 : W := mkw 0x902380a84b05bd44 0x2902380a84b05bd4 0x787f80f80fcfffcf 0xf787f80f80fcfffc

def z707 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdf98c3ec24f39c7 0xbfdf98c3ec24f39c

def z708 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x017bfc000fff0001 0xf017bfc000fff000

def z709 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0003806 0x0fffbfffff000380

def z710 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfef98339f1bc273b 0xdfef98339f1bc273

def z711 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x4541ff3ef0000000 0x04541ff3ef000000

def z712 : W := mkw 0x24004e12a0000009 0x024004e12a000000 0x07807f00f0000000 0x007807f00f000000

def z713 : W := mkw 0x23905b0014fa0218 0xc23905b0014fa021 0x07807f01307f0031 0x007807f01307f003

def z714 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff24f01c7 0xbfffbfffff24f01c

def z715 : W := mkw 0x80200412c0052940 0x080200412c005294 0x11110c36024f38c4 0xa11110c36024f38c

def z716 : W := mkw 0x20004a0000000008 0x020004a000000000 0x07807f00004f0001 0x007807f00004f000

def z717 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x87fbff060fff01c1 0xf87fbff060fff01c

def z718 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xa6a2f3c9f0000000 0x0a6a2f3c9f000000

def z719 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x111670c60c70c1f5 0x2111670c60c70c1f

def z720 : W := mkw 0x986024ffc005fde6 0x3986024ffc005fde 0xf80400ffc000fffe 0x0f80400ffc000fff

def z721 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x7e7bfff9f0000000 0x07e7bfff9f000000

def z722 : W := mkw 0x29c3eb450b9a40aa 0x529c3eb450b9a40a 0xbc458fc7038fc1fe 0x8bc458fc7038fc1f

def z723 : W := mkw 0x9c2024ffe0052947 0x09c2024ffe005294 0xf80000fff00001c0 0x0f80000fff00001c

def z724 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0780ff0001ff0001 0x00780ff0001ff000

def z725 : W := mkw 0x8c202457e0052943 0x08c202457e005294 0xd8000037f00039c6 0x0d8000037f00039c

def z726 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffff80de0c 0x6ffffffffff80de0

def z727 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x06007f01f0000000 0x006007f01f000000

def z728 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffe00f80e 0xffffffffffe00f80

def z729 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x17fffff00ffffe0f 0xf17fffff00ffffe0

def z730 : W := mkw 0x1f8035ffaffa0007 0xc1f8035ffaffa000 0xf80000ffffff0001 0xff80000ffffff000

def z731 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87d97f07f0000000 0x087d97f07f000000

def z732 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x17fbff300fff1805 0xf17fbff300fff180

def z733 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7ffffff80fffd805 0xf7ffffff80fffd80

def z734 : W := mkw 0x3c03eaed2b00940f 0x23c03eaed2b00940 0xeeeef3c9fd80e60a 0xdeeeef3c9fd80e60

def z735 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x07fbff0003cf0001 0xb07fbff0003cf000

def z736 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffe00d80e 0x7fffffffffe00d80

def z737 : W := mkw 0x80200412c0052940 0x080200412c005294 0x45410c36c24f38c0 0x845410c36c24f38c

def z738 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x785780f80f80fe0e 0xa785780f80f80fe0

def z739 : W := mkw 0xbc23eaed6005294f 0x0bc23eaed6005294 0x2222f3c9324f39c7 0xb2222f3c9324f39c

def z740 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0000006 0x3fffbfffff000000

def z741 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x6222f3f9f0000000 0x06222f3f9f000000

def z742 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x9f987f06007f01c7 0x39f987f06007f01c

def z743 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07ba7f00007f0001 0x007ba7f00007f000

def z744 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbfffffd800000 0x4fffbfffffd80000

def z745 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xbfbb7ff7f0000000 0x0bfbb7ff7f000000

def z746 : W := mkw 0x8020041280010840 0x0802004128001084 0xddd90c36c24f18c5 0xbddd90c36c24f18c

def z747 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfdff8cfe0fcfffcf 0xffdff8cfe0fcfffc

def z748 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xba3e70c70c30c1fe 0x7ba3e70c70c30c1f

def z749 : W := mkw 0x80200412c0052940 0x080200412c005294 0x9d990c36c24f19c7 0x39d990c36c24f19c

def z750 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x4ffbff000fff2003 0xf4ffbff000fff200

def z751 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07db7f000e7f0001 0xb07db7f000e7f000

def z752 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7c7f8cf80f8ffe0e 0xf7c7f8cf80f8ffe0

def z753 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7d7ffff80fcffe0e 0xf7d7ffff80fcffe0

def z754 : W := mkw 0x8020041280010840 0x0802004128001084 0x15910c36024f18c5 0x215910c36024f18c

def z755 : W := mkw 0x9c3024fff0052b57 0x09c3024fff0052b5 0xf80000fff0003ffe 0x0f80000fff0003ff

def z756 : W := mkw 0xa3a3df12cfff2948 0xca3a3df12cfff294 0xda22f336cdb039c6 0x4da22f336cdb039c

def z757 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7eff83f80f80fe0e 0xf7eff83f80f80fe0

def z758 : W := mkw 0x01100100509c2310 0x001100100509c231 0xa6a08309f1bc273b 0xda6a08309f1bc273

def z759 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x87fbff01ffff0001 0xf87fbff01ffff000

def z760 : W := mkw 0x8130051290990a50 0x08130051290990a5 0x33318f3f33f31efc 0x633318f3f33f31ef

def z761 : W := mkw 0x0b50314554fc63b2 0x90b50314554fc63b 0x5556f3cefdcce6c4 0xa5556f3cefdcce6c

def z762 : W := mkw 0x111381a85b9cb714 0x2111381a85b9cb71 0x969703f1fe3cd935 0x2969703f1fe3cd93

def z763 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x07c1ff00038f0000 0x807c1ff00038f000

def z764 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0x87a2ff07f0000000 0x087a2ff07f000000

def z765 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbef0cf0df0c7ff 0x7bbbef0cf0df0c7f

def z766 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff00018c4 0x0fffbfffff00018c

def z767 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07ffff000fffc00f 0xf07ffff000fffc00

def z768 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff1800000 0xdfffbfffff180000

def z769 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd5d10c36c24f39c5 0xad5d10c36c24f39c

def z770 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07937f00007f0001 0x007937f00007f000

def z771 : W := mkw 0x039011005ffe2310 0xc039011005ffe231 0x000000000fff0131 0xf000000000fff013

def z772 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xffe8fffff0000000 0x0ffe8fffff000000

def z773 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0000103 0x1fffbfffff000010

def z774 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbfff0ff0ff0ffff 0xffbfff0ff0ff0fff

def z775 : W := mkw 0x23c05b0004fa40a8 0xd23c05b0004fa40a 0x07847f000c7fc1ff 0x707847f000c7fc1f

def z776 : W := mkw 0x01100100509c2310 0x001100100509c231 0xaea88309f1bc073b 0x5aea88309f1bc073

def z777 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xeffbff09ffff013b 0xfeffbff09ffff013

def z778 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x7ffbfff80fff3807 0xf7ffbfff80fff380

def z779 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xa222f3cff0000000 0x0a222f3cff000000

def z780 : W := mkw 0x902384bacb05bd44 0x2902384bacb05bd4 0xa5a68ccecdcfc7c9 0x4a5a68ccecdcfc7c

def z781 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffbfffff3803e06 0xbfffbfffff3803e0

def z782 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xafa87f07f0000000 0x0afa87f07f000000

def z783 : W := mkw 0x0800204500000002 0x0080020450000000 0xeeeaf3c9f0000000 0x0eeeaf3c9f000000

def z784 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbffef3c70c70c1ff 0x7bffef3c70c70c1f

def z785 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x067bff000fbf0000 0xf067bff000fbf000

def z786 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0xd8000037c00039f6 0x0d8000037c00039f

def z787 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x47c1ff38f0000000 0x047c1ff38f000000

def z788 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07d97f000fff0001 0xf07d97f000fff000

def z789 : W := mkw 0x3403cebaab00940d 0x23403cebaab00940 0x7ffffff8ff80fe0e 0xf7ffffff8ff80fe0

def z790 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x01007c000fff0001 0xf01007c000fff000

def z791 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xeffbff09ffff260b 0xfeffbff09ffff260

def z792 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xfff98f3ff24f3fff 0xbfff98f3ff24f3ff

def z793 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x7773fffff0000000 0x07773fffff000000

def z794 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f1fc27ff 0xfeee88309f1fc27f

def z795 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xefeaffcff0000000 0x0efeaffcff000000

def z796 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80f80fe08 0xc787f80f80f80fe0

def z797 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xf8ff80f80f80ff0f 0xff8ff80f80f80ff0

def z798 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfeeaf3fff0000000 0x0feeaf3fff000000

def z799 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeffaf309f1bc273b 0xdeffaf309f1bc273

def z800 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x47c1ff3803ff3e01 0x847c1ff3803ff3e0

def z801 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xc7807f3ff0000000 0x0c7807f3ff000000

def z802 : W := mkw 0x01100100509c2310 0x001100100509c231 0x86808309f1bc0731 0x086808309f1bc073

def z803 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0xaffbff093fff073b 0xfaffbff093fff073

def z804 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeff98f09f1bc273b 0xdeff98f09f1bc273

def z805 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffbfffff2001800 0x0fffbfffff200180

def z806 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x7e7ffff9ff80fe0e 0xf7e7ffff9ff80fe0

def z807 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x57fffff80ffffe05 0xf57fffff80ffffe0

def z808 : W := mkw 0x33805ba804fa940c 0xe33805ba804fa940 0x7f847ff8007ffe0f 0x07f847ff8007ffe0

def z809 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x404780f80f80fe00 0x8404780f80f80fe0

def z810 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0x6662f3c9f0000000 0x06662f3c9f000000

def z811 : W := mkw 0xbc23eeffab019c4f 0x2bc23eeffab019c4 0xffffffffffc3fece 0xfffffffffffc3fec

def z812 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfff98c3fc3ff3fff 0xffff98c3fc3ff3ff

def z813 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x7ffbfff8f0000000 0x07ffbfff8f000000

def z814 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0xdffbff3ef0000000 0x0dffbff3ef000000

def z815 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x9f987f07f0000000 0x09f987f07f000000

def z816 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdf90c36c24f39cf 0xffdf90c36c24f39c

def z817 : W := mkw 0x1803a0ed0b009406 0x21803a0ed0b00940 0xfffff3ffff80fe0e 0xffffff3ffff80fe0

def z818 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddf98c36c3cf39c7 0xfddf98c36c3cf39c

def z819 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbf70f70e70d9ff 0x7bbbf70f70e70d9f

def z820 : W := mkw 0x3bc3fbed0ffad4ae 0xf3bc3fbed0ffad4a 0x2226f3c90db0c638 0x42226f3c90db0c63

def z821 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x82007307f0000000 0x082007307f000000

def z822 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee98f09f3bf273b 0xdeee98f09f3bf273

def z823 : W := mkw 0x0110010010980210 0x0011001001098021 0xa6a08309f1b00638 0x4a6a08309f1b0063

def z824 : W := mkw 0x3393dba81ffa961c 0xe3393dba81ffa961 0x27ffffc93fffc639 0xf27ffffc93fffc63

def z825 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff2000000 0xbfffbfffff200000

def z826 : W := mkw 0x9c2024ffe005bd47 0x29c2024ffe005bd4 0xf80400fff000ffce 0x0f80400fff000ffc

def z827 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x6ffbff380fff3e0b 0xf6ffbff380fff3e0

def z828 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff00c0001 0x9fffbfffff00c000

def z829 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x3ffbffc00fff0001 0xf3ffbffc00fff000

def z830 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfff98f0ff3ff27ff 0xffff98f0ff3ff27f

def z831 : W := mkw 0x80200412c0052940 0x080200412c005294 0x55510c36c24f39c7 0xb55510c36c24f39c

def z832 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x9b9e70c70c70c1f7 0x39b9e70c70c70c1f

def z833 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x786780f80f80fe0e 0xc786780f80f80fe0

def z834 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffffffff040c1ff 0x3fffffffff040c1f

def z835 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xfffaf3cff0000000 0x0fffaf3cff000000

def z836 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x03bb7c000fff0001 0xf03bb7c000fff000

def z837 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xafa87f07f030013b 0x5afa87f07f030013

def z838 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff0003ff0001 0x807fbff0003ff000

def z839 : W := mkw 0x2c03ee57ab00000b 0x02c03ee57ab00000 0x87fbff07ff800000 0xf87fbff07ff80000

def z840 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x13be70c60c70c1ff 0x713be70c60c70c1f

def z841 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x3fbe7fc00c7fc00f 0x73fbe7fc00c7fc00

def z842 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xc7c1ff3ff3803e00 0x8c7c1ff3ff3803e0

def z843 : W := mkw 0x20004a0000000008 0x020004a000000000 0xefe8ff09f0000000 0x0efe8ff09f000000

def z844 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x5ffbff300fff0001 0xf5ffbff300fff000

def z845 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f3bc3f3f 0xfeee88309f3bc3f3

def z846 : W := mkw 0x3643debaa46040ad 0x93643debaa46040a 0x44458f38fc70c1ff 0x744458f38fc70c1f

def z847 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xd7d3fffff0000000 0x0d7d3fffff000000

def z848 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70e7fc1ff 0xfbbbe70c70e7fc1f

def z849 : W := mkw 0x0000000000000000 0x0000000000000000 0xeffaf309f0000000 0x0effaf309f000000

def z850 : W := mkw 0x23c05b0004fa40a8 0xd23c05b0004fa40a 0x07807f00007f01f1 0x007807f00007f01f

def z851 : W := mkw 0x01100100509c2310 0x001100100509c231 0xec408309f1bc273b 0xdec408309f1bc273

def z852 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07eaff000dff0001 0xd07eaff000dff000

def z853 : W := mkw 0x2c406e57a00040ab 0x12c406e57a00040a 0xbf847fc7f000c1fe 0x0bf847fc7f000c1f

def z854 : W := mkw 0x8c202457e0052943 0x08c202457e005294 0x80000007f00001c0 0x080000007f00001c

def z855 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdff90c36c27f39c7 0xfdff90c36c27f39c

def z856 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbbe70cf0c70e7ff 0x7fbbe70cf0c70e7f

def z857 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0x80000007c00001f0 0x080000007c00001f

def z858 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeef98309f3bc273b 0xfeef98309f3bc273

def z859 : W := mkw 0x3003caa80b00940c 0x23003caa80b00940 0xfffffff9ff80fe0e 0xffffffff9ff80fe0

def z860 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xbfbe7fc7fc00c00e 0x7bfbe7fc7fc00c00

def z861 : W := mkw 0x1a43b0ed0f60d4a6 0xb1a43b0ed0f60d4a 0xc3c1f03f03f03ff1 0x8c3c1f03f03f03ff

def z862 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xba2670c70c70c1ff 0x7ba2670c70c70c1f

def z863 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07c87f00007f0001 0x907c87f00007f000

def z864 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07927f000c7f0001 0x207927f000c7f000

def z865 : W := mkw 0x3d13effff09c231f 0x03d13effff09c231 0x11137cf601bc273b 0xd11137cf601bc273

def z866 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x784580f80f80fe0e 0xf784580f80f80fe0

def z867 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbb9670c70c70c1ff 0x2bb9670c70c70c1f

def z868 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x05137f000e4f0000 0x205137f000e4f000

def z869 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7c7f83f8ff80fe0e 0xf7c7f83f8ff80fe0

def z870 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x303780f80f80fe0e 0xf303780f80f80fe0

def z871 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0443ff000f8f0000 0x80443ff000f8f000

def z872 : W := mkw 0x0310110054fc2310 0x80310110054fc231 0x000000000dfc273b 0xf000000000dfc273

def z873 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xddd90c37f24f39f7 0xbddd90c37f24f39f

def z874 : W := mkw 0x9c6024ffe00569e7 0x19c6024ffe00569e 0xf80400fff000f9fe 0x0f80400fff000f9f

def z875 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07817f00027f0001 0x007817f00027f000

def z876 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0x0000000001fc27fb 0xd0000000001fc27f

def z877 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffbfffff00001f0 0x0fffbfffff00001f

def z878 : W := mkw 0x01100100509c2310 0x001100100509c231 0xa2208309f1b00738 0x4a2208309f1b0073

def z879 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x7ffffff80fffc00f 0xf7ffffff80fffc00

def z880 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff000260a 0x0fffbfffff000260

def z881 : W := mkw 0x2293da005f662318 0xc2293da005f66231 0xe9137c09fe43273a 0x2e9137c09fe43273

def z882 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbbe70cffc70c1ff 0x7fbbe70cffc70c1f

def z883 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffffcffe0f 0xfffffffffffcffe0

def z884 : W := mkw 0x3083caa80b02940c 0x63083caa80b02940 0x787f8cf80f83fe0e 0xf787f8cf80f83fe0

def z885 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xea22f3c9f0000000 0x0ea22f3c9f000000

def z886 : W := mkw 0x8a603457c46569e2 0x98a603457c46569e 0x66677cf1ce3ff838 0xc66677cf1ce3ff83

def z887 : W := mkw 0x100000a80b009404 0x2100000a80b00940 0x780400f80d80fe0e 0x4780400f80d80fe0

def z888 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x87807f01007f0131 0x087807f01007f013

def z889 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x107f80f00f80fe0e 0xf107f80f00f80fe0

def z890 : W := mkw 0x2103cb0000980008 0x02103cb000098000 0x07fbff0003ff0001 0xf07fbff0003ff000

def z891 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000e7f0001 0x207fbff000e7f000

def z892 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffffc000000 0x7fffbfffffc00000

def z893 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x07fbff300fff1801 0xf07fbff300fff180

def z894 : W := mkw 0x3c43eeffa000d4af 0x33c43eeffa000d4a 0xfffffffff000fffe 0x0fffffffff000fff

def z895 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x3fffffc00ffffe0f 0xf3fffffc00ffffe0

def z896 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x4663ff38f0000000 0x04663ff38f000000

def z897 : W := mkw 0x3003caa80b00940c 0x23003caa80b00940 0x7ffffff80fcffe0f 0xf7ffffff80fcffe0

def z898 : W := mkw 0x3003caa80b00940c 0x23003caa80b00940 0x7c7f8ff80f80fe0e 0xf7c7f8ff80f80fe0

def z899 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0x3fffffc00fffc1ff 0xf3fffffc00fffc1f

def z900 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffff80d804 0xfffffffffff80d80

def z901 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x47fbff08ffff0001 0xf47fbff08ffff000

def z902 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff24319c7 0x3fffbfffff24319c

def z903 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x1ffbff000fff0007 0xf1ffbff000fff000

def z904 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x5fffff300ffffe0f 0xf5fffff300ffffe0

def z905 : W := mkw 0x8020041280010840 0x0802004128001084 0x15510c36024f18c4 0xa15510c36024f18c

def z906 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0xfffffffe0fffffcf 0xffffffffe0fffffc

def z907 : W := mkw 0x0390110054fe2310 0xc0390110054fe231 0x0000000001ff273b 0xd0000000001ff273

def z908 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdff8cfecfcfffcf 0xffdff8cfecfcfffc

def z909 : W := mkw 0x039391005ffe2310 0xc039391005ffe231 0x687b80080fff273b 0xf687b80080fff273

def z910 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x05db7c00024f0001 0xb05db7c00024f000

def z911 : W := mkw 0x0200100004600000 0x8020010000460000 0x7fff7cf00e7ff80f 0xf7fff7cf00e7ff80

def z912 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbfef0c70df0c1ff 0xfbbfef0c70df0c1f

def z913 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xeee88309f3bf3f3b 0xdeee88309f3bf3f3

def z914 : W := mkw 0x8020041280010840 0x0802004128001084 0x11110c36024f18c5 0xb11110c36024f18c

def z915 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfa7bf3fff0000000 0x0fa7bf3fff000000

def z916 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfd53fffff0000000 0x0fd53fffff000000

def z917 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07baff000dff0001 0x707baff000dff000

def z918 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x07fbff000f8f0000 0xf07fbff000f8f000

def z919 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xfff8830ff3ff3fff 0xffff8830ff3ff3ff

def z920 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffbffffff803e00 0xffffbffffff803e0

def z921 : W := mkw 0x8370110054fd6bf0 0x98370110054fd6bf 0x000400000fffffff 0xf000400000ffffff

def z922 : W := mkw 0x3283daa80f62940c 0xe3283daa80f62940 0x5ddf7cf00e4ff807 0xb5ddf7cf00e4ff80

def z923 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7a7f83f93f80fe0e 0xf7a7f83f93f80fe0

def z924 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0xbffbffc7f0000000 0x0bffbffc7f000000

def z925 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x9ffbff060fff0001 0xf9ffbff060fff000

def z926 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0x07fbff083fff0601 0xf07fbff083fff060

def z927 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x97917f37f0000000 0x097917f37f000000

def z928 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbfbe7cc70c7fc1ff 0x7bfbe7cc70c7fc1f

def z929 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07987f00007f0001 0x307987f00007f000

def z930 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xffa2fffff0000000 0x0ffa2fffff000000

def z931 : W := mkw 0x3e43feffaf60d4af 0xb3e43feffaf60d4a 0x11177cf60e40d8c4 0x211177cf60e40d8c

def z932 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x783e80f80d80fe0e 0x7783e80f80d80fe0

def z933 : W := mkw 0x100000a80b009404 0x2100000a80b00940 0x785d00f80f80fe0e 0xf785d00f80f80fe0

def z934 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x5fd97f30027f3807 0xb5fd97f30027f380

def z935 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7dff8cf80f80fe0e 0xf7dff8cf80f80fe0

def z936 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xbfffffc10fffc13f 0xfbfffffc10fffc13

def z937 : W := mkw 0x3c83eeffab02000f 0x43c83eeffab02000 0xfffbfffff2030000 0x0fffbfffff203000

def z938 : W := mkw 0x039011005ffe2310 0xc039011005ffe231 0x000000000dbc273b 0xd000000000dbc273

def z939 : W := mkw 0x039011005ffe2310 0xc039011005ffe231 0x000000000fff2601 0xf000000000fff260

def z940 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdffb7c36c24f39c7 0xbdffb7c36c24f39c

def z941 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07fbff00027f0001 0xb07fbff00027f000

def z942 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x999e70c60c70c1ff 0x7999e70c60c70c1f

def z943 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0x87937f07f0000000 0x087937f07f000000

def z944 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xfff9ff3ff0000000 0x0fff9ff3ff000000

def z945 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x11177cf00ffffe0f 0xf11177cf00ffffe0

def z946 : W := mkw 0x0000000000000000 0x0000000000000000 0x07fb7c00024f0001 0xb07fb7c00024f000

def z947 : W := mkw 0x9c2024ffe0052947 0x09c2024ffe005294 0xf80000fff0003800 0x0f80000fff000380

def z948 : W := mkw 0x80200412c0052940 0x080200412c005294 0x55d90c36c24f38c5 0xb55d90c36c24f38c

def z949 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xfffb7ff7f0000000 0x0fffb7ff7f000000

def z950 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xffd97ffff0000000 0x0ffd97ffff000000

def z951 : W := mkw 0x3c006effa000940f 0x23c006effa000940 0xff847ffff000fe0e 0x0ff847ffff000fe0

def z952 : W := mkw 0x2c006a452000000b 0x02c006a452000000 0x86807301f0000000 0x086807301f000000

def z953 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x101700f00f80fe04 0xa101700f00f80fe0

def z954 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffd80fe0e 0x4fffffffffd80fe0

def z955 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x07fbff080fff0601 0xf07fbff080fff060

def z956 : W := mkw 0x23905b0014fa0218 0xc23905b0014fa021 0x27a0ff0931ff0639 0x427a0ff0931ff063

def z957 : W := mkw 0x03d011005ffe63b0 0xd03d011005ffe63b 0x000400000fffe7ff 0xf000400000fffe7f

def z958 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffff000c00e 0x0fffffffff000c00

def z959 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c27f39ff 0xfddd90c36c27f39f

def z960 : W := mkw 0x9c23a4ffe0052947 0x09c23a4ffe005294 0xf87b80fff20039c6 0xbf87b80fff20039c

def z961 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xc7c0ff0ff0000000 0x0c7c0ff0ff000000

def z962 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0xfffbfff9ffff0001 0xffffbfff9ffff000

def z963 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07807f000e7f0001 0x207807f000e7f000

def z964 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xbffbff070fff01ff 0xfbffbff070fff01f

def z965 : W := mkw 0x01100100509c2310 0x001100100509c231 0x66608309f1bc273b 0xd66608309f1bc273

def z966 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x05007f00004f0000 0x005007f00004f000

def z967 : W := mkw 0x80200412c0052940 0x080200412c005294 0x95d90c36c24f19c5 0xb95d90c36c24f19c

def z968 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffffffff000c0c4 0x0fffffffff000c0c

def z969 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07f9ff0003ff0001 0xf07f9ff0003ff000

def z970 : W := mkw 0x039011005ffeb710 0xe039011005ffeb71 0x000400000fffff3f 0xf000400000fffff3

def z971 : W := mkw 0x80200412c0052940 0x080200412c005294 0x85810c36c24f19c1 0x085810c36c24f19c

def z972 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x05fbfc000fcf0001 0xf05fbfc000fcf000

def z973 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffd80e60e 0xffffffffffd80e60

def z974 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0xfffffff90fffff3f 0xffffffff90fffff3

def z975 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfaff80f90f80fe0e 0xffaff80f90f80fe0

def z976 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfa7ff3ffff80fe0e 0xffa7ff3ffff80fe0

def z977 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xefe8ff0ff180260a 0xdefe8ff0ff180260

def z978 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffff380fe0e 0x8fffffffff380fe0

def z979 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x27fbff080fff0609 0xf27fbff080fff060

def z980 : W := mkw 0x22805a0004620008 0xc22805a000462000 0x05d97c00024f0001 0xb05d97c00024f000

def z981 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff1b0273b 0xdfffbfffff1b0273

def z982 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbfe70c70c70e1ff 0xffbfe70c70c70e1f

def z983 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x797ffcf80ffffe0f 0xf797ffcf80ffffe0

def z984 : W := mkw 0x3003caa80000000c 0x03003caa80000000 0xfffbfff9f0000000 0x0fffbfff9f000000

def z985 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xfdf98c3ff3cf3fff 0xffdf98c3ff3cf3ff

def z986 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07e8ff00007f0001 0x007e8ff00007f000

def z987 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70c70c1f5 0x2bbbe70c70c70c1f

def z988 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x7fffffc80fffe60f 0xf7fffffc80fffe60

def z989 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfddd0cf6c24ff9cf 0xbfddd0cf6c24ff9c

def z990 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x27fbff093fff0001 0xf27fbff093fff000

def z991 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddfb0c36ce4f39c7 0xfddfb0c36ce4f39c

def z992 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xeeebfff9f0000000 0x0eeebfff9f000000

def z993 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffc00c008 0x4fffffffffc00c00

def z994 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xbf807fc7f0000000 0x0bf807fc7f000000

def z995 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x01137c000e7f0001 0x201137c000e7f000

def z996 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x5ffffff00ffff807 0xf5ffffff00ffff80

def z997 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07a2ff000fff0001 0xf07a2ff000fff000

def z998 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xcffbff00cfff0001 0xfcffbff00cfff000

def z999 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff04300c0 0x0fffbfffff04300c

def z1000 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07807f0003ff0001 0x807807f0003ff000

def z1001 : W := mkw 0x3403caa82b00940d 0x23403caa82b00940 0x787f83f83f80fe0e 0xf787f83f83f80fe0

def z1002 : W := mkw 0x3383dba804fa000c 0xc3383dba804fa000 0x7ffbfff8007f0001 0x07ffbfff8007f000

def z1003 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffe00fe0e 0x2fffffffffe00fe0

def z1004 : W := mkw 0x01100100509c2310 0x001100100509c231 0xefe88f09f1ff273b 0xdefe88f09f1ff273

def z1005 : W := mkw 0x020390000f600000 0x8020390000f60000 0x07fbfc000fff0001 0xf07fbfc000fff000

def z1006 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0663ff000fff0001 0xf0663ff000fff000

def z1007 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07c1ff00007f0001 0x007c1ff00007f000

def z1008 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x05537c000e4f0000 0xa05537c000e4f000

def z1009 : W := mkw 0x0000000000000000 0x0000000000000000 0xddd90c36024f39c7 0xbddd90c36024f39c

def z1010 : W := mkw 0x0300110004f80000 0x80300110004f8000 0x07fbff000fff0001 0xf07fbff000fff000

def z1011 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x9f987f07f04001c7 0x39f987f07f04001c

def z1012 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xeee88309f1ff27fb 0xdeee88309f1ff27f

def z1013 : W := mkw 0x01100100509c2310 0x001100100509c231 0x66e88309f1bc2639 0xd66e88309f1bc263

def z1014 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0xeffbff39f0000000 0x0effbff39f000000

def z1015 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x797f80fe0fc0fece 0xf797f80fe0fc0fec

def z1016 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07807f00027f0001 0xb07807f00027f000

def z1017 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70c30c1fe 0x4bbbe70c70c30c1f

def z1018 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfcff80f8cf80fe0e 0xffcff80f8cf80fe0

def z1019 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0x6ffbff093fff263b 0xf6ffbff093fff263

def z1020 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffffffff030c1ff 0x5fffffffff030c1f

def z1021 : W := mkw 0x2803ea450000000a 0x02803ea450000000 0xfffbffcff0000000 0x0fffbffcff000000

def z1022 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfff8830ff1bc273b 0xdfff8830ff1bc273

def z1023 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff04f0001 0x0fffbfffff04f000

def z1024 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xeee88309f1bc3fff 0xdeee88309f1bc3ff

def z1025 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80fb0ff3f 0xf787f80f80fb0ff3

def z1026 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c24f19c5 0x2ddd90c36c24f19c

def z1027 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x15137ff6f0000000 0x015137ff6f000000

def z1028 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffff80fe08 0xcffffffffff80fe0

def z1029 : W := mkw 0x0200100004600000 0x8020010000460000 0x07807c00007f0001 0x007807c00007f000

def z1030 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0xafa87f01007f013b 0x5afa87f01007f013

def z1031 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0xfffffff9fffffe0f 0xffffffff9fffffe0

def z1032 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xffff7cf70e7ff9ff 0xfffff7cf70e7ff9f

def z1033 : W := mkw 0x0800204500000002 0x0080020450000000 0xfffef3cffd80e60e 0xffffef3cffd80e60

def z1034 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff1802600 0x8fffbfffff180260

def z1035 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x7ffffff00ffff80f 0xf7ffffff00ffff80

def z1036 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfff90c37c24f39c7 0xbfff90c37c24f39c

def z1037 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fbf0000 0xc07fbff000fbf000

def z1038 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x939670c70c70c1ff 0x7939670c70c70c1f

def z1039 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffbfffff1800600 0x0fffbfffff180060

def z1040 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07d3ff000fff0001 0xa07d3ff000fff000

def z1041 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0002002 0x9fffbfffff000200

def z1042 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xeffbffc9f0000000 0x0effbffc9f000000

def z1043 : W := mkw 0x3c03eaed2000000f 0x03c03eaed2000000 0xfefbf3f9f0000000 0x0fefbf3f9f000000

def z1044 : W := mkw 0x01100100509c2310 0x001100100509c231 0xea688309f1b0273a 0xdea688309f1b0273

def z1045 : W := mkw 0x0000000000000000 0x0000000000000000 0xeee88309f1b0273b 0xdeee88309f1b0273

def z1046 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff24039c7 0xbfffbfffff24039c

def z1047 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87ba7f07f0000000 0x087ba7f07f000000

def z1048 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07bb7f000e7f0001 0x707bb7f000e7f000

def z1049 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfb33fffff0000000 0x0fb33fffff000000

def z1050 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xe7e3fffff0000000 0x0e7e3fffff000000

def z1051 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80fcffe0f 0xf787f80f80fcffe0

def z1052 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87807f07f0300131 0x087807f07f030013

def z1053 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x06ebff000fbf0001 0xd06ebff000fbf000

def z1054 : W := mkw 0x01100100509c2310 0x001100100509c231 0x6e688309f1bc263a 0xd6e688309f1bc263

def z1055 : W := mkw 0x88702457d0056bf2 0x188702457d0056bf 0xf80400fff000fffe 0x0f80400fff000fff

def z1056 : W := mkw 0x80200412c0052940 0x080200412c005294 0xcdc90c36c24f39c3 0x9cdc90c36c24f39c

def z1057 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7e7ffff80fbffe0e 0xf7e7ffff80fbffe0

def z1058 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbffe70c70c7cc1ff 0xfbffe70c70c7cc1f

def z1059 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x4641ff39f0000000 0x04641ff39f000000

def z1060 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x17ffffc00fffc005 0xf17ffffc00fffc00

def z1061 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0xeffbff0ff0000000 0x0effbff0ff000000

def z1062 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xa3be70c70c70c1f9 0x7a3be70c70c70c1f

def z1063 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0x000400000c7cc1ff 0x7000400000c7cc1f

def z1064 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffffffff180fe0e 0xdfffffffff180fe0

def z1065 : W := mkw 0xac206e57a001084b 0x0ac206e57a001084 0x87807f07f04300c0 0x087807f07f04300c

def z1066 : W := mkw 0x2c006a452000000b 0x02c006a452000000 0xeee8f309f0000000 0x0eee8f309f000000

def z1067 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0x07fbff000fff0639 0xf07fbff000fff063

def z1068 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff00001c6 0x0fffbfffff00001c

def z1069 : W := mkw 0x9c2024ffe0052947 0x09c2024ffe005294 0xd80000f6c00039c6 0x0d80000f6c00039c

def z1070 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x606780f80f80fe0e 0xf606780f80f80fe0

def z1071 : W := mkw 0x01100100509c2310 0x001100100509c231 0x46408309f1bc2630 0x846408309f1bc263

def z1072 : W := mkw 0x0000000000000000 0x0000000000000000 0x787f80f80f80fe0e 0xf787f80f80f80fe0

def z1073 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xabae70c70c70c1fb 0x5abae70c70c70c1f

def z1074 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x786e80f80d80fe0e 0xd786e80f80d80fe0

def z1075 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffd80c60e 0x7fffffffffd80c60

def z1076 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x87817f37f0000000 0x087817f37f000000

def z1077 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xdfd9ff3ff0000000 0x0dfd9ff3ff000000

def z1078 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfff98f3ff3cf3fcf 0xffff98f3ff3cf3fc

def z1079 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x0663ff00038f0000 0x80663ff00038f000

def z1080 : W := mkw 0x8b703557d4fd6bf2 0x98b703557d4fd6bf 0x87807f07f07f01f1 0x087807f07f07f01f

def z1081 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000dff0001 0x407fbff000dff000

def z1082 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0x07fbff013fff0031 0xf07fbff013fff003

def z1083 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0400001 0x3fffbfffff040000

def z1084 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x27fbffc80fff0001 0xf27fbffc80fff000

def z1085 : W := mkw 0x2003ca000b000008 0x02003ca000b00000 0x07fbff000fcf0001 0xf07fbff000fcf000

def z1086 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0x9fffff060fffc1ff 0xf9fffff060fffc1f

def z1087 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xdfdb7ff7f0000000 0x0dfdb7ff7f000000

def z1088 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x67fffff80ffffe09 0xf67fffff80ffffe0

def z1089 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07a27f000c7f0001 0x407a27f000c7f000

def z1090 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xfa0073fff0000000 0x0fa0073fff000000

def z1091 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xddd90c3ef24f3fc7 0xbddd90c3ef24f3fc

def z1092 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07ba7f000fff0001 0xf07ba7f000fff000

def z1093 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x602680f80d80fe08 0x4602680f80d80fe0

def z1094 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfa26f3fffd80fe0e 0x4fa26f3fffd80fe0

def z1095 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0773ff000fff0000 0xe0773ff000fff000

def z1096 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0300038 0x4fffbfffff030003

def z1097 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xbfbaffcff0000000 0x0bfbaffcff000000

def z1098 : W := mkw 0x2c006e57ab00940b 0x22c006e57ab00940 0x87847f07ff80fe0e 0xf87847f07ff80fe0

def z1099 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70c70c1f9 0x4bbbe70c70c70c1f

def z1100 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87d97f07f24f0001 0xb87d97f07f24f000

def z1101 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x17fbff060fff00c5 0xf17fbff060fff00c

def z1102 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffc30c13f 0x7fffffffffc30c13

def z1103 : W := mkw 0x3003caa80b00940c 0x23003caa80b00940 0x797ffcf80f80fe0e 0xf797ffcf80f80fe0

def z1104 : W := mkw 0x2003ce1280000008 0x02003ce128000000 0xfffbff3ff0000000 0x0fffbff3ff000000

def z1105 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdd90c3ff24f39c7 0xbfdd90c3ff24f39c

def z1106 : W := mkw 0x3003caa80000000c 0x03003caa80000000 0x7ffbfff8024f3807 0xb7ffbfff8024f380

def z1107 : W := mkw 0x100000a80b009404 0x2100000a80b00940 0x786c80f80f80fe0e 0xf786c80f80f80fe0

def z1108 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x47fbff380fff0001 0xf47fbff380fff000

def z1109 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xa3a670c70c70c1ff 0x7a3a670c70c70c1f

def z1110 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff3803e0e 0xffffbfffff3803e0

def z1111 : W := mkw 0x0200100004600000 0x8020010000460000 0x07d97c00027f0001 0xb07d97c00027f000

def z1112 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07d97f00007f0001 0x007d97f00007f000

def z1113 : W := mkw 0x20004a0000000008 0x020004a000000000 0x07d97f00024f0001 0xb07d97f00024f000

def z1114 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xaffbff010fff0001 0xfaffbff010fff000

def z1115 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdff98f36c24f39c7 0xbdff98f36c24f39c

def z1116 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xb3b670c70c70c1fd 0x6b3b670c70c70c1f

def z1117 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x6667fff9ff80fe08 0xc6667fff9ff80fe0

def z1118 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbfef0cf0c70c1ff 0x7fbfef0cf0c70c1f

def z1119 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x07fbff000fff3e01 0xf07fbff000fff3e0

def z1120 : W := mkw 0x0800204500000002 0x0080020450000000 0x87807307f0000000 0x087807307f000000

def z1121 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xff937ffff0000000 0x0ff937ffff000000

def z1122 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x17977ff00e7fd805 0x217977ff00e7fd80

def z1123 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07d9ff0003ff0001 0xb07d9ff0003ff000

def z1124 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xcfc87f07f0000000 0x0cfc87f07f000000

def z1125 : W := mkw 0x3c03eaed2b00940f 0x23c03eaed2b00940 0xfefff3f9ff80fe0e 0xffefff3f9ff80fe0

def z1126 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x87807f06007f01c1 0x087807f06007f01c

def z1127 : W := mkw 0xbc23eeffab019c4f 0x2bc23eeffab019c4 0xfffffffffe43d8c4 0x2fffffffffe43d8c

def z1128 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffffb0ff3f 0xfffffffffffb0ff3

def z1129 : W := mkw 0x0110010010980210 0x0011001001098021 0x66608309f1b00638 0x466608309f1b0063

def z1130 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfff98f39f3ff3f3f 0xffff98f39f3ff3f3

def z1131 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0xeeeaf309f0000000 0x0eeeaf309f000000

def z1132 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff24f3807 0xbfffbfffff24f380

def z1133 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee98339f3bc3f3b 0xdeee98339f3bc3f3

def z1134 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff20f0000 0x8fffbfffff20f000

def z1135 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffffffffc00c1fe 0x7fffffffffc00c1f

def z1136 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbff70f70c70c1ff 0x7fbff70f70c70c1f

def z1137 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffffffff200fe0e 0xbfffffffff200fe0

def z1138 : W := mkw 0x3183cba80b9a940c 0x63183cba80b9a940 0x7ffffff80f8ffe0e 0xf7ffffff80f8ffe0

def z1139 : W := mkw 0x035011005ffcf7b0 0xb035011005ffcf7b 0x000400000ffcffff 0xf000400000ffcfff

def z1140 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x781700f80f80fe0e 0xf781700f80f80fe0

def z1141 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfff9833ff3fc3fff 0xffff9833ff3fc3ff

def z1142 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xeff98f09f3ff3fff 0xfeff98f09f3ff3ff

def z1143 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x607f80f80f80fe08 0xf607f80f80f80fe0

def z1144 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffc00c004 0x2fffffffffc00c00

def z1145 : W := mkw 0x80200412c0052940 0x080200412c005294 0x99990c36024f39c7 0xb99990c36024f39c

def z1146 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xef807f0ff0000000 0x0ef807f0ff000000

def z1147 : W := mkw 0x01100100509c2310 0x001100100509c231 0xc6e88309f1bc2731 0xdc6e88309f1bc273

def z1148 : W := mkw 0x0800204500000002 0x0080020450000000 0xbfba73c7f0000000 0x0bfba73c7f000000

def z1149 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x07fbff000e4f0001 0xb07fbff000e4f000

def z1150 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0x787e80c80dfce7ff 0xf787e80c80dfce7f

def z1151 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07c0ff0001ff0001 0x807c0ff0001ff000

def z1152 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbffffff803806 0xffffbffffff80380

def z1153 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x7d7bfffef0000000 0x07d7bfffef000000

def z1154 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x27fbff010fff0039 0xf27fbff010fff003

def z1155 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0541ff0003cf0000 0x80541ff0003cf000

def z1156 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0300131 0x0fffbfffff030013

def z1157 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xddd90c36c24f3fff 0xbddd90c36c24f3ff

def z1158 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x6ffbff080fff0001 0xf6ffbff080fff000

def z1159 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x585f00f00f80fe0e 0xf585f00f00f80fe0

def z1160 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffbfffff0003e00 0x0fffbfffff0003e0

def z1161 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x333670c70c70c1ff 0x7333670c70c70c1f

def z1162 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x05007f06f0000000 0x005007f06f000000

def z1163 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdd90c37c24f39ff 0xbfdd90c37c24f39f

def z1164 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x27ffffc80ffffe0f 0xf27ffffc80ffffe0

def z1165 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbf7cc70e73c1ff 0x7bbbf7cc70e73c1f

def z1166 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x0553ff00038f0000 0x80553ff00038f000

def z1167 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbffffffcf0001 0xffffbffffffcf000

def z1168 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x393e70c60c70c1ff 0x7393e70c60c70c1f

def z1169 : W := mkw 0x100000a80b009404 0x2100000a80b00940 0x100400f00f80fe0e 0xf100400f00f80fe0

def z1170 : W := mkw 0x3283daa80f62940c 0xe3283daa80f62940 0x7dfffcf80fcffe0f 0xf7dfffcf80fcffe0

def z1171 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffff80c608 0xfffffffffff80c60

def z1172 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07a87f00007f0001 0x507a87f00007f000

def z1173 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff2001804 0x2fffbfffff200180

def z1174 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd98f3ef24f39c7 0xbddd98f3ef24f39c

def z1175 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x47ffff380ffffe0f 0xf47ffff380ffffe0

def z1176 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffff80fe04 0xaffffffffff80fe0

def z1177 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x87fbff01f0000000 0x087fbff01f000000

def z1178 : W := mkw 0xac206e57a001084b 0x0ac206e57a001084 0x97917f37f24318c4 0x297917f37f24318c

def z1179 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfee8830ff1bc27ff 0xdfee8830ff1bc27f

def z1180 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfeff83f9ffb0ff3f 0xffeff83f9ffb0ff3

def z1181 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xdffbff360fff39c7 0xfdffbff360fff39c

def z1182 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xf9ff80fe0f80fe0e 0xff9ff80fe0f80fe0

def z1183 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x57fbfffef0000000 0x057fbfffef000000

def z1184 : W := mkw 0x1803a0ed00000006 0x01803a0ed0000000 0xfffbf3fff0000000 0x0fffbf3fff000000

def z1185 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x2622ffc9f0000000 0x02622ffc9f000000

def z1186 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffe00f806 0xbfffffffffe00f80

def z1187 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f1bc2731 0x8eee88309f1bc273

def z1188 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x93be70c70c70c1f5 0x793be70c70c70c1f

def z1189 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfe63fffff0000000 0x0fe63fffff000000

def z1190 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbef3cf3c70c1ff 0x7bbbef3cf3c70c1f

def z1191 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0xb80400c7c000c1fe 0x0b80400c7c000c1f

def z1192 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdddf0cf6ce4ff9c7 0xbdddf0cf6ce4ff9c

def z1193 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdfd90c37c27f39f7 0xbdfd90c37c27f39f

def z1194 : W := mkw 0x02401000046040a0 0x902401000046040a 0xeeec8309fc70c1ff 0x7eeec8309fc70c1f

def z1195 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0xdffbff37f0000000 0x0dffbff37f000000

def z1196 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0553ff000fff0001 0xf0553ff000fff000

def z1197 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x2ffbff000fff000b 0xf2ffbff000fff000

def z1198 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xeffbff090fff273b 0xfeffbff090fff273

def z1199 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xf87f80f9ff80fe0e 0xff87f80f9ff80fe0

def z1200 : W := mkw 0x82201412c4652940 0x882201412c465294 0xdbba7036cc7039c7 0x7dbba7036cc7039c

def z1201 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fcf0000 0xa07fbff000fcf000

def z1202 : W := mkw 0x135391a85ffcf7b4 0xb135391a85ffcf7b 0x787f80f80ffcffff 0xf787f80f80ffcfff

def z1203 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x8ffbff000fff0103 0xf8ffbff000fff010

def z1204 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff24338c6 0xbfffbfffff24338c

def z1205 : W := mkw 0x3783dba82ffa000d 0xc3783dba82ffa000 0x07fbff083fff0001 0xf07fbff083fff000

def z1206 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbff70c70e70c1ff 0xfbbff70c70e70c1f

def z1207 : W := mkw 0x80200412c0052940 0x080200412c005294 0x15110c36c24f18c4 0x215110c36c24f18c

def z1208 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffffffffc00fe0e 0x7fffffffffc00fe0

def z1209 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07fbff000c7f0001 0x707fbff000c7f000

def z1210 : W := mkw 0x0200100004600000 0x8020010000460000 0x05db7c000e4f0001 0xb05db7c000e4f000

def z1211 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdd510c36c24f39c6 0xadd510c36c24f39c

def z1212 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xefe9ff3ff0000000 0x0efe9ff3ff000000

def z1213 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7bfff0f80f80fe0e 0xf7bfff0f80f80fe0

def z1214 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x01007c00007f0001 0x001007c00007f000

def z1215 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0x07fbff000fff01f1 0xf07fbff000fff01f

def z1216 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x07fb7c000e7f0001 0xf07fb7c000e7f000

def z1217 : W := mkw 0x80200412c0052940 0x080200412c005294 0xd9110c36c24f39c7 0xbd9110c36c24f39c

def z1218 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07937f000fff0001 0xf07937f000fff000

def z1219 : W := mkw 0x8020041280010840 0x0802004128001084 0x5dd90c36024f38c7 0xb5dd90c36024f38c

def z1220 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x797f8cf80fc3fe0e 0xf797f8cf80fc3fe0

def z1221 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x47fbff08f0000000 0x047fbff08f000000

def z1222 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfeff83f9ffbcff3f 0xffeff83f9ffbcff3

def z1223 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xa7fbffcff0000000 0x0a7fbffcff000000

def z1224 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x7d7ffffeff80fe0e 0xf7d7ffffeff80fe0

def z1225 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xffba7ffff0000000 0x0ffba7ffff000000

def z1226 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x07ffff000fffc609 0xf07ffff000fffc60

def z1227 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbfbe73c7fc70c1ff 0x7bfbe73c7fc70c1f

def z1228 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x6fffff080ffffe0f 0xf6fffff080ffffe0

def z1229 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7a7f80f90fb0fe3e 0xf7a7f80f90fb0fe3

def z1230 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbba670c70c70c1ff 0x4bba670c70c70c1f

def z1231 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0x00000000007c01f1 0x000000000007c01f

def z1232 : W := mkw 0x8020041280010840 0x0802004128001084 0x9dd90c36024f19c7 0xb9dd90c36024f19c

def z1233 : W := mkw 0x01100100509c2310 0x001100100509c231 0x62208309f1b02638 0x462208309f1b0263

def z1234 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7ffbfff80fff3e01 0xf7ffbfff80fff3e0

def z1235 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80d80fe0e 0x4787f80f80d80fe0

def z1236 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffffffff000d804 0x0fffffffff000d80

def z1237 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07827f000c7f0001 0x007827f000c7f000

def z1238 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xa22670c70c30c1f8 0x4a22670c70c30c1f

def z1239 : W := mkw 0x3c43eeffa00040af 0x13c43eeffa00040a 0xfffffffff000c038 0x0fffffffff000c03

def z1240 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x97fbfff7f0000000 0x097fbfff7f000000

def z1241 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fff013b 0xf07fbff000fff013

def z1242 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07fbff0001ff0001 0xd07fbff0001ff000

def z1243 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x37fffff80fffde0d 0xf37fffff80fffde0

def z1244 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x79ff80f80fc0fe0f 0xf79ff80f80fc0fe0

def z1245 : W := mkw 0x80200412c0052940 0x080200412c005294 0xc5c10c36c24f39c7 0xbc5c10c36c24f39c

def z1246 : W := mkw 0x20004a0000000008 0x020004a000000000 0x87807f01f0000000 0x087807f01f000000

def z1247 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfffe70c7cc70c1ff 0x7fffe70c7cc70c1f

def z1248 : W := mkw 0x09102145509c2312 0x009102145509c231 0xbbba70c701bc273b 0xdbbba70c701bc273

def z1249 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07b3ff000fff0001 0x607b3ff000fff000

def z1250 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x97977ff7fe00d804 0x297977ff7fe00d80

def z1251 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x87807f01f07f0001 0x087807f01f07f000

def z1252 : W := mkw 0x9863a4ffcb05fde6 0x39863a4ffcb05fde 0xf87f80ffcf80fffe 0xff87f80ffcf80fff

def z1253 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xa7a6ffcffd80c608 0x4a7a6ffcffd80c60

def z1254 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fff260b 0xf07fbff000fff260

def z1255 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x6fffffc80fffe60b 0xf6fffffc80fffe60

def z1256 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x87fbff010fff0131 0xf87fbff010fff013

def z1257 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x707780f80f80fe0c 0xe707780f80f80fe0

def z1258 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x507f80f80f80fe04 0xf507f80f80f80fe0

def z1259 : W := mkw 0x01100100509c2310 0x001100100509c231 0xe6e08309f1bc2739 0xce6e08309f1bc273

def z1260 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdc410c36c24f39c7 0xbdc410c36c24f39c

def z1261 : W := mkw 0x08402045000040a2 0x108402045000040a 0xbddd0cc7024fc1ff 0xbbddd0cc7024fc1f

def z1262 : W := mkw 0x2c03ee57a000000b 0x02c03ee57a000000 0x87c1ff07f0000000 0x087c1ff07f000000

def z1263 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0622ff000dbf0000 0x40622ff000dbf000

def z1264 : W := mkw 0x80200412c0052940 0x080200412c005294 0x11110c36024f19c5 0x211110c36024f19c

def z1265 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xdf807f37f0000000 0x0df807f37f000000

def z1266 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07807f000dff0001 0x407807f000dff000

def z1267 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x505780f80f80fe0e 0xf505780f80f80fe0

def z1268 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07917f00027f0001 0x207917f00027f000

def z1269 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddc10c36c24f39c7 0x8ddc10c36c24f39c

def z1270 : W := mkw 0x139391a85ffeb714 0xe139391a85ffeb71 0x787f80f80fffff3f 0xf787f80f80fffff3

def z1271 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0xafffff010fffc1ff 0xfafffff010fffc1f

def z1272 : W := mkw 0x2183cb00009a0008 0x42183cb00009a000 0x07fbff00000f0000 0x007fbff00000f000

def z1273 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0xbfffffc60fffc1cf 0xfbfffffc60fffc1c

def z1274 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x05937c000e4f0001 0x205937c000e4f000

def z1275 : W := mkw 0x0110010010980210 0x0011001001098021 0xeee88309f1bc0639 0xdeee88309f1bc063

def z1276 : W := mkw 0x3393dba81ffa961c 0xe3393dba81ffa961 0x7ffffff93ffffe3f 0xf7ffffff93ffffe3

def z1277 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07807f000c7f0001 0x707807f000c7f000

def z1278 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0x07ffff000fffc039 0xf07ffff000fffc03

def z1279 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x6fe8ff0801ff260b 0xd6fe8ff0801ff260

def z1280 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07e3ff000fff0001 0xc07e3ff000fff000

def z1281 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x97927fc7f0000000 0x097927fc7f000000

def z1282 : W := mkw 0x23c3db000ffad4a8 0xf23c3db000ffad4a 0x07ffff000fffffff 0xf07ffff000ffffff

def z1283 : W := mkw 0x88202457c0052942 0x088202457c005294 0xf80000f7c00039c6 0x0f80000f7c00039c

def z1284 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x06007f00003f0000 0x006007f00003f000

def z1285 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f1bc0739 0x4eee88309f1bc073

def z1286 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbb3670c70c70c1fe 0x6bb3670c70c70c1f

def z1287 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x4443fff8f0000000 0x04443fff8f000000

def z1288 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff0300001 0x5fffbfffff030000

def z1289 : W := mkw 0x80300412d0052b50 0x080300412d0052b5 0xfff90c3ff27f3fff 0xffff90c3ff27f3ff

def z1290 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x05dbff000fcf0001 0xb05dbff000fcf000

def z1291 : W := mkw 0x0800204500000002 0x0080020450000000 0xefe8f30ff0000000 0x0efe8f30ff000000

def z1292 : W := mkw 0x01100100509c2310 0x001100100509c231 0xefe8830ff1fc27fb 0xdefe8830ff1fc27f

def z1293 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfef88309f1bc273f 0xffef88309f1bc273

def z1294 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07c17f00027f0001 0x807c17f00027f000

def z1295 : W := mkw 0x2383db000ffa9408 0xe2383db000ffa940 0x07ffff000fffd805 0xf07ffff000fffd80

def z1296 : W := mkw 0x2203da0004600008 0x82203da000460000 0x07fbff000e7f0001 0xf07fbff000e7f000

def z1297 : W := mkw 0x83b011005fff2b50 0xc83b011005fff2b5 0x000000000fff3fff 0xf000000000fff3ff

def z1298 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0xefe8ff09f07f0001 0x0efe8ff09f07f000

def z1299 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdddd0c36ce4ff9cf 0xfdddd0c36ce4ff9c

def z1300 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0xa7807fcff0000000 0x0a7807fcff000000

def z1301 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x782680f80f80fe0e 0xf782680f80f80fe0

def z1302 : W := mkw 0x3183cba80b9a940c 0x63183cba80b9a940 0x7ffbfff8038f3e00 0x87ffbfff8038f3e0

def z1303 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xdfd97f37f2003806 0xbdfd97f37f200380

def z1304 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87807f07f04f0001 0x087807f07f04f000

def z1305 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xdddbfffef0000000 0x0dddbfffef000000

def z1306 : W := mkw 0x1c0024ffa0000007 0x01c0024ffa000000 0xfffaf3fff0000000 0x0fffaf3fff000000

def z1307 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeeec8309fdbce73f 0xfeeec8309fdbce73

def z1308 : W := mkw 0x3403cebaab00940d 0x23403cebaab00940 0x47fbff38ff803e00 0xf47fbff38ff803e0

def z1309 : W := mkw 0x01100100509c2310 0x001100100509c231 0xee608309f1bc273a 0xcee608309f1bc273

def z1310 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeff88309f1fc273b 0xfeff88309f1fc273

def z1311 : W := mkw 0x2403ce12a0000009 0x02403ce12a000000 0x07fbff00f0000000 0x007fbff00f000000

def z1312 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff24f18c5 0xbfffbfffff24f18c

def z1313 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7aff80f80fb0fe0f 0xf7aff80f80fb0fe0

def z1314 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0x838670c70c70c1f1 0x0838670c70c70c1f

def z1315 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07807f0001ff0001 0xd07807f0001ff000

def z1316 : W := mkw 0xbc23eeffa001084f 0x0bc23eeffa001084 0xfffbfffff2031800 0x0fffbfffff203180

def z1317 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x47fbff080fff2601 0xf47fbff080fff260

def z1318 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff04001c1 0x0fffbfffff04001c

def z1319 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x07ffffc00fffc001 0xf07ffffc00fffc00

def z1320 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fff3807 0xf07fbff000fff380

def z1321 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xfbff80ff0ff0ffff 0xffbff80ff0ff0fff

def z1322 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c24f38c4 0xaddd90c36c24f38c

def z1323 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87807f07f04001c1 0x087807f07f04001c

def z1324 : W := mkw 0x81300100509d2b50 0x081300100509d2b5 0xfef98339f3ff3fff 0xffef98339f3ff3ff

def z1325 : W := mkw 0x3003caa80b00940c 0x23003caa80b00940 0x7a7ff3f80f80fe0e 0xf7a7ff3f80f80fe0

def z1326 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeefa8309fdbc273b 0xfeefa8309fdbc273

def z1327 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f3ff273b 0xfeee88309f3ff273

def z1328 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07faff000dff0001 0xf07faff000dff000

def z1329 : W := mkw 0x80200412c0052940 0x080200412c005294 0xc5d90c36c24f39c1 0xbc5d90c36c24f39c

def z1330 : W := mkw 0x01100100509c2310 0x001100100509c231 0xcec88309f1bc2733 0x9cec88309f1bc273

def z1331 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xf87f80fe0f80ffce 0xff87f80fe0f80ffc

def z1332 : W := mkw 0x000000000b009400 0x2000000000b00940 0x787f00f00f80fe0e 0xf787f00f00f80fe0

def z1333 : W := mkw 0x120390a80f609404 0xa120390a80f60940 0x7ffffcf80ffffe0f 0xf7ffffcf80ffffe0

def z1334 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0333ff000fff0001 0xf0333ff000fff000

def z1335 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfeec83c9f1bce73f 0xdfeec83c9f1bce73

def z1336 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfffef3cffdf0e7ff 0xffffef3cffdf0e7f

def z1337 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x057bff000fcf0000 0xf057bff000fcf000

def z1338 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x7ffffff80fffc609 0xf7ffffff80fffc60

def z1339 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x783780f80f80fe0e 0x6783780f80f80fe0

def z1340 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff000013a 0x0fffbfffff000013

def z1341 : W := mkw 0x21804b00009a0008 0x421804b00009a000 0x07807f00000f0000 0x007807f00000f000

def z1342 : W := mkw 0x9c23a4ffeb05bd47 0x29c23a4ffeb05bd4 0xf87f80ffff80ffce 0xff87f80ffff80ffc

def z1343 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07e9ff0003ff0001 0xd07e9ff0003ff000

def z1344 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x05db7c000fff0001 0xf05db7c000fff000

def z1345 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff07001ff 0x7fffbfffff07001f

def z1346 : W := mkw 0x2183cb000b9a0008 0x42183cb000b9a000 0x07fbff0003bf0001 0xd07fbff0003bf000

def z1347 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c24f39c1 0x8ddd90c36c24f39c

def z1348 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x27ffffc00fffc009 0xf27ffffc00fffc00

def z1349 : W := mkw 0x80200412c0052940 0x080200412c005294 0x95910c36c24f39c7 0xb95910c36c24f39c

def z1350 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x47fbff300fff3801 0xf47fbff300fff380

def z1351 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f1bc2638 0xceee88309f1bc263

def z1352 : W := mkw 0x2283da000f620008 0xc2283da000f62000 0x01137c000e4f0001 0xb01137c000e4f000

def z1353 : W := mkw 0x0110010010980210 0x0011001001098021 0xeee88309f1b0263a 0xdeee88309f1b0263

def z1354 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfff98f3ff27f39ff 0xffff98f3ff27f39f

def z1355 : W := mkw 0x0390110054fe2310 0xc0390110054fe231 0x00000000007f0131 0x000000000007f013

def z1356 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffffffffc40c1cf 0x7fffffffffc40c1c

def z1357 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfefa83c9f1bc273b 0xdfefa83c9f1bc273

def z1358 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x0641ff0003bf0000 0x80641ff0003bf000

def z1359 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbaae70c70c30c1ff 0x5baae70c70c30c1f

def z1360 : W := mkw 0x2c406e57a00040ab 0x12c406e57a00040a 0x87807f07f00001f0 0x087807f07f00001f

def z1361 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeee88309f1b0273a 0x4eee88309f1b0273

def z1362 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xb7b3fffff0000000 0x0b7b3fffff000000

def z1363 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x07fbff00020f0000 0x807fbff00020f000

def z1364 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0x87e8ff07f0000000 0x087e8ff07f000000

def z1365 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xb91670c70c70c1ff 0x7b91670c70c70c1f

def z1366 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x7ffbfff80fff260b 0xf7ffbfff80fff260

def z1367 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff1800608 0x4fffbfffff180060

def z1368 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeea08309f1bc273b 0x4eea08309f1bc273

def z1369 : W := mkw 0x100000a80b009404 0x2100000a80b00940 0x783e00f80f80fe0e 0xf783e00f80f80fe0

def z1370 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x5557fff80fcffe04 0xa5557fff80fcffe0

def z1371 : W := mkw 0x22805a0004620008 0xc22805a000462000 0x05807c00004f0001 0x005807c00004f000

def z1372 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeeee83c9fdbce73b 0xdeeee83c9fdbce73

def z1373 : W := mkw 0x2393db001ffa0218 0xc2393db001ffa021 0xeffbff09ffff0639 0xfeffbff09ffff063

def z1374 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x686f80f80f80fe0a 0xd686f80f80f80fe0

def z1375 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x67fbfff9f0000000 0x067fbfff9f000000

def z1376 : W := mkw 0x0110010010980210 0x0011001001098021 0xeee88309f1b0073b 0x5eee88309f1b0073

def z1377 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfffe83cffdfce7ff 0xffffe83cffdfce7f

def z1378 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xc7fbff3ff0000000 0x0c7fbff3ff000000

def z1379 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdd90c3ec24f3fcf 0xbfdd90c3ec24f3fc

def z1380 : W := mkw 0x80200412c0052940 0x080200412c005294 0x59590c36024f39c7 0xb59590c36024f39c

def z1381 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffd80e60a 0xdfffffffffd80e60

def z1382 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeaa88309f1b0273b 0x5eaa88309f1b0273

def z1383 : W := mkw 0x23805b000ffa9408 0xe23805b000ffa940 0x07847f000ffffe0f 0xf07847f000ffffe0

def z1384 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd98c3ec3cf3fc7 0xbddd98c3ec3cf3fc

def z1385 : W := mkw 0x80200412c0052940 0x080200412c005294 0x5d590c36c24f38c6 0xb5d590c36c24f38c

def z1386 : W := mkw 0x80200412c0052940 0x080200412c005294 0xddd90c36c3cf3fcf 0xfddd90c36c3cf3fc

def z1387 : W := mkw 0x01100100509c2310 0x001100100509c231 0x26208309f1bc0638 0x426208309f1bc063

def z1388 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xfbbe70f70c70f9ff 0x7fbbe70f70c70f9f

def z1389 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0xd80400f6c000f9c6 0x0d80400f6c000f9c

def z1390 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xffffffffffc0ffcf 0xfffffffffffc0ffc

def z1391 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbfff7cc70c70c1ff 0x7bfff7cc70c70c1f

def z1392 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdfd90f37f24f39c7 0xbdfd90f37f24f39c

def z1393 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xc7c17f37f0000000 0x0c7c17f37f000000

def z1394 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xffffffffff80c00e 0xfffffffffff80c00

def z1395 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xa7a0ff0ff0000000 0x0a7a0ff0ff000000

def z1396 : W := mkw 0x33c3dba80ffad4ac 0xf33c3dba80ffad4a 0x7ffffff80fffffff 0xf7ffffff80ffffff

def z1397 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff2430000 0x2fffbfffff243000

def z1398 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xfffaffcff0000000 0x0fffaffcff000000

def z1399 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff04000c4 0x2fffbfffff04000c

def z1400 : W := mkw 0x2c006e57a000000b 0x02c006e57a000000 0xa7a27fc7f0000000 0x0a7a27fc7f000000

def z1401 : W := mkw 0x3c03eeffa000940f 0x23c03eeffa000940 0xfffffffff000c608 0x0fffffffff000c60

def z1402 : W := mkw 0x23c3db000ffa40a8 0xd23c3db000ffa40a 0x07ffff000fffc0c5 0xf07ffff000fffc0c

def z1403 : W := mkw 0x3403cebaa000000d 0x03403cebaa000000 0x4553ff38f0000000 0x04553ff38f000000

def z1404 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80fc0ffcf 0xf787f80f80fc0ffc

def z1405 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x01137c000fcf0000 0xa01137c000fcf000

def z1406 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x3fffffc80fffc60f 0xf3fffffc80fffc60

def z1407 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffbfffff3803e0a 0xdfffbfffff3803e0

def z1408 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x5ffbff380fff3e07 0xf5ffbff380fff3e0

def z1409 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x787f80f80f80fe04 0xa787f80f80f80fe0

def z1410 : W := mkw 0x0200100004600000 0x8020010000460000 0x07ba7c000c7f0001 0x707ba7c000c7f000

def z1411 : W := mkw 0x0350110054fc63b0 0x90350110054fc63b 0x000400000dbce73b 0xd000400000dbce73

def z1412 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70df0e7ff 0xfbbbe70c70df0e7f

def z1413 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbffffff80260a 0xffffbffffff80260

def z1414 : W := mkw 0x2003ca0000000008 0x02003ca000000000 0x07fbff00004f0001 0x007fbff00004f000

def z1415 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x585f80f80f80fe06 0xb585f80f80f80fe0

def z1416 : W := mkw 0x3c006effa000000f 0x03c006effa000000 0x97807ff7f0000000 0x097807ff7f000000

def z1417 : W := mkw 0x038011000ffa0000 0xc038011000ffa000 0x07fb7c000fff0001 0xf07fb7c000fff000

def z1418 : W := mkw 0x80200412c0052940 0x080200412c005294 0xdd910c36c24f39c7 0x2dd910c36c24f39c

def z1419 : W := mkw 0x01100100509c2310 0x001100100509c231 0xc6c08309f1bc273b 0xdc6c08309f1bc273

def z1420 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x383f00f00f80fe0e 0xf383f00f00f80fe0

def z1421 : W := mkw 0x01100100509c2310 0x001100100509c231 0xea208309f1bc273b 0xdea208309f1bc273

def z1422 : W := mkw 0x88602457c00569e2 0x188602457c00569e 0xf87f00f7ce00f9fe 0xff87f00f7ce00f9f

def z1423 : W := mkw 0x3c43eeffab00d4af 0x33c43eeffab00d4a 0xffffffffff80fffe 0xfffffffffff80fff

def z1424 : W := mkw 0x80200412c0052940 0x080200412c005294 0x15d90c36024f39c7 0xb15d90c36024f39c

def z1425 : W := mkw 0x2383db0004fa0008 0xc2383db0004fa000 0x07a2ff00007f0001 0x007a2ff00007f000

def z1426 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x8780ff0ff0000000 0x08780ff0ff000000

def z1427 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xffc1fffff0000000 0x0ffc1fffff000000

def z1428 : W := mkw 0x01100100509c2310 0x001100100509c231 0xa6e88309f1bc0739 0xda6e88309f1bc073

def z1429 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0x87827fc7f0000000 0x087827fc7f000000

def z1430 : W := mkw 0x3383dba80ffa000c 0xc3383dba80ffa000 0x17fbfff00fff0001 0xf17fbfff00fff000

def z1431 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfbbaf3fff0000000 0x0fbbaf3fff000000

def z1432 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x6667fff80fbffe08 0xc6667fff80fbffe0

def z1433 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x7ffbff380fff3e0f 0xf7ffbff380fff3e0

def z1434 : W := mkw 0x23805b000ffa0008 0xc23805b000ffa000 0x07e8ff000fff0001 0xf07e8ff000fff000

def z1435 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x3ffffff00fffd80f 0xf3ffffff00fffd80

def z1436 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0x7cff80f80f8cfe0f 0xf7cff80f80f8cfe0

def z1437 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0xfffffffffc00c000 0x0fffffffffc00c00

def z1438 : W := mkw 0x2003ca000b000008 0x02003ca000b00000 0xeffbff09ff80260a 0xfeffbff09ff80260

def z1439 : W := mkw 0x3c03eeffab00940f 0x23c03eeffab00940 0x5557fffeff80fe04 0xa5557fffeff80fe0

def z1440 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbfffff3800000 0x8fffbfffff380000

def z1441 : W := mkw 0x01100100509c2310 0x001100100509c231 0xeec08309f1bc273b 0x8eec08309f1bc273

def z1442 : W := mkw 0x0a403045046040a2 0x90a403045046040a 0xbbbe70c70e70f9ff 0xfbbbe70c70e70f9f

def z1443 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07a0ff0001ff0001 0x407a0ff0001ff000

def z1444 : W := mkw 0x3383dba80ffa940c 0xe3383dba80ffa940 0x27a6ffc80dffc609 0x427a6ffc80dffc60

def z1445 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07c1ff000fff0001 0xf07c1ff000fff000

def z1446 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff2003800 0x8fffbfffff200380

def z1447 : W := mkw 0x2383db000ffa0008 0xc2383db000ffa000 0x07fbff000fff01c7 0xf07fbff000fff01c

def z1448 : W := mkw 0x100380a80b009404 0x2100380a80b00940 0xf87f80f90f80ff3e 0xff87f80f90f80ff3

def z1449 : W := mkw 0x01100100509c2310 0x001100100509c231 0xfee88339f1bc3f3f 0xdfee88339f1bc3f3

def z1450 : W := mkw 0x100000a800009404 0x2100000a80000940 0x787e80f80d80fe0e 0xf787e80f80d80fe0

def z1451 : W := mkw 0x80200412c0052940 0x080200412c005294 0xfdfb0cf6c24f39c7 0xbfdfb0cf6c24f39c

def z1452 : W := mkw 0x3c03eeffab00000f 0x03c03eeffab00000 0xfffbfffffe000000 0x2fffbfffffe00000

def z1453 : W := mkw 0x23805b0004fa0008 0xc23805b0004fa000 0x07fb7f000e7f0001 0xf07fb7f000e7f000

def z1454 : W := mkw 0x80200412c0052940 0x080200412c005294 0xffff0cf7ce7ff9ff 0xfffff0cf7ce7ff9f

def z1455 : W := mkw 0x3c03eeffa000000f 0x03c03eeffa000000 0xfffbfffff000000a 0x5fffbfffff000000

def z1456 : W := mkw 0x0800245780000002 0x0080024578000000 0xfffbfffff0000000 0x0fffbfffff000000

def z1457 : W := mkw 0x0110010010980210 0x0011001001098021 0xea208309f1b00638 0x4ea208309f1b0063

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z8,z3,z4,z5,z9])],[(1,[z1,z2,z10,z4,z5,z9]),(0,[z11,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z4,z5,z13,z9]),(0,[z14,z15,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z16]),(0,[z1,z2,z3,z4,z5,z9,z17])],[],[(0,[z1,z18,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z19,z5,z20,z9]),(0,[z21,z22,z2,z3,z4,z5,z9]),(0,[z1,z23,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z25,z9])],[(0,[z1,z2,z26,z3,z12,z5,z9]),(0,[z22,z2,z3,z4,z27,z5,z9]),(0,[z28,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z29,z30]),(0,[z1,z2,z31,z3,z4,z5,z9]),(0,[z1,z2,z3,z32,z4,z33,z9]),(0,[z1,z2,z3,z4,z34,z5,z9])],[(0,[z1,z35,z2,z26,z3,z4,z9]),(0,[z36,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z37,z3,z4,z5,z9]),(0,[z38,z1,z2,z3,z4,z39,z9]),(0,[z40,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z41,z9]),(0,[z1,z2,z3,z4,z42,z5,z9]),(0,[z1,z2,z43,z3,z4,z44,z9]),(1,[z45,z2,z3,z4,z5,z9]),(0,[z1,z2,z46,z3,z4,z5,z9])],[(0,[z47,z1,z2,z3,z4,z33,z9]),(0,[z1,z48,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z49]),(1,[z1,z2,z50,z4,z5,z9]),(0,[z1,z2,z3,z4,z51,z33,z9]),(0,[z1,z52,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z53,z24,z5,z9])],[(0,[z54,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z55,z9]),(0,[z1,z2,z3,z4,z56,z5,z9]),(0,[z57,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z58,z5,z9]),(0,[z59,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z60,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z61,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z62,z9]),(0,[z63,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z64]),(0,[z1,z2,z3,z4,z5,z65,z9]),(0,[z1,z2,z3,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z66])],[(0,[z1,z2,z3,z67,z4,z44,z9]),(0,[z1,z68,z2,z3,z4,z44,z9]),(0,[z1,z2,z69,z3,z4,z5,z9]),(0,[z70,z1,z2,z3,z4,z33,z9])],[(0,[z45,z1,z2,z3,z4,z5,z9])],[(0,[z71,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z72,z4,z5,z9])],[(1,[z1,z2,z3,z4,z73,z9]),(0,[z1,z2,z74,z3,z4,z5,z9]),(0,[z75,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z76]),(0,[z1,z52,z3,z77,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z78,z9]),(0,[z1,z2,z3,z4,z79,z5,z9]),(0,[z1,z2,z3,z80,z4,z5,z9])],[(1,[z81,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z6,z9]),(0,[z1,z2,z3,z82,z4,z5,z9]),(0,[z1,z52,z3,z4,z5,z9,z83]),(0,[z1,z2,z3,z12,z5,z84,z9]),(0,[z59,z1,z2,z3,z4,z85,z9]),(0,[z1,z2,z3,z4,z5,z9,z86])]],
   [[(0,[z47,z1,z2,z10,z4,z5,z9]),(0,[z1,z87,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z88,z5,z9]),(0,[z1,z2,z89,z3,z24,z5,z9]),(0,[z21,z2,z3,z4,z5,z90,z9]),(0,[z22,z1,z91,z2,z3,z4,z9]),(0,[z92,z1,z2,z3,z24,z5,z9]),(0,[z1,z93,z2,z3,z4,z5,z9]),(0,[z1,z2,z43,z4,z5,z30,z9]),(1,[z94,z1,z2,z3,z5,z66])],[(0,[z95,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z9,z66]),(0,[z96,z1,z2,z3,z4,z44,z9]),(0,[z97,z1,z2,z3,z4,z5,z9])],[(1,[z1,z98,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z99,z5,z9]),(0,[z28,z2,z3,z4,z19,z5,z9]),(0,[z100,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z101,z4,z5,z9])],[(0,[z1,z2,z3,z4,z33,z20,z9]),(0,[z1,z2,z3,z4,z5,z30,z9])],[(0,[z11,z48,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z32,z5,z9]),(0,[z1,z2,z3,z4,z102,z5,z9])],[],[(0,[z103,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z104,z9]),(0,[z1,z2,z3,z4,z105,z85,z9]),(0,[z1,z2,z3,z4,z5,z9,z106])],[(0,[z1,z2,z3,z4,z5,z107,z9]),(0,[z1,z7,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z108]),(0,[z1,z2,z3,z109,z4,z5,z9]),(0,[z110,z1,z2,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z27,z5,z9]),(0,[z22,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z4,z44,z29,z9]),(0,[z1,z2,z3,z4,z5,z9,z111]),(0,[z112,z1,z2,z3,z12,z5,z9]),(0,[z1,z113,z2,z3,z24,z5,z9]),(0,[z1,z2,z114,z3,z4,z5,z9]),(0,[z1,z2,z43,z3,z4,z5,z30]),(0,[z115,z1,z2,z3,z4,z5,z9])],[(0,[z116,z2,z3,z4,z19,z5,z9]),(0,[z1,z2,z3,z19,z51,z5,z9]),(0,[z1,z2,z117,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z118,z29,z9]),(0,[z1,z2,z3,z24,z88,z5,z9]),(0,[z94,z1,z2,z119,z4,z5,z9])],[(0,[z1,z2,z3,z120,z4,z44,z9]),(0,[z121,z1,z2,z3,z4,z5,z9]),(0,[z122,z1,z2,z3,z4,z5,z9]),(0,[z123,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z124,z4,z5,z9])],[(0,[z1,z2,z3,z125,z4,z5,z9]),(0,[z1,z126,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z127,z5,z9])],[(0,[z1,z2,z3,z4,z128,z5,z9]),(0,[z22,z1,z129,z2,z3,z4,z9]),(0,[z1,z2,z3,z24,z5,z30,z9]),(0,[z1,z2,z3,z4,z5,z130,z9])],[(0,[z131,z1,z2,z3,z4,z5,z9]),(0,[z132,z1,z2,z3,z4,z5,z9]),(0,[z133,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z134,z3,z4,z5,z9]),(0,[z1,z2,z114,z3,z4,z33,z9])],[(0,[z135,z1,z2,z3,z4,z5,z136]),(0,[z137,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z138,z9]),(0,[z1,z2,z3,z139,z4,z5,z9])],[(0,[z1,z2,z3,z140,z4,z5,z9]),(0,[z141,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z142,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z5,z9,z66]),(0,[z143,z1,z2,z3,z4,z144,z9]),(0,[z1,z2,z3,z145,z4,z85,z9])]],
   [[(1,[z1,z2,z3,z146,z5,z9]),(0,[z147,z1,z2,z3,z4,z5,z9]),(0,[z22,z1,z2,z3,z4,z85,z9]),(0,[z1,z91,z2,z3,z4,z33,z9]),(0,[z148,z1,z2,z3,z24,z5,z9]),(0,[z149,z1,z2,z3,z4,z33,z9])],[(0,[z150,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z33,z90,z9]),(0,[z1,z2,z3,z24,z27,z5,z9]),(0,[z1,z2,z8,z4,z5,z9,z151]),(0,[z1,z2,z152,z3,z4,z5,z9]),(0,[z1,z153,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z154,z5,z9]),(1,[z1,z2,z3,z24,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z155])],[(0,[z1,z2,z3,z4,z156,z5,z9]),(0,[z1,z2,z43,z3,z12,z5,z9])],[(0,[z1,z2,z3,z4,z157,z5,z9]),(0,[z158,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z159]),(1,[z1,z2,z3,z4,z160,z9]),(0,[z94,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z53,z4,z20,z9])],[(0,[z1,z161,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z162,z4,z5,z9]),(0,[z38,z1,z2,z3,z4,z5,z9]),(0,[z14,z1,z2,z3,z24,z5,z9]),(0,[z112,z1,z2,z163,z4,z5,z9])],[(0,[z1,z2,z3,z4,z164,z5,z9]),(0,[z1,z2,z3,z165,z4,z5,z9]),(0,[z11,z1,z2,z3,z4,z44,z9]),(0,[z166,z1,z2,z3,z4,z5,z9]),(0,[z167,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z168,z9]),(0,[z1,z169,z2,z3,z4,z5,z83]),(0,[z1,z2,z3,z3,z12,z5,z9]),(0,[z143,z1,z2,z3,z4,z44,z9]),(0,[z170,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z85,z5,z171])],[(0,[z1,z2,z3,z4,z5,z172,z9]),(0,[z1,z2,z3,z67,z12,z5,z9]),(0,[z1,z2,z173,z4,z5,z9,z151]),(0,[z1,z68,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z174,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z175,z9]),(0,[z1,z2,z3,z4,z176,z5,z9]),(0,[z1,z2,z3,z4,z5,z177,z9])]],
   [[(1,[z1,z2,z3,z4,z178,z9]),(0,[z2,z3,z67,z4,z19,z5,z9]),(0,[z1,z2,z3,z4,z90,z179,z9]),(0,[z1,z2,z43,z173,z4,z5,z9]),(0,[z1,z2,z3,z77,z24,z5,z9]),(0,[z1,z2,z163,z3,z4,z5,z9]),(0,[z180,z1,z2,z3,z4,z5,z9]),(0,[z181,z1,z2,z3,z4,z5,z9])],[(0,[z11,z182,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z73,z9]),(0,[z183,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z184,z5,z9]),(0,[z1,z2,z3,z4,z185,z5,z9]),(0,[z1,z129,z2,z3,z145,z4,z9])],[(0,[z1,z2,z3,z4,z19,z33,z9]),(0,[z186,z1,z2,z3,z4,z5,z9]),(0,[z38,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z187,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z188]),(0,[z1,z2,z3,z4,z5,z9,z189]),(0,[z1,z2,z3,z12,z5,z30,z9]),(0,[z1,z2,z3,z4,z190,z44,z9]),(0,[z191,z1,z2,z3,z4,z5,z9])],[(0,[z28,z11,z2,z3,z4,z5,z9]),(0,[z1,z48,z2,z3,z4,z44,z9]),(0,[z1,z7,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z173,z4,z5,z9]),(0,[z1,z192,z2,z3,z4,z5,z9]),(0,[z1,z2,z193,z3,z4,z5,z9]),(0,[z1,z3,z4,z5,z194,z9,z83]),(0,[z1,z2,z3,z4,z195,z5,z9])],[(0,[z1,z2,z3,z19,z24,z5,z9]),(0,[z1,z2,z196,z3,z4,z5,z9]),(0,[z197,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z136,z171]),(1,[z1,z2,z3,z198,z5,z9]),(0,[z14,z1,z169,z3,z4,z5,z9]),(0,[z1,z2,z3,z199,z4,z5,z9])],[(0,[z200,z1,z2,z3,z4,z5,z9]),(0,[z201,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z202,z12,z5,z9])],[(0,[z0,z1,z2,z3,z4,z178,z9]),(0,[z1,z2,z3,z4,z5,z203,z9]),(0,[z167,z2,z3,z4,z5,z9,z136]),(0,[z1,z2,z3,z4,z204,z5,z9]),(0,[z1,z2,z3,z4,z205,z5,z9]),(0,[z1,z2,z206,z3,z4,z5,z9]),(0,[z112,z1,z2,z3,z4,z207,z9]),(0,[z1,z2,z3,z32,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z20,z9]),(0,[z1,z2,z208,z3,z4,z5,z9])],[(0,[z1,z2,z209,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z210,z9]),(0,[z1,z2,z3,z4,z5,z9,z211]),(0,[z1,z2,z3,z12,z27,z5,z9]),(0,[z14,z1,z2,z3,z212,z5,z9]),(0,[z1,z2,z163,z43,z4,z5,z9]),(0,[z1,z2,z3,z4,z44,z9,z213])]],
   [[(0,[z1,z26,z3,z173,z4,z5,z9]),(0,[z1,z214,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z51,z44,z9]),(2,[z1,z2,z24,z44,z9]),(1,[z1,z2,z24,z5,z9,z151]),(0,[z1,z2,z3,z4,z44,z9,z171])],[(0,[z1,z3,z4,z51,z5,z9,z83]),(0,[z215,z1,z2,z3,z4,z5,z9])],[(0,[z21,z1,z2,z3,z4,z33,z9]),(0,[z38,z216,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z145,z51,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z217]),(0,[z1,z2,z163,z3,z12,z5,z9]),(0,[z1,z2,z3,z53,z5,z218,z9]),(0,[z1,z2,z3,z4,z5,z219,z9]),(0,[z1,z220,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z4,z221,z9]),(0,[z94,z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z222,z4,z5,z9]),(0,[z1,z2,z3,z4,z223,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z224]),(0,[z1,z2,z3,z24,z5,z9,z189]),(0,[z1,z2,z3,z4,z5,z225,z9])],[(0,[z167,z1,z2,z3,z67,z5,z9]),(0,[z1,z2,z8,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z85,z5,z226])],[(0,[z1,z2,z3,z4,z5,z227,z9]),(0,[z1,z2,z3,z173,z12,z5,z9]),(0,[z1,z7,z2,z3,z12,z5,z9]),(0,[z94,z1,z68,z2,z3,z5,z9]),(0,[z1,z2,z3,z228,z4,z5,z9])],[(0,[z229,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z230,z5,z9]),(0,[z1,z2,z3,z77,z67,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z231])],[(0,[z167,z1,z2,z3,z19,z5,z9]),(0,[z21,z1,z2,z3,z232,z5,z9]),(0,[z1,z2,z3,z24,z5,z20,z9]),(0,[z1,z2,z3,z4,z33,z5,z9])]],
   [[(1,[z0,z2,z120,z4,z5,z9]),(0,[z1,z2,z3,z120,z12,z5,z9]),(0,[z182,z1,z2,z3,z24,z5,z9]),(0,[z1,z233,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z234]),(0,[z235,z1,z2,z3,z4,z5,z9])],[(1,[z1,z214,z2,z3,z4,z9]),(0,[z1,z2,z3,z77,z19,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z9]),(0,[z1,z2,z3,z4,z5,z29,z83]),(0,[z1,z236,z2,z3,z4,z5,z9]),(0,[z143,z1,z2,z3,z4,z5,z30])],[(0,[z1,z2,z3,z4,z5,z237,z9]),(0,[z1,z2,z3,z238,z4,z5,z9]),(0,[z1,z7,z2,z173,z4,z5,z9]),(0,[z1,z239,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z240,z24,z5,z9]),(1,[z1,z2,z3,z4,z33,z9]),(0,[z241,z1,z2,z3,z4,z5,z9]),(0,[z143,z1,z2,z3,z4,z5,z9]),(0,[z143,z1,z2,z3,z242,z5,z9]),(0,[z1,z243,z2,z3,z4,z5,z9])],[(0,[z244,z1,z2,z3,z4,z5,z9]),(0,[z182,z1,z2,z89,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z245]),(0,[z1,z2,z246,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z39,z5,z9]),(0,[z143,z1,z247,z3,z4,z5,z9]),(0,[z1,z248,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z249,z5,z9]),(0,[z0,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z30,z136]),(0,[z1,z2,z3,z4,z250,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z251])],[(0,[z1,z2,z89,z3,z146,z5,z9]),(0,[z1,z2,z3,z4,z5,z252,z9]),(0,[z1,z2,z89,z4,z5,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z253]),(0,[z28,z1,z2,z3,z198,z5,z9]),(0,[z1,z2,z3,z32,z4,z5,z29]),(0,[z254,z1,z2,z3,z4,z5,z9])],[(0,[z1,z7,z3,z4,z5,z9,z83]),(0,[z1,z2,z3,z4,z190,z5,z9]),(0,[z143,z1,z255,z3,z4,z5,z9]),(1,[z2,z3,z4,z5,z9,z256])],[(1,[z1,z2,z3,z232,z5,z9]),(0,[z1,z2,z4,z5,z30,z9,z151])]],
   [[(0,[z257,z1,z2,z3,z4,z5,z9]),(0,[z258,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z259,z9]),(0,[z1,z2,z3,z4,z5,z9,z260])],[(0,[z38,z1,z2,z3,z4,z261,z9]),(0,[z1,z2,z3,z4,z5,z160,z9]),(0,[z112,z1,z2,z3,z4,z262,z9]),(0,[z143,z1,z2,z43,z4,z5,z9]),(0,[z1,z129,z2,z3,z53,z5,z9])],[(0,[z0,z1,z2,z3,z249,z5,z9]),(0,[z1,z2,z3,z67,z51,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z263]),(0,[z1,z2,z3,z4,z5,z9,z264]),(0,[z1,z2,z8,z3,z4,z265,z9]),(0,[z1,z2,z266,z3,z4,z5,z9]),(0,[z94,z1,z2,z3,z12,z5,z9])],[(0,[z1,z2,z3,z4,z154,z5,z9]),(0,[z1,z2,z3,z4,z5,z267,z9]),(1,[z1,z2,z3,z125,z5,z9]),(0,[z1,z2,z3,z4,z24,z44,z9]),(0,[z268,z1,z2,z3,z4,z5,z9]),(0,[z1,z269,z2,z3,z4,z5,z9])],[(0,[z47,z1,z2,z3,z4,z5,z9]),(0,[z11,z1,z48,z3,z4,z5,z9]),(0,[z1,z48,z3,z4,z5,z179,z9]),(0,[z1,z2,z270,z3,z4,z5,z9]),(0,[z1,z2,z3,z271,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z272]),(0,[z1,z2,z3,z4,z5,z273,z9]),(0,[z1,z2,z3,z4,z51,z5,z9]),(0,[z1,z2,z3,z4,z33,z179,z9]),(1,[z1,z2,z3,z4,z138,z9]),(1,[z1,z2,z3,z12,z33,z9]),(0,[z143,z1,z2,z3,z12,z5,z9]),(0,[z1,z274,z2,z3,z4,z5,z9])],[(0,[z21,z1,z2,z3,z53,z4,z9]),(0,[z1,z2,z3,z275,z4,z5,z9]),(0,[z1,z2,z3,z145,z24,z5,z9]),(0,[z1,z2,z3,z12,z5,z20,z9]),(0,[z143,z1,z2,z3,z4,z276,z9]),(0,[z1,z2,z3,z277,z4,z5,z9])],[(0,[z11,z2,z3,z120,z4,z5,z9]),(0,[z278,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z33,z24,z9]),(0,[z94,z1,z2,z3,z145,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z279])],[(0,[z1,z2,z3,z4,z27,z44,z9]),(0,[z1,z2,z3,z4,z33,z9,z136]),(0,[z1,z2,z280,z3,z4,z5,z9]),(0,[z281,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z30,z83]),(0,[z1,z2,z114,z3,z4,z44,z9]),(0,[z70,z1,z2,z3,z4,z5,z9]),(0,[z1,z247,z2,z3,z4,z5,z9])]],
   [[(0,[z1,z169,z7,z3,z4,z5,z9]),(0,[z1,z2,z282,z3,z4,z5,z9]),(1,[z1,z68,z3,z51,z5,z9]),(1,[z1,z239,z3,z4,z179,z9]),(0,[z1,z2,z3,z53,z4,z5,z9])],[(0,[z1,z2,z3,z283,z4,z5,z9]),(0,[z1,z2,z43,z8,z4,z5,z9]),(0,[z1,z2,z3,z4,z284,z5,z9]),(0,[z1,z2,z3,z4,z105,z9,z171]),(0,[z14,z1,z2,z3,z4,z5,z194]),(0,[z112,z1,z2,z4,z24,z5,z9]),(0,[z1,z2,z3,z4,z226,z9,z171])],[(0,[z1,z2,z285,z3,z4,z5,z9]),(0,[z1,z2,z3,z51,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z286,z9]),(0,[z1,z91,z2,z3,z4,z44,z9]),(0,[z1,z2,z114,z3,z287,z5,z9]),(0,[z94,z1,z2,z3,z4,z288,z9])],[(1,[z1,z2,z3,z289,z5,z9]),(0,[z1,z2,z3,z4,z5,z290,z9]),(0,[z291,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z292]),(0,[z28,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z293,z9]),(0,[z1,z91,z2,z3,z294,z5,z9]),(0,[z1,z2,z3,z79,z24,z5,z9]),(0,[z1,z2,z3,z4,z33,z295,z9])],[(0,[z2,z26,z3,z4,z5,z9,z136]),(0,[z296,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z297,z5,z9])],[(0,[z1,z2,z120,z4,z5,z44,z9]),(0,[z1,z2,z3,z53,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z9,z298])],[(0,[z47,z1,z2,z3,z12,z5,z9]),(0,[z116,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z299,z5,z9]),(0,[z1,z52,z2,z3,z4,z300,z9]),(0,[z14,z1,z2,z3,z301,z5,z9]),(0,[z1,z2,z3,z12,z33,z5,z9]),(0,[z94,z1,z302,z3,z4,z5,z9]),(0,[z1,z2,z3,z5,z9,z303,z171])],[(0,[z1,z2,z3,z4,z304,z5,z9]),(0,[z1,z2,z305,z53,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z306,z5,z9]),(0,[z167,z116,z2,z3,z4,z5,z9]),(0,[z1,z307,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z44,z25,z9]),(1,[z1,z2,z3,z308,z5,z9]),(0,[z1,z2,z309,z3,z4,z5,z9])],[(0,[z1,z2,z310,z3,z4,z5,z9]),(0,[z0,z1,z2,z3,z289,z5,z9]),(0,[z21,z1,z246,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z261,z9]),(0,[z1,z2,z3,z4,z311,z5,z9]),(0,[z312,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z294,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z313,z9]),(0,[z94,z1,z2,z3,z4,z314,z9]),(0,[z315,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z109,z5,z9])],[(0,[z1,z48,z7,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z5,z9]),(0,[z1,z2,z3,z4,z33,z9,z83]),(0,[z92,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z316,z5,z9]),(0,[z1,z2,z3,z145,z4,z9,z171]),(0,[z94,z317,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z318,z9]),(0,[z1,z319,z2,z3,z4,z5,z9]),(0,[z1,z52,z2,z3,z77,z5,z9]),(0,[z1,z2,z3,z4,z320,z5,z9]),(0,[z1,z2,z321,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z19,z44,z9]),(0,[z1,z322,z2,z3,z4,z5,z9]),(0,[z323,z1,z2,z3,z4,z5,z9]),(0,[z28,z1,z2,z3,z125,z5,z9]),(0,[z1,z2,z3,z4,z5,z29,z151]),(0,[z38,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z8,z3,z4,z299,z9]),(0,[z1,z2,z43,z4,z24,z5,z9]),(0,[z1,z2,z324,z3,z4,z5,z9]),(0,[z1,z2,z3,z325,z4,z5,z9]),(0,[z1,z326,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z327,z4,z5,z9])],[(0,[z1,z2,z3,z328,z4,z5,z9]),(0,[z0,z1,z2,z3,z4,z73,z9]),(0,[z1,z2,z3,z329,z4,z5,z9]),(0,[z38,z1,z2,z8,z4,z5,z9]),(1,[z1,z2,z3,z4,z330,z9]),(1,[z1,z2,z3,z32,z5,z218])],[(1,[z1,z331,z3,z4,z5,z9]),(0,[z14,z1,z2,z3,z4,z160,z9])],[(0,[z1,z2,z89,z3,z4,z33,z9]),(0,[z1,z2,z332,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z333,z5,z9]),(0,[z1,z2,z3,z4,z24,z5,z9]),(0,[z1,z334,z2,z3,z4,z5,z9]),(0,[z1,z2,z163,z3,z4,z44,z9]),(0,[z1,z2,z335,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z9,z336]),(0,[z1,z2,z3,z19,z5,z218,z9]),(0,[z1,z2,z3,z337,z4,z5,z9]),(0,[z1,z338,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z39,z9]),(0,[z339,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z340]),(0,[z1,z341,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z109,z5,z9,z171])],[(1,[z1,z246,z3,z4,z5,z9]),(0,[z1,z342,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z343]),(0,[z22,z1,z239,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z344,z9]),(1,[z1,z2,z3,z4,z225,z9]),(1,[z1,z2,z119,z4,z5,z9]),(0,[z94,z1,z2,z3,z32,z5,z9])],[(0,[z1,z2,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z345,z9]),(0,[z1,z2,z3,z4,z5,z346,z9]),(0,[z1,z2,z3,z4,z5,z347,z9]),(0,[z21,z1,z2,z3,z4,z90,z9]),(0,[z1,z2,z3,z173,z4,z44,z9]),(1,[z1,z2,z3,z4,z299,z9]),(0,[z1,z2,z3,z4,z179,z9,z171]),(0,[z1,z2,z3,z24,z311,z5,z9])],[(0,[z1,z348,z2,z3,z4,z5,z9]),(0,[z0,z1,z98,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z349]),(0,[z1,z7,z2,z8,z4,z5,z9]),(0,[z1,z2,z3,z12,z51,z5,z9]),(0,[z1,z2,z3,z350,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z351])],[(0,[z123,z1,z2,z3,z4,z5,z9]),(0,[z116,z1,z2,z3,z67,z5,z9]),(0,[z1,z2,z3,z4,z5,z352,z9]),(0,[z1,z353,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z5,z9,z354,z83]),(0,[z1,z2,z3,z355,z4,z5,z9])],[(0,[z1,z2,z3,z4,z33,z105,z9]),(0,[z1,z2,z356,z3,z24,z5,z9]),(1,[z1,z2,z3,z4,z144,z9]),(1,[z143,z1,z2,z4,z5,z151]),(0,[z1,z2,z3,z4,z5,z9,z357]),(0,[z1,z2,z3,z4,z5,z9,z358])],[(1,[z1,z2,z3,z4,z5,z267]),(0,[z149,z1,z2,z3,z4,z5,z9]),(0,[z1,z359,z2,z3,z4,z5,z9]),(0,[z1,z2,z8,z3,z4,z44,z9]),(0,[z1,z360,z2,z3,z4,z5,z9]),(0,[z1,z91,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z361]),(0,[z1,z2,z3,z4,z44,z9,z66]),(0,[z1,z2,z255,z3,z4,z5,z9]),(0,[z362,z1,z2,z3,z4,z5,z9])],[(0,[z47,z2,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z363,z4,z5,z9]),(0,[z116,z1,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z364]),(0,[z94,z1,z52,z2,z3,z5,z9]),(1,[z1,z2,z3,z301,z5,z9]),(0,[z1,z2,z3,z145,z5,z20,z9])]],
   [[(0,[z365,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z366,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z367]),(0,[z1,z2,z3,z4,z232,z5,z9]),(0,[z368,z1,z2,z3,z4,z5,z9]),(0,[z1,z369,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z24,z5,z9]),(1,[z148,z1,z2,z24,z5,z9]),(0,[z1,z129,z2,z3,z24,z5,z9]),(0,[z370,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z371,z4,z5,z9]),(0,[z94,z1,z2,z3,z4,z5,z136]),(1,[z1,z52,z3,z77,z5,z9]),(0,[z1,z2,z3,z372,z4,z5,z9]),(0,[z1,z2,z3,z4,z212,z5,z9]),(0,[z1,z2,z3,z4,z5,z373,z9]),(0,[z123,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z85,z20,z9])],[(0,[z1,z2,z3,z374,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z136]),(0,[z1,z375,z2,z3,z4,z5,z9]),(0,[z376,z1,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z3,z4,z5,z9])],[(0,[z377,z1,z2,z3,z4,z5,z9]),(0,[z378,z1,z2,z3,z4,z5,z9]),(0,[z379,z1,z2,z3,z4,z5,z9])],[(0,[z1,z52,z2,z3,z51,z5,z9]),(0,[z1,z3,z77,z4,z51,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z380]),(0,[z1,z2,z3,z145,z77,z5,z9]),(1,[z1,z2,z3,z5,z9,z354]),(0,[z1,z2,z3,z4,z33,z194,z9]),(1,[z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z381,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z288,z9]),(0,[z94,z1,z2,z3,z5,z9,z66])],[(0,[z1,z2,z3,z4,z5,z265,z9]),(1,[z1,z2,z3,z294,z5,z9]),(0,[z1,z382,z2,z3,z4,z5,z9]),(0,[z1,z2,z114,z3,z12,z5,z9]),(0,[z94,z1,z341,z3,z4,z5,z9])],[(0,[z1,z2,z50,z3,z4,z5,z9]),(0,[z14,z1,z2,z383,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z384]),(0,[z1,z2,z3,z385,z4,z5,z9]),(0,[z1,z2,z3,z4,z33,z44,z9]),(0,[z1,z2,z3,z4,z386,z5,z9]),(0,[z1,z2,z3,z4,z5,z295,z9]),(0,[z143,z1,z2,z3,z387,z5,z9])],[(0,[z1,z2,z3,z4,z5,z388,z9]),(1,[z11,z48,z3,z4,z5,z9]),(0,[z1,z98,z2,z3,z4,z5,z9]),(0,[z14,z1,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z389,z4,z33,z9]),(0,[z1,z2,z3,z390,z4,z5,z9])]],
   [[(0,[z1,z35,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z19,z5,z9]),(0,[z1,z2,z3,z4,z27,z179,z9]),(0,[z1,z2,z3,z4,z105,z27,z9]),(0,[z1,z91,z2,z3,z12,z5,z9]),(0,[z391,z1,z2,z3,z4,z5,z9]),(0,[z1,z392,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z33,z218,z9]),(0,[z1,z2,z43,z3,z4,z5,z151]),(0,[z1,z2,z43,z3,z195,z5,z9])],[(0,[z47,z1,z2,z3,z4,z345,z9]),(0,[z1,z2,z3,z4,z5,z9,z393]),(0,[z14,z394,z2,z3,z4,z5,z9]),(0,[z395,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z313,z44,z9]),(0,[z1,z2,z3,z4,z44,z30,z9]),(0,[z1,z2,z3,z4,z33,z396,z9])],[(0,[z397,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z398,z5,z9]),(0,[z1,z2,z399,z3,z4,z5,z9]),(0,[z1,z2,z3,z77,z4,z5,z9]),(1,[z1,z2,z3,z4,z400,z9]),(0,[z1,z2,z3,z366,z12,z5,z9]),(1,[z59,z1,z2,z3,z4,z171])],[(0,[z1,z2,z3,z24,z5,z9,z136]),(0,[z1,z2,z3,z32,z4,z5,z136]),(0,[z1,z91,z2,z3,z4,z179,z9])],[(0,[z1,z2,z3,z4,z289,z5,z9]),(0,[z401,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z402,z4,z5,z9]),(0,[z28,z2,z3,z4,z5,z29,z9]),(0,[z1,z68,z52,z3,z4,z5,z9]),(0,[z14,z1,z2,z3,z4,z33,z9]),(0,[z403,z1,z2,z3,z4,z44,z9])],[(0,[z47,z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z3,z249,z4,z5,z9]),(0,[z167,z1,z2,z3,z4,z33,z9]),(0,[z1,z169,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z33,z9,z151])],[(0,[z404,z1,z2,z3,z4,z5,z9]),(0,[z1,z405,z2,z3,z4,z5,z9]),(0,[z1,z129,z2,z3,z67,z5,z9]),(0,[z1,z2,z3,z4,z5,z261,z9]),(0,[z1,z2,z3,z4,z5,z406,z9]),(0,[z1,z2,z3,z12,z24,z5,z9]),(1,[z1,z2,z3,z5,z9,z303])],[(1,[z1,z2,z3,z4,z5,z172]),(0,[z1,z2,z3,z67,z5,z20,z9]),(0,[z1,z2,z3,z4,z407,z5,z9]),(0,[z1,z2,z3,z77,z4,z33,z9]),(0,[z1,z2,z3,z4,z33,z9,z408]),(0,[z1,z2,z3,z4,z5,z409,z9])]],
   [[(0,[z410,z1,z2,z3,z4,z5,z9]),(0,[z21,z1,z2,z3,z4,z5,z9]),(0,[z21,z28,z2,z3,z4,z5,z9]),(0,[z135,z1,z2,z3,z24,z5,z9]),(0,[z411,z1,z2,z3,z4,z5,z9]),(0,[z1,z412,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z413,z5,z9]),(0,[z1,z2,z302,z3,z4,z5,z9])],[(0,[z1,z129,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z4,z414,z5,z9]),(0,[z14,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z415,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z416,z9]),(1,[z1,z129,z2,z3,z145,z9]),(0,[z1,z2,z3,z145,z5,z218,z9])],[(0,[z11,z1,z2,z3,z24,z5,z9]),(0,[z2,z3,z4,z27,z5,z90,z9]),(0,[z22,z1,z2,z3,z4,z27,z9]),(0,[z1,z2,z8,z3,z4,z5,z9]),(0,[z38,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z417,z4,z5,z9])],[(0,[z47,z1,z2,z3,z4,z44,z9]),(0,[z182,z2,z89,z3,z4,z5,z9]),(0,[z1,z418,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z419,z9]),(0,[z1,z2,z3,z4,z33,z226,z9]),(0,[z1,z2,z3,z4,z5,z9,z420])],[(0,[z421,z1,z2,z3,z4,z5,z9]),(0,[z1,z68,z2,z3,z77,z5,z9]),(0,[z1,z2,z3,z4,z422,z44,z9])],[(0,[z1,z2,z26,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z423,z9])],[(0,[z424,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z425,z5,z9]),(0,[z1,z2,z3,z24,z5,z9,z83]),(0,[z1,z2,z3,z4,z33,z426,z9])],[(0,[z1,z2,z3,z4,z5,z345,z9]),(0,[z1,z48,z2,z3,z24,z5,z9]),(0,[z427,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z178,z5,z9]),(0,[z1,z2,z3,z4,z5,z428,z9]),(0,[z21,z1,z429,z3,z4,z5,z9]),(0,[z38,z1,z2,z173,z4,z5,z9]),(0,[z1,z52,z2,z3,z24,z5,z9]),(1,[z1,z2,z383,z4,z5,z9]),(0,[z1,z2,z3,z53,z4,z44,z9]),(0,[z1,z430,z2,z3,z4,z5,z9])]],
   [[(1,[z1,z2,z3,z4,z5,z9]),(0,[z28,z182,z2,z3,z4,z5,z9]),(0,[z135,z2,z3,z4,z5,z9,z136]),(1,[z1,z2,z3,z4,z333,z9]),(0,[z1,z239,z2,z3,z4,z5,z9]),(0,[z59,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z12,z4,z24,z5,z9]),(0,[z1,z192,z2,z3,z12,z5,z9]),(1,[z1,z2,z3,z242,z5,z9]),(0,[z1,z2,z3,z4,z431,z5,z9])],[(0,[z1,z2,z3,z432,z4,z5,z9]),(0,[z21,z1,z2,z3,z4,z5,z263]),(0,[z1,z433,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z5,z9,z136]),(0,[z1,z2,z434,z3,z4,z5,z9])],[(0,[z21,z1,z2,z3,z12,z5,z9]),(1,[z394,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z435,z4,z44,z9]),(1,[z1,z2,z4,z436,z5,z9])],[(0,[z1,z2,z331,z3,z4,z5,z9]),(0,[z2,z89,z3,z120,z4,z5,z9]),(0,[z437,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z438,z4,z5,z9]),(1,[z1,z2,z163,z4,z44,z9])],[(0,[z439,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z8,z3,z12,z5,z9]),(0,[z1,z382,z2,z3,z5,z9,z83]),(0,[z1,z2,z3,z4,z440,z5,z9]),(1,[z1,z255,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z441,z9]),(1,[z1,z2,z3,z4,z85,z226])],[(0,[z1,z442,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z443,z9]),(0,[z1,z444,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z445,z4,z5,z9]),(0,[z148,z1,z2,z3,z308,z5,z9]),(0,[z1,z2,z3,z446,z4,z5,z9])],[(0,[z0,z1,z2,z3,z4,z5,z9]),(0,[z21,z1,z129,z2,z3,z4,z9]),(0,[z216,z1,z2,z3,z4,z5,z9]),(0,[z1,z52,z169,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z194,z30]),(0,[z1,z129,z2,z3,z4,z20,z9]),(0,[z1,z2,z3,z4,z20,z9,z171]),(0,[z1,z2,z3,z4,z447,z5,z9])],[(0,[z448,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z449]),(0,[z1,z2,z450,z3,z4,z5,z9]),(0,[z182,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z12,z19,z5,z9]),(1,[z1,z429,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z90,z9]),(0,[z1,z2,z8,z3,z451,z5,z9]),(0,[z1,z2,z3,z4,z5,z194,z9])]],
   [[(0,[z1,z452,z2,z3,z4,z5,z9]),(0,[z453,z1,z2,z3,z4,z5,z9]),(0,[z1,z169,z3,z173,z4,z5,z9]),(0,[z1,z454,z2,z3,z4,z5,z9]),(0,[z403,z1,z2,z3,z4,z5,z9]),(0,[z455,z1,z2,z3,z4,z5,z9]),(0,[z456,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z457]),(0,[z1,z2,z3,z458,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z263]),(0,[z1,z2,z3,z4,z5,z44,z9])],[(0,[z459,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z460]),(0,[z1,z239,z2,z3,z12,z5,z9]),(1,[z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z228,z12,z5,z9]),(1,[z1,z2,z3,z461,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z449]),(0,[z0,z1,z2,z3,z4,z33,z9]),(0,[z182,z2,z3,z4,z5,z9,z136]),(0,[z1,z462,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z463,z4,z5,z9]),(0,[z1,z2,z3,z4,z464,z5,z9]),(1,[z1,z2,z3,z4,z276,z9]),(0,[z1,z2,z3,z4,z5,z218,z9]),(0,[z1,z465,z2,z3,z4,z5,z9])],[(0,[z1,z2,z8,z120,z4,z5,z9]),(0,[z1,z2,z3,z4,z146,z5,z9]),(0,[z28,z1,z2,z3,z4,z5,z29]),(0,[z1,z91,z2,z3,z4,z105,z9]),(0,[z1,z2,z466,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z262,z5,z9]),(0,[z1,z2,z3,z4,z44,z20,z9]),(0,[z1,z2,z467,z3,z4,z5,z9]),(0,[z468,z1,z2,z3,z4,z5,z9])],[(0,[z0,z1,z2,z3,z4,z5,z449]),(1,[z216,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z451,z5,z9]),(0,[z1,z68,z2,z3,z51,z5,z9]),(0,[z469,z1,z2,z3,z4,z5,z9]),(0,[z1,z239,z2,z3,z4,z179,z9]),(0,[z1,z2,z3,z4,z85,z5,z9]),(0,[z59,z1,z2,z3,z4,z9,z171])],[(0,[z1,z2,z3,z470,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z471,z9]),(0,[z1,z2,z3,z301,z4,z5,z9]),(0,[z1,z2,z3,z4,z472,z5,z9])],[]],
   [[(0,[z1,z7,z26,z3,z4,z5,z9]),(0,[z473,z1,z2,z3,z4,z5,z9]),(0,[z0,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z24,z5,z90,z9]),(0,[z1,z2,z474,z3,z4,z5,z9]),(0,[z1,z475,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z194,z9]),(0,[z1,z2,z3,z4,z5,z476,z9]),(0,[z1,z2,z3,z4,z422,z5,z9])],[(0,[z1,z2,z3,z4,z221,z5,z9]),(0,[z477,z1,z2,z3,z4,z5,z9]),(0,[z22,z1,z2,z3,z24,z5,z9]),(0,[z28,z1,z2,z3,z4,z5,z9]),(0,[z2,z3,z4,z5,z29,z9,z136]),(1,[z1,z2,z3,z4,z118,z9]),(0,[z1,z2,z3,z4,z5,z226,z29]),(0,[z1,z2,z3,z478,z4,z5,z9]),(0,[z112,z1,z2,z3,z24,z5,z9]),(0,[z143,z1,z2,z3,z4,z5,z151]),(0,[z1,z2,z3,z4,z5,z9,z479])],[(1,[z1,z2,z3,z4,z99,z9]),(0,[z1,z2,z3,z4,z5,z480,z9]),(0,[z1,z2,z3,z24,z5,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z408]),(0,[z1,z2,z3,z4,z5,z481,z9]),(1,[z1,z2,z3,z4,z288,z9])],[(0,[z1,z2,z3,z4,z482,z5,z9]),(0,[z1,z2,z3,z4,z29,z9,z393]),(1,[z1,z2,z3,z4,z265,z9]),(1,[z1,z382,z2,z3,z5,z9]),(0,[z123,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z355,z4,z44,z9])],[(0,[z1,z2,z3,z483,z4,z5,z9]),(0,[z1,z2,z3,z33,z24,z5,z9]),(0,[z1,z2,z3,z24,z5,z218,z9]),(0,[z1,z2,z3,z145,z4,z33,z9]),(0,[z1,z2,z3,z4,z33,z85,z9])],[(0,[z1,z2,z3,z4,z5,z484,z9]),(0,[z1,z2,z3,z4,z400,z5,z9]),(0,[z485,z1,z2,z3,z4,z5,z9]),(0,[z486,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z487,z4,z5,z9]),(0,[z1,z2,z3,z24,z85,z5,z9]),(0,[z1,z2,z3,z435,z4,z5,z9]),(1,[z1,z302,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z226,z9])],[(1,[z1,z2,z3,z4,z9,z393]),(0,[z1,z2,z3,z488,z4,z5,z9]),(0,[z143,z430,z2,z3,z4,z5,z9])]],
   [[(0,[z0,z1,z2,z120,z4,z5,z9]),(0,[z71,z1,z2,z3,z4,z5,z9]),(0,[z116,z1,z2,z3,z4,z5,z9]),(0,[z1,z489,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z198,z5,z9]),(0,[z1,z2,z3,z490,z4,z5,z9]),(0,[z148,z1,z2,z3,z491,z5,z9]),(0,[z1,z492,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z493,z9])],[(0,[z47,z1,z48,z3,z4,z5,z9]),(0,[z1,z169,z2,z3,z4,z5,z194]),(0,[z148,z1,z2,z3,z4,z44,z9])],[(0,[z1,z2,z3,z494,z4,z5,z9]),(0,[z1,z2,z3,z4,z44,z90,z9]),(0,[z1,z2,z3,z4,z85,z179,z9]),(1,[z1,z2,z305,z4,z5,z9]),(1,[z317,z2,z3,z4,z5,z9])],[(0,[z28,z1,z2,z3,z12,z5,z9]),(0,[z38,z1,z2,z3,z56,z5,z9]),(0,[z1,z495,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z496,z5,z9]),(0,[z1,z2,z43,z3,z24,z5,z9]),(0,[z94,z1,z2,z3,z53,z5,z9]),(0,[z1,z2,z3,z497,z4,z5,z9])],[(0,[z1,z2,z498,z3,z4,z5,z9]),(0,[z1,z2,z89,z3,z4,z5,z9]),(0,[z28,z2,z3,z120,z4,z5,z9]),(0,[z1,z2,z3,z4,z499,z5,z9]),(0,[z500,z1,z2,z3,z4,z5,z9]),(0,[z116,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z53,z12,z5,z9]),(0,[z1,z2,z3,z4,z5,z501,z9])],[(0,[z1,z2,z3,z12,z5,z90,z9]),(0,[z22,z1,z2,z3,z4,z9,z171]),(0,[z14,z1,z2,z3,z4,z44,z9]),(0,[z502,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z5,z194,z9]),(0,[z1,z2,z3,z4,z44,z259,z9]),(0,[z1,z2,z3,z308,z4,z5,z9])],[(0,[z11,z1,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z503,z4,z5,z9]),(0,[z504,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z3,z24,z5,z9]),(0,[z1,z2,z3,z24,z5,z226,z9])]],
   [[(0,[z1,z2,z3,z67,z24,z5,z9]),(0,[z2,z3,z4,z27,z5,z9,z136]),(0,[z1,z68,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z505]),(0,[z1,z2,z3,z53,z4,z179,z9]),(1,[z1,z2,z3,z4,z207,z9]),(0,[z1,z2,z3,z12,z5,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z506])],[(0,[z1,z2,z3,z4,z4,z5,z9]),(0,[z1,z169,z3,z4,z51,z5,z9]),(0,[z1,z2,z3,z77,z4,z44,z9]),(1,[z1,z2,z163,z12,z5,z9])],[(0,[z1,z2,z3,z4,z507,z5,z9]),(0,[z1,z2,z3,z12,z5,z218,z9])],[(0,[z1,z2,z3,z508,z4,z5,z9]),(0,[z1,z2,z3,z4,z33,z27,z9]),(0,[z1,z509,z2,z3,z4,z5,z9]),(0,[z14,z1,z2,z3,z4,z5,z83])],[(0,[z14,z1,z2,z3,z4,z400,z9]),(0,[z1,z2,z3,z12,z85,z5,z9]),(0,[z510,z1,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z511]),(0,[z1,z113,z2,z3,z4,z5,z9]),(0,[z512,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z305,z3,z4,z5,z9])],[(0,[z513,z1,z2,z3,z4,z5,z9]),(0,[z1,z514,z2,z3,z4,z5,z9]),(0,[z1,z239,z2,z3,z4,z105,z9]),(0,[z1,z2,z3,z4,z5,z9,z515]),(0,[z59,z1,z2,z3,z4,z5,z171])],[(0,[z0,z1,z331,z3,z4,z5,z9]),(0,[z1,z2,z89,z3,z12,z5,z9]),(0,[z1,z2,z3,z4,z516,z5,z9]),(1,[z1,z2,z3,z4,z5,z367]),(0,[z21,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z517,z9]),(0,[z1,z2,z4,z24,z5,z44,z9]),(0,[z1,z2,z356,z3,z4,z5,z9]),(0,[z1,z2,z3,z145,z53,z4,z9]),(1,[z110,z2,z3,z4,z5,z9])]],
   [[(0,[z22,z1,z2,z3,z53,z4,z9]),(1,[z38,z1,z173,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z276,z9]),(0,[z1,z2,z3,z4,z5,z9,z518])],[(0,[z1,z2,z3,z4,z519,z5,z9]),(0,[z1,z2,z3,z520,z4,z5,z9])],[(0,[z521,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z179,z9]),(0,[z1,z2,z3,z4,z33,z386,z9]),(0,[z1,z129,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z56,z5,z9]),(0,[z1,z52,z2,z3,z5,z218,z9]),(0,[z1,z2,z163,z3,z24,z5,z9]),(0,[z1,z514,z2,z3,z4,z33,z9])],[(0,[z28,z2,z26,z3,z4,z5,z9]),(1,[z1,z35,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z29,z194]),(0,[z38,z126,z2,z3,z4,z5,z9]),(0,[z1,z2,z356,z3,z4,z33,z9]),(1,[z1,z2,z3,z387,z5,z9])],[(0,[z1,z2,z3,z10,z4,z5,z9]),(0,[z522,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z523,z9]),(0,[z1,z2,z3,z12,z5,z226,z9]),(0,[z1,z2,z3,z389,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z256])],[(0,[z167,z2,z3,z67,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z29,z171]),(0,[z1,z2,z3,z173,z24,z5,z9]),(0,[z1,z7,z2,z3,z24,z5,z9]),(0,[z524,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z24,z5,z9,z151]),(1,[z1,z2,z3,z491,z5,z9])],[(0,[z1,z26,z3,z4,z5,z179,z9]),(0,[z1,z2,z89,z3,z4,z99,z9]),(0,[z1,z2,z3,z4,z5,z525,z9]),(0,[z1,z2,z3,z4,z33,z29,z9]),(0,[z1,z239,z2,z3,z4,z44,z9]),(1,[z148,z1,z2,z4,z33,z9]),(0,[z1,z129,z2,z3,z4,z33,z9]),(0,[z1,z2,z53,z4,z436,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z526,z9]),(0,[z1,z2,z3,z4,z5,z194,z136]),(0,[z1,z2,z114,z3,z185,z5,z9])],[(0,[z1,z2,z3,z120,z24,z5,z9]),(0,[z1,z527,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z118,z5,z9]),(0,[z1,z2,z3,z528,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z529]),(0,[z123,z1,z2,z3,z12,z5,z9])],[(0,[z1,z2,z3,z4,z5,z530,z9]),(0,[z38,z1,z2,z3,z238,z5,z9]),(0,[z531,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z32,z51,z5,z9]),(0,[z1,z2,z3,z4,z33,z24,z9]),(1,[z1,z2,z3,z287,z5,z9]),(0,[z1,z2,z119,z3,z4,z5,z9])],[(0,[z1,z91,z48,z3,z4,z5,z9]),(0,[z167,z1,z2,z3,z4,z5,z9]),(0,[z167,z28,z2,z3,z4,z5,z9]),(0,[z532,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z179,z9]),(0,[z1,z533,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z262,z9]),(0,[z395,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z534,z4,z5,z9])],[(0,[z535,z1,z2,z3,z4,z5,z9]),(0,[z59,z1,z2,z3,z4,z5,z226])],[(0,[z0,z1,z2,z3,z4,z44,z9])],[(0,[z536,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z537,z5,z9])],[(1,[z21,z2,z3,z4,z90,z9]),(0,[z1,z2,z538,z3,z4,z5,z9]),(0,[z1,z169,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z389,z12,z5,z9]),(0,[z1,z2,z3,z12,z5,z9,z506])]],
   [[(0,[z0,z182,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z539,z9]),(0,[z540,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z83]),(0,[z1,z2,z3,z12,z4,z5,z9]),(0,[z1,z2,z3,z541,z4,z5,z9]),(1,[z1,z2,z3,z53,z20,z9])],[(0,[z1,z2,z3,z4,z542,z5,z9]),(0,[z1,z543,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z544,z4,z5,z9]),(0,[z1,z2,z3,z53,z4,z105,z9]),(1,[z1,z2,z3,z12,z44,z9]),(0,[z1,z545,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z546,z4,z5,z9]),(0,[z135,z1,z2,z3,z4,z5,z9]),(0,[z28,z1,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z547,z4,z5,z9]),(0,[z548,z1,z2,z3,z4,z5,z9])],[(0,[z549,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z550,z9]),(0,[z94,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z43,z3,z4,z330,z9]),(0,[z1,z2,z3,z4,z551,z5,z9]),(0,[z94,z1,z2,z325,z4,z5,z9])],[(0,[z48,z2,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z552,z4,z5,z9]),(1,[z126,z2,z3,z4,z5,z9]),(0,[z1,z169,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z85,z44,z9])],[(0,[z1,z2,z3,z553,z4,z5,z9]),(0,[z167,z1,z2,z3,z12,z5,z9]),(0,[z21,z1,z91,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z554,z9]),(0,[z1,z2,z3,z4,z44,z179,z9]),(0,[z1,z2,z3,z4,z5,z207,z9]),(0,[z143,z1,z2,z3,z24,z5,z9]),(0,[z1,z392,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z12,z4,z33,z9])],[(0,[z1,z2,z555,z3,z4,z5,z9]),(1,[z28,z2,z3,z4,z5,z29]),(0,[z1,z2,z556,z3,z4,z5,z9]),(0,[z557,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z558,z5,z9])],[(0,[z148,z1,z2,z120,z4,z5,z9]),(0,[z1,z2,z559,z3,z4,z5,z9]),(0,[z1,z2,z560,z3,z4,z5,z9]),(0,[z561,z1,z2,z3,z4,z5,z9]),(0,[z135,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z226,z136]),(0,[z1,z2,z3,z4,z5,z562,z9]),(0,[z1,z2,z3,z77,z12,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z563]),(0,[z1,z2,z163,z3,z4,z42,z9]),(0,[z564,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z43,z3,z4,z225,z9]),(0,[z1,z565,z2,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z5,z566,z9]),(0,[z1,z2,z3,z4,z44,z9,z136]),(0,[z28,z1,z2,z3,z4,z44,z9]),(0,[z1,z8,z3,z173,z4,z5,z9]),(0,[z1,z2,z3,z4,z567,z5,z9])],[(0,[z568,z1,z2,z3,z4,z5,z9]),(0,[z11,z1,z2,z3,z4,z33,z9]),(1,[z1,z2,z120,z4,z44,z9]),(0,[z1,z52,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z5,z179,z9]),(0,[z569,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z570,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z571]),(0,[z1,z2,z572,z3,z4,z5,z9]),(0,[z38,z1,z2,z3,z4,z5,z62]),(0,[z1,z2,z3,z573,z4,z5,z9]),(0,[z1,z2,z3,z541,z12,z5,z9]),(0,[z59,z1,z2,z3,z4,z5,z9])],[(0,[z1,z91,z26,z3,z4,z5,z9]),(0,[z574,z1,z2,z3,z4,z5,z9]),(0,[z575,z1,z2,z3,z4,z5,z9]),(0,[z576,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z558,z33,z9]),(0,[z1,z577,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z32,z4,z5,z218])],[(0,[z1,z2,z26,z3,z4,z33,z9]),(0,[z578,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z579,z5,z9]),(0,[z580,z1,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z163,z4,z5,z9]),(0,[z548,z1,z2,z3,z12,z5,z9]),(1,[z1,z247,z3,z4,z5,z9])],[(0,[z581,z1,z2,z3,z4,z5,z9]),(0,[z11,z2,z3,z4,z5,z9,z136]),(0,[z182,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z582,z4,z5,z9]),(0,[z1,z2,z3,z4,z583,z5,z9]),(0,[z14,z1,z3,z4,z5,z9,z83]),(0,[z1,z2,z3,z32,z24,z5,z9]),(0,[z1,z2,z3,z242,z4,z5,z9])],[(0,[z1,z2,z3,z4,z584,z5,z9]),(0,[z1,z48,z2,z3,z4,z33,z9]),(1,[z1,z2,z3,z140,z5,z9]),(0,[z38,z1,z7,z3,z4,z5,z9]),(0,[z1,z52,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z585,z4,z5,z9])],[(0,[z47,z1,z2,z3,z24,z5,z9]),(0,[z116,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z136,z83]),(0,[z586,z1,z2,z3,z4,z5,z9]),(0,[z59,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z33,z9,z171]),(0,[z1,z2,z3,z4,z5,z9,z587]),(0,[z1,z2,z3,z588,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z589])]],
   [[(0,[z590,z1,z2,z3,z4,z5,z9]),(0,[z1,z239,z3,z4,z5,z179,z9]),(0,[z1,z2,z3,z464,z24,z5,z9]),(0,[z1,z2,z114,z4,z5,z44,z9]),(0,[z148,z1,z2,z4,z33,z5,z9]),(0,[z591,z1,z2,z3,z4,z5,z9])],[(0,[z94,z1,z2,z3,z67,z5,z9]),(0,[z1,z2,z3,z4,z5,z592,z9]),(0,[z1,z2,z3,z4,z105,z5,z9]),(0,[z564,z1,z2,z3,z12,z5,z9]),(0,[z1,z593,z2,z3,z4,z5,z9]),(1,[z1,z2,z43,z4,z5,z30]),(0,[z594,z1,z2,z3,z4,z5,z9]),(0,[z1,z595,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z85,z226,z9])],[(0,[z47,z1,z2,z3,z371,z5,z9]),(1,[z1,z2,z3,z596,z5,z9]),(0,[z28,z2,z3,z4,z27,z5,z9]),(0,[z1,z2,z3,z4,z5,z29,z9]),(0,[z1,z597,z2,z3,z4,z5,z9]),(1,[z1,z2,z4,z33,z44,z9]),(0,[z1,z598,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z583,z33,z9]),(0,[z1,z599,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z600,z9])],[(0,[z1,z2,z601,z3,z4,z5,z9]),(1,[z1,z322,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z9,z602]),(0,[z1,z2,z3,z603,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z604,z9]),(0,[z1,z2,z3,z4,z44,z9,z83]),(0,[z1,z2,z3,z4,z144,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z605])],[(0,[z606,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z89,z3,z4,z44,z9]),(0,[z94,z1,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z67,z5,z218,z9]),(0,[z1,z68,z3,z4,z51,z5,z9]),(0,[z1,z68,z2,z3,z5,z218,z9]),(0,[z1,z2,z3,z4,z5,z607,z9]),(0,[z608,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z42,z9]),(0,[z94,z1,z2,z3,z4,z5,z66])],[(0,[z47,z1,z2,z3,z4,z5,z571]),(0,[z1,z2,z89,z8,z4,z5,z9]),(0,[z21,z1,z2,z3,z4,z85,z9]),(0,[z609,z1,z2,z3,z4,z5,z9]),(0,[z1,z91,z3,z4,z105,z5,z9]),(0,[z1,z2,z3,z12,z537,z5,z9]),(1,[z1,z2,z3,z185,z5,z9]),(0,[z1,z2,z3,z4,z387,z5,z9]),(0,[z94,z45,z2,z3,z4,z5,z9]),(0,[z1,z2,z610,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z611,z9]),(0,[z1,z612,z2,z3,z4,z5,z9]),(0,[z1,z613,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z330,z5,z9]),(0,[z110,z2,z3,z4,z5,z226,z9])],[(0,[z182,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z12,z5,z9,z83]),(0,[z1,z2,z3,z4,z491,z5,z9]),(1,[z1,z2,z3,z195,z5,z9])]],
   [[(0,[z47,z1,z2,z555,z4,z5,z9]),(0,[z1,z3,z173,z4,z5,z9,z83]),(0,[z1,z129,z2,z3,z4,z105,z9]),(0,[z1,z2,z3,z4,z5,z9,z354]),(0,[z1,z2,z3,z4,z240,z5,z9]),(0,[z1,z2,z3,z4,z44,z554,z9])],[(0,[z1,z2,z3,z614,z4,z5,z9]),(0,[z1,z2,z3,z4,z615,z5,z9])],[(0,[z1,z2,z616,z3,z4,z5,z9]),(0,[z1,z2,z3,z617,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z618,z9]),(1,[z1,z2,z3,z4,z5,z62]),(1,[z1,z2,z3,z4,z300,z9]),(0,[z1,z2,z3,z24,z105,z5,z9]),(1,[z1,z2,z12,z24,z5,z9]),(0,[z1,z2,z3,z145,z4,z5,z9])],[(0,[z619,z1,z2,z3,z4,z5,z9]),(0,[z22,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z29,z9]),(0,[z1,z91,z2,z3,z284,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z620]),(0,[z112,z1,z2,z3,z4,z5,z9]),(0,[z1,z593,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z4,z5,z621,z9]),(0,[z1,z2,z4,z33,z5,z44,z9]),(0,[z81,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z151]),(0,[z1,z2,z3,z4,z622,z5,z9])],[(0,[z1,z2,z3,z4,z623,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z624])],[(0,[z1,z214,z2,z26,z3,z4,z9]),(0,[z1,z2,z3,z4,z625,z5,z9]),(0,[z1,z48,z3,z173,z4,z5,z9]),(0,[z0,z2,z3,z120,z4,z5,z9]),(0,[z21,z1,z2,z432,z4,z5,z9]),(0,[z626,z1,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z114,z4,z5,z9]),(1,[z430,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z77,z32,z5,z9]),(0,[z1,z2,z3,z4,z5,z194,z151]),(0,[z1,z2,z3,z4,z396,z5,z9]),(0,[z1,z492,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z32,z4,z5,z66]),(0,[z1,z2,z3,z627,z4,z5,z9])],[(0,[z182,z1,z2,z120,z4,z5,z9]),(0,[z2,z3,z120,z4,z5,z9,z136]),(1,[z15,z2,z3,z4,z5,z9]),(0,[z628,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z114,z4,z44,z9]),(0,[z629,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z461,z4,z5,z9])]],
   [[(1,[z47,z26,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z530,z9]),(0,[z22,z1,z2,z3,z4,z33,z9]),(0,[z112,z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z163,z4,z5,z44,z9]),(0,[z143,z81,z2,z3,z4,z5,z9]),(0,[z630,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z631,z3,z4,z5,z9])],[(1,[z1,z2,z3,z329,z4,z9]),(0,[z1,z2,z3,z4,z5,z9,z632]),(0,[z633,z1,z2,z3,z4,z5,z9]),(0,[z14,z1,z2,z134,z4,z5,z9]),(0,[z1,z129,z2,z3,z4,z44,z9]),(0,[z634,z1,z2,z3,z4,z5,z9])],[(0,[z167,z1,z2,z3,z4,z5,z367]),(0,[z1,z334,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z635,z9]),(0,[z1,z2,z3,z4,z5,z9,z303])],[],[(0,[z21,z1,z2,z3,z4,z27,z9]),(0,[z1,z169,z3,z4,z5,z194,z9]),(0,[z1,z2,z3,z24,z5,z9,z151]),(0,[z636,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z145,z12,z5,z9]),(1,[z1,z2,z3,z4,z314,z9])],[(0,[z2,z26,z3,z120,z4,z5,z9]),(1,[z1,z2,z432,z4,z5,z9]),(0,[z1,z2,z3,z637,z4,z5,z9]),(1,[z1,z91,z3,z4,z105,z9]),(0,[z1,z2,z3,z4,z44,z194,z9]),(0,[z1,z2,z638,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z639,z5,z9]),(0,[z1,z2,z114,z3,z24,z5,z9]),(0,[z477,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z43,z3,z4,z5,z9]),(0,[z2,z3,z4,z5,z226,z9,z256]),(0,[z1,z2,z3,z4,z5,z9,z640])],[(0,[z1,z2,z3,z4,z5,z641,z9]),(0,[z1,z2,z3,z596,z4,z5,z9]),(1,[z112,z1,z2,z24,z5,z9]),(0,[z1,z2,z163,z4,z5,z9,z151]),(0,[z1,z2,z3,z4,z44,z44,z9]),(0,[z1,z642,z2,z3,z4,z5,z9])]],
   [[(0,[z182,z2,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z643,z5,z9]),(0,[z1,z644,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z105,z5,z9]),(0,[z1,z2,z3,z383,z4,z5,z9]),(0,[z645,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z646,z4,z5,z9])],[(0,[z1,z2,z3,z3,z4,z5,z9]),(0,[z1,z2,z647,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z5,z29,z9]),(0,[z1,z2,z3,z77,z5,z9,z66]),(0,[z1,z91,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z44,z218,z9]),(0,[z1,z2,z3,z4,z5,z9,z213]),(0,[z1,z648,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z67,z4,z5,z9]),(0,[z167,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z136,z151]),(0,[z1,z68,z2,z3,z4,z5,z9]),(0,[z1,z649,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z650]),(0,[z1,z2,z3,z4,z5,z9,z171])],[(0,[z1,z651,z2,z3,z4,z5,z9]),(0,[z1,z2,z89,z3,z140,z5,z9]),(0,[z652,z1,z2,z3,z4,z5,z9]),(0,[z1,z653,z2,z3,z4,z5,z9]),(0,[z1,z654,z2,z3,z4,z5,z9]),(0,[z15,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z635,z9]),(0,[z1,z2,z43,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z426,z5,z9]),(0,[z1,z2,z3,z4,z436,z5,z9])],[(0,[z21,z1,z2,z3,z4,z5,z237])],[(0,[z116,z1,z2,z3,z12,z5,z9]),(0,[z655,z1,z2,z3,z4,z5,z9]),(0,[z1,z429,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z656,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z657]),(0,[z658,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z643,z33,z9]),(0,[z659,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z53,z5,z20,z9])],[(0,[z1,z91,z239,z3,z4,z5,z9]),(0,[z1,z169,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z44,z9,z151]),(0,[z1,z2,z3,z3,z4,z33,z9])],[(0,[z1,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z660,z5,z9]),(0,[z1,z2,z3,z67,z4,z33,z9]),(0,[z1,z2,z3,z661,z4,z5,z9]),(0,[z1,z68,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z662,z4,z5,z9]),(0,[z1,z2,z3,z12,z4,z44,z9])]],
   [[(0,[z148,z1,z2,z89,z4,z5,z9]),(0,[z1,z2,z3,z202,z4,z5,z9]),(0,[z1,z2,z3,z4,z663,z5,z9]),(0,[z1,z2,z3,z4,z664,z5,z9]),(0,[z1,z2,z665,z3,z4,z5,z9]),(0,[z1,z666,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z4,z24,z5,z9]),(0,[z1,z2,z3,z12,z615,z5,z9]),(0,[z1,z2,z43,z3,z461,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z667]),(0,[z135,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z668,z9]),(0,[z1,z394,z2,z3,z4,z5,z9])],[(1,[z1,z2,z89,z4,z44,z9]),(0,[z669,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z53,z77,z5,z9]),(1,[z1,z2,z134,z4,z5,z9]),(1,[z1,z2,z4,z24,z44,z9]),(0,[z1,z2,z3,z12,z5,z9,z151]),(0,[z1,z2,z3,z12,z5,z621,z9]),(0,[z96,z1,z2,z3,z4,z5,z9]),(0,[z659,z1,z2,z3,z4,z33,z9])],[(0,[z670,z1,z2,z3,z4,z5,z9]),(0,[z38,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z671,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z9,z171])],[(0,[z47,z1,z26,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z237]),(0,[z1,z2,z3,z4,z44,z226,z9])],[(0,[z1,z2,z3,z672,z4,z5,z9]),(1,[z182,z2,z89,z4,z5,z9]),(0,[z167,z1,z2,z3,z4,z5,z172]),(0,[z1,z2,z3,z4,z673,z5,z9]),(1,[z1,z2,z3,z284,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z674])],[(0,[z47,z11,z2,z3,z4,z5,z9]),(0,[z675,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z26,z3,z4,z44,z9]),(0,[z1,z2,z3,z676,z4,z5,z9]),(1,[z1,z2,z24,z5,z44,z9])],[(0,[z1,z2,z89,z173,z4,z5,z9]),(0,[z677,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z300,z9]),(0,[z1,z2,z3,z4,z678,z5,z9])]],
   [[(0,[z1,z2,z679,z3,z4,z5,z9]),(0,[z38,z1,z2,z3,z4,z5,z680]),(0,[z1,z52,z2,z3,z4,z44,z9]),(1,[z1,z341,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z451,z5,z9]),(0,[z59,z1,z2,z3,z4,z44,z9]),(0,[z143,z1,z2,z4,z5,z9,z151]),(0,[z1,z2,z3,z32,z5,z218,z9])],[(0,[z681,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z163,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z44,z641,z9]),(0,[z682,z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z9,z683]),(0,[z1,z2,z684,z3,z4,z5,z9])],[(0,[z1,z2,z3,z120,z4,z5,z9]),(0,[z21,z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z685,z9])],[(0,[z1,z2,z3,z4,z5,z9,z686]),(0,[z182,z1,z2,z3,z4,z44,z9]),(1,[z116,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z687]),(0,[z1,z688,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z297,z24,z5,z9])],[(0,[z1,z2,z3,z4,z5,z9,z689]),(0,[z1,z2,z89,z3,z4,z530,z9]),(0,[z2,z3,z4,z19,z5,z9,z136]),(0,[z1,z2,z3,z173,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z9,z690]),(0,[z1,z7,z2,z3,z4,z33,z9]),(0,[z1,z2,z8,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z33,z9,z66])],[(0,[z47,z1,z2,z3,z154,z5,z9]),(0,[z1,z2,z3,z4,z105,z90,z9])],[(0,[z1,z691,z2,z3,z4,z5,z9]),(0,[z1,z129,z2,z3,z12,z5,z9]),(0,[z692,z1,z2,z3,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z120,z4,z33,z9]),(0,[z135,z1,z2,z3,z4,z5,z29]),(0,[z1,z3,z4,z105,z5,z179,z9]),(0,[z1,z2,z3,z4,z105,z44,z9]),(0,[z1,z593,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z4,z314,z5,z9])],[(0,[z1,z2,z3,z12,z5,z9,z171])],[(0,[z1,z129,z2,z3,z4,z179,z9])],[(0,[z1,z322,z2,z3,z4,z19,z9]),(0,[z21,z2,z3,z4,z5,z9,z136]),(0,[z1,z2,z3,z53,z51,z5,z9]),(0,[z1,z239,z2,z3,z24,z5,z9]),(1,[z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z693,z4,z5,z9]),(0,[z1,z129,z2,z3,z145,z5,z9]),(1,[z1,z2,z325,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z694])],[(0,[z1,z2,z3,z329,z4,z19,z9]),(0,[z1,z2,z163,z3,z4,z138,z9]),(0,[z94,z1,z2,z3,z4,z5,z218])],[(0,[z135,z28,z2,z3,z4,z5,z9]),(0,[z1,z613,z2,z3,z4,z44,z9]),(0,[z1,z695,z2,z3,z4,z5,z9]),(0,[z94,z1,z2,z3,z4,z5,z9])],[(1,[z1,z2,z3,z371,z5,z9]),(0,[z38,z1,z3,z173,z4,z5,z9]),(0,[z1,z2,z3,z287,z4,z5,z9])],[(0,[z11,z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z120,z173,z4,z5,z9]),(0,[z1,z2,z8,z3,z82,z5,z9]),(0,[z1,z236,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z5,z218,z9,z66])]],
   [[(0,[z21,z1,z2,z3,z4,z9,z171]),(0,[z22,z1,z2,z3,z4,z90,z9]),(1,[z1,z2,z3,z4,z5,z680]),(0,[z1,z2,z3,z4,z5,z83,z151]),(0,[z1,z2,z3,z4,z5,z84,z9]),(0,[z1,z2,z3,z4,z33,z30,z9])],[(0,[z696,z1,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z571]),(1,[z167,z2,z3,z67,z5,z9]),(0,[z1,z2,z3,z145,z4,z44,z9]),(0,[z1,z2,z3,z4,z33,z33,z9]),(0,[z1,z697,z2,z3,z4,z5,z9]),(0,[z1,z317,z2,z3,z4,z5,z9])],[(0,[z1,z2,z26,z3,z4,z5,z9]),(0,[z1,z698,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z3,z4,z44,z9]),(0,[z112,z1,z2,z3,z4,z44,z9]),(1,[z1,z2,z43,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z25,z9]),(0,[z1,z695,z2,z3,z4,z33,z9]),(0,[z94,z1,z2,z3,z4,z33,z9])],[(0,[z1,z2,z699,z3,z4,z5,z9]),(0,[z1,z700,z2,z3,z4,z5,z9]),(1,[z135,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z51,z5,z9,z66]),(0,[z701,z1,z2,z3,z4,z5,z9]),(0,[z1,z702,z2,z3,z4,z5,z9]),(0,[z1,z703,z2,z3,z4,z5,z9])],[(0,[z1,z48,z2,z3,z4,z5,z9]),(1,[z1,z2,z555,z4,z5,z9]),(0,[z0,z1,z2,z89,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z9,z680]),(0,[z1,z52,z2,z3,z4,z333,z9]),(0,[z1,z169,z2,z3,z12,z5,z9]),(0,[z1,z93,z2,z3,z4,z44,z9]),(0,[z143,z1,z2,z3,z4,z33,z9])],[(0,[z21,z1,z2,z3,z596,z5,z9]),(1,[z1,z2,z3,z238,z5,z9]),(1,[z1,z2,z3,z82,z5,z9]),(0,[z1,z704,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z212,z5,z9]),(0,[z1,z2,z3,z12,z12,z5,z9])],[(0,[z1,z2,z3,z4,z5,z705,z9]),(0,[z682,z1,z2,z3,z4,z5,z9]),(0,[z21,z1,z2,z50,z4,z5,z9]),(0,[z21,z1,z239,z2,z3,z4,z9]),(1,[z14,z1,z3,z4,z5,z83]),(0,[z1,z2,z3,z4,z5,z9,z706])],[(0,[z47,z1,z2,z3,z4,z221,z9]),(0,[z135,z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z163,z12,z4,z5,z9]),(0,[z1,z2,z3,z32,z4,z5,z9])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z26,z10,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z707]),(0,[z15,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z708,z33,z9])],[(0,[z47,z26,z3,z12,z5,z9]),(0,[z1,z2,z297,z24,z5,z151]),(0,[z1,z2,z3,z4,z709,z9]),(0,[z710,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z345,z571]),(0,[z1,z2,z3,z4,z711,z9]),(0,[z1,z2,z3,z4,z712,z9]),(0,[z1,z2,z43,z24,z225,z9])],[(0,[z1,z2,z3,z371,z5,z267]),(0,[z1,z2,z3,z713,z5,z9]),(0,[z1,z2,z3,z4,z714,z9]),(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z2,z3,z716,z5,z9])],[(0,[z167,z2,z3,z67,z5,z367]),(0,[z1,z246,z3,z232,z5,z9]),(0,[z1,z2,z3,z717,z5,z9])],[(0,[z1,z2,z555,z4,z345,z9]),(0,[z1,z2,z3,z4,z718,z9]),(0,[z1,z2,z3,z301,z33,z9]),(0,[z1,z2,z356,z4,z44,z9]),(0,[z1,z2,z305,z4,z42,z9])],[(0,[z1,z2,z196,z4,z44,z9]),(0,[z1,z2,z3,z82,z299,z9]),(0,[z1,z2,z3,z24,z44,z9]),(0,[z1,z2,z325,z4,z44,z9]),(0,[z1,z719,z3,z4,z5,z9])],[(0,[z1,z2,z67,z24,z44,z9]),(0,[z1,z2,z3,z51,z333,z9])],[(0,[z1,z35,z2,z3,z24,z9]),(0,[z1,z392,z3,z202,z5,z9])],[(0,[z1,z2,z89,z4,z44,z9]),(0,[z1,z2,z3,z5,z9,z720]),(0,[z1,z2,z3,z4,z721,z9]),(0,[z1,z2,z3,z389,z20,z9])],[(0,[z2,z331,z120,z4,z5,z9]),(0,[z1,z3,z722,z51,z5,z9]),(0,[z1,z2,z3,z5,z9,z723])],[(0,[z1,z2,z3,z329,z12,z9]),(0,[z1,z2,z3,z4,z5,z237]),(0,[z28,z2,z3,z4,z5,z237]),(0,[z126,z2,z8,z4,z5,z9]),(0,[z1,z2,z3,z724,z5,z9]),(0,[z1,z2,z3,z33,z9,z725])],[(0,[z1,z2,z3,z4,z44,z571]),(0,[z1,z98,z3,z289,z5,z9]),(0,[z1,z2,z3,z4,z726,z9]),(0,[z94,z1,z2,z3,z5,z657]),(0,[z1,z2,z3,z24,z400,z9])],[(0,[z1,z35,z3,z4,z179,z9]),(0,[z1,z2,z383,z4,z727,z9]),(0,[z1,z2,z3,z4,z728,z9]),(0,[z1,z2,z24,z5,z44,z9]),(0,[z45,z2,z119,z4,z5,z9])],[(0,[z1,z2,z3,z729,z5,z9]),(0,[z1,z2,z3,z4,z727,z9]),(0,[z1,z2,z3,z730,z5,z9]),(0,[z1,z129,z2,z3,z277,z9]),(0,[z1,z2,z119,z4,z731,z9])],[(0,[z1,z2,z555,z4,z44,z9]),(0,[z1,z2,z3,z732,z5,z9]),(0,[z1,z91,z3,z4,z422,z9])]],
   [[(0,[z1,z2,z3,z733,z5,z9]),(0,[z1,z2,z3,z4,z734,z9]),(0,[z1,z2,z3,z735,z5,z9]),(0,[z1,z2,z461,z24,z5,z9])],[(0,[z1,z2,z3,z4,z736,z9]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z1,z7,z8,z4,z44,z9]),(0,[z1,z129,z2,z436,z5,z9]),(0,[z1,z2,z3,z109,z20,z9])],[(0,[z1,z246,z3,z53,z4,z9])],[(0,[z1,z2,z738,z4,z5,z9]),(0,[z1,z2,z3,z249,z178,z9]),(0,[z1,z2,z3,z4,z739,z171])],[(0,[z1,z2,z374,z4,z44,z9])],[(0,[z40,z26,z3,z4,z5,z9]),(0,[z1,z129,z2,z3,z329,z9]),(0,[z1,z2,z3,z198,z33,z9]),(0,[z28,z2,z3,z24,z5,z29]),(0,[z1,z2,z325,z4,z5,z29]),(0,[z1,z2,z3,z4,z740,z9]),(0,[z1,z2,z3,z4,z741,z9]),(0,[z1,z2,z3,z742,z5,z9])],[(0,[z182,z2,z89,z12,z5,z9]),(0,[z1,z2,z3,z743,z5,z9]),(0,[z1,z2,z3,z4,z744,z9]),(0,[z148,z1,z2,z185,z5,z9]),(0,[z1,z2,z4,z33,z176,z9]),(0,[z94,z1,z2,z325,z5,z66])],[(0,[z1,z2,z3,z4,z221,z9]),(0,[z1,z2,z3,z4,z745,z9]),(0,[z1,z2,z3,z4,z5,z746]),(0,[z167,z2,z3,z67,z5,z172]),(0,[z1,z2,z747,z4,z5,z9]),(0,[z1,z748,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z2,z3,z750,z5,z9]),(0,[z1,z2,z3,z751,z5,z9]),(0,[z28,z2,z3,z4,z5,z210]),(0,[z629,z2,z89,z4,z5,z9]),(0,[z1,z2,z3,z596,z44,z9]),(0,[z1,z2,z752,z4,z5,z9]),(0,[z45,z2,z3,z4,z44,z9])],[(0,[z1,z2,z3,z753,z5,z9]),(0,[z1,z2,z50,z4,z44,z9]),(0,[z38,z1,z173,z4,z5,z62]),(0,[z1,z2,z383,z24,z5,z9]),(0,[z1,z2,z3,z12,z5,z754]),(0,[z1,z2,z3,z145,z109,z9])],[(0,[z1,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z5,z9,z755]),(0,[z502,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z5,z756,z66])],[(0,[z1,z2,z757,z4,z5,z9]),(0,[z21,z2,z3,z4,z55,z9]),(0,[z758,z2,z3,z4,z5,z9])],[(0,[z0,z2,z120,z4,z5,z9]),(0,[z1,z2,z3,z4,z118,z237]),(0,[z630,z1,z173,z4,z5,z9]),(0,[z521,z1,z2,z4,z5,z151]),(0,[z1,z2,z3,z53,z419,z9]),(0,[z394,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z759,z33,z9])],[(0,[z135,z2,z3,z4,z5,z760]),(0,[z2,z3,z4,z5,z9,z760])],[(0,[z761,z26,z3,z4,z5,z9]),(0,[z182,z2,z762,z4,z5,z9]),(0,[z540,z1,z2,z24,z5,z9]),(0,[z1,z255,z3,z24,z5,z9])],[(0,[z1,z91,z35,z3,z4,z9]),(0,[z1,z2,z3,z67,z5,z172]),(0,[z1,z2,z3,z4,z5,z680]),(0,[z1,z2,z665,z12,z5,z9]),(0,[z1,z2,z3,z763,z5,z9]),(0,[z1,z2,z3,z4,z764,z9])]],
   [[(0,[z1,z2,z3,z249,z5,z9]),(0,[z1,z765,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z9,z766]),(0,[z1,z2,z3,z767,z5,z9]),(0,[z1,z169,z383,z4,z5,z9]),(0,[z1,z2,z12,z24,z44,z9]),(0,[z430,z2,z3,z387,z5,z9])],[(0,[z1,z26,z3,z4,z345,z9]),(0,[z1,z2,z3,z4,z768,z9])],[(0,[z1,z2,z3,z4,z5,z769]),(0,[z1,z2,z3,z770,z5,z9]),(0,[z135,z2,z3,z4,z5,z136]),(0,[z1,z2,z24,z44,z259,z9]),(0,[z564,z1,z2,z3,z5,z506]),(0,[z1,z2,z4,z413,z44,z9])],[(0,[z1,z2,z555,z4,z5,z9]),(0,[z1,z771,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z772,z9]),(0,[z1,z2,z3,z232,z5,z9]),(0,[z1,z68,z302,z3,z5,z9]),(0,[z1,z2,z415,z4,z44,z9])],[(0,[z1,z2,z3,z4,z773,z9]),(0,[z568,z2,z3,z4,z5,z136]),(0,[z1,z774,z3,z4,z5,z9]),(0,[z1,z2,z3,z775,z5,z9]),(0,[z1,z2,z610,z24,z5,z9]),(0,[z1,z2,z3,z240,z20,z9]),(0,[z94,z1,z341,z3,z5,z66])],[(0,[z1,z98,z3,z4,z44,z9]),(0,[z1,z2,z3,z249,z33,z9]),(0,[z776,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z777,z5,z9]),(0,[z1,z2,z3,z4,z85,z219]),(0,[z1,z2,z3,z778,z5,z9])],[(0,[z96,z1,z2,z3,z4,z213]),(0,[z1,z2,z3,z5,z9,z725])],[(0,[z26,z3,z10,z4,z5,z9]),(0,[z45,z2,z3,z4,z5,z29]),(0,[z216,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z24,z779,z9]),(0,[z1,z2,z4,z5,z30,z780])],[(0,[z1,z2,z10,z4,z5,z9]),(0,[z1,z2,z3,z4,z781,z9]),(0,[z1,z2,z3,z4,z138,z9]),(1,[z1,z2,z24,z44,z9]),(0,[z1,z2,z387,z5,z9,z151]),(0,[z1,z341,z3,z4,z314,z9])],[(0,[z1,z2,z3,z4,z782,z9]),(0,[z131,z2,z120,z4,z5,z9]),(0,[z2,z3,z762,z4,z5,z9]),(0,[z1,z783,z2,z3,z4,z9])],[(0,[z1,z784,z3,z4,z5,z9]),(0,[z1,z2,z3,z785,z5,z9]),(0,[z1,z2,z3,z5,z9,z786]),(0,[z115,z1,z2,z24,z5,z9]),(0,[z1,z2,z3,z12,z787,z9]),(0,[z1,z2,z3,z788,z5,z9]),(0,[z1,z2,z4,z431,z44,z9])],[(0,[z1,z2,z3,z12,z5,z6]),(0,[z1,z2,z3,z24,z118,z9]),(0,[z1,z113,z3,z311,z5,z9]),(0,[z1,z2,z3,z4,z226,z739])],[(0,[z216,z2,z3,z4,z5,z680]),(0,[z1,z68,z3,z51,z5,z9]),(0,[z1,z2,z3,z4,z789,z9]),(0,[z1,z239,z3,z4,z179,z9])],[(0,[z1,z2,z50,z4,z5,z9]),(0,[z1,z2,z3,z790,z5,z9]),(0,[z126,z2,z3,z4,z5,z62]),(0,[z1,z2,z3,z24,z265,z9]),(0,[z1,z2,z3,z791,z5,z9]),(0,[z1,z2,z3,z4,z5,z792])],[(0,[z1,z2,z3,z4,z793,z9]),(0,[z794,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z154,z5,z267]),(0,[z1,z2,z3,z4,z795,z9]),(0,[z1,z2,z796,z4,z5,z9]),(0,[z1,z2,z4,z33,z205,z9]),(0,[z14,z1,z3,z12,z5,z83])]],
   [[(0,[z1,z2,z797,z4,z5,z9]),(0,[z1,z2,z3,z4,z798,z9]),(0,[z1,z2,z3,z109,z5,z29]),(0,[z799,z2,z3,z4,z5,z9]),(0,[z94,z1,z2,z3,z5,z17])],[(0,[z126,z7,z3,z4,z5,z9]),(0,[z1,z2,z3,z800,z5,z9]),(0,[z1,z68,z3,z51,z33,z9]),(0,[z1,z2,z3,z4,z801,z9]),(0,[z112,z1,z2,z24,z262,z9]),(0,[z1,z129,z2,z3,z730,z9])],[(0,[z535,z1,z173,z4,z5,z9]),(0,[z110,z2,z3,z4,z5,z237]),(0,[z802,z2,z3,z4,z5,z9])],[(0,[z2,z762,z120,z4,z5,z9]),(0,[z1,z2,z3,z146,z44,z9]),(0,[z1,z2,z325,z4,z314,z9])],[(1,[z331,z120,z4,z5,z9]),(0,[z1,z2,z3,z308,z5,z9])],[(0,[z81,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z329,z24,z9]),(0,[z94,z1,z2,z3,z5,z49]),(0,[z1,z129,z2,z356,z3,z9]),(0,[z1,z613,z3,z4,z422,z9]),(0,[z1,z2,z3,z109,z5,z9])],[(0,[z1,z2,z8,z24,z44,z9])],[(0,[z1,z248,z3,z51,z5,z9]),(0,[z1,z648,z3,z4,z179,z9]),(0,[z1,z2,z3,z803,z5,z9]),(0,[z1,z2,z3,z33,z9,z303]),(0,[z1,z2,z43,z4,z5,z780]),(0,[z804,z2,z3,z4,z5,z9]),(0,[z94,z1,z2,z119,z5,z66])],[(0,[z35,z2,z3,z4,z9,z136]),(0,[z1,z2,z3,z4,z805,z9]),(0,[z167,z1,z2,z24,z44,z9]),(0,[z1,z129,z246,z3,z4,z9]),(0,[z1,z2,z3,z4,z806,z9]),(0,[z430,z247,z3,z4,z5,z9])],[(0,[z1,z98,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z330,z9]),(0,[z1,z2,z3,z308,z33,z9]),(0,[z81,z255,z3,z4,z5,z9]),(0,[z594,z1,z2,z3,z4,z171])],[(0,[z1,z2,z3,z807,z5,z9]),(0,[z1,z2,z3,z4,z73,z449]),(0,[z1,z2,z559,z12,z5,z9]),(0,[z1,z2,z3,z67,z288,z9]),(0,[z1,z2,z3,z109,z33,z9]),(0,[z1,z2,z4,z436,z20,z9])],[(0,[z1,z2,z3,z4,z261,z680]),(0,[z633,z1,z2,z24,z5,z9]),(0,[z1,z2,z3,z42,z24,z9]),(0,[z1,z2,z163,z808,z5,z9]),(0,[z1,z2,z325,z32,z5,z9])],[(0,[z1,z2,z3,z4,z39,z9])],[(0,[z0,z331,z120,z4,z5,z9]),(0,[z1,z2,z3,z12,z73,z9]),(0,[z1,z2,z809,z4,z5,z9]),(0,[z1,z2,z383,z4,z5,z194]),(0,[z1,z2,z4,z24,z207,z9]),(0,[z1,z2,z3,z4,z225,z9])],[(0,[z339,z48,z3,z4,z5,z9]),(0,[z1,z302,z3,z67,z5,z9]),(0,[z1,z2,z3,z32,z33,z218])],[(0,[z1,z2,z3,z4,z810,z9]),(0,[z11,z2,z120,z4,z44,z9]),(0,[z1,z2,z50,z4,z99,z9]),(0,[z1,z2,z3,z198,z44,z9]),(0,[z1,z2,z3,z4,z9,z811]),(0,[z1,z2,z3,z4,z5,z812])]],
   [[(0,[z183,z1,z2,z24,z5,z9]),(0,[z21,z2,z3,z4,z136,z171]),(0,[z1,z2,z487,z4,z44,z9]),(0,[z1,z2,z3,z4,z813,z9]),(0,[z1,z392,z3,z77,z5,z9]),(0,[z394,z2,z3,z4,z5,z194])],[(0,[z1,z331,z3,z249,z5,z9]),(0,[z1,z2,z24,z44,z179,z9]),(0,[z1,z2,z134,z24,z5,z9]),(0,[z110,z2,z3,z24,z5,z9])],[(0,[z1,z2,z271,z24,z5,z9]),(0,[z38,z1,z173,z24,z5,z9]),(0,[z1,z2,z3,z4,z814,z9]),(0,[z1,z2,z383,z301,z5,z9]),(0,[z430,z2,z3,z4,z276,z9])],[(0,[z1,z2,z325,z4,z5,z136]),(0,[z485,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z301,z5,z9]),(0,[z1,z2,z134,z4,z815,z9]),(0,[z1,z2,z114,z185,z44,z9]),(0,[z1,z2,z3,z461,z330,z9])],[(0,[z1,z2,z3,z4,z5,z816]),(0,[z47,z761,z3,z4,z5,z9]),(0,[z1,z2,z3,z817,z4,z9]),(0,[z1,z2,z24,z44,z9,z136]),(0,[z148,z1,z2,z24,z5,z9]),(0,[z1,z2,z12,z33,z24,z9]),(0,[z1,z2,z3,z730,z4,z9])],[(0,[z182,z2,z699,z4,z5,z9]),(0,[z1,z2,z120,z4,z73,z9]),(0,[z394,z2,z3,z301,z5,z9]),(0,[z1,z2,z631,z24,z5,z9]),(0,[z45,z2,z3,z4,z314,z9]),(0,[z1,z2,z325,z228,z5,z9])],[(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z819,z3,z4,z5,z9]),(0,[z1,z246,z3,z4,z5,z263]),(0,[z2,z432,z4,z5,z9,z136]),(0,[z1,z2,z432,z596,z5,z9]),(0,[z1,z2,z3,z24,z820,z5]),(0,[z1,z2,z3,z4,z821,z9])],[(0,[z1,z2,z3,z4,z33,z267]),(0,[z1,z2,z3,z146,z5,z9]),(0,[z1,z246,z3,z12,z5,z9]),(0,[z38,z1,z173,z4,z5,z680]),(0,[z822,z2,z3,z4,z5,z9]),(0,[z1,z341,z3,z24,z5,z9]),(0,[z823,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z461,z225,z9]),(0,[z1,z341,z325,z4,z5,z9])],[(0,[z1,z2,z3,z824,z5,z9]),(0,[z1,z2,z3,z99,z24,z9]),(0,[z1,z2,z3,z4,z825,z9]),(0,[z1,z2,z3,z5,z9,z826])],[(0,[z1,z2,z3,z827,z5,z9]),(0,[z1,z2,z3,z4,z828,z9]),(0,[z116,z2,z3,z329,z19,z9]),(0,[z216,z2,z3,z4,z39,z9]),(0,[z1,z2,z3,z829,z5,z9]),(0,[z830,z2,z3,z4,z5,z9]),(0,[z94,z1,z2,z3,z288,z66])],[(0,[z1,z2,z3,z4,z5,z831]),(0,[z1,z2,z152,z12,z5,z9]),(0,[z1,z2,z383,z4,z160,z9])],[(0,[z11,z48,z3,z4,z5,z9]),(0,[z1,z832,z3,z4,z5,z9]),(0,[z0,z2,z120,z4,z44,z9]),(0,[z1,z2,z833,z4,z5,z9]),(0,[z1,z2,z3,z333,z218,z9]),(0,[z1,z2,z3,z4,z160,z9]),(0,[z1,z2,z3,z4,z834,z9])],[(0,[z22,z1,z2,z3,z294,z9])],[(0,[z1,z2,z10,z4,z345,z9]),(0,[z1,z2,z3,z4,z835,z9]),(0,[z1,z2,z3,z836,z5,z9]),(0,[z1,z2,z508,z4,z44,z9]),(0,[z1,z52,z302,z3,z5,z9]),(0,[z394,z2,z3,z4,z160,z9]),(0,[z1,z2,z3,z24,z262,z9]),(0,[z1,z113,z2,z24,z44,z9]),(0,[z1,z2,z4,z5,z9,z780])],[(0,[z1,z2,z3,z4,z837,z9]),(0,[z28,z2,z3,z198,z5,z29]),(0,[z1,z2,z3,z838,z5,z9]),(0,[z1,z2,z3,z4,z44,z680]),(0,[z14,z1,z382,z3,z5,z83]),(0,[z1,z2,z3,z4,z839,z9]),(0,[z59,z1,z2,z3,z4,z171])],[(0,[z1,z2,z3,z249,z44,z9]),(0,[z1,z2,z89,z140,z44,z9]),(0,[z1,z840,z3,z4,z5,z9]),(0,[z1,z2,z8,z4,z5,z680]),(0,[z1,z2,z3,z841,z5,z9]),(0,[z1,z2,z3,z4,z842,z9]),(0,[z1,z2,z24,z44,z9,z83]),(0,[z403,z1,z2,z24,z44,z9]),(0,[z1,z2,z3,z843,z12,z9]),(0,[z1,z2,z3,z844,z5,z9]),(0,[z845,z2,z3,z4,z5,z9])]],
   [[(0,[z11,z48,z3,z4,z33,z9]),(0,[z1,z3,z4,z846,z179,z9])],[(0,[z1,z2,z3,z4,z847,z9]),(0,[z21,z2,z3,z4,z9,z253]),(0,[z135,z2,z3,z4,z44,z136]),(0,[z1,z2,z3,z4,z118,z171]),(0,[z1,z2,z51,z436,z5,z9]),(0,[z112,z1,z2,z33,z24,z9]),(0,[z1,z848,z3,z4,z5,z9])],[(0,[z1,z2,z3,z232,z44,z9]),(0,[z849,z1,z2,z3,z4,z9]),(0,[z1,z2,z3,z850,z5,z9])],[(0,[z2,z89,z120,z4,z44,z9]),(0,[z1,z2,z450,z4,z44,z9]),(0,[z1,z2,z3,z198,z5,z9]),(0,[z1,z2,z399,z24,z5,z9]),(0,[z851,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z852,z5,z9]),(0,[z1,z2,z3,z4,z853,z9]),(0,[z1,z2,z24,z44,z554,z9]),(0,[z1,z2,z3,z5,z9,z854])],[(0,[z1,z2,z3,z4,z5,z855]),(0,[z47,z35,z26,z3,z4,z9]),(1,[z1,z2,z146,z44,z9]),(0,[z1,z2,z3,z596,z5,z237]),(0,[z403,z2,z3,z4,z90,z9]),(0,[z45,z2,z3,z4,z5,z136]),(0,[z1,z129,z2,z3,z145,z9])],[(0,[z1,z856,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z178,z449]),(0,[z126,z2,z3,z24,z5,z9])],[(0,[z1,z2,z10,z4,z44,z9]),(0,[z1,z2,z24,z5,z621,z9])],[(0,[z675,z2,z120,z4,z5,z9]),(0,[z1,z2,z3,z4,z33,z172]),(0,[z1,z2,z3,z5,z9,z857])],[(0,[z1,z2,z3,z12,z178,z9]),(0,[z1,z2,z350,z24,z5,z9]),(0,[z858,z2,z3,z4,z5,z9]),(0,[z45,z341,z3,z4,z5,z9])],[(0,[z1,z2,z3,z759,z5,z9]),(0,[z1,z2,z329,z4,z859,z9]),(0,[z1,z2,z3,z4,z860,z9]),(0,[z1,z2,z24,z5,z194,z151])],[(0,[z126,z2,z3,z4,z5,z680]),(0,[z1,z2,z528,z4,z44,z9]),(0,[z1,z68,z3,z51,z44,z9])],[(0,[z1,z2,z3,z146,z530,z9]),(0,[z1,z2,z3,z791,z44,z9])],[(0,[z1,z3,z861,z4,z5,z9]),(0,[z1,z862,z3,z4,z5,z9])],[(0,[z94,z1,z2,z3,z5,z211]),(0,[z1,z2,z3,z863,z5,z9]),(0,[z1,z2,z3,z109,z5,z136]),(0,[z1,z2,z4,z436,z5,z9]),(0,[z1,z2,z3,z174,z145,z9])],[]],
   [[(0,[z1,z2,z3,z864,z5,z9]),(0,[z1,z2,z432,z4,z27,z9]),(0,[z2,z3,z4,z5,z865,z9]),(0,[z1,z2,z866,z4,z5,z9]),(0,[z1,z23,z2,z3,z145,z9]),(0,[z1,z2,z3,z4,z85,z226])],[(0,[z1,z867,z3,z4,z5,z9]),(0,[z1,z2,z24,z44,z90,z9]),(0,[z38,z216,z173,z4,z5,z9]),(0,[z1,z2,z3,z242,z33,z9])],[(0,[z1,z2,z3,z868,z5,z9]),(0,[z1,z2,z4,z44,z9,z479]),(0,[z1,z247,z3,z4,z33,z9])],[(0,[z1,z2,z869,z4,z5,z9]),(0,[z1,z2,z43,z24,z5,z30]),(0,[z1,z2,z381,z12,z5,z9]),(0,[z1,z2,z3,z308,z44,z9]),(0,[z148,z1,z2,z308,z33,z9])],[(0,[z1,z2,z870,z4,z5,z9]),(0,[z1,z2,z3,z871,z5,z9]),(0,[z38,z1,z173,z4,z39,z9]),(0,[z81,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z109,z44,z9])],[(0,[z1,z2,z3,z4,z5,z263]),(0,[z1,z861,z173,z4,z5,z9]),(0,[z1,z872,z2,z3,z4,z9]),(0,[z1,z2,z24,z5,z9,z213])],[(0,[z48,z761,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z28,z2,z3,z232,z5,z9]),(0,[z1,z2,z24,z5,z136,z151]),(0,[z1,z2,z24,z5,z9,z650])],[(0,[z1,z2,z3,z4,z345,z267]),(0,[z1,z2,z3,z5,z9,z874])],[(0,[z1,z2,z3,z4,z33,z449]),(0,[z1,z429,z3,z4,z33,z9]),(0,[z1,z2,z432,z4,z5,z237]),(0,[z1,z2,z3,z32,z44,z218]),(0,[z1,z2,z3,z730,z53,z9])],[(0,[z1,z2,z3,z875,z5,z9]),(0,[z1,z876,z2,z3,z4,z9]),(0,[z1,z91,z3,z284,z105,z9]),(0,[z1,z2,z3,z24,z877,z9]),(0,[z1,z593,z2,z3,z355,z9]),(0,[z143,z1,z2,z4,z144,z151])],[(0,[z1,z246,z3,z4,z90,z9]),(0,[z1,z2,z3,z4,z33,z263]),(0,[z878,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z12,z33,z9])],[(0,[z182,z331,z3,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z62])],[(1,[z26,z10,z4,z5,z9]),(0,[z1,z2,z4,z19,z859,z9]),(0,[z1,z2,z3,z879,z5,z9]),(0,[z1,z2,z3,z33,z24,z9])],[(0,[z1,z2,z3,z4,z880,z9]),(0,[z1,z2,z3,z4,z288,z9]),(1,[z1,z2,z3,z5,z756])],[(0,[z2,z3,z881,z4,z5,z9]),(0,[z1,z882,z3,z4,z5,z9]),(0,[z1,z2,z32,z24,z44,z9]),(0,[z1,z2,z325,z4,z883,z9])]],
   [[(0,[z268,z1,z2,z24,z5,z9])],[(0,[z1,z2,z3,z4,z44,z267]),(0,[z148,z1,z2,z146,z5,z9]),(0,[z94,z1,z2,z3,z5,z264]),(0,[z1,z2,z114,z24,z44,z9])],[(0,[z1,z2,z4,z884,z5,z9]),(0,[z1,z2,z3,z24,z530,z9]),(0,[z1,z2,z3,z4,z885,z172]),(0,[z1,z2,z432,z4,z643,z9]),(0,[z1,z2,z3,z301,z44,z9]),(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z464,z24,z44,z9]),(0,[z1,z2,z887,z4,z5,z9])],[(0,[z1,z2,z3,z888,z5,z9]),(0,[z1,z214,z2,z3,z12,z9]),(0,[z1,z2,z889,z4,z5,z9]),(0,[z1,z2,z3,z890,z5,z9]),(0,[z1,z2,z3,z4,z9,z393]),(0,[z368,z1,z173,z4,z5,z9]),(0,[z1,z2,z663,z24,z5,z9]),(0,[z148,z1,z2,z24,z44,z9])],[(0,[z21,z246,z3,z4,z90,z9]),(0,[z576,z2,z3,z4,z90,z9]),(0,[z1,z2,z3,z53,z621,z9])],[(0,[z47,z26,z3,z371,z5,z9]),(0,[z1,z2,z3,z891,z5,z9]),(0,[z1,z2,z603,z4,z44,z9]),(0,[z1,z7,z3,z4,z5,z680]),(0,[z1,z2,z3,z4,z892,z9])],[(0,[z1,z2,z3,z893,z5,z9]),(0,[z2,z3,z4,z5,z484,z136]),(0,[z1,z2,z24,z44,z641,z9]),(0,[z1,z2,z3,z24,z314,z9]),(0,[z1,z2,z325,z53,z5,z9])],[(0,[z1,z2,z432,z24,z5,z9]),(0,[z1,z2,z50,z596,z5,z9]),(0,[z1,z2,z3,z4,z894,z9]),(0,[z1,z91,z3,z24,z105,z9]),(0,[z1,z2,z3,z895,z5,z9]),(0,[z1,z302,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z896,z9]),(0,[z1,z2,z4,z897,z5,z9])],[(0,[z1,z2,z560,z4,z44,z9]),(0,[z1,z2,z4,z898,z5,z9]),(0,[z1,z2,z3,z301,z400,z9]),(0,[z2,z3,z4,z44,z9,z256]),(0,[z1,z2,z3,z899,z33,z9])],[(0,[z1,z2,z3,z289,z5,z449]),(0,[z1,z2,z3,z4,z900,z9]),(0,[z2,z3,z4,z118,z9,z136]),(0,[z1,z2,z3,z12,z265,z9]),(0,[z59,z1,z2,z24,z44,z9]),(0,[z1,z129,z2,z24,z44,z9]),(0,[z1,z2,z3,z53,z413,z9])],[(0,[z11,z48,z3,z4,z44,z9])],[(0,[z1,z2,z3,z901,z5,z9]),(0,[z1,z2,z3,z4,z9,z902]),(0,[z15,z2,z3,z212,z5,z9]),(0,[z1,z2,z185,z5,z44,z9]),(0,[z317,z2,z3,z4,z33,z9]),(0,[z1,z2,z305,z4,z33,z9])],[(0,[z1,z2,z3,z903,z5,z9]),(0,[z2,z3,z12,z5,z9,z256]),(0,[z1,z2,z3,z32,z5,z218])],[(0,[z403,z2,z120,z4,z5,z9]),(0,[z1,z2,z163,z461,z5,z9]),(0,[z1,z2,z3,z904,z5,z9])],[(0,[z1,z2,z3,z4,z5,z905])],[(0,[z1,z2,z3,z906,z5,z9]),(0,[z1,z907,z2,z3,z4,z9])]],
   [[(0,[z1,z2,z432,z232,z5,z9]),(0,[z1,z2,z356,z24,z44,z9])],[(0,[z1,z2,z3,z4,z5,z908]),(0,[z1,z2,z120,z4,z265,z9]),(0,[z1,z909,z2,z3,z4,z9]),(0,[z1,z2,z3,z910,z5,z9]),(0,[z1,z2,z3,z4,z299,z9]),(0,[z1,z911,z2,z3,z5,z9])],[(0,[z1,z2,z3,z12,z261,z9]),(0,[z1,z2,z43,z4,z330,z30])],[(0,[z1,z912,z3,z4,z5,z9]),(0,[z28,z1,z2,z24,z44,z9]),(0,[z1,z382,z52,z3,z5,z9]),(0,[z2,z3,z4,z5,z9,z913]),(0,[z143,z1,z2,z4,z5,z780]),(0,[z1,z2,z3,z4,z5,z914])],[(0,[z1,z331,z3,z4,z5,z449]),(0,[z1,z2,z679,z4,z44,z9]),(0,[z1,z2,z89,z24,z44,z9]),(0,[z1,z2,z3,z299,z24,z9]),(0,[z1,z2,z24,z5,z83,z151]),(0,[z1,z2,z3,z4,z915,z9]),(0,[z1,z2,z3,z4,z144,z9]),(0,[z143,z1,z2,z242,z5,z151])],[(0,[z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z3,z4,z916,z9]),(0,[z823,z2,z3,z4,z5,z9])],[(0,[z331,z3,z120,z4,z5,z9]),(0,[z1,z2,z3,z24,z5,z237]),(0,[z1,z2,z3,z917,z5,z9]),(0,[z1,z360,z3,z4,z179,z9]),(0,[z1,z2,z3,z918,z44,z9]),(0,[z1,z2,z43,z4,z225,z30])],[(0,[z1,z331,z3,z12,z5,z9]),(0,[z40,z2,z120,z4,z5,z9]),(0,[z2,z3,z4,z5,z9,z919])],[(0,[z1,z2,z3,z4,z33,z367]),(0,[z1,z2,z3,z4,z920,z9]),(0,[z1,z2,z33,z24,z9,z151]),(0,[z1,z2,z3,z387,z5,z9]),(0,[z1,z2,z684,z4,z44,z9]),(0,[z1,z255,z3,z4,z144,z9])],[(0,[z1,z243,z3,z4,z105,z9]),(0,[z1,z2,z355,z24,z44,z9])],[(0,[z1,z2,z119,z12,z5,z9])],[(0,[z1,z2,z3,z12,z345,z9]),(0,[z1,z2,z3,z4,z9,z921]),(0,[z2,z3,z4,z865,z90,z9]),(0,[z1,z2,z3,z922,z5,z9]),(0,[z1,z2,z3,z242,z44,z9])],[(0,[z1,z405,z3,z51,z5,z9]),(0,[z1,z2,z923,z4,z5,z9]),(0,[z1,z2,z3,z56,z33,z9]),(0,[z1,z2,z3,z4,z924,z9]),(0,[z1,z2,z3,z925,z5,z9]),(0,[z1,z2,z435,z24,z5,z9]),(0,[z1,z2,z163,z12,z138,z9])],[(0,[z1,z2,z3,z926,z5,z9]),(0,[z21,z1,z2,z24,z44,z9]),(0,[z1,z2,z4,z436,z44,z9]),(0,[z1,z2,z4,z426,z44,z9]),(0,[z1,z2,z3,z387,z33,z9])],[(0,[z1,z2,z432,z53,z4,z9]),(0,[z1,z2,z3,z4,z927,z9]),(0,[z143,z1,z2,z12,z5,z151]),(0,[z1,z928,z3,z4,z5,z9])],[(0,[z1,z331,z120,z4,z5,z9]),(0,[z1,z703,z3,z4,z179,z9]),(0,[z143,z1,z2,z4,z276,z151])]],
   [[(0,[z182,z2,z280,z4,z5,z9]),(0,[z1,z2,z3,z929,z5,z9]),(0,[z1,z2,z3,z4,z930,z9]),(0,[z2,z3,z4,z44,z931,z9])],[(0,[z1,z2,z932,z4,z5,z9]),(0,[z1,z2,z933,z4,z5,z9])],[(0,[z1,z2,z3,z4,z44,z449]),(0,[z1,z246,z3,z4,z85,z9]),(0,[z1,z429,z3,z4,z44,z9]),(0,[z1,z2,z3,z934,z5,z9]),(0,[z1,z2,z935,z4,z5,z9]),(0,[z1,z2,z119,z4,z288,z9])],[(0,[z21,z2,z3,z4,z90,z9])],[(0,[z1,z2,z3,z936,z5,z9]),(0,[z1,z2,z3,z4,z44,z263])],[(0,[z1,z2,z3,z4,z937,z9]),(0,[z1,z2,z3,z12,z44,z9]),(0,[z1,z2,z436,z24,z5,z9]),(0,[z1,z2,z325,z24,z5,z9]),(0,[z1,z2,z3,z5,z9,z303]),(0,[z1,z938,z2,z3,z4,z9])],[(0,[z1,z2,z3,z4,z5,z172]),(0,[z28,z2,z3,z4,z5,z172]),(0,[z1,z302,z119,z4,z5,z9])],[(0,[z1,z939,z2,z3,z4,z9]),(0,[z0,z2,z120,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z2,z4,z673,z44,z9])],[(0,[z1,z2,z3,z941,z5,z9])],[(0,[z1,z2,z50,z4,z5,z237]),(0,[z1,z942,z3,z4,z5,z9]),(0,[z1,z2,z3,z294,z179,z9])],[(0,[z0,z2,z762,z4,z5,z9]),(0,[z1,z2,z3,z4,z943,z9]),(0,[z1,z2,z3,z24,z5,z680]),(0,[z1,z2,z3,z918,z5,z9]),(0,[z317,z2,z119,z4,z5,z9])],[(0,[z1,z2,z3,z24,z5,z571]),(0,[z1,z2,z3,z4,z944,z9]),(0,[z1,z2,z3,z945,z5,z9]),(0,[z946,z1,z2,z3,z5,z9]),(0,[z1,z2,z3,z12,z400,z9])],[(0,[z116,z2,z3,z881,z5,z9]),(0,[z1,z644,z3,z51,z5,z9]),(0,[z1,z2,z3,z5,z9,z947]),(0,[z1,z2,z4,z839,z44,z9])],[(0,[z1,z2,z3,z4,z5,z948]),(0,[z1,z214,z2,z3,z24,z9]),(0,[z1,z2,z120,z4,z44,z9]),(0,[z1,z2,z4,z33,z227,z9]),(0,[z135,z2,z3,z24,z5,z136]),(0,[z1,z173,z4,z5,z9,z680])],[(0,[z1,z2,z555,z24,z5,z9]),(0,[z1,z2,z3,z329,z20,z9]),(0,[z1,z2,z3,z4,z949,z9]),(0,[z1,z2,z3,z44,z9,z354]),(0,[z1,z2,z3,z4,z950,z9]),(0,[z1,z2,z3,z4,z951,z9])],[(0,[z167,z2,z3,z67,z33,z9]),(0,[z1,z2,z3,z4,z952,z9]),(0,[z1,z2,z3,z4,z333,z9]),(0,[z1,z2,z953,z4,z5,z9]),(0,[z1,z2,z3,z242,z5,z9]),(0,[z1,z2,z3,z4,z954,z9])]],
   [[(0,[z1,z247,z3,z4,z5,z9]),(0,[z1,z7,z8,z24,z5,z9]),(0,[z1,z2,z3,z955,z5,z9])],[(0,[z47,z26,z3,z154,z5,z9]),(0,[z1,z2,z3,z956,z5,z9]),(0,[z1,z52,z3,z445,z5,z9]),(0,[z1,z302,z3,z4,z44,z9])],[(0,[z675,z1,z173,z4,z5,z9]),(0,[z1,z957,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z958,z9]),(0,[z1,z2,z163,z4,z44,z9]),(0,[z1,z255,z3,z4,z5,z30])],[(0,[z1,z2,z10,z24,z5,z9]),(0,[z1,z2,z3,z53,z25,z9]),(0,[z1,z255,z3,z242,z5,z9])],[(0,[z1,z2,z555,z4,z5,z571]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z28,z2,z3,z12,z5,z29]),(0,[z1,z2,z24,z44,z29,z9]),(0,[z143,z1,z255,z4,z5,z151])],[(0,[z21,z2,z3,z4,z426,z9]),(0,[z1,z91,z117,z3,z4,z9]),(0,[z1,z2,z3,z5,z9,z960]),(0,[z317,z2,z3,z4,z44,z9]),(0,[z1,z2,z305,z4,z44,z9])],[(0,[z1,z429,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z961,z9]),(0,[z1,z2,z3,z4,z5,z449]),(0,[z1,z2,z325,z19,z5,z9]),(0,[z2,z3,z4,z5,z29,z760]),(0,[z1,z2,z3,z389,z621,z9])],[(0,[z1,z2,z3,z962,z5,z9]),(0,[z411,z2,z3,z67,z5,z9]),(0,[z1,z2,z3,z963,z5,z9]),(0,[z1,z2,z3,z964,z5,z9]),(0,[z965,z2,z3,z4,z5,z9]),(0,[z1,z239,z3,z24,z179,z9]),(0,[z1,z2,z934,z24,z5,z9]),(0,[z45,z2,z3,z24,z5,z9]),(0,[z45,z2,z325,z4,z5,z9])],[(0,[z1,z2,z3,z966,z5,z9]),(0,[z1,z2,z3,z4,z5,z967]),(0,[z1,z2,z50,z24,z5,z9]),(0,[z1,z2,z383,z12,z5,z9])],[(0,[z1,z2,z3,z12,z5,z9]),(0,[z1,z2,z10,z4,z5,z571]),(0,[z1,z2,z3,z4,z968,z9]),(0,[z1,z2,z187,z24,z5,z9])],[(0,[z1,z2,z3,z969,z5,z9]),(0,[z14,z1,z3,z212,z5,z83]),(0,[z1,z2,z3,z4,z276,z9]),(0,[z1,z255,z43,z4,z5,z9])],[(0,[z394,z2,z3,z12,z5,z9])],[(0,[z403,z2,z120,z4,z44,z9]),(0,[z1,z2,z3,z4,z288,z29]),(0,[z126,z3,z173,z4,z5,z9]),(0,[z1,z2,z3,z451,z5,z9]),(0,[z1,z970,z2,z3,z24,z9])],[(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z2,z134,z301,z5,z9]),(0,[z1,z2,z24,z44,z9,z151]),(0,[z1,z255,z3,z12,z5,z9]),(0,[z403,z2,z3,z4,z641,z9])],[(0,[z1,z2,z3,z972,z5,z9]),(0,[z1,z695,z3,z4,z583,z9])],[(0,[z1,z2,z3,z4,z973,z9]),(0,[z2,z3,z67,z881,z5,z9]),(0,[z1,z2,z3,z4,z592,z171]),(0,[z94,z317,z2,z3,z5,z66])]],
   [[(0,[z1,z2,z10,z974,z5,z9]),(0,[z1,z302,z3,z4,z5,z29]),(0,[z81,z2,z3,z24,z5,z9]),(0,[z143,z1,z2,z387,z5,z151])],[(0,[z1,z2,z89,z146,z44,z9]),(0,[z1,z2,z50,z232,z5,z9]),(0,[z1,z169,z3,z4,z5,z539]),(0,[z1,z3,z77,z722,z5,z9])],[(0,[z1,z2,z975,z4,z5,z9]),(0,[z2,z3,z120,z4,z5,z449]),(0,[z1,z2,z3,z4,z44,z367]),(0,[z1,z653,z3,z4,z105,z9]),(0,[z1,z2,z3,z294,z105,z9])],[(0,[z1,z2,z516,z24,z5,z9]),(0,[z1,z2,z3,z4,z976,z9])],[(0,[z28,z2,z3,z4,z5,z566]),(0,[z1,z98,z3,z24,z5,z9]),(0,[z21,z1,z2,z3,z109,z9]),(0,[z1,z2,z24,z44,z635,z9]),(0,[z1,z2,z174,z12,z5,z9]),(0,[z1,z2,z4,z33,z436,z9])],[(0,[z1,z2,z3,z4,z73,z6]),(0,[z1,z2,z4,z977,z44,z9]),(0,[z1,z2,z3,z4,z978,z9]),(0,[z1,z302,z3,z4,z5,z9]),(0,[z1,z2,z134,z4,z160,z9])],[(0,[z0,z98,z120,z4,z5,z9]),(0,[z1,z2,z3,z979,z5,z9]),(0,[z1,z2,z12,z128,z5,z9]),(0,[z216,z2,z3,z12,z5,z9]),(0,[z430,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z899,z5,z9]),(0,[z1,z2,z3,z145,z9,z515])],[(0,[z1,z2,z638,z24,z5,z9]),(0,[z1,z2,z3,z387,z44,z9])],[(0,[z2,z26,z120,z4,z44,z9]),(0,[z1,z2,z3,z980,z5,z9]),(0,[z45,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z53,z232,z9]),(0,[z1,z2,z3,z4,z981,z9]),(0,[z15,z2,z3,z4,z33,z9]),(0,[z1,z2,z53,z24,z44,z9])],[(0,[z47,z26,z3,z4,z33,z9]),(0,[z1,z982,z3,z4,z5,z9]),(0,[z317,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z983,z5,z9]),(0,[z1,z2,z51,z24,z44,z9]),(0,[z1,z2,z305,z4,z5,z9]),(0,[z1,z2,z3,z984,z24,z9])],[(0,[z1,z2,z3,z12,z118,z9]),(0,[z1,z2,z24,z205,z5,z9]),(0,[z1,z2,z3,z12,z5,z985])],[(0,[z1,z2,z3,z12,z99,z9]),(0,[z1,z2,z3,z986,z5,z9]),(0,[z126,z2,z3,z4,z39,z9]),(0,[z1,z2,z3,z24,z813,z9]),(0,[z1,z2,z435,z24,z44,z9])],[(0,[z26,z120,z173,z4,z5,z9]),(0,[z1,z987,z3,z4,z5,z9]),(0,[z137,z2,z89,z4,z5,z9]),(0,[z1,z2,z24,z44,z9,z171])],[(0,[z1,z2,z3,z988,z5,z9]),(0,[z1,z2,z3,z4,z5,z989])],[(0,[z1,z2,z555,z807,z5,z9]),(0,[z1,z2,z3,z990,z5,z9]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z94,z1,z302,z3,z5,z66])],[(0,[z1,z2,z3,z4,z992,z9]),(0,[z1,z2,z3,z4,z993,z9]),(0,[z1,z2,z3,z451,z265,z9]),(0,[z1,z2,z3,z4,z994,z9]),(0,[z1,z2,z3,z4,z207,z9]),(0,[z1,z2,z24,z5,z225,z9]),(0,[z1,z2,z4,z79,z44,z9]),(0,[z1,z2,z3,z995,z5,z9])]],
   [[(0,[z1,z2,z209,z24,z5,z9]),(0,[z1,z2,z3,z996,z5,z9]),(0,[z1,z2,z3,z997,z5,z9])],[(0,[z1,z2,z3,z998,z5,z9]),(0,[z1,z2,z24,z5,z227,z9]),(0,[z512,z2,z3,z4,z5,z29]),(0,[z1,z2,z383,z906,z5,z9]),(0,[z1,z2,z335,z4,z44,z9]),(0,[z1,z2,z325,z4,z821,z9])],[(0,[z1,z2,z3,z12,z314,z9])],[(0,[z1,z2,z3,z4,z9,z999]),(0,[z1,z2,z3,z1000,z5,z9]),(0,[z1,z2,z4,z1001,z5,z9]),(0,[z1,z2,z119,z4,z954,z9])],[(0,[z2,z761,z3,z4,z5,z9]),(0,[z1,z2,z560,z24,z5,z9]),(0,[z1,z2,z436,z24,z44,z9]),(0,[z1,z2,z3,z1002,z5,z9]),(0,[z1,z2,z3,z4,z190,z259])],[(0,[z1,z2,z26,z24,z44,z9]),(0,[z1,z2,z3,z4,z44,z172]),(0,[z1,z246,z3,z4,z9,z171]),(0,[z1,z2,z4,z44,z9,z687])],[(0,[z1,z2,z3,z4,z5,z367]),(0,[z1,z2,z3,z4,z1003,z9]),(0,[z1,z68,z3,z722,z5,z9]),(0,[z1,z2,z3,z24,z160,z9]),(0,[z1004,z2,z3,z12,z5,z9])],[(0,[z1,z1005,z2,z3,z5,z9]),(0,[z1,z2,z3,z1006,z5,z9]),(0,[z1,z2,z3,z1007,z5,z9]),(0,[z1,z2,z3,z1008,z5,z9]),(0,[z1009,z1,z2,z3,z24,z5]),(0,[z94,z1,z2,z3,z5,z506])],[(0,[z1,z26,z10,z4,z5,z9]),(0,[z1,z1010,z2,z3,z5,z9]),(0,[z312,z48,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1011,z9]),(0,[z2,z3,z4,z44,z9,z1012])],[(0,[z1013,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z1014,z9]),(0,[z1,z2,z1015,z4,z5,z9]),(0,[z1,z2,z3,z56,z5,z9]),(0,[z110,z2,z3,z4,z85,z226]),(0,[z1,z2,z3,z1016,z5,z9])],[(0,[z1,z35,z2,z3,z4,z9]),(0,[z28,z35,z2,z3,z4,z9]),(0,[z1,z52,z3,z77,z333,z9]),(0,[z1,z1017,z3,z4,z5,z9])],[(0,[z1,z2,z1018,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z754]),(0,[z1,z2,z3,z1019,z5,z9])],[(0,[z477,z2,z3,z537,z5,z9]),(0,[z1,z2,z277,z4,z33,z9])],[(0,[z1,z48,z3,z4,z345,z9]),(0,[z182,z2,z89,z4,z33,z9]),(0,[z1,z2,z3,z4,z1020,z9]),(0,[z1,z302,z3,z4,z314,z9])],[(0,[z1,z2,z3,z4,z1021,z9]),(0,[z1,z7,z2,z24,z44,z9]),(0,[z1022,z2,z3,z4,z5,z9]),(0,[z1,z2,z24,z24,z44,z9]),(0,[z1,z2,z3,z12,z1023,z9]),(0,[z1,z247,z3,z4,z44,z9]),(0,[z1,z255,z3,z387,z5,z9]),(0,[z2,z3,z4,z5,z9,z1024])]],
   [[(0,[z116,z2,z3,z19,z5,z9]),(0,[z391,z2,z3,z4,z27,z9]),(0,[z1,z2,z134,z12,z5,z9]),(0,[z110,z2,z3,z12,z5,z9]),(0,[z1,z2,z356,z4,z436,z9])],[(0,[z1,z2,z3,z4,z178,z6]),(0,[z1,z2,z3,z4,z39,z62]),(0,[z38,z1,z173,z12,z5,z9]),(0,[z133,z1,z2,z3,z4,z171]),(0,[z1,z2,z3,z5,z218,z756])],[(0,[z1,z2,z1025,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z1,z2,z3,z232,z5,z237]),(0,[z1,z2,z3,z4,z1027,z9]),(0,[z1,z2,z3,z4,z1028,z9]),(0,[z317,z2,z3,z4,z314,z9])],[(0,[z22,z1,z2,z24,z44,z9]),(0,[z1,z1029,z2,z3,z5,z9])],[(0,[z1,z2,z3,z1030,z5,z9]),(1,[z2,z762,z4,z5,z9]),(0,[z1,z269,z3,z4,z105,z9]),(0,[z1,z2,z684,z24,z5,z9]),(0,[z1,z2,z43,z4,z5,z476])],[(0,[z1,z2,z3,z24,z221,z9]),(0,[z116,z2,z3,z19,z33,z9]),(0,[z1,z2,z3,z1031,z5,z9]),(0,[z1,z1032,z3,z4,z5,z9]),(0,[z143,z430,z2,z4,z5,z151])],[(0,[z1,z1033,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z1034,z9]),(0,[z1,z2,z3,z1035,z5,z9]),(0,[z1,z341,z3,z12,z5,z9]),(0,[z1,z302,z3,z32,z5,z9]),(0,[z1,z2,z3,z4,z9,z739])],[(0,[z216,z2,z3,z56,z5,z9]),(0,[z1,z2,z3,z4,z85,z344]),(0,[z1,z2,z308,z24,z5,z9]),(0,[z1,z2,z4,z44,z9,z706])],[(0,[z1,z2,z3,z4,z5,z1036]),(0,[z1,z52,z3,z464,z5,z9]),(0,[z1,z2,z3,z1037,z5,z9]),(0,[z148,z1,z2,z12,z33,z9])],[(0,[z1,z1038,z3,z4,z5,z9])],[(0,[z1,z2,z3,z371,z5,z9]),(0,[z561,z1,z2,z4,z33,z9]),(0,[z291,z1,z3,z4,z5,z83]),(0,[z1,z2,z3,z4,z288,z136]),(0,[z1,z2,z3,z4,z1039,z9]),(0,[z148,z1,z2,z33,z24,z9]),(1,[z1,z2,z24,z225,z9]),(0,[z1,z2,z3,z195,z44,z9])],[(0,[z1,z2,z3,z1040,z5,z9]),(0,[z1,z2,z3,z4,z221,z571]),(0,[z1,z2,z3,z4,z1041,z9]),(0,[z1,z2,z3,z451,z44,z9]),(0,[z1,z113,z3,z51,z5,z9]),(0,[z1,z2,z4,z185,z44,z9])],[(0,[z1,z2,z3,z4,z1042,z9]),(0,[z1,z2,z508,z24,z5,z9]),(0,[z1,z2,z3,z12,z262,z9]),(0,[z1,z2,z327,z4,z33,z9])],[(0,[z1,z2,z3,z4,z1043,z9]),(0,[z167,z2,z3,z67,z5,z9]),(0,[z21,z1,z2,z4,z436,z9]),(0,[z135,z1,z2,z24,z44,z9]),(0,[z123,z1,z2,z24,z44,z9])],[(0,[z1,z2,z555,z4,z221,z9]),(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z24,z44,z9]),(0,[z1,z2,z3,z4,z859,z9]),(0,[z1,z302,z3,z4,z5,z136]),(0,[z1,z2,z861,z4,z5,z9]),(0,[z1044,z2,z3,z12,z5,z9]),(0,[z1,z341,z3,z4,z288,z9])],[(0,[z1,z2,z3,z371,z33,z9]),(0,[z1,z2,z3,z289,z178,z9]),(0,[z1,z2,z50,z729,z5,z9])]],
   [[(0,[z0,z2,z120,z249,z5,z9]),(0,[z28,z2,z120,z4,z44,z9]),(0,[z1045,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1046,z9]),(0,[z1,z2,z3,z4,z1047,z9]),(0,[z1,z2,z3,z5,z218,z106])],[(0,[z1,z2,z3,z238,z5,z9]),(0,[z1,z2,z3,z82,z5,z9]),(0,[z1,z2,z3,z24,z5,z873])],[(0,[z2,z3,z329,z4,z9,z136]),(0,[z15,z2,z3,z4,z44,z9]),(0,[z14,z1,z3,z4,z5,z83])],[(0,[z1,z2,z10,z4,z221,z9]),(0,[z1,z2,z3,z4,z33,z6]),(0,[z1,z2,z897,z5,z9,z171])],[(0,[z1,z2,z3,z1048,z5,z9]),(0,[z1,z2,z3,z4,z1049,z9]),(1,[z126,z173,z4,z5,z9]),(0,[z1,z2,z3,z4,z1050,z9]),(0,[z1,z2,z3,z4,z85,z295]),(0,[z1,z2,z1051,z4,z5,z9])],[(0,[z2,z89,z762,z4,z5,z9]),(0,[z126,z2,z3,z12,z5,z9])],[(0,[z1,z2,z3,z4,z1052,z9]),(0,[z1,z2,z3,z1053,z5,z9]),(0,[z1,z2,z432,z4,z90,z9]),(0,[z1,z2,z3,z56,z261,z9]),(0,[z1,z2,z3,z238,z33,z9]),(0,[z1054,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z82,z33,z9]),(0,[z1,z2,z3,z212,z33,z9]),(0,[z1,z2,z3,z24,z138,z9]),(0,[z317,z341,z3,z4,z5,z9])],[(0,[z1,z2,z3,z5,z9,z1055]),(0,[z21,z2,z3,z4,z493,z9]),(0,[z14,z1,z3,z4,z33,z83]),(0,[z1,z2,z3,z4,z5,z756])],[(0,[z1,z2,z3,z4,z5,z1056]),(0,[z1,z2,z474,z24,z5,z9]),(0,[z15,z2,z3,z4,z400,z9]),(0,[z1,z2,z3,z1057,z5,z9]),(0,[z59,z1,z2,z3,z303,z171])],[(0,[z1,z1058,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1059,z9])],[(0,[z47,z214,z26,z3,z4,z9]),(0,[z1,z2,z3,z1060,z5,z9]),(0,[z1,z2,z3,z4,z1061,z9]),(0,[z2,z3,z271,z4,z5,z136]),(0,[z126,z2,z173,z4,z5,z9]),(0,[z1,z2,z24,z44,z9,z66])],[(0,[z11,z761,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z42,z9]),(0,[z1,z1062,z3,z4,z5,z9])],[(0,[z1,z2,z762,z4,z5,z9]),(0,[z1,z1063,z2,z3,z4,z9]),(0,[z2,z3,z232,z5,z9,z136]),(0,[z1,z2,z240,z24,z44,z9])],[(0,[z1,z2,z3,z4,z1064,z9]),(0,[z1,z2,z3,z4,z865,z9]),(1,[z1,z255,z4,z5,z151]),(0,[z1,z2,z3,z4,z5,z780])],[(1,[z761,z3,z4,z5,z9]),(0,[z216,z2,z3,z238,z5,z9]),(0,[z148,z1,z2,z1002,z5,z9]),(0,[z1,z2,z3,z195,z5,z9]),(0,[z1,z2,z3,z995,z44,z9])],[(0,[z1,z2,z3,z4,z9,z1065]),(0,[z1,z2,z3,z4,z1066,z9])]],
   [[(0,[z1,z2,z555,z4,z782,z9]),(0,[z1,z429,z3,z596,z5,z9]),(0,[z21,z2,z432,z4,z90,z9]),(0,[z456,z2,z3,z4,z5,z136]),(0,[z1,z3,z173,z4,z5,z680]),(0,[z1,z52,z3,z722,z5,z9]),(0,[z1,z2,z3,z240,z25,z9])],[(0,[z1,z2,z3,z1067,z5,z9]),(0,[z1,z2,z3,z4,z300,z9]),(0,[z1,z2,z3,z4,z1068,z9]),(0,[z1,z255,z3,z4,z276,z9]),(0,[z1,z2,z305,z53,z20,z9])],[(0,[z1,z2,z3,z4,z984,z9]),(0,[z1,z2,z3,z596,z5,z263]),(0,[z38,z1,z173,z56,z5,z9]),(0,[z1,z2,z43,z12,z5,z30])],[(0,[z1,z2,z4,z146,z44,z9]),(0,[z1,z2,z3,z329,z218,z9]),(0,[z1,z2,z3,z5,z9,z1069]),(0,[z1,z2,z1070,z4,z5,z9]),(0,[z1071,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z289,z5,z6]),(0,[z430,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z82,z265,z9])],[(0,[z1072,z1,z2,z4,z5,z9]),(0,[z2,z120,z4,z313,z44,z9]),(0,[z1,z1073,z3,z4,z5,z9]),(0,[z2,z74,z3,z4,z5,z136]),(0,[z15,z2,z383,z4,z5,z9])],[(0,[z15,z2,z3,z4,z5,z9]),(0,[z1,z2,z1074,z4,z5,z9]),(0,[z1,z2,z3,z4,z1075,z9])],[(0,[z47,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1076,z9]),(0,[z21,z2,z3,z4,z865,z9]),(0,[z1,z2,z3,z4,z1077,z9]),(0,[z1,z2,z145,z24,z44,z9]),(0,[z1,z2,z3,z4,z44,z1078]),(0,[z1,z2,z3,z1079,z5,z9])],[(0,[z1,z2,z4,z5,z9,z1080]),(0,[z182,z2,z89,z4,z44,z9]),(0,[z1,z2,z3,z329,z4,z9]),(0,[z28,z2,z3,z329,z4,z9]),(0,[z1,z2,z478,z4,z44,z9]),(0,[z1,z2,z3,z1081,z5,z9]),(0,[z430,z255,z3,z4,z5,z9])],[(0,[z291,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z1082,z5,z9]),(0,[z1,z2,z402,z12,z5,z9]),(0,[z1,z2,z3,z56,z44,z9]),(0,[z1,z2,z3,z4,z1083,z9]),(0,[z1,z192,z3,z615,z5,z9]),(0,[z1,z2,z3,z1084,z5,z9]),(0,[z1,z2,z60,z4,z44,z9]),(0,[z1,z2,z3,z1085,z5,z9]),(0,[z94,z1,z2,z3,z33,z66]),(0,[z1,z2,z3,z1086,z5,z9])],[(0,[z1,z2,z3,z4,z1087,z9]),(0,[z1,z2,z146,z5,z44,z9]),(0,[z1,z2,z3,z24,z39,z9]),(0,[z1,z2,z134,z929,z5,z9]),(0,[z1,z2,z3,z1088,z5,z9]),(0,[z1,z2,z3,z1089,z5,z9]),(0,[z1,z2,z3,z4,z1090,z9])],[(0,[z1,z2,z3,z4,z5,z1091]),(0,[z513,z2,z3,z4,z5,z136]),(0,[z2,z3,z881,z19,z5,z9]),(0,[z1,z2,z3,z12,z5,z62]),(0,[z1,z2,z3,z1092,z5,z9]),(0,[z1,z2,z1093,z4,z5,z9]),(0,[z1,z169,z2,z24,z44,z9]),(0,[z1,z2,z24,z5,z409,z9]),(0,[z1,z2,z3,z24,z225,z9]),(0,[z1,z2,z12,z808,z5,z9]),(0,[z1,z2,z3,z4,z1094,z9])],[(0,[z1,z2,z3,z1095,z5,z9]),(0,[z1,z2,z3,z4,z1096,z9]),(0,[z1,z126,z173,z4,z5,z9]),(0,[z1,z2,z3,z4,z1097,z9]),(0,[z1,z2,z4,z1098,z44,z9]),(0,[z1,z1099,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1100,z9])],[(0,[z1,z2,z3,z1101,z5,z9]),(0,[z1,z98,z3,z249,z5,z9]),(0,[z1,z2,z3,z4,z1102,z9]),(0,[z1,z322,z2,z3,z12,z9]),(0,[z1,z2,z4,z1103,z5,z9]),(0,[z1,z2,z3,z238,z261,z9]),(0,[z1,z2,z79,z24,z44,z9])],[(0,[z1,z2,z3,z1104,z4,z9]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z2,z3,z1106,z5,z9]),(0,[z59,z1,z2,z3,z4,z408])],[(0,[z1,z2,z3,z371,z345,z9]),(0,[z1,z331,z3,z4,z5,z6]),(0,[z116,z2,z3,z19,z44,z9]),(0,[z1,z2,z1107,z4,z5,z9]),(0,[z1,z246,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z39,z680]),(0,[z1,z2,z3,z1108,z5,z9]),(0,[z1,z2,z3,z24,z144,z9]),(0,[z1,z2,z24,z5,z9,z420]),(0,[z1,z2,z3,z435,z20,z9])]],
   [[(0,[z1,z2,z3,z24,z5,z267]),(1,[z1,z2,z4,z859,z9]),(0,[z1,z91,z2,z432,z4,z9]),(0,[z71,z2,z3,z79,z5,z9]),(0,[z1,z2,z24,z422,z44,z9]),(0,[z1,z2,z114,z12,z44,z9]),(0,[z1,z2,z12,z33,z44,z9]),(0,[z1,z1109,z3,z4,z5,z9])],[(0,[z1,z2,z3,z12,z530,z9]),(0,[z1,z2,z665,z4,z44,z9])],[(0,[z1,z2,z3,z4,z1110,z9]),(0,[z1,z1111,z2,z3,z5,z9]),(0,[z94,z1,z2,z436,z5,z9]),(0,[z1,z2,z3,z1112,z5,z9])],[(0,[z1,z429,z432,z4,z5,z9]),(0,[z1,z2,z438,z4,z33,z9]),(1,[z1,z2,z808,z5,z9]),(0,[z1,z2,z43,z330,z24,z9]),(0,[z1,z2,z3,z1113,z5,z9])],[(0,[z670,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z1114,z5,z9])],[(0,[z1,z2,z432,z4,z5,z263])],[(0,[z1,z2,z3,z154,z5,z9]),(0,[z1,z2,z3,z289,z73,z9]),(0,[z1,z2,z3,z4,z5,z1115]),(0,[z1,z2,z432,z12,z5,z9]),(0,[z126,z2,z3,z56,z5,z9]),(0,[z1,z2,z12,z184,z5,z9]),(0,[z1,z91,z3,z12,z105,z9])],[(0,[z1,z1116,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1117,z9]),(0,[z2,z3,z4,z33,z9,z256])],[(0,[z112,z1,z2,z808,z5,z9]),(0,[z1,z2,z3,z1113,z33,z9])],[(0,[z1,z2,z555,z4,z5,z267]),(0,[z1,z2,z3,z371,z44,z9]),(0,[z11,z48,z3,z24,z5,z9]),(0,[z1,z1118,z3,z4,z5,z9]),(0,[z38,z1,z173,z238,z5,z9]),(0,[z1,z2,z3,z1119,z5,z9]),(0,[z1,z91,z3,z4,z846,z9]),(0,[z1,z2,z4,z24,z44,z9])],[],[(0,[z1,z2,z3,z154,z33,z9]),(0,[z1,z1120,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z1121,z9]),(0,[z1,z2,z3,z1122,z5,z9]),(0,[z1,z2,z3,z1123,z5,z9]),(0,[z1,z2,z1002,z24,z5,z9]),(0,[z1,z2,z3,z4,z5,z1078])],[(0,[z1,z2,z3,z4,z178,z9]),(0,[z182,z2,z89,z4,z5,z9]),(0,[z167,z2,z3,z67,z44,z9]),(0,[z1,z2,z3,z4,z1124,z9]),(0,[z1,z2,z3,z4,z1125,z9]),(0,[z38,z1,z2,z24,z44,z9]),(0,[z1,z2,z24,z311,z44,z9]),(0,[z1,z2,z24,z44,z9,z189]),(0,[z1,z2,z163,z12,z42,z9])],[(0,[z1,z2,z3,z4,z44,z6]),(0,[z1,z2,z3,z53,z288,z9])],[(0,[z1,z2,z10,z4,z5,z267]),(0,[z1,z2,z432,z4,z85,z9]),(0,[z21,z2,z3,z24,z90,z9]),(0,[z1,z239,z3,z4,z396,z9]),(0,[z1,z2,z3,z1126,z5,z9])],[(0,[z1045,z2,z3,z4,z44,z9]),(1,[z1,z2,z4,z5,z780]),(0,[z1,z2,z3,z4,z9,z1127])]],
   [[(0,[z1,z2,z3,z4,z1128,z9]),(0,[z1,z2,z3,z238,z44,z9]),(0,[z1,z2,z3,z82,z44,z9]),(0,[z1,z2,z3,z212,z44,z9]),(0,[z1,z2,z24,z44,z20,z9]),(0,[z1,z2,z142,z4,z44,z9]),(0,[z1,z2,z4,z1098,z5,z9])],[(0,[z1,z2,z3,z24,z5,z172]),(0,[z1,z2,z285,z4,z44,z9]),(0,[z1129,z2,z3,z4,z5,z9]),(0,[z14,z1,z3,z4,z44,z83]),(0,[z682,z1,z2,z24,z44,z9]),(0,[z1130,z2,z3,z4,z5,z9]),(0,[z1,z302,z3,z53,z5,z9])],[(0,[z246,z3,z4,z5,z9,z136]),(0,[z1,z429,z3,z4,z5,z237]),(0,[z57,z1,z3,z4,z5,z83]),(0,[z1,z2,z12,z431,z5,z9]),(0,[z1,z2,z3,z1131,z4,z9])],[(0,[z1,z2,z89,z12,z44,z9]),(0,[z1,z2,z3,z4,z1132,z9])],[(0,[z1133,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1134,z9]),(0,[z1,z2,z3,z12,z1135,z9]),(0,[z1,z1136,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1137,z9])],[(0,[z1,z2,z3,z12,z5,z237]),(0,[z1,z2,z3,z1138,z5,z9]),(0,[z14,z394,z3,z4,z5,z83]),(0,[z148,z1,z2,z4,z42,z9])],[(0,[z1,z1139,z2,z3,z4,z9]),(0,[z1,z2,z1140,z4,z5,z9]),(0,[z116,z2,z3,z537,z5,z9]),(0,[z1141,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z212,z400,z9]),(0,[z486,z1,z2,z24,z5,z9])],[(0,[z14,z1,z3,z4,z400,z83]),(0,[z2,z3,z4,z5,z9,z1142])],[(0,[z1,z577,z3,z77,z5,z9]),(0,[z1,z2,z385,z4,z44,z9]),(0,[z1,z2,z4,z386,z44,z9]),(0,[z70,z1,z2,z3,z4,z408])],[(0,[z1,z236,z2,z24,z44,z9])],[(0,[z1,z2,z3,z24,z333,z9]),(0,[z1,z2,z1143,z4,z5,z9]),(0,[z1,z2,z3,z53,z567,z9])],[(0,[z1,z2,z3,z4,z1144,z9]),(0,[z1,z247,z3,z24,z5,z9]),(0,[z110,z2,z3,z4,z85,z9])],[(0,[z47,z26,z3,z4,z345,z9]),(0,[z1,z2,z559,z4,z44,z9]),(0,[z1,z2,z3,z56,z5,z62])],[(0,[z1,z2,z3,z4,z5,z1145]),(0,[z1,z2,z3,z4,z1146,z9]),(0,[z1,z2,z3,z4,z85,z237]),(0,[z1147,z2,z3,z4,z5,z9]),(0,[z1,z52,z3,z77,z300,z9]),(0,[z1,z2,z163,z24,z44,z9])],[(0,[z1,z1148,z2,z3,z4,z9]),(0,[z182,z2,z89,z4,z99,z9]),(0,[z1,z2,z3,z1149,z5,z9]),(0,[z112,z1,z2,z24,z207,z9]),(0,[z1,z2,z3,z24,z85,z226])],[(0,[z167,z2,z3,z125,z5,z9])]],
   [[(0,[z1,z1150,z2,z3,z4,z9]),(0,[z21,z2,z3,z596,z90,z9]),(1,[z1,z173,z4,z5,z680]),(0,[z1,z2,z3,z4,z787,z9])],[(0,[z1,z2,z3,z1151,z5,z9]),(0,[z1,z2,z3,z24,z5,z449]),(0,[z1,z429,z3,z24,z5,z9]),(0,[z21,z2,z50,z4,z90,z9]),(0,[z1,z2,z43,z24,z5,z9]),(0,[z1,z748,z3,z12,z5,z9]),(0,[z1,z129,z2,z3,z355,z9]),(0,[z1,z2,z3,z4,z1152,z9])],[(0,[z1,z2,z3,z4,z1153,z9]),(0,[z1,z2,z3,z1154,z5,z9]),(0,[z1,z2,z3,z19,z5,z172])],[(0,[z0,z2,z120,z4,z5,z449]),(0,[z1,z2,z3,z1155,z5,z9]),(0,[z45,z2,z3,z4,z5,z172]),(0,[z1,z2,z3,z24,z5,z263]),(0,[z2,z3,z4,z5,z237,z136]),(0,[z22,z1,z2,z4,z436,z9]),(0,[z1,z2,z383,z212,z5,z9]),(0,[z430,z2,z3,z4,z44,z9])],[(0,[z1,z2,z3,z4,z1156,z9]),(0,[z1,z2,z3,z4,z5,z1157]),(0,[z1,z2,z3,z212,z5,z9]),(0,[z14,z1,z383,z4,z5,z83]),(0,[z1,z2,z3,z808,z5,z9]),(0,[z1,z2,z24,z5,z9,z506]),(0,[z1,z2,z325,z12,z5,z9])],[(0,[z1,z2,z3,z1158,z5,z9]),(0,[z1,z2,z1159,z4,z5,z9]),(0,[z1,z2,z3,z4,z1160,z9]),(0,[z1,z3,z4,z5,z886,z83]),(0,[z1,z2,z3,z24,z276,z9])],[(0,[z47,z26,z3,z4,z44,z9]),(0,[z0,z2,z120,z12,z5,z9]),(0,[z1,z1161,z3,z4,z5,z9]),(0,[z394,z2,z3,z212,z5,z9])],[(0,[z1,z2,z3,z4,z1162,z9]),(0,[z1,z2,z3,z4,z5,z1163]),(0,[z1,z322,z2,z3,z24,z9]),(0,[z96,z1,z2,z3,z4,z171]),(0,[z1,z2,z3,z1164,z5,z9])],[(0,[z116,z1,z2,z24,z44,z9]),(0,[z1,z1165,z3,z4,z5,z9]),(0,[z1,z2,z3,z1166,z5,z9]),(0,[z878,z2,z3,z24,z5,z9]),(0,[z1,z2,z3,z1085,z44,z9]),(0,[z1,z2,z3,z4,z1167,z9]),(0,[z1,z2,z325,z145,z5,z9])],[(0,[z1,z1168,z3,z4,z5,z9]),(0,[z1,z2,z1169,z329,z4,z9]),(0,[z1,z2,z3,z1170,z5,z9]),(0,[z1,z2,z3,z12,z5,z680]),(0,[z1,z2,z3,z4,z1171,z9])],[(0,[z1,z2,z3,z1172,z5,z9]),(0,[z1,z2,z3,z12,z5,z571])],[(0,[z1,z2,z3,z154,z345,z9]),(0,[z1,z2,z3,z4,z1173,z9]),(0,[z36,z1,z2,z4,z5,z151])],[(0,[z1,z2,z3,z4,z5,z1174]),(0,[z1,z970,z2,z3,z4,z9]),(0,[z1,z91,z246,z3,z4,z9]),(0,[z1,z2,z3,z232,z5,z263]),(0,[z135,z2,z3,z12,z5,z136]),(0,[z1,z2,z3,z125,z33,z9]),(0,[z1,z2,z152,z4,z44,z9]),(0,[z1,z2,z3,z24,z288,z9]),(0,[z1,z2,z4,z5,z780,z151]),(0,[z1,z2,z325,z4,z288,z9])],[(0,[z1,z2,z555,z12,z5,z9]),(0,[z1,z331,z3,z4,z178,z9]),(0,[z1,z2,z3,z1175,z5,z9]),(0,[z1,z2,z3,z33,z9,z354])],[(0,[z1,z2,z3,z4,z1176,z9]),(0,[z1,z1168,z3,z4,z33,z9])],[(0,[z1,z2,z3,z289,z5,z9]),(0,[z1,z2,z3,z1177,z4,z9]),(0,[z1,z2,z3,z4,z9,z1178]),(0,[z1179,z2,z3,z4,z5,z9]),(0,[z1,z2,z77,z436,z5,z9]),(0,[z1,z2,z1180,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z542,z5,z218]),(0,[z1,z2,z3,z1181,z5,z9]),(0,[z1,z2,z1182,z4,z5,z9]),(0,[z1,z302,z3,z24,z5,z9]),(0,[z1,z302,z325,z4,z5,z9])],[(0,[z1,z2,z3,z4,z1183,z9]),(0,[z1,z2,z3,z1184,z4,z9]),(0,[z1,z2,z3,z24,z9,z393]),(0,[z1,z2,z3,z4,z1185,z9]),(0,[z1,z2,z69,z4,z33,z9]),(0,[z1,z383,z4,z5,z9,z83])],[(0,[z1,z2,z10,z12,z5,z9]),(0,[z1,z2,z3,z301,z160,z9])],[(0,[z535,z26,z3,z4,z5,z9]),(0,[z1,z700,z3,z4,z179,z9]),(0,[z1,z2,z3,z4,z73,z9]),(0,[z1,z2,z3,z4,z1186,z9]),(0,[z1187,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z289,z33,z9]),(0,[z1,z1188,z3,z4,z5,z9]),(0,[z1,z429,z50,z4,z5,z9]),(0,[z1,z2,z3,z4,z1189,z9]),(0,[z1,z3,z212,z5,z9,z83]),(0,[z1,z2,z305,z24,z5,z9]),(0,[z317,z2,z3,z24,z5,z9]),(0,[z317,z2,z325,z4,z5,z9])],[(0,[z1,z2,z3,z154,z44,z9]),(0,[z1,z2,z24,z5,z9,z529]),(0,[z81,z2,z3,z242,z5,z9])],[(0,[z1,z2,z50,z4,z5,z263]),(0,[z1,z1190,z3,z4,z5,z9]),(0,[z1,z239,z3,z12,z179,z9]),(0,[z45,z2,z3,z12,z5,z9]),(0,[z1,z2,z3,z5,z9,z1191])],[(0,[z1,z2,z3,z4,z5,z1192]),(0,[z1,z2,z50,z12,z5,z9]),(0,[z1,z2,z4,z240,z44,z9]),(0,[z1,z2,z43,z195,z5,z30]),(0,[z94,z1,z2,z3,z5,z66])],[(0,[z1,z2,z3,z4,z5,z1193]),(0,[z1,z2,z3,z4,z885,z9]),(0,[z1,z1194,z2,z3,z4,z9]),(0,[z1,z68,z2,z325,z5,z9])],[(0,[z1,z2,z3,z77,z333,z9]),(0,[z1,z3,z4,z105,z846,z9]),(0,[z1,z382,z302,z3,z5,z9])],[(0,[z2,z3,z4,z5,z931,z9]),(0,[z1,z2,z3,z24,z207,z9]),(0,[z1,z2,z3,z4,z1195,z9])],[(0,[z1,z2,z3,z1196,z5,z9]),(0,[z47,z1,z2,z24,z44,z9]),(0,[z116,z322,z2,z3,z19,z9]),(0,[z1,z2,z638,z4,z5,z30])],[(0,[z1,z2,z3,z1197,z5,z9]),(0,[z424,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z1198,z5,z9]),(0,[z1,z2,z134,z4,z1028,z9]),(0,[z1,z2,z3,z843,z4,z9])],[(0,[z1,z246,z3,z4,z5,z9]),(0,[z1,z2,z3,z19,z288,z9]),(0,[z1,z2,z1199,z4,z5,z9]),(0,[z22,z1,z2,z3,z109,z9]),(0,[z1,z2,z3,z5,z9,z1200]),(0,[z1,z2,z119,z4,z5,z9])],[(0,[z1,z2,z3,z1201,z5,z9]),(0,[z1,z2,z3,z1202,z4,z9]),(0,[z1,z2,z33,z24,z44,z9]),(0,[z1,z334,z2,z356,z3,z9]),(0,[z1,z514,z3,z4,z396,z9]),(0,[z1,z2,z255,z4,z5,z151]),(0,[z45,z2,z3,z4,z288,z9])],[(0,[z1,z331,z3,z4,z33,z9]),(0,[z28,z2,z3,z4,z29,z393]),(0,[z81,z2,z3,z12,z5,z9])]],
   [[(0,[z1,z2,z3,z4,z221,z267]),(0,[z1,z2,z3,z1203,z5,z9]),(0,[z1,z98,z3,z4,z5,z449]),(0,[z1,z2,z3,z4,z9,z1204]),(0,[z1,z2,z3,z1205,z5,z9]),(0,[z1,z1206,z3,z4,z5,z9]),(0,[z1,z2,z24,z85,z44,z9]),(0,[z1,z2,z46,z24,z5,z9])],[(0,[z1,z91,z3,z4,z625,z9]),(0,[z1,z302,z3,z19,z5,z9]),(0,[z1,z2,z3,z24,z5,z367]),(0,[z1,z2,z3,z4,z5,z1207]),(0,[z1,z2,z3,z4,z1208,z9]),(0,[z630,z1,z3,z4,z5,z83]),(0,[z1,z2,z24,z5,z207,z9]),(0,[z1,z2,z3,z4,z190,z226])],[(0,[z21,z2,z3,z4,z90,z237]),(0,[z1,z2,z3,z1209,z5,z9]),(0,[z1,z2,z119,z4,z33,z9]),(0,[z1,z2,z3,z53,z316,z9]),(0,[z45,z302,z3,z4,z5,z9])],[(0,[z1,z1210,z2,z3,z5,z9]),(0,[z1,z98,z3,z12,z5,z9]),(0,[z1,z3,z4,z846,z5,z9]),(0,[z1,z2,z3,z12,z330,z9]),(0,[z430,z2,z3,z4,z5,z151])],[(0,[z1,z2,z3,z4,z5,z1211]),(0,[z2,z120,z4,z44,z9,z136]),(0,[z1,z2,z3,z4,z85,z739])],[(0,[z1,z2,z3,z4,z977,z9])],[(0,[z143,z1,z2,z4,z33,z151]),(0,[z1,z2,z325,z5,z9,z66])],[(0,[z1,z2,z3,z4,z1212,z9]),(0,[z1009,z1,z2,z3,z4,z5]),(0,[z1,z2,z1213,z4,z5,z9]),(0,[z1,z2,z3,z12,z225,z9]),(0,[z1,z2,z119,z461,z5,z9]),(0,[z1,z2,z145,z4,z436,z9]),(0,[z1,z2,z3,z109,z288,z9])],[(0,[z1,z2,z3,z1214,z5,z9]),(0,[z1,z2,z3,z1215,z5,z9]),(0,[z1,z2,z3,z5,z9,z354])],[(0,[z1,z761,z3,z4,z5,z9]),(0,[z1,z2,z3,z1216,z5,z9]),(0,[z1,z2,z3,z4,z5,z1217]),(0,[z94,z1,z2,z3,z329,z9]),(0,[z1,z239,z2,z432,z4,z9]),(0,[z1,z2,z50,z986,z5,z9])],[(0,[z1,z2,z3,z1218,z5,z9]),(0,[z1,z2,z3,z4,z5,z1219]),(0,[z1,z2,z3,z329,z51,z9]),(0,[z1,z52,z3,z77,z33,z9])],[(0,[z1,z2,z134,z212,z5,z9]),(0,[z1,z2,z163,z308,z5,z9]),(0,[z1,z2,z3,z330,z195,z9]),(0,[z1,z2,z3,z32,z5,z756]),(0,[z1,z2,z887,z109,z5,z9])],[(0,[z14,z1,z134,z4,z5,z83])],[(0,[z1,z2,z3,z4,z1098,z9])],[(0,[z21,z360,z2,z3,z4,z9]),(0,[z1,z2,z3,z294,z33,z9]),(0,[z110,z2,z3,z4,z9,z171])],[(0,[z1,z2,z1220,z4,z5,z9])]],
   [[(0,[z1,z2,z3,z1221,z4,z9]),(0,[z1,z331,z3,z289,z5,z9]),(0,[z561,z1,z2,z24,z5,z9]),(1,[z1,z3,z722,z5,z9]),(0,[z1222,z2,z3,z4,z5,z9]),(0,[z1,z2,z43,z24,z44,z9]),(0,[z1,z1032,z3,z24,z5,z9]),(0,[z1,z2,z3,z4,z1223,z9])],[(0,[z1,z2,z3,z4,z1224,z9]),(0,[z1,z2,z3,z4,z1225,z9]),(0,[z1,z3,z383,z4,z5,z83]),(0,[z92,z1,z2,z3,z5,z66]),(0,[z1,z2,z3,z1226,z5,z9])],[(0,[z182,z2,z89,z140,z5,z9]),(0,[z1,z239,z3,z4,z846,z9]),(0,[z1,z1227,z3,z4,z33,z9]),(0,[z1,z255,z4,z5,z9,z151])],[(0,[z11,z375,z3,z4,z5,z9]),(0,[z1,z2,z3,z1228,z5,z9]),(0,[z1,z2,z43,z4,z5,z273]),(0,[z1,z2,z538,z4,z44,z9])],[(0,[z1,z2,z1229,z4,z5,z9]),(0,[z1,z331,z3,z4,z73,z9]),(0,[z1,z1230,z3,z4,z5,z9]),(0,[z1,z2,z163,z4,z225,z9])],[(0,[z1,z1231,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z5,z1232]),(0,[z395,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z12,z160,z9])],[(0,[z1,z35,z246,z3,z4,z9]),(0,[z1,z2,z3,z125,z44,z9]),(0,[z1233,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z1234,z5,z9])],[(0,[z1,z2,z24,z5,z9,z151])],[(0,[z1,z2,z173,z24,z44,z9]),(0,[z1,z2,z1235,z4,z5,z9])],[(0,[z1,z2,z3,z4,z1236,z9]),(1,[z2,z3,z881,z5,z9]),(0,[z1,z593,z2,z436,z5,z9]),(1,[z1,z2,z436,z20,z9])],[(0,[z21,z2,z3,z232,z90,z9])],[(0,[z1,z2,z3,z371,z5,z571]),(0,[z1,z2,z120,z24,z44,z9]),(0,[z1,z2,z3,z1237,z5,z9]),(0,[z1,z2,z3,z109,z105,z9]),(0,[z1,z1238,z3,z4,z5,z9]),(0,[z1,z2,z3,z44,z9,z826])],[(0,[z1,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z859,z5,z9]),(0,[z28,z2,z3,z4,z33,z29]),(0,[z1,z2,z3,z4,z1239,z9]),(1,[z1,z2,z24,z207,z9])],[(0,[z1,z2,z3,z4,z1240,z9]),(0,[z1,z2,z3,z32,z5,z41]),(0,[z1,z2,z413,z24,z5,z9]),(0,[z81,z2,z3,z4,z144,z9])],[(0,[z1,z2,z3,z1241,z5,z9]),(0,[z394,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z289,z44,z9]),(0,[z1,z2,z3,z1242,z5,z9]),(0,[z1,z2,z3,z1243,z5,z9]),(0,[z1,z2,z1244,z4,z5,z9]),(0,[z1,z2,z3,z722,z5,z9]),(0,[z1,z334,z2,z3,z145,z9])],[(0,[z1,z2,z3,z4,z118,z226]),(0,[z1,z52,z3,z5,z9,z298])]],
   [[(0,[z1,z214,z2,z3,z4,z9]),(0,[z126,z2,z3,z238,z5,z9]),(0,[z1,z2,z3,z4,z5,z1245]),(0,[z15,z2,z134,z4,z5,z9]),(0,[z1,z2,z383,z4,z33,z9])],[(0,[z1,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z1246,z4,z9]),(0,[z1,z2,z24,z44,z194,z9]),(0,[z59,z1,z2,z3,z12,z171]),(0,[z81,z2,z3,z387,z5,z9])],[],[(0,[z1,z2,z3,z329,z77,z9]),(0,[z1,z1247,z3,z4,z5,z9]),(0,[z1,z1248,z2,z3,z4,z9]),(0,[z394,z2,z3,z4,z33,z9]),(0,[z1,z2,z24,z44,z44,z9])],[(0,[z1,z2,z3,z12,z221,z9]),(0,[z1,z2,z3,z1249,z5,z9]),(0,[z1,z2,z3,z4,z1250,z9]),(0,[z1,z2,z546,z4,z44,z9]),(0,[z182,z2,z89,z4,z530,z9]),(0,[z549,z2,z3,z19,z5,z9]),(0,[z1,z2,z3,z1251,z5,z9]),(0,[z1,z2,z134,z1088,z5,z9])],[(0,[z2,z3,z4,z5,z9,z256]),(0,[z1,z2,z3,z125,z5,z29]),(0,[z540,z1,z2,z4,z33,z9]),(0,[z1,z2,z3,z5,z9,z1252]),(0,[z1,z2,z24,z44,z218,z9]),(0,[z1,z2,z163,z4,z839,z9]),(0,[z1,z2,z3,z4,z1253,z9]),(0,[z1,z255,z3,z4,z33,z9])],[(0,[z1,z2,z3,z1254,z5,z9]),(0,[z1,z2,z3,z461,z5,z9]),(0,[z94,z1,z2,z3,z44,z66]),(0,[z1,z2,z3,z53,z386,z9])],[(0,[z2,z3,z125,z19,z5,z9]),(0,[z1,z2,z3,z1255,z5,z9]),(0,[z1,z2,z3,z145,z730,z9])],[(1,[z2,z3,z4,z5,z760]),(0,[z235,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z32,z5,z84])],[(0,[z216,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z1256,z5,z9]),(0,[z1,z2,z1257,z4,z5,z9]),(0,[z167,z2,z3,z881,z5,z9]),(0,[z548,z2,z3,z67,z5,z9]),(0,[z1,z2,z3,z4,z779,z9])],[(0,[z1,z2,z3,z249,z5,z449]),(0,[z1,z2,z3,z125,z5,z9]),(0,[z1,z129,z2,z3,z483,z9]),(0,[z94,z1,z2,z24,z44,z9]),(0,[z1,z593,z2,z3,z541,z9])],[(0,[z241,z1,z2,z24,z5,z9]),(0,[z1,z2,z3,z461,z33,z9]),(0,[z1,z2,z610,z4,z33,z9])],[(0,[z1,z2,z1258,z4,z5,z9]),(0,[z1,z246,z3,z4,z44,z9]),(0,[z1,z2,z474,z4,z5,z30]),(0,[z1259,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z1260]),(0,[z1,z2,z3,z53,z604,z9]),(0,[z1,z1261,z2,z3,z5,z9]),(0,[z1,z2,z3,z24,z300,z9]),(0,[z1,z2,z3,z4,z1262,z9]),(0,[z92,z1,z2,z4,z5,z151]),(0,[z1,z2,z119,z4,z44,z9]),(0,[z1,z2,z436,z5,z20,z9])],[(0,[z1,z429,z3,z232,z5,z9]),(0,[z1,z2,z3,z1263,z5,z9]),(0,[z557,z1,z3,z4,z5,z83]),(0,[z1,z91,z2,z24,z44,z9]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z3,z4,z44,z1264]),(0,[z1,z2,z3,z4,z1265,z9]),(0,[z1,z2,z3,z1266,z5,z9])],[(0,[z1,z2,z1267,z4,z5,z9]),(0,[z1,z2,z3,z4,z99,z9]),(0,[z1,z2,z3,z1268,z5,z9]),(0,[z216,z2,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z1269]),(0,[z2,z3,z24,z5,z9,z256])],[(0,[z1,z2,z3,z4,z265,z9]),(0,[z430,z2,z3,z24,z5,z9]),(1,[z1,z2,z4,z1098,z9]),(0,[z94,z1,z2,z3,z5,z260])]],
   [[(0,[z21,z2,z3,z4,z352,z9]),(0,[z1,z2,z24,z44,z226,z9]),(0,[z143,z1,z2,z4,z44,z151])],[(0,[z1,z2,z3,z1270,z4,z9]),(0,[z1,z2,z3,z1271,z5,z9]),(0,[z1,z2,z173,z4,z5,z680]),(0,[z504,z1,z2,z4,z5,z151]),(0,[z15,z2,z3,z24,z5,z9]),(0,[z1,z492,z2,z356,z3,z9]),(0,[z115,z1,z2,z4,z33,z9])],[(0,[z47,z26,z3,z24,z5,z9]),(0,[z182,z1,z2,z24,z44,z9]),(0,[z1,z2,z3,z1272,z5,z9]),(0,[z1,z2,z3,z228,z5,z84]),(0,[z2,z3,z4,z5,z9,z1012]),(0,[z1,z2,z3,z1273,z5,z9]),(0,[z1,z2,z3,z1274,z5,z9]),(0,[z1275,z2,z3,z4,z5,z9])],[(0,[z92,z1,z2,z3,z5,z189])],[(0,[z1,z2,z10,z966,z5,z9]),(0,[z1,z2,z3,z1276,z5,z9]),(0,[z1,z2,z3,z1277,z5,z9]),(0,[z1,z2,z3,z1278,z5,z9]),(0,[z1,z382,z2,z3,z33,z9]),(0,[z1,z2,z43,z33,z24,z9])],[(0,[z1,z48,z10,z4,z5,z9]),(0,[z1,z2,z3,z1279,z5,z9]),(0,[z1,z239,z246,z3,z4,z9]),(0,[z1,z2,z432,z1031,z5,z9]),(0,[z1,z2,z3,z1280,z5,z9]),(0,[z1,z2,z3,z12,z138,z9]),(0,[z1,z2,z12,z436,z5,z9])],[(0,[z1,z2,z3,z4,z1281,z9]),(0,[z1,z2,z3,z238,z5,z62]),(0,[z1,z2,z3,z1282,z5,z9]),(0,[z1,z2,z3,z5,z9,z1283]),(0,[z1,z2,z383,z1284,z5,z9]),(0,[z1,z2,z228,z24,z5,z9]),(0,[z1285,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z1284,z5,z9]),(0,[z1,z2,z3,z1215,z44,z9])],[(0,[z47,z26,z3,z4,z5,z571]),(0,[z1,z1286,z3,z4,z5,z9]),(0,[z1,z2,z3,z232,z85,z9]),(0,[z1,z2,z3,z4,z261,z9])],[(0,[z692,z2,z3,z19,z5,z9]),(0,[z1,z2,z528,z12,z5,z9]),(0,[z81,z247,z3,z4,z5,z9])],[(0,[z1,z2,z3,z99,z146,z9]),(0,[z1,z2,z3,z4,z1287,z9]),(0,[z1,z2,z3,z436,z20,z9])],[(0,[z47,z26,z555,z4,z5,z9]),(0,[z1,z2,z61,z4,z44,z9])],[(0,[z1,z2,z3,z4,z1288,z9]),(0,[z1,z2,z3,z4,z5,z1289]),(0,[z1,z2,z24,z105,z44,z9])],[(0,[z1,z2,z3,z1290,z5,z9]),(0,[z1,z331,z3,z4,z5,z9])],[(0,[z94,z2,z3,z19,z5,z136]),(0,[z1,z2,z4,z623,z44,z9]),(0,[z1,z1291,z2,z3,z4,z9]),(0,[z1292,z2,z3,z4,z5,z9])],[(0,[z11,z2,z3,z4,z5,z571]),(0,[z1,z2,z3,z329,z232,z9]),(0,[z1293,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z1294,z5,z9])]],
   [[(0,[z1,z2,z3,z1295,z5,z9]),(0,[z28,z246,z3,z4,z5,z9]),(0,[z368,z1,z2,z4,z44,z9])],[(0,[z1,z2,z3,z4,z345,z9]),(1,[z1,z3,z4,z846,z9]),(0,[z1,z2,z3,z1296,z5,z9]),(1,[z1,z383,z4,z5,z83]),(0,[z1,z2,z3,z4,z5,z1264])],[(0,[z1,z2,z3,z4,z9,z1297]),(0,[z1,z2,z3,z1298,z5,z9]),(0,[z1,z2,z3,z4,z5,z1299]),(0,[z1,z334,z2,z24,z44,z9]),(0,[z1,z2,z163,z12,z33,z9])],[(0,[z1,z48,z2,z24,z44,z9]),(0,[z81,z2,z3,z4,z276,z9]),(0,[z1,z2,z3,z4,z1300,z9])],[(0,[z1,z2,z432,z4,z9,z171]),(0,[z38,z1,z173,z4,z5,z9]),(0,[z92,z1,z2,z24,z44,z9]),(0,[z143,z1,z2,z4,z5,z151]),(0,[z1,z2,z3,z242,z144,z9]),(0,[z1,z2,z1301,z4,z5,z9]),(0,[z59,z1,z2,z3,z109,z171])],[(0,[z1,z2,z699,z4,z44,z9]),(0,[z167,z2,z3,z79,z5,z9]),(0,[z216,z2,z3,z4,z261,z9]),(0,[z1,z382,z3,z51,z5,z9]),(0,[z1,z2,z3,z109,z179,z9])],[(0,[z1,z2,z3,z1302,z5,z9]),(0,[z1,z2,z277,z24,z5,z9])],[(0,[z1,z2,z3,z154,z5,z571]),(0,[z182,z2,z89,z24,z5,z9]),(0,[z1,z2,z3,z4,z1303,z9]),(0,[z1,z2,z3,z4,z1304,z9]),(0,[z1,z2,z3,z5,z9,z756])],[(0,[z1,z2,z3,z4,z1305,z9]),(0,[z1,z2,z3,z1306,z4,z9]),(0,[z1307,z2,z3,z4,z5,z9]),(0,[z1,z52,z3,z77,z5,z9]),(0,[z1,z2,z3,z4,z1308,z9]),(0,[z1,z2,z134,z4,z33,z9]),(0,[z14,z1,z2,z24,z44,z9]),(0,[z1,z2,z381,z4,z44,z9]),(0,[z110,z2,z3,z4,z33,z9])],[(0,[z1,z2,z3,z12,z39,z9]),(0,[z38,z1,z173,z4,z33,z9]),(0,[z1309,z2,z3,z4,z5,z9])],[(0,[z1,z2,z555,z154,z5,z9]),(0,[z1,z2,z4,z643,z44,z9]),(0,[z1,z2,z383,z4,z44,z9]),(0,[z1,z2,z24,z5,z9,z706]),(0,[z1,z2,z3,z491,z5,z9])],[(0,[z1,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z12,z299,z9]),(0,[z1310,z2,z3,z4,z5,z9]),(0,[z59,z1,z2,z3,z24,z171]),(0,[z148,z1,z2,z4,z33,z9])],[(0,[z1,z2,z3,z4,z1311,z9]),(0,[z1,z2,z3,z294,z5,z9]),(0,[z1,z2,z3,z195,z225,z9])],[(0,[z1,z2,z1169,z4,z5,z9]),(0,[z1,z2,z3,z4,z172,z1312]),(0,[z1,z2,z280,z4,z44,z9]),(0,[z1,z2,z3,z56,z5,z680]),(0,[z394,z2,z3,z4,z44,z9])],[(0,[z1,z2,z1313,z4,z5,z9]),(0,[z1,z2,z3,z287,z5,z9]),(0,[z1,z2,z3,z24,z1132,z9]),(0,[z1,z2,z3,z12,z144,z9]),(0,[z1,z2,z3,z12,z915,z9]),(0,[z1,z341,z3,z4,z33,z9])],[(0,[z1,z2,z3,z12,z5,z267]),(0,[z1,z2,z601,z4,z44,z9]),(0,[z1,z129,z2,z3,z519,z9]),(0,[z1,z1314,z3,z4,z5,z9]),(0,[z1,z255,z3,z4,z44,z9]),(0,[z1,z2,z3,z491,z33,z9])]],
   [[(0,[z1,z1227,z3,z4,z5,z9]),(0,[z1,z2,z3,z1315,z5,z9]),(0,[z1,z2,z383,z4,z400,z9]),(0,[z1,z93,z2,z24,z44,z9])],[(0,[z1,z2,z3,z4,z9,z1316]),(0,[z1,z2,z3,z4,z400,z9]),(0,[z1,z2,z305,z308,z5,z9]),(0,[z1,z492,z2,z3,z145,z9])],[(0,[z1,z2,z3,z1317,z5,z9]),(0,[z1,z2,z3,z4,z1318,z9]),(0,[z1,z907,z2,z3,z12,z9])],[(0,[z1,z2,z3,z125,z5,z136]),(0,[z394,z2,z3,z4,z400,z9]),(0,[z1,z2,z3,z287,z33,z9]),(0,[z94,z1,z2,z3,z314,z66])],[(0,[z1,z2,z3,z1319,z5,z9]),(0,[z258,z1,z2,z3,z4,z171]),(0,[z1,z3,z4,z5,z9,z886])],[(0,[z1,z2,z3,z371,z221,z9]),(0,[z182,z2,z3,z4,z5,z449]),(0,[z96,z1,z2,z24,z44,z9]),(0,[z1,z2,z327,z24,z5,z9]),(0,[z1,z2,z3,z461,z44,z9]),(0,[z1,z2,z3,z1320,z5,z9])],[(0,[z1,z2,z1321,z4,z5,z9]),(1,[z1,z2,z897,z5,z9])],[(0,[z1,z2,z3,z4,z5,z1322]),(0,[z1,z2,z3,z4,z1323,z9]),(0,[z2,z3,z4,z33,z9,z1324])],[(0,[z11,z48,z3,z12,z5,z9]),(0,[z216,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z389,z386,z9]),(0,[z1,z2,z4,z1325,z5,z9])],[(0,[z1,z173,z4,z5,z83,z151]),(0,[z149,z2,z3,z4,z426,z9]),(0,[z1,z2,z119,z4,z314,z9])],[(0,[z1,z246,z432,z4,z5,z9]),(0,[z21,z429,z3,z4,z90,z9]),(0,[z28,z2,z3,z4,z5,z29]),(0,[z1326,z2,z3,z4,z5,z9])],[(0,[z1327,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z1328,z5,z9]),(0,[z1,z2,z3,z24,z5,z6]),(0,[z21,z2,z3,z4,z90,z263]),(0,[z1,z2,z3,z4,z5,z1329]),(0,[z1330,z2,z3,z4,z5,z9]),(0,[z1,z2,z1331,z4,z5,z9]),(0,[z1332,z1,z2,z4,z5,z9]),(0,[z1,z2,z3,z1333,z5,z9]),(0,[z143,z1,z2,z24,z44,z9]),(0,[z1,z2,z335,z12,z5,z9])],[(0,[z1,z2,z3,z1334,z5,z9]),(0,[z21,z2,z3,z12,z90,z9]),(0,[z126,z2,z3,z4,z33,z9]),(0,[z1335,z2,z3,z4,z5,z9]),(0,[z557,z1,z2,z3,z5,z66]),(0,[z1,z1336,z3,z4,z44,z9])],[(0,[z1,z2,z3,z1337,z5,z9]),(0,[z0,z2,z120,z4,z5,z6]),(0,[z362,z2,z3,z19,z5,z9]),(0,[z1,z2,z383,z4,z5,z9]),(0,[z1,z68,z2,z24,z44,z9]),(0,[z1,z2,z297,z24,z44,z9]),(0,[z1,z2,z3,z1338,z5,z9])],[(0,[z1,z2,z3,z33,z146,z9]),(0,[z1,z2,z3,z4,z9,z1312])]],
   [[(0,[z1,z2,z3,z12,z5,z172]),(0,[z38,z1,z173,z4,z261,z9]),(0,[z394,z2,z383,z4,z5,z9]),(0,[z14,z1,z3,z24,z5,z83]),(0,[z368,z1,z2,z4,z5,z151]),(0,[z1,z247,z3,z242,z5,z9])],[(0,[z1,z2,z555,z371,z5,z9]),(0,[z1,z2,z3,z33,z185,z9])],[(0,[z1,z2,z3,z140,z5,z9])],[(0,[z1,z2,z1339,z4,z5,z9]),(0,[z1,z2,z325,z67,z5,z9]),(0,[z1,z2,z3,z32,z5,z364]),(0,[z1,z255,z3,z4,z5,z9]),(0,[z170,z1,z2,z24,z5,z9])],[(0,[z1,z2,z3,z4,z1340,z9]),(0,[z1,z2,z3,z238,z5,z680]),(0,[z1,z2,z3,z1341,z5,z9]),(0,[z1,z2,z24,z5,z9,z111]),(0,[z1,z2,z3,z5,z9,z1342])],[(0,[z1,z2,z3,z1343,z5,z9]),(0,[z1,z2,z432,z1214,z5,z9]),(0,[z1,z52,z2,z325,z5,z9]),(0,[z1,z2,z43,z4,z5,z30])],[(0,[z1,z2,z10,z371,z5,z9])],[(0,[z1,z2,z3,z140,z33,z9])],[(0,[z1,z2,z3,z1344,z5,z9]),(0,[z1,z2,z3,z4,z1345,z9]),(0,[z28,z2,z3,z125,z5,z29]),(0,[z1,z2,z3,z44,z9,z303])],[(0,[z1,z2,z3,z12,z333,z9])],[(0,[z1,z2,z3,z1346,z5,z9]),(0,[z1,z2,z3,z56,z39,z9]),(0,[z1,z2,z3,z4,z5,z1347]),(0,[z1,z2,z3,z1348,z5,z9]),(0,[z1,z247,z3,z12,z5,z9]),(0,[z1,z2,z43,z4,z33,z30]),(0,[z1,z2,z3,z242,z276,z9]),(0,[z2,z3,z4,z85,z226,z256])],[(0,[z1,z2,z3,z4,z5,z1349]),(0,[z1,z2,z3,z232,z9,z171]),(0,[z1,z2,z3,z596,z33,z9]),(0,[z1,z2,z3,z4,z877,z9]),(0,[z1,z2,z3,z1350,z5,z9]),(0,[z94,z1,z2,z3,z333,z9]),(0,[z1351,z2,z3,z4,z5,z9]),(0,[z1,z2,z4,z33,z1098,z9]),(0,[z143,z1,z247,z4,z5,z151]),(0,[z1,z2,z3,z1352,z5,z9])],[(0,[z1,z331,z3,z4,z44,z9]),(0,[z1,z2,z163,z12,z44,z9]),(0,[z1353,z2,z3,z4,z5,z9]),(1,[z1,z2,z3,z4,z739])],[(0,[z1,z382,z2,z3,z5,z29]),(0,[z1,z2,z3,z4,z5,z1354]),(0,[z395,z1,z2,z24,z44,z9]),(0,[z1,z2,z3,z12,z85,z226]),(0,[z1,z341,z119,z4,z5,z9])],[(0,[z1,z2,z555,z1172,z5,z9]),(0,[z1,z2,z3,z24,z73,z9]),(0,[z1,z1355,z2,z3,z4,z9]),(0,[z1,z2,z4,z436,z179,z9]),(0,[z1,z2,z3,z4,z1356,z9])],[(0,[z1,z429,z3,z4,z5,z263]),(0,[z1357,z2,z3,z4,z5,z9]),(0,[z548,z2,z3,z366,z5,z9]),(0,[z1,z2,z3,z1358,z5,z9]),(0,[z1,z2,z43,z461,z5,z30])]],
   [[(0,[z1,z2,z10,z4,z1162,z9]),(0,[z1,z2,z3,z12,z5,z449]),(0,[z1,z1359,z3,z4,z5,z9]),(0,[z1,z429,z3,z12,z5,z9]),(0,[z1,z2,z3,z4,z118,z9]),(0,[z28,z2,z3,z4,z118,z9]),(0,[z1,z2,z3,z4,z1360,z9]),(0,[z1,z2,z3,z387,z144,z9]),(0,[z1361,z2,z3,z4,z5,z9])],[(0,[z11,z691,z3,z4,z5,z9]),(0,[z1,z2,z89,z4,z73,z9]),(0,[z1,z2,z3,z4,z1362,z9]),(0,[z1,z2,z3,z1363,z5,z9]),(0,[z1,z1336,z3,z4,z5,z9])],[(0,[z1,z2,z555,z4,z1176,z9]),(0,[z47,z26,z3,z4,z221,z9]),(0,[z1,z2,z3,z4,z1364,z9]),(0,[z1,z2,z3,z12,z5,z263]),(0,[z1,z382,z2,z3,z5,z9]),(0,[z1,z2,z109,z897,z5,z9])],[(0,[z1,z1365,z3,z4,z5,z9]),(0,[z1,z2,z3,z1366,z5,z9]),(0,[z1,z2,z271,z4,z44,z9]),(0,[z1,z2,z3,z4,z33,z62]),(0,[z38,z1,z173,z4,z44,z9]),(0,[z1,z2,z43,z451,z5,z9]),(0,[z71,z1,z2,z24,z44,z9]),(0,[z1,z2,z43,z24,z5,z151]),(0,[z1,z2,z24,z176,z5,z9]),(0,[z1,z2,z114,z4,z44,z9])],[(0,[z1,z2,z3,z4,z530,z9]),(0,[z1,z2,z3,z4,z1367,z9]),(0,[z36,z2,z120,z4,z5,z9]),(0,[z182,z2,z89,z146,z5,z9]),(0,[z1,z2,z3,z881,z5,z9]),(0,[z126,z2,z3,z4,z261,z9]),(0,[z609,z1,z173,z4,z5,z9]),(0,[z38,z1,z861,z4,z5,z9]),(0,[z1368,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z276,z9])],[(0,[z45,z2,z3,z67,z5,z9]),(0,[z1,z2,z1369,z4,z5,z9])],[(0,[z1,z239,z2,z24,z44,z9]),(0,[z1,z2,z24,z190,z44,z9])],[(0,[z1,z52,z3,z77,z44,z9]),(0,[z1,z2,z4,z42,z44,z9]),(0,[z268,z1,z2,z4,z33,z9]),(0,[z1,z2,z3,z897,z5,z9])],[(0,[z1,z2,z3,z1370,z5,z9]),(0,[z1,z246,z3,z24,z5,z9]),(0,[z1,z2,z3,z1371,z5,z9]),(0,[z1372,z2,z3,z4,z5,z9]),(0,[z1,z2,z114,z4,z1098,z9]),(0,[z1,z2,z3,z4,z314,z9]),(0,[z1,z274,z2,z3,z145,z9]),(0,[z1,z2,z3,z1373,z5,z9])],[(0,[z1,z2,z1374,z4,z5,z9]),(0,[z1,z2,z3,z4,z1375,z9]),(0,[z1,z2,z3,z491,z44,z9]),(0,[z148,z1,z2,z491,z33,z9])],[(0,[z439,z2,z3,z4,z5,z136]),(0,[z2,z3,z4,z5,z760,z136]),(0,[z1,z243,z3,z77,z5,z9]),(0,[z1376,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z4,z1098,z9]),(0,[z1377,z2,z3,z4,z5,z9])],[(0,[z1,z98,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1378,z9]),(0,[z1,z2,z3,z294,z44,z9]),(0,[z112,z1,z2,z24,z5,z9]),(0,[z1,z2,z24,z44,z9,z213]),(0,[z1,z2,z4,z24,z225,z9]),(0,[z1,z2,z3,z12,z288,z9])],[(0,[z536,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z4,z5,z1379]),(0,[z1,z2,z3,z4,z5,z1380]),(0,[z1,z2,z3,z4,z1381,z9]),(0,[z1382,z2,z3,z4,z5,z9]),(0,[z1,z2,z438,z24,z5,z9]),(0,[z1,z2,z3,z1383,z5,z9]),(0,[z1004,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z33,z195,z9])],[(0,[z1,z2,z3,z287,z44,z9])],[(0,[z1,z2,z3,z4,z5,z1384]),(0,[z1,z2,z432,z4,z33,z9])],[(0,[z1,z2,z3,z4,z5,z1385]),(0,[z1,z2,z3,z4,z5,z1386]),(0,[z1387,z2,z3,z4,z5,z9]),(0,[z1,z599,z3,z4,z5,z194]),(0,[z1,z1388,z3,z4,z5,z9]),(0,[z1,z302,z3,z12,z5,z9]),(0,[z1,z2,z3,z145,z288,z9])]],
   [[(0,[z1,z2,z3,z5,z9,z1389]),(0,[z1,z2,z3,z12,z9,z393]),(0,[z1,z2,z383,z4,z1390,z9]),(0,[z1,z2,z163,z12,z5,z9]),(0,[z1,z1391,z3,z4,z5,z9])],[(0,[z1,z2,z3,z154,z221,z9]),(0,[z1,z2,z3,z4,z5,z1392]),(0,[z110,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z238,z39,z9]),(0,[z1,z2,z3,z4,z1390,z9]),(0,[z1,z2,z3,z4,z1393,z9]),(0,[z1,z593,z2,z24,z44,z9]),(0,[z1,z2,z3,z4,z33,z1380]),(0,[z1,z2,z3,z4,z558,z295]),(0,[z1,z2,z436,z5,z218,z9])],[(0,[z1,z2,z4,z88,z44,z9]),(0,[z1,z2,z3,z4,z1394,z9])],[(0,[z47,z26,z10,z4,z5,z9]),(0,[z1,z2,z89,z4,z977,z9]),(0,[z21,z1,z2,z3,z294,z9]),(0,[z1,z2,z3,z4,z5,z760]),(0,[z1,z2,z3,z4,z1395,z9]),(0,[z28,z2,z3,z4,z5,z760]),(0,[z1,z93,z3,z4,z179,z9]),(0,[z1,z2,z3,z1396,z5,z9]),(0,[z1,z2,z305,z12,z5,z9]),(0,[z317,z2,z3,z12,z5,z9]),(0,[z1,z302,z3,z145,z5,z9])],[(0,[z1,z2,z4,z99,z44,z9]),(0,[z1,z2,z3,z4,z1397,z9]),(0,[z1,z2,z399,z4,z44,z9]),(0,[z14,z1,z3,z4,z5,z886]),(0,[z1,z2,z24,z5,z9,z234])],[(0,[z1,z2,z3,z24,z5,z1219]),(0,[z1,z2,z3,z4,z1023,z9])],[(0,[z1,z2,z3,z4,z1398,z9]),(0,[z1,z2,z3,z4,z1399,z9]),(0,[z110,z2,z3,z4,z5,z9]),(0,[z1,z2,z134,z4,z5,z9]),(0,[z1,z2,z3,z4,z1400,z9]),(0,[z1,z2,z3,z4,z1401,z9]),(0,[z1,z2,z3,z4,z33,z1392]),(0,[z94,z45,z2,z3,z5,z66])],[(0,[z1,z2,z3,z1402,z5,z9]),(0,[z126,z2,z3,z4,z44,z9]),(0,[z1,z2,z4,z436,z105,z9]),(0,[z1,z2,z3,z4,z1135,z9]),(0,[z1,z302,z3,z4,z288,z9])],[(0,[z1,z2,z3,z4,z1403,z9]),(0,[z38,z126,z173,z4,z5,z9]),(0,[z1,z52,z2,z24,z44,z9]),(0,[z394,z2,z134,z4,z5,z9]),(0,[z1,z247,z3,z4,z144,z9])],[(0,[z1,z129,z2,z432,z4,z9]),(0,[z591,z2,z3,z4,z5,z136]),(0,[z28,z2,z3,z4,z44,z29]),(0,[z1,z2,z3,z33,z451,z9]),(0,[z1,z2,z3,z284,z5,z9]),(0,[z14,z1,z3,z301,z5,z83]),(0,[z1,z2,z3,z12,z207,z9])],[(0,[z11,z2,z10,z4,z5,z9]),(0,[z1,z2,z3,z24,z178,z9]),(0,[z1,z246,z3,z596,z5,z9]),(0,[z1,z2,z3,z4,z261,z62]),(0,[z1,z2,z1404,z4,z5,z9]),(0,[z1,z2,z24,z190,z5,z9])],[(0,[z1,z246,z50,z4,z5,z9]),(0,[z21,z2,z3,z124,z4,z9]),(0,[z1,z2,z3,z4,z820,z5]),(0,[z1,z2,z3,z1405,z5,z9]),(0,[z1,z2,z3,z1406,z5,z9]),(0,[z1,z2,z24,z88,z44,z9]),(0,[z1,z2,z3,z297,z5,z218]),(0,[z1,z2,z3,z435,z25,z9]),(0,[z317,z2,z3,z4,z288,z9])],[(0,[z1,z2,z3,z4,z1407,z9]),(0,[z0,z2,z120,z4,z178,z9]),(0,[z1,z341,z3,z4,z5,z9]),(0,[z1,z695,z3,z4,z105,z9]),(0,[z1,z2,z3,z1408,z5,z9]),(0,[z1,z247,z3,z387,z5,z9])],[(0,[z1,z98,z3,z4,z73,z9]),(0,[z2,z3,z4,z5,z172,z136]),(0,[z1,z2,z3,z4,z33,z237])],[(0,[z1,z2,z1409,z4,z5,z9]),(0,[z1,z2,z4,z128,z44,z9]),(0,[z1,z2,z3,z284,z33,z9]),(0,[z1,z1410,z2,z3,z5,z9])],[(0,[z1,z1411,z2,z3,z4,z9]),(0,[z1130,z2,z3,z24,z5,z9]),(0,[z317,z302,z3,z4,z5,z9])]],
   [[(0,[z1,z1412,z3,z4,z5,z9]),(0,[z1,z2,z3,z12,z5,z367]),(0,[z1,z2,z24,z5,z9,z272]),(0,[z1,z2,z3,z212,z160,z9])],[(0,[z1,z2,z3,z140,z44,z9]),(0,[z1,z2,z3,z4,z1413,z9]),(0,[z521,z1,z3,z4,z5,z83]),(0,[z14,z1,z3,z4,z160,z83]),(0,[z1,z2,z3,z1414,z5,z9])],[(0,[z1,z2,z10,z154,z5,z9]),(0,[z1,z3,z51,z5,z9,z657]),(0,[z1,z2,z3,z4,z846,z9]),(0,[z1,z2,z383,z4,z5,z83]),(0,[z1,z2,z3,z4,z262,z9]),(0,[z201,z1,z2,z24,z5,z9]),(0,[z143,z81,z2,z4,z5,z151]),(0,[z1,z2,z43,z387,z5,z9]),(0,[z110,z2,z3,z1352,z5,z9])],[(0,[z1,z2,z1415,z4,z5,z9]),(0,[z1,z2,z3,z4,z1416,z9]),(0,[z1,z2,z24,z27,z44,z9])],[(0,[z606,z1,z173,z4,z5,z9]),(0,[z1,z1417,z2,z3,z5,z9]),(0,[z1044,z2,z3,z4,z5,z9]),(0,[z1,z2,z43,z4,z44,z30])],[(0,[z1,z2,z3,z4,z5,z1418]),(0,[z1419,z2,z3,z4,z5,z9]),(0,[z394,z2,z3,z4,z5,z83]),(0,[z1,z593,z2,z24,z5,z9]),(0,[z181,z1,z2,z24,z5,z9])],[(0,[z1,z2,z3,z5,z218,z76]),(0,[z1,z2,z163,z4,z207,z9]),(0,[z1,z613,z2,z24,z44,z9]),(0,[z1,z1238,z3,z24,z5,z9]),(0,[z1,z93,z3,z4,z554,z9]),(0,[z1,z2,z3,z387,z276,z9])],[(0,[z1,z465,z3,z51,z5,z9]),(0,[z1,z2,z325,z4,z5,z9]),(0,[z1,z2,z3,z53,z20,z9])],[(0,[z1,z2,z1420,z4,z5,z9]),(0,[z1,z2,z3,z185,z44,z9]),(0,[z1421,z2,z3,z4,z5,z9])],[(0,[z1,z2,z3,z4,z815,z9]),(0,[z1,z2,z3,z5,z9,z1422]),(0,[z1,z2,z174,z4,z44,z9]),(0,[z430,z2,z3,z4,z144,z9])],[(0,[z1,z2,z3,z4,z1423,z9]),(0,[z1,z2,z77,z24,z44,z9]),(0,[z14,z15,z3,z4,z5,z83])],[(0,[z126,z2,z3,z4,z5,z9]),(0,[z148,z1,z2,z4,z99,z9]),(0,[z1,z2,z402,z4,z44,z9]),(0,[z1,z2,z3,z4,z5,z1424]),(0,[z1,z462,z3,z77,z5,z9]),(0,[z1,z382,z2,z3,z5,z136]),(0,[z1,z2,z4,z184,z44,z9]),(0,[z1,z928,z3,z12,z5,z9]),(0,[z1353,z2,z3,z4,z44,z9]),(0,[z1,z2,z3,z1425,z5,z9])],[(0,[z1,z2,z10,z4,z1128,z9]),(0,[z1,z2,z3,z4,z1426,z9]),(0,[z1,z2,z24,z44,z25,z9]),(0,[z1,z2,z43,z934,z5,z9]),(0,[z1,z2,z325,z4,z33,z9])],[(0,[z1,z2,z3,z4,z5,z571]),(0,[z47,z26,z3,z4,z5,z267]),(0,[z1,z2,z3,z4,z1427,z9]),(0,[z1,z2,z3,z4,z44,z62]),(0,[z15,z2,z3,z301,z5,z9]),(0,[z1428,z2,z3,z4,z5,z9])],[(0,[z1,z35,z2,z3,z12,z9]),(0,[z0,z2,z120,z4,z33,z9])],[(0,[z1,z2,z3,z4,z1429,z9]),(0,[z1,z129,z2,z3,z541,z9]),(0,[z110,z2,z3,z1373,z5,z9])]],
   [[(0,[z1,z2,z3,z1430,z5,z9]),(0,[z1,z2,z24,z5,z29,z151]),(0,[z1,z2,z3,z299,z451,z9]),(0,[z1,z3,z4,z722,z5,z9]),(0,[z1,z2,z3,z4,z1431,z9]),(0,[z1,z593,z2,z3,z145,z9]),(1,[z1,z2,z3,z730,z9])],[(0,[z1,z2,z3,z4,z33,z680]),(0,[z1,z2,z3,z1432,z5,z9]),(0,[z1,z382,z2,z3,z44,z9]),(0,[z1,z2,z3,z763,z33,z9]),(0,[z1,z302,z3,z5,z9,z66])],[(0,[z1,z2,z3,z4,z33,z571]),(0,[z11,z1,z2,z24,z44,z9]),(0,[z1,z2,z3,z1433,z5,z9])],[(0,[z1,z2,z3,z1434,z5,z9])],[(0,[z1,z2,z3,z974,z5,z9]),(0,[z1,z2,z3,z1435,z5,z9]),(0,[z1,z2,z1436,z4,z5,z9]),(0,[z370,z2,z3,z67,z5,z9]),(0,[z1,z246,z3,z4,z27,z9]),(0,[z135,z2,z3,z4,z33,z136]),(0,[z1,z2,z4,z808,z5,z9])],[(0,[z1,z2,z555,z4,z33,z9]),(0,[z1,z2,z3,z249,z5,z6]),(0,[z1,z2,z3,z4,z1437,z9]),(0,[z1,z2,z3,z232,z33,z9]),(0,[z1,z2,z3,z4,z237,z171]),(0,[z15,z2,z3,z4,z160,z9]),(0,[z1,z2,z114,z287,z44,z9])],[(0,[z1,z342,z3,z4,z179,z9]),(0,[z1,z2,z451,z5,z9,z151]),(0,[z14,z1,z3,z5,z354,z83]),(0,[z1,z236,z3,z464,z5,z9])],[(0,[z576,z26,z3,z4,z5,z9]),(0,[z1,z2,z3,z1438,z4,z9]),(0,[z92,z1,z2,z24,z5,z151])],[(0,[z1,z2,z432,z4,z44,z9])],[(0,[z1,z2,z3,z4,z1439,z9]),(0,[z1,z98,z3,z4,z178,z9]),(0,[z1,z2,z3,z596,z5,z9]),(0,[z45,z2,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z1440,z9]),(0,[z1,z91,z3,z294,z105,z9]),(0,[z1,z169,z3,z212,z5,z9]),(0,[z1,z2,z4,z33,z44,z9]),(0,[z1,z2,z53,z436,z20,z9])],[(0,[z1,z2,z10,z4,z33,z9]),(0,[z1,z2,z120,z12,z44,z9]),(0,[z1,z322,z2,z3,z4,z9]),(0,[z323,z2,z3,z19,z5,z9]),(0,[z1,z2,z69,z24,z5,z9]),(0,[z1,z129,z2,z3,z488,z9]),(0,[z112,z1,z2,z24,z44,z9]),(0,[z1,z2,z3,z730,z20,z9]),(0,[z1,z2,z3,z4,z731,z9])],[(0,[z1441,z2,z3,z4,z5,z9]),(0,[z1,z2,z266,z4,z44,z9]),(0,[z1,z1442,z3,z4,z5,z9])],[(0,[z1,z2,z285,z12,z5,z9]),(0,[z1,z246,z3,z4,z5,z237]),(0,[z1,z2,z3,z185,z5,z9])],[(0,[z1,z2,z89,z4,z265,z9]),(0,[z1,z2,z3,z1443,z5,z9])],[(0,[z0,z1,z2,z24,z44,z9]),(0,[z28,z2,z3,z4,z118,z29]),(0,[z1,z2,z3,z1444,z5,z9]),(0,[z45,z2,z3,z4,z33,z9]),(0,[z1,z247,z3,z4,z276,z9])],[(0,[z0,z2,z120,z289,z5,z9]),(0,[z1,z2,z50,z4,z33,z9]),(0,[z110,z2,z3,z4,z5,z136]),(0,[z1,z2,z3,z1445,z5,z9]),(0,[z1,z2,z3,z4,z5,z739])]],
   [[],[(0,[z1,z129,z2,z3,z232,z9]),(0,[z1,z2,z3,z4,z5,z62]),(0,[z1,z2,z3,z4,z1446,z9]),(0,[z1,z2,z12,z24,z5,z9])],[(0,[z1,z719,z3,z4,z44,z9]),(0,[z1,z255,z3,z4,z5,z151])],[(0,[z0,z2,z120,z4,z73,z9]),(0,[z1,z2,z3,z24,z261,z9]),(0,[z430,z2,z3,z4,z5,z30]),(0,[z94,z1,z2,z3,z5,z756])],[(0,[z1,z68,z3,z615,z5,z9]),(0,[z1,z2,z3,z1447,z5,z9]),(0,[z1,z2,z3,z4,z883,z9]),(0,[z430,z2,z3,z242,z5,z9])],[(0,[z1,z2,z134,z4,z44,z9]),(0,[z1,z2,z24,z313,z44,z9]),(0,[z1,z2,z24,z44,z30,z9]),(0,[z1,z2,z3,z12,z42,z9]),(0,[z110,z2,z3,z4,z44,z9]),(0,[z2,z3,z4,z5,z9,z1324])],[(0,[z1,z2,z1448,z4,z5,z9])],[(0,[z1,z2,z3,z249,z73,z9]),(0,[z1,z2,z3,z140,z99,z9]),(0,[z1,z2,z3,z4,z44,z237]),(0,[z45,z2,z3,z125,z5,z9]),(0,[z1449,z2,z3,z4,z5,z9]),(0,[z81,z2,z3,z4,z33,z9])],[(0,[z2,z26,z3,z4,z5,z571]),(0,[z1,z2,z1450,z4,z5,z9]),(0,[z1,z331,z3,z24,z5,z9]),(0,[z1,z2,z3,z284,z44,z9])],[(0,[z1,z2,z3,z4,z5,z1451]),(0,[z1,z2,z3,z297,z5,z635]),(0,[z1,z2,z631,z4,z44,z9])],[(0,[z1,z2,z3,z4,z1452,z9]),(0,[z1,z2,z3,z140,z530,z9]),(0,[z1,z2,z3,z1453,z5,z9]),(0,[z1,z2,z808,z24,z5,z9]),(1,[z1,z2,z185,z44,z9])],[(0,[z675,z1,z2,z24,z5,z9]),(0,[z1,z331,z89,z4,z5,z9]),(0,[z1,z98,z3,z4,z33,z9]),(0,[z1,z2,z3,z4,z5,z1454]),(0,[z1,z2,z3,z708,z5,z9]),(0,[z1,z2,z3,z12,z300,z9]),(0,[z1,z2,z134,z4,z400,z9]),(0,[z1,z2,z119,z24,z5,z9]),(0,[z1,z341,z3,z4,z44,z9])],[(0,[z1,z2,z3,z4,z1455,z9]),(0,[z1,z2,z3,z24,z345,z9]),(0,[z1,z2,z432,z4,z5,z9]),(0,[z28,z2,z432,z4,z5,z9]),(0,[z1,z91,z3,z4,z105,z9]),(0,[z1,z2,z3,z330,z24,z9])],[(0,[z1,z1456,z2,z3,z4,z9]),(0,[z395,z2,z3,z88,z5,z9]),(0,[z59,z1,z2,z3,z4,z739])],[(0,[z216,z2,z3,z4,z5,z62]),(0,[z430,z2,z3,z12,z5,z9])],[(0,[z143,z1,z2,z24,z5,z151]),(0,[z1457,z2,z3,z4,z5,z9])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 482).take 484) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 966).take 484) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1450).take 54) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1504)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [482, 484, 484, 54] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 79).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 167).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 249).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 329).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 412).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 489).take 23).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [79, 88, 82, 80, 83, 77, 23] = true :=
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

end PEqualNP.Outside.L_meta_36390

theorem PEqualNP.Outside.L_meta_36390 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4276944608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4276944608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36390.solve