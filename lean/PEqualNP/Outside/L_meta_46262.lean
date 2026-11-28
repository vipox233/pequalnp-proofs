import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46262

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277070016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x400004540988de50#64 ++ 0x00800008a81311bc#64 ++ 0xa0a40cfc1b99fe7b#64 ++ 0xdf414819f83733fc#64 : BitVec 256),
   (0x8008313020a22ae0#64 ++ 0x8900106260414455#64 ++ 0x7958733064e63ff7#64 ++ 0xbef2b0e660c9cc7f#64 : BitVec 256),
   (0x026182c187054504#64 ++ 0x2204c305830e0a8a#64 ++ 0xf66383c38707c7ef#64 ++ 0x75ecc707870e0f8f#64 : BitVec 256),
   (0x0d82dc02f807b009#64 ++ 0x4c1b05b805f00f60#64 ++ 0xef83fc03f807f85e#64 ++ 0xf3df07f807f00ff0#64 : BitVec 256),
   (0x07f400035650000e#64 ++ 0x700fe80006aca000#64 ++ 0xfffc0003fff8003e#64 ++ 0x0ffff80007fff000#64 : BitVec 256),
   (0x07ff6ba80000000f#64 ++ 0x800ffed750000000#64 ++ 0xe7fffffc00000001#64 ++ 0xffcffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383c38707c7ef 0x75ecc707870e0f8f

def z1 : W := mkw 0x027d23a906500006 0xb004fa47520ca000 0x107c03fc07f80021 0x0c20f807f80ff000

def z2 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003fff8003e 0x0ffff80007fff000

def z3 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc00000001 0xffcffffff8000000

def z4 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03f807f85e 0xf3df07f807f00ff0

def z5 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b99fe7b 0xdf414819f83733fc

def z6 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958733064e63ff7 0xbef2b0e660c9cc7f

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x7958000064e00036 0x0ef2b00000c9c000

def z8 : W := mkw 0x87fc313376f22aee 0xf90ff86266ede455 0xfffc7333fffe3fff 0xbffff8e667fffc7f

def z9 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1918703064e63ff6 0x8a3230e060c9cc7f

def z10 : W := mkw 0x80083120202220a0 0x8900106240404441 0x5958730064660184 0x20b2b0e600c8cc03

def z11 : W := mkw 0x07fc21235650000e 0xf00ff84246aca000 0xfffc7333fff8003f 0xbffff8e667fff000

def z12 : W := mkw 0x07f582c3d755450e 0x720feb0587aeaa8a 0xffff83c3ffffc7ff 0x7fffff0787ffff8f

def z13 : W := mkw 0x426186d58f8ddf54 0x2284c30dab1f1bbe 0xf6e78fff9f9fffff 0xffedcf1fff3f3fff

def z14 : W := mkw 0x0000004107004500 0x22000000820e008a 0x10000000070007a0 0x00200000000e000f

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x70400300040607e7 0x34e0800600080c0f

def z16 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x87bffcfc00000000 0xcb0f7ff9f8000000

def z17 : W := mkw 0x8269b3f1a7a76fe4 0xab04d367e34f4edf 0xff7bf3f3e7e7ffff 0xfffef7e7e7cfcfff

def z18 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x0003fffc00000001 0xf00007fff8000000

def z19 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x0918703060e03810 0x8a1230e060c1c070

def z20 : W := mkw 0x0d82cc02d8059009 0x441b059805b00b20 0x86838c039801c008 0x410d071807300380

def z21 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x1058033004e007a1 0x0c20b0066009c00f

def z22 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0x5643830384060184 0x20ac870607080c03

def z23 : W := mkw 0x059400025050000a 0x500b280004a0a000 0x099c000078f80010 0x0a13380000f1f000

def z24 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffffffffff8003f 0xfffffffffffff000

def z25 : W := mkw 0x4000041408889a50 0x0080000828111134 0x00840c3c18983810 0x8a01081878313070

def z26 : W := mkw 0x0802dc02f807b001 0x4c1005b805f00f60 0x0803fc03f807f85e 0xf01007f807f00ff0

def z27 : W := mkw 0x8d8afd32f8a7bae9 0xcd1b15fa65f14f75 0xffdbff33fce7ffff 0xffffb7fe67f9cfff

def z28 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99f818 0xcb014819f83733f0

def z29 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x475bf30000000000 0x208eb7e600000000

def z30 : W := mkw 0x47ff6ffc0988de5f 0x808ffedff81311bc 0xe7fffffc1b99fe7b 0xffcffffff83733fc

def z31 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0303fffe07ff 0x3ffff80607fffc0f

def z32 : W := mkw 0x07ff6baa5000000f 0xc00ffed754a00000 0xeffffffff800001f 0xffdffffffff00000

def z33 : W := mkw 0x000182c081054500 0x0200030581020a8a 0xe60383c38007c7cf 0x71cc070787000f8f

def z34 : W := mkw 0xc008317421aa6ef0 0x89801062e84354dd 0x797c73fc67fe3ff7 0xbef2f8e7f8cffc7f

def z35 : W := mkw 0x826933b020a22ae4 0x8904d26760414455 0xff7bf3f064e63ff7 0xfffef7e7e0c9cc7f

def z36 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x0000733000063fc1 0xb00000e660000c7f

def z37 : W := mkw 0xc000145429aafef0 0x09800028a85355fd 0xb8a40cfc7fffffff 0xdf714819f8ffffff

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000300000607c1 0x3000000600000c0f

def z39 : W := mkw 0x4000041408889a50 0x0080000828111134 0xa0840c3c1899f85a 0xdb410818783133f0

def z40 : W := mkw 0x0000004001004400 0x0000000080020088 0xa02000c00301c66b 0x554040018006038c

def z41 : W := mkw 0x47f404175ed89a5e 0x708fe8082ebdb134 0xfffc0c3ffff8383e 0x8ffff8187ffff070

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0a40cfc1b98003b 0xdf414819f8373000

def z43 : W := mkw 0x0ff6d803f657200f 0x7c1fedb007ecae40 0x5f5bf003e4660004 0x20beb7e007c8cc00

def z44 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0xa083fc001807f85a 0xf34107f800300ff0

def z45 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xd66383c38707c18c 0x61acc707870e0f83

def z46 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x0983fc007807f850 0xf21307f800f00ff0

def z47 : W := mkw 0x8009b3f0a1a76fe0 0x8b001367e1434edf 0x0003f3f00007ffc1 0xf00007e7e0000fff

def z48 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x0003f30000000000 0x200007e600000000

def z49 : W := mkw 0x0582480000000009 0x000b049000000000 0xe783fc0000000000 0xf3cf07f800000000

def z50 : W := mkw 0x027f6ba800000007 0x8004fed750000000 0x007ffffc00000001 0xfc00fffff8000000

def z51 : W := mkw 0x0580000250000008 0x400b000004a00000 0xef800003f800001e 0x03df000007f00000

def z52 : W := mkw 0x058b6ba800000009 0x800b16d750000000 0xe783fffc00000001 0xf3cf07fff8000000

def z53 : W := mkw 0x0ff7de8af807b00f 0x4c1fefbd15f00f60 0xefa7fccff807f85e 0xf3df4ff99ff00ff0

def z54 : W := mkw 0x0261028000000004 0x0004c20500000000 0xe66383c000000001 0x75ccc70780000000

def z55 : W := mkw 0x0ff65c037e52b00f 0x7c1fecb806fca560 0xfffc7c03fff8383e 0x8ffff8f807fff070

def z56 : W := mkw 0x0000100020022000 0x0800002000400440 0x7940730064063ff7 0xb6f280e600c80c7f

def z57 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xf0e40ffc1f9fffff 0xffe1c81ff83f3fff

def z58 : W := mkw 0x027d23a800000006 0x8004fa4750000000 0x007c03fc00000001 0x0c00f807f8000000

def z59 : W := mkw 0x0275028800000006 0x0004ea0510000000 0x002400cc00000000 0x0000480198000000

def z60 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5f580003fff8003e 0x00beb00007fff000

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0a40cfc00000001 0xdf414819f8000000

def z62 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x000000001b99fe7a 0x00000000003733fc

def z63 : W := mkw 0x0d825c027802b009 0x4c1b04b804f00560 0x09807c0078003810 0x821300f800f00070

def z64 : W := mkw 0x0d82d802f0072009 0x4c1b05b005e00e40 0x4f03f003e0060004 0x209e07e007c00c00

def z65 : W := mkw 0x4000005401884e50 0x00800000a803109c 0x002400fc03980621 0x0c004801f807300c

def z66 : W := mkw 0x0000001000800a40 0x0000000020010014 0x2000003000803e73 0x9e4000006001007c

def z67 : W := mkw 0x8008b130a0a72ae0 0x8900116261414e55 0xff5bf333e4e7ffff 0xfffeb7e667c9cfff

def z68 : W := mkw 0x000b6ba800000001 0x800016d750000000 0xa0a7fffc00000001 0xff414ffff8000000

def z69 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xfffffffc64e00037 0xfffffffff8c9c000

def z70 : W := mkw 0x0ff7ce8ad805900f 0x441fef9d15b00b20 0x86a78ccf9801c008 0x410d4f199f300380

def z71 : W := mkw 0x0000800080050000 0x0000010001000a00 0xf64383038407c7ef 0x75ec870607080f8f

def z72 : W := mkw 0xc008257409a8def0 0x8180104ae81351bd 0xb0fc0ffc1ff9fffb 0xdf61f81ff83ff3ff

def z73 : W := mkw 0x026b6ba800000005 0x8004d6d750000000 0xe663fffc00000001 0xf5ccc7fff8000000

def z74 : W := mkw 0x0d8bffaaf807b009 0xcc1b17ff55f00f60 0xef83fffff807f85f 0xf3df07fffff00ff0

def z75 : W := mkw 0x0fffffa8a807b00f 0x8c1fffff51500f60 0xe7fffffc0007f841 0xffcffffff8000ff0

def z76 : W := mkw 0x0582480000000009 0x000b049000000000 0x86838c0000000000 0x410d071800000000

def z77 : W := mkw 0x0000100020022000 0x0800002000400440 0x0800000060063856 0x0010000000c00c70

def z78 : W := mkw 0x027d23e907004506 0xa204fa47d20e008a 0x107c03fc070007a1 0x0c20f807f80e000f

def z79 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5fdc0003fcf80014 0x0abfb80007f9f000

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0a400001b98003a 0x0f41480000373000

def z81 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc1b98003b 0xffcffffff8373000

def z82 : W := mkw 0x8000001000a00ae0 0x0100000020014015 0x1000000004e007a0 0x002000000009c00f

def z83 : W := mkw 0x001c212800000002 0x8000384250000000 0x001c003c00000000 0x0800380078000000

def z84 : W := mkw 0x0d825c027802b009 0x4c1b04b804f00560 0x69807c0078063856 0xb2d300f800f00c70

def z85 : W := mkw 0x0000000356500000 0x7000000006aca000 0x18000003e4600004 0x0030000007c8c000

def z86 : W := mkw 0x0ff6dc03fe57b00f 0x7c1fedb807fcaf60 0xffdbfc03fc67f85e 0xf3ffb7f807f8cff0

def z87 : W := mkw 0x400004440908d410 0x00800008881211a8 0x80a40ccc1b19c008 0x4101481998363380

def z88 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00000cfc0001fe41 0xd0000019f80003fc

def z89 : W := mkw 0x48009456f98ffe50 0x4c900128adf31ffc 0x08000003fb9ffe7e 0x0010000007f73ffc

def z90 : W := mkw 0x0000004001004400 0x0000000080020088 0xf06003c00707c7ef 0x75e0c007800e0f8f

def z91 : W := mkw 0x07ff6baa5050000f 0xd00ffed754a0a000 0xeffffffc78f80011 0xffdffffff8f1f000

def z92 : W := mkw 0x026192c1a7076504 0x2a04c325834e0eca 0xff63f3c3e707ffff 0xf7fec7e787ce0fff

def z93 : W := mkw 0x08009402f807b000 0x4c10012805f00f60 0x08000003f807f85e 0x0010000007f00ff0

def z94 : W := mkw 0x0274000106500006 0x3004e800020ca000 0x797c000067f80036 0x0ef2f80000cff000

def z95 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xcf83fc03f807c00c 0x619f07f807f00f80

def z96 : W := mkw 0x0d825c027802b009 0x4c1b04b804f00560 0xef807c03f800381e 0x83df00f807f00070

def z97 : W := mkw 0x026102c107004504 0x2204c205820e008a 0x106003c0070007a1 0x0420c007800e000f

def z98 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5f580003e4600004 0x00beb00007c8c000

def z99 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x2918703060e03e73 0x9e5230e060c1c07c

def z100 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xc7ffffcc00000000 0x618fffff98000000

def z101 : W := mkw 0x0fe3dec3ff07f50d 0x6e1fc7bd87fe0fea 0xffe3ffc3ff07ffff 0xf7ffc7ff87fe0fff

def z102 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x475bfffc00000001 0xf08eb7fff8000000

def z103 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0cfffff8003f 0xdffff819fffff000

def z104 : W := mkw 0x0d82c802d0050009 0x441b059005a00a00 0x0603800380000000 0x000c070007000000

def z105 : W := mkw 0x0fffffabfe57b00f 0xfc1fffff57fcaf60 0xfffffffffffff87f 0xfffffffffffffff0

def z106 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x7958000064e63ff6 0x0ef2b00000c9cc7f

def z107 : W := mkw 0x0000804187054500 0x22000100830e0a8a 0x100000038707c7ee 0x00200000070e0f8f

def z108 : W := mkw 0x40008454898dde50 0x00800108a9131bbc 0xe6a78cff9b9ffe7f 0xffcd4f19ff373ffc

def z109 : W := mkw 0x0d82580270022009 0x4c1b04b004e00440 0x0900700060000000 0x001200e000c00000

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000001b98003a 0x0000000000373000

def z111 : W := mkw 0x0000000356500000 0x7000000006aca000 0x18000003fff8003e 0x0030000007fff000

def z112 : W := mkw 0x0ff6dc03fe57b00f 0x7c1fedb807fcaf60 0xfffffc03fffff87e 0xfffffff807fffff0

def z113 : W := mkw 0x47f404575fd8de5e 0x708fe808aebfb1bc 0xfffc0cfffff9fe7f 0xdffff819fffff3fc

def z114 : W := mkw 0x0580100270022008 0x480b002004e00440 0xef807003f806385e 0xb3df00e007f00c70

def z115 : W := mkw 0x400004440908d410 0x00800008881211a8 0x00000ccc0001c000 0x4000001998000380

def z116 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8683fc039807f848 0xf10d07f807300ff0

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x002400fc00000001 0x0c004801f8000000

def z118 : W := mkw 0x0fffffaaf807b00f 0xcc1fffff55f00f60 0xeffffffff807f85f 0xffdffffffff00ff0

def z119 : W := mkw 0x0000000356500000 0x7000000006aca000 0xb8a40003fff8003e 0x0f71480007fff000

def z120 : W := mkw 0x400004440908d410 0x00800008881211a8 0xa0a40ccc1b19f85a 0xd3414819983633f0

def z121 : W := mkw 0x000182c081054500 0x0200030581020a8a 0x000383c00007c7c1 0x7000070780000f8f

def z122 : W := mkw 0x08009400a807b000 0x0c10012801500f60 0x000000000007f840 0x0000000000000ff0

def z123 : W := mkw 0x026182c3d7554504 0x7204c30587aeaa8a 0xfe6383c3ffffc7ff 0x75fcc70787ffff8f

def z124 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x86a7fffc00000001 0xf10d4ffff8000000

def z125 : W := mkw 0x48009456f98ffe50 0x4c900128adf31ffc 0xa8a40cfffb9ffe7f 0xdf514819fff73ffc

def z126 : W := mkw 0x4000005401884e50 0x00800000a803109c 0xa0a40cfc03980621 0xdf414819f807300c

def z127 : W := mkw 0x8269a3f187a54fe4 0xa304d347e30f4a9f 0xf67b83f387e7c7ef 0x7decf707e70fcf8f

def z128 : W := mkw 0x0008212000000000 0x8000104240000000 0xe1fc7ffc00000001 0xffc3f8fff8000000

def z129 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x862380c38301c008 0x410c470187060380

def z130 : W := mkw 0x07f58283d655010e 0x720feb0507acaa02 0x5f5b8303e4660184 0x20beb70607c8cc03

def z131 : W := mkw 0x059400025050000a 0x500b280004a0a000 0x0084000018180000 0x0001080000303000

def z132 : W := mkw 0x0000100020022000 0x0800002000400440 0x0900700060003810 0x821200e000c00070

def z133 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x000000000001fe40 0x00000000000003fc

def z134 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x7158733004e007a1 0xbee2b0e66009c00f

def z135 : W := mkw 0x400004440908d410 0x00800008881211a8 0x000000001b19c008 0x0000000000363380

def z136 : W := mkw 0x87ff7bb820a22aef 0x890ffef770414455 0xeffffffc60e03811 0xffdffffff8c1c070

def z137 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa7fcfff807f85f 0xffdf4ff9fff00ff0

def z138 : W := mkw 0x4594045659d8de5a 0x508b2808acb3b1bc 0xa9bc0cfc7bf9fe7b 0xdf537819f8f7f3fc

def z139 : W := mkw 0x0000800186050100 0x22000100030c0a02 0x1000000384060184 0x0020000007080c03

def z140 : W := mkw 0x0000800080050000 0x0000010001000a00 0x860380038001c008 0x410c070007000380

def z141 : W := mkw 0x0274000106500006 0x3004e800020ca000 0xf67c000387f8002e 0x0decf800070ff000

def z142 : W := mkw 0x8008317021a26ee0 0x89001062e04344dd 0xf97873f067e7ffff 0xfff2f0e7e0cfcfff

def z143 : W := mkw 0x87ff7bb820a22aef 0x890ffef770414455 0x7f5bf33064e63ff7 0xbefeb7e660c9cc7f

def z144 : W := mkw 0x0ff7dec3ff57f50f 0x7e1fefbd87feafea 0xffffffc3ffffffff 0xffffffff87ffffff

def z145 : W := mkw 0x0d96dc02f857b00b 0x5c1b2db805f0af60 0xef9ffc03f8fff85e 0xfbdf3ff807f1fff0

def z146 : W := mkw 0x0d809402f807b008 0x4c1b012805f00f60 0xef800003f807f85e 0x03df000007f00ff0

def z147 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0x019ffffc00000001 0xfa033ffff8000000

def z148 : W := mkw 0x0000004001004400 0x0000000080020088 0x802000c00301c008 0x4100400180060380

def z149 : W := mkw 0x07ffebe98705450f 0xa20fffd7d30e0a8a 0xe7ffffff8301c009 0xffcfffffff060380

def z150 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064663fc5 0xb0b2b0e660c8cc7f

def z151 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x0600000380000000 0x000c000007000000

def z152 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x615bfffc00000001 0xfec2b7fff8000000

def z153 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x86a400039b180008 0x010d480007363000

def z154 : W := mkw 0x027d23a800000006 0x8004fa4750000000 0x0058030000000000 0x0000b00600000000

def z155 : W := mkw 0x0fe3cec3df05d50d 0x661fc79d87be0baa 0xf6e38fc39f07c7ef 0x75edc71f873e0f8f

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0x7958030064e607f7 0x3ef2b00600c9cc0f

def z157 : W := mkw 0x80083120202220a0 0x8900106240404441 0x0918700060600000 0x001230e000c0c000

def z158 : W := mkw 0x826923f107a04fe4 0xa304d247e20f409f 0x107803f007e007a1 0x0c20f007e00fc00f

def z159 : W := mkw 0x4802dc54a98ffe51 0x0c9005b8a9531ffc 0x0003fcfc0007fe41 0xf00007f9f8000ffc

def z160 : W := mkw 0x07ff6bb800800a4f 0x800ffed770010014 0xe7fffffc00803e73 0xffcffffff801007c

def z161 : W := mkw 0x07ffebe98705450f 0xa20fffd7d30e0a8a 0xf7ffffff8707c7ef 0xffefffffff0e0f8f

def z162 : W := mkw 0x0fff7faa7802b00f 0xcc1ffeff54f00560 0xeffffffc78003811 0xffdffffff8f00070

def z163 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xf7fffffc040607e7 0xffeffffff8080c0f

def z164 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1058733004e63fe1 0xbc20b0e66009cc7f

def z165 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0x0003fc000007f840 0xf00007f800000ff0

def z166 : W := mkw 0x0000800080050000 0x0000010001000a00 0x000380000007c040 0x7000070000000f80

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0x6040030000000001 0x34c0800600000000

def z168 : W := mkw 0xc008353428aabaf0 0x8980106a68515575 0x099c7c3c78f83810 0x8a1338f878f1f070

def z169 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x1800000064e63ff6 0x0030000000c9cc7f

def z170 : W := mkw 0xc008357429aafef0 0x8980106ae85355fd 0xf9fc7ffc7fffffff 0xfff3f8fff8ffffff

def z171 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xe66383c38301c009 0x75ccc70787060380

def z172 : W := mkw 0x0000804187054500 0x22000100830e0a8a 0xb02000c38707c7ef 0x55604001870e0f8f

def z173 : W := mkw 0x07f74a8b5650000f 0x700fee9516aca000 0xffff8ccffff8003e 0x4fffff199ffff000

def z174 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1800733064e63ff7 0xb03000e660c9cc7f

def z175 : W := mkw 0x0274000106500006 0x3004e800020ca000 0x107c000007f80020 0x0c20f800000ff000

def z176 : W := mkw 0x027582c187554506 0x3204eb05830eaa8a 0xf67f83c387ffc7ef 0x7decff07870fff8f

def z177 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xff7b83c3e7e7c7ff 0x7ffef70787cfcf8f

def z178 : W := mkw 0x0000101020822a40 0x0800002020410454 0x6900703060863e77 0xbed200e060c10c7c

def z179 : W := mkw 0x0260000106000004 0x2004c000020c0000 0xf66000038700002e 0x05ecc000070e0000

def z180 : W := mkw 0x0000040008009000 0x0000000800100120 0xa0800c001801f85a 0xd3410018003003f0

def z181 : W := mkw 0x400825740988de50 0x8080104ae81311bc 0xe1fc7ffc1b99fe7b 0xffc3f8fff83733fc

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0xe60000038000000e 0x01cc000007000000

def z183 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x19fc00007ff80030 0x0e33f80000fff000

def z184 : W := mkw 0x87fc3123767220ae 0xf90ff86246ece441 0x5f587303e4660184 0x20beb0e607c8cc03

def z185 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf9fc7ffc64e63ff7 0xfff3f8fff8c9cc7f

def z186 : W := mkw 0x0d82d802f0072009 0x4c1b05b005e00e40 0xef83fc03e0060004 0xf3df07f807c00c00

def z187 : W := mkw 0x027d23a800000006 0x8004fa4750000000 0xa0fc0ffc00000001 0xdf41f81ff8000000

def z188 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x0000000000063fc0 0x0000000000000c7f

def z189 : W := mkw 0x0000100020022000 0x0800002000400440 0x6900700060063856 0xb2d200e000c00c70

def z190 : W := mkw 0x0000800080050000 0x0000010001000a00 0xe60380038007c04e 0x71cc070007000f80

def z191 : W := mkw 0x0a63dec1af07f505 0x2e14c7bd835e0fea 0xf663ffc38707ffef 0xf5ecc7ff870e0fff

def z192 : W := mkw 0x026182d187854f44 0x2204c305a30f0a9e 0xf66383f38787ffff 0xffecc707e70f0fff

def z193 : W := mkw 0x8ffefd33fef7baef 0xfd1ffdfa67fdef75 0xffffff33ffffffff 0xfffffffe67ffffff

def z194 : W := mkw 0x059400035650000a 0x700b280006aca000 0x199c0003fff8003e 0x0a33380007fff000

def z195 : W := mkw 0x059e69280000000b 0x800b3cd250000000 0x019c7c3c00000000 0x8a0338f878000000

def z196 : W := mkw 0x00009000a0072000 0x0800012001400e40 0xef03f003e007f85e 0xf3de07e007c00ff0

def z197 : W := mkw 0x07f648000000000f 0x000fec9000000000 0xe7fffc0000000000 0xffcffff800000000

def z198 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x86ff8ffc00000001 0x4d0dff1ff8000000

def z199 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x20000cfc0081fe73 0xde400019f80103fc

def z200 : W := mkw 0x0269a3e187054504 0xa204d347c30e0a8a 0xf77bf3f38707c7ef 0xffeef7e7e70e0f8f

def z201 : W := mkw 0x07f502835650000e 0x700fea0506aca000 0xffff83c3fff8003f 0x7fffff0787fff000

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000000060046 0x30c0000000000c00

def z203 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x0018003000e00000 0x080030006001c000

def z204 : W := mkw 0x400084558f8ddf50 0x22800108ab1f1bbe 0x100000039f9ffffe 0x00200000073f3fff

def z205 : W := mkw 0x0802cc0088059001 0x0410059801100b20 0x00038c000001c000 0x4000071800000380

def z206 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b19fe49 0xd1014819f83633fc

def z207 : W := mkw 0x8d8af932f0a72ae9 0xcd1b15f265e14e55 0x7f5bf333e4e63ff7 0xbefeb7e667c9cc7f

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x80a400001b180008 0x0101480000363000

def z209 : W := mkw 0x0d8afd22f807b009 0xcc1b15fa45f00f60 0xefdbff33f807f85f 0xffdfb7fe67f00ff0

def z210 : W := mkw 0x4d82dc56f98ffe59 0x4c9b05b8adf31ffc 0xefa7fcfffb9ffe7f 0xffdf4ff9fff73ffc

def z211 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xe62380c38307c04e 0x71cc470187060f80

def z212 : W := mkw 0x0008212000000000 0x8000104240000000 0x6158733000000001 0xbec2b0e660000000

def z213 : W := mkw 0x4802dc54a98ffe51 0x0c9005b8a9531ffc 0xa0a7fcfc1b9ffe7b 0xff414ff9f8373ffc

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x0918000060e00010 0x0a12300000c1c000

def z215 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x566383c3870607a5 0x24acc707870e0c0f

def z216 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x8fbc0003fbf80018 0x0b1f780007f7f000

def z217 : W := mkw 0x0580000250000008 0x400b000004a00000 0x4f000003e0000004 0x009e000007c00000

def z218 : W := mkw 0x000182c081054500 0x0200030581020a8a 0xa02383c00307c7eb 0x7540470780060f8f

def z219 : W := mkw 0x827c213106f00ae6 0xb104f842620de015 0x107c033007f807a1 0x0c20f806600ff00f

def z220 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x106003c38707c7ef 0x0420c007870e0f8f

def z221 : W := mkw 0x0001028000000000 0x0000020500000000 0x000383c000000001 0x7000070780000000

def z222 : W := mkw 0x07fe692b5650000f 0xf00ffcd256aca000 0xfffc7c3ffff8003e 0x8ffff8f87ffff000

def z223 : W := mkw 0x07e000035600000c 0x600fc00006ac0000 0xffe00003ff00003e 0x07ffc00007fe0000

def z224 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f03f003f807f85e 0x209e07e007f00ff0

def z225 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x96fc00039ff80028 0x0d2df800073ff000

def z226 : W := mkw 0x07f648035650000f 0x700fec9006aca000 0xfffffc03fff8003e 0xfffffff807fff000

def z227 : W := mkw 0x07f400025000000e 0x400fe80004a00000 0xeffc0003f800001e 0x0fdff80007f00000

def z228 : W := mkw 0x40001454298afe50 0x08800028a85315fc 0xe9a47cfc7b9ffe7f 0xffd348f9f8f73ffc

def z229 : W := mkw 0x4000041408889a50 0x0080000828111134 0xa0a40cfc18983811 0xdf414819f8313070

def z230 : W := mkw 0x0000804081054500 0x0200010081020a8a 0x000000000007c7c0 0x0000000000000f8f

def z231 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x6158733000063fc1 0xbec2b0e660000c7f

def z232 : W := mkw 0x8588313270a22ae8 0xc90b106264e14455 0xffd87333fce63fff 0xbfffb0e667f9cc7f

def z233 : W := mkw 0x0d82cc02d8059009 0x441b059805b00b20 0xa6838c039801f85a 0xd34d0718073003f0

def z234 : W := mkw 0x07f4001356d00a4e 0x700fe80026ada014 0xfffc0033fff83e7f 0x9ffff80067fff07c

def z235 : W := mkw 0x0d825c027802b009 0x4c1b04b804f00560 0xa9807c007801f85a 0xd35300f800f003f0

def z236 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0x0603800000000000 0x000c070000000000

def z237 : W := mkw 0x0582580020022009 0x080b04b000400440 0xef83fc0060063856 0xf3df07f800c00c70

def z238 : W := mkw 0x0000040008009000 0x0000000800100120 0x80800c001801c008 0x4101001800300380

def z239 : W := mkw 0x07ffebebd755450f 0xf20fffd7d7aeaa8a 0xffffffffffffc7ff 0xffffffffffffff8f

def z240 : W := mkw 0x400084558f8ddf50 0x22800108ab1f1bbe 0xb0a40cff9f9fffff 0xdf614819ff3f3fff

def z241 : W := mkw 0x0d965c027852b00b 0x5c1b2cb804f0a560 0x099c7c0078f83810 0x8a1338f800f1f070

def z242 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x6900733060063fd7 0xb2d200e660c00c7f

def z243 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x2000733000863ff3 0xbe4000e660010c7f

def z244 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99c629 0x4d014819f837338c

def z245 : W := mkw 0x059648080000000b 0x000b2c9010000000 0x00840c0c00000000 0x0001081818000000

def z246 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x564383c38407c7c5 0x70ac870787080f8f

def z247 : W := mkw 0xc7fc35777ffafefe 0xf98ff86aeefff5fd 0xfffc7fffffffffff 0xfffff8ffffffffff

def z248 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffff303fff8003e 0x2fffffe607fff000

def z249 : W := mkw 0x47ff6bfc01884e5f 0x808ffed7f803109c 0xe7fffffc03980621 0xffcffffff807300c

def z250 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x7840030064e63ff7 0x34f0800600c9cc7f

def z251 : W := mkw 0x07ff6be80100440f 0x800ffed7d0020088 0xe7fffffc0301c66b 0xffcffffff806038c

def z252 : W := mkw 0x8d8afd32f8a7bae9 0xcd1b15fa65f14f75 0xef9bfc33f8e7f85e 0xfbdf37f867f1cff0

def z253 : W := mkw 0x0002480000000001 0x0000049000000000 0x0003fc0000000000 0xf00007f800000000

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0xa08000001800001a 0x0341000000300000

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x6100700000000000 0xb2c200e000000000

def z256 : W := mkw 0x07f7cac98705450f 0x220fef95930e0a8a 0xf6e78fcf8707c7ef 0x75edcf1f9f0e0f8f

def z257 : W := mkw 0x059400000000000a 0x000b280000000000 0x019c000000000000 0x0a03380000000000

def z258 : W := mkw 0x0274000106500006 0x3004e800020ca000 0x1058000004600000 0x0020b0000008c000

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x1058000004e00020 0x0c20b0000009c000

def z261 : W := mkw 0x47ff6ffc0988de5f 0x808ffedff81311bc 0xe7fffffc0001fe41 0xffcffffff80003fc

def z262 : W := mkw 0x0008312020022000 0x8800106240400440 0x6958733060063857 0xbed2b0e660c00c70

def z263 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x0918733060e63fd1 0xba1230e660c1cc7f

def z264 : W := mkw 0x859e793820a22aeb 0x890b3cf270414455 0x79dc7f3c64e63ff7 0xbef3b8fe78c9cc7f

def z265 : W := mkw 0x4000001400880a50 0x0080000028011014 0x0004003c00980000 0x0800080078013000

def z266 : W := mkw 0x0008212000000000 0x8000104240000000 0x0000733000000001 0xb00000e660000000

def z267 : W := mkw 0x000923a800000000 0x8000124750000000 0x000003fc00000001 0x00000007f8000000

def z268 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e783c39f9fc7ff 0x7fedcf07873f3f8f

def z269 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0xf6638303870601ae 0x25ecc706070e0c03

def z270 : W := mkw 0x080014027802b000 0x4c10002804f00560 0x0800000078003810 0x0010000000f00070

def z271 : W := mkw 0x0d825c027802b009 0x4c1b04b804f00560 0xef83fc0078003810 0xf3df07f800f00070

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x6158000000000000 0x0ec2b00000000000

def z273 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0x5f5bf303e4600004 0x20beb7e607c8c000

def z274 : W := mkw 0x0000000250500000 0x5000000004a0a000 0x0800000078f80010 0x0010000000f1f000

def z275 : W := mkw 0x87ff7bb820a22aef 0x890ffef770414455 0xfffffffc64e63ff7 0xfffffffff8c9cc7f

def z276 : W := mkw 0x07f400000000000e 0x000fe80000000000 0xe7fc000000000000 0x0fcff80000000000

def z277 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa7fc03fb9ff87e 0xffdf4ff807f73ff0

def z278 : W := mkw 0xc008357429aafef0 0x8980106ae85355fd 0xa0a47ffc1b9ffffb 0xff4148fff8373fff

def z279 : W := mkw 0x0274000106500006 0x3004e800020ca000 0x0024000003180000 0x0000480000063000

def z280 : W := mkw 0x8000101376f22ae0 0x7900002026ede455 0x18000003fffe3ffe 0x0030000007fffc7f

def z281 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x675bf33000000001 0xbeceb7e660000000

def z282 : W := mkw 0x8009b3f0a1a76fe0 0x8b001367e1434edf 0x795bf3f064e7fff7 0xfef2b7e7e0c9cfff

def z283 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa02000c01b99fe7b 0x55404001803733fc

def z284 : W := mkw 0x4000005401884e50 0x00800000a803109c 0x000000fc00000601 0x00000001f800000c

def z285 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958730064e63ff6 0x20b2b0e600c9cc7f

def z286 : W := mkw 0x07f48043d755450e 0x720fe90087aeaa8a 0xfffc0003ffffc7fe 0x0ffff80007ffff8f

def z287 : W := mkw 0x400004575fd8de50 0x70800008aebfb1bc 0xb8a40cfffff9fe7f 0xdf714819fffff3fc

def z288 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x7958033064e007b7 0x0ef2b00660c9c00f

def z289 : W := mkw 0x87f4101376f22aee 0x790fe82026ede455 0xfffc0003fffe3ffe 0x0ffff80007fffc7f

def z290 : W := mkw 0x027502c107504506 0x3204ea05820ea08a 0x107c03c007f807a1 0x0c20f807800ff00f

def z291 : W := mkw 0x07f582c3d755450e 0x720feb0587aeaa8a 0xffff80c3fff9c03e 0x4fffff0187fff380

def z292 : W := mkw 0x000a692800000001 0x800014d250000000 0x00007c3c00000000 0x800000f878000000

def z293 : W := mkw 0x80083120202220a0 0x8900106240404441 0x0000730000060180 0x200000e600000c03

def z294 : W := mkw 0x426004550f88de54 0x2084c008aa1f11bc 0xf6e40cff9f99fe7f 0xdfedc819ff3f33fc

def z295 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x862383c38307c7c9 0x710c470787060f8f

def z296 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003e4600004 0x0ffff80007c8c000

def z297 : W := mkw 0x87fc213356f00aee 0xf10ff84266ade015 0xfffc0333fff807bf 0x0ffff80667fff00f

def z298 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958703064e03836 0x8ef2b0e060c9c070

def z299 : W := mkw 0x0000004001004400 0x0000000080020088 0x002000c003000621 0x040040018006000c

def z300 : W := mkw 0x0ffffbaaf007200f 0xcc1ffff755e00e40 0x4f5bf303e0060004 0x209eb7e607c00c00

def z301 : W := mkw 0x07f410037652200e 0x780fe82006eca440 0xfffc7003fffe387e 0xbffff8e007fffc70

def z302 : W := mkw 0x0274000356500006 0x7004e80006aca000 0x187c0003fff8003e 0x0c30f80007fff000

def z303 : W := mkw 0x0582480000000009 0x000b049000000000 0xe7a7fcfc00000001 0xffcf4ff9f8000000

def z304 : W := mkw 0x07ffebe88105450f 0x820fffd7d1020a8a 0xe7fffffc0007c7c1 0xffcffffff8000f8f

def z305 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0800cfc1801fe5b 0xd3410019f83003fc

def z306 : W := mkw 0x0d82d802f0072009 0x4c1b05b005e00e40 0x6f03f003e0063856 0xb2de07e007c00c70

def z307 : W := mkw 0x8d8a7d3278a2bae9 0xcd1b14fa64f14575 0x79d87f307ce63ff7 0xbef3b0fe60f9cc7f

def z308 : W := mkw 0x026bebe987054505 0xa204d7d7d30e0a8a 0xf663ffff8707c7ef 0xf5ecc7ffff0e0f8f

def z309 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1858033064e63ff7 0x0c30b00660c9cc7f

def z310 : W := mkw 0x427d23fc01884e56 0x8084fa47f803109c 0x007c03fc03980621 0x0c00f807f807300c

def z311 : W := mkw 0x0ff6cc03de55900f 0x741fed9807bcab20 0xffff8c03fff9c03e 0x4fffff1807fff380

def z312 : W := mkw 0x05808002d0050008 0x400b010005a00a00 0xef838003f807c05e 0x73df070007f00f80

def z313 : W := mkw 0x4d82dc56f98ffe59 0x4c9b05b8adf31ffc 0xef83fcfff807fe5f 0xf3df07f9fff00ffc

def z314 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xffdbfc03fce7f87e 0xffffb7f807f9cff0

def z315 : W := mkw 0x0fe3de82f807b00d 0x4c1fc7bd05f00f60 0xefe3ffc3f807f85f 0xf7dfc7ff87f00ff0

def z316 : W := mkw 0x4000004401084410 0x0080000088021088 0x002400cc03180000 0x0000480198063000

def z317 : W := mkw 0x07f400025050000e 0x500fe80004a0a000 0xeffc000078f80010 0x0fdff80000f1f000

def z318 : W := mkw 0x0fffffaaf807b00f 0xcc1fffff55f00f60 0xefdbff03f807f85e 0xf3dfb7fe07f00ff0

def z319 : W := mkw 0x0000004001004400 0x0000000080020088 0x000000c00001c641 0x500000018000038c

def z320 : W := mkw 0x0000840088059000 0x0000010801100b20 0xe6838c039807f85e 0xf3cd071807300ff0

def z321 : W := mkw 0x8269b3b1a6a72be4 0xab04d367634d4e57 0x7f5bf333e4e63ff7 0xbefeb7e667c9cc7f

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x0084000018980010 0x0a01080000313000

def z323 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0xe6e78fcc00000001 0x75cdcf1f98000000

def z324 : W := mkw 0x0582480250000009 0x400b049004a00000 0xef83fc03f800001e 0xf3df07f807f00000

def z325 : W := mkw 0x0580040258009008 0x400b000804b00120 0xef800c03f801f85e 0xd3df001807f003f0

def z326 : W := mkw 0x0580000356500008 0x700b000006aca000 0xff800003fff8003e 0x03ff000007fff000

def z327 : W := mkw 0x0008212000000000 0x8000104240000000 0x4158730000000000 0x2082b0e600000000

def z328 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8e838c03f807f85e 0x411d071807f00ff0

def z329 : W := mkw 0x059400025050000a 0x500b280004a0a000 0xef9c0003f8f8001e 0x0bdf380007f1f000

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0xa02000000300002a 0x0540400000060000

def z331 : W := mkw 0x47ff6fff5fd8de5f 0xf08ffedffebfb1bc 0xfffffffffff9fe7f 0xfffffffffffff3fc

def z332 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0x86a78ccc00000000 0x410d4f1998000000

def z333 : W := mkw 0x000102c001004500 0x020002058002008a 0x000003c000000781 0x000000078000000f

def z334 : W := mkw 0x0582c80080050009 0x000b059001000a00 0xe783fc038007c04e 0xf3cf07f807000f80

def z335 : W := mkw 0x07f400000000000e 0x000fe80000000000 0x4758000000000000 0x008eb00000000000

def z336 : W := mkw 0x827c313126f22ae6 0xb904f862624de455 0x797c733067fe3ff7 0xbef2f8e660cffc7f

def z337 : W := mkw 0x4594041658d89a5a 0x508b28082cb1b134 0x099c0c3c78f83810 0x8a13381878f1f070

def z338 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x9ea40003fff8003e 0x013d480007fff000

def z339 : W := mkw 0x0274000000000006 0x0004e80000000000 0x007c000000000000 0x0c00f80000000000

def z340 : W := mkw 0x4d82dc46f90ff419 0x4c9b05b88df21fe8 0xefa7fccffb1ff85e 0xf3df4ff99ff63ff0

def z341 : W := mkw 0x0000004001004400 0x0000000080020088 0xa0a400c01b99c67b 0x5f4148018037338c

def z342 : W := mkw 0x47f586d7dfdddf5e 0x728feb0dafbfbbbe 0xffff8fffffffffff 0xffffff1fffffffff

def z343 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7040733004063fe7 0xb4e080e660080c7f

def z344 : W := mkw 0x07ffeba98605010f 0xa20fffd7530c0a02 0x575bf30384060184 0x20aeb7e607080c03

def z345 : W := mkw 0x0000000250000000 0x4000000004a00000 0x08000003f800001e 0x0010000007f00000

def z346 : W := mkw 0x0260000106000004 0x2004c000020c0000 0xf6600303870607ef 0x35ecc006070e0c0f

def z347 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x0000703000003800 0x800000e060000070

def z348 : W := mkw 0x07fd23a80000000e 0x800ffa4750000000 0xe7fc03fc00000001 0x0fcff807f8000000

def z349 : W := mkw 0x0260000000000004 0x0004c00000000000 0xe660000000000000 0x05ccc00000000000

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0xe603800000000000 0x71cc070000000000

def z351 : W := mkw 0x47f404540988de5e 0x008fe808a81311bc 0xe7fc0cfc1b99fe7b 0xdfcff819f83733fc

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000000001c04a 0x5140000000000380

def z353 : W := mkw 0x07e34a800000000d 0x000fc69500000000 0xe7e3ffc000000001 0xf7cfc7ff80000000

def z354 : W := mkw 0x0000000356500000 0x7000000006aca000 0x000000039b180008 0x0000000007363000

def z355 : W := mkw 0x0261028000000004 0x0004c20500000000 0xf66383c0040607e7 0x75ecc70780080c0f

def z356 : W := mkw 0x800b7bb820a22ae1 0x890016f770414455 0x0003fffc00063fc1 0xf00007fff8000c7f

def z357 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xffffffffe4600005 0xffffffffffc8c000

def z358 : W := mkw 0x080bffa8a807b001 0x8c1017ff51500f60 0x0003fffc0007f841 0xf00007fff8000ff0

def z359 : W := mkw 0x0000804187054500 0x22000100830e0a8a 0x704003038707c7ef 0x34e08006070e0f8f

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x10400300040007a1 0x042080060008000f

def z361 : W := mkw 0x07f400000000000e 0x000fe80000000000 0xe7fc0cfc00000001 0xdfcff819f8000000

def z362 : W := mkw 0x0d82cc02d8059009 0x441b059805b00b20 0xef838c03f801c01e 0x43df071807f00380

def z363 : W := mkw 0x859c313270f22aea 0xd90b386264e1e455 0x79dc73307cfe3ff7 0xbef3b8e660f9fc7f

def z364 : W := mkw 0x87ff7ba8202220af 0x890ffef750404441 0x5f5bf30064660184 0x20beb7e600c8cc03

def z365 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xdffc0003ff78000c 0x01bff80007fef000

def z366 : W := mkw 0x0580000000000008 0x000b000000000000 0xe780000000000000 0x03cf000000000000

def z367 : W := mkw 0x000182c081054500 0x0200030581020a8a 0x704383c00407c7e7 0x74e0870780080f8f

def z368 : W := mkw 0x0014000000500002 0x100028000000a000 0x001c000000f80000 0x080038000001f000

def z369 : W := mkw 0x858a793020a22ae9 0x890b14f260414455 0xffdbff3064e63ff7 0xffffb7fe60c9cc7f

def z370 : W := mkw 0x4000005401884e50 0x00800000a803109c 0x202400fc03983e73 0x9e404801f807307c

def z371 : W := mkw 0x87fffbf9a7a76fef 0xab0ffff7f34f4edf 0xffffffffe7e7ffff 0xffffffffffcfcfff

def z372 : W := mkw 0x026923a000000004 0x8004d24740000000 0xe77bf3f000000001 0xffcef7e7e0000000

def z373 : W := mkw 0x08009002f0072000 0x4c10012005e00e40 0x08000003e0060004 0x0010000007c00c00

def z374 : W := mkw 0x08009402f807b000 0x4c10012805f00f60 0x69007003f807f85e 0xb2d200e007f00ff0

def z375 : W := mkw 0x08009443ff07f500 0x6e10012887fe0fea 0x18000003ff07fffe 0x0030000007fe0fff

def z376 : W := mkw 0x8008b171a7a76fe0 0xab001162e34f4edf 0x79587333e7e7ffff 0xbef2b0e667cfcfff

def z377 : W := mkw 0x8268313126a22ae4 0xa904d062624d4455 0xff787333e7e63fff 0xbffef0e667cfcc7f

def z378 : W := mkw 0x07f7cac98705450f 0x220fef95930e0a8a 0x86a78ccf8301c008 0x410d4f199f060380

def z379 : W := mkw 0x4ffffffef98ffe5f 0xcc9ffffffdf31ffc 0xeffffffffb9ffe7f 0xffdffffffff73ffc

def z380 : W := mkw 0x0000100020022000 0x0800002000400440 0x4900700060060004 0x209200e000c00c00

def z381 : W := mkw 0x0260000106000004 0x2004c000020c0000 0x8620000383000008 0x010c400007060000

def z382 : W := mkw 0x07f582c3d755450e 0x720feb0587aeaa8a 0xf6e783c39f1fc7ef 0x75edcf07873e3f8f

def z383 : W := mkw 0x0261028000000004 0x0004c20500000000 0x4643830000000000 0x208c870600000000

def z384 : W := mkw 0x426102d507884f54 0x2284c205aa0f109e 0x106403fc079807a1 0x0c20c807f80f300f

def z385 : W := mkw 0x07fc21200000000e 0x800ff84240000000 0xe7fc733000000001 0xbfcff8e660000000

def z386 : W := mkw 0x0580000250000008 0x400b000004a00000 0xffd80003fce0003e 0x0fffb00007f9c000

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000040607e6 0x0020000000080c0f

def z388 : W := mkw 0x426106d40988de54 0x0084c20da81311bc 0xe6e78ffc1b99fe7b 0xffcdcf1ff83733fc

def z389 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xf6e400039f18002e 0x05edc800073e3000

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x0024000003980020 0x0c00480000073000

def z391 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00840cfc1899fe51 0xda010819f83133fc

def z392 : W := mkw 0x0261028000000004 0x0004c20500000000 0x862380c000000000 0x410c470180000000

def z393 : W := mkw 0x059400025050000a 0x500b280004a0a000 0xa9bc00007bf8003a 0x0f53780000f7f000

def z394 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x564383038707c7ee 0x20ac8706070e0f8f

def z395 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x200000301b99fe7b 0x9e400000603733fc

def z396 : W := mkw 0x8269b3e1a72765a4 0xab04d367c34e4ecb 0xff7bf3c3e767c7ef 0x75fef7e787cecf8f

def z397 : W := mkw 0x07ff6be90700450f 0xa20ffed7d20e008a 0xf7fffffc070007a1 0xffeffffff80e000f

def z398 : W := mkw 0x0261028000000004 0x0004c20500000000 0xe6e78ffc00000001 0xffcdcf1ff8000000

def z399 : W := mkw 0x4000040408089010 0x0080000808101120 0x00840c0c18180000 0x0001081818303000

def z400 : W := mkw 0x427d27fc0988de56 0x8084fa4ff81311bc 0xa0fc0ffc1b99fe7b 0xdf41f81ff83733fc

def z401 : W := mkw 0x426186d58f8ddf54 0x2284c30dab1f1bbe 0xf66383c39f9fffff 0x75ecc707873f3fff

def z402 : W := mkw 0x0000804187054500 0x22000100830e0a8a 0x000000038301c008 0x0000000007060380

def z403 : W := mkw 0x458004565988de58 0x408b0008acb311bc 0xefa40cfffb99fe7f 0xdfdf4819fff733fc

def z404 : W := mkw 0x000182c187054500 0x22000305830e0a8a 0x100383c38707c7ef 0x70200707870e0f8f

def z405 : W := mkw 0x059e692a5050000b 0xd00b3cd254a0a000 0x099c7c3c78f80010 0x8a1338f878f1f000

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000cfc00000001 0xd0000019f8000000

def z407 : W := mkw 0x8febfff3ffa7ffed 0xef1fd7ffe7ff4fff 0xfffbfff3ffe7ffff 0xfffff7ffe7ffcfff

def z408 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63994 0xaab2b0e660c9cc73

def z409 : W := mkw 0x0000001000800a40 0x0000000020010014 0x7040033004863ff7 0xbee0800660090c7f

def z410 : W := mkw 0x4000041408889a50 0x0080000828111134 0xa0a40c3c1b98383a 0x8f41481878373070

def z411 : W := mkw 0x000182c081054500 0x0200030581020a8a 0x000380c00001c000 0x4000070180000380

def z412 : W := mkw 0x0261028106000004 0x2004c205020c0000 0xf66383c38700002f 0x75ecc707870e0000

def z413 : W := mkw 0x026102c107004504 0x2204c205820e008a 0x706003c0070607e7 0x34e0c007800e0c0f

def z414 : W := mkw 0x059e69280000000b 0x800b3cd250000000 0x0118700000000000 0x000230e000000000

def z415 : W := mkw 0x0fe3cec3df05d50d 0x661fc79d87be0baa 0x86a38cc39b01c008 0x410d471987360380

def z416 : W := mkw 0x87ff7bbb76f22aef 0xf90ffef776ede455 0xfffffffffffe3fff 0xfffffffffffffc7f

def z417 : W := mkw 0x0260800186050004 0x2004c100030c0a00 0xf66380038707c06e 0x75ecc700070e0f80

def z418 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xe7ffffff9b180009 0xffcfffffff363000

def z419 : W := mkw 0x07f400000000000e 0x000fe80000000000 0xfffc000064e00036 0x0ffff80000c9c000

def z420 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1958733064e03fb1 0x8e32b0e660c9c07f

def z421 : W := mkw 0x0000000356500000 0x7000000006aca000 0x79580003fff8003e 0x0ef2b00007fff000

def z422 : W := mkw 0x47f404475f58d41e 0x708fe8088ebeb1a8 0xfffc0ccffff9c03e 0x4ffff8199ffff380

def z423 : W := mkw 0x0d82d802f0072009 0x4c1b05b005e00e40 0xef03f003e007c04e 0x71de07e007c00f80

def z424 : W := mkw 0x0582480000000009 0x000b049000000000 0x4703f00000000000 0x208e07e000000000

def z425 : W := mkw 0x0d82dc12f887ba49 0x4c1b05b825f10f74 0xef83fc33f887fe7f 0xffdf07f867f10ffc

def z426 : W := mkw 0x0d82cc02d8059009 0x441b059805b00b20 0xe6838c039807c04e 0x71cd071807300f80

def z427 : W := mkw 0x00034a8800000001 0x0000069510000000 0x00038ccc00000000 0x4000071998000000

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000000800032 0x0e40000000010000

def z429 : W := mkw 0x0000040008009000 0x0000000800100120 0x000000001801f85a 0x00000000003003f0

def z430 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5f7c0003e7f80024 0x0cbef80007cff000

def z431 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x0800000060e03810 0x0010000000c1c070

def z432 : W := mkw 0x0000000106500000 0x30000000020ca000 0x1000000007f80020 0x00200000000ff000

def z433 : W := mkw 0x027da3e987054506 0xa204fb47d30e0a8a 0xf67f83ff8707c7ef 0x7decff07ff0e0f8f

def z434 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000003000000001 0x9e40000060000000

def z435 : W := mkw 0x0274000106500006 0x3004e800020ca000 0xb0fc00001ff8003a 0x0f61f800003ff000

def z436 : W := mkw 0x0000001000800a40 0x0000000020010014 0x0000003000800621 0x0c0000006001000c

def z437 : W := mkw 0x0000000000000000 0x0000000000000000 0x00840c3c00000000 0x8a01081878000000

def z438 : W := mkw 0x07f58283d655010e 0x720feb0507acaa02 0xffff8303fffe01be 0x2fffff0607fffc03

def z439 : W := mkw 0x059e69280000000b 0x800b3cd250000000 0xa1bc7cfc00000001 0xdf4378f9f8000000

def z440 : W := mkw 0x0000100020022000 0x0800002000400440 0x0000700000063840 0xb00000e000000c70

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x5958000064600004 0x00b2b00000c8c000

def z442 : W := mkw 0x0000040008009000 0x0000000800100120 0xa0a40cfc1801f85b 0xdf414819f83003f0

def z443 : W := mkw 0x87ff6bb800a00aef 0x810ffed770014015 0xf7fffffc04e007a1 0xffeffffff809c00f

def z444 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0xe603fc038007f84e 0xf1cc07f807000ff0

def z445 : W := mkw 0x0ff6dc02f807b00f 0x4c1fedb805f00f60 0xeffffc03f807f85e 0xffdffff807f00ff0

def z446 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00000cfc1b99fe7b 0xd0000019f83733fc

def z447 : W := mkw 0x07ff6ba90650000f 0xb00ffed7520ca000 0xf7fffffc07f80021 0xffeffffff80ff000

def z448 : W := mkw 0x00008043d7554500 0x7200010087aeaa8a 0x18000003ffffc7fe 0x0030000007ffff8f

def z449 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xffc3ff03fc07ffff 0xf7ff87fe07f80fff

def z450 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f03fc03e007f844 0xf09e07f807c00ff0

def z451 : W := mkw 0x4000041408889a50 0x0080000828111134 0x0000000018983810 0x0000000000313070

def z452 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc0001fe41 0xdf414819f80003fc

def z453 : W := mkw 0x07f582c18705450e 0x220feb05830e0a8a 0xf7ff83c38707c7ef 0x7fefff07870e0f8f

def z454 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xff780003e760002e 0x05fef00007cec000

def z455 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x477ff3fc00000001 0x2c8effe7f8000000

def z456 : W := mkw 0x07ffeba88005000f 0x800fffd751000a00 0xe7ffffff8007c04f 0xffcfffffff000f80

def z457 : W := mkw 0x0000001000800a40 0x0000000020010014 0x0000003000803810 0x8a00000060010070

def z458 : W := mkw 0xc008353428aabaf0 0x8980106a68515575 0x79dc7f3c7cfe3ff7 0xbef3b8fe78f9fc7f

def z459 : W := mkw 0x0d83dec2f907f509 0x4e1b07bd85f20fea 0xef83ffc3f807ffdf 0xf3df07ff87f00fff

def z460 : W := mkw 0x026102c107004504 0x2204c205820e008a 0x002000c003000000 0x0000400180060000

def z461 : W := mkw 0x0260000106000004 0x2004c000020c0000 0xff780003e7e0003e 0x0ffef00007cfc000

def z462 : W := mkw 0x4000041408889a50 0x0080000828111134 0x20840c3c18983e73 0x9e4108187831307c

def z463 : W := mkw 0x0d82dc00a807b009 0x0c1b05b801500f60 0xe783fc000007f840 0xf3cf07f800000ff0

def z464 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x002400fc1b99fe7b 0x0c004801f83733fc

def z465 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0xf64383038407c1ce 0x71ec870607080f83

def z466 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x6958733060e03811 0xbed2b0e660c1c070

def z467 : W := mkw 0x45824c540988de59 0x008b0498a81311bc 0xe7a7fcfc1b99fe7b 0xffcf4ff9f83733fc

def z468 : W := mkw 0x459e6d3c08889a5b 0x808b3cda78111134 0x019c7c3c18983810 0x8a0338f878313070

def z469 : W := mkw 0x8d8a7d3278a2bae9 0xcd1b14fa64f14575 0x09987c3078e03810 0x8a1330f860f1c070

def z470 : W := mkw 0x0000000000000000 0x0000000000000000 0xf9fc00007ff8003e 0x0ff3f80000fff000

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x7040000004000026 0x04e0800000080000

def z472 : W := mkw 0x0260804187054504 0x2204c100830e0a8a 0xf66000038707c7ee 0x05ecc000070e0f8f

def z473 : W := mkw 0x08009402f807b000 0x4c10012805f00f60 0xa8800c03f807f85e 0xd351001807f00ff0

def z474 : W := mkw 0x47ffeffd8f8ddf5f 0xa28fffdffb1f1bbe 0xf7ffffff9f9fffff 0xffefffffff3f3fff

def z475 : W := mkw 0x459e6d7c0988de5b 0x808b3cdaf81311bc 0xa1bc7cfc1b99fe7b 0xdf4378f9f83733fc

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000000000663 0x144000000000000c

def z477 : W := mkw 0x80083120202220a0 0x8900106240404441 0x79587300646639d6 0xb2f2b0e600c8cc73

def z478 : W := mkw 0x4fe3ded7ff8fff5d 0x6e9fc7bdafff1ffe 0xffe7ffffff9fffff 0xffffcfffffff3fff

def z479 : W := mkw 0x4d825c56798afe59 0x4c9b04b8acf315fc 0xa9a47cfc7b99fe7b 0xdf5348f9f8f733fc

def z480 : W := mkw 0x0d82dc42f907f409 0x4c1b05b885f20fe8 0xefa3fcc3fb07fe7f 0xf7df47f987f60ffc

def z481 : W := mkw 0x400b6ffc0988de51 0x808016dff81311bc 0x0003fffc0001fe41 0xf00007fff80003fc

def z482 : W := mkw 0x87fdb3f3f7f76fee 0xfb0ffb67e7efeedf 0xfffff3f3ffffffff 0xffffffe7e7ffffff

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0800c0000000000 0xd341001800000000

def z484 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x47dfff3c00000000 0xaa8fbffe78000000

def z485 : W := mkw 0x0a6196c3ff07f504 0x6e14c32d87fe0fea 0xfe6383c3ff07ffff 0x75fcc70787fe0fff

def z486 : W := mkw 0x07f502c35750450e 0x720fea0586aea08a 0xfffc03c3fff807bf 0x0ffff80787fff00f

def z487 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xf9fc0cfc7ff9fe7f 0xdff3f819f8fff3fc

def z488 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e78fff8707c7ef 0xffedcf1fff0e0f8f

def z489 : W := mkw 0x400186d4898ddf50 0x0280030da9131bbe 0x00038ffc0007ffc1 0xf000071ff8000fff

def z490 : W := mkw 0x87fc313376f22aee 0xf90ff86266ede455 0xfffc7033fff8383e 0x8ffff8e067fff070

def z491 : W := mkw 0x0fffffebff07f50f 0xee1fffffd7fe0fea 0xffffffffff07ffff 0xfffffffffffe0fff

def z492 : W := mkw 0x426106d50f88df54 0x2284c20daa1f11be 0xb0e40ffc1f99fffb 0xdf61c81ff83f33ff

def z493 : W := mkw 0x0261828080050004 0x0004c30501000a00 0xe66383c38007c04f 0x75ccc70787000f80

def z494 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0200cfc0301fe6b 0xd5404019f80603fc

def z495 : W := mkw 0x827d33b820a22ae6 0x8904fa6770414455 0x797c73fc64e63ff7 0xbef2f8e7f8c9cc7f

def z496 : W := mkw 0x0ff49403fe57b00e 0x7c1fe92807fcaf60 0xfffc0003fffff87e 0x0ffff80007fffff0

def z497 : W := mkw 0x0000001000800a40 0x0000000020010014 0x0000000000803e72 0x000000000001007c

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0a4000000000000 0x0f41480000000000

def z499 : W := mkw 0x87fc313376f22aee 0xf90ff86266ede455 0x7f587333e4e63ff7 0xbefeb0e667c9cc7f

def z500 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f83fc03f8063814 0xa29f07f807f00c70

def z501 : W := mkw 0x07f582c3d755450e 0x720feb0587aeaa8a 0xff7b83c3e767c7ef 0x75fef70787cecf8f

def z502 : W := mkw 0x8269b3f1a7a76fe4 0xab04d367e34f4edf 0xf663f3f38707ffef 0xf5ecc7e7e70e0fff

def z503 : W := mkw 0x0000001000800a40 0x0000000020010014 0xa0a40cfc00803e73 0xdf414819f801007c

def z504 : W := mkw 0x0fe3dac3f707650d 0x6e1fc7b587ee0eca 0xff63f3c3e707c7ef 0x75fec7e787ce0f8f

def z505 : W := mkw 0x027d23a800000006 0x8004fa4750000000 0x617c73fc00000001 0xbec2f8e7f8000000

def z506 : W := mkw 0x0000000106000000 0x20000000020c0000 0x100000038700002e 0x00200000070e0000

def z507 : W := mkw 0x0260000356500004 0x7004c00006aca000 0xfe600003fff8003e 0x05fcc00007fff000

def z508 : W := mkw 0x0008212000000000 0x8000104240000000 0x0058033000000001 0x0c00b00660000000

def z509 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x0000033000000781 0x000000066000000f

def z510 : W := mkw 0x07ffebe98705450f 0xa20fffd7d30e0a8a 0xf77bf3c38707c7ef 0x75eef7e7870e0f8f

def z511 : W := mkw 0x058a692000000009 0x800b14d240000000 0xe7dbff3000000001 0xffcfb7fe60000000

def z512 : W := mkw 0x8269b3a1a62721a4 0xab04d367434c4e43 0x5f5bf303e4660184 0x20beb7e607c8cc03

def z513 : W := mkw 0x0802d800a0072001 0x0c1005b001400e40 0x0003f00000060000 0x200007e000000c00

def z514 : W := mkw 0x400b6ffc0988de51 0x808016dff81311bc 0xa0a7fffc1b99fe7b 0xff414ffff83733fc

def z515 : W := mkw 0x88009412f8a7bae0 0x4d10012825f14f75 0x18000003fce7fffe 0x0030000007f9cfff

def z516 : W := mkw 0x07f502800000000e 0x000fea0500000000 0xe7ff83c000000001 0x7fcfff0780000000

def z517 : W := mkw 0x07f582c3d755450e 0x720feb0587aeaa8a 0x86a780c39b19c008 0x410d4f0187363380

def z518 : W := mkw 0x800b7bb820a22ae1 0x890016f770414455 0x795bfffc64e63ff7 0xfef2b7fff8c9cc7f

def z519 : W := mkw 0x05824c0008009009 0x000b049800100120 0xe783fc001801f85a 0xf3cf07f8003003f0

def z520 : W := mkw 0x87fc313020a22aee 0x890ff86260414455 0xfffc733064e63ff7 0xbffff8e660c9cc7f

def z521 : W := mkw 0x07ff6fa80800900f 0x800ffedf50100120 0xe7fffffc1801f85b 0xffcffffff83003f0

def z522 : W := mkw 0x0000804187054500 0x22000100830e0a8a 0xf60380038707c7ee 0x71ec0700070e0f8f

def z523 : W := mkw 0x0260000106000004 0x2004c000020c0000 0x5640000384000004 0x00ac800007080000

def z524 : W := mkw 0x0000800080050000 0x0000010001000a00 0x4603800380060004 0x208c070007000c00

def z525 : W := mkw 0x400186d4898ddf50 0x0280030da9131bbe 0xa0a78ffc1b9ffffb 0xff414f1ff8373fff

def z526 : W := mkw 0x0000800080050000 0x0000010001000a00 0x000000038007c04e 0x0000000007000f80

def z527 : W := mkw 0x0580000250000008 0x400b000004a00000 0x8680000398000008 0x010d000007300000

def z528 : W := mkw 0x47f404575fd8de5e 0x708fe808aebfb1bc 0xfffc0003fff9fe7e 0x0ffff80007fff3fc

def z529 : W := mkw 0x0ff6d803f657200f 0x7c1fedb007ecae40 0xfffff003fffe003e 0x2fffffe007fffc00

def z530 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xa6a400039b98003a 0x0f4d480007373000

def z531 : W := mkw 0x07fe69280000000f 0x800ffcd250000000 0xe7fc7c3c00000000 0x8fcff8f878000000

def z532 : W := mkw 0x826933f127a26fe4 0xab04d267e24f44df 0x797873f067e63ff7 0xbef2f0e7e0cfcc7f

def z533 : W := mkw 0x8fffffbaf8a7baef 0xcd1fffff75f14f75 0xfffffffffce7ffff 0xfffffffffff9cfff

def z534 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x966383c38701c7a9 0x452cc707870e038f

def z535 : W := mkw 0x07f74a8b5650000f 0x700fee9516aca000 0x86a78ccf9b180008 0x410d4f199f363000

def z536 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0x6903fc006007f856 0xf2d207f800c00ff0

def z537 : W := mkw 0x4000005401884e50 0x00800000a803109c 0x0000000003980620 0x000000000007300c

def z538 : W := mkw 0xc008357429aafef0 0x8980106ae85355fd 0x79587ffc64e7fff7 0xfef2b0fff8c9cfff

def z539 : W := mkw 0x8808b532f8a7bae0 0xcd10116a65f14f75 0x79587333fce7ffff 0xbef2b0e667f9cfff

def z540 : W := mkw 0x0260004107004404 0x2004c000820e0088 0xf66000c38701c66f 0x55ecc001870e038c

def z541 : W := mkw 0x0260000106000004 0x2004c000020c0000 0xf6e400039f98003e 0x0fedc800073f3000

def z542 : W := mkw 0x0000040008009000 0x0000000800100120 0x00800c0018003810 0x8201001800300070

def z543 : W := mkw 0x07f400000000000e 0x000fe80000000000 0x86a4000000000000 0x010d480000000000

def z544 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x106383c00707c7e1 0x7420c707800e0f8f

def z545 : W := mkw 0xc008357429aafef0 0x8980106ae85355fd 0x00007ffc0007ffc1 0xf00000fff8000fff

def z546 : W := mkw 0x426186c58f0dd514 0x2284c30d8b1e1baa 0xf6e78fcf9f1fc7ef 0x75edcf1f9f3e3f8f

def z547 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x3800003064e63ff7 0x9e70000060c9cc7f

def z548 : W := mkw 0x827d23b800a00ae6 0x8104fa4770014015 0x107c03fc04e007a1 0x0c20f807f809c00f

def z549 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xe7fc00039b180008 0x0fcff80007363000

def z550 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf9fc73307ffe3fff 0xbff3f8e660fffc7f

def z551 : W := mkw 0x0d9e7d2a7802b00b 0xcc1b3cfa54f00560 0x099c7c3c78003810 0x8a1338f878f00070

def z552 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0800c001b99fe7a 0xd3410018003733fc

def z553 : W := mkw 0x4d82cc56d98dde59 0x449b0598adb31bbc 0xa6a78cff9b99fe7b 0xdf4d4f19ff3733fc

def z554 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xf7ffffff8700002f 0xffefffffff0e0000

def z555 : W := mkw 0x026102c107004504 0x2204c205820e008a 0xf66003c3870007af 0x05ecc007870e000f

def z556 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x962380c38707c7ee 0x412c4701870e0f8f

def z557 : W := mkw 0x8d82dc12f8a7bae9 0x4d1b05b825f14f75 0xff83fc03fce7fffe 0xf3ff07f807f9cfff

def z558 : W := mkw 0xc000145429aafef0 0x09800028a85355fd 0x180000007ffffffe 0x0030000000ffffff

def z559 : W := mkw 0x87ff7ba8202220af 0x890ffef750404441 0xfffffffc64660185 0xfffffffff8c8cc03

def z560 : W := mkw 0x400004440908d410 0x00800008881211a8 0xa0a40ccc1b99c03a 0x4f41481998373380

def z561 : W := mkw 0x4d82dc56f98ffe59 0x4c9b05b8adf31ffc 0xef83fc03fb9ffe7e 0xf3df07f807f73ffc

def z562 : W := mkw 0x000004400900d400 0x00000008801201a8 0xa0a00cc01b01fe7b 0xd7414019803603fc

def z563 : W := mkw 0x0fe3dec3ff07f50d 0x6e1fc7bd87fe0fea 0xefa3fcc3fb07f85e 0xf3df47f987f60ff0

def z564 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0x76438303840607e7 0x34ec870607080c0f

def z565 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a400001b99fe7a 0x0f414800003733fc

def z566 : W := mkw 0x08009403fe57b000 0x7c10012807fcaf60 0x18000003fffff87e 0x0030000007fffff0

def z567 : W := mkw 0x0580000250000008 0x400b000004a00000 0xefa40003fb98003e 0x0fdf480007f73000

def z568 : W := mkw 0x87fc3123767220ae 0xf90ff86246ece441 0xfffc7303fffe01be 0x2ffff8e607fffc03

def z569 : W := mkw 0x000bebe881054501 0x820017d7d1020a8a 0x0003fffc0007c7c1 0xf00007fff8000f8f

def z570 : W := mkw 0x4000005401884e50 0x00800000a803109c 0xa02400fc0399c66b 0x5d404801f807338c

def z571 : W := mkw 0x026102c001004404 0x0004c20580020088 0xe66383c00301c66b 0x75ccc7078006038c

def z572 : W := mkw 0x8d8af922f02720a9 0xcd1b15f245e04e41 0x5f5bf303e4660184 0x20beb7e607c8cc03

def z573 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00240cfc0399fe61 0xdc004819f80733fc

def z574 : W := mkw 0x859c313270f22aea 0xd90b386264e1e455 0x099c703078f83810 0x8a1338e060f1f070

def z575 : W := mkw 0xc7ff7ffc29aafeff 0x898ffefff85355fd 0xfffffffc7fffffff 0xfffffffff8ffffff

def z576 : W := mkw 0x027d23a800000006 0x8004fa4750000000 0xe67f83fc00000001 0x7dccff07f8000000

def z577 : W := mkw 0x80001000202220a0 0x0900002000404441 0x1800000064660184 0x0030000000c8cc03

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000064e00036 0x0030000000c9c000

def z579 : W := mkw 0x426182d5878d4f54 0x2284c305ab0f1a9e 0xf66783ff879fc7ef 0x7deccf07ff0f3f8f

def z580 : W := mkw 0x07ffeba98605010f 0xa20fffd7530c0a02 0xf7ffffff84060185 0xffefffffff080c03

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x5040030004060184 0x20a0800600080c03

def z582 : W := mkw 0xc008357429aafef0 0x8980106ae85355fd 0x795873307fffffff 0xbef2b0e660ffffff

def z583 : W := mkw 0x4d82cc46d90dd419 0x449b05988db21ba8 0x86a78ccf9b19c008 0x410d4f199f363380

def z584 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe77bf3c000000001 0x75cef7e780000000

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x6900000060000016 0x02d2000000c00000

def z586 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fff30000000000 0x2fcfffe600000000

def z587 : W := mkw 0x87ff7bb820a22aef 0x890ffef770414455 0xe7fffffc00063fc1 0xffcffffff8000c7f

def z588 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e607a5 0x2cb2b0e660c9cc0f

def z589 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8f83fc03f801f818 0xc31f07f807f003f0

def z590 : W := mkw 0x47f404575fd8de5e 0x708fe808aebfb1bc 0xa6a40cff9b99fe7b 0xdf4d4819ff3733fc

def z591 : W := mkw 0x4274005507d84e56 0x3084e800aa0fb09c 0x107c00fc07f80621 0x0c20f801f80ff00c

def z592 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0xf66383c384060185 0x75ecc70787080c03

def z593 : W := mkw 0x400004440908d410 0x00800008881211a8 0xa0a40cfc1b19c009 0xdf414819f8363380

def z594 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x6918703060e63856 0xbad230e060c1cc70

def z595 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0x0603800380000000 0x000c070007000000

def z596 : W := mkw 0x0000004001004400 0x0000000080020088 0x000000000301c66a 0x000000000006038c

def z597 : W := mkw 0x0008213000800a40 0x8000104260010014 0x6158733000803e73 0xbec2b0e66001007c

def z598 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40ccc1b99fe7a 0x41014819983733fc

def z599 : W := mkw 0x80083120202220a0 0x8900106240404441 0x7958733064660185 0xbef2b0e660c8cc03

def z600 : W := mkw 0x059e69280000000b 0x800b3cd250000000 0x61dc7f3c00000001 0xbec3b8fe78000000

def z601 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7dbff0000000000 0xf3cfb7fe00000000

def z602 : W := mkw 0x0000004001004400 0x0000000080020088 0xa0a40cfc0301c66b 0xdf414819f806038c

def z603 : W := mkw 0x0ff6dc03fe57b00f 0x7c1fedb807fcaf60 0xefa7fc03fb1ff85e 0xf3df4ff807f63ff0

def z604 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x01fc7ffc00000001 0x8e03f8fff8000000

def z605 : W := mkw 0xcd8afd76f9affef9 0xcd9b15faedf35ffd 0xffffffffffffffff 0xffffffffffffffff

def z606 : W := mkw 0x0d82dc03fe57b009 0x7c1b05b807fcaf60 0xff83fc03fffff87e 0xf3ff07f807fffff0

def z607 : W := mkw 0x4d825c16788aba59 0x4c9b04b82cf11574 0x09847c3c78983810 0x8a1308f878f13070

def z608 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66380c38701c02e 0x45ecc701870e0380

def z609 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xffd80003fc60001e 0x03ffb00007f8c000

def z610 : W := mkw 0x0d824c0258009009 0x441b049804b00120 0x00800c0018000000 0x0001001800300000

def z611 : W := mkw 0x47ff6fbc08889a5f 0x808ffedf78111134 0xe7fffffc18983811 0xffcffffff8313070

def z612 : W := mkw 0x0ff6cc03de55900f 0x741fed9807bcab20 0x86a78c039b19c008 0x410d4f1807363380

def z613 : W := mkw 0x07f404035e50900e 0x700fe80806bca120 0xfffc0c03fff9f87e 0xdffff81807fff3f0

def z614 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xa62380c38301c66b 0x554c47018706038c

def z615 : W := mkw 0x0fffefaad805900f 0xc41fffdf55b00b20 0xe7ffffff9801c009 0xffcfffffff300380

def z616 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x09807c03f807f85e 0x821300f807f00ff0

def z617 : W := mkw 0x0000005001804e40 0x00000000a003009c 0xa02000f00381fe7b 0xdf404001e00703fc

def z618 : W := mkw 0x07e182c3d705450c 0x620fc30587ae0a8a 0xffe383c3ff07c7ff 0x77ffc70787fe0f8f

def z619 : W := mkw 0x0000040008009000 0x0000000800100120 0x00000c000001f840 0xd0000018000003f0

def z620 : W := mkw 0x47f404475f58d41e 0x708fe8088ebeb1a8 0x86a40ccf9b19c008 0x410d48199f363380

def z621 : W := mkw 0x0260000106000004 0x2004c000020c0000 0x1060000007000020 0x0420c000000e0000

def z622 : W := mkw 0x0d82d802f0072009 0x4c1b05b005e00e40 0xef83f003f806001e 0x23df07e007f00c00

def z623 : W := mkw 0x08025c002802b001 0x0c1004b800500560 0x00007c0000003800 0x800000f800000070

def z624 : W := mkw 0x4000041408889a50 0x0080000828111134 0x00000c3c00003800 0x8000001878000070

def z625 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0xe7ff8ccc00000000 0x4fcfff1998000000

def z626 : W := mkw 0xc008217401a84ef0 0x81801042e803509d 0x107c03fc07f807a1 0x0c20f807f80ff00f

def z627 : W := mkw 0x07f400010600000e 0x200fe800020c0000 0xf7fc00038700002e 0x0feff800070e0000

def z628 : W := mkw 0x859e793820a22aeb 0x890b3cf270414455 0x099c7c3c60e03810 0x8a1338f878c1c070

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000000003852 0x9240000000000070

def z630 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xefa40003fb18001e 0x03df480007f63000

def z631 : W := mkw 0x0580000250000008 0x400b000004a00000 0x0980000078000010 0x0213000000f00000

def z632 : W := mkw 0x47f74edc0988de5f 0x008fee9db81311bc 0xa6a78cfc1b99fe7b 0xdf4d4f19f83733fc

def z633 : W := mkw 0x000014002802b000 0x0800002800500560 0xe9807c007807f85e 0xf3d300f800f00ff0

def z634 : W := mkw 0x0fe3da83f607210d 0x6e1fc7b507ec0e42 0x5f43f303e4060184 0x20be87e607c80c03

def z635 : W := mkw 0x80083120202220a0 0x8900106240404441 0x79587300646607e7 0x34f2b0e600c8cc0f

def z636 : W := mkw 0x0000001000800a40 0x0000000020010014 0x0000003000003e41 0x900000006000007c

def z637 : W := mkw 0x07ff7ba82002200f 0x880ffef750400440 0xeffffffc60063857 0xffdffffff8c00c70

def z638 : W := mkw 0x059e69280000000b 0x800b3cd250000000 0xe79ffc3c00000000 0xfbcf3ff878000000

def z639 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0xe7a7fccc00000000 0xf3cf4ff998000000

def z640 : W := mkw 0x4d82dc16f88fba59 0x4c9b05b82df11f74 0xef87fc3ff89ff85e 0xfbdf0ff87ff13ff0

def z641 : W := mkw 0x0000040008009000 0x0000000800100120 0xa0a40c001b99f87a 0xdf414818003733f0

def z642 : W := mkw 0x880afd30a8a7bae1 0x8d1015fa61514f75 0x795bff3064e7fff7 0xfef2b7fe60c9cfff

def z643 : W := mkw 0x0d82dc43ff07f509 0x6e1b05b887fe0fea 0xff83fc03ff07fffe 0xf3ff07f807fe0fff

def z644 : W := mkw 0x07f48003d655000e 0x700fe90007acaa00 0xffff8003ffffc07e 0x7fffff0007ffff80

def z645 : W := mkw 0x0008212000000000 0x8000104240000000 0x7958733064e00037 0xbef2b0e660c9c000

def z646 : W := mkw 0x0000100020022000 0x0800002000400440 0x7958700064e63876 0xbef2b0e000c9cc70

def z647 : W := mkw 0x07e3cac18705450d 0x220fc795830e0a8a 0xf7e3ffc38707c7ef 0xf7efc7ff870e0f8f

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0xa02000c000000001 0x5540400180000000

def z649 : W := mkw 0x07f400000000000e 0x000fe80000000000 0xe7fc00001b98003a 0x0fcff80000373000

def z650 : W := mkw 0x880afd30a8a7bae1 0x8d1015fa61514f75 0x0003ff300007ffc1 0xf00007fe60000fff

def z651 : W := mkw 0x0d9efd2af807b00b 0xcc1b3dfa55f00f60 0xef9ffc3ff807f85e 0xfbdf3ff87ff00ff0

def z652 : W := mkw 0x0fe3de83fe07b10d 0x6e1fc7bd07fc0f62 0xffc3ff03fc07f9de 0xf3ff87fe07f80ff3

def z653 : W := mkw 0x059400025050000a 0x500b280004a0a000 0x79dc00007cf80036 0x0ef3b80000f9f000

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x80a40ccc00000000 0x4101481998000000

def z655 : W := mkw 0x826192d1a7a76fe4 0x2b04c325a34f4edf 0xfe6383c3e7e7ffff 0x75fcc70787cfcfff

def z656 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x3058033004e03ff3 0x9e60b0066009c07f

def z657 : W := mkw 0x426186d58f8ddf54 0x2284c30dab1f1bbe 0xa6a78cff9b99fe7b 0xdf4d4f19ff3733fc

def z658 : W := mkw 0x4000005401884e50 0x00800000a803109c 0xa0a400fc1b98063b 0x0f414801f837300c

def z659 : W := mkw 0x0000001000800a40 0x0000000020010014 0xa0a400301b983e7b 0x9f4148006037307c

def z660 : W := mkw 0x026186c18f05d504 0x2204c30d831e0baa 0xf6e38fc39f07ffff 0xf7edc71f873e0fff

def z661 : W := mkw 0x0001828080050100 0x0200030501000a02 0x0003830000060180 0x2000070600000c03

def z662 : W := mkw 0x0582480000000009 0x000b049000000000 0x01807c0000000000 0x820300f800000000

def z663 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00a40cfc1b983e31 0x8e014819f837307c

def z664 : W := mkw 0x0261028106000104 0x2204c205020c0002 0x1040030004000180 0x0020800600080003

def z665 : W := mkw 0x8008353028a2bae0 0x8900106a60514575 0xf9d87f307ce7ffff 0xfff3b0fe60f9cfff

def z666 : W := mkw 0x0008212000000000 0x8000104240000000 0x71587330040607e7 0xbee2b0e660080c0f

def z667 : W := mkw 0x0803dec0a907f501 0x0e1007bd81520fea 0x0003ffc00007ffc1 0xf00007ff80000fff

def z668 : W := mkw 0x4ff6dc57ffdffe5f 0x7c9fedb8afffbffc 0xfffffcfffffffe7f 0xfffffff9fffffffc

def z669 : W := mkw 0x47f74ecc0908d41f 0x008fee9d981211a8 0x86a78ccc1b19c008 0x410d4f1998363380

def z670 : W := mkw 0x0fe2dc03fe07b00d 0x6c1fc5b807fc0f60 0xffe3fc03ff07f87e 0xf7ffc7f807fe0ff0

def z671 : W := mkw 0x8008213000a00ae0 0x8100104260014015 0x7058033004e607e7 0x3ce0b0066009cc0f

def z672 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x7f580003e4e00036 0x0efeb00007c9c000

def z673 : W := mkw 0x8000101020a22ae0 0x0900002020414455 0x7900700064e63ff6 0xb2f200e000c9cc7f

def z674 : W := mkw 0x059400025050000a 0x500b280004a0a000 0x0918000060600000 0x0012300000c0c000

def z675 : W := mkw 0x07fd23ab5650000e 0xf00ffa4756aca000 0xfffc03fffff8003f 0x0ffff807fffff000

def z676 : W := mkw 0x08009402f807b000 0x4c10012805f00f60 0xee038003f807f85e 0x71dc070007f00ff0

def z677 : W := mkw 0x08008402d8059000 0x4410010805b00b20 0x000000039801c008 0x0000000007300380

def z678 : W := mkw 0x0d82cc02d8059009 0x441b059805b00b20 0xe783fc039801c008 0xf3cf07f807300380

def z679 : W := mkw 0x8d8afd22f827b0a9 0xcd1b15fa45f04f61 0xffdbff03fc67f9de 0xf3ffb7fe07f8cff3

def z680 : W := mkw 0x427404550fd8de56 0x3084e808aa1fb1bc 0xb0fc0cfc1ff9fe7b 0xdf61f819f83ff3fc

def z681 : W := mkw 0x026102c107004504 0x2204c205820e008a 0xf66383c0070007a1 0x75ecc707800e000f

def z682 : W := mkw 0x0000041008809a40 0x0000000820110134 0xa0800c301881fe7b 0xdf410018603103fc

def z683 : W := mkw 0x400004440908d410 0x00800008881211a8 0xa0a40ccc1b19c66b 0x554148199836338c

def z684 : W := mkw 0x8008313376f22ae0 0xf900106266ede455 0x79587333fffe3fff 0xbef2b0e667fffc7f

def z685 : W := mkw 0x80083120202220a0 0x8900106240404441 0x7958730064e601b6 0x2ef2b0e600c9cc03

def z686 : W := mkw 0x0000804081054400 0x0000010081020a88 0xe62380c38307c66f 0x75cc470187060f8c

def z687 : W := mkw 0x026102c107004504 0x2204c205820e008a 0xb06003c00701c7eb 0x5560c007800e038f

def z688 : W := mkw 0x0261028000000004 0x0004c20500000000 0x006003c000000001 0x0400c00780000000

def z689 : W := mkw 0x07f400435750440e 0x700fe80086aea088 0xfffc00c3fff9c67f 0x5ffff80187fff38c

def z690 : W := mkw 0x80082120002000a0 0x8100104240004001 0x1058030004600180 0x0020b0060008c003

def z691 : W := mkw 0x426186c58f0dd514 0x2284c30d8b1e1baa 0x86a78ccf9b19c008 0x410d4f199f363380

def z692 : W := mkw 0xc269b7f5afaffff4 0xab84d36feb5f5fff 0xffffffffffffffff 0xffffffffffffffff

def z693 : W := mkw 0xc008357429aafef0 0x8980106ae85355fd 0xa9bc7cfc7bf9fe7b 0xdf5378f9f8f7f3fc

def z694 : W := mkw 0x47ff6fec0908d41f 0x808ffedfd81211a8 0xe7fffffc1b19c009 0xffcffffff8363380

def z695 : W := mkw 0x0000001000800a40 0x0000000020010014 0x7958003064e03e77 0x9ef2b00060c9c07c

def z696 : W := mkw 0x07f400010650000e 0x300fe800020ca000 0xf7fc000007f80020 0x0feff800000ff000

def z697 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0xa6a78cfc00000001 0xdf4d4f19f8000000

def z698 : W := mkw 0x026182c081054504 0x0204c30581020a8a 0xe66383c00007c7c1 0x75ccc70780000f8f

def z699 : W := mkw 0x400004575fd8de50 0x70800008aebfb1bc 0x18000003fff9fe7e 0x0030000007fff3fc

def z700 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00840c3c1b99fe7a 0x8a010818783733fc

def z701 : W := mkw 0x0008212000000000 0x8000104240000000 0x0118703000000000 0x8a0230e060000000

def z702 : W := mkw 0x80009051a7a76fe0 0x2b000120a34f4edf 0x18000003e7e7fffe 0x0030000007cfcfff

def z703 : W := mkw 0x8d8afd32f8a7bae9 0xcd1b15fa65f14f75 0xef83ff33f807ffdf 0xf3df07fe67f00fff

def z704 : W := mkw 0x47f4005757d84e5e 0x708fe800aeafb09c 0xfffc00fffff8063f 0x0ffff801fffff00c

def z705 : W := mkw 0x426186d58f8ddf54 0x2284c30dab1f1bbe 0xf6638fff8707ffef 0xf5ecc71fff0e0fff

def z706 : W := mkw 0x0ffffbaaf007200f 0xcc1ffff755e00e40 0xefffffffe0060005 0xffdfffffffc00c00

def z707 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef87fc03f89ff85e 0xfbdf0ff807f13ff0

def z708 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xa7bffcfc00000001 0xdf4f7ff9f8000000

def z709 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffffffffffe07ff 0xfffffffffffffc0f

def z710 : W := mkw 0x0a7db7aaf807b006 0xcc14fb6f55f00f60 0x087c03fff807f85f 0x0c10f807fff00ff0

def z711 : W := mkw 0x8d8aed32d8a59ae9 0xc51b15da65b14b35 0x96db8f339ce1c7a9 0x4d2db71e6739c38f

def z712 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0x0087fffc00000001 0xf0010ffff8000000

def z713 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffffffffc60001f 0xfffffffffff8c000

def z714 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xff587333e4e63fff 0xbffeb0e667c9cc7f

def z715 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xeffffffc60000017 0xffdffffff8c00000

def z716 : W := mkw 0x00009000a0072000 0x0800012001400e40 0xe603f0038007f84e 0xf1cc07e007000ff0

def z717 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc7003fff8003e 0xbffff8e007fff000

def z718 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958730064663fc4 0x20b2b0e600c8cc7f

def z719 : W := mkw 0x07f648035650000f 0x700fec9006aca000 0xfffc7c03fff8003e 0x8ffff8f807fff000

def z720 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63ff7 0x2cb2b0e660c9cc7f

def z721 : W := mkw 0x026b6ba906000005 0xa004d6d7520c0000 0xf663ffff8700002f 0xf5ecc7ffff0e0000

def z722 : W := mkw 0x8008a13080a50ae0 0x8100114261014a15 0xf65b833384e7c7ef 0x7decb7066709cf8f

def z723 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xf9fc0ffc7fffffff 0xfff3f81ff8ffffff

def z724 : W := mkw 0xc008313420aa2af0 0x8980106268415455 0x795c733c64fe3ff7 0xbef2b8e678c9fc7f

def z725 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99fe7b 0x4d014819f83733fc

def z726 : W := mkw 0x027f6ba800000007 0x8004fed750000000 0x005bfffc00000001 0xf000b7fff8000000

def z727 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x9ffc0003fff80038 0x0f3ff80007fff000

def z728 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x564383038407c7c4 0x20ac870607080f8f

def z729 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa7fcfffb9ff87f 0xffdf4ff9fff73ff0

def z730 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b19fe5b 0xd3414819f83633fc

def z731 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xe7ffffff80000001 0xffcfffffff000000

def z732 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc0300002b 0xffcffffff8060000

def z733 : W := mkw 0x47f404575fd8de5e 0x708fe808aebfb1bc 0x5f580cffe461fe45 0xd0beb019ffc8c3fc

def z734 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xa62383c38307c7eb 0x754c470787060f8f

def z735 : W := mkw 0x026112c127026504 0x2a04c225824e04ca 0x796073c067063ff7 0xb6f2c0e780ce0c7f

def z736 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0xe683fc039807f85e 0xf3cd07f807300ff0

def z737 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0x86a7ffff9b180009 0xf10d4fffff363000

def z738 : W := mkw 0x059582c2d155450a 0x520b2b0585a2aa8a 0x099f83c078ffc7d1 0x7a133f0780f1ff8f

def z739 : W := mkw 0x87fc313376f22aee 0xf90ff86266ede455 0x86a473339b1e3fc9 0xb10d48e667363c7f

def z740 : W := mkw 0x400004440908d410 0x00800008881211a8 0xa0a40cfc1b19f85b 0xdf414819f83633f0

def z741 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xf7fffffc04000027 0xffeffffff8080000

def z742 : W := mkw 0x827d23f107f04fe6 0xb304fa47e20fe09f 0x107c03f007f807a1 0x0c20f807e00ff00f

def z743 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0303fffe01be 0x2ffff80607fffc03

def z744 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc000607c1 0xffcffffff8000c0f

def z745 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83ff03f807ffdf 0xf3df07fe07f00fff

def z746 : W := mkw 0x026923a000000004 0x8004d24740000000 0xe7fffffc00000001 0xffcffffff8000000

def z747 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e38fc38707c7ef 0xf7edc71f870e0f8f

def z748 : W := mkw 0x0274000356500006 0x7004e80006aca000 0xfe7c0003fff8003e 0x0dfcf80007fff000

def z749 : W := mkw 0x07ff6ba80050000f 0x900ffed75000a000 0xe7fffffc00f80001 0xffcffffff801f000

def z750 : W := mkw 0x001f6ba800000003 0x80003ed750000000 0x001ffffc00000001 0xf8003ffff8000000

def z751 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xffffffffe7f80025 0xffffffffffcff000

def z752 : W := mkw 0xc0009455afaffff0 0x2b800128ab5f5fff 0x18000003fffffffe 0x0030000007ffffff

def z753 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc00fffff8003f 0x0ffff801fffff000

def z754 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x19fc0003fff8003e 0x0e33f80007fff000

def z755 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x0087fffc00000001 0xfa010ffff8000000

def z756 : W := mkw 0x427d23fd07d84e56 0xb084fa47fa0fb09c 0x107c03fc07f80621 0x0c20f807f80ff00c

def z757 : W := mkw 0x426186958e8d9b54 0x2284c30d2b1d1b36 0x56c78f3f9c9e3994 0xaaad8f1e7f393c73

def z758 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffffcfffff8003e 0xcffffff9fffff000

def z759 : W := mkw 0x8269b3f1a7a76fe4 0xab04d367e34f4edf 0x8f3bf0f3e3e1f818 0xcb1e77e1e7c7c3f0

def z760 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe1fc0cfc1b99fe7b 0xdfc3f819f83733fc

def z761 : W := mkw 0x000182c081054500 0x0200030581020a8a 0x860383c38007c7c9 0x710c070787000f8f

def z762 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf64383038707c7ee 0x71ec8706070e0f8f

def z763 : W := mkw 0x07ff6baa5000000f 0xc00ffed754a00000 0xfffffffffce0003f 0xfffffffffff9c000

def z764 : W := mkw 0x059400035650000a 0x700b280006aca000 0x099c0003fbf80018 0x0a13380007f7f000

def z765 : W := mkw 0x0d82d802f0072009 0x4c1b05b005e00e40 0xef03f003e007f85e 0xf3de07e007c00ff0

def z766 : W := mkw 0x000b6ba800000001 0x800016d750000000 0xa0a7fffc1b98003b 0xff414ffff8373000

def z767 : W := mkw 0x0000804187054500 0x22000100830e0a8a 0xf64383038707c7ef 0x75ec8706070e0f8f

def z768 : W := mkw 0x058b6ba800000009 0x800b16d750000000 0x4703fffc00000001 0xf08e07fff8000000

def z769 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f83fc03f807f85e 0xa29f07f807f00ff0

def z770 : W := mkw 0x0000000356500000 0x7000000006aca000 0x19180003fff8003e 0x0a32300007fff000

def z771 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0ccffff8003e 0x4ffff8199ffff000

def z772 : W := mkw 0x07ff6ba90650000f 0xb00ffed7520ca000 0xf7fffffc1ff8003b 0xffeffffff83ff000

def z773 : W := mkw 0x07f648035650000f 0x700fec9006aca000 0xfffffcfffff8003f 0xfffffff9fffff000

def z774 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99fe69 0xdd014819f83733fc

def z775 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fcfff807f85f 0xf3df07f9fff00ff0

def z776 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66783c3879fc7ef 0x7deccf07870f3f8f

def z777 : W := mkw 0x0002480000000001 0x0000049000000000 0xa0a7fcfc00000001 0xff414ff9f8000000

def z778 : W := mkw 0x87ff6ba8002000af 0x810ffed750004001 0xf7fffffc04600181 0xffeffffff808c003

def z779 : W := mkw 0x059ee9698705450b 0xa20b3dd2d30e0a8a 0x119c7c3f8707c7ee 0x8a2338f87f0e0f8f

def z780 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xe683fc039807f84e 0xf1cd07f807300ff0

def z781 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8f83fc03f807f85e 0xc31f07f807f00ff0

def z782 : W := mkw 0x48009456f98ffe50 0x4c900128adf31ffc 0x08000003f807fe5e 0x0010000007f00ffc

def z783 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003fff8387e 0x9ffff80007fff070

def z784 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1958733064e63ff1 0xbe32b0e660c9cc7f

def z785 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc0001c04b 0xffcffffff8000380

def z786 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0303fff807bf 0x0ffff80607fff00f

def z787 : W := mkw 0x0a76dc01ae57b007 0x3c14edb8035caf60 0x107ffc0007fff860 0xfc20fff8000ffff0

def z788 : W := mkw 0x059400035650000a 0x700b280006aca000 0x79dc0003fff8003e 0x0ef3b80007fff000

def z789 : W := mkw 0x4d82d856f18f6e59 0x4c9b05b0ade31edc 0x4f27f0ffe39e0625 0x2c9e4fe1ffc73c0c

def z790 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x6f03f003f807f85e 0xb2de07e007f00ff0

def z791 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xf7ffffff84000005 0xffefffffff080000

def z792 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffcfc00000000 0xcfcffff9f8000000

def z793 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf9fc7ffc7ffe3fff 0xfff3f8fff8fffc7f

def z794 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x966383c38707c7e9 0x752cc707870e0f8f

def z795 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa7fccff807f85e 0xf3df4ff99ff00ff0

def z796 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xffffffffff78000d 0xfffffffffffef000

def z797 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958730064e63ff7 0x34f2b0e600c9cc7f

def z798 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b19fe6b 0xd5414819f83633fc

def z799 : W := mkw 0x0580000250000008 0x400b000004a00000 0xfffc0003fff8003e 0x0ffff80007fff000

def z800 : W := mkw 0x80083120202220a0 0x8900106240404441 0x7958730064663ff7 0xb6f2b0e600c8cc7f

def z801 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefdbfc03f807f85e 0xffdfb7f807f00ff0

def z802 : W := mkw 0x426182c5870d4514 0x2284c3058b0e1a8a 0xf66783cf871fc7ef 0x75eccf079f0e3f8f

def z803 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xffdbff03fce7ffff 0xffffb7fe07f9cfff

def z804 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf97873f064e63ff7 0xfff2f0e7e0c9cc7f

def z805 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xff780003fff8003e 0x05fef00007fff000

def z806 : W := mkw 0x058b6ba800000009 0x800b16d750000000 0xe7a7fffc00000001 0xffcf4ffff8000000

def z807 : W := mkw 0x07f648035650000f 0x700fec9006aca000 0xfffff003fff8003e 0x2fffffe007fff000

def z808 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xffd80003fff8003e 0x03ffb00007fff000

def z809 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383c38707ffff 0xf7ecc707870e0fff

def z810 : W := mkw 0x0d96dc0af807b00b 0x4c1b2db815f00f60 0xef87fc0ff807f85e 0xf3df0ff81ff00ff0

def z811 : W := mkw 0x0261828186050104 0x2204c305030c0a02 0xf64383038407c7ef 0x75ec870607080f8f

def z812 : W := mkw 0x027f6ba800000007 0x8004fed750000000 0x0027fffc00000001 0xf0004ffff8000000

def z813 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99fe59 0xdb014819f83733fc

def z814 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03f887f87e 0xffdf07f807f10ff0

def z815 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383f38707c7ef 0xffecc707e70e0f8f

def z816 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x0027fffc00000001 0xfc004ffff8000000

def z817 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x2003fffc00000001 0xfe4007fff8000000

def z818 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x87bffffc00000001 0xfb0f7ffff8000000

def z819 : W := mkw 0x026b6ba800000005 0x8004d6d750000000 0xe77bfffc00000001 0xffcef7fff8000000

def z820 : W := mkw 0x07eb6ba80000000d 0x800fd6d750000000 0xe7e3fffc00000001 0xf7cfc7fff8000000

def z821 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xff83fc03fc07fffe 0xf3ff07f807f80fff

def z822 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0xe79ffffc00000001 0xfbcf3ffff8000000

def z823 : W := mkw 0xc0083564292af4b0 0x8980106ac85255e9 0xd9fc7fcc7f7fc18c 0x61b3f8ff98feff83

def z824 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8e83fc03f807f85e 0xf11d07f807f00ff0

def z825 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc33f807f85f 0xffdf07f867f00ff0

def z826 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958730064e63ff6 0x2ef2b0e600c9cc7f

def z827 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003fffe007e 0x3ffff80007fffc00

def z828 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xf7fffffc040007a1 0xffeffffff808000f

def z829 : W := mkw 0x026182c081054504 0x0204c30581020a8a 0xe66383c38007c7cf 0x75ccc70787000f8f

def z830 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6638fff8707c7ef 0xf5ecc71fff0e0f8f

def z831 : W := mkw 0x026b6ba800000005 0x8004d6d750000000 0x4643fffc00000001 0xf08c87fff8000000

def z832 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7ffffff8000000f 0xffcfffffff000000

def z833 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf9fc733064e63ff7 0xbff3f8e660c9cc7f

def z834 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03fb9ff87e 0xf3df07f807f73ff0

def z835 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b99f83a 0xcf414819f83733f0

def z836 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xffffffffe760002f 0xffffffffffcec000

def z837 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xc7fffffc00000001 0x6d8ffffff8000000

def z838 : W := mkw 0x87f75a9820a22aef 0x090feeb530414455 0x9ea78ccc64e63ff6 0x413d4f1998c9cc7f

def z839 : W := mkw 0x058b6ba800000009 0x800b16d750000000 0x8683fffc00000001 0xf10d07fff8000000

def z840 : W := mkw 0x48009457ff8fff50 0x6e900128afff1ffe 0x18000003ff9ffffe 0x0030000007ff3fff

def z841 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0xef03fc03e007f85e 0xf3de07f807c00ff0

def z842 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00a40cfc1b99fe7b 0x8e014819f83733fc

def z843 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0x5f5bffffe4600005 0xf0beb7ffffc8c000

def z844 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e78fff9f9fc7ff 0xffedcf1fff3f3f8f

def z845 : W := mkw 0x0000040008009000 0x0000000800100120 0xa0a40cfc1b99f87b 0xdf414819f83733f0

def z846 : W := mkw 0x0000000356500000 0x7000000006aca000 0x59580003fff8003e 0x00b2b00007fff000

def z847 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x564383c38707c7ef 0x70ac8707870e0f8f

def z848 : W := mkw 0x0d82dc00a807b009 0x0c1b05b801500f60 0xe783fc038007f84e 0xf3cf07f807000ff0

def z849 : W := mkw 0x4ff49457ffdffe5e 0x7c9fe928afffbffc 0xfffc0003fffffe7e 0x0ffff80007fffffc

def z850 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa7fc03f807f85e 0xffdf4ff807f00ff0

def z851 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe6a40cff9b99fe7f 0xdfcd4819ff3733fc

def z852 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x6f03fc03e007f856 0xf2de07f807c00ff0

def z853 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc18980011 0xffcffffff8313000

def z854 : W := mkw 0x0fe35ec37f02f50d 0x6e1fc6bd86fe05ea 0x19e07fc07f003fb1 0x8633c0ff80fe007f

def z855 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x79587ffc64e63ff7 0xfef2b0fff8c9cc7f

def z856 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x0603fffc00000001 0xf00c07fff8000000

def z857 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffffffc7ff80031 0xfffffffff8fff000

def z858 : W := mkw 0x8d9e7d3278f2baeb 0xdd1b3cfa64f1e575 0x099c7c3078f83810 0x8a1338f860f1f070

def z859 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xeffffffffb18001f 0xffdffffffff63000

def z860 : W := mkw 0x000182c187054500 0x22000305830e0a8a 0xf60383c38707c7ef 0x71ec0707870e0f8f

def z861 : W := mkw 0x000b6bab56500001 0xf00016d756aca000 0x1803fffffff8003f 0xf03007fffffff000

def z862 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa7fc03fb1ff85e 0xf3df4ff807f63ff0

def z863 : W := mkw 0x0582480000000009 0x000b049000000000 0xe783fcfc00000001 0xf3cf07f9f8000000

def z864 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xff83fc03fce7f87e 0xf3ff07f807f9cff0

def z865 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5f7c0003fff8003e 0x0cbef80007fff000

def z866 : W := mkw 0x07e34a800000000d 0x000fc69500000000 0xe7e7fffc00000001 0xffcfcffff8000000

def z867 : W := mkw 0x07f502835650000e 0x700fea0506aca000 0xffff83c3fffe07ff 0x7fffff0787fffc0f

def z868 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003fff8067f 0x1ffff80007fff00c

def z869 : W := mkw 0x48009457ffdffe50 0x7c900128afffbffc 0x18000003fffffe7e 0x0030000007fffffc

def z870 : W := mkw 0x07ff6ba90650000f 0xb00ffed7520ca000 0xfffffffc67f80037 0xfffffffff8cff000

def z871 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe1a47cfc1b99fe7b 0xffc348f9f83733fc

def z872 : W := mkw 0x026b6ba800000005 0x8004d6d750000000 0xe6e7fffc00000001 0xffcdcffff8000000

def z873 : W := mkw 0x47ff6ffc0988de5f 0x808ffedff81311bc 0x475bf3001b99fe7a 0x208eb7e6003733fc

def z874 : W := mkw 0x0260000356500004 0x7004c00006aca000 0xff780003fff8003e 0x0ffef00007fff000

def z875 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x0003fcfc00000000 0xc00007f9f8000000

def z876 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xf7ffffff9f18002f 0xffefffffff3e3000

def z877 : W := mkw 0x0ffffbabf657200f 0xfc1ffff757ecae40 0x5f5bf303e4660004 0x20beb7e607c8cc00

def z878 : W := mkw 0x0274000356500006 0x7004e80006aca000 0x797c0003fff8003e 0x0ef2f80007fff000

def z879 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef03fc03e007f84e 0xf1de07f807c00ff0

def z880 : W := mkw 0x027f6ba800000007 0x8004fed750000000 0xe67ffffc00000001 0xfdccfffff8000000

def z881 : W := mkw 0x059400035650000a 0x700b280006aca000 0xb9bc0003fff8003e 0x0f73780007fff000

def z882 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83f003f807f85e 0x23df07e007f00ff0

def z883 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf958733064e7ffff 0xfff2b0e660c9cfff

def z884 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x6043fffc00000001 0xf4c087fff8000000

def z885 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x011bfffc00000001 0xfa0237fff8000000

def z886 : W := mkw 0x0000804081054400 0x0000010081020a88 0xf66383c38707c7ef 0x75ecc707870e0f8f

def z887 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x060383c38007c7c1 0x700c070787000f8f

def z888 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xc7fffffc00000000 0xeb8ffffff8000000

def z889 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5ffc0003fff80034 0x0ebff80007fff000

def z890 : W := mkw 0xc26923f507a84ff4 0xa384d247ea0f509f 0x107c03fc07f807a1 0x0c20f807f80ff00f

def z891 : W := mkw 0x027582c187054506 0x2204eb05830e0a8a 0xf67f83c38707c7ef 0x7decff07870e0f8f

def z892 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xe62383c38307c7cf 0x71cc470787060f8f

def z893 : W := mkw 0xcd8a7d3678aabaf9 0xcd9b14fa6cf15575 0x099c7c3c78f83810 0x8a1338f878f1f070

def z894 : W := mkw 0x000182c081054500 0x0200030581020a8a 0x460383c38007c7c5 0x708c070787000f8f

def z895 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e383c39f07c7ff 0x77edc707873e0f8f

def z896 : W := mkw 0x07ff6baa5000000f 0xc00ffed754a00000 0xeffffffffb98003f 0xffdffffffff73000

def z897 : W := mkw 0x058a692000000009 0x800b14d240000000 0xe7fffffc00000001 0xffcffffff8000000

def z898 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03f807fe7f 0xf7df07f807f00ffc

def z899 : W := mkw 0x07f74a8b5650000f 0x700fee9516aca000 0xffff8cfffff8003f 0xdfffff19fffff000

def z900 : W := mkw 0x07ff6ba90650000f 0xb00ffed7520ca000 0xf7fffffc04600001 0xffeffffff808c000

def z901 : W := mkw 0x0580000356500008 0x700b000006aca000 0xffd80003fff8003e 0x0fffb00007fff000

def z902 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958733064663fe7 0xb4f2b0e660c8cc7f

def z903 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x966383c38707c7ef 0x452cc707870e0f8f

def z904 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xd66383c38707c7ad 0x65acc707870e0f8f

def z905 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xa683fc039807f85a 0xf34d07f807300ff0

def z906 : W := mkw 0x0582d800a0072009 0x080b05b001400e40 0xef83fc03e007f85e 0xf3df07f807c00ff0

def z907 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xb0fc0cfc1ff9fe7b 0xdf61f819f83ff3fc

def z908 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x79dc73307cfe3ff7 0xbef3b8e660f9fc7f

def z909 : W := mkw 0x07f648000000000f 0x000fec9000000000 0xe7fffcfc00000001 0xffcffff9f8000000

def z910 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03f801f81e 0xc3df07f807f003f0

def z911 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc00c3fff8003f 0x5ffff80187fff000

def z912 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0033fff8003f 0x9ffff80067fff000

def z913 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa9bc0cfc7bf9fe7b 0xdf537819f8f7f3fc

def z914 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xb0e40ffc1f99fffb 0xdf61c81ff83f33ff

def z915 : W := mkw 0x4d82dc06f80fb019 0x4c9b05b80df01f60 0xef87fc0ff81ff85e 0xf3df0ff81ff03ff0

def z916 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x797c733067fe3ff7 0xbef2f8e660cffc7f

def z917 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7dbfffc00000001 0xf3cfb7fff8000000

def z918 : W := mkw 0x026182c187554504 0x3204c305830eaa8a 0xf66383c387ffc7ef 0x75ecc707870fff8f

def z919 : W := mkw 0x05809002f0072008 0x480b012005e00e40 0xef83f003f807f85e 0xf3df07e007f00ff0

def z920 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xeffffffc60e00011 0xffdffffff8c1c000

def z921 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe0e40ffc1b99fe7b 0xffc1c81ff83733fc

def z922 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x764383c38407c7e7 0x74ec870787080f8f

def z923 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc00000663 0xffcffffff800000c

def z924 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0x61dffffc00000001 0xfec3bffff8000000

def z925 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383038707c7ee 0x25ecc706070e0f8f

def z926 : W := mkw 0x07ff6ba90650000f 0xb00ffed7520ca000 0xe7fffffc03180001 0xffcffffff8063000

def z927 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xfffffc03fffff87e 0xfffffff807fffff0

def z928 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0c03fff8003e 0xdffff81807fff000

def z929 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x764383038707c7ef 0x34ec8706070e0f8f

def z930 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x566383c38707c7e5 0x74acc707870e0f8f

def z931 : W := mkw 0x07ff6baa5000000f 0xc00ffed754a00000 0xe7ffffff98000009 0xffcfffffff300000

def z932 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe6a78cfc1b99fe7b 0xffcd4f19f83733fc

def z933 : W := mkw 0x058b6baa50000009 0xc00b16d754a00000 0xef83fffff800001f 0xf3df07fffff00000

def z934 : W := mkw 0x059f6baa5050000b 0xd00b3ed754a0a000 0x099ffffc78f80011 0xfa133ffff8f1f000

def z935 : W := mkw 0x059e69280000000b 0x800b3cd250000000 0xe7bffcfc00000001 0xffcf7ff9f8000000

def z936 : W := mkw 0x0ff7cec3df55d50f 0x761fef9d87beabaa 0x86a78cc39b19c008 0x410d4f1987363380

def z937 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x797c73fc64e63ff7 0xbef2f8e7f8c9cc7f

def z938 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefc3ff03f807f85f 0xf7df87fe07f00ff0

def z939 : W := mkw 0x07ff6bab5600000f 0xe00ffed756ac0000 0xffffffffff00003f 0xfffffffffffe0000

def z940 : W := mkw 0x48009454a98ffe50 0x0c900128a9531ffc 0x000000000007fe40 0x0000000000000ffc

def z941 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0x019ffcfc00000000 0xca033ff9f8000000

def z942 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x9efc0003fff8003e 0x0d3df80007fff000

def z943 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x87fffffc00000001 0xcf0ffffff8000000

def z944 : W := mkw 0x07f74a8b5650000f 0x700fee9516aca000 0xffff8003fff8003e 0x0fffff0007fff000

def z945 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xeffffffffbf80019 0xffdffffffff7f000

def z946 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0x8fbffcfffbf80018 0xcb1f7ff9fff7f000

def z947 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x795bfffc64e00037 0xfef2b7fff8c9c000

def z948 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xf7fffffc04e00021 0xffeffffff809c000

def z949 : W := mkw 0x07f74a8b5650000f 0x700fee9516aca000 0xffff8fcffff8003f 0x7fffff1f9ffff000

def z950 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf763f3c38707c7ef 0xf7eec7e7870e0f8f

def z951 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf9d873307ce63fff 0xbff3b0e660f9cc7f

def z952 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf64383c38407c7cf 0x71ec870787080f8f

def z953 : W := mkw 0x48009454a98ffe50 0x0c900128a9531ffc 0x000000001b9ffe7a 0x0000000000373ffc

def z954 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xff7b83c3e767c7ef 0x75fef70787cecf8f

def z955 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf978733067e63fff 0xbff2f0e660cfcc7f

def z956 : W := mkw 0x059400035650000a 0x700b280006aca000 0x19180003fff8003e 0x0032300007fff000

def z957 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xd66383c38707c7ee 0x61acc707870e0f8f

def z958 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b19fe49 0xdf414819f83633fc

def z959 : W := mkw 0x0d82cc02d8059009 0x441b059805b00b20 0xe783fc039801f85a 0xf3cf07f8073003f0

def z960 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xfffffffc7ff8003f 0xfffffffff8fff000

def z961 : W := mkw 0x4d809456f98ffe58 0x4c9b0128adf31ffc 0xefa40003fb9ffe7e 0x0fdf480007f73ffc

def z962 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x415bfffc00000001 0xf082b7fff8000000

def z963 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa3fc03fb07f87e 0xf7df47f807f60ff0

def z964 : W := mkw 0x00009400a807b000 0x0800012801500f60 0xef83fc03f807f85e 0xf3df07f807f00ff0

def z965 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7a7fffc00000001 0xf3cf4ffff8000000

def z966 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x86a7fcfc00000000 0xc10d4ff9f8000000

def z967 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xefbc0003fbf8001e 0x0bdf780007f7f000

def z968 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0x4603fc038007f844 0xf08c07f807000ff0

def z969 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xcf83fc03f807f85e 0x619f07f807f00ff0

def z970 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003fff9c07e 0x5ffff80007fff380

def z971 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc03980021 0xffcffffff8073000

def z972 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xffdbfc03fc67f85e 0xf3ffb7f807f8cff0

def z973 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03e007f844 0xf3df07f807c00ff0

def z974 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xffc3ff03fc07f9de 0xf3ff87fe07f80ff3

def z975 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc00003853 0xffcffffff8000070

def z976 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0003fffe07fe 0x0ffff80007fffc0f

def z977 : W := mkw 0x826923f107a04fe4 0xa304d247e20f409f 0x106003f0070007a1 0x0420c007e00e000f

def z978 : W := mkw 0x0000100020022000 0x0800002000400440 0x7958730064e63ff7 0xbef2b0e600c9cc7f

def z979 : W := mkw 0x027582c987054506 0x2204eb05930e0a8a 0xf66783cf8707c7ef 0x75eccf079f0e0f8f

def z980 : W := mkw 0x07f502835650000e 0x700fea0506aca000 0xffff80c3fff8003e 0x4fffff0187fff000

def z981 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xcf83fc03f807f81c 0xe39f07f807f00ff0

def z982 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99fe7b 0xd1014819f83733fc

def z983 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xa6a7fffc00000001 0xff4d4ffff8000000

def z984 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xf7ffffff870607ef 0xffefffffff0e0c0f

def z985 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xefa3fcc3f807f85f 0xf7df47f987f00ff0

def z986 : W := mkw 0x0d96dc02f857b00b 0x5c1b2db805f0af60 0xefbffc03fbfff87e 0xffdf7ff807f7fff0

def z987 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xf0e40cfc1f99fe7f 0xdfe1c819f83f33fc

def z988 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b99f85a 0xdb414819f83733f0

def z989 : W := mkw 0x07ff6ba90650000f 0xb00ffed7520ca000 0xf7ffffff87f8002f 0xffefffffff0ff000

def z990 : W := mkw 0x07f502835650000e 0x700fea0506aca000 0xffff8ffffff8003f 0xffffff1ffffff000

def z991 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f03fc03f807f85e 0xf09e07f807f00ff0

def z992 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40ffc1b9ffffb 0xff41481ff8373fff

def z993 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x5fdc0003fff8003e 0x0abfb80007fff000

def z994 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63fb5 0xaeb2b0e660c9cc7f

def z995 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63ff7 0xb0b2b0e660c9cc7f

def z996 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x00a40cfc1b99fe71 0xde014819f83733fc

def z997 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99fe39 0xcf014819f83733fc

def z998 : W := mkw 0x05824c0258009009 0x400b049804b00120 0xef83fc03f801f85e 0xf3df07f807f003f0

def z999 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63fe5 0xbcb2b0e660c9cc7f

def z1000 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xcf83fc03f807f84c 0xf19f07f807f00ff0

def z1001 : W := mkw 0x0000800080050000 0x0000010001000a00 0xe60383038007c7cf 0x71cc070607000f8f

def z1002 : W := mkw 0x8d82dc02f827b0a9 0x4d1b05b805f04f61 0xff83fc03fc67f9de 0xf3ff07f807f8cff3

def z1003 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef03f003f807f85e 0x71de07e007f00ff0

def z1004 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe9a40cfc7b99fe7f 0xdfd34819f8f733fc

def z1005 : W := mkw 0x000b6ba800000001 0x800016d750000000 0xa083fffc00000001 0xf34107fff8000000

def z1006 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x80a7fffc00000001 0xf1014ffff8000000

def z1007 : W := mkw 0x07ff6ba90600010f 0xa20ffed7520c0002 0xf7fffffc04000181 0xffeffffff8080003

def z1008 : W := mkw 0x027582c187554506 0x3204eb05830eaa8a 0xf6ff83c39fffc7ff 0x7fedff07873fff8f

def z1009 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe77bfffc00000001 0xf5cef7fff8000000

def z1010 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x47fffffc00000001 0xae8ffffff8000000

def z1011 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xfe6383c3e7e7c7ff 0x75fcc70787cfcf8f

def z1012 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x675bfffc00000001 0xfeceb7fff8000000

def z1013 : W := mkw 0xc000045409a8def0 0x01800008a81351bd 0xb0a40cfc1ff9fffb 0xdf614819f83ff3ff

def z1014 : W := mkw 0x827d23f907a04fe6 0xa304fa47f20f409f 0x107c03fc07e007a1 0x0c20f807f80fc00f

def z1015 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xff6383c3e707c7ff 0x77fec70787ce0f8f

def z1016 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f03f003e007f844 0x209e07e007c00ff0

def z1017 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xa0a40cfc1b99f819 0xdf414819f83733f0

def z1018 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc00800033 0xffcffffff8010000

def z1019 : W := mkw 0x0582cc0088059009 0x000b059801100b20 0xe783fc039807f85e 0xf3cf07f807300ff0

def z1020 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x962383c38707c7ef 0x712c4707870e0f8f

def z1021 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xf9d87f3064e63ff7 0xfff3b0fe60c9cc7f

def z1022 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xf7fffffc07000021 0xffeffffff80e0000

def z1023 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0x566383c38707c7ef 0x24acc707870e0f8f

def z1024 : W := mkw 0x0000000356500000 0x7000000006aca000 0xf9fc0003fff8003e 0x0ff3f80007fff000

def z1025 : W := mkw 0x07ff6baa5050000f 0xd00ffed754a0a000 0xeffffffc7bf8003b 0xffdffffff8f7f000

def z1026 : W := mkw 0x0802dc00a807b001 0x0c1005b801500f60 0x8603fc038007f848 0xf10c07f807000ff0

def z1027 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xffff8003fff8003e 0x7fffff0007fff000

def z1028 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e783c38707c7ef 0x7fedcf07870e0f8f

def z1029 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc1b180009 0xffcffffff8363000

def z1030 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63ff6 0xaab2b0e660c9cc7f

def z1031 : W := mkw 0x07f648035650000f 0x700fec9006aca000 0xffff8c03fff8003e 0x4fffff1807fff000

def z1032 : W := mkw 0x000b6ba800000001 0x800016d750000000 0xe1fffffc00000001 0xffc3fffff8000000

def z1033 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xffff83c3ffffc7ff 0x7fffff0787ffff8f

def z1034 : W := mkw 0x07ff6baa5050000f 0xd00ffed754a0a000 0xfffffffc7cf80037 0xfffffffff8f9f000

def z1035 : W := mkw 0x027f6ba800000007 0x8004fed750000000 0x617ffffc00000001 0xfec2fffff8000000

def z1036 : W := mkw 0x0260800186050004 0x2004c100030c0a00 0xf66383038707c7ef 0x75ecc706070e0f8f

def z1037 : W := mkw 0x0274000356500006 0x7004e80006aca000 0x18580003fff8003e 0x0030b00007fff000

def z1038 : W := mkw 0x0d96dc02f857b00b 0x5c1b2db805f0af60 0xef9bfc03f867f85e 0xf3df37f807f0cff0

def z1039 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x79dc7f3c64e63ff7 0xbef3b8fe78c9cc7f

def z1040 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x7f580003fff8003e 0x0efeb00007fff000

def z1041 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x0603fc038007f840 0xf00c07f807000ff0

def z1042 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0xa1bffffc00000001 0xff437ffff8000000

def z1043 : W := mkw 0xc009b7f4a9affff0 0x8b80136fe9535fff 0x0003fffc0007ffc1 0xf00007fff8000fff

def z1044 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xb8a40cfc7ff9fe7f 0xdf714819f8fff3fc

def z1045 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xe7ffffff9b98003b 0xffcfffffff373000

def z1046 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e783c39f1fc7ef 0x75edcf07873e3f8f

def z1047 : W := mkw 0x026b6ba800000005 0x8004d6d750000000 0x0063fffc00000001 0xf400c7fff8000000

def z1048 : W := mkw 0x07ff6baa5000000f 0xc00ffed754a00000 0xefffffffe0000005 0xffdfffffffc00000

def z1049 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xc7fffffc00000001 0xf18ffffff8000000

def z1050 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf77b83c38707c7ef 0x7feef707870e0f8f

def z1051 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383c38407c7c5 0x75ecc70787080f8f

def z1052 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x795873307ffe3fff 0xbef2b0e660fffc7f

def z1053 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x47dffffc00000001 0xfa8fbffff8000000

def z1054 : W := mkw 0x07f502835650000e 0x700fea0506aca000 0xfffc03c3fff8003f 0x0ffff80787fff000

def z1055 : W := mkw 0xc8009456f9affef0 0x4d900128adf35ffd 0x18000003fffffffe 0x0030000007ffffff

def z1056 : W := mkw 0x0002480000000001 0x0000049000000000 0x0003fcfc00000001 0xf00007f9f8000000

def z1057 : W := mkw 0x027582c187554506 0x3204eb05830eaa8a 0xf67b83c38767c7ef 0x75ecf707870ecf8f

def z1058 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xdffc0003fff8002c 0x0dbff80007fff000

def z1059 : W := mkw 0x0d82dc02f857b009 0x5c1b05b805f0af60 0xef83fc03f8fff85e 0xf3df07f807f1fff0

def z1060 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66783ff8707c7ef 0x7deccf07ff0e0f8f

def z1061 : W := mkw 0x0000000356500000 0x7000000006aca000 0x18580003fff8003e 0x0c30b00007fff000

def z1062 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xb0a40cfc1f9fffff 0xdf614819f83f3fff

def z1063 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xffffffffe7e0003f 0xffffffffffcfc000

def z1064 : W := mkw 0x026b6ba800000005 0x8004d6d750000000 0x8623fffc00000001 0xf10c47fff8000000

def z1065 : W := mkw 0x058b6ba800000009 0x800b16d750000000 0xe7dbfffc00000001 0xffcfb7fff8000000

def z1066 : W := mkw 0x0260000106000004 0x2004c000020c0000 0xfffc0003fff8003e 0x0ffff80007fff000

def z1067 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b19f808 0xc1014819f83633f0

def z1068 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xeffc0003fbf80018 0x0fdff80007f7f000

def z1069 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x86fffffc00000001 0xfd0dfffff8000000

def z1070 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x6103fffc00000001 0xf2c207fff8000000

def z1071 : W := mkw 0x400004540988de50 0x00800008a81311bc 0xe0a40cfc1b9ffe7f 0xffc14819f8373ffc

def z1072 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xafbc0003fbf8003a 0x0f5f780007f7f000

def z1073 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xaf83fc03f801f85a 0xd35f07f807f003f0

def z1074 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc1800001b 0xffcffffff8300000

def z1075 : W := mkw 0x0261828080050004 0x0004c30501000a00 0xf66383c38407c7ef 0x75ecc70787080f8f

def z1076 : W := mkw 0xc80afd74a9affef1 0x8d9015fae9535ffd 0x0003fffc0007ffc1 0xf00007fff8000fff

def z1077 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x005bfffc00000001 0xfc00b7fff8000000

def z1078 : W := mkw 0x07f6480b5650000f 0x700fec9016aca000 0xfffc0c0ffff8003e 0x0ffff8181ffff000

def z1079 : W := mkw 0x000b6ba800000001 0x800016d750000000 0xa023fffc00000001 0xf54047fff8000000

def z1080 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x0003fffc000607c1 0xf00007fff8000c0f

def z1081 : W := mkw 0x07f74a835650000f 0x700fee9506aca000 0xffffffc3fff8003f 0xffffffff87fff000

def z1082 : W := mkw 0x000182c081054500 0x0200030581020a8a 0xe62383c38307c7ef 0x75cc470787060f8f

def z1083 : W := mkw 0x0014000356500002 0x7000280006aca000 0x181c0003fff8003e 0x0830380007fff000

def z1084 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958733064663fd7 0xb2f2b0e660c8cc7f

def z1085 : W := mkw 0x08009402f807b000 0x4c10012805f00f60 0xef03f003f807f85e 0xf3de07e007f00ff0

def z1086 : W := mkw 0x0274000356500006 0x7004e80006aca000 0xb8fc0003fff8003e 0x0f71f80007fff000

def z1087 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958733064663fc5 0xbef2b0e660c8cc7f

def z1088 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xfffffffffcf80015 0xfffffffffff9f000

def z1089 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xe783fc039807f848 0xf3cf07f807300ff0

def z1090 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xd66383c38707c7cd 0x71acc707870e0f8f

def z1091 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x4f83fc03f807f854 0xf29f07f807f00ff0

def z1092 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0303fff8003f 0x3ffff80607fff000

def z1093 : W := mkw 0x427d23fd07884f56 0xa284fa47fa0f109e 0x107c03fc079807a1 0x0c20f807f80f300f

def z1094 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef87fc3ff807f85e 0xfbdf0ff87ff00ff0

def z1095 : W := mkw 0x07f74a880000000f 0x000fee9510000000 0xe7a7fcfc00000001 0xffcf4ff9f8000000

def z1096 : W := mkw 0x400004540988de50 0x00800008a81311bc 0x80a40cfc1b99fe7a 0xcb014819f83733fc

def z1097 : W := mkw 0x07ff6baa5050000f 0xd00ffed754a0a000 0xe7fffffc18180001 0xffcffffff8303000

def z1098 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383c38787c7ff 0x7fecc707870f0f8f

def z1099 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe6e7fffc00000001 0xf5cdcffff8000000

def z1100 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xdffc0003fff8001c 0x0bbff80007fff000

def z1101 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xf7ffffff9ff80029 0xffefffffff3ff000

def z1102 : W := mkw 0x0d96dc02f857b00b 0x5c1b2db805f0af60 0xef87fc03f81ff85e 0xf3df0ff807f03ff0

def z1103 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0x9fbc0003fff8003e 0x0b3f780007fff000

def z1104 : W := mkw 0x058b6ba800000009 0x800b16d750000000 0x0183fffc00000001 0xf20307fff8000000

def z1105 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf6e78fcf8707c7ef 0x75edcf1f9f0e0f8f

def z1106 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8683fc039801f808 0xc10d07f8073003f0

def z1107 : W := mkw 0x000b6ba800000001 0x800016d750000000 0x7043fffc040607e7 0xf4e087fff8080c0f

def z1108 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x7958730064e63ff6 0xb2f2b0e600c9cc7f

def z1109 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xdffc0003fff8003e 0x01bff80007fff000

def z1110 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef9bfc03f8e7f85e 0xfbdf37f807f1cff0

def z1111 : W := mkw 0x07f400035650000e 0x700fe80006aca000 0xfffc0c3ffff8003e 0x8ffff8187ffff000

def z1112 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xf7ffffff9f98003f 0xffefffffff3f3000

def z1113 : W := mkw 0x8d8a7d3278a2bae9 0xcd1b14fa64f14575 0x09807c3078003810 0x821300f860f00070

def z1114 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7fffffc00060047 0xffcffffff8000c00

def z1115 : W := mkw 0x0582480250000009 0x400b049004a00000 0xefa7fcfffb98003f 0xffdf4ff9fff73000

def z1116 : W := mkw 0x0802dc02f807b001 0x4c1005b805f00f60 0xee03fc03f807f85e 0xf1dc07f807f00ff0

def z1117 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x1958733064e63ff7 0x8e32b0e660c9cc7f

def z1118 : W := mkw 0x027f6ba800000007 0x8004fed750000000 0xa0fffffc00000001 0xff41fffff8000000

def z1119 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xfffffffc64600005 0xfffffffff8c8c000

def z1120 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf66383c39f9fc7ff 0x75ecc707873f3f8f

def z1121 : W := mkw 0x059f6ba80000000b 0x800b3ed750000000 0x011bfffc00000001 0xf00237fff8000000

def z1122 : W := mkw 0x027f6ba906500007 0xb004fed7520ca000 0x107ffffc07f80021 0xfc20fffff80ff000

def z1123 : W := mkw 0x027582c187554506 0x3204eb05830eaa8a 0xff7f83c3e7ffc7ff 0x7ffeff0787cfff8f

def z1124 : W := mkw 0x07ff6ba90600000f 0xa00ffed7520c0000 0xe7ffffff83000009 0xffcfffffff060000

def z1125 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xe7bffcfc00000000 0xfbcf7ff9f8000000

def z1126 : W := mkw 0x027582c187554506 0x3204eb05830eaa8a 0xf66783c3871fc7ef 0x75eccf07870e3f8f

def z1127 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xf7fffffc04060185 0xffeffffff8080c03

def z1128 : W := mkw 0x07ff6bab5650000f 0xf00ffed756aca000 0xffffffffe4e00037 0xffffffffffc9c000

def z1129 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x01fffffc00000001 0xfe03fffff8000000

def z1130 : W := mkw 0x07ff6baa5050000f 0xd00ffed754a0a000 0xeffffffff8f8001f 0xffdffffffff1f000

def z1131 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0x477ffffc00000001 0xfc8efffff8000000

def z1132 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xe66383c38307c7c9 0x75ccc70787060f8f

def z1133 : W := mkw 0x000182c081054500 0x0200030581020a8a 0xf64383c38407c7ef 0x75ec870787080f8f

def z1134 : W := mkw 0x8d9e7d3a78a2baeb 0xcd1b3cfa74f14575 0x099c7c3c78e03810 0x8a1338f878f1c070

def z1135 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0x8f83fc03f807f858 0xf31f07f807f00ff0

def z1136 : W := mkw 0x059400035650000a 0x700b280006aca000 0xff9c0003fff8003e 0x0bff380007fff000

def z1137 : W := mkw 0x07ff6ba80000000f 0x800ffed750000000 0xfffffffc64e607f7 0xfffffffff8c9cc0f

def z1138 : W := mkw 0x07f5028b5650000e 0x700fea0516aca000 0xfffc00cffff8003e 0x0ffff8019ffff000

def z1139 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xffc3fc03fc07f87e 0xf7ff87f807f80ff0

def z1140 : W := mkw 0x0d96dc02f807b00b 0x4c1b2db805f00f60 0xef9ffc03f807f85e 0xfbdf3ff807f00ff0

def z1141 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0xff5bf33064e63ff7 0xfffeb7e660c9cc7f

def z1142 : W := mkw 0x07f502835650010e 0x720fea0506aca002 0xfffc0303fff801be 0x0ffff80607fff003

def z1143 : W := mkw 0x0d82dc02f807b009 0x4c1b05b805f00f60 0xef83fc03f801f818 0xf3df07f807f003f0

def z1144 : W := mkw 0x07f502835650000e 0x700fea0506aca000 0xffff8303fff8003e 0x2fffff0607fff000

def z1145 : W := mkw 0x07ff6baa5000000f 0xc00ffed754a00000 0xeffffffc78000011 0xffdffffff8f00000

def z1146 : W := mkw 0x059400025050000a 0x500b280004a0a000 0xefbc0003fbf8003e 0x0fdf780007f7f000

def z1147 : W := mkw 0x000b6ba800000001 0x800016d750000000 0xe603fffc00000001 0xf1cc07fff8000000

def z1148 : W := mkw 0x026182c187054504 0x2204c305830e0a8a 0xf67b83c387e7c7ef 0x7decf707870fcf8f

def z1149 : W := mkw 0x07f74a8b5650000f 0x700fee9516aca000 0xfffffccffff8003e 0xfffffff99ffff000

def z1150 : W := mkw 0x8008313020a22ae0 0x8900106260414455 0x5958733064e63fd5 0xbab2b0e660c9cc7f

def z1151 : W := mkw 0x07ff6baa5050000f 0xd00ffed754a0a000 0xeffffffc60600001 0xffdffffff8c0c000

def z1152 : W := mkw 0x0d96dc02f857b00b 0x5c1b2db805f0af60 0xffdffc03fcfff87e 0xffffbff807f9fff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z5,z8])],[(0,[z0,z2,z3,z4,z5,z9,z6]),(0,[z0,z2,z3,z4,z5,z10,z8]),(0,[z0,z2,z11,z3,z4,z5,z6])],[(0,[z2,z12,z3,z4,z5,z13,z6]),(0,[z14,z0,z2,z3,z4,z5,z6]),(0,[z15,z0,z2,z16,z4,z5,z6]),(1,[z15,z2,z3,z4,z5,z17]),(0,[z18,z0,z2,z4,z5,z19,z6]),(0,[z0,z2,z3,z20,z4,z5,z21])],[(0,[z22,z2,z12,z3,z4,z5,z6]),(0,[z0,z23,z2,z24,z4,z5,z6]),(0,[z2,z3,z4,z25,z5,z13,z6]),(0,[z0,z2,z3,z26,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z6,z27])],[(1,[z0,z2,z3,z4,z28,z6]),(0,[z0,z2,z29,z3,z4,z30,z6])],[(0,[z15,z0,z31,z3,z4,z5,z6]),(1,[z0,z2,z32,z4,z5,z6]),(0,[z33,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z34])],[],[(0,[z0,z2,z3,z4,z5,z6,z35])]],
   [[(0,[z0,z2,z24,z4,z5,z13,z6]),(1,[z0,z24,z4,z5,z36,z6]),(0,[z0,z2,z3,z4,z5,z6,z37])],[(0,[z38,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z39,z5,z6]),(0,[z40,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z41,z6]),(0,[z42,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z43,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z6]),(0,[z45,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z46,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z47]),(0,[z48,z0,z2,z3,z4,z5,z6]),(0,[z18,z0,z49,z2,z4,z5,z6]),(0,[z0,z50,z51,z2,z4,z5,z6]),(0,[z0,z52,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z53,z5,z6]),(0,[z0,z2,z3,z5,z21,z6,z27]),(1,[z0,z2,z3,z20,z5,z21])],[(0,[z18,z54,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z55,z5,z6]),(0,[z0,z2,z3,z4,z5,z21,z6])],[(0,[z0,z2,z12,z3,z4,z5,z6]),(0,[z56,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z57,z6]),(0,[z0,z58,z49,z2,z4,z5,z6]),(0,[z0,z59,z2,z3,z4,z5,z6]),(0,[z0,z60,z2,z3,z4,z5,z6]),(0,[z61,z0,z2,z3,z4,z62,z6]),(0,[z0,z2,z29,z4,z62,z5,z6])],[(0,[z0,z2,z3,z63,z5,z6,z27]),(0,[z0,z2,z3,z64,z65,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z67]),(0,[z68,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z69,z4,z5,z6]),(0,[z0,z2,z3,z4,z70,z5,z6]),(0,[z71,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z72])],[(0,[z0,z73,z23,z2,z4,z5,z6]),(0,[z18,z22,z0,z2,z4,z5,z6]),(0,[z18,z0,z2,z4,z74,z5,z6]),(0,[z0,z2,z3,z4,z75,z5,z6]),(0,[z0,z76,z2,z3,z4,z5,z6]),(0,[z77,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z78,z2,z3,z4,z5,z6]),(0,[z0,z79,z2,z3,z4,z5,z6]),(0,[z0,z51,z2,z24,z4,z5,z6]),(0,[z80,z0,z2,z81,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z82,z6])],[(0,[z83,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z84,z4,z5,z6]),(0,[z85,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z86,z5,z6]),(0,[z0,z2,z3,z4,z87,z88,z6]),(0,[z0,z2,z3,z4,z5,z89,z6]),(0,[z90,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z91,z4,z5,z6]),(0,[z0,z92,z2,z3,z4,z5,z6])],[(0,[z18,z0,z2,z63,z4,z5,z6]),(0,[z0,z49,z2,z3,z93,z5,z6]),(0,[z0,z94,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z4,z5,z6])],[(0,[z0,z2,z3,z96,z4,z5,z6]),(0,[z97,z2,z3,z63,z4,z5,z6])],[(0,[z0,z98,z3,z24,z4,z5,z6])],[(0,[z2,z3,z63,z4,z5,z19,z6]),(0,[z0,z2,z3,z4,z5,z99,z6]),(0,[z18,z0,z2,z4,z25,z5,z6]),(0,[z18,z0,z2,z4,z5,z36,z6]),(0,[z0,z2,z100,z3,z4,z5,z6])],[(0,[z0,z23,z2,z3,z4,z5,z6]),(1,[z0,z73,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z101,z5,z6]),(0,[z80,z0,z2,z102,z4,z5,z6]),(1,[z0,z103,z3,z4,z5,z6]),(0,[z0,z2,z3,z104,z4,z5,z6])]],
   [[(0,[z0,z98,z2,z24,z4,z5,z6]),(0,[z0,z2,z24,z4,z105,z5,z6]),(0,[z0,z2,z3,z4,z5,z106,z6])],[(0,[z107,z54,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z108,z6]),(0,[z0,z2,z3,z109,z4,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z6]),(0,[z111,z0,z3,z4,z112,z5,z6]),(0,[z80,z0,z2,z3,z4,z113,z6]),(0,[z0,z114,z2,z3,z4,z5,z6])],[(0,[z15,z0,z2,z3,z4,z28,z6]),(0,[z0,z2,z3,z4,z115,z5,z6]),(0,[z7,z0,z2,z3,z116,z5,z6]),(0,[z117,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z24,z4,z5,z30,z6]),(0,[z7,z18,z0,z2,z4,z5,z6]),(1,[z33,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z118,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z120,z5,z6]),(0,[z66,z0,z2,z3,z4,z87,z6])],[(0,[z121,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z101,z5,z6,z27]),(0,[z0,z2,z24,z122,z4,z5,z6]),(0,[z0,z123,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z124,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z125,z6]),(0,[z0,z2,z3,z4,z126,z5,z6]),(0,[z0,z2,z3,z64,z4,z65,z6]),(0,[z0,z2,z3,z4,z5,z6,z127]),(0,[z128,z0,z2,z3,z4,z5,z6])],[(0,[z129,z2,z12,z3,z4,z5,z6]),(0,[z0,z2,z130,z3,z4,z5,z6]),(0,[z0,z131,z2,z3,z4,z5,z6]),(0,[z107,z22,z2,z3,z4,z5,z6]),(0,[z132,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z133,z5,z6]),(0,[z18,z0,z2,z2,z4,z5,z6]),(0,[z0,z2,z3,z81,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z134,z6]),(0,[z0,z2,z3,z4,z135,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z136]),(0,[z61,z0,z2,z3,z137,z5,z6])],[(0,[z0,z2,z3,z4,z5,z138,z6]),(0,[z139,z0,z2,z3,z4,z5,z6]),(0,[z140,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z111,z0,z23,z3,z4,z5,z6]),(0,[z0,z141,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z142]),(0,[z111,z0,z3,z4,z5,z36,z6]),(0,[z0,z2,z3,z4,z5,z6,z143])],[(0,[z0,z2,z3,z4,z144,z5,z6]),(0,[z0,z23,z2,z3,z145,z5,z6]),(0,[z18,z0,z2,z146,z4,z5,z6]),(0,[z18,z0,z2,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z87,z5,z6])],[(0,[z0,z147,z2,z3,z4,z5,z6]),(0,[z121,z2,z3,z4,z5,z13,z6]),(0,[z148,z0,z2,z3,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z21,z6])],[(0,[z0,z2,z3,z149,z4,z5,z6]),(0,[z80,z0,z2,z3,z4,z5,z150]),(0,[z0,z151,z2,z3,z4,z5,z6]),(0,[z152,z0,z153,z2,z4,z5,z6]),(0,[z0,z154,z2,z3,z4,z5,z6]),(1,[z0,z58,z2,z93,z5,z6]),(0,[z0,z2,z3,z4,z155,z5,z6])],[(0,[z156,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z157,z6]),(0,[z0,z2,z3,z5,z6,z158,z17]),(0,[z0,z2,z24,z4,z88,z5,z6]),(0,[z0,z51,z2,z3,z4,z5,z6]),(0,[z80,z0,z3,z4,z5,z113,z6]),(0,[z0,z2,z3,z4,z5,z159,z6]),(0,[z0,z2,z3,z160,z4,z5,z6])],[(0,[z0,z2,z24,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z162,z5,z6]),(0,[z0,z2,z3,z163,z4,z5,z6]),(0,[z18,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z5,z164,z6]),(0,[z0,z2,z3,z165,z64,z5,z6]),(0,[z0,z2,z3,z4,z5,z150,z6]),(1,[z80,z0,z3,z4,z113,z6])],[(0,[z166,z0,z2,z3,z4,z5,z6]),(0,[z167,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z168])],[(0,[z0,z2,z24,z4,z5,z169,z6]),(0,[z111,z0,z98,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z8,z170]),(0,[z171,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z172,z0,z2,z3,z4,z5,z6]),(1,[z0,z173,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z169,z10])],[(0,[z0,z2,z3,z4,z5,z174,z6]),(0,[z175,z176,z2,z3,z4,z5,z6]),(1,[z177,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z137,z5,z6]),(0,[z178,z0,z2,z3,z4,z5,z6])],[(1,[z179,z12,z3,z4,z5,z6]),(0,[z0,z73,z2,z3,z4,z5,z6]),(0,[z18,z129,z0,z2,z4,z5,z6]),(0,[z180,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z181,z6])],[(0,[z182,z0,z2,z3,z4,z5,z6]),(0,[z0,z183,z2,z3,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z6,z17]),(0,[z0,z2,z3,z4,z5,z6,z184]),(0,[z0,z2,z3,z4,z5,z6,z185])],[(0,[z0,z2,z3,z186,z4,z5,z6]),(0,[z0,z187,z2,z3,z4,z5,z6])],[(0,[z111,z0,z12,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z188,z6]),(0,[z0,z2,z3,z165,z4,z5,z6])],[(0,[z189,z190,z0,z2,z3,z5,z6]),(0,[z18,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z191,z4,z5,z6]),(1,[z189,z0,z2,z3,z5,z27]),(0,[z0,z192,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z54,z0,z2,z161,z4,z5,z6]),(1,[z0,z2,z16,z4,z5,z6]),(0,[z0,z1,z2,z24,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z106,z6]),(0,[z0,z2,z3,z4,z5,z6,z193])]],
   [[(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z0,z194,z2,z3,z4,z5,z6]),(0,[z54,z0,z195,z2,z4,z5,z6]),(0,[z0,z2,z31,z3,z4,z5,z6]),(1,[z196,z0,z2,z3,z5,z6]),(0,[z0,z2,z197,z3,z4,z5,z6]),(0,[z0,z2,z198,z3,z4,z5,z6])],[(0,[z15,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z165,z20,z5,z6]),(0,[z0,z2,z3,z4,z199,z5,z6]),(0,[z0,z200,z2,z3,z4,z5,z6])],[(0,[z179,z2,z12,z3,z4,z5,z6]),(0,[z0,z2,z201,z3,z4,z5,z6]),(0,[z202,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z203,z6]),(0,[z0,z2,z3,z4,z5,z204,z6]),(1,[z0,z31,z3,z4,z5,z6]),(0,[z0,z2,z3,z205,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z3,z4,z5,z6,z207])],[(0,[z54,z0,z2,z24,z4,z5,z6]),(0,[z129,z0,z2,z3,z4,z5,z19]),(0,[z18,z0,z153,z2,z4,z5,z6]),(0,[z208,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z209,z5,z6]),(0,[z0,z2,z3,z65,z5,z210,z6]),(0,[z211,z0,z2,z3,z4,z5,z6])],[(0,[z212,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z213,z6]),(0,[z0,z2,z3,z4,z5,z113,z6])],[(0,[z214,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z19,z6]),(1,[z0,z2,z3,z4,z5,z150])],[(0,[z215,z0,z2,z3,z4,z5,z6])],[(0,[z15,z0,z216,z3,z4,z5,z6]),(0,[z0,z217,z2,z3,z4,z5,z6]),(0,[z218,z0,z2,z3,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z6,z8]),(0,[z0,z2,z3,z4,z5,z6,z219]),(0,[z220,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z222,z3,z4,z5,z6]),(0,[z0,z223,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z224,z4,z5,z6]),(0,[z0,z225,z2,z3,z4,z5,z6])],[(1,[z0,z226,z3,z4,z5,z6]),(0,[z0,z227,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z228,z6])],[(0,[z0,z2,z3,z4,z229,z5,z6]),(0,[z230,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z231,z6]),(0,[z0,z2,z3,z4,z5,z6,z232]),(0,[z0,z2,z3,z233,z4,z5,z6])],[(0,[z0,z2,z12,z24,z4,z5,z6]),(0,[z0,z3,z24,z4,z5,z36,z6]),(0,[z111,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z234,z3,z4,z5,z6])],[(0,[z0,z2,z3,z235,z4,z5,z6]),(0,[z0,z2,z236,z3,z4,z5,z6]),(0,[z0,z237,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z169,z170]),(0,[z238,z0,z2,z3,z4,z5,z6])],[(0,[z0,z12,z3,z24,z4,z5,z6]),(0,[z0,z2,z3,z239,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z240,z6]),(0,[z22,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z165,z5,z210,z6]),(1,[z68,z0,z2,z4,z5,z6])],[(0,[z189,z97,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z241,z5,z6]),(0,[z0,z2,z3,z4,z5,z242,z6]),(0,[z0,z2,z3,z4,z5,z243,z6]),(0,[z0,z2,z3,z4,z244,z5,z6]),(0,[z71,z2,z3,z4,z5,z6,z27])],[(0,[z0,z245,z2,z3,z4,z5,z6]),(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z247]),(1,[z7,z0,z3,z4,z5,z8]),(0,[z0,z2,z3,z248,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z249,z6])]],
   [[(0,[z2,z12,z3,z63,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z250,z6]),(0,[z0,z2,z3,z251,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z252]),(0,[z253,z18,z0,z2,z4,z5,z6]),(0,[z254,z0,z2,z3,z4,z5,z6]),(0,[z0,z177,z2,z3,z4,z5,z6]),(0,[z255,z0,z2,z3,z4,z5,z6]),(0,[z61,z0,z60,z3,z4,z5,z6]),(0,[z0,z2,z256,z3,z4,z5,z6])],[(0,[z0,z153,z12,z3,z4,z5,z6]),(0,[z0,z257,z2,z3,z4,z5,z6]),(0,[z0,z258,z2,z3,z4,z5,z6])],[(0,[z2,z3,z63,z4,z101,z5,z6]),(0,[z259,z0,z2,z24,z4,z5,z6]),(0,[z18,z0,z2,z20,z4,z5,z6]),(0,[z0,z50,z2,z3,z4,z5,z6]),(0,[z260,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z261,z6])],[(0,[z0,z23,z3,z24,z4,z5,z6]),(0,[z0,z2,z3,z32,z4,z5,z6]),(0,[z0,z49,z2,z4,z62,z5,z6]),(0,[z262,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z263,z6]),(0,[z0,z2,z3,z4,z5,z6,z264]),(0,[z0,z2,z3,z4,z265,z5,z6]),(1,[z0,z24,z4,z112,z5,z6]),(0,[z266,z18,z0,z2,z4,z5,z6]),(0,[z267,z0,z2,z3,z4,z5,z6]),(0,[z80,z268,z2,z3,z4,z5,z6]),(0,[z269,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z270,z4,z5,z6]),(0,[z0,z2,z3,z271,z4,z5,z6]),(0,[z15,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z24,z63,z4,z5,z6]),(0,[z272,z0,z2,z3,z4,z5,z6]),(0,[z61,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z273,z4,z5,z6])],[(0,[z274,z0,z2,z3,z4,z5,z6]),(0,[z54,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z161,z4,z5,z6,z275]),(0,[z111,z0,z276,z3,z4,z5,z6]),(0,[z80,z0,z2,z3,z277,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z278])]],
   [[(0,[z0,z279,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z280,z6]),(0,[z0,z2,z281,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z282]),(0,[z0,z2,z3,z4,z283,z5,z6]),(0,[z0,z2,z24,z4,z25,z5,z6]),(0,[z0,z2,z24,z4,z5,z36,z6]),(0,[z0,z2,z3,z4,z284,z5,z6]),(0,[z0,z2,z3,z4,z5,z285,z6]),(0,[z0,z2,z3,z4,z5,z6,z170])],[(0,[z0,z2,z286,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z287,z6]),(0,[z0,z2,z3,z4,z5,z288,z6])],[(0,[z179,z0,z12,z3,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z113,z6]),(0,[z0,z3,z4,z5,z36,z6,z8]),(0,[z0,z2,z3,z4,z5,z6,z289])],[(0,[z121,z179,z2,z3,z4,z5,z6]),(0,[z0,z290,z2,z3,z4,z5,z6]),(0,[z0,z2,z291,z3,z4,z5,z6]),(1,[z0,z175,z24,z4,z5,z6]),(0,[z80,z0,z2,z24,z4,z5,z6]),(0,[z292,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z277,z5,z6]),(0,[z0,z2,z3,z4,z5,z293,z6]),(0,[z0,z2,z3,z69,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z294,z6]),(0,[z18,z0,z2,z4,z5,z6,z8]),(0,[z295,z0,z2,z3,z4,z5,z6]),(0,[z0,z296,z2,z3,z4,z5,z6]),(0,[z189,z0,z2,z3,z5,z6,z27]),(0,[z0,z2,z3,z4,z5,z6,z297])],[(0,[z230,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z298,z6])],[(0,[z299,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z300,z5,z6]),(1,[z180,z0,z2,z3,z210,z6]),(0,[z0,z2,z301,z3,z4,z5,z6])]],
   [[(0,[z80,z0,z2,z3,z4,z88,z6]),(0,[z7,z0,z2,z69,z4,z5,z6]),(0,[z0,z302,z2,z3,z4,z5,z6]),(1,[z0,z303,z2,z4,z5,z6])],[(0,[z0,z2,z3,z304,z4,z5,z6]),(0,[z0,z2,z3,z4,z305,z5,z6]),(0,[z0,z2,z3,z306,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z307]),(0,[z18,z0,z308,z2,z4,z5,z6]),(0,[z18,z0,z2,z4,z112,z5,z6]),(0,[z0,z2,z3,z4,z5,z309,z6]),(0,[z61,z0,z2,z93,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z310,z6])],[(0,[z0,z98,z3,z4,z88,z5,z6]),(0,[z0,z2,z3,z4,z311,z5,z6])],[(0,[z0,z312,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z313,z6]),(1,[z0,z2,z3,z314,z5,z6])],[(0,[z0,z2,z3,z4,z315,z5,z6]),(0,[z0,z2,z24,z4,z5,z21,z6]),(0,[z111,z0,z3,z4,z5,z113,z6])],[(0,[z259,z0,z2,z3,z4,z5,z6]),(0,[z23,z2,z12,z3,z4,z5,z6]),(0,[z54,z2,z3,z161,z4,z5,z6]),(1,[z268,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z316,z5,z6])],[(0,[z0,z317,z2,z3,z4,z5,z6]),(0,[z33,z175,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z318,z5,z6])]],
   [[(0,[z2,z12,z3,z4,z5,z6,z17]),(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z18,z97,z0,z2,z4,z5,z6]),(0,[z320,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z321]),(0,[z0,z2,z24,z4,z62,z5,z6]),(0,[z0,z2,z103,z3,z4,z5,z6]),(1,[z0,z60,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z10])],[(0,[z322,z0,z2,z3,z4,z5,z6]),(0,[z18,z0,z2,z64,z4,z5,z6]),(1,[z0,z2,z3,z277,z5,z6])],[(0,[z179,z0,z147,z2,z4,z5,z6]),(0,[z0,z2,z323,z3,z4,z5,z6]),(0,[z0,z324,z2,z3,z4,z5,z6]),(0,[z0,z175,z2,z3,z165,z5,z6]),(0,[z0,z325,z2,z3,z4,z5,z6]),(0,[z61,z0,z2,z3,z4,z5,z6])],[(0,[z0,z326,z2,z3,z4,z5,z6]),(0,[z327,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z328,z4,z5,z6]),(0,[z0,z2,z3,z4,z87,z10,z6])],[(1,[z190,z2,z3,z101,z5,z6]),(0,[z0,z329,z2,z3,z4,z5,z6])],[(0,[z330,z0,z2,z3,z4,z5,z6]),(0,[z190,z2,z3,z4,z5,z19,z6]),(0,[z0,z2,z3,z4,z5,z331,z6]),(0,[z0,z2,z3,z93,z64,z5,z6])],[(0,[z0,z2,z24,z4,z5,z6,z17]),(1,[z0,z2,z24,z4,z5,z6]),(1,[z295,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z36,z170]),(0,[z0,z2,z4,z62,z5,z30,z6]),(0,[z0,z2,z332,z3,z4,z5,z275])],[(0,[z40,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z333,z0,z2,z3,z4,z5,z6]),(0,[z121,z2,z3,z63,z4,z5,z6]),(0,[z0,z334,z2,z3,z4,z5,z6]),(0,[z0,z335,z2,z3,z4,z5,z6]),(0,[z189,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z336]),(0,[z80,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z337,z6]),(0,[z0,z3,z4,z88,z5,z113,z6]),(0,[z0,z338,z2,z3,z4,z5,z6])],[(0,[z0,z2,z24,z4,z101,z5,z6]),(0,[z0,z339,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z340,z6])],[(0,[z341,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z342,z6]),(0,[z0,z2,z3,z4,z5,z343,z6]),(0,[z0,z2,z3,z344,z4,z5,z6]),(0,[z190,z18,z0,z2,z4,z5,z6]),(0,[z345,z0,z2,z3,z4,z5,z6]),(0,[z346,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z347,z6]),(0,[z97,z0,z2,z3,z165,z5,z6]),(0,[z0,z2,z348,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z87,z13,z6]),(1,[z0,z216,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z285])],[(0,[z349,z0,z2,z3,z4,z5,z6]),(1,[z121,z23,z3,z4,z5,z6]),(0,[z350,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z351,z6]),(0,[z0,z2,z3,z93,z4,z5,z6])],[(0,[z352,z0,z2,z3,z4,z5,z6]),(0,[z0,z353,z2,z3,z4,z5,z6]),(0,[z354,z0,z2,z3,z4,z5,z6]),(0,[z355,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z356]),(1,[z71,z2,z3,z4,z5,z6])],[(0,[z0,z2,z24,z4,z133,z5,z6])]],
   [[(1,[z129,z2,z3,z4,z5,z19]),(0,[z0,z98,z2,z357,z4,z5,z6]),(0,[z0,z2,z3,z358,z4,z5,z6]),(0,[z359,z0,z2,z3,z4,z5,z6])],[(0,[z18,z0,z23,z2,z4,z5,z6]),(0,[z360,z0,z2,z3,z4,z5,z6]),(0,[z0,z361,z2,z3,z4,z5,z6]),(0,[z0,z2,z173,z3,z4,z5,z6])],[(0,[z0,z2,z3,z362,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z363]),(0,[z7,z177,z2,z3,z4,z5,z6]),(1,[z0,z49,z2,z118,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z364]),(0,[z0,z365,z2,z3,z4,z5,z6])],[(0,[z22,z0,z2,z24,z4,z5,z6]),(0,[z0,z366,z2,z3,z4,z5,z6]),(0,[z367,z0,z2,z3,z4,z5,z6])],[(0,[z368,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z13,z6,z170]),(0,[z0,z268,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z369]),(0,[z0,z2,z3,z4,z370,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z371]),(0,[z0,z175,z2,z3,z112,z5,z6]),(0,[z61,z0,z2,z3,z224,z5,z6])],[(0,[z0,z2,z3,z4,z145,z5,z6]),(0,[z15,z0,z2,z3,z4,z5,z17]),(0,[z0,z372,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z373,z4,z5,z6]),(0,[z0,z2,z3,z374,z4,z5,z6])]],
   [[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z23,z153,z3,z4,z5,z6]),(0,[z0,z2,z3,z375,z4,z5,z6]),(0,[z22,z2,z3,z4,z25,z5,z6]),(0,[z0,z3,z24,z4,z5,z113,z6])],[(0,[z0,z2,z3,z4,z5,z6,z376]),(0,[z18,z0,z2,z4,z101,z5,z6]),(0,[z196,z0,z2,z3,z5,z6,z17]),(0,[z7,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z377]),(0,[z121,z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z378,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z379,z6]),(0,[z380,z0,z2,z3,z4,z5,z6])],[(0,[z381,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z382,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z65,z5,z6])],[(0,[z383,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z384,z6]),(0,[z66,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z385,z3,z4,z5,z6]),(0,[z0,z386,z2,z3,z4,z5,z6])],[(0,[z387,z0,z2,z3,z4,z5,z6]),(0,[z15,z2,z3,z63,z4,z5,z6]),(0,[z0,z2,z24,z20,z4,z5,z6]),(0,[z18,z0,z2,z4,z118,z5,z6]),(0,[z7,z0,z2,z3,z4,z5,z36]),(0,[z0,z2,z3,z93,z5,z210,z6]),(0,[z0,z2,z3,z4,z5,z210,z6])],[(0,[z0,z2,z3,z4,z5,z388,z6]),(0,[z0,z389,z2,z3,z4,z5,z6]),(0,[z390,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z36]),(0,[z0,z2,z3,z4,z5,z6,z27])],[(0,[z0,z2,z3,z4,z391,z5,z6]),(0,[z392,z0,z2,z3,z4,z5,z6]),(0,[z97,z0,z2,z3,z112,z5,z6]),(0,[z0,z393,z2,z3,z4,z5,z6]),(0,[z0,z3,z24,z4,z112,z5,z6]),(0,[z61,z394,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z395,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z396])]],
   [[(0,[z121,z2,z3,z4,z5,z6,z17]),(0,[z0,z2,z3,z397,z4,z5,z6]),(0,[z398,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z399,z5,z6]),(0,[z0,z2,z3,z4,z5,z400,z6]),(0,[z0,z2,z3,z4,z5,z401,z6])],[(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z403,z6]),(0,[z0,z2,z4,z5,z169,z6,z275])],[(0,[z190,z0,z2,z3,z165,z5,z6]),(0,[z0,z2,z3,z63,z20,z5,z6]),(0,[z404,z0,z2,z3,z4,z5,z6]),(0,[z0,z405,z2,z3,z4,z5,z6]),(0,[z406,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z226,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z5,z13,z6]),(0,[z18,z0,z2,z4,z87,z5,z6]),(0,[z61,z0,z2,z4,z5,z30,z6])],[(0,[z121,z0,z23,z3,z4,z5,z6]),(1,[z0,z2,z3,z145,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z407]),(0,[z0,z2,z3,z4,z5,z408,z6]),(0,[z409,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z410,z5,z6]),(0,[z411,z0,z2,z3,z4,z5,z6]),(0,[z15,z190,z2,z3,z4,z5,z6]),(0,[z412,z0,z2,z24,z4,z5,z6]),(1,[z0,z2,z332,z4,z5,z169]),(0,[z413,z0,z2,z3,z4,z5,z6])],[(0,[z190,z2,z12,z3,z4,z5,z6]),(0,[z0,z414,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z415,z5,z6]),(0,[z22,z0,z2,z3,z4,z25,z6]),(0,[z0,z2,z24,z4,z5,z113,z6]),(0,[z0,z2,z24,z4,z5,z6,z416]),(1,[z0,z2,z29,z4,z62,z6])],[(0,[z111,z0,z175,z3,z4,z5,z6]),(0,[z417,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z418,z4,z5,z6]),(0,[z0,z58,z2,z3,z118,z5,z6]),(0,[z0,z419,z2,z3,z4,z5,z6])]],
   [[(0,[z22,z0,z2,z3,z4,z13,z6]),(1,[z0,z24,z4,z5,z113,z6]),(0,[z0,z2,z24,z4,z5,z6,z8]),(0,[z0,z302,z49,z3,z4,z5,z6])],[(0,[z107,z0,z195,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z420,z6]),(0,[z0,z2,z3,z165,z5,z6,z27]),(0,[z421,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z422,z6])],[(0,[z0,z2,z3,z423,z4,z5,z6]),(0,[z0,z424,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z425,z5,z6])],[(0,[z0,z2,z3,z426,z4,z5,z6]),(0,[z427,z0,z2,z3,z4,z5,z6]),(0,[z428,z0,z2,z3,z4,z5,z6]),(0,[z429,z0,z2,z3,z4,z5,z6]),(0,[z0,z430,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z431,z6]),(0,[z0,z2,z3,z4,z5,z6,z158])],[(0,[z0,z2,z24,z4,z112,z5,z6]),(0,[z432,z0,z2,z3,z4,z5,z6]),(0,[z0,z433,z2,z3,z4,z5,z6]),(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z0,z332,z173,z3,z4,z5,z6]),(0,[z0,z435,z2,z3,z4,z5,z6])],[(0,[z190,z97,z2,z3,z4,z5,z6]),(0,[z129,z0,z2,z24,z4,z5,z6]),(1,[z0,z2,z3,z224,z5,z6]),(0,[z436,z0,z2,z3,z4,z5,z6])],[(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z438,z3,z4,z5,z6]),(0,[z0,z439,z2,z3,z4,z5,z6]),(0,[z18,z0,z2,z165,z4,z5,z6]),(0,[z440,z0,z2,z3,z4,z5,z6]),(0,[z441,z0,z2,z3,z4,z5,z6]),(0,[z442,z0,z2,z3,z4,z5,z6]),(0,[z212,z0,z2,z3,z4,z5,z275]),(0,[z0,z2,z3,z4,z5,z6,z443])]],
   [[(0,[z0,z2,z3,z444,z4,z5,z6]),(0,[z0,z2,z3,z4,z445,z5,z6]),(0,[z0,z2,z3,z4,z446,z5,z6]),(1,[z0,z2,z447,z4,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z448,z0,z2,z3,z4,z5,z6]),(0,[z190,z2,z3,z4,z101,z5,z6]),(1,[z0,z2,z3,z449,z5,z6]),(0,[z0,z324,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z450,z4,z5,z6])],[(0,[z0,z2,z3,z4,z451,z5,z6]),(0,[z107,z2,z3,z4,z5,z13,z6]),(0,[z97,z0,z2,z3,z5,z21,z6]),(0,[z0,z2,z3,z4,z25,z6,z170]),(0,[z0,z2,z3,z4,z452,z5,z6]),(0,[z0,z2,z3,z4,z314,z5,z6]),(0,[z212,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z453,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z105,z5,z6]),(0,[z0,z303,z2,z3,z4,z5,z6])],[(0,[z0,z2,z332,z161,z4,z5,z6]),(0,[z0,z454,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z64,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z210,z6]),(0,[z0,z2,z455,z3,z4,z5,z6])],[(0,[z121,z129,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z456,z4,z5,z6]),(0,[z457,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z458]),(0,[z18,z0,z58,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z459,z5,z6]),(0,[z190,z0,z2,z3,z112,z5,z6]),(0,[z460,z0,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z24,z4,z5,z6]),(0,[z461,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z30,z6]),(0,[z0,z2,z332,z4,z5,z169,z6]),(0,[z0,z2,z3,z20,z5,z21,z6])],[(0,[z22,z2,z3,z161,z4,z5,z6]),(0,[z0,z2,z3,z4,z462,z5,z6]),(0,[z0,z2,z3,z122,z4,z5,z6]),(0,[z0,z2,z3,z463,z4,z5,z6]),(0,[z0,z2,z3,z4,z464,z5,z6]),(1,[z394,z2,z3,z4,z5,z6]),(0,[z61,z0,z2,z3,z4,z5,z285])]],
   [[(0,[z18,z0,z276,z2,z4,z5,z6]),(0,[z0,z2,z332,z24,z4,z5,z6]),(0,[z0,z175,z51,z3,z4,z5,z6]),(0,[z0,z2,z93,z4,z62,z5,z6]),(0,[z465,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z466,z6]),(1,[z0,z2,z3,z5,z6,z158]),(0,[z111,z0,z2,z3,z4,z5,z6]),(0,[z412,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z467,z6]),(0,[z0,z2,z3,z4,z5,z468,z6]),(1,[z2,z3,z4,z5,z6,z469]),(0,[z470,z0,z2,z3,z4,z5,z6])],[(0,[z471,z0,z2,z3,z4,z5,z6]),(0,[z18,z472,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z473,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z474,z6]),(0,[z0,z2,z3,z4,z5,z475,z6]),(0,[z476,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z6,z170]),(0,[z0,z49,z2,z4,z118,z5,z6]),(0,[z0,z303,z2,z4,z5,z210,z6]),(0,[z0,z2,z3,z4,z5,z477,z6])],[(0,[z0,z2,z3,z4,z5,z478,z6]),(0,[z0,z2,z3,z4,z5,z479,z6]),(0,[z0,z2,z3,z4,z480,z5,z6]),(0,[z40,z2,z3,z4,z5,z13,z6]),(0,[z0,z2,z3,z4,z5,z481,z6])],[(0,[z0,z2,z3,z4,z5,z6,z482])],[(0,[z97,z0,z2,z3,z101,z5,z6]),(0,[z0,z2,z102,z3,z4,z5,z6]),(0,[z7,z0,z2,z3,z314,z5,z6]),(0,[z483,z0,z2,z3,z4,z5,z6])],[(0,[z121,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z484,z3,z4,z5,z6]),(0,[z0,z2,z3,z485,z4,z5,z6])]],
   [[(0,[z107,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z161,z4,z5,z6]),(0,[z0,z2,z486,z3,z4,z5,z6]),(0,[z0,z175,z3,z165,z4,z5,z6]),(1,[z0,z2,z3,z4,z487,z6]),(1,[z488,z2,z3,z4,z5,z6]),(0,[z0,z2,z332,z3,z4,z5,z169])],[(0,[z0,z2,z3,z4,z5,z489,z6]),(0,[z0,z2,z3,z4,z5,z6,z490])],[(0,[z0,z23,z3,z4,z5,z6,z8]),(0,[z0,z2,z3,z4,z491,z5,z6]),(0,[z0,z2,z3,z4,z5,z492,z6]),(0,[z129,z0,z2,z3,z4,z5,z6]),(0,[z266,z0,z2,z3,z4,z5,z6]),(0,[z493,z0,z2,z3,z4,z5,z6]),(1,[z61,z0,z2,z4,z30,z6]),(0,[z0,z2,z3,z4,z5,z169,z6])],[(0,[z0,z2,z3,z4,z494,z5,z6]),(0,[z0,z49,z2,z3,z118,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z495]),(0,[z0,z2,z3,z4,z496,z5,z6]),(0,[z497,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z24,z4,z5,z6]),(1,[z0,z175,z3,z165,z5,z6])],[(1,[z107,z195,z2,z4,z5,z6]),(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z7,z0,z3,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z499]),(0,[z61,z0,z49,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z275,z170]),(0,[z180,z0,z2,z3,z4,z65,z6])],[(0,[z0,z175,z52,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z6,z170])],[(0,[z54,z0,z194,z3,z4,z5,z6]),(0,[z0,z2,z3,z500,z4,z5,z6]),(0,[z0,z216,z2,z3,z4,z5,z6]),(0,[z15,z0,z2,z3,z449,z5,z6]),(0,[z0,z2,z2,z24,z4,z5,z6]),(0,[z221,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z501,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z502]),(0,[z503,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z504,z5,z6]),(0,[z0,z505,z2,z3,z4,z5,z6])]],
   [[(0,[z506,z0,z2,z3,z4,z5,z6]),(0,[z507,z0,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z25,z6]),(0,[z7,z0,z2,z24,z4,z5,z6]),(0,[z7,z295,z2,z3,z4,z5,z6]),(0,[z508,z0,z2,z3,z4,z5,z6])],[(0,[z190,z0,z2,z3,z5,z21,z6]),(0,[z0,z2,z3,z4,z5,z487,z6]),(0,[z212,z0,z2,z332,z4,z5,z6]),(1,[z421,z0,z3,z4,z5,z6])],[(0,[z190,z121,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z13,z6]),(0,[z0,z2,z3,z4,z5,z509,z6]),(0,[z0,z98,z2,z3,z4,z113,z6]),(0,[z0,z2,z3,z510,z4,z5,z6]),(0,[z0,z511,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z512]),(0,[z18,z0,z2,z4,z5,z6,z170]),(0,[z0,z51,z2,z3,z165,z5,z6]),(0,[z0,z2,z3,z513,z4,z5,z6]),(0,[z0,z2,z29,z3,z4,z62,z6])],[(0,[z0,z2,z3,z4,z5,z514,z6]),(0,[z0,z2,z332,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z275]),(0,[z0,z2,z3,z4,z5,z6,z515])],[(0,[z0,z2,z516,z3,z4,z5,z6]),(0,[z0,z2,z517,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z518]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z519,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z520]),(0,[z80,z0,z2,z3,z450,z5,z6]),(0,[z0,z2,z3,z521,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z472,z0,z2,z3,z4,z5,z6]),(0,[z522,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z523,z0,z2,z3,z4,z5,z6]),(0,[z524,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z28,z5,z6]),(0,[z0,z2,z24,z4,z118,z5,z6]),(0,[z0,z2,z3,z4,z88,z6,z170])],[(0,[z0,z2,z3,z4,z5,z525,z6]),(0,[z526,z0,z2,z3,z4,z5,z6]),(0,[z0,z405,z2,z24,z4,z5,z6]),(0,[z0,z527,z2,z3,z4,z5,z6]),(0,[z0,z153,z2,z3,z4,z5,z36])],[(1,[z176,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z528,z6]),(0,[z0,z2,z3,z4,z529,z5,z6]),(0,[z0,z530,z2,z3,z4,z5,z6])],[(0,[z0,z2,z531,z3,z4,z5,z6])],[(0,[z15,z18,z0,z2,z4,z5,z6]),(0,[z0,z51,z3,z4,z112,z5,z6]),(1,[z0,z302,z3,z4,z5,z6])],[(0,[z190,z0,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z532]),(0,[z0,z276,z3,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z533]),(0,[z534,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z535,z24,z4,z5,z6]),(0,[z0,z2,z24,z4,z87,z5,z6]),(1,[z0,z2,z357,z4,z5,z6]),(0,[z0,z2,z29,z3,z4,z5,z6])],[(0,[z179,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z536,z4,z5,z6]),(0,[z0,z2,z3,z4,z537,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z170]),(0,[z0,z2,z3,z4,z87,z5,z10])]],
   [[(0,[z18,z0,z195,z2,z4,z5,z6]),(0,[z0,z276,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z538]),(0,[z0,z2,z3,z4,z5,z6,z539]),(0,[z61,z0,z2,z3,z4,z30,z6])],[(0,[z540,z0,z2,z3,z4,z5,z6])],[(0,[z541,z0,z2,z3,z4,z5,z6]),(1,[z18,z0,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z275])],[(0,[z97,z0,z2,z3,z63,z5,z6]),(0,[z542,z0,z2,z3,z4,z5,z6]),(0,[z18,z0,z98,z2,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z185])],[(0,[z0,z543,z2,z3,z4,z5,z6]),(0,[z48,z18,z0,z2,z4,z5,z6]),(0,[z544,z0,z2,z3,z4,z5,z6]),(0,[z61,z0,z2,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z545]),(0,[z0,z2,z3,z4,z5,z546,z6])],[(0,[z0,z2,z3,z4,z74,z5,z6]),(0,[z0,z2,z3,z112,z5,z210,z6]),(0,[z0,z2,z3,z4,z5,z547,z6]),(0,[z0,z2,z3,z4,z5,z6,z548]),(0,[z421,z0,z332,z3,z4,z5,z6]),(0,[z0,z549,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z6])],[(0,[z80,z0,z2,z3,z4,z5,z550]),(0,[z394,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z16,z3,z4,z5,z6]),(0,[z0,z51,z2,z32,z4,z5,z6]),(0,[z0,z51,z2,z3,z112,z5,z6]),(0,[z152,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z551,z5,z6]),(0,[z0,z2,z3,z4,z552,z5,z6]),(0,[z0,z2,z3,z4,z5,z553,z6])]],
   [[(1,[z0,z2,z3,z450,z5,z6])],[(1,[z0,z2,z554,z4,z5,z6]),(0,[z0,z2,z3,z63,z4,z5,z6]),(0,[z212,z0,z2,z24,z4,z5,z6]),(0,[z555,z0,z2,z3,z4,z5,z6]),(0,[z556,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z557]),(0,[z0,z2,z3,z4,z5,z6,z558])],[(0,[z15,z0,z2,z163,z4,z5,z6]),(0,[z0,z2,z24,z165,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z188,z6]),(1,[z0,z51,z3,z112,z5,z6]),(0,[z189,z0,z2,z3,z20,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z559])],[(0,[z0,z195,z2,z332,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z6,z275]),(0,[z0,z2,z3,z4,z560,z5,z6]),(0,[z0,z2,z3,z4,z5,z561,z6]),(0,[z180,z0,z2,z3,z64,z5,z6])],[(0,[z0,z23,z2,z91,z4,z5,z6]),(0,[z562,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z25,z5,z6]),(0,[z18,z0,z2,z4,z5,z6,z518]),(0,[z0,z2,z3,z4,z113,z6,z170]),(0,[z0,z2,z3,z4,z5,z36,z6])],[(0,[z0,z2,z3,z4,z563,z5,z6]),(0,[z0,z2,z24,z4,z65,z5,z6]),(0,[z259,z18,z0,z2,z4,z5,z6]),(0,[z80,z246,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z418,z4,z5,z6]),(0,[z180,z0,z2,z3,z4,z210,z6]),(0,[z564,z0,z2,z3,z4,z5,z6])],[(0,[z121,z23,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z565,z5,z6]),(0,[z0,z2,z3,z566,z4,z5,z6]),(0,[z0,z2,z3,z20,z112,z5,z6]),(0,[z0,z567,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z568])],[(0,[z569,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z449,z5,z6]),(0,[z0,z2,z24,z4,z5,z210,z6]),(0,[z18,z0,z2,z93,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z570,z5,z6]),(1,[z0,z2,z3,z4,z57,z6]),(0,[z111,z0,z2,z24,z4,z5,z6]),(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z572])],[(0,[z61,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z573,z5,z6]),(0,[z0,z176,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z574]),(0,[z0,z58,z2,z93,z4,z5,z6]),(0,[z212,z0,z2,z3,z4,z5,z169]),(0,[z212,z0,z2,z4,z5,z6,z275])],[(0,[z196,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z535,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z575])],[(0,[z107,z0,z2,z161,z4,z5,z6]),(0,[z195,z2,z3,z161,z4,z5,z6]),(0,[z0,z576,z2,z3,z4,z5,z6]),(0,[z61,z488,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z577,z6]),(0,[z180,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z87,z5,z170])],[(0,[z129,z0,z2,z3,z4,z5,z17]),(0,[z0,z276,z2,z3,z4,z5,z6]),(0,[z0,z175,z3,z24,z4,z5,z6]),(0,[z578,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z579,z6])],[(0,[z0,z2,z3,z580,z4,z5,z6]),(0,[z581,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z582]),(0,[z0,z2,z3,z4,z5,z583,z6])],[(0,[z54,z0,z201,z3,z4,z5,z6]),(0,[z0,z2,z3,z447,z4,z5,z6])],[(0,[z107,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z584,z3,z4,z5,z6]),(0,[z18,z0,z2,z3,z4,z5,z6]),(0,[z0,z175,z2,z24,z4,z5,z6]),(0,[z80,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z146,z4,z5,z6])]],
   [[(0,[z18,z0,z175,z2,z4,z5,z6]),(0,[z585,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z550]),(0,[z0,z2,z586,z3,z4,z5,z6]),(0,[z189,z0,z2,z3,z4,z5,z27])],[(0,[z0,z2,z3,z4,z5,z6,z587]),(0,[z0,z58,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z588,z6])],[(1,[z0,z194,z3,z4,z5,z6]),(0,[z190,z0,z2,z3,z63,z5,z6]),(0,[z0,z2,z3,z4,z25,z87,z6]),(0,[z0,z2,z3,z589,z4,z5,z6]),(0,[z0,z2,z24,z239,z4,z5,z6]),(0,[z7,z0,z153,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z590,z6]),(0,[z0,z2,z3,z4,z62,z5,z6]),(1,[z212,z0,z2,z4,z5,z275]),(1,[z0,z2,z3,z4,z87,z10])],[(0,[z121,z0,z12,z3,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z10,z6])],[(0,[z18,z0,z2,z4,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z591,z6]),(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z593,z5,z6])],[(0,[z0,z2,z3,z4,z5,z594,z6]),(0,[z595,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z469,z27]),(1,[z66,z0,z2,z3,z4,z170])],[(0,[z596,z0,z2,z3,z4,z5,z6]),(1,[z246,z2,z3,z4,z5,z6]),(0,[z597,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z598,z5,z6])]],
   [[(0,[z97,z0,z2,z24,z4,z5,z6]),(0,[z15,z2,z3,z4,z5,z6,z17]),(0,[z18,z0,z2,z4,z5,z6,z27]),(0,[z406,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z599,z6]),(0,[z189,z0,z2,z3,z4,z5,z21])],[(0,[z0,z2,z3,z4,z5,z6,z17]),(1,[z0,z276,z24,z4,z5,z6]),(0,[z0,z49,z2,z24,z4,z5,z6])],[(0,[z0,z600,z2,z3,z4,z5,z6]),(0,[z18,z0,z51,z2,z4,z5,z6]),(0,[z0,z2,z601,z3,z4,z5,z6])],[(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z0,z195,z2,z24,z4,z5,z6]),(0,[z7,z111,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z603,z5,z6]),(0,[z180,z0,z2,z3,z5,z210,z6]),(1,[z0,z2,z4,z5,z89,z6])],[(1,[z0,z2,z91,z4,z5,z6]),(0,[z0,z2,z604,z3,z4,z5,z6]),(0,[z0,z153,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z605])],[(0,[z18,z0,z2,z4,z5,z13,z6]),(0,[z0,z2,z3,z4,z606,z5,z6]),(0,[z18,z0,z2,z4,z565,z5,z6]),(0,[z0,z2,z3,z64,z112,z5,z6]),(0,[z0,z2,z3,z4,z5,z607,z6])],[(0,[z15,z0,z2,z3,z4,z57,z6]),(0,[z608,z0,z2,z3,z4,z5,z6]),(0,[z0,z609,z2,z3,z4,z5,z6])],[(0,[z0,z12,z3,z4,z5,z6,z8]),(0,[z0,z2,z3,z610,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z611,z6]),(0,[z0,z2,z273,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z612,z5,z6]),(0,[z0,z2,z613,z3,z4,z5,z6]),(0,[z614,z0,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z116,z5,z6]),(0,[z0,z2,z3,z4,z615,z5,z6])],[(0,[z0,z2,z3,z616,z4,z5,z6]),(0,[z617,z0,z2,z3,z4,z5,z6]),(1,[z18,z0,z2,z4,z5,z6]),(0,[z253,z0,z2,z3,z4,z5,z6]),(0,[z0,z618,z2,z3,z4,z5,z6]),(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z620,z6]),(0,[z0,z98,z2,z3,z4,z88,z6])],[(1,[z0,z147,z2,z4,z5,z6]),(0,[z621,z0,z2,z3,z4,z5,z6]),(0,[z0,z23,z2,z3,z444,z5,z6]),(0,[z42,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z88,z5,z6]),(0,[z0,z2,z3,z4,z87,z113,z6]),(1,[z0,z2,z124,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z487,z6]),(0,[z0,z2,z3,z118,z5,z210,z6])],[(1,[z54,z2,z161,z4,z5,z6]),(0,[z0,z195,z2,z4,z5,z6,z275]),(0,[z0,z175,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z622,z4,z5,z6]),(0,[z66,z0,z2,z3,z4,z6,z170])],[(0,[z0,z2,z3,z623,z4,z5,z6]),(0,[z0,z2,z3,z4,z624,z5,z6]),(0,[z0,z2,z625,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z626])],[(0,[z0,z627,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z101,z5,z6]),(0,[z0,z2,z29,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z628]),(0,[z629,z0,z2,z3,z4,z5,z6]),(0,[z0,z630,z2,z3,z4,z5,z6])],[(0,[z179,z0,z2,z24,z4,z5,z6]),(0,[z15,z0,z2,z3,z4,z5,z19]),(0,[z18,z0,z2,z332,z4,z5,z6]),(0,[z61,z0,z2,z3,z4,z5,z185]),(0,[z0,z2,z4,z5,z89,z210,z6])],[(0,[z0,z631,z2,z3,z4,z5,z6]),(1,[z7,z0,z24,z4,z5,z6]),(1,[z0,z2,z81,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z632,z6]),(0,[z633,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z634,z5,z6]),(0,[z0,z2,z3,z4,z5,z635,z6]),(0,[z636,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z93,z4,z118,z5,z6]),(0,[z0,z2,z3,z637,z4,z5,z6])],[(0,[z0,z638,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z206,z5,z6]),(0,[z0,z2,z639,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z640,z6])],[(0,[z641,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z642]),(0,[z0,z2,z3,z116,z4,z5,z6])],[(0,[z0,z2,z3,z4,z643,z5,z6]),(0,[z97,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z644,z3,z4,z5,z6]),(0,[z40,z22,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z589,z5,z6]),(0,[z645,z0,z2,z24,z4,z5,z6])],[(0,[z292,z0,z2,z3,z4,z5,z6]),(0,[z15,z129,z2,z3,z4,z5,z6]),(0,[z189,z0,z2,z24,z4,z5,z6]),(0,[z111,z18,z0,z3,z4,z5,z6]),(0,[z646,z0,z2,z3,z4,z5,z6]),(0,[z0,z647,z2,z3,z4,z5,z6]),(0,[z0,z49,z2,z3,z4,z5,z6])],[(0,[z648,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z19,z6,z17]),(0,[z0,z2,z24,z24,z4,z5,z6]),(1,[z0,z2,z102,z4,z5,z6])],[(0,[z0,z195,z2,z3,z4,z5,z6]),(0,[z190,z0,z2,z24,z4,z5,z6]),(1,[z0,z2,z163,z4,z5,z6]),(0,[z0,z3,z165,z4,z112,z5,z6]),(0,[z0,z649,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z650])]],
   [[(0,[z0,z2,z3,z4,z651,z5,z6]),(0,[z0,z2,z3,z4,z652,z5,z6]),(0,[z0,z653,z2,z3,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z30,z6]),(0,[z654,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z6])],[(0,[z18,z179,z0,z2,z4,z5,z6]),(0,[z0,z98,z2,z3,z4,z5,z6]),(1,[z152,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z655]),(0,[z0,z2,z3,z4,z5,z656,z6])],[(0,[z0,z2,z3,z4,z5,z657,z6]),(0,[z0,z2,z24,z4,z5,z331,z6]),(0,[z427,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z658,z5,z6]),(0,[z659,z0,z2,z3,z4,z5,z6]),(0,[z0,z660,z2,z3,z4,z5,z6])],[(0,[z18,z0,z2,z12,z4,z5,z6]),(0,[z661,z0,z2,z3,z4,z5,z6]),(0,[z0,z662,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z663,z5,z6]),(0,[z664,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z19,z6]),(0,[z0,z2,z3,z4,z5,z6,z665]),(0,[z0,z2,z3,z4,z5,z6,z469])],[(0,[z666,z0,z2,z3,z4,z5,z6]),(0,[z0,z308,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z357,z4,z5,z6])],[(1,[z0,z23,z24,z4,z5,z6]),(0,[z0,z2,z3,z667,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z668,z6]),(0,[z0,z2,z3,z4,z5,z669,z6])],[(0,[z0,z2,z3,z4,z670,z5,z6]),(0,[z0,z2,z3,z4,z5,z671,z6]),(0,[z0,z2,z24,z4,z5,z6,z275]),(0,[z267,z18,z0,z2,z4,z5,z6]),(0,[z0,z672,z2,z3,z4,z5,z6])],[(0,[z0,z49,z226,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z673,z6])]],
   [[(0,[z0,z674,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z675,z3,z4,z5,z6])],[(1,[z0,z201,z3,z4,z5,z6]),(0,[z0,z2,z3,z676,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z416]),(0,[z18,z0,z2,z4,z88,z5,z6]),(0,[z0,z175,z2,z447,z4,z5,z6]),(0,[z0,z153,z2,z3,z4,z5,z8]),(0,[z0,z153,z3,z4,z5,z36,z6])],[(1,[z0,z2,z3,z444,z5,z6]),(0,[z18,z0,z2,z161,z4,z5,z6]),(0,[z180,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z24,z93,z4,z5,z6]),(1,[z0,z52,z2,z4,z5,z6]),(0,[z0,z2,z124,z3,z4,z5,z6]),(0,[z0,z2,z3,z677,z4,z5,z6]),(0,[z0,z488,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z678,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z679])],[(1,[z40,z2,z3,z4,z13,z6]),(0,[z18,z0,z3,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z680,z6]),(0,[z0,z2,z3,z4,z5,z6,z8]),(0,[z681,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z137,z5,z6]),(0,[z682,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z683,z5,z6]),(1,[z0,z98,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z684]),(0,[z18,z0,z2,z4,z5,z169,z6]),(0,[z0,z2,z3,z4,z5,z685,z6]),(0,[z686,z0,z2,z3,z4,z5,z6]),(0,[z687,z0,z2,z3,z4,z5,z6])],[(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z689,z3,z4,z5,z6]),(1,[z22,z2,z3,z4,z25,z6]),(0,[z0,z153,z2,z418,z4,z5,z6])],[(0,[z179,z0,z2,z554,z4,z5,z6]),(0,[z2,z3,z161,z4,z5,z13,z6]),(0,[z107,z195,z2,z3,z4,z5,z6]),(0,[z18,z0,z2,z24,z4,z5,z6]),(0,[z80,z0,z98,z3,z4,z5,z6])],[(0,[z0,z2,z3,z554,z4,z5,z6]),(0,[z0,z58,z2,z3,z93,z5,z6]),(0,[z0,z2,z3,z4,z5,z690,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z691,z6]),(0,[z0,z58,z2,z24,z4,z5,z6]),(0,[z645,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z112,z5,z6]),(1,[z0,z98,z3,z4,z88,z6]),(0,[z0,z2,z3,z64,z118,z5,z6])],[(0,[z66,z0,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z112,z5,z6,z27]),(0,[z0,z2,z3,z64,z4,z210,z6]),(0,[z189,z0,z2,z3,z4,z5,z6])],[(1,[z0,z12,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z692]),(0,[z15,z0,z2,z3,z589,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z693]),(0,[z68,z0,z98,z2,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z27]),(0,[z0,z2,z3,z4,z5,z694,z6])],[(0,[z179,z0,z23,z3,z4,z5,z6]),(0,[z190,z0,z2,z3,z4,z5,z6]),(1,[z111,z18,z0,z4,z5,z6]),(0,[z695,z0,z2,z3,z4,z5,z6]),(0,[z0,z696,z2,z3,z4,z5,z6]),(0,[z0,z2,z697,z3,z4,z5,z6])],[(0,[z129,z2,z3,z4,z5,z19,z6]),(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z699,z6])],[(0,[z0,z2,z3,z4,z700,z5,z6]),(0,[z701,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z702,z6]),(0,[z0,z2,z3,z4,z5,z6,z550]),(0,[z0,z2,z3,z4,z5,z6,z703]),(0,[z0,z2,z3,z4,z5,z704,z6])],[(0,[z18,z0,z2,z4,z5,z514,z6])],[(0,[z107,z18,z0,z2,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z10,z6]),(1,[z0,z50,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z705,z6]),(0,[z61,z0,z103,z3,z4,z5,z6]),(0,[z0,z2,z3,z64,z4,z5,z6]),(0,[z0,z2,z3,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z707,z5,z6]),(0,[z0,z2,z708,z4,z5,z6]),(0,[z0,z31,z709,z4,z5,z6]),(0,[z0,z216,z163,z4,z5,z6]),(0,[z0,z58,z2,z710,z5,z6]),(0,[z0,z2,z3,z20,z5,z711])],[(0,[z0,z147,z2,z4,z5,z6]),(0,[z0,z73,z2,z444,z5,z6])],[(0,[z0,z2,z3,z5,z21,z532]),(0,[z0,z712,z2,z4,z5,z6]),(0,[z2,z24,z4,z5,z6,z469]),(0,[z0,z197,z24,z4,z5,z6]),(0,[z7,z0,z69,z4,z5,z8]),(0,[z61,z0,z2,z4,z30,z185]),(0,[z0,z2,z713,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z714]),(0,[z0,z2,z24,z4,z206,z6]),(0,[z0,z225,z24,z4,z5,z6]),(0,[z0,z2,z715,z4,z5,z6]),(0,[z295,z2,z3,z4,z206,z6])],[(0,[z0,z201,z24,z4,z5,z6]),(0,[z0,z627,z24,z4,z5,z6]),(0,[z472,z195,z2,z4,z5,z6]),(0,[z716,z0,z2,z3,z5,z6]),(0,[z0,z717,z3,z4,z5,z6])],[(0,[z0,z2,z91,z145,z5,z6]),(0,[z0,z24,z64,z112,z5,z6]),(0,[z0,z1,z2,z93,z5,z6]),(0,[z0,z2,z3,z4,z5,z718]),(0,[z33,z52,z2,z4,z5,z6])],[(0,[z18,z0,z194,z4,z5,z6]),(0,[z0,z719,z3,z4,z5,z6]),(0,[z40,z2,z24,z4,z13,z6]),(0,[z0,z175,z24,z112,z5,z6]),(0,[z0,z2,z24,z137,z5,z6]),(0,[z0,z2,z81,z4,z5,z6]),(0,[z0,z386,z3,z112,z5,z6]),(0,[z0,z2,z3,z4,z5,z720])],[(0,[z0,z721,z2,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z722]),(0,[z0,z24,z4,z5,z481,z6]),(0,[z0,z124,z24,z4,z5,z6]),(0,[z0,z58,z2,z93,z5,z6]),(1,[z0,z2,z3,z5,z711])]],
   [[(0,[z461,z12,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z723,z6]),(0,[z0,z2,z3,z4,z5,z724]),(0,[z272,z0,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z725,z6]),(0,[z0,z726,z2,z4,z5,z6])],[(0,[z0,z727,z3,z4,z5,z6]),(0,[z15,z196,z2,z3,z5,z6]),(0,[z728,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z729,z5,z6]),(0,[z0,z2,z3,z4,z730,z6]),(0,[z80,z0,z3,z4,z113,z6]),(0,[z0,z2,z731,z4,z5,z6]),(0,[z0,z2,z234,z3,z4,z170])],[(0,[z0,z2,z732,z4,z5,z6]),(0,[z18,z0,z2,z145,z5,z6]),(0,[z0,z3,z4,z5,z733,z6]),(0,[z734,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z589,z5,z6]),(0,[z735,z0,z2,z3,z5,z6]),(0,[z0,z98,z24,z4,z88,z6]),(0,[z0,z2,z3,z4,z487,z8]),(0,[z128,z0,z2,z4,z5,z275])],[(0,[z121,z23,z3,z444,z5,z6]),(0,[z0,z2,z3,z736,z5,z6]),(0,[z71,z2,z3,z165,z5,z6]),(0,[z80,z246,z3,z4,z113,z6])],[(0,[z177,z2,z3,z4,z5,z6]),(0,[z0,z2,z102,z4,z5,z6]),(0,[z0,z234,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z593,z10])],[(0,[z0,z2,z737,z4,z5,z6]),(0,[z0,z226,z4,z118,z5,z6]),(0,[z503,z0,z2,z3,z4,z170])],[(0,[z12,z24,z4,z5,z6,z17]),(0,[z23,z738,z3,z4,z5,z6]),(0,[z66,z18,z0,z2,z4,z170]),(0,[z80,z0,z3,z4,z113,z150]),(0,[z0,z3,z4,z5,z739,z8]),(0,[z0,z2,z3,z4,z740,z6])]],
   [[(0,[z0,z2,z741,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z742]),(0,[z0,z743,z3,z4,z5,z6]),(0,[z18,z0,z51,z112,z5,z6])],[(0,[z0,z2,z744,z4,z5,z6]),(0,[z0,z2,z3,z745,z5,z6]),(0,[z56,z0,z2,z3,z5,z27]),(0,[z0,z746,z2,z4,z5,z6]),(0,[z747,z2,z3,z4,z5,z6]),(0,[z0,z2,z697,z4,z5,z169])],[(0,[z405,z12,z24,z4,z5,z6]),(0,[z0,z748,z3,z4,z5,z6]),(0,[z0,z24,z4,z5,z6,z502]),(0,[z0,z2,z93,z137,z5,z6])],[(0,[z0,z2,z16,z4,z5,z6])],[(0,[z0,z2,z749,z4,z5,z6]),(0,[z196,z0,z2,z3,z5,z6]),(0,[z750,z0,z2,z4,z5,z6]),(0,[z0,z24,z4,z5,z487,z6]),(0,[z18,z0,z2,z224,z5,z6])],[(0,[z31,z3,z63,z4,z5,z6]),(0,[z15,z2,z24,z4,z5,z17]),(0,[z7,z295,z3,z4,z5,z8]),(0,[z0,z2,z751,z4,z5,z6])],[(0,[z0,z31,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z752]),(0,[z0,z2,z24,z4,z57,z6]),(0,[z0,z549,z24,z4,z5,z6]),(0,[z0,z753,z3,z4,z5,z6])],[(0,[z0,z73,z24,z4,z5,z6]),(0,[z0,z754,z3,z4,z5,z6]),(0,[z40,z18,z2,z4,z13,z6]),(0,[z755,z0,z2,z4,z5,z6]),(0,[z18,z0,z2,z449,z5,z6]),(0,[z0,z2,z24,z4,z28,z6]),(0,[z0,z24,z4,z5,z514,z6]),(0,[z0,z2,z24,z5,z756,z6]),(0,[z0,z24,z4,z5,z6,z650])]],
   [[(0,[z0,z201,z3,z4,z5,z6]),(0,[z40,z2,z3,z4,z757,z6]),(0,[z0,z454,z24,z4,z5,z6]),(0,[z68,z0,z98,z4,z88,z6])],[(0,[z0,z2,z3,z444,z5,z6]),(0,[z0,z2,z758,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z759]),(0,[z0,z52,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z760,z6]),(0,[z0,z2,z3,z4,z5,z150]),(0,[z0,z332,z173,z4,z5,z169])],[(0,[z18,z0,z103,z4,z5,z6]),(0,[z0,z2,z3,z137,z5,z6]),(0,[z761,z2,z3,z4,z5,z6])],[(0,[z0,z98,z24,z4,z5,z6]),(0,[z762,z2,z3,z4,z5,z6]),(0,[z0,z2,z763,z4,z5,z6])],[(0,[z22,z2,z3,z4,z757,z6]),(0,[z33,z175,z24,z4,z5,z6]),(0,[z0,z175,z447,z165,z5,z6]),(0,[z442,z0,z2,z3,z210,z6]),(0,[z0,z764,z3,z4,z5,z6])],[(0,[z0,z2,z3,z765,z5,z6]),(0,[z0,z216,z3,z4,z28,z6]),(0,[z0,z24,z4,z5,z668,z6]),(0,[z766,z0,z24,z4,z5,z6]),(0,[z0,z24,z4,z5,z528,z6]),(0,[z728,z2,z3,z4,z5,z6]),(0,[z767,z2,z3,z4,z5,z6]),(0,[z0,z768,z2,z4,z5,z6])],[(0,[z0,z2,z3,z769,z5,z6]),(0,[z0,z291,z24,z4,z5,z6])],[(0,[z0,z2,z3,z20,z5,z671]),(0,[z770,z0,z3,z4,z5,z6]),(0,[z0,z771,z3,z4,z5,z6]),(0,[z0,z2,z772,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z19,z307]),(0,[z42,z0,z24,z4,z113,z6]),(0,[z111,z0,z124,z4,z5,z6]),(0,[z71,z2,z3,z112,z5,z6]),(0,[z0,z773,z3,z4,z5,z6])],[(0,[z738,z12,z3,z4,z5,z6]),(0,[z68,z0,z2,z4,z5,z6]),(0,[z0,z335,z24,z4,z5,z6]),(0,[z0,z301,z24,z4,z5,z6]),(0,[z0,z324,z2,z118,z5,z6]),(0,[z111,z0,z3,z4,z487,z6]),(0,[z0,z2,z3,z4,z774,z6]),(0,[z295,z2,z69,z4,z5,z6])],[(0,[z221,z308,z2,z4,z5,z6]),(0,[z0,z2,z3,z775,z5,z6])],[(0,[z175,z176,z24,z4,z5,z6]),(0,[z0,z24,z4,z5,z680,z6]),(0,[z7,z0,z3,z4,z5,z8])],[(0,[z666,z0,z2,z4,z5,z275]),(0,[z0,z419,z24,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z684]),(0,[z776,z2,z3,z4,z5,z6]),(0,[z777,z0,z2,z4,z5,z6]),(0,[z0,z302,z49,z118,z5,z6]),(0,[z0,z2,z4,z5,z6,z778])],[(0,[z0,z779,z2,z4,z5,z6]),(0,[z0,z2,z163,z449,z5,z6]),(0,[z0,z737,z24,z4,z5,z6]),(1,[z0,z24,z314,z5,z6]),(0,[z0,z2,z3,z116,z487,z6])],[(0,[z111,z0,z73,z4,z5,z6]),(0,[z0,z2,z3,z780,z5,z6]),(0,[z15,z18,z2,z4,z5,z17]),(0,[z0,z50,z2,z4,z5,z6]),(0,[z18,z0,z2,z4,z487,z6])],[(0,[z0,z2,z3,z781,z5,z6]),(1,[z2,z3,z4,z5,z759]),(0,[z0,z2,z124,z4,z487,z6]),(0,[z7,z0,z3,z4,z5,z739])]],
   [[(0,[z398,z2,z161,z4,z5,z6]),(0,[z2,z3,z4,z5,z759,z17]),(0,[z0,z24,z4,z74,z5,z6]),(0,[z0,z24,z112,z5,z210,z6]),(0,[z695,z0,z24,z4,z5,z6]),(0,[z0,z2,z4,z5,z782,z6]),(0,[z0,z783,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z784]),(0,[z0,z2,z785,z4,z5,z6]),(0,[z0,z786,z3,z4,z5,z6]),(0,[z0,z3,z787,z112,z5,z6])],[(0,[z0,z788,z3,z4,z5,z6]),(0,[z0,z103,z24,z4,z5,z6]),(0,[z18,z268,z2,z4,z5,z6]),(0,[z266,z0,z173,z4,z5,z6]),(0,[z0,z2,z3,z789,z210,z6]),(0,[z0,z2,z3,z4,z789,z6])],[(0,[z0,z2,z3,z4,z28,z6]),(0,[z0,z187,z2,z93,z5,z6]),(0,[z0,z2,z3,z790,z5,z6])],[(0,[z0,z23,z554,z4,z5,z6]),(0,[z0,z2,z791,z4,z5,z6]),(0,[z18,z0,z216,z4,z5,z6]),(0,[z230,z405,z2,z4,z5,z6]),(0,[z7,z0,z24,z4,z487,z6]),(0,[z0,z2,z32,z4,z5,z6]),(0,[z0,z49,z2,z74,z5,z6]),(0,[z189,z0,z2,z3,z5,z711])],[(0,[z0,z2,z792,z4,z5,z6]),(0,[z31,z3,z4,z5,z6,z17]),(0,[z0,z24,z4,z5,z6,z703]),(0,[z0,z2,z24,z4,z5,z793]),(0,[z0,z24,z4,z5,z704,z6]),(0,[z0,z303,z2,z118,z5,z6])],[(0,[z179,z147,z12,z4,z5,z6]),(0,[z33,z2,z24,z4,z5,z6]),(0,[z66,z0,z2,z24,z4,z170]),(0,[z794,z2,z3,z4,z5,z6])],[(0,[z0,z24,z4,z5,z36,z6]),(0,[z0,z2,z3,z795,z5,z6]),(0,[z0,z2,z796,z4,z5,z6])]],
   [[(0,[z368,z0,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z797]),(0,[z0,z175,z24,z4,z5,z6]),(0,[z406,z0,z2,z4,z514,z6]),(0,[z421,z0,z124,z4,z5,z6]),(0,[z0,z103,z3,z4,z5,z285])],[(0,[z0,z2,z3,z4,z560,z10]),(0,[z0,z2,z3,z20,z5,z21])],[(0,[z18,z179,z12,z4,z5,z6]),(0,[z0,z130,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z798,z6]),(0,[z177,z2,z3,z314,z5,z6]),(0,[z0,z2,z93,z710,z5,z6]),(0,[z48,z0,z103,z4,z5,z6]),(0,[z0,z799,z3,z4,z5,z6])],[(1,[z779,z2,z4,z5,z6]),(0,[z779,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z800]),(0,[z15,z196,z2,z3,z5,z17]),(0,[z80,z0,z3,z277,z113,z6]),(0,[z180,z0,z2,z3,z210,z6])],[(0,[z355,z2,z161,z4,z5,z6]),(0,[z0,z2,z3,z801,z5,z6]),(0,[z0,z2,z24,z4,z5,z718]),(0,[z659,z0,z2,z3,z4,z170])],[(0,[z541,z12,z3,z4,z5,z6]),(0,[z0,z2,z69,z4,z5,z6]),(0,[z18,z2,z4,z5,z6,z469]),(0,[z0,z2,z3,z450,z5,z550]),(0,[z61,z0,z60,z4,z30,z6]),(0,[z2,z3,z4,z5,z802,z6])],[(0,[z0,z2,z3,z803,z5,z6]),(0,[z0,z2,z3,z4,z5,z804]),(0,[z0,z805,z3,z4,z5,z6]),(0,[z0,z50,z51,z112,z5,z6])],[(0,[z0,z806,z2,z4,z5,z6]),(0,[z0,z435,z3,z165,z5,z6]),(0,[z394,z2,z3,z137,z5,z6])]],
   [[(0,[z80,z0,z24,z4,z113,z6]),(0,[z0,z2,z24,z729,z5,z6]),(0,[z0,z175,z3,z463,z5,z6]),(0,[z0,z807,z3,z4,z5,z6]),(0,[z0,z808,z3,z4,z5,z6]),(0,[z809,z2,z3,z4,z5,z6]),(0,[z189,z2,z3,z5,z469,z27])],[(0,[z0,z12,z554,z4,z5,z6]),(0,[z0,z2,z3,z810,z5,z6]),(0,[z0,z24,z4,z5,z41,z6]),(0,[z0,z24,z4,z43,z5,z6]),(0,[z177,z3,z24,z4,z5,z6]),(0,[z0,z173,z4,z5,z169,z6]),(0,[z811,z2,z3,z4,z5,z6])],[(0,[z268,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z710,z5,z6]),(0,[z212,z0,z173,z4,z5,z6]),(0,[z0,z812,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z813,z6]),(0,[z0,z24,z4,z55,z5,z6]),(0,[z0,z173,z24,z4,z5,z6]),(0,[z18,z0,z675,z4,z5,z6]),(0,[z0,z2,z3,z814,z5,z6]),(0,[z0,z303,z2,z137,z5,z6]),(0,[z815,z2,z3,z4,z5,z6]),(0,[z816,z0,z2,z4,z5,z6]),(0,[z817,z0,z2,z4,z5,z6])],[(0,[z0,z2,z818,z4,z5,z6]),(0,[z177,z2,z24,z4,z5,z6]),(0,[z246,z2,z3,z450,z5,z6]),(0,[z80,z0,z3,z4,z733,z6])],[(0,[z381,z12,z3,z4,z5,z6]),(0,[z179,z12,z24,z4,z5,z6]),(0,[z0,z819,z2,z4,z5,z6]),(0,[z0,z183,z24,z4,z5,z6]),(0,[z0,z2,z3,z277,z5,z6])],[(0,[z0,z73,z2,z4,z5,z6]),(0,[z0,z738,z3,z4,z5,z6])],[(0,[z0,z820,z2,z4,z5,z6]),(0,[z569,z0,z24,z4,z5,z6]),(0,[z0,z2,z3,z821,z5,z6]),(0,[z71,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z5,z711])]],
   [[(0,[z0,z822,z2,z4,z5,z6]),(0,[z602,z2,z3,z4,z13,z6]),(0,[z0,z2,z709,z4,z5,z6]),(0,[z15,z2,z3,z449,z5,z17]),(0,[z0,z24,z4,z5,z591,z6]),(0,[z268,z2,z3,z4,z5,z150]),(0,[z0,z2,z3,z5,z789,z6]),(0,[z66,z0,z2,z3,z4,z823])],[(0,[z0,z2,z3,z449,z57,z6]),(0,[z0,z2,z3,z824,z5,z6]),(0,[z0,z24,z4,z86,z5,z6]),(0,[z0,z2,z3,z4,z5,z793]),(0,[z18,z0,z2,z4,z5,z185]),(0,[z0,z2,z3,z825,z5,z6])],[(0,[z0,z2,z24,z4,z5,z6]),(0,[z33,z2,z3,z4,z5,z6]),(0,[z295,z2,z3,z4,z5,z6]),(0,[z0,z12,z418,z4,z5,z6]),(0,[z0,z2,z3,z449,z28,z6]),(0,[z0,z2,z3,z4,z5,z826]),(0,[z61,z0,z2,z137,z30,z6])],[(0,[z0,z201,z161,z4,z5,z6]),(0,[z0,z827,z3,z4,z5,z6]),(0,[z190,z0,z24,z112,z5,z6]),(0,[z0,z2,z828,z4,z5,z6]),(0,[z0,z1,z24,z112,z5,z6]),(0,[z829,z2,z3,z4,z5,z6]),(0,[z18,z830,z2,z4,z5,z6]),(0,[z119,z18,z0,z4,z5,z6]),(0,[z0,z2,z3,z277,z5,z150]),(0,[z488,z2,z3,z4,z5,z185]),(0,[z0,z60,z3,z137,z5,z6]),(0,[z189,z71,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z823])],[(0,[z0,z73,z194,z4,z5,z6]),(0,[z0,z831,z2,z4,z5,z6]),(0,[z766,z0,z2,z4,z5,z6])],[(0,[z0,z2,z832,z4,z5,z6]),(0,[z107,z405,z2,z4,z5,z6]),(0,[z0,z31,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z833]),(0,[z470,z0,z24,z4,z5,z6]),(0,[z0,z2,z3,z834,z5,z6]),(0,[z18,z0,z173,z4,z5,z6]),(0,[z0,z94,z3,z165,z5,z6])],[(0,[z0,z2,z3,z4,z835,z6]),(0,[z121,z393,z3,z4,z5,z6]),(0,[z190,z2,z3,z191,z5,z6]),(0,[z0,z2,z836,z4,z5,z6]),(0,[z18,z0,z2,z450,z5,z6]),(0,[z0,z2,z837,z4,z5,z6])],[(0,[z18,z0,z175,z165,z5,z6]),(0,[z0,z2,z3,z4,z5,z838]),(0,[z0,z839,z2,z4,z5,z6])]],
   [[(0,[z0,z216,z3,z4,z5,z6]),(0,[z0,z73,z2,z145,z5,z6]),(0,[z0,z2,z24,z444,z5,z6]),(0,[z0,z2,z4,z5,z840,z6]),(0,[z0,z216,z16,z4,z5,z6]),(0,[z0,z24,z4,z5,z106,z6]),(0,[z0,z2,z24,z4,z5,z150]),(0,[z0,z649,z24,z4,z5,z6]),(0,[z7,z0,z3,z314,z5,z8])],[(0,[z121,z23,z3,z4,z5,z6]),(0,[z0,z2,z3,z841,z5,z6]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z2,z843,z4,z5,z6]),(0,[z844,z2,z3,z4,z5,z6])],[(0,[z645,z0,z24,z4,z5,z36]),(0,[z845,z0,z2,z24,z4,z6]),(0,[z7,z18,z0,z4,z5,z8]),(0,[z846,z0,z3,z4,z5,z6])],[(0,[z461,z0,z24,z4,z5,z6]),(0,[z766,z0,z98,z4,z5,z6])],[(1,[z738,z3,z4,z5,z6]),(0,[z847,z2,z3,z4,z5,z6]),(0,[z246,z2,z3,z4,z5,z550]),(0,[z0,z2,z81,z450,z5,z6])],[(0,[z0,z2,z3,z848,z5,z6]),(1,[z0,z24,z145,z5,z6]),(0,[z409,z0,z2,z3,z4,z170]),(0,[z0,z24,z4,z87,z113,z6]),(0,[z0,z2,z4,z5,z849,z6])],[(0,[z18,z0,z2,z4,z57,z6]),(0,[z0,z2,z3,z850,z5,z6]),(1,[z0,z2,z710,z5,z6])],[(0,[z0,z173,z3,z4,z5,z6]),(0,[z0,z49,z2,z118,z5,z6]),(0,[z0,z2,z3,z137,z5,z285]),(0,[z0,z2,z3,z5,z711,z27])]],
   [[(0,[z0,z2,z3,z4,z851,z6]),(0,[z0,z257,z24,z4,z5,z6]),(0,[z180,z0,z2,z3,z789,z6])],[(0,[z179,z12,z3,z4,z5,z6]),(0,[z111,z177,z3,z4,z5,z6]),(0,[z18,z0,z11,z4,z5,z6]),(0,[z176,z52,z2,z4,z5,z6]),(0,[z0,z2,z3,z852,z5,z6]),(0,[z0,z2,z3,z4,z87,z823])],[(0,[z156,z0,z24,z4,z5,z6]),(0,[z0,z2,z853,z4,z5,z6]),(0,[z190,z2,z3,z854,z5,z6]),(0,[z7,z0,z24,z4,z5,z8]),(0,[z18,z0,z2,z4,z5,z855]),(0,[z0,z103,z3,z224,z5,z6]),(0,[z0,z2,z856,z4,z5,z6])],[(0,[z0,z2,z857,z4,z5,z6]),(0,[z97,z0,z24,z112,z5,z6]),(0,[z2,z3,z4,z5,z6,z858]),(0,[z0,z2,z102,z450,z5,z6]),(0,[z0,z2,z859,z4,z5,z6])],[(0,[z413,z2,z3,z63,z5,z6])],[(0,[z860,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z125,z6]),(0,[z189,z0,z2,z3,z5,z27]),(0,[z189,z71,z2,z3,z5,z27])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z861,z0,z3,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z550]),(0,[z0,z175,z3,z787,z5,z6])],[(0,[z121,z653,z3,z4,z5,z6])]],
   [[(0,[z0,z290,z24,z4,z5,z6]),(0,[z0,z2,z3,z862,z5,z6])],[(0,[z190,z12,z24,z4,z5,z6]),(0,[z129,z2,z3,z4,z5,z298]),(0,[z0,z438,z24,z4,z5,z6]),(0,[z0,z24,z4,z5,z174,z6]),(0,[z18,z0,z2,z4,z87,z10]),(0,[z0,z863,z2,z4,z5,z6])],[(0,[z54,z194,z161,z4,z5,z6]),(0,[z0,z2,z3,z864,z5,z6]),(0,[z0,z2,z69,z314,z5,z6]),(0,[z0,z865,z3,z4,z5,z6])],[(0,[z292,z0,z24,z4,z5,z6]),(0,[z0,z866,z2,z4,z5,z6]),(0,[z18,z0,z226,z4,z5,z6]),(0,[z0,z98,z357,z4,z88,z6]),(0,[z0,z2,z69,z4,z487,z6]),(0,[z394,z103,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z838]),(0,[z0,z867,z3,z4,z5,z6])],[(0,[z71,z2,z3,z63,z5,z6]),(0,[z0,z868,z3,z4,z5,z6]),(0,[z0,z2,z163,z4,z57,z6]),(0,[z0,z2,z4,z5,z869,z6]),(0,[z0,z2,z81,z4,z5,z550]),(0,[z0,z2,z870,z4,z5,z6])],[(0,[z367,z23,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z871,z6]),(0,[z0,z49,z2,z137,z5,z6])],[(0,[z0,z872,z2,z4,z5,z6]),(0,[z779,z2,z161,z4,z5,z6]),(0,[z18,z861,z0,z4,z5,z6]),(0,[z0,z2,z3,z4,z873,z6]),(0,[z0,z2,z332,z4,z5,z838])],[(0,[z0,z286,z24,z4,z5,z6]),(0,[z874,z0,z3,z4,z5,z6]),(0,[z875,z0,z31,z4,z5,z6]),(0,[z0,z386,z24,z4,z5,z6]),(0,[z0,z103,z4,z5,z30,z6])]],
   [[(0,[z0,z2,z3,z145,z5,z6]),(0,[z0,z2,z876,z4,z5,z6]),(0,[z267,z0,z24,z4,z5,z6]),(0,[z0,z226,z3,z4,z5,z6]),(0,[z0,z51,z3,z787,z5,z6])],[(0,[z121,z73,z23,z4,z5,z6]),(0,[z0,z2,z332,z4,z5,z169]),(1,[z0,z773,z4,z5,z6])],[(0,[z54,z308,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z877,z6]),(0,[z0,z878,z3,z4,z5,z6]),(0,[z0,z303,z2,z93,z5,z6])],[(0,[z22,z12,z24,z4,z5,z6]),(0,[z0,z2,z3,z879,z5,z6]),(0,[z54,z779,z2,z4,z5,z6]),(0,[z18,z488,z2,z4,z5,z6]),(0,[z246,z2,z81,z4,z5,z6]),(0,[z0,z2,z102,z4,z5,z550])],[(0,[z0,z674,z24,z4,z5,z6]),(0,[z0,z24,z4,z5,z113,z6]),(0,[z268,z2,z3,z277,z5,z6]),(0,[z488,z103,z3,z4,z5,z6])],[(0,[z0,z880,z2,z4,z5,z6]),(0,[z0,z881,z3,z4,z5,z6]),(0,[z830,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z882,z5,z6]),(0,[z0,z2,z3,z4,z113,z550])],[(0,[z0,z2,z3,z4,z5,z883]),(0,[z884,z0,z2,z4,z5,z6]),(0,[z18,z0,z2,z116,z5,z6]),(0,[z0,z672,z3,z4,z88,z6]),(0,[z177,z153,z3,z4,z5,z6])],[(0,[z885,z0,z2,z4,z5,z6]),(0,[z0,z2,z24,z314,z5,z6]),(0,[z295,z2,z3,z314,z5,z6]),(0,[z0,z2,z124,z116,z5,z6]),(0,[z61,z488,z2,z4,z30,z6]),(0,[z886,z2,z3,z4,z5,z6]),(0,[z887,z2,z3,z4,z5,z6])]],
   [[(0,[z18,z0,z338,z4,z5,z6]),(0,[z0,z3,z165,z787,z5,z6])],[(0,[z18,z0,z222,z4,z5,z6]),(0,[z0,z2,z888,z4,z5,z6]),(0,[z268,z2,z24,z4,z5,z6]),(1,[z0,z24,z4,z487,z6]),(0,[z0,z2,z29,z4,z565,z6]),(1,[z0,z3,z787,z5,z6]),(0,[z0,z3,z4,z88,z733,z6]),(0,[z0,z2,z710,z118,z5,z6])],[(0,[z0,z889,z3,z4,z5,z6]),(0,[z0,z486,z24,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z890]),(0,[z891,z2,z3,z4,z5,z6]),(0,[z645,z0,z2,z4,z5,z275]),(0,[z892,z2,z3,z4,z5,z6]),(0,[z246,z2,z102,z4,z5,z6]),(0,[z0,z81,z4,z5,z113,z6]),(0,[z0,z2,z3,z224,z5,z6]),(0,[z2,z3,z4,z5,z6,z893])],[(0,[z0,z24,z4,z112,z5,z6]),(0,[z0,z60,z24,z4,z5,z6]),(0,[z894,z2,z3,z4,z5,z6])],[(0,[z0,z195,z201,z4,z5,z6]),(0,[z0,z24,z112,z5,z6,z27]),(0,[z0,z2,z24,z277,z5,z6]),(0,[z7,z0,z24,z116,z5,z6]),(0,[z111,z861,z0,z4,z5,z6]),(0,[z895,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z873,z6]),(0,[z0,z2,z896,z4,z5,z6]),(0,[z0,z897,z2,z4,z5,z6])],[(0,[z22,z2,z3,z4,z410,z6]),(0,[z0,z2,z16,z449,z5,z6]),(0,[z0,z32,z4,z112,z5,z6])],[(0,[z0,z2,z3,z898,z5,z6]),(0,[z0,z24,z4,z241,z5,z6]),(0,[z0,z24,z4,z5,z242,z6]),(0,[z0,z24,z4,z5,z243,z6]),(0,[z0,z303,z773,z4,z5,z6]),(0,[z0,z899,z3,z4,z5,z6])],[(0,[z190,z2,z24,z101,z5,z6]),(0,[z190,z92,z2,z3,z5,z6]),(0,[z0,z2,z900,z4,z5,z6]),(0,[z0,z901,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z902]),(0,[z0,z31,z3,z449,z5,z6]),(0,[z42,z0,z2,z4,z331,z6]),(0,[z903,z2,z3,z4,z5,z6]),(0,[z904,z2,z3,z4,z5,z6])],[(0,[z295,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z20,z5,z288]),(0,[z0,z2,z3,z905,z5,z6])],[(0,[z0,z906,z2,z3,z5,z6]),(0,[z18,z0,z2,z589,z5,z6]),(0,[z0,z2,z3,z4,z907,z6]),(1,[z0,z2,z4,z873,z6])],[(0,[z394,z2,z3,z4,z5,z6]),(0,[z80,z18,z0,z4,z113,z6]),(0,[z61,z0,z2,z4,z873,z6])],[(0,[z0,z2,z3,z4,z5,z908]),(0,[z18,z0,z60,z4,z5,z6]),(0,[z0,z51,z32,z112,z5,z6]),(0,[z0,z2,z909,z4,z5,z6]),(0,[z0,z2,z4,z5,z169,z838])],[(0,[z196,z2,z12,z3,z5,z6]),(0,[z0,z2,z3,z910,z5,z6]),(0,[z0,z911,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z158]),(0,[z0,z339,z24,z4,z5,z6]),(0,[z0,z912,z3,z4,z5,z6])],[(0,[z12,z24,z4,z5,z13,z6]),(0,[z0,z273,z24,z4,z113,z6]),(0,[z80,z268,z3,z4,z113,z6]),(0,[z177,z2,z3,z4,z487,z6])],[(0,[z0,z2,z3,z4,z913,z6]),(0,[z0,z2,z3,z4,z914,z6]),(0,[z0,z2,z3,z5,z915,z6]),(0,[z0,z216,z24,z4,z5,z6]),(0,[z15,z2,z3,z4,z57,z17]),(0,[z0,z24,z4,z5,z6,z278]),(0,[z0,z2,z24,z4,z5,z285]),(0,[z0,z58,z226,z4,z5,z6]),(0,[z0,z303,z2,z4,z5,z6])]],
   [[(0,[z412,z12,z24,z4,z5,z6]),(0,[z121,z23,z24,z4,z5,z6]),(0,[z0,z141,z24,z4,z5,z6]),(0,[z844,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z916]),(0,[z695,z0,z2,z3,z4,z170])],[(0,[z0,z317,z24,z4,z5,z6]),(0,[z190,z2,z3,z667,z5,z6]),(0,[z71,z2,z24,z4,z5,z6]),(0,[z0,z2,z917,z4,z5,z6])],[(0,[z0,z173,z161,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z759]),(0,[z918,z2,z3,z4,z5,z6])],[(0,[z0,z919,z2,z3,z5,z6]),(0,[z0,z2,z920,z4,z5,z6]),(0,[z0,z2,z3,z4,z921,z6]),(0,[z875,z0,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z19,z759]),(0,[z129,z2,z24,z4,z5,z19]),(0,[z0,z2,z3,z314,z5,z6]),(0,[z922,z2,z3,z4,z5,z6])],[(0,[z18,z507,z0,z4,z5,z6]),(0,[z0,z2,z923,z4,z5,z6]),(0,[z0,z24,z4,z5,z293,z6]),(0,[z18,z0,z248,z4,z5,z6]),(0,[z0,z58,z2,z146,z5,z6])],[(0,[z0,z924,z2,z4,z5,z6]),(0,[z0,z329,z3,z112,z5,z6]),(0,[z0,z24,z4,z5,z6,z47]),(0,[z861,z0,z276,z4,z5,z6]),(0,[z412,z2,z239,z4,z5,z6]),(0,[z0,z258,z24,z4,z5,z6]),(0,[z925,z2,z3,z4,z5,z6]),(0,[z0,z2,z926,z4,z5,z6]),(0,[z0,z2,z3,z116,z206,z6]),(0,[z0,z49,z2,z710,z5,z6]),(0,[z180,z0,z303,z2,z210,z6]),(0,[z0,z2,z3,z927,z5,z6])],[(0,[z129,z12,z24,z4,z5,z6]),(0,[z18,z0,z2,z4,z206,z6]),(0,[z0,z928,z3,z4,z5,z6]),(0,[z61,z0,z2,z4,z30,z6]),(0,[z929,z2,z3,z4,z5,z6])],[(0,[z15,z2,z3,z4,z5,z759]),(0,[z0,z60,z3,z4,z5,z6]),(0,[z930,z2,z3,z4,z5,z6]),(0,[z0,z2,z931,z4,z5,z6]),(0,[z0,z2,z124,z4,z206,z6]),(0,[z0,z103,z3,z4,z5,z185])]],
   [[(0,[z18,z0,z2,z444,z5,z6]),(0,[z0,z2,z3,z4,z932,z6]),(0,[z0,z2,z163,z589,z5,z6]),(0,[z0,z2,z3,z4,z487,z36])],[(0,[z54,z201,z161,z4,z5,z6]),(0,[z0,z933,z24,z4,z5,z6]),(0,[z18,z0,z2,z137,z5,z6]),(0,[z61,z0,z2,z4,z467,z6]),(0,[z0,z2,z4,z5,z6,z838]),(0,[z0,z2,z3,z5,z6,z711])],[(0,[z0,z934,z2,z4,z5,z6]),(0,[z0,z935,z2,z4,z5,z6]),(0,[z33,z18,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z936,z5]),(0,[z195,z779,z2,z4,z5,z6]),(0,[z190,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z5,z937]),(0,[z488,z2,z3,z137,z5,z6])],[(0,[z0,z2,z3,z938,z5,z6]),(0,[z0,z195,z173,z4,z5,z6]),(0,[z0,z2,z939,z4,z5,z6]),(0,[z7,z0,z24,z4,z206,z6]),(0,[z0,z2,z4,z5,z940,z6]),(0,[z0,z941,z2,z4,z5,z6]),(0,[z0,z942,z3,z4,z5,z6])],[(0,[z738,z2,z3,z4,z5,z6]),(0,[z0,z2,z332,z4,z5,z250]),(0,[z861,z0,z24,z4,z5,z6])],[(0,[z0,z2,z943,z4,z5,z6]),(0,[z0,z944,z3,z4,z5,z6])],[(0,[z0,z227,z24,z4,z5,z6])]],
   [[(0,[z0,z79,z24,z4,z5,z6]),(0,[z0,z2,z945,z4,z5,z6]),(0,[z0,z2,z946,z4,z5,z6]),(0,[z18,z129,z2,z4,z5,z19]),(0,[z947,z0,z2,z4,z5,z6]),(0,[z0,z2,z948,z4,z5,z6]),(0,[z180,z0,z2,z89,z210,z6])],[(0,[z141,z12,z3,z4,z5,z6]),(0,[z698,z23,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z757,z6]),(0,[z0,z949,z3,z4,z5,z6]),(0,[z18,z0,z2,z775,z5,z6]),(0,[z7,z0,z3,z116,z5,z8]),(0,[z950,z2,z3,z4,z5,z6])],[(0,[z71,z18,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z951]),(0,[z952,z2,z3,z4,z5,z6])],[(0,[z260,z0,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z285])],[(0,[z412,z12,z3,z4,z5,z6]),(0,[z0,z3,z24,z145,z5,z6]),(0,[z7,z0,z3,z4,z487,z8])],[(0,[z190,z2,z3,z144,z5,z6]),(0,[z71,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z953,z6]),(0,[z954,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z955]),(0,[z176,z2,z3,z4,z5,z6]),(0,[z0,z956,z3,z4,z5,z6]),(0,[z111,z0,z52,z4,z5,z6]),(0,[z48,z0,z2,z4,z565,z6]),(0,[z957,z2,z3,z4,z5,z6])],[(0,[z0,z2,z24,z145,z5,z6]),(0,[z129,z2,z3,z4,z5,z19]),(0,[z0,z226,z24,z4,z5,z6]),(0,[z7,z0,z737,z4,z5,z6]),(0,[z0,z609,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z2,z3,z959,z5,z6]),(0,[z0,z2,z960,z4,z5,z6])]],
   [[(0,[z196,z0,z2,z24,z5,z6])],[(0,[z190,z31,z3,z4,z5,z6]),(0,[z0,z324,z2,z105,z5,z6]),(0,[z0,z2,z24,z4,z877,z6])],[(0,[z0,z24,z4,z5,z342,z6]),(0,[z0,z24,z4,z5,z138,z6]),(0,[z0,z24,z4,z5,z343,z6]),(0,[z884,z0,z216,z4,z5,z6]),(0,[z18,z0,z2,z4,z28,z6]),(0,[z0,z2,z357,z4,z5,z6]),(0,[z427,z0,z2,z4,z5,z106]),(0,[z0,z2,z4,z5,z961,z6]),(0,[z80,z0,z3,z450,z113,z6]),(0,[z962,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z963,z5,z6]),(0,[z964,z0,z2,z3,z5,z6]),(0,[z18,z0,z326,z4,z5,z6]),(0,[z0,z2,z965,z4,z5,z6]),(0,[z0,z60,z3,z224,z5,z6])],[(0,[z0,z24,z4,z144,z5,z6]),(0,[z0,z23,z24,z444,z5,z6]),(0,[z61,z0,z2,z4,z514,z6]),(0,[z0,z567,z3,z112,z5,z6])],[(0,[z0,z2,z966,z4,z5,z6]),(0,[z0,z967,z3,z4,z5,z6]),(0,[z0,z2,z3,z968,z5,z6]),(0,[z0,z24,z4,z5,z351,z6]),(0,[z0,z98,z3,z4,z733,z6]),(0,[z0,z2,z3,z969,z5,z6])],[(0,[z121,z23,z3,z145,z5,z6]),(0,[z0,z970,z3,z4,z5,z6]),(0,[z18,z0,z24,z4,z5,z6]),(0,[z0,z3,z787,z4,z5,z6]),(0,[z0,z2,z971,z4,z5,z6]),(0,[z0,z2,z3,z972,z5,z6])],[(0,[z0,z2,z3,z4,z757,z6]),(0,[z0,z2,z3,z973,z5,z6]),(0,[z111,z176,z3,z4,z5,z6])]],
   [[(0,[z179,z12,z554,z4,z5,z6]),(0,[z0,z2,z3,z974,z5,z6]),(0,[z0,z535,z24,z4,z5,z36]),(0,[z0,z103,z29,z4,z5,z6]),(0,[z0,z2,z975,z4,z5,z6])],[(0,[z0,z976,z3,z4,z5,z6]),(0,[z0,z2,z24,z224,z5,z6]),(0,[z18,z177,z2,z4,z5,z6]),(0,[z0,z175,z52,z165,z5,z6]),(0,[z0,z2,z3,z5,z6,z977])],[(0,[z978,z0,z2,z3,z4,z5]),(0,[z107,z439,z2,z4,z5,z6]),(0,[z979,z2,z3,z4,z5,z6])],[(0,[z0,z980,z3,z4,z5,z6]),(0,[z0,z2,z3,z981,z5,z6]),(0,[z15,z2,z3,z589,z5,z17]),(0,[z0,z2,z3,z4,z982,z6]),(0,[z33,z2,z447,z4,z5,z6]),(0,[z0,z2,z983,z4,z5,z6]),(0,[z0,z2,z69,z116,z5,z6]),(0,[z0,z2,z984,z4,z5,z6])],[(0,[z2,z12,z3,z444,z5,z6]),(0,[z0,z2,z3,z985,z5,z6]),(0,[z0,z2,z24,z449,z5,z6]),(0,[z0,z2,z3,z589,z57,z6]),(0,[z18,z176,z2,z4,z5,z6]),(0,[z0,z2,z3,z450,z5,z6]),(0,[z0,z98,z81,z4,z5,z6]),(0,[z0,z2,z3,z4,z88,z550]),(0,[z394,z60,z3,z4,z5,z6])],[(0,[z0,z2,z554,z4,z5,z6]),(0,[z179,z738,z3,z4,z5,z6]),(0,[z346,z12,z3,z4,z5,z6]),(0,[z0,z2,z3,z986,z5,z6]),(0,[z0,z361,z24,z4,z5,z6])],[(0,[z0,z2,z3,z4,z987,z6]),(0,[z190,z2,z3,z5,z203,z6]),(0,[z0,z2,z3,z4,z988,z6]),(0,[z0,z2,z989,z4,z5,z6]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z564,z2,z3,z4,z25,z6]),(0,[z15,z2,z163,z4,z5,z17]),(0,[z0,z2,z3,z991,z5,z6]),(0,[z18,z925,z2,z4,z5,z6]),(0,[z18,z0,z302,z4,z5,z6]),(0,[z0,z2,z3,z137,z5,z185])],[(0,[z0,z2,z3,z4,z992,z6]),(0,[z0,z24,z4,z145,z5,z6]),(0,[z0,z993,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z994]),(0,[z0,z2,z3,z4,z5,z995]),(0,[z7,z177,z24,z4,z5,z6]),(0,[z0,z153,z24,z4,z5,z36]),(0,[z0,z2,z3,z224,z5,z285])]],
   [[(0,[z0,z2,z3,z4,z996,z6]),(0,[z0,z2,z3,z4,z997,z6]),(0,[z0,z2,z163,z4,z28,z6]),(0,[z0,z453,z24,z4,z5,z6]),(0,[z0,z98,z3,z4,z452,z6]),(0,[z266,z0,z2,z4,z5,z518])],[(0,[z42,z0,z2,z4,z30,z6]),(0,[z0,z998,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z999]),(0,[z0,z2,z3,z1000,z5,z6]),(0,[z7,z0,z3,z4,z206,z8]),(0,[z1001,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z1002])],[(0,[z0,z2,z3,z1003,z5,z6]),(0,[z0,z216,z3,z449,z5,z6]),(0,[z394,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z450,z5,z150]),(0,[z80,z0,z3,z4,z113,z550])],[(0,[z196,z121,z2,z3,z5,z6]),(0,[z15,z2,z16,z4,z5,z17]),(0,[z0,z2,z3,z4,z1004,z6]),(0,[z1005,z0,z2,z4,z5,z6]),(0,[z0,z2,z773,z4,z5,z6]),(0,[z1006,z0,z2,z4,z5,z6])],[(0,[z0,z2,z1007,z4,z5,z6]),(0,[z0,z2,z16,z4,z57,z6]),(0,[z71,z2,z3,z449,z5,z6]),(0,[z0,z2,z24,z5,z6,z158]),(0,[z0,z435,z24,z4,z5,z6]),(0,[z1008,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1009,z4,z5,z6]),(1,[z2,z3,z4,z757,z6]),(0,[z0,z672,z24,z4,z5,z6]),(0,[z646,z0,z2,z3,z5,z27]),(0,[z470,z0,z3,z4,z5,z8]),(0,[z0,z2,z29,z4,z62,z6])],[(0,[z0,z2,z1010,z4,z5,z6]),(0,[z15,z31,z3,z4,z5,z17]),(0,[z0,z2,z418,z4,z5,z6]),(0,[z1011,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z739])],[(0,[z0,z31,z3,z4,z57,z6]),(0,[z0,z3,z24,z314,z5,z6]),(0,[z0,z2,z1012,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1013])]],
   [[(0,[z0,z2,z3,z5,z6,z1014]),(0,[z15,z2,z3,z5,z158,z17]),(0,[z0,z933,z2,z4,z5,z6]),(0,[z0,z3,z24,z4,z487,z6]),(0,[z0,z2,z3,z4,z5,z855]),(0,[z394,z2,z3,z4,z5,z285]),(0,[z61,z394,z2,z4,z30,z6])],[(0,[z0,z613,z24,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z826]),(0,[z1015,z2,z3,z4,z5,z6]),(0,[z0,z302,z52,z4,z5,z6])],[(0,[z107,z779,z2,z4,z5,z6]),(0,[z189,z0,z2,z3,z5,z67])],[(0,[z0,z2,z24,z4,z487,z6]),(0,[z488,z2,z24,z4,z5,z6]),(0,[z0,z2,z3,z1016,z5,z6]),(0,[z0,z2,z3,z787,z5,z6]),(0,[z295,z2,z3,z4,z487,z6])],[(0,[z0,z2,z3,z4,z1017,z6]),(0,[z861,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z550]),(0,[z0,z2,z1018,z4,z5,z6])],[(0,[z0,z1019,z2,z3,z5,z6]),(0,[z1020,z2,z3,z4,z5,z6]),(0,[z0,z175,z933,z4,z5,z6]),(0,[z636,z0,z2,z3,z4,z170]),(0,[z0,z2,z3,z4,z5,z1021])],[(0,[z0,z194,z3,z4,z5,z6]),(0,[z0,z2,z1022,z4,z5,z6]),(0,[z56,z190,z2,z3,z5,z6]),(0,[z1023,z2,z3,z4,z5,z6]),(0,[z1024,z0,z3,z4,z5,z6])],[(0,[z23,z12,z24,z4,z5,z6]),(0,[z292,z0,z201,z4,z5,z6]),(0,[z359,z195,z2,z4,z5,z6]),(0,[z0,z2,z1025,z4,z5,z6]),(0,[z0,z2,z3,z1026,z5,z6]),(0,[z0,z175,z24,z165,z5,z6]),(0,[z180,z0,z2,z24,z210,z6]),(0,[z0,z2,z447,z4,z5,z6]),(0,[z33,z175,z3,z165,z5,z6]),(0,[z212,z0,z2,z4,z5,z275]),(0,[z0,z2,z3,z4,z87,z10])]],
   [[(0,[z0,z1027,z3,z4,z5,z6]),(0,[z0,z2,z3,z449,z5,z6]),(0,[z1028,z2,z3,z4,z5,z6]),(0,[z212,z0,z2,z4,z5,z518]),(0,[z0,z2,z1029,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1030]),(0,[z0,z2,z535,z4,z5,z169])],[(0,[z156,z0,z3,z4,z5,z8]),(0,[z0,z94,z24,z4,z5,z6]),(0,[z189,z18,z0,z2,z5,z27]),(0,[z0,z1031,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z4,z170]),(0,[z0,z2,z3,z4,z6,z823])],[(0,[z246,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z854,z5,z6]),(0,[z0,z696,z24,z4,z5,z6]),(0,[z1032,z0,z2,z4,z5,z6]),(0,[z0,z2,z69,z4,z206,z6]),(0,[z0,z2,z710,z4,z5,z6]),(0,[z61,z0,z2,z4,z30,z285])],[(0,[z12,z24,z63,z4,z5,z6]),(0,[z196,z18,z0,z2,z5,z6]),(0,[z0,z501,z24,z4,z5,z6]),(0,[z18,z0,z98,z4,z88,z6]),(0,[z0,z60,z3,z4,z5,z285]),(0,[z1033,z2,z3,z4,z5,z6])],[(0,[z121,z183,z3,z4,z5,z6]),(0,[z90,z2,z3,z4,z13,z6]),(0,[z0,z2,z1034,z4,z5,z6]),(0,[z0,z1035,z2,z4,z5,z6]),(0,[z1036,z2,z3,z4,z5,z6]),(0,[z0,z1037,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1038,z5,z6]),(0,[z129,z31,z3,z4,z5,z6]),(0,[z175,z176,z3,z165,z5,z6]),(0,[z177,z2,z3,z116,z5,z6])],[(0,[z190,z2,z3,z459,z5,z6]),(0,[z0,z2,z3,z4,z5,z1039]),(0,[z0,z2,z4,z5,z89,z6]),(0,[z0,z1040,z3,z4,z5,z6]),(0,[z0,z2,z3,z1041,z5,z6])]],
   [[(0,[z0,z1042,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z469]),(0,[z0,z3,z4,z5,z6,z1043]),(0,[z646,z0,z24,z4,z5,z6]),(0,[z0,z365,z24,z4,z5,z6]),(0,[z177,z2,z124,z4,z5,z6])],[(0,[z121,z18,z23,z4,z5,z6]),(0,[z129,z2,z3,z4,z5,z759]),(0,[z0,z2,z3,z4,z1044,z6]),(0,[z246,z2,z3,z4,z5,z150]),(0,[z80,z0,z81,z4,z113,z6]),(0,[z0,z2,z1045,z4,z5,z6])],[(0,[z0,z516,z24,z4,z5,z6]),(0,[z0,z308,z24,z4,z5,z6]),(0,[z0,z24,z4,z314,z5,z6]),(0,[z176,z3,z24,z4,z5,z6]),(0,[z1046,z2,z3,z4,z5,z6])],[(0,[z15,z2,z3,z4,z28,z17])],[(0,[z0,z1047,z2,z4,z5,z6]),(0,[z0,z2,z1048,z4,z5,z6]),(0,[z0,z2,z3,z116,z5,z6]),(0,[z0,z2,z1049,z4,z5,z6]),(0,[z0,z2,z3,z64,z126,z6]),(0,[z0,z2,z4,z62,z873,z6])],[(0,[z18,z0,z2,z4,z5,z6]),(0,[z0,z216,z945,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z176,z2,z24,z4,z5,z6]),(0,[z1051,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1052]),(1,[z0,z3,z4,z733,z6])],[(0,[z0,z2,z1053,z4,z5,z6]),(0,[z0,z2,z91,z444,z5,z6]),(0,[z0,z1054,z3,z4,z5,z6]),(0,[z0,z2,z124,z4,z5,z6]),(0,[z266,z0,z24,z4,z5,z6]),(0,[z441,z0,z24,z4,z5,z6]),(0,[z0,z24,z4,z5,z6,z289]),(0,[z0,z226,z4,z62,z5,z6]),(0,[z0,z2,z4,z5,z6,z1055])],[(0,[z54,z2,z161,z4,z5,z6]),(0,[z488,z2,z3,z4,z5,z6]),(0,[z0,z302,z24,z4,z5,z6]),(0,[z0,z2,z3,z4,z487,z6]),(0,[z0,z103,z3,z137,z5,z6])]],
   [[(0,[z121,z2,z3,z444,z5,z6]),(0,[z292,z472,z2,z4,z5,z6]),(0,[z18,z246,z2,z4,z5,z6]),(0,[z1056,z0,z2,z4,z5,z6]),(0,[z1057,z2,z3,z4,z5,z6]),(0,[z80,z0,z102,z4,z113,z6]),(0,[z0,z418,z4,z5,z36,z6]),(0,[z0,z60,z3,z4,z5,z185]),(0,[z0,z1058,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z10,z823])],[(0,[z0,z2,z3,z1059,z5,z6]),(0,[z33,z2,z3,z165,z5,z6]),(0,[z1060,z2,z3,z4,z5,z6]),(0,[z1061,z0,z3,z4,z5,z6])],[(0,[z111,z0,z3,z145,z5,z6]),(0,[z0,z2,z3,z4,z1062,z6]),(0,[z0,z2,z1063,z4,z5,z6]),(0,[z0,z1064,z2,z4,z5,z6]),(0,[z0,z1065,z2,z4,z5,z6])],[(0,[z190,z18,z2,z101,z5,z6]),(0,[z1066,z0,z3,z4,z5,z6]),(0,[z7,z0,z24,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z150]),(0,[z0,z175,z3,z165,z5,z6]),(0,[z268,z2,z3,z450,z5,z6])],[(0,[z0,z2,z3,z4,z1067,z6]),(0,[z107,z195,z2,z4,z5,z6]),(0,[z0,z1068,z3,z4,z5,z6]),(0,[z0,z2,z1069,z4,z5,z6]),(0,[z1070,z0,z2,z4,z5,z6])],[(0,[z0,z2,z332,z4,z5,z106])],[(0,[z0,z721,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z1071,z6]),(0,[z0,z1072,z3,z4,z5,z6]),(0,[z0,z2,z3,z1073,z5,z6]),(0,[z0,z24,z4,z311,z5,z6]),(0,[z0,z2,z24,z4,z5,z185]),(0,[z0,z2,z1074,z4,z5,z6]),(0,[z61,z0,z226,z4,z5,z6]),(0,[z1075,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1076]),(0,[z1077,z0,z2,z4,z5,z6])],[(0,[z0,z1078,z3,z4,z5,z6]),(0,[z0,z689,z24,z4,z5,z6]),(0,[z1079,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z87,z635]),(0,[z1080,z0,z2,z4,z5,z6]),(0,[z7,z0,z24,z4,z5,z36])]],
   [[(0,[z0,z1081,z3,z4,z5,z6]),(0,[z0,z2,z16,z589,z5,z6]),(0,[z421,z0,z3,z4,z5,z6]),(1,[z861,z0,z4,z5,z6])],[(0,[z0,z2,z81,z4,z5,z150]),(0,[z0,z1037,z303,z4,z5,z6])],[(0,[z2,z3,z4,z25,z757,z6]),(0,[z394,z2,z3,z224,z5,z6])],[(0,[z0,z2,z163,z4,z5,z6]),(0,[z0,z31,z3,z589,z5,z6]),(0,[z0,z2,z24,z450,z5,z6]),(0,[z0,z24,z4,z496,z5,z6]),(0,[z1082,z2,z3,z4,z5,z6])],[(0,[z1083,z0,z3,z4,z5,z6]),(0,[z18,z0,z2,z882,z5,z6])],[(0,[z152,z0,z2,z4,z5,z6]),(0,[z0,z51,z24,z112,z5,z6]),(0,[z641,z0,z2,z3,z210,z6])],[(0,[z0,z393,z24,z4,z5,z6]),(0,[z0,z31,z163,z4,z5,z6]),(0,[z0,z177,z24,z4,z5,z6]),(0,[z0,z430,z24,z4,z5,z6]),(0,[z845,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1084]),(0,[z177,z2,z3,z4,z206,z6]),(0,[z7,z0,z124,z4,z5,z8])],[(0,[z0,z2,z3,z1085,z5,z6]),(0,[z470,z0,z3,z4,z113,z6]),(0,[z0,z1086,z3,z4,z5,z6])]],
   [[(0,[z0,z183,z3,z165,z5,z6]),(0,[z0,z2,z3,z4,z5,z1087]),(0,[z0,z2,z102,z4,z5,z150]),(0,[z0,z2,z3,z4,z823,z170])],[(0,[z0,z23,z24,z4,z5,z6]),(0,[z0,z2,z1088,z4,z5,z6]),(0,[z0,z176,z24,z4,z5,z6]),(0,[z0,z24,z4,z5,z36,z170]),(0,[z189,z0,z2,z24,z5,z27]),(0,[z0,z2,z3,z1089,z5,z6]),(0,[z1090,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1091,z5,z6]),(0,[z0,z24,z4,z5,z509,z6])],[(0,[z0,z1092,z3,z4,z5,z6]),(0,[z0,z31,z16,z4,z5,z6]),(0,[z0,z302,z3,z4,z5,z6]),(0,[z0,z24,z4,z5,z337,z6]),(0,[z180,z18,z0,z2,z210,z6]),(0,[z268,z2,z3,z4,z5,z550]),(0,[z177,z3,z4,z5,z6,z8]),(0,[z488,z2,z3,z224,z5,z6]),(0,[z421,z0,z332,z4,z5,z169])],[(0,[z0,z2,z3,z5,z1093,z6]),(0,[z0,z2,z3,z1094,z5,z6]),(0,[z0,z98,z24,z4,z113,z6]),(0,[z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z4,z5,z838,z275]),(0,[z0,z2,z1095,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1096,z6]),(0,[z33,z2,z3,z112,z5,z6]),(0,[z61,z0,z2,z224,z30,z6])],[(0,[z0,z24,z4,z5,z347,z6]),(0,[z0,z2,z1097,z4,z5,z6]),(0,[z0,z329,z24,z4,z5,z6]),(0,[z0,z2,z535,z4,z5,z188]),(0,[z0,z2,z3,z277,z5,z550]),(0,[z1098,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z854,z5,z6]),(0,[z40,z2,z3,z4,z13,z6]),(0,[z0,z324,z24,z112,z5,z6]),(0,[z0,z175,z32,z4,z5,z6])]],
   [[(0,[z0,z2,z1099,z4,z5,z6]),(0,[z412,z2,z161,z4,z5,z6]),(0,[z0,z1100,z3,z4,z5,z6]),(0,[z15,z216,z3,z4,z5,z17]),(0,[z0,z2,z273,z4,z133,z6]),(0,[z68,z0,z60,z4,z5,z6]),(0,[z0,z2,z1101,z4,z5,z6])],[(0,[z22,z2,z3,z4,z25,z6]),(0,[z0,z216,z3,z4,z57,z6]),(0,[z0,z24,z4,z5,z6,z356])],[(0,[z0,z2,z3,z1102,z5,z6]),(0,[z0,z1103,z3,z4,z5,z6]),(0,[z0,z1104,z2,z4,z5,z6]),(0,[z0,z2,z24,z1016,z5,z6]),(0,[z0,z998,z2,z24,z5,z6]),(0,[z0,z24,z4,z529,z5,z6]),(0,[z0,z2,z3,z4,z5,z185]),(0,[z1105,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1106,z5,z6]),(0,[z0,z23,z24,z145,z5,z6]),(0,[z1107,z0,z2,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z550]),(0,[z0,z24,z358,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1108]),(0,[z61,z0,z103,z4,z30,z6]),(0,[z0,z1109,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1110,z5,z6]),(0,[z0,z1111,z3,z4,z5,z6]),(0,[z0,z2,z1112,z4,z5,z6]),(0,[z18,z0,z2,z5,z6,z158]),(1,[z177,z24,z4,z5,z6]),(0,[z0,z98,z3,z4,z88,z6]),(0,[z2,z3,z4,z5,z6,z1113])],[(0,[z0,z194,z24,z4,z5,z6]),(0,[z111,z0,z3,z314,z5,z6]),(0,[z246,z2,z3,z277,z5,z6]),(0,[z0,z3,z4,z5,z6,z739])],[(0,[z0,z12,z24,z4,z5,z6]),(0,[z0,z2,z1114,z4,z5,z6]),(0,[z2,z3,z854,z101,z5,z6]),(0,[z0,z1115,z2,z4,z5,z6]),(0,[z0,z2,z24,z4,z87,z10]),(1,[z0,z2,z3,z4,z823])],[(0,[z0,z2,z3,z1116,z5,z6]),(0,[z0,z2,z3,z4,z5,z1117]),(0,[z0,z653,z24,z4,z5,z6]),(0,[z111,z18,z0,z4,z5,z6]),(1,[z176,z24,z4,z5,z6]),(0,[z0,z1118,z2,z4,z5,z6]),(0,[z0,z2,z1119,z4,z5,z6])]],
   [[(0,[z12,z3,z4,z5,z6,z377]),(0,[z156,z2,z3,z4,z5,z17]),(0,[z0,z721,z24,z4,z5,z6]),(0,[z15,z2,z3,z4,z5,z67]),(0,[z2,z3,z63,z449,z5,z6]),(0,[z0,z2,z3,z589,z28,z6]),(0,[z196,z2,z3,z5,z19,z6]),(0,[z1120,z2,z3,z4,z5,z6])],[(0,[z22,z2,z3,z4,z229,z6]),(0,[z0,z1121,z2,z4,z5,z6]),(0,[z0,z1122,z2,z4,z5,z6]),(0,[z0,z2,z273,z4,z62,z6]),(0,[z0,z51,z3,z112,z5,z6]),(0,[z1123,z2,z3,z4,z5,z6])],[(0,[z246,z2,z24,z4,z5,z6]),(0,[z18,z0,z2,z314,z5,z6]),(0,[z267,z0,z226,z4,z5,z6]),(0,[z0,z2,z4,z873,z30,z6])],[(0,[z0,z2,z1124,z4,z5,z6]),(0,[z0,z2,z1125,z4,z5,z6]),(0,[z0,z2,z124,z314,z5,z6])],[(0,[z18,z0,z31,z4,z5,z6]),(0,[z0,z24,z4,z5,z6,z545]),(0,[z7,z0,z418,z4,z5,z6]),(0,[z0,z2,z3,z314,z487,z6])],[(0,[z121,z738,z3,z4,z5,z6]),(0,[z0,z773,z4,z5,z210,z6]),(0,[z0,z2,z3,z5,z21,z711])],[(0,[z15,z2,z3,z4,z5,z17]),(0,[z212,z0,z2,z4,z5,z838])],[(0,[z0,z2,z3,z4,z57,z6]),(0,[z267,z0,z2,z146,z5,z6]),(0,[z18,z0,z2,z277,z5,z6]),(0,[z18,z394,z2,z4,z5,z6]),(0,[z176,z2,z447,z4,z5,z6]),(0,[z1126,z2,z3,z4,z5,z6]),(0,[z0,z2,z93,z5,z561,z6])]],
   [[(0,[z190,z2,z3,z449,z5,z6]),(0,[z0,z2,z1127,z4,z5,z6]),(0,[z0,z2,z16,z4,z28,z6]),(0,[z7,z0,z24,z314,z5,z6]),(0,[z0,z2,z3,z5,z756,z6]),(0,[z253,z0,z2,z74,z5,z6]),(0,[z488,z60,z3,z4,z5,z6]),(0,[z0,z2,z1128,z4,z5,z6])],[(0,[z0,z24,z4,z5,z10,z36])],[(0,[z0,z2,z1129,z4,z5,z6]),(0,[z18,z0,z201,z4,z5,z6]),(0,[z0,z2,z1130,z4,z5,z6]),(0,[z0,z2,z1131,z4,z5,z6]),(0,[z268,z2,z81,z4,z5,z6])],[(0,[z0,z31,z3,z4,z28,z6]),(0,[z0,z2,z24,z116,z5,z6]),(0,[z0,z324,z3,z112,z5,z6]),(0,[z1132,z2,z3,z4,z5,z6]),(0,[z1133,z2,z3,z4,z5,z6]),(0,[z295,z2,z3,z116,z5,z6]),(0,[z2,z3,z4,z5,z6,z1134])],[(0,[z0,z2,z3,z1135,z5,z6]),(0,[z0,z24,z4,z113,z6,z170]),(0,[z0,z3,z4,z733,z113,z6]),(0,[z0,z2,z3,z4,z87,z685]),(0,[z177,z2,z69,z4,z5,z6])],[(0,[z0,z1136,z3,z4,z5,z6]),(0,[z0,z2,z81,z277,z5,z6]),(0,[z295,z2,z124,z4,z5,z6]),(0,[z0,z49,z226,z118,z5,z6])],[(0,[z121,z23,z91,z4,z5,z6]),(0,[z0,z24,z20,z112,z5,z6]),(0,[z0,z2,z3,z224,z5,z185])],[(0,[z421,z18,z0,z4,z5,z6])]],
   [[(0,[z0,z2,z1137,z4,z5,z6]),(0,[z2,z3,z4,z757,z13,z6]),(0,[z71,z2,z3,z5,z21,z6])],[(0,[z48,z0,z24,z4,z5,z6]),(0,[z42,z0,z3,z4,z113,z6]),(0,[z0,z625,z24,z4,z5,z6]),(0,[z268,z2,z102,z4,z5,z6])],[(0,[z214,z0,z24,z4,z5,z6]),(0,[z0,z23,z418,z4,z5,z6]),(0,[z0,z52,z24,z4,z5,z6]),(0,[z0,z296,z24,z4,z5,z6]),(0,[z18,z295,z2,z4,z5,z6]),(0,[z18,z0,z2,z4,z5,z285])],[(0,[z0,z1138,z3,z4,z5,z6]),(0,[z0,z103,z93,z4,z5,z6])],[(0,[z0,z24,z4,z5,z422,z6]),(0,[z0,z2,z102,z277,z5,z6]),(0,[z488,z2,z3,z4,z5,z285])],[(0,[z0,z2,z3,z1139,z5,z6]),(0,[z0,z2,z3,z1140,z5,z6]),(0,[z0,z2,z3,z4,z5,z1141])],[(0,[z0,z1142,z3,z4,z5,z6]),(0,[z0,z49,z103,z4,z5,z6])],[(0,[z0,z2,z3,z1143,z5,z6]),(0,[z0,z2,z24,z589,z5,z6]),(0,[z421,z0,z24,z4,z5,z6]),(0,[z394,z2,z3,z4,z5,z185])]],
   [[(0,[z0,z276,z24,z4,z5,z6]),(0,[z7,z295,z24,z4,z5,z6])],[(0,[z0,z1144,z3,z4,z5,z6]),(0,[z0,z644,z24,z4,z5,z6]),(0,[z0,z1,z2,z122,z5,z6]),(0,[z111,z68,z0,z4,z5,z6]),(0,[z0,z2,z3,z314,z206,z6])],[(0,[z0,z2,z1145,z4,z5,z6]),(0,[z645,z0,z2,z4,z5,z416]),(0,[z68,z0,z24,z4,z5,z6])],[(0,[z0,z2,z91,z4,z5,z6]),(0,[z0,z1146,z3,z4,z5,z6]),(0,[z0,z24,z4,z445,z5,z6]),(0,[z0,z103,z3,z4,z5,z6]),(0,[z0,z2,z29,z4,z873,z6])],[(0,[z1147,z0,z2,z4,z5,z6])],[(0,[z0,z216,z3,z589,z5,z6]),(0,[z1148,z2,z3,z4,z5,z6]),(0,[z0,z1149,z3,z4,z5,z6])],[(0,[z341,z2,z3,z4,z13,z6])],[(0,[z0,z2,z3,z4,z5,z1150]),(0,[z0,z2,z1151,z4,z5,z6]),(0,[z0,z2,z3,z1152,z5,z6]),(0,[z0,z2,z3,z4,z733,z6]),(0,[z7,z177,z3,z4,z5,z8])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 513).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1039).take 186) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1225)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [513, 526, 186] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 95).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 183).take 73).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [95, 88, 73] = true :=
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

end PEqualNP.Outside.L_meta_46262

theorem PEqualNP.Outside.L_meta_46262 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277070016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277070016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46262.solve