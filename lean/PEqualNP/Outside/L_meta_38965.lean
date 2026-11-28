import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38965

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4241026248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa0044c18dc489c8a#64 ++ 0x340089831b891391#64 ++ 0xdc0cfd39fc49bc9b#64 ++ 0xfb819fa73f893793#64 : BitVec 256),
   (0x4011204220130130#64 ++ 0x8802240844026026#64 ++ 0xba3322c6307fc7ff#64 ++ 0xf7466458c60ff8ff#64 : BitVec 256),
   (0x80c2c305458c68c3#64 ++ 0x10185860a8b18d18#64 ++ 0x7dc3c307cf8e78e7#64 ++ 0x6fb87860f9f1cf1c#64 : BitVec 256),
   (0x016c03a80ae07604#64 ++ 0x202d8075015c0ec0#64 ++ 0xfffc03f80ff07f06#64 ++ 0xdfff807f01fe0fe0#64 : BitVec 256),
   (0x05bff4000f7f8007#64 ++ 0xc0b7fe8001eff000#64 ++ 0xf5fffc000fff8006#64 ++ 0x3ebfff8001fff000#64 : BitVec 256),
   (0x03fbbbf7b0000000#64 ++ 0x007f777ef6000000#64 ++ 0xf3fffffff0000001#64 ++ 0xfe7ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc03f80ff07f06 0xdfff807f01fe0fe0

def z1 : W := mkw 0x020008f2b0000000 0x0040011e56000000 0x020000f830000000 0x8040001f06000000

def z2 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z3 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc000fff8006 0x3ebfff8001fff000

def z4 : W := mkw 0x4011204220130130 0x8802240844026026 0xba3322c6307fc7ff 0xf7466458c60ff8ff

def z5 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc3c307cf8e78e7 0x6fb87860f9f1cf1c

def z6 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0cfd39fc49bc9b 0xfb819fa73f893793

def z7 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff049849b 0xff7ffffffe093093

def z8 : W := mkw 0xa5bffc10df7f888f 0xd4b7ff821beff111 0xf5fffc01ffff809f 0x3ebfff803ffff013

def z9 : W := mkw 0x0000081090000000 0x0000010212000000 0xd00cfd39f0000001 0xfa019fa73e000000

def z10 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x2dc302060f8e78e6 0x05b86040c1f1cf1c

def z11 : W := mkw 0xe5bffc5aff7f9dbf 0xfcb7ff8b5feff3b7 0xffffffffffffffff 0xffffffffffffffff

def z12 : W := mkw 0x07fffff7bf7f8007 0xc0fffffef7eff000 0xf7ffffffffff8007 0xfefffffffffff000

def z13 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x45cffc000f8f8000 0x28b9ff8001f1f000

def z14 : W := mkw 0x053d34000a738004 0xc0a7a680014e7000 0x803c3c0000718000 0x10078780000e3000

def z15 : W := mkw 0xa5aedc18df6c9c8f 0x74b5db831bed9391 0xddccfd39ffc9bc9b 0xfbb99fa73ff93793

def z16 : W := mkw 0x016803a000000000 0x002d007400000000 0xf3fc03f800000000 0xde7f807f00000000

def z17 : W := mkw 0x03ffbbffbae07604 0x207ff77ff75c0ec0 0xfffffffffff07f07 0xfffffffffffe0fe0

def z18 : W := mkw 0x01bfb0000a600004 0x0037f600014c0000 0xf5fffc000ff00006 0x3ebfff8001fe0000

def z19 : W := mkw 0xa0c2cb1dd58c7ccb 0x34185963bab18f99 0x7dc3c33fff8e7cff 0xefb87867fff1cf9f

def z20 : W := mkw 0x4011204220130130 0x8802240844026026 0x00032006300f80f9 0x20006400c601f01f

def z21 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf5fffc063fff80ff 0x3ebfff80c7fff01f

def z22 : W := mkw 0x036c0bffbae07604 0x206d817ff75c0ec0 0xfffc03fffff07f07 0xdfff807ffffe0fe0

def z23 : W := mkw 0x0493b00001170001 0xc09276000022e000 0x0003000000060000 0x000060000000c000

def z24 : W := mkw 0xa0c2cf15d58ce8cb 0x141859e2bab19d19 0x7dc3ff07ff8ff8ff 0x6fb87fe0fff1ff1f

def z25 : W := mkw 0x016803a800807600 0x202d007500100ec0 0xfbfc03f800007f00 0xdf7f807f00000fe0

def z26 : W := mkw 0x82400bf7f08068c0 0x1048017efe100d18 0x0a0003fff00078e1 0xc140007ffe000f1c

def z27 : W := mkw 0x83fbfbf7f58c68c3 0x107f7f7efeb18d18 0xffffffffff8e78e7 0xfffffffffff1cf1c

def z28 : W := mkw 0x0486c4000f7f8007 0xc090d88001eff000 0x75c3c0000fff8006 0x2eb8780001fff000

def z29 : W := mkw 0x20040c1898409408 0x2400818313081281 0x800c3c3830418418 0x9001878706083083

def z30 : W := mkw 0x8000400044080882 0x1000080008810110 0x5c00c101cc083883 0x6b80182039810710

def z31 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff07fc7ff 0xff7ffffffe0ff8ff

def z32 : W := mkw 0x80004000458c68c3 0x1000080008b18d18 0x040000000f803800 0x0080000001f00700

def z33 : W := mkw 0x05fff7a80ffff607 0xe0bffef501fffec0 0xfffffff80fffff06 0xffffffff01ffffe0

def z34 : W := mkw 0x80400305408068c0 0x10080060a8100d18 0x08000307c00078e1 0x41000060f8000f1c

def z35 : W := mkw 0x016c0bb89ae07604 0x202d8177135c0ec0 0xfffcfff9fff07f07 0xffff9fff3ffe0fe0

def z36 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x4fcc03f80f807f00 0xc9f9807f01f00fe0

def z37 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0xf1fffd39c0000000 0x3e3fffa738000000

def z38 : W := mkw 0xa0040818d8401c88 0x340081031b080391 0xdc0c0139fc403c9b 0xdb8180273f880793

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x38030206000e40e7 0x67006040c001c81c

def z40 : W := mkw 0xc0d3e347659f69f3 0x981a7c68ecb3ed3e 0xfff3e3c7ffffffff 0xfffe7c78ffffffff

def z41 : W := mkw 0x42400bf7b0000130 0x0848017ef6000026 0x0a0003fff00047f9 0xc140007ffe0008ff

def z42 : W := mkw 0x80004810d4080882 0x100009021a810110 0xdc0cfd39fc083883 0xfb819fa73f810710

def z43 : W := mkw 0x004003a800807600 0x2008007500100ec0 0x0a0003f800007f00 0xc140007f00000fe0

def z44 : W := mkw 0x20000c1090008008 0x0400018212001001 0x00003c0030018018 0x0000078006003003

def z45 : W := mkw 0x4011204220130130 0x8802240844026026 0x2a3302c6303647fd 0xc5466058c606c8ff

def z46 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x41ccdd39c0000000 0x08399ba738000000

def z47 : W := mkw 0x0493f400051f8003 0xc0927e8000a3f000 0x0003fc00000f8000 0x20007f800001f000

def z48 : W := mkw 0x0482d400050c8003 0x40905a8000a19000 0x0000dc0000000000 0x00001b8000000000

def z49 : W := mkw 0xa2444ffffc489c8a 0x344889ffff891391 0xde0cfffffc49bc9b 0xfbc19fffff893793

def z50 : W := mkw 0x8082c005450c08c3 0x10105800a8a18118 0x0003c007c00e00e1 0x20007800f801c01c

def z51 : W := mkw 0x040444000f7f8007 0xc080888001eff000 0x040000000fff8006 0x0080000001fff000

def z52 : W := mkw 0xa5bffc18df7f9c8f 0xf4b7ff831beff391 0xfdfffd39ffffbc9f 0xffbfffa73ffff793

def z53 : W := mkw 0x02400bb590000000 0x00480176b2000000 0x00000139c0000000 0x0000002738000000

def z54 : W := mkw 0x20040c1898409408 0x2400818313081281 0x000c1c3800000000 0x0001838700000000

def z55 : W := mkw 0x45bbb04223370135 0xc8b776084466e026 0xbbf322c633ffc7ff 0xf77e6458c67ff8ff

def z56 : W := mkw 0xe0116c52f41b89ba 0x9c022d8a5e837137 0xba33fec7f07fc7ff 0xf7467fd8fe0ff8ff

def z57 : W := mkw 0x4011204220130130 0x8802240844026026 0x023000c000300300 0x0046001800060060

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0x980020003049849b 0xf300040006093093

def z59 : W := mkw 0x4011204220130130 0x8802240844026026 0x223302c600364364 0x04466058c006c86c

def z60 : W := mkw 0xa00044004408888a 0x1400088008811111 0x0000000000098098 0x0000000000013013

def z61 : W := mkw 0x02400bf7b0000000 0x0048017ef6000000 0x020003fff0000001 0xc040007ffe000000

def z62 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffec63fffc7ff 0xffffffd8c7fff8ff

def z63 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x040000000c003800 0x0080000001800700

def z64 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x440cdd39cc003800 0x08819ba739800700

def z65 : W := mkw 0x05eed7a80fecf607 0x60bddaf501fd9ec0 0x45ccdd380f803800 0x08b99ba701f00700

def z66 : W := mkw 0x80004000458c68c3 0x1000080008b18d18 0x3c0302060f8e78e7 0x67806040c1f1cf1c

def z67 : W := mkw 0xa0000818d0001c88 0x340001031a000391 0x08000139f0003c99 0xc10000273e000793

def z68 : W := mkw 0xc0116042641b09b2 0x98022c084c836136 0xfe33e3c7fc7fffff 0xffc67c78ff8fffff

def z69 : W := mkw 0x4011204220130130 0x8802240844026026 0x3a3302c6003e43e7 0x67466058c007c87c

def z70 : W := mkw 0x012c00a80a601604 0x20258015014c02c0 0x823c00f800700700 0x9047801f000e00e0

def z71 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000000c49bc9a 0x0180000001893793

def z72 : W := mkw 0xa16c4fb8dee8fe8e 0x342d89f71bdd1fd1 0xfffcfff9fff9ff9f 0xffff9fff3fff3ff3

def z73 : W := mkw 0x03fbb3e720000000 0x007f767ce4000000 0x23f302c600000000 0x047e6058c0000000

def z74 : W := mkw 0x07fff7e72f7f8007 0xc0fffefce5eff000 0xf7fffec60fff8006 0x3effffd8c1fff000

def z75 : W := mkw 0xa0040c18d8409c88 0x340081831b081391 0x880c3d39f041bc99 0xd10187a73e083793

def z76 : W := mkw 0x000444000c488002 0x0000888001891000 0xd40cfc000c498002 0x3a819f8001893000

def z77 : W := mkw 0x20040c1898409408 0x2400818313081281 0x980c3c383049849b 0xf301878706093093

def z78 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdc3e307ffcffcff 0xffb87c60fff9ff9f

def z79 : W := mkw 0x0086c4000d4c8003 0x0010d88001a99000 0xf5cffc000fcf8006 0x3eb9ff8001f9f000

def z80 : W := mkw 0xa0c6cf1dddccfccb 0x3418d9e3bbb99f99 0xfdcfff3fffcffcff 0xffb9ffe7fff9ff9f

def z81 : W := mkw 0x041564000f7f8007 0xc082ac8001eff000 0xb43320000fff8006 0x3686640001fff000

def z82 : W := mkw 0x816c03ad4ae07ec4 0x302d8075a95c0fd8 0xfffc03ffcff07fe7 0xdfff807ff9fe0ffc

def z83 : W := mkw 0x85bff4054f7f88c7 0xd0b7fe80a9eff118 0xf5fffc07cfff80e7 0x3ebfff80f9fff01c

def z84 : W := mkw 0x4000000000000130 0x0800000000000026 0x08000000000047f8 0x01000000000008ff

def z85 : W := mkw 0x07fbb3e723370005 0xc0ff767ce466e000 0x23f302c603b60004 0x047e6058c076c000

def z86 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x63ffdfffc0000000 0x0c7ffbfff8000000

def z87 : W := mkw 0x05bbf000073f0007 0xc0b77e0000e7e000 0x75f3c0000fbe0006 0x2ebe780001f7c000

def z88 : W := mkw 0x43ffbbffbaf37734 0xa87ff77ff75e6ee6 0xffffffffffffffff 0xffffffffffffffff

def z89 : W := mkw 0x4093e042251f0133 0x88127c0844a3e026 0xfff3e2c63fffc7ff 0xfffe7c58c7fff8ff

def z90 : W := mkw 0x4011204220130130 0x8802240844026026 0x9a3020c03079879b 0xf3460418060f30f3

def z91 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x23f303fff0000001 0xc47e607ffe000000

def z92 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x45ccdc000f800000 0x08b99b8001f00000

def z93 : W := mkw 0x81eec3ad4fec7ec7 0x303dd875a9fd8fd8 0xffffc3ffcffe7fe7 0xfffff87ff9ffcffc

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x3003020600000001 0x66006040c0000000

def z95 : W := mkw 0x80004000450c08c3 0x1000080008a18118 0x00000000000e00e0 0x000000000001c01c

def z96 : W := mkw 0xa0004c10d408888a 0x140009821a811111 0xd00cfd39f0098099 0xfa019fa73e013013

def z97 : W := mkw 0x8082c005450c08c3 0x10105800a8a18118 0x3803c207c00e40e7 0x67007840f801c81c

def z98 : W := mkw 0x00c2830500000000 0x00185060a0000000 0x21c3020600000000 0x04386040c0000000

def z99 : W := mkw 0x02d3bbf7b0000000 0x005a777ef6000000 0x0203fffff0000001 0xe0407ffffe000000

def z100 : W := mkw 0x016803a002a06204 0x002d007400540c40 0x01c0000003800000 0x0038000000700000

def z101 : W := mkw 0x012c00080ae07604 0x20258001015c0ec0 0xfdfc00000ff07f06 0x1fbf800001fe0fe0

def z102 : W := mkw 0x4000004220000130 0x0800000844000026 0x0a0002c6300047f9 0xc1400058c60008ff

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z104 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x71cfdf3fc0000001 0x6e39fbe7f8000000

def z105 : W := mkw 0x02d3bb57b0000000 0x005a776af6000000 0x71c3ff07f0000001 0x6e387fe0fe000000

def z106 : W := mkw 0xa293fc57f408888a 0x14527f8afe811111 0x0003fc07f0098099 0x20007f80fe013013

def z107 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0x21f3000003b60004 0x043e60000076c000

def z108 : W := mkw 0x01bbf000050c0003 0x00377e0000a18000 0xf5fffc000f8e0006 0x3ebfff8001f1c000

def z109 : W := mkw 0x417d23ea2af37734 0xa82fa47d455e6ee6 0xffff23fe3fffffff 0xffffe47fc7ffffff

def z110 : W := mkw 0x0011200000130000 0x8002240000026000 0xb8332000307f849f 0xf7066400060ff093

def z111 : W := mkw 0x03fbbbf7b2a06204 0x007f777ef6540c40 0xf3fffffff3b04305 0xfe7ffffffe760860

def z112 : W := mkw 0x0082800500000000 0x00105000a0000000 0x0003c007c0000001 0x20007800f8000000

def z113 : W := mkw 0x80000005400008c0 0x10000000a8000118 0x00000007c00000e1 0x00000000f800001c

def z114 : W := mkw 0xa16c0bb8dae07e8c 0x342d81771b5c0fd1 0xfffc03f9fff07f9f 0xdfff807f3ffe0ff3

def z115 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff00e40e7 0xff7ffffffe01c81c

def z116 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc23f83ff9ff9f 0xffff847f07ff3ff3

def z117 : W := mkw 0x00c2830501846041 0x00185060a0308c08 0x21c3020603864064 0x04386040c070c80c

def z118 : W := mkw 0x4011204220000130 0x0802240844000026 0xba3322c6300047f9 0xf7466458c60008ff

def z119 : W := mkw 0x0000081090000000 0x0000010212000000 0x400cdd39c0000000 0x08019ba738000000

def z120 : W := mkw 0xa0c6cf1ddc489c8a 0x3418d9e3bb891391 0xfdcfff3ffc49bc9b 0xffb9ffe7ff893793

def z121 : W := mkw 0x8000400044080882 0x1000080008810110 0x0c0000000c083882 0x0180000001810710

def z122 : W := mkw 0xa00444084dccfccb 0x3400888109b99f99 0x0c0000000fcffcfe 0x0180000001f9ff9f

def z123 : W := mkw 0x87fffff7ffffe8c7 0xd0fffffefffffd18 0xfffffffffffff8e7 0xffffffffffffff1c

def z124 : W := mkw 0x03bbb8f7b0000000 0x0077771ef6000000 0x823ffcfff0000001 0xb047ff9ffe000000

def z125 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x75cfdc000f8e0006 0x2eb9fb8001f1c000

def z126 : W := mkw 0x81eec3ad4fec7ec7 0x303dd875a9fd8fd8 0x45ccc139cf803800 0x08b9982739f00700

def z127 : W := mkw 0x01bbb00000130000 0x8037760000026000 0xf1fffc00007f8006 0x3e3fff80000ff000

def z128 : W := mkw 0x03ee9bbd9ae07604 0x207dd377b35c0ec0 0xfffcdff9cff07f06 0xdfff9bff39fe0fe0

def z129 : W := mkw 0x05bbf400051f8003 0xc0b77e8000a3f000 0xf1fffc00000f8000 0x3e3fff800001f000

def z130 : W := mkw 0x000400080ae07604 0x20008001015c0ec0 0x0c0000000ff07f06 0x0180000001fe0fe0

def z131 : W := mkw 0x012c00000a600004 0x00258000014c0000 0xf5fc00000ff00006 0x1ebf800001fe0000

def z132 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff0704707 0xff7ffffffe0e08e0

def z133 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x45cc01380f803800 0x08b9802701f00700

def z134 : W := mkw 0x012c00a80ae07604 0x20258015015c0ec0 0x8e3c00f80ff07f06 0x91c7801f01fe0fe0

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000200030000001 0xf200040006000000

def z136 : W := mkw 0x000000a800001600 0x20000015000002c0 0x020000f800000700 0x8040001f000000e0

def z137 : W := mkw 0x0004000808401400 0x2000800101080280 0xdc0c01380c403c02 0xdb81802701880780

def z138 : W := mkw 0x4000000000130130 0x8800000000026026 0x08000000007fc7fe 0x01000000000ff8ff

def z139 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xfdfffc000fffc7fe 0x3fbfff8001fff8ff

def z140 : W := mkw 0xa16c47a84ee8fe8e 0x342d88f509dd1fd1 0xfffc03f80ff9ff9e 0xdfff807f01ff3ff3

def z141 : W := mkw 0x00c2c305058c6043 0x00185860a0b18c08 0x75c3c2060f8e4066 0x2eb87840c1f1c80c

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0x2003020600064064 0x04006040c000c80c

def z143 : W := mkw 0xe0156c5afc5b9dba 0xbc02ad8b5f8b73b7 0xde3cfdf9fc79bf9b 0xfbc79fbf3f8f37f3

def z144 : W := mkw 0xa0004c10d408888a 0x140009821a811111 0x0000fc01f0098099 0x20001f803e013013

def z145 : W := mkw 0x4293b857b0130130 0x8852770af6026026 0xba33fec7f07fc7ff 0xf7467fd8fe0ff8ff

def z146 : W := mkw 0x47fffff7bf7f8137 0xc8fffffef7eff026 0xffffffffffffc7ff 0xfffffffffffff8ff

def z147 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0x45ccdc000fff8006 0x08b99b8001fff000

def z148 : W := mkw 0x00c28b1590000000 0x00185162b2000000 0xf1cfff3ff0000001 0xfe39ffe7fe000000

def z149 : W := mkw 0x03fbb3e720000000 0x007f767ce4000000 0xf3ff03fe00000000 0xde7fe07fc0000000

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0xba3002c000704706 0xd7460058000e08e0

def z151 : W := mkw 0x016803a002a06204 0x002d007400540c40 0xbbf002c003f04706 0xd77e0058007e08e0

def z152 : W := mkw 0x0040030000806000 0x0008006000100c00 0x7dc003000f807806 0x4fb8006001f00f00

def z153 : W := mkw 0x03fbbbf7b0806000 0x007f777ef6100c00 0xffffffffff807807 0xfffffffffff00f00

def z154 : W := mkw 0x01ee83ad0ae07604 0x203dd075a15c0ec0 0xffffc3ffcff07f07 0xfffff87ff9fe0fe0

def z155 : W := mkw 0x033938f2b0000000 0x0067271e56000000 0x823c3cf830000000 0x9047879f06000000

def z156 : W := mkw 0x4011204220130130 0x8802240844026026 0x0003000600060060 0x00006000c000c00c

def z157 : W := mkw 0x05eed7a80fecf607 0x60bddaf501fd9ec0 0xfffcdff80ff07f06 0xdfff9bff01fe0fe0

def z158 : W := mkw 0x4011204220130130 0x8802240844026026 0x8a3020c0307fc7fe 0x91460418060ff8ff

def z159 : W := mkw 0x417d23ea2af37734 0xa82fa47d455e6ee6 0xffff03fe0ff67f66 0xdfffe07fc1fecfec

def z160 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x65c3c307cf867864 0x0cb87860f9f0cf0c

def z161 : W := mkw 0x033938f2b0000000 0x0067271e56000000 0xd23cfdf9f0000001 0xfa479fbf3e000000

def z162 : W := mkw 0x85fff7054fffe8c7 0xd0bffee0a9fffd18 0xfdffff07cffff8e7 0x7fbfffe0f9ffff1c

def z163 : W := mkw 0x0000081090000000 0x0000010212000000 0xd80cfd39f049849b 0xfb019fa73e093093

def z164 : W := mkw 0x2004040808409408 0x2400808101081281 0x0000000000418418 0x0000000000083083

def z165 : W := mkw 0x80c2cb15d58c68c3 0x10185962bab18d18 0xfdcfff3fff8e78e7 0xffb9ffe7fff1cf1c

def z166 : W := mkw 0x00c2830501846041 0x00185060a0308c08 0x71c3c307c3864065 0x6e387860f870c80c

def z167 : W := mkw 0xc1ffe3ef6fff7ff7 0xb83ffc7dedffeffe 0xffffe3ffffffffff 0xfffffc7fffffffff

def z168 : W := mkw 0x0497f4000d5f8003 0xc092fe8001abf000 0xd40ffc000c4f8002 0x3a81ff800189f000

def z169 : W := mkw 0x0082c000050c0003 0x0010580000a18000 0x75c3c0000f8e0006 0x2eb8780001f1c000

def z170 : W := mkw 0xa000000840001c88 0x3400000108000391 0x0800000000003c98 0x0100000000000793

def z171 : W := mkw 0x01fbb3a000000000 0x003f767400000000 0xf3fffff800000000 0xfe7fffff00000000

def z172 : W := mkw 0x8082c005450c08c3 0x10105800a8a18118 0x5c03c107cc0e38e3 0x6b807820f981c71c

def z173 : W := mkw 0xa3fffffffc489c8a 0x347fffffff891391 0xfffffffffc49bc9b 0xffffffffff893793

def z174 : W := mkw 0x4011204220130130 0x8802240844026026 0x823020c030718718 0x90460418060e30e3

def z175 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfc0fff3ffc4ffcff 0xff81ffe7ff89ff9f

def z176 : W := mkw 0x00c2830500000000 0x00185060a0000000 0x71c3c307c0000001 0x6e387860f8000000

def z177 : W := mkw 0x03793bf7b0000000 0x006f277ef6000000 0x823c3ffff0000001 0xd04787fffe000000

def z178 : W := mkw 0x0293b857b0000000 0x0052770af6000000 0x0003fc07f0000001 0x20007f80fe000000

def z179 : W := mkw 0xe0156c5afc5b9dba 0xbc02ad8b5f8b73b7 0xfe3ffffffc7fffff 0xffc7ffffff8fffff

def z180 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0xf1fffc0003b60004 0x3e3fff800076c000

def z181 : W := mkw 0x00d3a34720000000 0x001a7468e4000000 0xf3f3e3c7f0000001 0xfe7e7c78fe000000

def z182 : W := mkw 0xa493fc10d51f888b 0xd4927f821aa3f111 0x0003fc01f00f8099 0x20007f803e01f013

def z183 : W := mkw 0x0411340000138000 0xc082268000027000 0x00003c0000018000 0x0000078000003000

def z184 : W := mkw 0x0082c000050c0003 0x0010580000a18000 0x7dc3c2060f8e40e7 0x6fb87840c1f1c81c

def z185 : W := mkw 0x05bff4a80f7f9607 0xe0b7fe9501eff2c0 0xf7fffcf80fff8706 0xbeffff9f01fff0e0

def z186 : W := mkw 0x040444000f6c8007 0x4080888001ed9000 0x040000000f800000 0x0080000001f00000

def z187 : W := mkw 0xa4044c18df7f9c8f 0xf48089831beff391 0xdc0cfd39ffffbc9f 0xfb819fa73ffff793

def z188 : W := mkw 0x4493f442251f8133 0xc8927e8844a3f026 0x0003fc06300f80f9 0x20007f80c601f01f

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000000080083 0x6300000000010010

def z190 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0xf5fffc000f800000 0x3ebfff8001f00000

def z191 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xd1ccfd39f0000001 0xfa399fa73e000000

def z192 : W := mkw 0x23ffbfffb8409408 0x247ff7fff7081281 0xf3fffffff0418419 0xfe7ffffffe083083

def z193 : W := mkw 0x053d34000a738004 0xc0a7a680014e7000 0xf5fc3c000ff18006 0x1ebf878001fe3000

def z194 : W := mkw 0x05aa900003240005 0x40b5520000648000 0x01c0000003800000 0x0038000000700000

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a0002c000004700 0xc1400058000008e0

def z196 : W := mkw 0x0000440004088002 0x0000088000811000 0x0000fc0000098000 0x20001f8000013000

def z197 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfff3c3c7cffe7fe7 0xfffe7878f9ffcffc

def z198 : W := mkw 0xe00444084c5b9dba 0xbc008881098b73b7 0x0c0000000c7ffffe 0x01800000018fffff

def z199 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xa3ff3efe30000000 0x947fe7dfc6000000

def z200 : W := mkw 0x80004000458c68c3 0x1000080008b18d18 0x0c0000000f8e78e6 0x0180000001f1cf1c

def z201 : W := mkw 0x4051234220936130 0x880a246844126c26 0xfff323c63fffffff 0xfffe6478c7ffffff

def z202 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffe060fffc0e7 0x7fbfffc0c1fff81c

def z203 : W := mkw 0x0400000003370005 0xc08000000066e000 0x0000000003b60004 0x000000000076c000

def z204 : W := mkw 0x037d3bfabae07604 0x206fa77f575c0ec0 0xfffc3ff83ff07f06 0xdfff87ff07fe0fe0

def z205 : W := mkw 0x453d34422a738134 0xc8a7a688454e7026 0x823c3cc030718718 0x90478798060e30e3

def z206 : W := mkw 0x80400305408068c0 0x10080060a8100d18 0x38030307c00e78e7 0x67006060f801cf1c

def z207 : W := mkw 0x0000081090000000 0x0000010212000000 0x00000139f0000001 0xc00000273e000000

def z208 : W := mkw 0xa0c6cf1dddccfccb 0x3418d9e3bbb99f99 0x45ccdd39cf803800 0x08b99ba739f00700

def z209 : W := mkw 0x40d3a34720130130 0x881a7468e4026026 0xfbf3e3c7f07fc7ff 0xff7e7c78fe0ff8ff

def z210 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x45c0c101cf803800 0x08b8182039f00700

def z211 : W := mkw 0x80404300458c68c3 0x1008086008b18d18 0x7dc003000f8e78e6 0x4fb8006001f1cf1c

def z212 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x0803c307c00e78e1 0x61007860f801cf1c

def z213 : W := mkw 0x4011204220130130 0x8802240844026026 0x823320c6307f87f9 0xb0466418c60ff0ff

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000000e40e6 0x010000000001c81c

def z215 : W := mkw 0xa40444084f7f9c8f 0xf480888109eff391 0x0c0000000fffbc9e 0x0180000001fff793

def z216 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfffffec00fffc706 0xffffffd801fff8e0

def z217 : W := mkw 0x01bbb00000000000 0x0037760000000000 0xf1fffc0000000000 0x3e3fff8000000000

def z218 : W := mkw 0xa0000818d0001c88 0x340001031a000391 0x00000139c0003800 0x0000002738000700

def z219 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xc5fcfc000ff18000 0x18bf9f8001fe3000

def z220 : W := mkw 0x01bbb04220000000 0x0037760844000000 0xf3fffec630000001 0xfe7fffd8c6000000

def z221 : W := mkw 0x017d23ea2ae07604 0x202fa47d455c0ec0 0xffff23fe3ff07f07 0xffffe47fc7fe0fe0

def z222 : W := mkw 0x4000004220000130 0x0800000844000026 0x9a0022c63049c7fb 0xf3400458c60938ff

def z223 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xc7fc01f80ff03f00 0x98ff803f01fe07e0

def z224 : W := mkw 0x04004400051f8003 0xc080088000a3f000 0x00000000000f8000 0x000000000001f000

def z225 : W := mkw 0x0004000808401400 0x2000800101080280 0x440c01380c003800 0x0881802701800700

def z226 : W := mkw 0x012800a002200204 0x0025001400440040 0x023000c000300300 0x0046001800060060

def z227 : W := mkw 0x0011204220000000 0x0002240844000000 0xba3322c63049849b 0xf7466458c6093093

def z228 : W := mkw 0x80400305408068c0 0x10080060a8100d18 0x7dc00307cf8078e7 0x4fb80060f9f00f1c

def z229 : W := mkw 0x417923e222b36334 0x882f247c44566c66 0x23f302c603b64364 0x047e6058c076c86c

def z230 : W := mkw 0xa0004c10d408888a 0x140009821a811111 0x5c00fd01fc09b89b 0x6b801fa03f813713

def z231 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xd40cfd39cc49b802 0x3a819fa739893700

def z232 : W := mkw 0x01ee83ad0be47645 0x203dd075a17c8ec8 0xffff03fe0ff67f66 0xdfffe07fc1fecfec

def z233 : W := mkw 0x016803a002a06204 0x002d007400540c40 0x23f002c003b04304 0x047e005800760860

def z234 : W := mkw 0x016c03000ae06004 0x002d8060015c0c00 0xfdfc03000ff07806 0x5fbf806001fe0f00

def z235 : W := mkw 0x00112852b0000000 0x0002250a56000000 0xf23ffffff0000001 0xfe47fffffe000000

def z236 : W := mkw 0xa0400bb8d0807e88 0x340801771a100fd1 0x0a0003f9f0007f99 0xc140007f3e000ff3

def z237 : W := mkw 0x000444000c488002 0x0000888001891000 0x440cdc000c000000 0x08819b8001800000

def z238 : W := mkw 0xc0512347609369f0 0x980a2468ec126d3e 0xba3323c7f07fffff 0xf7466478fe0fffff

def z239 : W := mkw 0x0040030000000000 0x0008006000000000 0x71c0030000000000 0x4e38006000000000

def z240 : W := mkw 0x80c28305408068c0 0x10185060a8100d18 0x79c3c307c00078e1 0x6f387860f8000f1c

def z241 : W := mkw 0xa0044c18dee8fe8e 0x340089831bdd1fd1 0xdc0cfd39fff9ff9f 0xfb819fa73fff3ff3

def z242 : W := mkw 0xa497fc18dd5f9c8b 0xf492ff831babf391 0xdc0ffd39fc4fbc9b 0xfb81ffa73f89f793

def z243 : W := mkw 0x0011200000130000 0x8002240000026000 0xb0332000007f8006 0x36066400000ff000

def z244 : W := mkw 0xa0000818d0001c88 0x340001031a000391 0x98002139f049bc9b 0xf30004273e093793

def z245 : W := mkw 0xa1eecfbddfecfecf 0x343dd9f7bbfd9fd9 0xffffffffffffffff 0xffffffffffffffff

def z246 : W := mkw 0x0082800501040041 0x00105000a0208008 0x0003000600060060 0x00006000c000c00c

def z247 : W := mkw 0x00c2830500000000 0x00185060a0000000 0x79c3c307c00e40e7 0x6f387860f801c81c

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000c101c0000001 0x6a00182038000000

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00c013800000000 0xda01802700000000

def z250 : W := mkw 0xa086cc18dd4c9c8b 0x3410d9831ba99391 0xfdcffd39ffcfbc9f 0xffb9ffa73ff9f793

def z251 : W := mkw 0x0011204220000000 0x0002240844000000 0xb23322c630000001 0xf6466458c6000000

def z252 : W := mkw 0x00c2830500000000 0x00185060a0000000 0x41c0c101c0000000 0x0838182038000000

def z253 : W := mkw 0x413d20422a730134 0x8827a408454e6026 0xffff22c63fffc7ff 0xffffe458c7fff8ff

def z254 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff0364365 0xfe7ffffffe06c86c

def z255 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x440cfd39fc09b899 0x28819fa73f813713

def z256 : W := mkw 0x03fbb3e721846041 0x007f767ce4308c08 0x23f302c603864064 0x047e6058c070c80c

def z257 : W := mkw 0x03bbb857b0000000 0x0077770af6000000 0xf1fffc07f0000001 0x3e3fff80fe000000

def z258 : W := mkw 0x440444000f7f8137 0xc880888001eff026 0x0c0000000fffc7fe 0x0180000001fff8ff

def z259 : W := mkw 0x8000400044080882 0x1000080008810110 0xdc00e101fc49bc9b 0xfb801c203f893793

def z260 : W := mkw 0x004003a000000000 0x0008007400000000 0x020003f800000000 0xc040007f00000000

def z261 : W := mkw 0x0004000808401400 0x2000800101080280 0xfe3c03f80c707f06 0xdfc7807f018e0fe0

def z262 : W := mkw 0x07bffc57bf7f8007 0xc0f7ff8af7eff000 0xf5fffc07ffff8007 0x3ebfff80fffff000

def z263 : W := mkw 0x4011204220130130 0x8802240844026026 0xb0332006307f80ff 0x36066400c60ff01f

def z264 : W := mkw 0x0011204220000000 0x0002240844000000 0x823020c030000000 0x9046041806000000

def z265 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xc3fcfdf9f0000000 0x987f9fbf3e000000

def z266 : W := mkw 0x02000857b0000000 0x0040010af6000000 0x00000007f0000001 0x00000000fe000000

def z267 : W := mkw 0x00044c109c488002 0x0000898213891000 0xd40cfd39fc498003 0xfa819fa73f893000

def z268 : W := mkw 0x4000000000130130 0x8800000000026026 0x0000000000364364 0x000000000006c86c

def z269 : W := mkw 0x233d3cfab8409408 0x2467a79f57081281 0x823c3cf830418418 0x9047879f06083083

def z270 : W := mkw 0x0044030808c07400 0x2008806101180e80 0xfdcc03380fc07c06 0xdfb9806701f80f80

def z271 : W := mkw 0x032818b090000000 0x0065031612000000 0x000c1c3800000000 0x0001838700000000

def z272 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x5dc0c101cf883883 0x6bb8182039f10710

def z273 : W := mkw 0x05bfb0000b770005 0xc0b7f600016ee000 0xf5ff00000ff60006 0x1ebfe00001fec000

def z274 : W := mkw 0x4000000000130130 0x8800000000026026 0x98002000307fc7ff 0xf3000400060ff8ff

def z275 : W := mkw 0x4011204220130130 0x8802240844026026 0xb23320c0307f871e 0xb6466418060ff0e3

def z276 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xd5ccfc000fc98002 0x3ab99f8001f93000

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0xba3302c6007e47e7 0xf7466058c00fc8fc

def z278 : W := mkw 0x01ffb3a80ae07604 0x203ff675015c0ec0 0xfffffff80ff07f06 0xffffffff01fe0fe0

def z279 : W := mkw 0x433938f2b0130130 0x8867271e56026026 0xba3f3efe307fc7ff 0xf747e7dfc60ff8ff

def z280 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffcc03fff871e 0xbeffff9807fff0e3

def z281 : W := mkw 0x02512bf7b0000000 0x004a257ef6000000 0xb23323fff0000001 0xf646647ffe000000

def z282 : W := mkw 0x01680bb090000000 0x002d017612000000 0xf3fcfff9f0000001 0xfe7f9fff3e000000

def z283 : W := mkw 0x02400bffb0807600 0x2048017ff6100ec0 0x0a0003fff0007f01 0xc140007ffe000fe0

def z284 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xf5fcdc000ff00006 0x1ebf9b8001fe0000

def z285 : W := mkw 0x040444000f7f8007 0xc080888001eff000 0xd40cfc000fff8006 0x3a819f8001fff000

def z286 : W := mkw 0x4011204220130130 0x8802240844026026 0xb23322c630364365 0xf6466458c606c86c

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0xb030000000700006 0x16060000000e0000

def z288 : W := mkw 0x000400080ae07604 0x20008001015c0ec0 0xbe3002c00ff07f06 0xd7c6005801fe0fe0

def z289 : W := mkw 0x053d74000f7f8007 0xc0a7ae8001eff000 0x843c3c000fff8006 0x1087878001fff000

def z290 : W := mkw 0x8493f405451f88c3 0xd0927e80a8a3f118 0x0003fc07c00f80e1 0x20007f80f801f01c

def z291 : W := mkw 0xa0444f1ddcc8fcca 0x340889e3bb991f99 0xdc0cff3ffc49fcfb 0xfb819fe7ff893f9f

def z292 : W := mkw 0xa0400b1dd0807cc8 0x34080163ba100f99 0x0800033ff0007cf9 0xc1000067fe000f9f

def z293 : W := mkw 0x03ee9bbd9ae07604 0x207dd377b35c0ec0 0x45ccdd39cf803800 0x08b99ba739f00700

def z294 : W := mkw 0x84d3f705459fe8c3 0xd09a7ee0a8b3fd18 0x7dc3ff07cf8ff8e7 0x6fb87fe0f9f1ff1c

def z295 : W := mkw 0x43fbb3e720130130 0x887f767ce4026026 0x23f302c600364364 0x047e6058c006c86c

def z296 : W := mkw 0x000400000a600004 0x00008000014c0000 0x040000000ff00006 0x0080000001fe0000

def z297 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff00f80f9 0xfe7ffffffe01f01f

def z298 : W := mkw 0x4000004220130130 0x8800000844026026 0x0a0002c6307fc7ff 0xc1400058c60ff8ff

def z299 : W := mkw 0x053d34a80a739604 0xe0a7a695014e72c0 0x823c3cf800718700 0x9047879f000e30e0

def z300 : W := mkw 0xa0000810d0000888 0x140001021a000111 0x00000001f0000099 0x000000003e000013

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000049849a 0x0100000000093093

def z302 : W := mkw 0x8000400044080882 0x1000080008810110 0x0000c001c0080081 0x2000180038010010

def z303 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xf5fc01380ff03806 0x1ebf802701fe0700

def z304 : W := mkw 0x0082800000000000 0x0010500000000000 0x71c3c00000000000 0x2e38780000000000

def z305 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x65ffdc000fb60004 0x0cbffb8001f6c000

def z306 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff0718719 0xfe7ffffffe0e30e3

def z307 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffec60fffc366 0x3effffd8c1fff86c

def z308 : W := mkw 0x0000000002a06204 0x0000000000540c40 0x0000000003b04304 0x0000000000760860

def z309 : W := mkw 0x80000000408068c0 0x1000000008100d18 0x08000000000078e0 0x0100000000000f1c

def z310 : W := mkw 0xc0400347608069f0 0x18080068ec100d3e 0x0a0003c7f0007ff9 0xc1400078fe000fff

def z311 : W := mkw 0xa0004818d4081c8a 0x340009031a810391 0x5c00c139fc083c9b 0xeb8018273f810793

def z312 : W := mkw 0x040444080ffff607 0xe080888101fffec0 0x0c0000000fffff06 0x0180000001ffffe0

def z313 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffc003fff849f 0xffbfff8007fff093

def z314 : W := mkw 0x8082c005450c08c3 0x10105800a8a18118 0x75c3c007cf8e00e7 0x2eb87800f9f1c01c

def z315 : W := mkw 0xa0004c10d408888a 0x140009821a811111 0x0000dc01c0000000 0x00001b8038000000

def z316 : W := mkw 0x03ffbbffba601604 0x207ff77ff74c02c0 0xf3fffffff0700701 0xfe7ffffffe0e00e0

def z317 : W := mkw 0x0004000008400000 0x0000800001080000 0xd40c00000c400002 0x1a81800001880000

def z318 : W := mkw 0xa0444fb8dcc8fe8a 0x340889f71b991fd1 0xde0cfff9fc49ff9b 0xfbc19fff3f893ff3

def z319 : W := mkw 0x0128000002200004 0x0025000000440000 0x21f0000003b00004 0x043e000000760000

def z320 : W := mkw 0x413d20ea2a731734 0xa827a41d454e62e6 0x823c20f830718718 0x9047841f060e30e3

def z321 : W := mkw 0x0011200000000000 0x0002240000000000 0xb033200000000000 0x3606640000000000

def z322 : W := mkw 0xe015644a6c5b9dba 0xbc02ac894d8b73b7 0xbe3322c63c7fffff 0xf7c66458c78fffff

def z323 : W := mkw 0x80404305458c68c3 0x10080860a8b18d18 0x0c000307cf8e78e7 0x41800060f9f1cf1c

def z324 : W := mkw 0x0282981590000000 0x00505302b2000000 0x0000dc01c0000000 0x00001b8038000000

def z325 : W := mkw 0x0004000808401400 0x2000800101080280 0x0c0000000c403c02 0x0180000001880780

def z326 : W := mkw 0x07fffff7bf6c8007 0x40fffffef7ed9000 0xf7ffffffff800001 0xfefffffffff00000

def z327 : W := mkw 0x012c00a80a601604 0x20258015014c02c0 0xf7fc00f80ff00706 0x9eff801f01fe00e0

def z328 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xffff03fe0ffe7fe7 0xffffe07fc1ffcffc

def z329 : W := mkw 0x0293b857b0000000 0x0052770af6000000 0xd00ffd3ff0000001 0xfa01ffa7fe000000

def z330 : W := mkw 0x4000004220000130 0x0800000844000026 0x020002c600004360 0x00400058c000086c

def z331 : W := mkw 0xc0d3e347659f69f3 0x981a7c68ecb3ed3e 0x7ff3c3c7cfbe7be7 0x6ffe7878f9f7cf7c

def z332 : W := mkw 0x0693fc57b51f8003 0xc0d27f8af6a3f000 0x0003fc07f00f8001 0x20007f80fe01f000

def z333 : W := mkw 0x81eec3ad4fec7ec7 0x303dd875a9fd8fd8 0xfffcc3f9cff07f06 0xdfff987f39fe0fe0

def z334 : W := mkw 0xa0004c18d4089c8a 0x340009831a811391 0x0800fd39f009bc99 0xe1001fa73e013793

def z335 : W := mkw 0x0000081090000000 0x0000010212000000 0x0000fc01f0000001 0x20001f803e000000

def z336 : W := mkw 0x057d37a80af3f604 0xe0afa6f5015e7ec0 0xfffc3ff80ff1ff06 0xdfff87ff01fe3fe0

def z337 : W := mkw 0x84c6c7054fffe8c7 0xd098d8e0a9fffd18 0x7dc3c307cffff8e7 0x6fb87860f9ffff1c

def z338 : W := mkw 0x80d3e305459f68c3 0x901a7c60a8b3ed18 0xfdf3e307cffff8e7 0x7fbe7c60f9ffff1c

def z339 : W := mkw 0xa0004c10d408888a 0x140009821a811111 0x9800fc01f049849b 0xf3001f803e093093

def z340 : W := mkw 0x0040030500806040 0x00080060a0100c08 0x0000020600004060 0x00000040c000080c

def z341 : W := mkw 0x01bbb81090000000 0x0037770212000000 0xf1fffd39f0000001 0xfe3fffa73e000000

def z342 : W := mkw 0x0128000000000000 0x0025000000000000 0xf1fc000000000000 0x1e3f800000000000

def z343 : W := mkw 0x012c00000a600004 0x00258000014c0000 0x45cc00000f800000 0x08b9800001f00000

def z344 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x45c3c107cf8e38e1 0x28b87820f9f1c71c

def z345 : W := mkw 0x800440084c481c82 0x3000880109890390 0xdc0cc139cc483c83 0xfb81982739890790

def z346 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x75c3c307cf803801 0x6eb87860f9f00700

def z347 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x4dc0c307cf8078e1 0x49b81860f9f00f1c

def z348 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x67fc03f80fb07b04 0x0cff807f01f60f60

def z349 : W := mkw 0x20044c189c48940a 0x2400898313891281 0xd40cfc383c49841a 0xba819f8707893083

def z350 : W := mkw 0x012800a000000000 0x0025001400000000 0x823c00f800000000 0x9047801f00000000

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x00030006000e00e1 0x20006000c001c01c

def z352 : W := mkw 0x01fbb30500000000 0x003f7660a0000000 0xf1ffff07c0000001 0x7e3fffe0f8000000

def z353 : W := mkw 0x2000081890001408 0x2400010312000281 0x0000003830000418 0x8000000706000083

def z354 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x21c3c207c38e40e5 0x24387840f871c81c

def z355 : W := mkw 0xa3fffffffc489c8a 0x347fffffff891391 0xf7fffffffc003801 0xfeffffffff800700

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x30030000000e0006 0x260060000001c000

def z357 : W := mkw 0xe0d7ef5ffddffdfb 0xbc1afdebffbbffbf 0xffffffffffffffff 0xffffffffffffffff

def z358 : W := mkw 0xc093e047651f09f3 0x98127c08eca3e13e 0xba33e2c7f07fc7ff 0xf7467c58fe0ff8ff

def z359 : W := mkw 0x83fbf3e7658c68c3 0x107f7e7cecb18d18 0x7ff3c3c7cf8e78e7 0x6ffe7878f9f1cf1c

def z360 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xa3fc02f803f04704 0x947f805f007e08e0

def z361 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfe3cfff9fc79ff9f 0xffc79fff3f8f3ff3

def z362 : W := mkw 0x056c47a80ffff607 0xe0ad88f501fffec0 0xfffc03f80fffff06 0xdfff807f01ffffe0

def z363 : W := mkw 0x012c00000a600004 0x00258000014c0000 0xfffc02c00ff04706 0xdfff805801fe08e0

def z364 : W := mkw 0x012c44000e688006 0x0025888001cd1000 0xf5fcfc000ff98006 0x3ebf9f8001ff3000

def z365 : W := mkw 0x40d3a34721976171 0x881a7468e432ec2e 0x23f302c603b64364 0x047e6058c076c86c

def z366 : W := mkw 0xe0156c5afc5b9dba 0xbc02ad8b5f8b73b7 0xdc0ffd3ffc4fbcfb 0xfb81ffa7ff89f79f

def z367 : W := mkw 0x85fbf30547bf68c7 0xd0bf7e60a8f7ed18 0x7df3c307cfbe78e7 0x6fbe7860f9f7cf1c

def z368 : W := mkw 0x05bff4080ffff607 0xe0b7fe8101fffec0 0xfdfffc000fffff06 0x3fbfff8001ffffe0

def z369 : W := mkw 0x01aec0000f6c0007 0x0035d80001ed8000 0xf5ffc0000ffe0006 0x3ebff80001ffc000

def z370 : W := mkw 0x0011204220000000 0x0002240844000000 0x0003200630000001 0x20006400c6000000

def z371 : W := mkw 0xa0c6cf1dddccfccb 0x3418d9e3bbb99f99 0x7dcfdf3fcf8e78e7 0x6fb9fbe7f9f1cf1c

def z372 : W := mkw 0x02113852b0000000 0x0042270a56000000 0x00003c0030000000 0x0000078006000000

def z373 : W := mkw 0x80400305408068c0 0x10080060a8100d18 0x00000101c0003800 0x0000002038000700

def z374 : W := mkw 0x001564000c5b8002 0x8002ac80018b7000 0xf43ffc000c7f8006 0x3e87ff80018ff000

def z375 : W := mkw 0xa3fbbbfff0001c88 0x347f777ffe000391 0xfbfffffff0003c99 0xff7ffffffe000793

def z376 : W := mkw 0x81eec3ad4fec7ec7 0x303dd875a9fd8fd8 0x7dcfc33fcf8e78e7 0x6fb9f867f9f1cf1c

def z377 : W := mkw 0x80c2c3ad458c7ec3 0x30185875a8b18fd8 0x7fc3c3ffcf8e7fe7 0xeff8787ff9f1cffc

def z378 : W := mkw 0x8000400044080882 0x1000080008810110 0x7c03c307cc0e78e7 0x6f807860f981cf1c

def z379 : W := mkw 0xa0044c18ddccfccb 0x340089831bb99f99 0xdc0cfd39ffcffcff 0xfb819fa73ff9ff9f

def z380 : W := mkw 0xa16c4fb8dee8fe8e 0x342d89f71bdd1fd1 0xfffcdff9cff07f06 0xdfff9bff39fe0fe0

def z381 : W := mkw 0x81eac3a547ac6ac7 0x103d5874a8f58d58 0x7ff3c3c7cfbe7be7 0x6ffe7878f9f7cf7c

def z382 : W := mkw 0x804003ad40807ec0 0x30080075a8100fd8 0x0a0003ffc0007fe1 0xc140007ff8000ffc

def z383 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x41cffd3ff0000001 0x2839ffa7fe000000

def z384 : W := mkw 0x004003a800807600 0x2008007500100ec0 0x0000013800003800 0x0000002700000700

def z385 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x803ffc00007f8000 0x3007ff80000ff000

def z386 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x800cfc39f0498499 0xb0019f873e093093

def z387 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xc40cfd39fc41bc18 0x98819fa73f883783

def z388 : W := mkw 0xa7ffffffff7f9c8f 0xf4ffffffffeff391 0xffffffffffffbc9f 0xfffffffffffff793

def z389 : W := mkw 0x00c2830500806000 0x00185060a0100c00 0x7dc3c307cf807807 0x6fb87860f9f00f00

def z390 : W := mkw 0x052c44000f7f8007 0xc0a5888001eff000 0xf5fc00000fff8006 0x1ebf800001fff000

def z391 : W := mkw 0x05bbf400073f8007 0xc0b77e8000e7f000 0x21f3fc0003bf8004 0x243e7f800077f000

def z392 : W := mkw 0x03ea93a500000000 0x007d5274a0000000 0x01c0000000000000 0x0038000000000000

def z393 : W := mkw 0x0011204220000000 0x0002240844000000 0xba3322c630704707 0xf7466458c60e08e0

def z394 : W := mkw 0x07eedfb59f6c8007 0x40fddbf6b3ed9000 0x45ccdd39cf800000 0x08b99ba739f00000

def z395 : W := mkw 0xa0044c10dc48888a 0x140089821b891111 0xd40cfc01fc49809b 0x3a819f803f893013

def z396 : W := mkw 0x0082c000050c0003 0x0010580000a18000 0x45c0c0000f800000 0x08b8180001f00000

def z397 : W := mkw 0x85bff4004f7f8887 0xd0b7fe8009eff110 0xfdfffd01cfffb887 0x7fbfffa039fff710

def z398 : W := mkw 0x0011204220000000 0x0002240844000000 0x223302c600000000 0x04466058c0000000

def z399 : W := mkw 0x004003a800807600 0x2008007500100ec0 0x7fc003f80f807f06 0xcff8007f01f00fe0

def z400 : W := mkw 0x8082c005450c08c3 0x10105800a8a18118 0x0000c001c0000000 0x0000180038000000

def z401 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x2ff002c00ff07f06 0x05fe005801fe0fe0

def z402 : W := mkw 0x016c03a00a600004 0x002d8074014c0000 0xf7fc03f80ff00006 0xdeff807f01fe0000

def z403 : W := mkw 0xe0116c52f41b89ba 0x9c022d8a5e837137 0x0003fc07f00f80f9 0x20007f80fe01f01f

def z404 : W := mkw 0x441564422f7f8137 0xc882ac8845eff026 0xbe3322c63fffc7ff 0xf7c66458c7fff8ff

def z405 : W := mkw 0x800444004c488882 0x1000888009891110 0xdc0cfd01cc49b883 0x7b819fa039893710

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000030000499 0xc100000006000093

def z407 : W := mkw 0x0493f400051f8003 0xc0927e8000a3f000 0x75c3fc000f8f8006 0x2eb87f8001f1f000

def z408 : W := mkw 0x0004081898401400 0x2000810313080280 0xdc0cfd39fc403c03 0xfb819fa73f880780

def z409 : W := mkw 0x0011200000130000 0x8002240000026000 0x2033000000360004 0x040660000006c000

def z410 : W := mkw 0x85eed7054fece8c7 0x50bddae0a9fd9d18 0x45ccdd01cf803800 0x08b99ba039f00700

def z411 : W := mkw 0x8000000040000880 0x1000000008000110 0x08000101c0003881 0x4100002038000710

def z412 : W := mkw 0x41bbb04220130130 0x8837760844026026 0xfbfffec6307fc7ff 0xff7fffd8c60ff8ff

def z413 : W := mkw 0x016803a002a06204 0x002d007400540c40 0xf3fc03f803b04304 0xde7f807f00760860

def z414 : W := mkw 0x01aa900000000000 0x0035520000000000 0x41ccdc0000000000 0x08399b8000000000

def z415 : W := mkw 0x004003a800807600 0x2008007500100ec0 0xba3003f800707f06 0xd746007f000e0fe0

def z416 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x0c000139fc49bc9b 0xc18000273f893793

def z417 : W := mkw 0x212c0cb89a60960c 0x24258197134c12c1 0x823c3cf830718718 0x9047879f060e30e3

def z418 : W := mkw 0x4293b857b0130130 0x8852770af6026026 0x0003fc07f00f80f9 0x20007f80fe01f01f

def z419 : W := mkw 0x0082c000050c0003 0x0010580000a18000 0x0003c000000e0000 0x200078000001c000

def z420 : W := mkw 0x03fbfbf7b50c0003 0x007f7f7ef6a18000 0xf7ffffffff8e0007 0xfefffffffff1c000

def z421 : W := mkw 0x417923e220130130 0x882f247c44026026 0xfbff23fe307fc7ff 0xff7fe47fc60ff8ff

def z422 : W := mkw 0x012c00a80a601604 0x20258015014c02c0 0x000c003800000000 0x0001800700000000

def z423 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0x43ccdffff0000001 0xc8799bfffe000000

def z424 : W := mkw 0x016803a000000000 0x002d007400000000 0x41cc013800000000 0x0839802700000000

def z425 : W := mkw 0xc5fff7476fffe9f7 0xd8bffee8edfffd3e 0xffffffc7ffffffff 0xfffffff8ffffffff

def z426 : W := mkw 0x05bff4080f7f9407 0xe0b7fe8101eff280 0xfdfffd380fffbc06 0xffbfffa701fff780

def z427 : W := mkw 0x83fffbffffec7ec7 0x307fff7ffffd8fd8 0xfffffffffffe7fe7 0xffffffffffffcffc

def z428 : W := mkw 0xa3fffffffee8fe8e 0x347fffffffdd1fd1 0xfffffffffff9ff9f 0xffffffffffff3ff3

def z429 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x9c0020003c49bc9b 0xf380040007893793

def z430 : W := mkw 0xe3fffffffc5b9dba 0xbc7fffffff8b73b7 0xfffffffffc7fffff 0xffffffffff8fffff

def z431 : W := mkw 0x4011204220130130 0x8802240844026026 0x2a3302c6007fc7fe 0x05466058c00ff8ff

def z432 : W := mkw 0x052c14000a608004 0x40a58280014c1000 0x000c1c0000000000 0x0001838000000000

def z433 : W := mkw 0x8082c005458c68c3 0x10105800a8b18d18 0x0c03c007cf8e78e7 0x21807800f9f1cf1c

def z434 : W := mkw 0xe011285af0131db8 0xbc02250b5e0263b7 0xba3323fff07fffff 0xf746647ffe0fffff

def z435 : W := mkw 0x81eac3a5458c68c3 0x103d5874a8b18d18 0xffffc3ffcf8e78e7 0xfffff87ff9f1cf1c

def z436 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000200030098099 0x2000040006013013

def z437 : W := mkw 0xa0c6cf1dddccfccb 0x3418d9e3bbb99f99 0xddccfd39ffc9bc9b 0xfbb99fa73ff93793

def z438 : W := mkw 0xa5bff4084f7f9c8f 0xf4b7fe8109eff391 0xfdfffc000fffbc9e 0x3fbfff8001fff793

def z439 : W := mkw 0x83fbbbf7f08068c0 0x107f777efe100d18 0xfbfffffff00078e1 0xff7ffffffe000f1c

def z440 : W := mkw 0x8082c000458c68c3 0x1010580008b18d18 0x7dc3c0000f8e78e6 0x2fb8780001f1cf1c

def z441 : W := mkw 0x012c00a80a601604 0x20258015014c02c0 0xba3c02f800704706 0xd747805f000e08e0

def z442 : W := mkw 0x05bfb4000a738004 0xc0b7f680014e7000 0xf1fffc0000718000 0x3e3fff80000e3000

def z443 : W := mkw 0x000444080c489402 0x2000888101891280 0xdc0cfd380c49bc02 0xfb819fa701893780

def z444 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x4dcc01380ff07f06 0x09b9802701fe0fe0

def z445 : W := mkw 0x60152c5ab8539538 0xac02a58b570a72a7 0xba3f3efe307fc7ff 0xf747e7dfc60ff8ff

def z446 : W := mkw 0x05fff7000fffe007 0xc0bffee001fffc00 0xfdffff000ffff806 0x7fbfffe001ffff00

def z447 : W := mkw 0x000444000c488002 0x0000888001891000 0xdc0cfc003c49849b 0xfb819f8007893093

def z448 : W := mkw 0x4011204220130130 0x8802240844026026 0x8a3022c63071c7f9 0xd1460458c60e38ff

def z449 : W := mkw 0x0000000000806000 0x0000000000100c00 0x0c0000000f807806 0x0180000001f00f00

def z450 : W := mkw 0x0000400004080002 0x0000080000810000 0x5400c0000c080002 0x2a80180001810000

def z451 : W := mkw 0xa53d7c18de7b9c8e 0xf4a7af831bcf7391 0xdc3cfd39fc79bc9b 0xfb879fa73f8f3793

def z452 : W := mkw 0x8040430044886882 0x1008086008910d10 0x7dc0c301cf887887 0x6fb8186039f10f10

def z453 : W := mkw 0x80c28305418468c1 0x10185060a8308d18 0x29c30307c38678e5 0x45386060f870cf1c

def z454 : W := mkw 0x000400080ae07604 0x20008001015c0ec0 0x040000000f803800 0x0080000001f00700

def z455 : W := mkw 0x016803a002a06204 0x002d007400540c40 0x7ff003c00fb07b06 0x4ffe007801f60f60

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x823000c000700700 0x90460018000e00e0

def z457 : W := mkw 0xa12c4c18de689c8e 0x342589831bcd1391 0xfdfcfd39fff9bc9f 0xffbf9fa73fff3793

def z458 : W := mkw 0x253d3c189a73940c 0xe4a7a783134e7281 0x803c3c3830718418 0x90078787060e3083

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0xba3022c03079c79f 0xf7460458060f38f3

def z460 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xfbfffffff00047f9 0xff7ffffffe0008ff

def z461 : W := mkw 0x05fff7a00f7f8007 0xc0bffef401eff000 0xf7fffff80fff8006 0xfeffffff01fff000

def z462 : W := mkw 0x004003a000806200 0x0008007400100c40 0x020002c000004300 0x0040005800000860

def z463 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xf7fffec63fff8007 0xfeffffd8c7fff000

def z464 : W := mkw 0x012c00a80a601604 0x20258015014c02c0 0xde3c01f80c703f02 0xdbc7803f018e07e0

def z465 : W := mkw 0xa33d7cfafc489c8a 0x3467af9f5f891391 0xde3cfdf9fc49bc9b 0xfbc79fbf3f893793

def z466 : W := mkw 0xc0116042659f69f3 0x98022c084cb3ed3e 0xbe3322c63fffffff 0xf7c66458c7ffffff

def z467 : W := mkw 0x417d23ea2af37734 0xa82fa47d455e6ee6 0xfffc23f83ff1ff1e 0xdfff847f07fe3fe3

def z468 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc0c301cf807806 0x4fb8186039f00f00

def z469 : W := mkw 0x417923e222b36334 0x882f247c44566c66 0xbbf322c633ffc7ff 0xf77e6458c67ff8ff

def z470 : W := mkw 0x00c2830501846041 0x00185060a0308c08 0x7dc303060f867866 0x4fb86060c1f0cf0c

def z471 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xd40cfd39fc003801 0xfa819fa73f800700

def z472 : W := mkw 0xc3fbfbf7f59f69f3 0x987f7f7efeb3ed3e 0xffffffffffffffff 0xffffffffffffffff

def z473 : W := mkw 0x0040030000806000 0x0008006000100c00 0x7dc303060f8e78e7 0x6fb86060c1f1cf1c

def z474 : W := mkw 0x0011200000130000 0x8002240000026000 0xb8332206007fc0e7 0x77066440c00ff81c

def z475 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xddcc01380fc03c02 0xdbb9802701f80780

def z476 : W := mkw 0x07fbbbf7b3370005 0xc0ff777ef666e000 0xf3fffffff3b60005 0xfe7ffffffe76c000

def z477 : W := mkw 0x0139300000000000 0x0027260000000000 0x803c3c0000000000 0x1007878000000000

def z478 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xf3fcdff9c0000000 0xde7f9bff38000000

def z479 : W := mkw 0x05bffc109f7f8007 0xc0b7ff8213eff000 0xf5fffd39ffff8007 0xfebfffa73ffff000

def z480 : W := mkw 0xe000085af0001db8 0x3c00010b5e0003b7 0x0a0003fff0007ff9 0xc140007ffe000fff

def z481 : W := mkw 0x0000000800001400 0x2000000100000280 0x0800013800003c00 0xc100002700000780

def z482 : W := mkw 0x4015204a28531530 0xa802a409450a62a6 0xfe3f23fe3c7fffff 0xffc7e47fc78fffff

def z483 : W := mkw 0x4000004220000130 0x0800000844000026 0xba3002c6307047ff 0xd7460058c60e08ff

def z484 : W := mkw 0x0293b04720000000 0x00527608e4000000 0x0003000600000000 0x00006000c0000000

def z485 : W := mkw 0x4011204220130130 0x8802240844026026 0xba3022c03071c71e 0xd7460458060e38e3

def z486 : W := mkw 0x073d3cf2ba738004 0xc0e7a79e574e7000 0x823c3cf830718000 0x9047879f060e3000

def z487 : W := mkw 0xa0c6c70d4dccfccb 0x3418d8e1a9b99f99 0x7dc3c307cfcffcff 0x6fb87860f9f9ff9f

def z488 : W := mkw 0xa1bffc18dc489c8a 0x3437ff831b891391 0xfdfffd39fc49bc9b 0xffbfffa73f893793

def z489 : W := mkw 0x85bff4004fffe8c7 0xd0b7fe8009fffd18 0xfdfffc000ffff8e6 0x3fbfff8001ffff1c

def z490 : W := mkw 0x83eadbb5d58c68c3 0x107d5b76bab18d18 0x45ccdd39cf803800 0x08b99ba739f00700

def z491 : W := mkw 0x840444004fffe8c7 0xd080888009fffd18 0x0c0000000ffff8e6 0x0180000001ffff1c

def z492 : W := mkw 0x033938f2b0000000 0x0067271e56000000 0xb23f3efe30000001 0xf647e7dfc6000000

def z493 : W := mkw 0x01bbb00000000000 0x0037760000000000 0x21f3000000000000 0x043e600000000000

def z494 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x8a3c03f800707f00 0xd147807f000e0fe0

def z495 : W := mkw 0x03fbbbf7b1846041 0x007f777ef6308c08 0xf3fffffff3864065 0xfe7ffffffe70c80c

def z496 : W := mkw 0x05fff7a80ffff607 0xe0bffef501fffec0 0xf5fffd380fffb806 0x3ebfffa701fff700

def z497 : W := mkw 0x040404000a738004 0xc0808080014e7000 0x0000000000718000 0x00000000000e3000

def z498 : W := mkw 0xe0044c18dc5b9dba 0xbc0089831b8b73b7 0xdc0cfd39fc7fffff 0xfb819fa73f8fffff

def z499 : W := mkw 0x0093e000051f0003 0x80127c0000a3e000 0xf5f3e0000fff8006 0x3ebe7c0001fff000

def z500 : W := mkw 0x4011200000130130 0x8802240000026026 0xb8332000007fc7fe 0x37066400000ff8ff

def z501 : W := mkw 0x07ffffb59f7f8007 0xc0fffff6b3eff000 0xf5fffd39cfff8006 0x3ebfffa739fff000

def z502 : W := mkw 0xc093e047651f09f3 0x98127c08eca3e13e 0x0003e007f00f80f9 0x20007c00fe01f01f

def z503 : W := mkw 0xa16c4fb8dc489c8a 0x342d89f71b891391 0xfffcfff9fc49bc9b 0xffff9fff3f893793

def z504 : W := mkw 0x80d3e347658c68c3 0x101a7c68ecb18d18 0xfff3e3c7ff8e78e7 0xfffe7c78fff1cf1c

def z505 : W := mkw 0x433938f2b0130130 0x8867271e56026026 0x823c3cf830718718 0x9047879f060e30e3

def z506 : W := mkw 0x4000000000130130 0x8800000000026026 0x0000000000718718 0x00000000000e30e3

def z507 : W := mkw 0x43fbb3e720130130 0x887f767ce4026026 0xbbf322c6307fc7ff 0xf77e6458c60ff8ff

def z508 : W := mkw 0x4000000000130130 0x8800000000026026 0x38030206007fc7ff 0x67006040c00ff8ff

def z509 : W := mkw 0x07ffbff7ba738004 0xc0fff7fef74e7000 0xf3fffffff0718001 0xfe7ffffffe0e3000

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000000704706 0x01000000000e08e0

def z511 : W := mkw 0x83fbfbf7f58c68c3 0x107f7f7efeb18d18 0xf7ffffffff803801 0xfefffffffff00700

def z512 : W := mkw 0x0539300002330004 0xc0a7260000466000 0x0030000000300000 0x0006000000060000

def z513 : W := mkw 0x816c43a84ee87e86 0x302d887509dd0fd0 0xfffcc3f9cff87f87 0xffff987f39ff0ff0

def z514 : W := mkw 0x000400080a601604 0x20008001014c02c0 0x0000000000700700 0x00000000000e00e0

def z515 : W := mkw 0x80004000458c68c3 0x1000080008b18d18 0x5c00c101cf8e78e7 0x6b80182039f1cf1c

def z516 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xf3fffffff07f8007 0xfe7ffffffe0ff000

def z517 : W := mkw 0xa5ffff1ddffffccf 0xf4bfffe3bbffff99 0xfdffff3ffffffcff 0xffbfffe7ffffff9f

def z518 : W := mkw 0xa0156c5afc489c8a 0x3402ad8b5f891391 0xfe3ffffffc49bc9b 0xffc7ffffff893793

def z519 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x8c0c3c383c49bc9a 0x9181878707893793

def z520 : W := mkw 0x4011204220130130 0x8802240844026026 0xb23322c630718719 0xf6466458c60e30e3

def z521 : W := mkw 0xa3fbfff7f408888a 0x147f7ffefe811111 0xf3fffffff0098099 0xfe7ffffffe013013

def z522 : W := mkw 0x017d23a80af37604 0xa02fa475015e6ec0 0xffff23f80fffff06 0xffffe47f01ffffe0

def z523 : W := mkw 0x0293b857b0000000 0x0052770af6000000 0xb233fec7f0000001 0xf6467fd8fe000000

def z524 : W := mkw 0x0093b00000000000 0x0012760000000000 0x0003fc0000000000 0x20007f8000000000

def z525 : W := mkw 0x05bfb4000b778005 0xc0b7f680016ef000 0xa1ff3c0003f78004 0x143fe780007ef000

def z526 : W := mkw 0xa3eedfbddc489c8a 0x347ddbf7bb891391 0xddccfd39fc49bc9b 0xfbb99fa73f893793

def z527 : W := mkw 0x8082c000450c0883 0x1010580008a18110 0x7dc3c101cf8e3887 0x6fb8782039f1c710

def z528 : W := mkw 0x02400bf7b0000000 0x0048017ef6000000 0xd20cfffff0000001 0xfa419ffffe000000

def z529 : W := mkw 0x0011204220130000 0x8002240844026000 0xb23322c6307f8007 0xf6466458c60ff000

def z530 : W := mkw 0x40112852b0130130 0x8802250a56026026 0xfa3ffffff07fc7ff 0xff47fffffe0ff8ff

def z531 : W := mkw 0x05fff7050fffe047 0xc0bffee0a1fffc08 0xf5fffe060fffc066 0x3ebfffc0c1fff80c

def z532 : W := mkw 0x000444000c488002 0x0000888001891000 0x040000000c498002 0x0080000001893000

def z533 : W := mkw 0x4011204220130130 0x8802240844026026 0x0a0322c6300fc7f9 0xe1406458c601f8ff

def z534 : W := mkw 0x4493f442251f8133 0xc8927e8844a3f026 0xba33fec6307fc7ff 0xf7467fd8c60ff8ff

def z535 : W := mkw 0x01ea83a503a46245 0x003d5074a0748c48 0x23f302c603b64364 0x047e6058c076c86c

def z536 : W := mkw 0xa3fffffffdccfccb 0x347fffffffb99f99 0xffffffffffcffcff 0xfffffffffff9ff9f

def z537 : W := mkw 0xe0044c5afc489dba 0x3c00898b5f8913b7 0xde0cfffffc49fffb 0xfbc19fffff893fff

def z538 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x0c00fc01fc49bc9b 0x21801f803f893793

def z539 : W := mkw 0x033d38faba601604 0x2067a71f574c02c0 0x823c3cf830700700 0x9047879f060e00e0

def z540 : W := mkw 0xa5ffffb8dffffe8f 0xf4bffff71bffffd1 0xfffffff9ffffff9f 0xffffffff3ffffff3

def z541 : W := mkw 0x216c0fb89ae0f60c 0x242d81f7135c1ec1 0xfffc3ff83ff1ff1e 0xdfff87ff07fe3fe3

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800000000400402 0xd300000000080080

def z543 : W := mkw 0x83eadbb5d58c68c3 0x107d5b76bab18d18 0x7dcfdf3fcf8e78e7 0x6fb9fbe7f9f1cf1c

def z544 : W := mkw 0x016803a000806000 0x002d007400100c00 0xfffc03f80f807806 0xdfff807f01f00f00

def z545 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x4c0cdd39cc49bc9a 0x09819ba739893793

def z546 : W := mkw 0x016803a000000000 0x002d007400000000 0x23f002c000000000 0x047e005800000000

def z547 : W := mkw 0xa3eedfbddc489c8a 0x347ddbf7bb891391 0x45ccdd39cc003800 0x08b99ba739800700

def z548 : W := mkw 0x416c03a80af37734 0xa82d8075015e6ee6 0xfffc03f80ffffffe 0xdfff807f01ffffff

def z549 : W := mkw 0x45bbb04223370135 0xc8b776084466e026 0x23f302c603b64364 0x047e6058c076c86c

def z550 : W := mkw 0xa082cc15d50c88cb 0x14105982baa19119 0x0003fc07f00f80f9 0x20007f80fe01f01f

def z551 : W := mkw 0x4011204220130130 0x8802240844026026 0xa23322c63077c77c 0x94466458c60ef8ef

def z552 : W := mkw 0x80c6c30d4fec7ec7 0x3018d861a9fd8fd8 0x7dc3c307cffe7fe7 0x6fb87860f9ffcffc

def z553 : W := mkw 0x03fbb3e722a06204 0x007f767ce4540c40 0x23f302c603b04304 0x047e6058c0760860

def z554 : W := mkw 0x4000004220000130 0x0800000844000026 0x00000006300000f9 0x00000000c600001f

def z555 : W := mkw 0xa00444084ee8fe8e 0x3400888109dd1fd1 0x0c0000000ff9ff9e 0x0180000001ff3ff3

def z556 : W := mkw 0x4011204220130130 0x8802240844026026 0x0000200030018018 0x0000040006003003

def z557 : W := mkw 0xa0156c18dc5b9c8a 0xb402ad831b8b7391 0xfc3ffd39fc7fbc9f 0xff87ffa73f8ff793

def z558 : W := mkw 0x03ffbbffbae07604 0x207ff77ff75c0ec0 0xf7ffffffff803801 0xfefffffffff00700

def z559 : W := mkw 0x4011204220130130 0x8802240844026026 0x38032206300fc0ff 0x67006440c601f81f

def z560 : W := mkw 0x4011204220130130 0x8802240844026026 0xb23322c6007fc366 0x36466458c00ff86c

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x75c000000f800006 0x0eb8000001f00000

def z562 : W := mkw 0x01bff4000c488002 0x0037fe8001891000 0xf5fffc000c498002 0x3ebfff8001893000

def z563 : W := mkw 0x4000004220000130 0x0800000844000026 0x020000c030000718 0x80400018060000e3

def z564 : W := mkw 0x02c28bf7b0000000 0x0058517ef6000000 0x73c3c3fff0000001 0xee78787ffe000000

def z565 : W := mkw 0x03ffbbffb8401400 0x207ff77ff7080280 0xfffffffffc403c03 0xffffffffff880780

def z566 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000200000498002 0x3200040000093000

def z567 : W := mkw 0x4000004220000130 0x0800000844000026 0x3a0302c6300e47ff 0xe7406058c601c8ff

def z568 : W := mkw 0x01eec3a80fec7607 0x203dd87501fd8ec0 0xffffc3f80ffe7f06 0xfffff87f01ffcfe0

def z569 : W := mkw 0x4000000000130130 0x8800000000026026 0xba3002c0007fc7fe 0xd7460058000ff8ff

def z570 : W := mkw 0x85fff7ad4ffffec7 0xf0bffef5a9ffffd8 0xffffffffcfffffe7 0xfffffffff9fffffc

def z571 : W := mkw 0x0000000000130000 0x8000000000026000 0x00000000007f8006 0x00000000000ff000

def z572 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x4dc0c101cf8e78e6 0x09b8182039f1cf1c

def z573 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x75c3c101cf8e3806 0x2eb8782039f1c700

def z574 : W := mkw 0x81fbf305458c68c3 0x103f7e60a8b18d18 0xfdffff07cf8e78e7 0x7fbfffe0f9f1cf1c

def z575 : W := mkw 0x85eed7054fece8c7 0x50bddae0a9fd9d18 0x7dcfdf07cf8e78e7 0x6fb9fbe0f9f1cf1c

def z576 : W := mkw 0x816c43a84fec7ec7 0x302d887509fd8fd8 0xfffc03f80ffe7fe6 0xdfff807f01ffcffc

def z577 : W := mkw 0x00c2830501846041 0x00185060a0308c08 0x39c30206038e40e7 0x67386040c071c81c

def z578 : W := mkw 0x82c2cbf7f58c68c3 0x1058597efeb18d18 0x7fc3c3ffff8e78e7 0xeff8787ffff1cf1c

def z579 : W := mkw 0x8000400044080882 0x1000080008810110 0x4400c101cc003800 0x0880182039800700

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x223002c000304304 0x0446005800060860

def z581 : W := mkw 0xa086cc1ddd4c9ccb 0x3410d983bba99399 0xdc0ffd3ffc4fbcfb 0xfb81ffa7ff89f79f

def z582 : W := mkw 0x0000081090000000 0x0000010212000000 0x800c3c3830000000 0x9001878706000000

def z583 : W := mkw 0x0497f4000f7f8007 0xc092fe8001eff000 0x0403fc000fff8006 0x20807f8001fff000

def z584 : W := mkw 0x000400080ae07604 0x20008001015c0ec0 0xdc0c01380ff07f06 0xdb81802701fe0fe0

def z585 : W := mkw 0xa5bffc18df7f9c8f 0xf4b7ff831beff391 0xf5fffd39cfffb806 0x3ebfffa739fff700

def z586 : W := mkw 0x0011200000130000 0x8002240000026000 0x00032000000f8000 0x200064000001f000

def z587 : W := mkw 0xa0000818d0001c88 0x340001031a000391 0xd80cfd39f0003c99 0xfb019fa73e000793

def z588 : W := mkw 0x0040030000806000 0x0008006000100c00 0x21c0020003804004 0x0438004000700800

def z589 : W := mkw 0x012c00080a601404 0x20258001014c0280 0xfdfc01380ff03c06 0xdfbf802701fe0780

def z590 : W := mkw 0x03680bf7b0000000 0x006d017ef6000000 0xf3fc03fff0000001 0xde7f807ffe000000

def z591 : W := mkw 0xa16c4fb8dee8fe8e 0x342d89f71bdd1fd1 0x45ccdd39cf803800 0x08b99ba739f00700

def z592 : W := mkw 0x4015204a2af37734 0xa802a409455e6ee6 0xbe3322c63fffffff 0xf7c66458c7ffffff

def z593 : W := mkw 0x80c6c30d4dcc7cc3 0x3018d861a9b98f98 0xfdcfc33fcfce7ce7 0xffb9f867f9f9cf9c

def z594 : W := mkw 0x00c2c300058c6003 0x0018586000b18c00 0x7dc3c3000f8e7806 0x6fb8786001f1cf00

def z595 : W := mkw 0x81eec3054fec68c7 0x103dd860a9fd8d18 0xfdffc307cffe78e7 0x7fbff860f9ffcf1c

def z596 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x7dcc03380f807806 0x4fb9806701f00f00

def z597 : W := mkw 0x83fbfbf7f50c08c3 0x107f7f7efea18118 0xf3fffffff00e00e1 0xfe7ffffffe01c01c

def z598 : W := mkw 0x016803a000000000 0x002d007400000000 0xfbfc03f800704706 0xdf7f807f000e08e0

def z599 : W := mkw 0x05fbb30503b76045 0xc0bf7660a076ec08 0x21f3020603b64064 0x043e6040c076c80c

def z600 : W := mkw 0x00c2c305050c0003 0x00185860a0a18000 0x75c3c307cf8e0007 0x6eb87860f9f1c000

def z601 : W := mkw 0x016c03a80a601604 0x202d8075014c02c0 0xf3fc03f800700700 0xde7f807f000e00e0

def z602 : W := mkw 0x0082800001040001 0x0010500000208000 0x21c3000003860004 0x043860000070c000

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0xb23002c000000000 0xd646005800000000

def z604 : W := mkw 0x0011200000130000 0x8002240000026000 0xba3322c0007fc706 0xf7466458000ff8e0

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00cfc0000000000 0x3a019f8000000000

def z606 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x5c0cdd39cc083883 0x6b819ba739810710

def z607 : W := mkw 0x0040030000806000 0x0008006000100c00 0x45c001000f803800 0x08b8002001f00700

def z608 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xf7fc03f80f803800 0xdeff807f01f00700

def z609 : W := mkw 0x0011200000130000 0x8002240000026000 0x8030200000718000 0x10060400000e3000

def z610 : W := mkw 0x453d34422a738134 0xc8a7a688454e7026 0xba3f3ec6307fc7ff 0xf747e7d8c60ff8ff

def z611 : W := mkw 0x03fbb3e720000000 0x007f767ce4000000 0x73f3c3c7c0000001 0x6e7e7878f8000000

def z612 : W := mkw 0x80c6c7054dcce8c3 0x1018d8e0a9b99d18 0xfdcfff07cfcff8e7 0x7fb9ffe0f9f9ff1c

def z613 : W := mkw 0x404003ea20807730 0x2808007d44100ee6 0x0a0003fe30007ff9 0xc140007fc6000fff

def z614 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0xdc0c01380c49bc9a 0xdb81802701893793

def z615 : W := mkw 0xe17d6ffafefbffbe 0xbc2fadff5fdf7ff7 0xffffffffffffffff 0xffffffffffffffff

def z616 : W := mkw 0x053d34000a738004 0xc0a7a680014e7000 0xb03f3c00007f8006 0x3607e780000ff000

def z617 : W := mkw 0x401564422c5b8132 0x8802ac88458b7026 0xfe3ffec63c7fc7ff 0xffc7ffd8c78ff8ff

def z618 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x5c00c101cc49bc9b 0x6b80182039893793

def z619 : W := mkw 0x40d3a34721976171 0x881a7468e432ec2e 0xbbf322c633ffc7ff 0xf77e6458c67ff8ff

def z620 : W := mkw 0xa5aedc18df6c9c8f 0x74b5db831bed9391 0x45ccdd39cf803800 0x08b99ba739f00700

def z621 : W := mkw 0x0040030000806000 0x0008006000100c00 0xfff003c00ff07f06 0xdffe007801fe0fe0

def z622 : W := mkw 0x45fff7ea2ffff737 0xe8bffefd45fffee6 0xfffffffe3fffffff 0xffffffffc7ffffff

def z623 : W := mkw 0x05fff7050f7f8007 0xc0bffee0a1eff000 0xf5ffff07cfff8007 0x7ebfffe0f9fff000

def z624 : W := mkw 0x053d74000e7b8006 0xc0a7ae8001cf7000 0xd43cfc000c798002 0x3a879f80018f3000

def z625 : W := mkw 0x25bffc189f7f940f 0xe4b7ff8313eff281 0xf5fffc383fff841e 0xbebfff8707fff083

def z626 : W := mkw 0x03ffbbf7ba600004 0x007ff77ef74c0000 0xf7fffffffff00007 0xfefffffffffe0000

def z627 : W := mkw 0x0493f400051f8003 0xc0927e8000a3f000 0xb033fc00007f8006 0x36067f80000ff000

def z628 : W := mkw 0xa0444f18dcc8fc8a 0x340889e31b991f91 0xfdccff39ffc9fc9f 0xffb99fe73ff93f93

def z629 : W := mkw 0x60152c5ab8539538 0xac02a58b570a72a7 0x823c3cf830718718 0x9047879f060e30e3

def z630 : W := mkw 0x4000000000130130 0x8800000000026026 0x00000000000f80f8 0x000000000001f01f

def z631 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x23f3fec7f0000001 0x247e7fd8fe000000

def z632 : W := mkw 0x85fff7054fffe8c7 0xd0bffee0a9fffd18 0xf5fffd01cfffb806 0x3ebfffa039fff700

def z633 : W := mkw 0xc0004000459f69f3 0x9800080008b3ed3e 0x0c0000000ffffffe 0x0180000001ffffff

def z634 : W := mkw 0x016c03a00ae06204 0x002d8074015c0c40 0xf7fc02c00ff04306 0x1eff805801fe0860

def z635 : W := mkw 0x0000000800807600 0x2000000100100ec0 0x0800000000007f00 0x0100000000000fe0

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8032206304fc4ff 0xf7006440c609f89f

def z637 : W := mkw 0x012c00000a600004 0x00258000014c0000 0x803c000000700000 0x10078000000e0000

def z638 : W := mkw 0x0040030500000000 0x00080060a0000000 0x00000307c0000001 0x40000060f8000000

def z639 : W := mkw 0x405123ea20937730 0xa80a247d44126ee6 0xba3323fe307fffff 0xf746647fc60fffff

def z640 : W := mkw 0x4011204220130130 0x8802240844026026 0xb23322c6300f80f9 0xf6466458c601f01f

def z641 : W := mkw 0x400400080af37734 0xa8008001015e6ee6 0x0c0000000ffffffe 0x0180000001ffffff

def z642 : W := mkw 0x4011204220130130 0x8802240844026026 0x223322c6303fc3fd 0x24466458c607f87f

def z643 : W := mkw 0x05fff7a00fffe207 0xc0bffef401fffc40 0xf7fffec00fffc306 0x3effffd801fff860

def z644 : W := mkw 0x00004000050c0003 0x0000080000a18000 0x040000000f8e0006 0x0080000001f1c000

def z645 : W := mkw 0x05fbb3a003b76205 0xc0bf76740076ec40 0x23f302c003b64304 0x047e60580076c860

def z646 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0xdc0cfc000c49bc9a 0x3b819f8001893793

def z647 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x25f300000fff8006 0x04be600001fff000

def z648 : W := mkw 0x07fbfff7b51f8003 0xc0ff7ffef6a3f000 0xf3fffffff00f8001 0xfe7ffffffe01f000

def z649 : W := mkw 0x03ffb3ef2ae07604 0x207ff67de55c0ec0 0xffff03fe0ff07f06 0xdfffe07fc1fe0fe0

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000206000040e1 0x41000040c000081c

def z651 : W := mkw 0x03fbb3e720000000 0x007f767ce4000000 0xf3fffec600000000 0x3e7fffd8c0000000

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800020000004006 0x4700004000000800

def z653 : W := mkw 0x03fbb3e720000000 0x007f767ce4000000 0xb3f322c630000001 0xf67e6458c6000000

def z654 : W := mkw 0x83fbfbf7f4080882 0x107f7f7efe810110 0xfffffffffc083883 0xffffffffff810710

def z655 : W := mkw 0x0000000001846041 0x0000000000308c08 0x0000000003864064 0x000000000070c80c

def z656 : W := mkw 0x03793bf2b0000000 0x006f277e56000000 0xf3fc3ff830000000 0xde7f87ff06000000

def z657 : W := mkw 0x07bffcf2bf7f8007 0xc0f7ff9e57eff000 0xf7fffcf83fff8006 0xbeffff9f07fff000

def z658 : W := mkw 0x0004000808401400 0x2000800101080280 0x800c003800400400 0x9001800700080080

def z659 : W := mkw 0x024003e720000000 0x0048007ce4000000 0x020002c600000000 0x00400058c0000000

def z660 : W := mkw 0xc0c2c305459f69f3 0x98185860a8b3ed3e 0x7dc3c307cfffffff 0x6fb87860f9ffffff

def z661 : W := mkw 0x016c47a80ee8f606 0x202d88f501dd1ec0 0xfffcfff80ff9ff06 0xffff9fff01ff3fe0

def z662 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0cdd39cc403c02 0xdb819ba739880780

def z663 : W := mkw 0x07ffffffbffff607 0xe0fffffff7fffec0 0xffffffffffffff07 0xffffffffffffffe0

def z664 : W := mkw 0x017923e220000000 0x002f247c44000000 0xf3ff23fe30000001 0xfe7fe47fc6000000

def z665 : W := mkw 0x413d20ea2a731734 0xa827a41d454e62e6 0xba3f22fe307fc7ff 0xf747e45fc60ff8ff

def z666 : W := mkw 0x03fbbbffb0807600 0x207f777ff6100ec0 0xfbfffffff0007f01 0xff7ffffffe000fe0

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c0001000c003802 0x4b80002001800700

def z668 : W := mkw 0x0004040008408000 0x0000808001081000 0x800c3c0000418000 0x1001878000083000

def z669 : W := mkw 0xc0d3e347659f69f3 0x981a7c68ecb3ed3e 0x7dc3e307ff8ff8ff 0x6fb87c60fff1ff1f

def z670 : W := mkw 0x800440084fec7ec7 0x3000880109fd8fd8 0x0c0000000ffe7fe6 0x0180000001ffcffc

def z671 : W := mkw 0xa2400bfff0001c88 0x3448017ffe000391 0x0a0003fff0003c99 0xc140007ffe000793

def z672 : W := mkw 0xa16c4fb8dee8fe8e 0x342d89f71bdd1fd1 0xddccfd39ffc9bc9b 0xfbb99fa73ff93793

def z673 : W := mkw 0xa12c4cb8de689e8e 0x342589971bcd13d1 0xde3cfdf9fc79bf9b 0xfbc79fbf3f8f37f3

def z674 : W := mkw 0x004403080ae07604 0x20088061015c0ec0 0x7dc003000ff07f06 0x4fb8006001fe0fe0

def z675 : W := mkw 0x0004000808401400 0x2000800101080280 0xdc0c21383c49bc9b 0xfb81842707893793

def z676 : W := mkw 0x013d20000a730004 0x8027a400014e6000 0xf5ff20000fff8006 0x3ebfe40001fff000

def z677 : W := mkw 0x0011204220000000 0x0002240844000000 0xba3322c6300e40e7 0xf7466458c601c81c

def z678 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0xb1f3200003ff8006 0x363e6400007ff000

def z679 : W := mkw 0x033930e220000000 0x0067261c44000000 0x023000c000000000 0x0046001800000000

def z680 : W := mkw 0x004403a80ae07604 0x20088075015c0ec0 0x0e0003f80ff07f06 0xc1c0007f01fe0fe0

def z681 : W := mkw 0x4011204220130130 0x8802240844026026 0xba3302c600764766 0xd7466058c00ec8ec

def z682 : W := mkw 0x01ea83a500000000 0x003d5074a0000000 0xf3ffc3ffc0000001 0xfe7ff87ff8000000

def z683 : W := mkw 0x42512bf7b0130130 0x884a257ef6026026 0xba3323fff07fc7ff 0xf746647ffe0ff8ff

def z684 : W := mkw 0x80c2c305450c08c3 0x10185860a8a18118 0x71c3c307c00e00e1 0x6e387860f801c01c

def z685 : W := mkw 0x80404305448868c2 0x10080860a8910d18 0x5c00c307cc0878e3 0x6b801860f9810f1c

def z686 : W := mkw 0x4011204220130130 0x8802240844026026 0x98032006304f84fb 0xf3006400c609f09f

def z687 : W := mkw 0x0040030000806000 0x0008006000100c00 0x0800030000007800 0x4100006000000f00

def z688 : W := mkw 0x05ffb3a80bf77605 0xe0bff675017eeec0 0xffff03f80ff67f06 0xdfffe07f01fecfe0

def z689 : W := mkw 0x8293f857f50c08c3 0x10527f0afea18118 0x0003fc07f00e00e1 0x20007f80fe01c01c

def z690 : W := mkw 0x20040c1898409408 0x2400818313081281 0xd00cfd39f0418419 0xfa019fa73e083083

def z691 : W := mkw 0x4011204220130130 0x8802240844026026 0x08032006307fc7ff 0x21006400c60ff8ff

def z692 : W := mkw 0x82d3fb57f58c68c3 0x105a7f6afeb18d18 0x7dc3ff07ff8e78e7 0x6fb87fe0fff1cf1c

def z693 : W := mkw 0xc0c2c347658c69f3 0x18185868ecb18d3e 0x7fc3c3c7ff8e7fff 0xeff87878fff1cfff

def z694 : W := mkw 0x03bbb8f2b0000000 0x0077771e56000000 0xf3fffcf830000000 0xbe7fff9f06000000

def z695 : W := mkw 0x004403a808c07600 0x2008807501180ec0 0xde0c03f80c407f02 0xdbc1807f01880fe0

def z696 : W := mkw 0x0000004220000000 0x0000000844000000 0x020002c630000001 0xc0400058c6000000

def z697 : W := mkw 0x80c2c30544080882 0x10185860a8810110 0x7dc3c307cc083883 0x6fb87860f9810710

def z698 : W := mkw 0x416c03ea2ae07734 0x282d807d455c0ee6 0xfffc03fe3ff07fff 0xdfff807fc7fe0fff

def z699 : W := mkw 0x016803a802a07604 0x202d007500540ec0 0x2bf003f803b07f04 0xc57e007f00760fe0

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000200030418418 0x9000040006083083

def z701 : W := mkw 0x00c2830501846041 0x00185060a0308c08 0x01c0000003800000 0x0038000000700000

def z702 : W := mkw 0x20040c1898409408 0x2400818313081281 0xdc0c3d383c41bc1a 0xdb8187a707883783

def z703 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x4c0cdd39fc003c99 0xc9819ba73f800793

def z704 : W := mkw 0x03fffff7bc488002 0x007ffffef7891000 0xf7fffffffc498003 0xfeffffffff893000

def z705 : W := mkw 0xa297fc5ffc489c8a 0x3452ff8bff891391 0xdc0ffd3ffc49bc9b 0xfb81ffa7ff893793

def z706 : W := mkw 0x016c03a808401400 0x202d807501080280 0xfffc03f80c403c02 0xdfff807f01880780

def z707 : W := mkw 0x82400bb5d08068c0 0x10480176ba100d18 0x0800033fc00078e1 0x41000067f8000f1c

def z708 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x45cffc000fff8006 0x28b9ff8001fff000

def z709 : W := mkw 0x01bfb0000a600004 0x0037f600014c0000 0xf5fffc000f800000 0x3ebfff8001f00000

def z710 : W := mkw 0xa1684fb0d6a8ea8e 0x142d09f61ad51d51 0x23f0fec1f3b9c39d 0x247e1fd83e773873

def z711 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x63ffdffff0000001 0xcc7ffbfffe000000

def z712 : W := mkw 0xe0156c5afc5b9dba 0xbc02ad8b5f8b73b7 0x663fdfffcc367b64 0x0cc7fbfff986cf6c

def z713 : W := mkw 0x0297b85fbae07604 0x2052f70bf75c0ec0 0x0c03fc07fff07f07 0x21807f80fffe0fe0

def z714 : W := mkw 0x05aad400072c8007 0x40b55a8000e59000 0x01c0dc0003800000 0x00381b8000700000

def z715 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xcffc03f80ff07f00 0xd9ff807f01fe0fe0

def z716 : W := mkw 0x80004810d4080882 0x100009021a810110 0xdc0cfd39fc49bc9b 0xfb819fa73f893793

def z717 : W := mkw 0xe093ec57f51f89fb 0x9c127d8afea3f13f 0x0003fc07f00f80f9 0x20007f80fe01f01f

def z718 : W := mkw 0xa0004c18d4089c8a 0x340009831a811391 0xd80cfd39f009bc99 0xfb019fa73e013793

def z719 : W := mkw 0x01680bb090000000 0x002d017612000000 0xfbfcfff9f079c79f 0xff7f9fff3e0f38f3

def z720 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xf5fffc000fff871e 0x3ebfff8001fff0e3

def z721 : W := mkw 0x833978f2f58c68c3 0x10672f1e5eb18d18 0x8e3c3cf83f8e78e6 0x91c7879f07f1cf1c

def z722 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffcc3f9cff07f07 0xffff987f39fe0fe0

def z723 : W := mkw 0xa00444084dccfccb 0x3400888109b99f99 0x0c0000000f8e78e6 0x0180000001f1cf1c

def z724 : W := mkw 0xa5bbb818d3371c8d 0xf4b777031a66e391 0x29f30139f3b63c9d 0xc53e60273e76c793

def z725 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdc3c307cfce7ce7 0xffb87860f9f9cf9c

def z726 : W := mkw 0x20c68f1d99c4f449 0x2418d1e3b3389e89 0xa1cf3e3e33c7c47c 0x9439e7c7c678f88f

def z727 : W := mkw 0x0000081090000000 0x0000010212000000 0xd80cfd39f0000499 0xfb019fa73e000093

def z728 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x43fcddf9c0000000 0x087f9bbf38000000

def z729 : W := mkw 0x0282981590000000 0x00505302b2000000 0x400cdd39c0000000 0x08019ba738000000

def z730 : W := mkw 0xc293f857f51f09f3 0x98527f0afea3e13e 0x0003fc07f00f80f9 0x20007f80fe01f01f

def z731 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0xf5fffc000f8e0006 0x3ebfff8001f1c000

def z732 : W := mkw 0xa0004c10d408888a 0x140009821a811111 0xdc0cfd39fc09b89b 0xfb819fa73f813713

def z733 : W := mkw 0x43fbbbf7b2b36334 0x887f777ef6566c66 0xf3fffffff3b64365 0xfe7ffffffe76c86c

def z734 : W := mkw 0x43fbbbf7b1976171 0x887f777ef632ec2e 0xfbfffffff3ffc7ff 0xff7ffffffe7ff8ff

def z735 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x040000000c09b898 0x0080000001813713

def z736 : W := mkw 0x04d3f7a8059ff603 0xe09a7ef500b3fec0 0x0a03fff8000fff00 0xe1407fff0001ffe0

def z737 : W := mkw 0x216c07a80ae0f60c 0x242d80f5015c1ec1 0xfffc03f80ff1ff1e 0xdfff807f01fe3fe3

def z738 : W := mkw 0xe00444084c489dba 0x3c008881098913b7 0x0c0000000c49fffa 0x0180000001893fff

def z739 : W := mkw 0x05bff4a00f7f8207 0xc0b7fe9401eff040 0xf7fffcc00fff8306 0x3effff9801fff060

def z740 : W := mkw 0x016c07a80ae0f604 0x202d80f5015c1ec0 0xfffc3ff80ff1ff06 0xdfff87ff01fe3fe0

def z741 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffc000fff8406 0xffbfff8001fff080

def z742 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0x45cffc063f8f80f9 0x28b9ff80c7f1f01f

def z743 : W := mkw 0x05bff4a80f7f9607 0xe0b7fe9501eff2c0 0xf5fffc380fff8006 0x3ebfff8701fff000

def z744 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0ffd3ffc4fbcfb 0xfb81ffa7ff89f79f

def z745 : W := mkw 0xa0000818d0001c88 0x340001031a000391 0xd80cfd39f049bc9b 0xfb019fa73e093793

def z746 : W := mkw 0x01aa981090000000 0x0035530212000000 0xd1ccfd39f0000001 0xfa399fa73e000000

def z747 : W := mkw 0xe415644a6f7f9dbf 0xfc82ac894deff3b7 0xbe3322c63fffffff 0xf7c66458c7ffffff

def z748 : W := mkw 0xa5bff4084f7f9c8f 0xf4b7fe8109eff391 0xf5fffc000fffb806 0x3ebfff8001fff700

def z749 : W := mkw 0x45aed4422f6c8137 0x48b5da8845ed9026 0x4fccdec63f8047f9 0xc9f99bd8c7f008ff

def z750 : W := mkw 0x653d3c5aba73953c 0xeca7a78b574e72a7 0x823c3cf830718718 0x9047879f060e30e3

def z751 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff077c77d 0xfe7ffffffe0ef8ef

def z752 : W := mkw 0xa3fff7ef6c489c8a 0x347ffefded891391 0x2ff302c60c49bc9a 0x05fe6058c1893793

def z753 : W := mkw 0x03bbb8f2b0000000 0x0077771e56000000 0xf3fffdf9f0000001 0xfe7fffbf3e000000

def z754 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x2dc3c207cf8e78e7 0x25b87840f9f1cf1c

def z755 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc000f8f8000 0x3ebfff8001f1f000

def z756 : W := mkw 0x417d23ea2af37734 0xa82fa47d455e6ee6 0x45cf213e3f8fb8f9 0x28b9e427c7f1f71f

def z757 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xcc0cfd39fc41bc99 0xd9819fa73f883793

def z758 : W := mkw 0x05aed4080f6c9407 0x60b5da8101ed9280 0x45ccdd380f803800 0x08b99ba701f00700

def z759 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x2ff003f80ff07f06 0xc5fe007f01fe0fe0

def z760 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xd1ccfd39c0000000 0x3a399fa738000000

def z761 : W := mkw 0xa4044c18df6c9c8f 0x748089831bed9391 0xdc0cfd39ffc9bc9b 0xfb819fa73ff93793

def z762 : W := mkw 0x03ea9bb591846041 0x007d5376b2308c08 0x61cfdf3fc3864064 0x0c39fbe7f870c80c

def z763 : W := mkw 0x01bff4000e688006 0x0037fe8001cd1000 0xf5fffc000ff98006 0x3ebfff8001ff3000

def z764 : W := mkw 0x01680bb090000000 0x002d017612000000 0xd1ccfd39f0000001 0xfa399fa73e000000

def z765 : W := mkw 0x0082c000050c0003 0x0010580000a18000 0xf5cffc000f8e0006 0x3eb9ff8001f1c000

def z766 : W := mkw 0x00c28b1591846041 0x00185162b2308c08 0xf1cfff3ff3864065 0xfe39ffe7fe70c80c

def z767 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xd1ccdd39c0000000 0xda399ba738000000

def z768 : W := mkw 0x43bbb8f7b0130130 0x8877771ef6026026 0x823ffcfff07f87f9 0xb047ff9ffe0ff0ff

def z769 : W := mkw 0x81aec0ad4f6c1ec7 0x3035d815a9ed83d8 0x823fc0ffc07e07e1 0xb047f81ff80fc0fc

def z770 : W := mkw 0x8082c000450c0883 0x1010580008a18110 0x7dc3c307cf8e78e7 0x6fb87860f9f1cf1c

def z771 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xd5cffc000fcf8002 0x3ab9ff8001f9f000

def z772 : W := mkw 0x03793bf2b0000000 0x006f277e56000000 0xf3fcfff9f0000001 0xfe7f9fff3e000000

def z773 : W := mkw 0x01680bb092a06204 0x002d017612540c40 0xf3fcfff9f3b04305 0xfe7f9fff3e760860

def z774 : W := mkw 0x40112852b0130130 0x8802250a56026026 0xd23cfdf9f0718719 0xfa479fbf3e0e30e3

def z775 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0xf1fffc0003ff8006 0x3e3fff80007ff000

def z776 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdcfc33fcf8e78e7 0xffb9f867f9f1cf1c

def z777 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc3e307ff8ff8ff 0x6fb87c60fff1ff1f

def z778 : W := mkw 0x05bbf400073f8007 0xc0b77e8000e7f000 0xf1fffc0003bf8004 0x3e3fff800077f000

def z779 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xfffcdec00ff04706 0xdfff9bd801fe08e0

def z780 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xc5fcdc000ff00000 0x18bf9b8001fe0000

def z781 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc03fe0ff07fe7 0xdfff807fc1fe0ffc

def z782 : W := mkw 0x05bfb4000b778005 0xc0b7f680016ef000 0x81fc3c0003f18000 0x103f8780007e3000

def z783 : W := mkw 0x03bbb8f7b0000000 0x0077771ef6000000 0xd23ffdfff0000001 0xfa47ffbffe000000

def z784 : W := mkw 0xe5bff44a6f7f9dbf 0xfcb7fe894deff3b7 0xfffffec63fffffff 0xffffffd8c7ffffff

def z785 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0x61ffdd39c0000000 0x0c3ffba738000000

def z786 : W := mkw 0x07fbbbb593370005 0xc0ff7776b266e000 0x61ffdd39c3b60004 0x0c3ffba73876c000

def z787 : W := mkw 0xa00444084c5b9c8a 0xb4008881098b7391 0x0c0000000c7fbc9e 0x01800000018ff793

def z788 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff07fc367 0xfe7ffffffe0ff86c

def z789 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3ffffffc0000000 0x3e7ffffff8000000

def z790 : W := mkw 0xa00444084e689e8e 0x3400888109cd13d1 0x0c0000000c79bf9a 0x01800000018f37f3

def z791 : W := mkw 0x03ea9bb592a06204 0x007d5376b2540c40 0x63fcdff9c3b04304 0x0c7f9bff38760860

def z792 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xddccfc003fc9849b 0xfbb99f8007f93093

def z793 : W := mkw 0x80400305408068c0 0x10080060a8100d18 0x7dc30307cf8e78e7 0x6fb86060f9f1cf1c

def z794 : W := mkw 0x012c44000e688006 0x0025888001cd1000 0xf5fcdc000ff00006 0x1ebf9b8001fe0000

def z795 : W := mkw 0xa00444084cc8fc8a 0x3400888109991f91 0x0c0000000fc9fc9e 0x0180000001f93f93

def z796 : W := mkw 0x01ae90000a600004 0x0035d200014c0000 0xf5fcdc000ff00006 0x1ebf9b8001fe0000

def z797 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x7ffc03f80fb07b06 0x4fff807f01f60f60

def z798 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x41ccfd39f0000000 0x08399fa73e000000

def z799 : W := mkw 0x06444ff7bf7f8007 0xc0c889fef7eff000 0x060003ffffff8007 0xc0c0007ffffff000

def z800 : W := mkw 0x004447a80cc8f602 0x200888f501991ec0 0xde0cfff80c49ff02 0xfbc19fff01893fe0

def z801 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3ffdfffc0000000 0xde7ffbfff8000000

def z802 : W := mkw 0x056c17a80ae0f604 0x60ad82f5015c1ec0 0xfffc1ff80ff07f06 0xdfff83ff01fe0fe0

def z803 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x45ccdc000fc98002 0x08b99b8001f93000

def z804 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff07f871f 0xfe7ffffffe0ff0e3

def z805 : W := mkw 0x05bff4422f6c8007 0x40b7fe8845ed9000 0xf7fffec63f800001 0xfeffffd8c7f00000

def z806 : W := mkw 0x4011204220130130 0x8802240844026026 0xaa3322c6307fc7fe 0x95466458c60ff8ff

def z807 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xcc0cfd39fc49bc9a 0x99819fa73f893793

def z808 : W := mkw 0x0000081090000000 0x0000010212000000 0x400cdd39f0000001 0xc8019ba73e000000

def z809 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xf5cffc000fcf8006 0x3eb9ff8001f9f000

def z810 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfdccfd39ffc9bc9f 0xffb99fa73ff93793

def z811 : W := mkw 0x057d37a80af3f604 0xe0afa6f5015e7ec0 0x8a3c3ff80071ff00 0xd14787ff000e3fe0

def z812 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff0400403 0xff7ffffffe080080

def z813 : W := mkw 0x47fbbbf7b3370135 0xc8ff777ef666e026 0xf3fffffff3b64365 0xfe7ffffffe76c86c

def z814 : W := mkw 0x05aed4080f6c9407 0x60b5da8101ed9280 0xddccdd380fc03c02 0xdbb99ba701f80780

def z815 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x040000000c41bc18 0x0080000001883783

def z816 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffc000fffc706 0x3fbfff8001fff8e0

def z817 : W := mkw 0x80c2c705458ce8c3 0x101858e0a8b19d18 0x7dc3ff07cf8ff8e7 0x6fb87fe0f9f1ff1c

def z818 : W := mkw 0x41792bf2b0130130 0x882f257e56026026 0xfbfffffff07fc7ff 0xff7ffffffe0ff8ff

def z819 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0x65ffdc000f800000 0x0cbffb8001f00000

def z820 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x65fffc000fbf8004 0x2cbfff8001f7f000

def z821 : W := mkw 0x0000081090000000 0x0000010212000000 0xd80cfd39f0400403 0xfb019fa73e080080

def z822 : W := mkw 0x01aad000050c0003 0x00355a0000a18000 0x45ccdc000f800000 0x08b99b8001f00000

def z823 : W := mkw 0x03ea9bb591846041 0x007d5376b2308c08 0x41ccdd39c3800000 0x08399ba738700000

def z824 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xfffffec63fffc0e7 0xffffffd8c7fff81c

def z825 : W := mkw 0x85bff4054f7f88c7 0xd0b7fe80a9eff118 0xfdfffd07cfffb8e7 0x7fbfffa0f9fff71c

def z826 : W := mkw 0x0000081090000000 0x0000010212000000 0xf00fff3ff0000001 0xfe01ffe7fe000000

def z827 : W := mkw 0x02400bf7b0806000 0x0048017ef6100c00 0x0a0003fff0007801 0xc140007ffe000f00

def z828 : W := mkw 0x02400bb590000000 0x00480176b2000000 0xd00cfd39f0000001 0xfa019fa73e000000

def z829 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000000c4ffcfe 0x018000000189ff9f

def z830 : W := mkw 0x85bff4004f7f8887 0xd0b7fe8009eff110 0xf5fffd01cfffb806 0x3ebfffa039fff700

def z831 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x43ccdff9c0000000 0xc8799bff38000000

def z832 : W := mkw 0xa5aed4084f6c9c8f 0x74b5da8109ed9391 0x45ccdc000f803800 0x08b99b8001f00700

def z833 : W := mkw 0xa40444084ffffe8f 0xf480888109ffffd1 0x0c0000000fffff9e 0x0180000001fffff3

def z834 : W := mkw 0x82512bf7f08068c0 0x104a257efe100d18 0xba3323fff00e78e7 0xf746647ffe01cf1c

def z835 : W := mkw 0x433938f2b0130130 0x8867271e56026026 0xfa3ffffff07fc7ff 0xff47fffffe0ff8ff

def z836 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffe060fff8007 0x7ebfffc0c1fff000

def z837 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc23f83ff07f07 0xffff847f07fe0fe0

def z838 : W := mkw 0x03fbbbb590130000 0x807f7776b2026000 0xf1fffd39c07f8006 0x3e3fffa7380ff000

def z839 : W := mkw 0xe015644a6c5b9dba 0xbc02ac894d8b73b7 0x2e3302c60c7ffffe 0x05c66058c18fffff

def z840 : W := mkw 0x03fbbbf7b2200004 0x007f777ef6440000 0xf3fffffff3b00005 0xfe7ffffffe760000

def z841 : W := mkw 0x42400bffb0807730 0x2848017ff6100ee6 0x0a0003fff0007ff9 0xc140007ffe000fff

def z842 : W := mkw 0x01bbf042250c0003 0x00377e0844a18000 0xfffffec63f8e40e7 0xffffffd8c7f1c81c

def z843 : W := mkw 0x03fbbbf7b1846041 0x007f777ef6308c08 0xfbfffffff38e40e7 0xff7ffffffe71c81c

def z844 : W := mkw 0x453d34422a738134 0xc8a7a688454e7026 0xfffc3ec03ff1c71e 0xdfff87d807fe38e3

def z845 : W := mkw 0xa5bff4084f7f9c8f 0xf4b7fe8109eff391 0xfdfffd01cfffbc9f 0x7fbfffa039fff793

def z846 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0x45cffc000f800000 0x28b9ff8001f00000

def z847 : W := mkw 0x80400b15d08068c0 0x10080162ba100d18 0x0800033ff00078e1 0xc1000067fe000f1c

def z848 : W := mkw 0x43ea9bb590130130 0x887d5376b2026026 0x49ccdd39c07fc7fe 0x09399ba7380ff8ff

def z849 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdc3e307ff8e78e7 0xffb87c60fff1cf1c

def z850 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x75ffdc000fbe0006 0x2ebffb8001f7c000

def z851 : W := mkw 0x45bfb4422b778135 0xc8b7f688456ef026 0xbbff3ec633ffc7ff 0xf77fe7d8c67ff8ff

def z852 : W := mkw 0x016c03ad0ae07644 0x202d8075a15c0ec8 0xfffc03fe0ff07f66 0xdfff807fc1fe0fec

def z853 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0x43ccddf9f0000000 0x88799bbf3e000000

def z854 : W := mkw 0x02512bf7b0000000 0x004a257ef6000000 0xf23ffffff0000001 0xfe47fffffe000000

def z855 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0xa1ff3c0003b60004 0x143fe7800076c000

def z856 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x45cfdc000f860000 0x08b9fb8001f0c000

def z857 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc003fff8007 0xfebfff8007fff000

def z858 : W := mkw 0xa00444084d4c9c8b 0x3400888109a99391 0x0c0000000fcfbc9e 0x0180000001f9f793

def z859 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xfbfffffff07fc0e7 0xff7ffffffe0ff81c

def z860 : W := mkw 0x0082881590000000 0x00105102b2000000 0xd00ffd3ff0000001 0xfa01ffa7fe000000

def z861 : W := mkw 0x012c44000e688006 0x0025888001cd1000 0xfffcfec03ff9c79f 0xffff9fd807ff38f3

def z862 : W := mkw 0x43fbbbf7b0936130 0x887f777ef6126c26 0xffffffffffffffff 0xffffffffffffffff

def z863 : W := mkw 0x45bbf442273f8137 0xc8b77e8844e7f026 0x23f3fec633bfc3fd 0x247e7fd8c677f87f

def z864 : W := mkw 0x03fbbbf7b0806000 0x007f777ef6100c00 0xf3fffffff3804005 0xfe7ffffffe700800

def z865 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x79cfdf3fc00e40e7 0x6f39fbe7f801c81c

def z866 : W := mkw 0x013d64000e7b8006 0x8027ac8001cf7000 0xf5fffc000fff8006 0x3ebfff8001fff000

def z867 : W := mkw 0x42400bf7b0000130 0x0848017ef6000026 0xda0cfffff049c7fb 0xfb419ffffe0938ff

def z868 : W := mkw 0x01aa981090000000 0x0035530212000000 0x41ccdd39c0000000 0x08399ba738000000

def z869 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x41cfdd3fc0000001 0x2839fba7f8000000

def z870 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x65ffdc000fff8006 0x0cbffb8001fff000

def z871 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xd5ccfc000f800000 0x3ab99f8001f00000

def z872 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xf7fc03f80ff07b06 0x1eff807f01fe0f60

def z873 : W := mkw 0x033938f2b0000000 0x0067271e56000000 0x823cfcf9f0000001 0xb0479f9f3e000000

def z874 : W := mkw 0x012c00000a600004 0x00258000014c0000 0xf5fcfc000ff00006 0x3ebf9f8001fe0000

def z875 : W := mkw 0x613d2cfaba73973c 0xac27a59f574e72e7 0x823c3cf830718718 0x9047879f060e30e3

def z876 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xd40cfd39fc49b89b 0x3a819fa73f893713

def z877 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc000fb60004 0x3ebfff8001f6c000

def z878 : W := mkw 0x0000081090000000 0x0000010212000000 0xc00cfd39f0000000 0x98019fa73e000000

def z879 : W := mkw 0xa41564084f7f9c8f 0xf482ac8109eff391 0xbc3320003fffbc9f 0xf786640007fff793

def z880 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xf7fc03f80ff03f00 0xdeff807f01fe07e0

def z881 : W := mkw 0x05bfb4000b778005 0xc0b7f680016ef000 0xf1fffc0003f78004 0x3e3fff80007ef000

def z882 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xf3fffffff0360005 0xfe7ffffffe06c000

def z883 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xe7fc03f80ff07f04 0x9cff807f01fe0fe0

def z884 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x65cfdc000f860004 0x0cb9fb8001f0c000

def z885 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff00e00e1 0xfe7ffffffe01c01c

def z886 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xf3fffffff0004361 0xfe7ffffffe00086c

def z887 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0x21f3fc0003b60004 0x243e7f800076c000

def z888 : W := mkw 0x052c14000a608004 0x40a58280014c1000 0x45cc1c000f800000 0x08b9838001f00000

def z889 : W := mkw 0x41bfb0422a730134 0x8837f608454e6026 0xfffffec63fffc7ff 0xffffffd8c7fff8ff

def z890 : W := mkw 0xa5bff4084f7f9c8f 0xf4b7fe8109eff391 0xfdfffc003fffbc9f 0xffbfff8007fff793

def z891 : W := mkw 0x05bbb00003370005 0xc0b776000066e000 0x61ffdc0003b60004 0x0c3ffb800076c000

def z892 : W := mkw 0x857d37054af3e8c4 0xd0afa6e0a95e7d18 0x883c3f07c071f8e1 0x510787e0f80e3f1c

def z893 : W := mkw 0x00d3ab57b0000000 0x001a756af6000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z894 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x6ffc03f80ff07f06 0x0dff807f01fe0fe0

def z895 : W := mkw 0x07fbbbf7b3370005 0xc0ff777ef666e000 0xf3fffffff3ff8007 0xfe7ffffffe7ff000

def z896 : W := mkw 0x4011204220130130 0x8802240844026026 0xfa3f23fe307fc7ff 0xff47e47fc60ff8ff

def z897 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xf5fffc000fff80fe 0x3ebfff8001fff01f

def z898 : W := mkw 0xa5bff4004f7f888f 0xd4b7fe8009eff111 0xf5fffc000fff809e 0x3ebfff8001fff013

def z899 : W := mkw 0x45bbb04223370135 0xc8b776084466e026 0xfbfffec633ffc7ff 0xff7fffd8c67ff8ff

def z900 : W := mkw 0x8082c005458c68c3 0x10105800a8b18d18 0x7dc3c007cf8e78e7 0x2fb87800f9f1cf1c

def z901 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000000c79ff9e 0x01800000018f3ff3

def z902 : W := mkw 0xa1eecfbddfecfecf 0x343dd9f7bbfd9fd9 0x45ccdd39cf803800 0x08b99ba739f00700

def z903 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x7dcfde060f8e40e7 0x6fb9fbc0c1f1c81c

def z904 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0064065 0xfe7ffffffe00c80c

def z905 : W := mkw 0xe015644a6ddffdfb 0xbc02ac894dbbffbf 0xbe3322c63fffffff 0xf7c66458c7ffffff

def z906 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0xf3fcdffff0000001 0xde7f9bfffe000000

def z907 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xf3fffffff0000719 0xfe7ffffffe0000e3

def z908 : W := mkw 0x03680bf7b0000000 0x006d017ef6000000 0xf3fcfffff0000001 0xfe7f9ffffe000000

def z909 : W := mkw 0x05bbf400073f8007 0xc0b77e8000e7f000 0x75f3fc000fbf8006 0x2ebe7f8001f7f000

def z910 : W := mkw 0x00c2830500806000 0x00185060a0100c00 0x7dc3c307cf8e78e7 0x6fb87860f9f1cf1c

def z911 : W := mkw 0x804447054cc8e8c2 0x100888e0a9991d18 0xdc0cff07cc49f8e3 0x7b819fe0f9893f1c

def z912 : W := mkw 0x03bbb857b0000000 0x0077770af6000000 0xf1fffd3ff0000001 0xfe3fffa7fe000000

def z913 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xc3fffdfff0000001 0xb87fffbffe000000

def z914 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff0060061 0xfe7ffffffe00c00c

def z915 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfe3ffffffc7fffff 0xffc7ffffff8fffff

def z916 : W := mkw 0xe40444084f7f9dbf 0xfc80888109eff3b7 0x0c0000000ffffffe 0x0180000001ffffff

def z917 : W := mkw 0x4011204220130130 0x8802240844026026 0x2a3322c6307fc7ff 0x25466458c60ff8ff

def z918 : W := mkw 0x0128081090000000 0x0025010212000000 0xf1fcfd39f0000001 0xfe3f9fa73e000000

def z919 : W := mkw 0xe00444084c5b9dba 0xbc008881098b73b7 0x0c0000000c4fbcfa 0x018000000189f79f

def z920 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x75c3c307cf867865 0x6eb87860f9f0cf0c

def z921 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xfdfffc003fffc7ff 0xffbfff8007fff8ff

def z922 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffec63fffc367 0xfeffffd8c7fff86c

def z923 : W := mkw 0xe493fc52f51f89bb 0xdc927f8a5ea3f137 0x0003fc07f00f80f9 0x20007f80fe01f01f

def z924 : W := mkw 0xa00444084cc8fcca 0x3400888109991f99 0x0c0000000c49fcfa 0x0180000001893f9f

def z925 : W := mkw 0xa0400b1dd0807cc8 0x34080163ba100f99 0x0800033fc00078e1 0x41000067f8000f1c

def z926 : W := mkw 0x05bff4050f7f8007 0xc0b7fe80a1eff000 0xf5fffc07cfff8007 0x3ebfff80f9fff000

def z927 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x45cfdc000f8e0000 0x28b9fb8001f1c000

def z928 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff00e0007 0xfe7ffffffe01c000

def z929 : W := mkw 0x85bff4054f7f88c7 0xd0b7fe80a9eff118 0xfdfffe07cfffc0e7 0x7fbfffc0f9fff81c

def z930 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x440cfd39fc01b818 0x08819fa73f803703

def z931 : W := mkw 0x45bff44a2f7f9537 0xe8b7fe8945eff2a6 0xfffffffe3fffffff 0xffffffffc7ffffff

def z932 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xc3fcfdf9f0718718 0x987f9fbf3e0e30e3

def z933 : W := mkw 0x4011204220130130 0x8802240844026026 0xfa33e3c7f07fc7ff 0xff467c78fe0ff8ff

def z934 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x040000000c49b802 0x0080000001893700

def z935 : W := mkw 0x004003a800807600 0x2008007500100ec0 0xfff003f80ff07f06 0xdffe007f01fe0fe0

def z936 : W := mkw 0x4011204220130130 0x8802240844026026 0x2a3302c6307fc7ff 0xc5466058c60ff8ff

def z937 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0x75cfdc000fff8006 0x2eb9fb8001fff000

def z938 : W := mkw 0x05bff4080f7f9607 0xe0b7fe8101eff2c0 0xf5fffc000fff8706 0x3ebfff8001fff0e0

def z939 : W := mkw 0xa5bff4084f7f9c8f 0xf4b7fe8109eff391 0xfdfffd380fffbc9e 0xffbfffa701fff793

def z940 : W := mkw 0x03793bf7b0000000 0x006f277ef6000000 0xd23cfffff0000001 0xfa479ffffe000000

def z941 : W := mkw 0x00400b1090000000 0x0008016212000000 0xf1ccff39f0000001 0xfe399fe73e000000

def z942 : W := mkw 0x05aa900003240005 0x40b5520000648000 0x41ccdc0003800000 0x08399b8000700000

def z943 : W := mkw 0x80c2c3a5458c6ac3 0x10185874a8b18d58 0x7fc3c3c7cf8e7be7 0x6ff87878f9f1cf7c

def z944 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0700007 0xfe7ffffffe0e0000

def z945 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffec03fffc71e 0xffffffd807fff8e3

def z946 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfc0ffd39fc4fbc9f 0xff81ffa73f89f793

def z947 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x51ccdd39c0000001 0x6a399ba738000000

def z948 : W := mkw 0x43fbb3e722b36334 0x887f767ce4566c66 0x23f302c603b64364 0x047e6058c076c86c

def z949 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfc3cfd39fc79bc9f 0xff879fa73f8f3793

def z950 : W := mkw 0xa0400bbdd0807ec8 0x34080177ba100fd9 0x0a0003fff0007ff9 0xc140007ffe000fff

def z951 : W := mkw 0x03bbb8f7b0000000 0x0077771ef6000000 0xb23ffefff0000001 0xf647ffdffe000000

def z952 : W := mkw 0x05bbf000073f0007 0xc0b77e0000e7e000 0xf5fffc000fbe0006 0x3ebfff8001f7c000

def z953 : W := mkw 0x01bbb00001040001 0x0037760000208000 0xf1fffc0003860004 0x3e3fff800070c000

def z954 : W := mkw 0x0093b81090000000 0x0012770212000000 0xd00ffd39f0000001 0xfa01ffa73e000000

def z955 : W := mkw 0x01bbb00000000000 0x0037760000000000 0xf5fffc000f800006 0x3ebfff8001f00000

def z956 : W := mkw 0x0497f4000f7f8007 0xc092fe8001eff000 0x75c3fc000fff8006 0x2eb87f8001fff000

def z957 : W := mkw 0x840444084ffffec7 0xf080888109ffffd8 0x0c0000000fffffe6 0x0180000001fffffc

def z958 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf5fffc060fff8066 0x3ebfff80c1fff00c

def z959 : W := mkw 0x0000081090000000 0x0000010212000000 0xd80cfd39f0080083 0xfb019fa73e010010

def z960 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc03f80ff87f87 0xffff807f01ff0ff0

def z961 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff0764767 0xff7ffffffe0ec8ec

def z962 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff03647fd 0xff7ffffffe06c8ff

def z963 : W := mkw 0x42512bf7b0130130 0x884a257ef6026026 0xfa3ffffff07fc7ff 0xff47fffffe0ff8ff

def z964 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xd40cfd39fc09b899 0xfa819fa73f813713

def z965 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x9c0020000c49bc9a 0x3380040001893793

def z966 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff00fc7f9 0xff7ffffffe01f8ff

def z967 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x6dc3c307cf8e78e6 0x0db87860f9f1cf1c

def z968 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x73ffdfffc0000001 0x6e7ffbfff8000000

def z969 : W := mkw 0x43fbb3e721976171 0x887f767ce432ec2e 0x23f302c603b64364 0x047e6058c076c86c

def z970 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0418419 0xfe7ffffffe083083

def z971 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xde0cfff9fc49ff9b 0xfbc19fff3f893ff3

def z972 : W := mkw 0xa40444084ffffccf 0xf480888109ffff99 0x0c0000000ffffcfe 0x0180000001ffff9f

def z973 : W := mkw 0xa0400b15d08068c8 0x14080162ba100d19 0x08000307f00078f9 0x41000060fe000f1f

def z974 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffc000fff849e 0x3fbfff8001fff093

def z975 : W := mkw 0x00c28b1590000000 0x00185162b2000000 0xd1ccfd39f0000001 0xfa399fa73e000000

def z976 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffcc03fffc7fe 0xbfffff9807fff8ff

def z977 : W := mkw 0x012c00080a601404 0x20258001014c0280 0xfffc03f80ff07f06 0xdfff807f01fe0fe0

def z978 : W := mkw 0x0000081090000000 0x0000010212000000 0x500cdd39c0000001 0x6a019ba738000000

def z979 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xf1fcdd39c0000000 0x1e3f9ba738000000

def z980 : W := mkw 0x053d34000a738004 0xc0a7a680014e7000 0xc5fc3c000ff18000 0x18bf878001fe3000

def z981 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffec63fff871f 0xfeffffd8c7fff0e3

def z982 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff07f80ff 0xfe7ffffffe0ff01f

def z983 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xfbfffffff07fc707 0xff7ffffffe0ff8e0

def z984 : W := mkw 0x03fbbbf7b3a46245 0x007f777ef6748c48 0xf3fffffff3b64365 0xfe7ffffffe76c86c

def z985 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xfbfffffff00e47ff 0xff7ffffffe01c8ff

def z986 : W := mkw 0x05bff4080f7f9407 0xe0b7fe8101eff280 0xfffffff80fffff06 0xffffffff01ffffe0

def z987 : W := mkw 0x4097e4422d5f8133 0x8812fc8845abf026 0xfffffec63fffc7ff 0xffffffd8c7fff8ff

def z988 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff03e43e7 0xff7ffffffe07c87c

def z989 : W := mkw 0x0293b857b0000000 0x0052770af6000000 0xf23ffffff0000001 0xfe47fffffe000000

def z990 : W := mkw 0xa00444084d4c9ccb 0x3400888109a99399 0x0c0000000c4fbcfa 0x018000000189f79f

def z991 : W := mkw 0x01fbb3a500000000 0x003f7674a0000000 0xf3ffffffc0000001 0xfe7ffffff8000000

def z992 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x75c3c307cf8e7866 0x2eb87860f9f1cf0c

def z993 : W := mkw 0x45bff4ea2f7f9737 0xe8b7fe9d45eff2e6 0xf7fffcf83fff871e 0xbeffff9f07fff0e3

def z994 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffec60fffc3e7 0x7fffffd8c1fff87c

def z995 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x41cfdd3fc0000000 0x0839fba7f8000000

def z996 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xc5fffc000fff8000 0x38bfff8001fff000

def z997 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc3c307cf867866 0x4fb87860f9f0cf0c

def z998 : W := mkw 0x016803a000806000 0x002d007400100c00 0xfffc03f80ff07f06 0xdfff807f01fe0fe0

def z999 : W := mkw 0x01bfb0000a730004 0x8037f600014e6000 0xf5fffc000fff8006 0x3ebfff8001fff000

def z1000 : W := mkw 0x01792bf2b0000000 0x002f257e56000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z1001 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfffffffffc003803 0xffffffffff800700

def z1002 : W := mkw 0x42512bffb0937730 0xa84a257ff6126ee6 0xba3323fff07fffff 0xf746647ffe0fffff

def z1003 : W := mkw 0x0482d400050c8003 0x40905a8000a19000 0x45c0dc000f800000 0x08b81b8001f00000

def z1004 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xffff03fe0ff67f66 0xdfffe07fc1fecfec

def z1005 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffcc63fff87ff 0xbeffff98c7fff0ff

def z1006 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0xf1fffd39f0000001 0xfe3fffa73e000000

def z1007 : W := mkw 0x84c2d705458ce8c3 0x50985ae0a8b19d18 0x7dc3df07cf8e78e7 0x6fb87be0f9f1cf1c

def z1008 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0700701 0xfe7ffffffe0e00e0

def z1009 : W := mkw 0x45aed4000f7f8137 0xc8b5da8001eff026 0x4dccdc000fffc7fe 0x09b99b8001fff8ff

def z1010 : W := mkw 0x05bbf400051f8003 0xc0b77e8000a3f000 0xf5fffc000f8f8006 0x3ebfff8001f1f000

def z1011 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x71cfff3ff0000001 0x6e39ffe7fe000000

def z1012 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x45ccdc000f8e0006 0x08b99b8001f1c000

def z1013 : W := mkw 0xa0400b1dd0807cc8 0x34080163ba100f99 0x00000139c0003800 0x0000002738000700

def z1014 : W := mkw 0xc5bff4476f7f89f7 0xd8b7fe88edeff13e 0xf5fffc07ffff80ff 0x3ebfff80fffff01f

def z1015 : W := mkw 0x0011281090130000 0x8002250212026000 0xf03ffd39f07f8007 0xfe07ffa73e0ff000

def z1016 : W := mkw 0x07fbbbf7b3240005 0x40ff777ef6648000 0xf3fffffff3800001 0xfe7ffffffe700000

def z1017 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff0300301 0xfe7ffffffe060060

def z1018 : W := mkw 0x03fbbbf7b0806000 0x007f777ef6100c00 0xffffffffff8e78e7 0xfffffffffff1cf1c

def z1019 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x63fcdff9c0000000 0x0c7f9bff38000000

def z1020 : W := mkw 0x01bff0000f6c0007 0x0037fe0001ed8000 0xf5fffc000ffe0006 0x3ebfff8001ffc000

def z1021 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x45ccfc000f898000 0x28b99f8001f13000

def z1022 : W := mkw 0x052c14000a608004 0x40a58280014c1000 0xf5fc1c000ff00006 0x1ebf838001fe0000

def z1023 : W := mkw 0x433d38faba731734 0xa867a71f574e62e6 0x823c3cf830718718 0x9047879f060e30e3

def z1024 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffe060fffc066 0x3ebfffc0c1fff80c

def z1025 : W := mkw 0x05bfb0000b770005 0xc0b7f600016ee000 0xf5fffc000ff60006 0x3ebfff8001fec000

def z1026 : W := mkw 0xc2400bf7f08069f0 0x1848017efe100d3e 0x0a0003fff0007ff9 0xc140007ffe000fff

def z1027 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xd9ccfd39f049849b 0xfb399fa73e093093

def z1028 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x75cfdc000f800000 0x2eb9fb8001f00000

def z1029 : W := mkw 0x02400bf7b0806040 0x0048017ef6100c08 0x020003fff0004061 0xc040007ffe00080c

def z1030 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0x45ccdc000f8f8000 0x08b99b8001f1f000

def z1031 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0xbe3002c00c79ff9e 0xd7c60058018f3ff3

def z1032 : W := mkw 0xa00444084fecfecf 0x3400888109fd9fd9 0x0c0000000ffffffe 0x0180000001ffffff

def z1033 : W := mkw 0x05bbf400073f8007 0xc0b77e8000e7f000 0x01c3fc00038f8000 0x20387f800071f000

def z1034 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xa3fffefff0000001 0xb47fffdffe000000

def z1035 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xa5ff3c000fff8006 0x14bfe78001fff000

def z1036 : W := mkw 0x0000081090000000 0x0000010212000000 0xd00cfd39c0000000 0x3a019fa738000000

def z1037 : W := mkw 0xa0c2c705458ce8cb 0x141858e0a8b19d19 0x7dc3c307cf8ff8ff 0x6fb87860f9f1ff1f

def z1038 : W := mkw 0x053d74000f7f8007 0xc0a7ae8001eff000 0xf5fc3c000fff8006 0x1ebf878001fff000

def z1039 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdf3c307cffe78e7 0x7fbe7860f9ffcf1c

def z1040 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xf5ffdc000ffe0006 0x3ebffb8001ffc000

def z1041 : W := mkw 0x0497f4000d5f8003 0xc092fe8001abf000 0xf5cffc000fcf8006 0x3eb9ff8001f9f000

def z1042 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xffff03f80ffe7f06 0xffffe07f01ffcfe0

def z1043 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x1c0000000c49bc9b 0x6380000001893793

def z1044 : W := mkw 0x016c03ad0ae07604 0x202d8075a15c0ec0 0xfffc03ffcff07f07 0xdfff807ff9fe0fe0

def z1045 : W := mkw 0xa0c6c70d4dccfccb 0x3418d8e1a9b99f99 0x2dc302060fcffcfe 0x05b86040c1f9ff9f

def z1046 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xf7fffec60fff8006 0x3effffd8c1fff000

def z1047 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x55ccdc000f880002 0x2ab99b8001f10000

def z1048 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfdfffc063fffc7ff 0x3fbfff80c7fff8ff

def z1049 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0x63ffdfffc0364364 0x0c7ffbfff806c86c

def z1050 : W := mkw 0x85bff4004f7f8887 0xd0b7fe8009eff110 0xfdfffc000fffb886 0x3fbfff8001fff710

def z1051 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffec63fffc3ff 0x3effffd8c7fff87f

def z1052 : W := mkw 0x0086c4000d4c8003 0x0010d88001a99000 0xfdcffe063fcfc4ff 0xffb9ffc0c7f9f89f

def z1053 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xd3fcfdf9f0000001 0xfa7f9fbf3e000000

def z1054 : W := mkw 0x07bff4472f7f8007 0xc0f7fe88e5eff000 0xf5fffc060fff8006 0x3ebfff80c1fff000

def z1055 : W := mkw 0x0282981590000000 0x00505302b2000000 0xd00cfd39f0000001 0xfa019fa73e000000

def z1056 : W := mkw 0xa0400b18d0807c88 0x340801631a100f91 0x08000339f0007c99 0xc10000673e000f93

def z1057 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x41ccdf3fc0000001 0x48399be7f8000000

def z1058 : W := mkw 0x0086c4000d4c8003 0x0010d88001a99000 0xd5ccfc000fc98002 0x3ab99f8001f93000

def z1059 : W := mkw 0x053d34000a738004 0xc0a7a680014e7000 0xa1fc3c0003f18004 0x143f8780007e3000

def z1060 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0x73cfdffff0000001 0xee79fbfffe000000

def z1061 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc003fff809f 0x3ebfff8007fff013

def z1062 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff0000499 0xff7ffffffe000093

def z1063 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0cff3ffc49fcfb 0xfb819fe7ff893f9f

def z1064 : W := mkw 0xe015644a6efbffbe 0xbc02ac894ddf7ff7 0xbe3322c63fffffff 0xf7c66458c7ffffff

def z1065 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xe5fffc000ff78004 0x1cbfff8001fef000

def z1066 : W := mkw 0x80c2c3a5458c68c3 0x10185874a8b18d18 0x7fc3c3ffcf8e78e7 0xeff8787ff9f1cf1c

def z1067 : W := mkw 0x0000081090000000 0x0000010212000000 0xd00cdd39c0000000 0xda019ba738000000

def z1068 : W := mkw 0x02400bf7b0806200 0x0048017ef6100c40 0x020003fff0004301 0xc040007ffe000860

def z1069 : W := mkw 0xc2512bf7f09369f0 0x984a257efe126d3e 0xba3323fff07fffff 0xf746647ffe0fffff

def z1070 : W := mkw 0x0000000000000000 0x0000000000000000 0xba3322c6307fc7ff 0xf7466458c60ff8ff

def z1071 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xc7fcfcc03ff18718 0x98ff9f9807fe30e3

def z1072 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x45ccfc000f818000 0x08b99f8001f03000

def z1073 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdc3e307cfcff8e7 0x7fb87c60f9f9ff1c

def z1074 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x9c0000000c49bc9a 0xd380000001893793

def z1075 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xf7fffcc03fff8006 0xbeffff9807fff000

def z1076 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0x41ccdd3ff0000001 0x08399ba7fe000000

def z1077 : W := mkw 0x40112852b0130130 0x8802250a56026026 0xd00ffd3ff00f80f9 0xfa01ffa7fe01f01f

def z1078 : W := mkw 0x016803a802a07604 0x202d007500540ec0 0x7ff003f80fb07f06 0xcffe007f01f60fe0

def z1079 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x880cfd39f049bc99 0xf1019fa73e093793

def z1080 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0xf5fffc000ff00006 0x3ebfff8001fe0000

def z1081 : W := mkw 0x01aec4000f6c8007 0x0035d88001ed9000 0xf5fffc000fff8006 0x3ebfff8001fff000

def z1082 : W := mkw 0xa00444084dccfccb 0x3400888109b99f99 0x040000000f803800 0x0080000001f00700

def z1083 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xa1fffc0003ff8004 0x343fff80007ff000

def z1084 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xc5fcfc000fff8006 0x18bf9f8001fff000

def z1085 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xf7fc03f80fb07b04 0xdeff807f01f60f60

def z1086 : W := mkw 0x0086c4000d4c8003 0x0010d88001a99000 0x45ccdc000f800000 0x08b99b8001f00000

def z1087 : W := mkw 0x07fbbbf7b1170001 0xc0ff777ef622e000 0xf3fffffff0060001 0xfe7ffffffe00c000

def z1088 : W := mkw 0xe015644a6c5b9dba 0xbc02ac894d8b73b7 0x0c0320063c4fbcfb 0x21806400c789f79f

def z1089 : W := mkw 0x25bff4080f7f940f 0xe4b7fe8101eff281 0xf5fffc000fff841e 0x3ebfff8001fff083

def z1090 : W := mkw 0x05bff4080f7f9407 0xe0b7fe8101eff280 0xfdfffc000fffbc06 0x3fbfff8001fff780

def z1091 : W := mkw 0x05bff4a80f7f9607 0xe0b7fe9501eff2c0 0xfffffdf80fffbf06 0xffffffbf01fff7e0

def z1092 : W := mkw 0xa082c818d50c1c8b 0x341059031aa18391 0x7dc3c139ff8e3c9f 0xefb878273ff1c793

def z1093 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7fc3c3c7cf8e7fe7 0xeff87878f9f1cffc

def z1094 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xfffffec00fffc7fe 0xffffffd801fff8ff

def z1095 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5ffdc000ff60006 0x1ebffb8001fec000

def z1096 : W := mkw 0x07ea9bb593240005 0x40fd5376b2648000 0x41ccdd39c3800000 0x08399ba738700000

def z1097 : W := mkw 0x01bbb81090130000 0x8037770212026000 0xf9fffd39f07f849f 0xff3fffa73e0ff093

def z1098 : W := mkw 0xa01564084c5b9c8a 0xb402ac81098b7391 0xbc3320000c7fbc9e 0x37866400018ff793

def z1099 : W := mkw 0xc0d3e347659f69f3 0x981a7c68ecb3ed3e 0xc7f0e1c1fff1bf18 0x98fe1c383ffe37e3

def z1100 : W := mkw 0x85bff4054f7f88c7 0xd0b7fe80a9eff118 0xf5fffc01cfff8006 0x3ebfff8039fff000

def z1101 : W := mkw 0x032818b090000000 0x0065031612000000 0x400cdd39c0000000 0x08019ba738000000

def z1102 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xfffffec63fffc707 0xffffffd8c7fff8e0

def z1103 : W := mkw 0x03ea9bb590806000 0x007d5376b2100c00 0x45ccdd39cf803800 0x08b99ba739f00700

def z1104 : W := mkw 0x0082c400050c8003 0x0010588000a19000 0x75c3fc000f8f8006 0x2eb87f8001f1f000

def z1105 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc000ff18000 0x3ebfff8001fe3000

def z1106 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0498003 0xfe7ffffffe093000

def z1107 : W := mkw 0x03bbb8f7b0000000 0x0077771ef6000000 0x000ffc3ff0000001 0x2001ff87fe000000

def z1108 : W := mkw 0x80c28305418468c1 0x10185060a8308d18 0x7dc30307cf8678e7 0x4fb86060f9f0cf1c

def z1109 : W := mkw 0x01680bb090000000 0x002d017612000000 0xf3fcdff9c0000000 0xde7f9bff38000000

def z1110 : W := mkw 0x01bbb852b0000000 0x0037770a56000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z1111 : W := mkw 0x012c04000a608004 0x00258080014c1000 0xf5fc3c000ff18006 0x1ebf878001fe3000

def z1112 : W := mkw 0x00c2830501846041 0x00185060a0308c08 0x7dc3c307cf867867 0x6fb87860f9f0cf0c

def z1113 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffe063fffc4ff 0xffbfffc0c7fff89f

def z1114 : W := mkw 0xa40444084d5f9c8b 0xf480888109abf391 0x0c0000000c4fbc9a 0x018000000189f793

def z1115 : W := mkw 0xe0400b5ff0807df8 0x3c08016bfe100fbf 0x0a0003fff0007ff9 0xc140007ffe000fff

def z1116 : W := mkw 0x45bbf442273f8137 0xc8b77e8844e7f026 0xbbf3fec633ffc7ff 0xf77e7fd8c67ff8ff

def z1117 : W := mkw 0x02400bfab0807600 0x2048017f56100ec0 0x0a0003f830007f00 0xc140007f06000fe0

def z1118 : W := mkw 0x0486c4000f7f8007 0xc090d88001eff000 0xf5cffc000fff8006 0x3eb9ff8001fff000

def z1119 : W := mkw 0x85bff4004f7f8887 0xd0b7fe8009eff110 0xfdfffd01ffffbc9f 0xffbfffa03ffff793

def z1120 : W := mkw 0xa2400bfff0807e88 0x3448017ffe100fd1 0x0a0003fff0007f99 0xc140007ffe000ff3

def z1121 : W := mkw 0x85aed4054f6c88c7 0x50b5da80a9ed9118 0x45cfdc07cf8e00e1 0x28b9fb80f9f1c01c

def z1122 : W := mkw 0x0000081090000000 0x0000010212000000 0x400cfd39f0000001 0x28019fa73e000000

def z1123 : W := mkw 0x41bbf042251f0133 0x88377e0844a3e026 0xfffffec63fffc7ff 0xffffffd8c7fff8ff

def z1124 : W := mkw 0x00400b1090806000 0x0008016212100c00 0xfdccff39ff807807 0xffb99fe73ff00f00

def z1125 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xd40cfd39fc41bc19 0xfa819fa73f883783

def z1126 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x71cfdd39c0000000 0x2e39fba738000000

def z1127 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x75ccdc000f800006 0x0eb99b8001f00000

def z1128 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0xf3fffff9c0000000 0xfe7fffff38000000

def z1129 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffec60fffc7fe 0x3fffffd8c1fff8ff

def z1130 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc23f83ff1ff1e 0xdfff847f07fe3fe3

def z1131 : W := mkw 0x05bfb4000b778005 0xc0b7f680016ef000 0xf5ff3c000ff78006 0x1ebfe78001fef000

def z1132 : W := mkw 0x03fbbbf7b0806000 0x007f777ef6100c00 0xfffffffffff07f07 0xfffffffffffe0fe0

def z1133 : W := mkw 0x47fbbbf7b3370135 0xc8ff777ef666e026 0xfbfffffff3ffc7ff 0xff7ffffffe7ff8ff

def z1134 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xfffffec63fff849f 0xffffffd8c7fff093

def z1135 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffec60fffc766 0xffffffd8c1fff8ec

def z1136 : W := mkw 0x016803a002a06204 0x002d007400540c40 0xfffc03f80fb07b06 0xdfff807f01f60f60

def z1137 : W := mkw 0x01ae90000a600004 0x0035d200014c0000 0x45ccdc000f800000 0x08b99b8001f00000

def z1138 : W := mkw 0x03fbbbf7b0806000 0x007f777ef6100c00 0xfbfffffff0007801 0xff7ffffffe000f00

def z1139 : W := mkw 0xa0400bb8d0807e88 0x340801771a100fd1 0x00000139c0003800 0x0000002738000700

def z1140 : W := mkw 0x82400bb5d08068c0 0x10480176ba100d18 0x00000139c0003800 0x0000002738000700

def z1141 : W := mkw 0x05bfb4000b778005 0xc0b7f680016ef000 0xb1ff3c0003ff8006 0x363fe780007ff000

def z1142 : W := mkw 0xa00444084cc8fe8a 0x3400888109991fd1 0x0c0000000c49ff9a 0x0180000001893ff3

def z1143 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffdf9f0000000 0xbe7fffbf3e000000

def z1144 : W := mkw 0x0293b857b0000000 0x0052770af6000000 0x400ffd3ff0000001 0x2801ffa7fe000000

def z1145 : W := mkw 0xe0512b5ff0937df8 0xbc0a256bfe126fbf 0xba3323fff07fffff 0xf746647ffe0fffff

def z1146 : W := mkw 0x01bbb00002200004 0x0037760000440000 0xf1fffc0003b00004 0x3e3fff8000760000

def z1147 : W := mkw 0xe004444a6c489dba 0x3c0088894d8913b7 0x0e0002c63c49fffb 0xc1c00058c7893fff

def z1148 : W := mkw 0x000444000c488002 0x0000888001891000 0xf5ccfc000fc98006 0x3eb99f8001f93000

def z1149 : W := mkw 0xa0044c18de689e8e 0x340089831bcd13d1 0xdc0cfd39fc79bf9b 0xfb819fa73f8f37f3

def z1150 : W := mkw 0x05bbf400073f8007 0xc0b77e8000e7f000 0xb1f3fc0003ff8006 0x363e7f80007ff000

def z1151 : W := mkw 0x03fbbbf7b1846041 0x007f777ef6308c08 0xf3fffffff3800001 0xfe7ffffffe700000

def z1152 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x3c0302060c4ffcff 0x67806040c189ff9f

def z1153 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xd40cfd39fc49bc1a 0xba819fa73f893783

def z1154 : W := mkw 0xe5bff4084f7f9dbf 0xfcb7fe8109eff3b7 0xfdfffc000ffffffe 0x3fbfff8001ffffff

def z1155 : W := mkw 0x05bbb00003240005 0x40b7760000648000 0xf1fffc0003800000 0x3e3fff8000700000

def z1156 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xf3fffffff00000f9 0xfe7ffffffe00001f

def z1157 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffc000fff8087 0x7fbfff8001fff010

def z1158 : W := mkw 0x85bff4004f7f88c7 0xd0b7fe8009eff118 0xf5fffc000fff80e6 0x3ebfff8001fff01c

def z1159 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0000000000498498 0x0000000000093093

def z1160 : W := mkw 0x01bbb81090000000 0x0037770212000000 0xf1fffd39c0000000 0x3e3fffa738000000

def z1161 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x25f3fc000fff8006 0x24be7f8001fff000

def z1162 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xf3fffffff00f8001 0xfe7ffffffe01f000

def z1163 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0020003c49bc9b 0x2180040007893793

def z1164 : W := mkw 0x43fbbbf7b2b36334 0x887f777ef6566c66 0xfbfffffff3ffc7ff 0xff7ffffffe7ff8ff

def z1165 : W := mkw 0x01bbf000051f0003 0x80377e0000a3e000 0xf5fffc000fff8006 0x3ebfff8001fff000

def z1166 : W := mkw 0xc5bff4476f7f89f7 0xd8b7fe88edeff13e 0xfffffec7ffffc7ff 0xffffffd8fffff8ff

def z1167 : W := mkw 0xe0512bfaf0937fb8 0xbc0a257f5e126ff7 0xba3323fff07fffff 0xf746647ffe0fffff

def z1168 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff071c7f9 0xff7ffffffe0e38ff

def z1169 : W := mkw 0xa40444084e7b9c8e 0xf480888109cf7391 0x0c0000000c79bc9a 0x01800000018f3793

def z1170 : W := mkw 0x4011204220130130 0x8802240844026026 0xa23322c6307fc7fd 0xb4466458c60ff8ff

def z1171 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0cfd39fc79ff9f 0xfb819fa73f8f3ff3

def z1172 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xfdfffe060fffc7ff 0x7fbfffc0c1fff8ff

def z1173 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xf3fffffff0718001 0xfe7ffffffe0e3000

def z1174 : W := mkw 0x00112852b0000000 0x0002250a56000000 0xd23cfdf9f0000001 0xfa479fbf3e000000

def z1175 : W := mkw 0x03fbbbf7b1040041 0x007f777ef6208008 0xf3fffffff0060061 0xfe7ffffffe00c00c

def z1176 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xc3fcfffff0000001 0xd87f9ffffe000000

def z1177 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xd1cffd3ff0000001 0xfa39ffa7fe000000

def z1178 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfff3e3c7ffffffff 0xfffe7c78ffffffff

def z1179 : W := mkw 0x02400bffb0807600 0x2048017ff6100ec0 0x020003fff0003801 0xc040007ffe000700

def z1180 : W := mkw 0x02400bbd90807600 0x20480177b2100ec0 0x0a0003f9c0007f00 0xc140007f38000fe0

def z1181 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x2dc30307cf8e78e7 0x45b86060f9f1cf1c

def z1182 : W := mkw 0x0493f400051f8003 0xc0927e8000a3f000 0x45c3fc000f8f8000 0x28b87f8001f1f000

def z1183 : W := mkw 0x012808b090000000 0x0025011612000000 0xd23cfdf9f0000001 0xfa479fbf3e000000

def z1184 : W := mkw 0x85aed4004f6c8887 0x50b5da8009ed9110 0x45ccdd01cf803800 0x08b99ba039f00700

def z1185 : W := mkw 0x4011204220130130 0x8802240844026026 0x8a3322c6307fc7f9 0xf1466458c60ff8ff

def z1186 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffd01cfff8007 0x7ebfffa039fff000

def z1187 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0xc5fcfc000f800000 0x18bf9f8001f00000

def z1188 : W := mkw 0xa00444084dccfccb 0x3400888109b99f99 0x0c0000000fc9bc9a 0x0180000001f93793

def z1189 : W := mkw 0x05bff4080f7f9407 0xe0b7fe8101eff280 0xf5fffd380fffb806 0x3ebfffa701fff700

def z1190 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fcfc000ff18006 0x1ebf9f8001fe3000

def z1191 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x75c3c307cf8e38e1 0x6eb87860f9f1c71c

def z1192 : W := mkw 0xa40444084f6c9c8f 0x7480888109ed9391 0x0c0000000fc9bc9a 0x0180000001f93793

def z1193 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xfbfffffff07047ff 0xff7ffffffe0e08ff

def z1194 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0x43ccdfffc0000000 0x08799bfff8000000

def z1195 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffec63fffc77e 0xbeffffd8c7fff8ef

def z1196 : W := mkw 0x00400bb890807600 0x2008017712100ec0 0x0a0003f9f0007f01 0xc140007f3e000fe0

def z1197 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xaffc02f80ff07f06 0x95ff805f01fe0fe0

def z1198 : W := mkw 0x0082881090000000 0x0010510212000000 0xf1cffd39f0000001 0xfe39ffa73e000000

def z1199 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x8c0020003c49bc9a 0x9180040007893793

def z1200 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x45c3c107cf863860 0x08b87820f9f0c70c

def z1201 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000000c003c98 0x0180000001800793

def z1202 : W := mkw 0x053d34000a738004 0xc0a7a680014e7000 0xf5ff3c000fff8006 0x3ebfe78001fff000

def z1203 : W := mkw 0x4493f442251f8133 0xc8927e8844a3f026 0x7dc3fe063f8fc0ff 0x6fb87fc0c7f1f81f

def z1204 : W := mkw 0xa12c0818da601c8c 0x342581031b4c0391 0xfdfc0139fff03c9f 0xdfbf80273ffe0793

def z1205 : W := mkw 0x20040c1898409408 0x2400818313081281 0xdc0cfd39fc41bc1b 0xfb819fa73f883783

def z1206 : W := mkw 0xa00444084dccfccb 0x3400888109b99f99 0xbc0322063fcffcff 0xf7806440c7f9ff9f

def z1207 : W := mkw 0x05bfb4000b778005 0xc0b7f680016ef000 0x21ff1c0003b60004 0x043fe3800076c000

def z1208 : W := mkw 0x01bbf000050c0003 0x00377e0000a18000 0xf5fffc000f800000 0x3ebfff8001f00000

def z1209 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xd5fcfc000ff98002 0x3abf9f8001ff3000

def z1210 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xffff23fe3fffffff 0xffffe47fc7ffffff

def z1211 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfdfffc063fff84ff 0xffbfff80c7fff09f

def z1212 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffcfff80ff07f06 0xffff9fff01fe0fe0

def z1213 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc3c307cfcffcff 0x6fb87860f9f9ff9f

def z1214 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffec63fff80ff 0xfeffffd8c7fff01f

def z1215 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc03f80ff9ff9e 0xdfff807f01ff3ff3

def z1216 : W := mkw 0x033938f2b0000000 0x0067271e56000000 0xc23cfdf9f0000000 0x98479fbf3e000000

def z1217 : W := mkw 0x82400bf7f08068c0 0x1048017efe100d18 0x020003fff0003801 0xc040007ffe000700

def z1218 : W := mkw 0x4011204220130130 0x8802240844026026 0xfa3ffec6307fc7ff 0xff47ffd8c60ff8ff

def z1219 : W := mkw 0x85bff4004f7f8887 0xd0b7fe8009eff110 0xf5fffc01cfff8087 0x3ebfff8039fff010

def z1220 : W := mkw 0x05bbf400073f8007 0xc0b77e8000e7f000 0x21f3dc0003b60004 0x043e7b800076c000

def z1221 : W := mkw 0x43fbbbf7b1976171 0x887f777ef632ec2e 0xf3fffffff3b64365 0xfe7ffffffe76c86c

def z1222 : W := mkw 0xa0400b1dd0807cc8 0x34080163ba100f99 0x08000139f0003c99 0xc10000273e000793

def z1223 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x4c0cfd39fc49bc9b 0x29819fa73f893793

def z1224 : W := mkw 0xa5bff4084f7f9c8f 0xf4b7fe8109eff391 0x2df300000fffbc9e 0x05be600001fff793

def z1225 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x43cffffff0000001 0xe879fffffe000000

def z1226 : W := mkw 0x4011204220130130 0x8802240844026026 0xfe3323c63c7fffff 0xffc66478c78fffff

def z1227 : W := mkw 0x05aed4a80f6c9607 0x60b5da9501ed92c0 0x45ccdc380f800000 0x08b99b8701f00000

def z1228 : W := mkw 0x0482d400050c8003 0x40905a8000a19000 0x75c3dc000f8e0006 0x2eb87b8001f1c000

def z1229 : W := mkw 0xe0400bfaf0807fb8 0x3c08017f5e100ff7 0x0a0003fff0007ff9 0xc140007ffe000fff

def z1230 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xffff03fe0ff07f07 0xffffe07fc1fe0fe0

def z1231 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffd000fffb806 0x7fbfffa001fff700

def z1232 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0xc1fcfd39c0000000 0x183f9fa738000000

def z1233 : W := mkw 0x052c44000f7f8007 0xc0a5888001eff000 0xf5fcfc000fff8006 0x3ebf9f8001fff000

def z1234 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xf5fcfc000ff98006 0x3ebf9f8001ff3000

def z1235 : W := mkw 0x413d64422e7b8136 0x8827ac8845cf7026 0xfffffec63fffc7ff 0xffffffd8c7fff8ff

def z1236 : W := mkw 0x02400bbd90807600 0x20480177b2100ec0 0x00000139c0003800 0x0000002738000700

def z1237 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff079c79f 0xff7ffffffe0f38f3

def z1238 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x47fc01f80fb03b00 0x08ff803f01f60760

def z1239 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x61cfdf3fc0000000 0x0c39fbe7f8000000

def z1240 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xc1ccfd39f0000000 0x98399fa73e000000

def z1241 : W := mkw 0xa00444084e689c8e 0x3400888109cd1391 0x0c0000000ff9bc9e 0x0180000001ff3793

def z1242 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x823ffffff0000001 0xf047fffffe000000

def z1243 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc3c307ff8e7cff 0xefb87860fff1cf9f

def z1244 : W := mkw 0x02400bf7b0000000 0x0048017ef6000000 0x420cdffff0000001 0xc8419bfffe000000

def z1245 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0xf5fcdc000fff8006 0x1ebf9b8001fff000

def z1246 : W := mkw 0xa0400bb8d0807e88 0x340801771a100fd1 0x08000139f0003c99 0xc10000273e000793

def z1247 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfffffec60fffc7e7 0xffffffd8c1fff8fc

def z1248 : W := mkw 0xe00444084ddffdfb 0xbc00888109bbffbf 0x0c0000000ffffffe 0x0180000001ffffff

def z1249 : W := mkw 0x01bfb0422a600004 0x0037f608454c0000 0xfffffec63ff04707 0xffffffd8c7fe08e0

def z1250 : W := mkw 0x03ea9bb592a06204 0x007d5376b2540c40 0x41ccdd39c3800000 0x08399ba738700000

def z1251 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfdcfff07cf8e78e7 0x7fb9ffe0f9f1cf1c

def z1252 : W := mkw 0x05bbb40003378005 0xc0b776800066f000 0x21f33c0003b78004 0x043e67800076f000

def z1253 : W := mkw 0x43ea9bf7b0000130 0x087d537ef6000026 0x4bccdffff00047f9 0xc9799bfffe0008ff

def z1254 : W := mkw 0x40112852b0130130 0x8802250a56026026 0xf23ffffff0364365 0xfe47fffffe06c86c

def z1255 : W := mkw 0x41bbb852b0130130 0x8837770a56026026 0xfbfffffff07fc7ff 0xff7ffffffe0ff8ff

def z1256 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfdfffe063fffc0ff 0x7fbfffc0c7fff81f

def z1257 : W := mkw 0x02512bffb0807600 0x204a257ff6100ec0 0xba3323fff0707f07 0xf746647ffe0e0fe0

def z1258 : W := mkw 0x45bfb4422b778135 0xc8b7f688456ef026 0xa3ff3ec633f7c77c 0x947fe7d8c67ef8ef

def z1259 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xe3fffffff0000000 0x9c7ffffffe000000

def z1260 : W := mkw 0x0097e4000d5f8003 0x8012fc8001abf000 0xf5fffc000fff8006 0x3ebfff8001fff000

def z1261 : W := mkw 0x4011204220130130 0x8802240844026026 0xfff322c63fffc7ff 0xfffe6458c7fff8ff

def z1262 : W := mkw 0xa00444084ee8fe8e 0x3400888109dd1fd1 0x040000000f803800 0x0080000001f00700

def z1263 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7ff3c3c7cfbe7be7 0x6ffe7878f9f7cf7c

def z1264 : W := mkw 0x05bff4080f7f9407 0xe0b7fe8101eff280 0xfdfffd383fffbc9f 0xffbfffa707fff793

def z1265 : W := mkw 0x0000081090000000 0x0000010212000000 0xd00cfd39f0418419 0xfa019fa73e083083

def z1266 : W := mkw 0x0493f400051f8003 0xc0927e8000a3f000 0x21c3fc00038f8004 0x24387f800071f000

def z1267 : W := mkw 0x07fbbbf7b3b76205 0xc0ff777ef676ec40 0xf3fffffff3b64305 0xfe7ffffffe76c860

def z1268 : W := mkw 0x00000852b0000000 0x0000010a56000000 0xd20cfffff0000001 0xfa419ffffe000000

def z1269 : W := mkw 0x03fbbbf7b2a06204 0x007f777ef6540c40 0xfbfffffff3f04707 0xff7ffffffe7e08e0

def z1270 : W := mkw 0x020008f2b0000000 0x0040011e56000000 0xd20cfdf9f0000001 0xfa419fbf3e000000

def z1271 : W := mkw 0x07fbbbf7b2330004 0xc0ff777ef6466000 0xf3fffffff0300001 0xfe7ffffffe060000

def z1272 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x4c0cfd39fc09bc99 0xe9819fa73f813793

def z1273 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x75c3c107cf8e38e7 0x2eb87820f9f1c71c

def z1274 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x71ccdf39c0000000 0x4e399be738000000

def z1275 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xc3fcddf9c0000000 0x987f9bbf38000000

def z1276 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0x41cffd3ff00f80f9 0x2839ffa7fe01f01f

def z1277 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xcffc01f80ff07f06 0x99ff803f01fe0fe0

def z1278 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x45fcdc000fb00000 0x08bf9b8001f60000

def z1279 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0x41cffd39c0000000 0x2839ffa738000000

def z1280 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000003c49bc9b 0xc180000007893793

def z1281 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000000c083882 0x0180000001810710

def z1282 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff00040e1 0xff7ffffffe00081c

def z1283 : W := mkw 0x01fbbbb090000000 0x003f777612000000 0xf3fffff9f0000001 0xfe7fffff3e000000

def z1284 : W := mkw 0xa16c47a84ee8fe8e 0x342d88f509dd1fd1 0x2ff002c00ff9ff9e 0x05fe005801ff3ff3

def z1285 : W := mkw 0x00400bb090000000 0x0008017612000000 0xd20cfff9f0000001 0xfa419fff3e000000

def z1286 : W := mkw 0xa5aed4084f6c9c8f 0x74b5da8109ed9391 0x4dccdc000fc9bc9a 0x09b99b8001f93793

def z1287 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0x67ffdec60fb64364 0x0cfffbd8c1f6c86c

def z1288 : W := mkw 0xa0044c18dd4c9ccb 0x340089831ba99399 0xdc0cfd39fc4fbcfb 0xfb819fa73f89f79f

def z1289 : W := mkw 0x03fbbbf7b1846041 0x007f777ef6308c08 0xffffffffff867867 0xfffffffffff0cf0c

def z1290 : W := mkw 0x43fbbbf7b0000130 0x087f777ef6000026 0xfbfffffff049c7fb 0xff7ffffffe0938ff

def z1291 : W := mkw 0xa0400bb8d0807e88 0x340801771a100fd1 0x0a0003f9c0007f00 0xc140007f38000fe0

def z1292 : W := mkw 0x02113852b0000000 0x0042270a56000000 0xd00cfd39f0000001 0xfa019fa73e000000

def z1293 : W := mkw 0xa0044c18de689c8e 0x340089831bcd1391 0xdc0cfd39fff9bc9f 0xfb819fa73fff3793

def z1294 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0x75cffc000f8f8006 0x2eb9ff8001f1f000

def z1295 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff0080083 0xff7ffffffe010010

def z1296 : W := mkw 0xa40444084f7f9c8f 0xf480888109eff391 0x040000000fffb806 0x0080000001fff700

def z1297 : W := mkw 0x02400bb590000000 0x00480176b2000000 0x400cdd39c0000000 0x08019ba738000000

def z1298 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xf3fcfff9f0000001 0xfe7f9fff3e000000

def z1299 : W := mkw 0x4493f442251f8133 0xc8927e8844a3f026 0xfff3fec63fffc7ff 0xfffe7fd8c7fff8ff

def z1300 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff04f84fb 0xff7ffffffe09f09f

def z1301 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x65fcdc000fb00004 0x0cbf9b8001f60000

def z1302 : W := mkw 0x05aed4a80f6c9607 0x60b5da9501ed92c0 0xc7fcdcf80ff00700 0x98ff9b9f01fe00e0

def z1303 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff079879b 0xff7ffffffe0f30f3

def z1304 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffd380fff8006 0xfebfffa701fff000

def z1305 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x65c3c307cf8e78e5 0x2cb87860f9f1cf1c

def z1306 : W := mkw 0xe00444084efbffbe 0xbc00888109df7ff7 0x0c0000000ffffffe 0x0180000001ffffff

def z1307 : W := mkw 0x05bff4422f7f8007 0xc0b7fe8845eff000 0xf5fffc063fff8007 0x3ebfff80c7fff000

def z1308 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff0004007 0xff7ffffffe000800

def z1309 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfc0cff39fc49fc9f 0xff819fe73f893f93

def z1310 : W := mkw 0x0000081090000000 0x0000010212000000 0xf80fff3ff00e40e7 0xff01ffe7fe01c81c

def z1311 : W := mkw 0x05bff4a80f7f9607 0xe0b7fe9501eff2c0 0xfffffef80fffc706 0xffffffdf01fff8e0

def z1312 : W := mkw 0x03fbbbf7b0806000 0x007f777ef6100c00 0xf7ffffffff803801 0xfefffffffff00700

def z1313 : W := mkw 0x0000081090000000 0x0000010212000000 0xf23cfff9f0000001 0xfe479fff3e000000

def z1314 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf7fffcc00fff8306 0x3effff9801fff060

def z1315 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x6dc3c307cf8678e5 0x4db87860f9f0cf1c

def z1316 : W := mkw 0xa2400bfff0807cc8 0x3448017ffe100f99 0x0a0003fff0007cf9 0xc140007ffe000f9f

def z1317 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0x45ccdc000ff00006 0x08b99b8001fe0000

def z1318 : W := mkw 0x03fbbbf7b0806040 0x007f777ef6100c08 0xf3fffffff0004061 0xfe7ffffffe00080c

def z1319 : W := mkw 0xa04447084cc8fc8a 0x340888e109991f91 0x7dc003000fc9fc9e 0x4fb8006001f93f93

def z1320 : W := mkw 0x03fbbbf7b2200204 0x007f777ef6440040 0xf3fffffff0300301 0xfe7ffffffe060060

def z1321 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x7dc3c307cffe7fe7 0x6fb87860f9ffcffc

def z1322 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xde3cfdf9fc79bf9b 0xfbc79fbf3f8f37f3

def z1323 : W := mkw 0x8040430044886882 0x1008086008910d10 0x7dc3c307cf8e78e7 0x6fb87860f9f1cf1c

def z1324 : W := mkw 0x012c44000e688006 0x0025888001cd1000 0xd5ccfc000fc98002 0x3ab99f8001f93000

def z1325 : W := mkw 0xe015644a6c5b9dba 0xbc02ac894d8b73b7 0x8e3020c03c79bf9a 0x91c60418078f37f3

def z1326 : W := mkw 0x01680bb090000000 0x002d017612000000 0x41ccdd39c0000000 0x08399ba738000000

def z1327 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffc000fffc0e6 0x3fbfff8001fff81c

def z1328 : W := mkw 0x01aad000050c0003 0x00355a0000a18000 0x75cfdc000f8e0006 0x2eb9fb8001f1c000

def z1329 : W := mkw 0xa0044c18dd4c9c8b 0x340089831ba99391 0xdc0cfd39ffcfbc9f 0xfb819fa73ff9f793

def z1330 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff071c71f 0xff7ffffffe0e38e3

def z1331 : W := mkw 0x07bff4e22f7f8007 0xc0f7fe9c45eff000 0xf7fffcc00fff8006 0x3effff9801fff000

def z1332 : W := mkw 0x02d3bbf7b0000000 0x005a777ef6000000 0xd20ffffff0000001 0xfa41fffffe000000

def z1333 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xc5ccfc000fc18000 0x18b99f8001f83000

def z1334 : W := mkw 0x02d3bb57b0000000 0x005a776af6000000 0xf1cfff3ff0000001 0xfe39ffe7fe000000

def z1335 : W := mkw 0xa00444084ee8fe8e 0x3400888109dd1fd1 0xbe3022c03ff9ff9f 0xf7c6045807ff3ff3

def z1336 : W := mkw 0x00c28b1590000000 0x00185162b2000000 0x71cfdf3fc0000001 0x6e39fbe7f8000000

def z1337 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x0c0000000c403c02 0x0180000001880780

def z1338 : W := mkw 0x03bbb8f7b0000000 0x0077771ef6000000 0xf3fffcfff0000001 0xbe7fff9ffe000000

def z1339 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0cfd39fc41bc1a 0xdb819fa73f883783

def z1340 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc23f80ff9ff06 0xffff847f01ff3fe0

def z1341 : W := mkw 0x03fbbbf7b0806200 0x007f777ef6100c40 0xf3fffffff0004301 0xfe7ffffffe000860

def z1342 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xf5fcdc000f800000 0x1ebf9b8001f00000

def z1343 : W := mkw 0xa015644a6c489c8a 0x3402ac894d891391 0xbe3322c63c49bc9b 0xf7c66458c7893793

def z1344 : W := mkw 0x45bbb04223370135 0xc8b776084466e026 0xf3fffec633b64365 0xfe7fffd8c676c86c

def z1345 : W := mkw 0x20400bb890807608 0x2408017712100ec1 0x0a0003f830007f18 0xc140007f06000fe3

def z1346 : W := mkw 0x00400b1590000000 0x00080162b2000000 0xd00cff3ff0000001 0xfa019fe7fe000000

def z1347 : W := mkw 0x40d3ab57b0130130 0x881a756af6026026 0xfbfffffff07fc7ff 0xff7ffffffe0ff8ff

def z1348 : W := mkw 0x012c00a80a601604 0x20258015014c02c0 0xfffc01f80ff03f06 0xdfff803f01fe07e0

def z1349 : W := mkw 0x053d74000e7b8006 0xc0a7ae8001cf7000 0xf5fcfc000ff98006 0x3ebf9f8001ff3000

def z1350 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc03f83ff07f9f 0xdfff807f07fe0ff3

def z1351 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xfffc03f80ffe7fe6 0xdfff807f01ffcffc

def z1352 : W := mkw 0xa00444084c489c8a 0x3400888109891391 0x5c0001000c49bc9a 0x4b80002001893793

def z1353 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xfbfffffff00fc0ff 0xff7ffffffe01f81f

def z1354 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfc0fff3ffc49bc9b 0xff81ffe7ff893793

def z1355 : W := mkw 0x05aed4000f6c8007 0x40b5da8001ed9000 0xd5ccdc000fc00002 0x1ab99b8001f80000

def z1356 : W := mkw 0x00c28b1590000000 0x00185162b2000000 0xf9cfff3ff04fc4ff 0xff39ffe7fe09f89f

def z1357 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0xd5ccfc000fff8006 0x3ab99f8001fff000

def z1358 : W := mkw 0x4293b857b0130130 0x8852770af6026026 0xfa3ffffff07fc7ff 0xff47fffffe0ff8ff

def z1359 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xdc0cfd39fc4ffcff 0xfb819fa73f89ff9f

def z1360 : W := mkw 0x013d30000a600004 0x0027a600014c0000 0xf5fc3c000ff00006 0x1ebf878001fe0000

def z1361 : W := mkw 0x0000081090000000 0x0000010212000000 0xd00cfd39f0098099 0xfa019fa73e013013

def z1362 : W := mkw 0xa0040c18d8409c88 0x340081831b081391 0xd80cfd39f041bc99 0xfb019fa73e083793

def z1363 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xdffc01f80ff03f02 0xdbff803f01fe07e0

def z1364 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xfbfcdff9c0704706 0xdf7f9bff380e08e0

def z1365 : W := mkw 0x032818b090000000 0x0065031612000000 0xd00cfd39f0000001 0xfa019fa73e000000

def z1366 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff0004701 0xff7ffffffe0008e0

def z1367 : W := mkw 0x40000852b0000130 0x0800010a56000026 0xda0cfffff00047f9 0xfb419ffffe0008ff

def z1368 : W := mkw 0x85aed4004f6c8887 0x50b5da8009ed9110 0x5dccdd01cf883883 0x6bb99ba039f10710

def z1369 : W := mkw 0x0493f400051f8003 0xc0927e8000a3f000 0xf5f3fc000fff8006 0x3ebe7f8001fff000

def z1370 : W := mkw 0x00c28b1590000000 0x00185162b2000000 0x41ccdd39c0000000 0x08399ba738000000

def z1371 : W := mkw 0x03fbbbf7b0130000 0x807f777ef6026000 0xfbfffffff07f849f 0xff7ffffffe0ff093

def z1372 : W := mkw 0x01ea8bb590000000 0x003d5176b2000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z1373 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff0018019 0xfe7ffffffe003003

def z1374 : W := mkw 0x03ea9bb590806000 0x007d5376b2100c00 0x7dccdf39cf807806 0x4fb99be739f00f00

def z1375 : W := mkw 0x45bff4ea2f7f9737 0xe8b7fe9d45eff2e6 0xfffffefe3fffc7ff 0xffffffdfc7fff8ff

def z1376 : W := mkw 0xa00444084ee8fe8e 0x3400888109dd1fd1 0x0c0000000ff07f06 0x0180000001fe0fe0

def z1377 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fcfff9f0000000 0xde7f9fff3e000000

def z1378 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x5dc3c107cf8e38e3 0x6bb87820f9f1c71c

def z1379 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff07f87f9 0xfe7ffffffe0ff0ff

def z1380 : W := mkw 0xa0400bb8d0807e88 0x340801771a100fd1 0xba3023f9f079ff9f 0xf746047f3e0f3ff3

def z1381 : W := mkw 0x02000857b0000000 0x0040010af6000000 0xd00cfd3ff0000001 0xfa019fa7fe000000

def z1382 : W := mkw 0x0139381090000000 0x0027270212000000 0xd03cfd39f0000001 0xfa079fa73e000000

def z1383 : W := mkw 0x033938f2b0000000 0x0067271e56000000 0xf23ffffff0000001 0xfe47fffffe000000

def z1384 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff04fc4ff 0xff7ffffffe09f89f

def z1385 : W := mkw 0x0000081090000000 0x0000010212000000 0xfa3cfff9f0704707 0xff479fff3e0e08e0

def z1386 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf7fffec00fffc306 0x3effffd801fff860

def z1387 : W := mkw 0x05bff4000f6c8007 0x40b7fe8001ed9000 0xf5fffc000fc98002 0x3ebfff8001f93000

def z1388 : W := mkw 0x01fbbb1590000000 0x003f7762b2000000 0xf1ffff3ff0000001 0xfe3fffe7fe000000

def z1389 : W := mkw 0x85bff4084f7f9c87 0xf0b7fe8109eff390 0xfdfffd39cfffbc87 0xffbfffa739fff790

def z1390 : W := mkw 0x453d34422a738134 0xc8a7a688454e7026 0xffff3ec63fffc7ff 0xffffe7d8c7fff8ff

def z1391 : W := mkw 0x85bff4004f7f8887 0xd0b7fe8009eff110 0xfdffff07cffff8e7 0x7fbfffe0f9ffff1c

def z1392 : W := mkw 0x0000081090000000 0x0000010212000000 0xdc0cfd39fc003803 0xfb819fa73f800700

def z1393 : W := mkw 0x02c28bf7b0000000 0x0058517ef6000000 0xf3cffffff0000001 0xfe79fffffe000000

def z1394 : W := mkw 0x03fbbbb590000000 0x007f7776b2000000 0xf1ffff3fc0000001 0x7e3fffe7f8000000

def z1395 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x4dc3c107cf8e78e7 0x29b87820f9f1cf1c

def z1396 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0xf7fc01f80ff03f06 0x9eff803f01fe07e0

def z1397 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0098099 0xfe7ffffffe013013

def z1398 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc003fff841e 0xbebfff8007fff083

def z1399 : W := mkw 0x05bff4a00f7f8007 0xc0b7fe9401eff000 0xf7fffcf80fff8006 0xbeffff9f01fff000

def z1400 : W := mkw 0x85aed4054f6c88c7 0x50b5da80a9ed9118 0x45ccdc01cf800000 0x08b99b8039f00000

def z1401 : W := mkw 0x01bff4000d4c8003 0x0037fe8001a99000 0xf5fffc000fcf8006 0x3ebfff8001f9f000

def z1402 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xf1cfff3ff0000001 0xfe39ffe7fe000000

def z1403 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0x4dc3c307cf8e78e1 0x69b87860f9f1cf1c

def z1404 : W := mkw 0x012c00a80ae07604 0x20258015015c0ec0 0xfffc00f80ff07f06 0x9fff801f01fe0fe0

def z1405 : W := mkw 0x0293b857b0000000 0x0052770af6000000 0x800ffc3ff0000001 0xb001ff87fe000000

def z1406 : W := mkw 0x82400bfff0807ec0 0x3048017ffe100fd8 0x0a0003fff0007fe1 0xc140007ffe000ffc

def z1407 : W := mkw 0x05bbb81093370005 0xc0b777021266e000 0xf1fffd39f3b60005 0xfe3fffa73e76c000

def z1408 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xc40cfd39fc49bc99 0xb8819fa73f893793

def z1409 : W := mkw 0x0004081898401400 0x2000810313080280 0xdc0cfd39fc49bc9b 0xfb819fa73f893793

def z1410 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0x45ccdc000ff18000 0x08b99b8001fe3000

def z1411 : W := mkw 0x03fbbbf7b2a06204 0x007f777ef6540c40 0xffffffffffb07b07 0xfffffffffff60f60

def z1412 : W := mkw 0x05bff4050f7f8047 0xc0b7fe80a1eff008 0xf5fffc060fff8066 0x3ebfff80c1fff00c

def z1413 : W := mkw 0x4000081090130130 0x8800010212026026 0xd80cfd39f07fc7ff 0xfb019fa73e0ff8ff

def z1414 : W := mkw 0x05aed4000f7f8007 0xc0b5da8001eff000 0x45ccdc000fb60004 0x08b99b8001f6c000

def z1415 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf1fffd3ff0000001 0x3e3fffa7fe000000

def z1416 : W := mkw 0x05bfb4000a738004 0xc0b7f680014e7000 0xf5fffc000ff18006 0x3ebfff8001fe3000

def z1417 : W := mkw 0x012c44000e688006 0x0025888001cd1000 0x45ccdc000f800000 0x08b99b8001f00000

def z1418 : W := mkw 0x00112852b0000000 0x0002250a56000000 0xd00ffd3ff0000001 0xfa01ffa7fe000000

def z1419 : W := mkw 0x0000081090000000 0x0000010212000000 0xd00cfd39f0498003 0xfa019fa73e093000

def z1420 : W := mkw 0x80c2c305458c68c3 0x10185860a8b18d18 0xfff3c3c7cf8e78e7 0xfffe7878f9f1cf1c

def z1421 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf7fffec00fff8006 0xfeffffd801fff000

def z1422 : W := mkw 0x82400b57f08068c0 0x1048016afe100d18 0x08000307f00078e1 0x41000060fe000f1c

def z1423 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xfbfffffff07e47e7 0xff7ffffffe0fc8fc

def z1424 : W := mkw 0x0044030808c07400 0x2008806101180e80 0xfffc03f80ff07f06 0xdfff807f01fe0fe0

def z1425 : W := mkw 0x0086c4000d4c8003 0x0010d88001a99000 0x75cfdc000f8e0006 0x2eb9fb8001f1c000

def z1426 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfdfffe000fffc006 0x7fbfffc001fff800

def z1427 : W := mkw 0x43bbb8f7b0130130 0x8877771ef6026026 0xba3ffefff07fc7ff 0xf747ffdffe0ff8ff

def z1428 : W := mkw 0x43fbbbf7b0130130 0x887f777ef6026026 0xf3fffffff03fc3fd 0xfe7ffffffe07f87f

def z1429 : W := mkw 0xe00444084c5b9dba 0xbc008881098b73b7 0x0c0000000c79bf9a 0x01800000018f37f3

def z1430 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0xfe3cfff9fc49bc9b 0xffc79fff3f893793

def z1431 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf5fffc060fff80e7 0x3ebfff80c1fff01c

def z1432 : W := mkw 0x433938f2b0130130 0x8867271e56026026 0xda3cfdf9f079879b 0xfb479fbf3e0f30f3

def z1433 : W := mkw 0x03fbbbf7b2a06204 0x007f777ef6540c40 0xf3fffffff3800001 0xfe7ffffffe700000

def z1434 : W := mkw 0x0093f000050c0003 0x00127e0000a18000 0x75c3fc000f8e0006 0x2eb87f8001f1c000

def z1435 : W := mkw 0x03aa98b590000000 0x00755316b2000000 0x000cdc39c0000000 0x00019b8738000000

def z1436 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x41ccfd39f0000001 0x28399fa73e000000

def z1437 : W := mkw 0x8082c005450c08c3 0x10105800a8a18118 0x7dc3c107cf8e38e7 0x6fb87820f9f1c71c

def z1438 : W := mkw 0xa00444084ee8fe8e 0x3400888109dd1fd1 0x0c0000000fc9bc9a 0x0180000001f93793

def z1439 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0xf3ffdfffc0000001 0xfe7ffbfff8000000

def z1440 : W := mkw 0x84d3f705459fe8c3 0xd09a7ee0a8b3fd18 0x0803ff07c00ff8e1 0x61007fe0f801ff1c

def z1441 : W := mkw 0x016c03a80ae07604 0x202d8075015c0ec0 0x6ffc03f80fb07f04 0xcdff807f01f60fe0

def z1442 : W := mkw 0xc5bff4426f7f89b7 0xd8b7fe884deff136 0xffffffc7ffffffff 0xfffffff8ffffffff

def z1443 : W := mkw 0x07fbbbf7b3b76045 0xc0ff777ef676ec08 0xf3fffffff3b64065 0xfe7ffffffe76c80c

def z1444 : W := mkw 0x03ea9bb590000000 0x007d5376b2000000 0x41ccdd39f0000001 0xc8399ba73e000000

def z1445 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xf7fffcc00fff8706 0xbeffff9801fff0e0

def z1446 : W := mkw 0xa0400b1dd0807cc8 0x34080163ba100f99 0xb803233ff04ffcff 0xf7006467fe09ff9f

def z1447 : W := mkw 0x4293b857b0130130 0x8852770af6026026 0xd80ffd3ff04f84fb 0xfb01ffa7fe09f09f

def z1448 : W := mkw 0x03ea9bf7b0000000 0x007d537ef6000000 0xd3ccfffff0000001 0xfa799ffffe000000

def z1449 : W := mkw 0x0000081090000000 0x0000010212000000 0x800cfc39f0000001 0xb0019f873e000000

def z1450 : W := mkw 0x05bff4080f7f9407 0xe0b7fe8101eff280 0xf5fffc380fff8406 0xbebfff8701fff080

def z1451 : W := mkw 0xa0044c18dc489c8a 0x340089831b891391 0x5c0cfd39fc09b89b 0x6b819fa73f813713

def z1452 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf3fffffff0304305 0xfe7ffffffe060860

def z1453 : W := mkw 0x03fbbbf7b1040001 0x007f777ef6208000 0xf3fffffff3860005 0xfe7ffffffe70c000

def z1454 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xfffffcc03fff879f 0xffffff9807fff0f3

def z1455 : W := mkw 0x05ae94000b648005 0x40b5d280016c9000 0x01cc1c0003800000 0x0039838000700000

def z1456 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0xf7ffffffff800007 0xfefffffffff00000

def z1457 : W := mkw 0x03bbb8f7b0000000 0x0077771ef6000000 0x823cfcf9f0000000 0x90479f9f3e000000

def z1458 : W := mkw 0x03fbbbf7b0000000 0x007f777ef6000000 0x63fffffff0000001 0x2c7ffffffe000000

def z1459 : W := mkw 0xa40444084f6c9c8f 0x7480888109ed9391 0x040000000f803800 0x0080000001f00700

def z1460 : W := mkw 0x0011281090000000 0x0002250212000000 0xf03ffd39f0000001 0xfe07ffa73e000000

def z1461 : W := mkw 0x45bff4422f7f8137 0xc8b7fe8845eff026 0xf5fffc003fff801e 0x3ebfff8007fff003

def z1462 : W := mkw 0x05bff4000f7f8007 0xc0b7fe8001eff000 0xfffffec03fffc79f 0xffffffd807fff8f3

def z1463 : W := mkw 0x45bff4000f7f8137 0xc8b7fe8001eff026 0xf5fffc000fffc366 0x3ebfff8001fff86c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z8]),(0,[z9,z0,z3,z4,z10,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z11])],[(0,[z9,z0,z3,z12,z4,z5,z6])],[(1,[z0,z2,z13,z4,z5,z6]),(0,[z9,z0,z14,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z15])],[(1,[z16,z17,z3,z4,z5,z6]),(0,[z0,z18,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z19])],[(0,[z0,z2,z20,z4,z21,z5,z6]),(0,[z0,z22,z2,z3,z4,z5,z6])],[(0,[z0,z2,z23,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z24]),(0,[z25,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z26,z27,z6]),(0,[z0,z2,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z29,z4,z30,z5])],[(0,[z0,z3,z4,z31,z32,z5,z6])],[(0,[z0,z2,z33,z4,z34,z5,z6]),(0,[z9,z0,z35,z3,z4,z5,z6]),(0,[z36,z0,z2,z3,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z38,z6]),(1,[z39,z0,z2,z3,z6,z40])],[(0,[z0,z3,z4,z41,z31,z5,z6]),(0,[z0,z2,z3,z4,z42,z5,z6])],[(0,[z43,z0,z2,z33,z4,z5,z6]),(0,[z0,z2,z3,z44,z4,z5,z6]),(0,[z0,z2,z3,z45,z4,z5,z6])],[(0,[z0,z46,z47,z3,z4,z5,z6]),(0,[z0,z2,z48,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z49])],[(0,[z9,z0,z3,z4,z50,z5,z6])],[(0,[z0,z51,z3,z12,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z52])],[(0,[z43,z2,z47,z3,z4,z5,z6]),(0,[z9,z43,z0,z3,z4,z5,z6]),(0,[z0,z53,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z54,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z55,z5,z6])],[(0,[z43,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z56])],[(0,[z16,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z57,z4,z5,z6]),(0,[z58,z0,z2,z3,z59,z5,z6])],[(0,[z0,z2,z3,z4,z5,z60,z6]),(0,[z0,z61,z2,z12,z4,z5,z6]),(0,[z0,z2,z12,z4,z62,z5,z6]),(0,[z0,z3,z4,z5,z63,z64,z6])],[(0,[z0,z2,z3,z65,z4,z5,z6]),(0,[z0,z2,z3,z4,z66,z5,z6]),(0,[z9,z0,z3,z4,z5,z27,z6]),(0,[z0,z2,z4,z5,z67,z6,z52]),(0,[z0,z2,z3,z4,z5,z6,z68]),(0,[z0,z2,z3,z69,z4,z5,z6])],[(0,[z70,z0,z46,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z72]),(0,[z9,z0,z73,z3,z4,z5,z6]),(0,[z0,z2,z3,z74,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z75,z6]),(0,[z76,z0,z2,z3,z4,z5,z52]),(0,[z0,z2,z3,z77,z4,z5,z6]),(1,[z0,z2,z3,z4,z78,z6]),(0,[z79,z0,z2,z4,z5,z6,z80])],[(0,[z0,z2,z81,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z82,z6])],[(0,[z0,z2,z3,z4,z5,z83,z6]),(0,[z0,z2,z3,z84,z4,z5,z6]),(0,[z0,z2,z3,z85,z4,z5,z6]),(0,[z0,z86,z2,z3,z4,z5,z6]),(0,[z0,z2,z87,z3,z4,z5,z6])],[(0,[z0,z3,z4,z31,z88,z5,z6]),(0,[z0,z2,z3,z4,z89,z5,z6]),(0,[z58,z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z90,z4,z5,z6])],[(0,[z0,z2,z4,z62,z30,z5,z6]),(0,[z0,z91,z2,z3,z4,z5,z6])],[(0,[z0,z2,z92,z4,z5,z93,z6]),(0,[z94,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z95,z5,z6]),(0,[z0,z2,z3,z4,z5,z96,z6]),(0,[z0,z2,z3,z4,z97,z5,z6]),(1,[z0,z61,z51,z4,z5,z6]),(0,[z98,z0,z2,z3,z4,z5,z6])],[(0,[z0,z99,z2,z3,z4,z5,z6]),(0,[z100,z0,z2,z3,z4,z5,z6]),(0,[z101,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z102,z4,z5,z6]),(0,[z103,z0,z3,z4,z5,z71,z6]),(0,[z0,z104,z2,z3,z4,z5,z6])],[(0,[z0,z105,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z106])],[(0,[z0,z2,z107,z33,z4,z5,z6]),(0,[z0,z61,z46,z3,z4,z5,z6]),(0,[z0,z108,z2,z3,z4,z5,z6])],[(0,[z0,z46,z3,z4,z109,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z111,z3,z4,z5,z6])],[(0,[z112,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z34,z5,z6])],[(0,[z0,z2,z3,z4,z113,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z114]),(0,[z0,z2,z115,z3,z4,z5,z6]),(0,[z0,z116,z2,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z29,z4,z6])],[(0,[z0,z2,z3,z118,z4,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z120]),(0,[z0,z2,z3,z4,z121,z5,z6]),(0,[z0,z73,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z122,z6])],[(0,[z0,z2,z3,z4,z5,z123,z6]),(0,[z103,z0,z2,z4,z62,z5,z6])],[(0,[z0,z124,z2,z3,z4,z5,z6]),(1,[z0,z2,z125,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z126,z6]),(0,[z0,z127,z2,z3,z4,z5,z6]),(0,[z0,z128,z2,z3,z4,z5,z6])],[(0,[z0,z2,z129,z3,z4,z5,z6]),(0,[z130,z0,z46,z3,z4,z5,z6]),(0,[z39,z0,z115,z3,z4,z5,z6])],[(0,[z131,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z132,z3,z4,z5,z6]),(0,[z133,z2,z3,z4,z5,z6,z72]),(0,[z133,z0,z2,z4,z62,z5,z6]),(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z135,z9,z0,z3,z4,z5,z6])],[],[(0,[z136,z0,z2,z3,z4,z5,z6]),(0,[z0,z47,z3,z4,z5,z71,z6]),(0,[z137,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z138,z4,z139,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z140]),(0,[z141,z0,z2,z3,z4,z5,z6]),(0,[z142,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z143])],[(0,[z0,z2,z92,z4,z5,z144,z6])],[(0,[z0,z2,z3,z4,z145,z5,z6]),(0,[z133,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z146,z5,z6]),(0,[z0,z2,z147,z3,z4,z5,z6])],[(0,[z0,z2,z92,z138,z4,z5,z6]),(0,[z148,z0,z3,z4,z5,z6,z80])],[(0,[z0,z149,z2,z3,z4,z5,z6])],[(0,[z150,z0,z3,z4,z5,z71,z6]),(0,[z58,z0,z46,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z152,z0,z153,z3,z4,z5,z6]),(0,[z0,z154,z2,z3,z4,z5,z6]),(0,[z0,z155,z2,z4,z62,z5,z6])],[(0,[z43,z131,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z156,z4,z5,z6]),(0,[z0,z2,z92,z157,z4,z5,z6])],[(0,[z0,z2,z92,z4,z62,z5,z6])],[(0,[z0,z2,z3,z158,z4,z5,z6]),(0,[z0,z2,z92,z59,z4,z5,z6]),(0,[z0,z2,z3,z4,z159,z5,z6])],[(0,[z0,z3,z138,z4,z5,z71,z6]),(0,[z0,z155,z2,z92,z4,z5,z6]),(0,[z58,z0,z2,z3,z4,z160,z6]),(1,[z0,z161,z3,z4,z5,z6])],[(0,[z131,z0,z2,z4,z5,z162,z6]),(0,[z163,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z164,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z165,z6]),(0,[z166,z0,z3,z4,z5,z71,z6])],[(0,[z0,z2,z3,z4,z5,z6,z167]),(0,[z0,z2,z168,z3,z4,z5,z6]),(0,[z169,z0,z46,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z170,z71,z6])],[(0,[z0,z171,z2,z3,z4,z5,z6]),(0,[z150,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z172,z5,z6]),(0,[z0,z2,z92,z4,z5,z6,z173]),(0,[z0,z2,z92,z174,z4,z5,z6]),(0,[z76,z169,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z175])],[(0,[z9,z131,z0,z3,z4,z5,z6]),(0,[z0,z2,z92,z20,z4,z5,z6]),(0,[z176,z0,z2,z92,z4,z5,z6]),(0,[z0,z177,z2,z3,z4,z5,z6])],[(0,[z0,z178,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z93,z6,z40]),(0,[z58,z0,z2,z3,z5,z6,z179])],[],[(0,[z0,z2,z3,z4,z5,z6,z72])],[(0,[z43,z0,z2,z14,z4,z5,z6]),(0,[z0,z2,z180,z4,z5,z71,z6]),(0,[z181,z0,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z31,z5,z63,z6]),(1,[z176,z0,z3,z4,z27,z6]),(0,[z0,z2,z3,z4,z5,z6,z182])],[(0,[z150,z0,z2,z3,z109,z5,z6]),(0,[z0,z3,z29,z4,z31,z5,z6]),(0,[z76,z0,z2,z4,z5,z6,z52])],[(0,[z9,z0,z178,z3,z4,z5,z6]),(0,[z0,z2,z183,z3,z4,z5,z6]),(0,[z0,z46,z2,z3,z4,z5,z6]),(0,[z58,z0,z86,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z122,z6,z80])]],
   [[(0,[z0,z3,z4,z31,z5,z64,z6]),(0,[z184,z0,z2,z4,z62,z5,z6])],[(0,[z70,z0,z2,z185,z4,z5,z6]),(0,[z0,z186,z3,z4,z31,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z187]),(0,[z0,z2,z4,z188,z62,z5,z6])],[(0,[z9,z0,z3,z4,z109,z5,z6]),(0,[z189,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z190,z3,z4,z5,z6]),(1,[z0,z104,z3,z4,z5,z6]),(1,[z0,z191,z3,z4,z5,z6]),(0,[z0,z2,z3,z192,z4,z5,z6])],[(0,[z0,z3,z4,z31,z5,z67,z6])],[(1,[z0,z2,z193,z4,z5,z6]),(0,[z0,z3,z4,z5,z162,z71,z6]),(0,[z76,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z194,z3,z4,z5,z6])],[(0,[z195,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z109,z5,z71,z6]),(0,[z0,z61,z2,z51,z4,z5,z6]),(0,[z169,z0,z61,z2,z4,z5,z6]),(0,[z0,z2,z51,z4,z62,z5,z6]),(0,[z117,z0,z161,z3,z4,z5,z6])],[(0,[z196,z0,z2,z3,z4,z5,z6]),(0,[z150,z0,z2,z3,z4,z197,z6]),(0,[z0,z2,z3,z4,z10,z5,z6]),(0,[z0,z3,z4,z5,z6,z198,z179]),(0,[z0,z199,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z12,z4,z5,z6]),(0,[z0,z46,z3,z4,z200,z5,z6])],[(0,[z9,z0,z3,z33,z4,z5,z6]),(0,[z0,z2,z3,z4,z201,z5,z6]),(0,[z137,z0,z2,z3,z4,z5,z144]),(0,[z0,z3,z4,z31,z5,z6,z179]),(0,[z76,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z14,z3,z4,z5,z6])],[(0,[z152,z2,z3,z4,z5,z93,z6]),(0,[z0,z2,z51,z92,z4,z5,z6]),(0,[z0,z2,z3,z202,z4,z5,z6])],[(0,[z0,z2,z203,z3,z4,z5,z6]),(0,[z0,z46,z107,z3,z4,z5,z6]),(0,[z0,z204,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z6]),(0,[z0,z2,z14,z107,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z78,z6])],[(0,[z0,z2,z3,z4,z206,z5,z6])],[(0,[z0,z2,z3,z33,z4,z5,z6]),(0,[z207,z0,z2,z3,z4,z5,z6]),(1,[z0,z46,z3,z138,z5,z6])],[]],
   [[(0,[z0,z2,z3,z4,z5,z6,z208])],[(0,[z0,z2,z3,z4,z209,z5,z6]),(0,[z0,z3,z4,z210,z5,z71,z6])],[(0,[z0,z2,z3,z4,z211,z5,z6])],[(0,[z0,z2,z3,z4,z212,z5,z6]),(0,[z0,z2,z3,z213,z4,z5,z6]),(0,[z214,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z215])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z216,z4,z5,z6]),(0,[z0,z2,z3,z4,z50,z5,z6]),(0,[z0,z217,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z218,z6]),(0,[z39,z0,z2,z219,z4,z5,z6])],[(0,[z0,z220,z2,z3,z4,z5,z6])],[(0,[z0,z221,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z222,z4,z5,z6]),(0,[z39,z223,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z202,z4,z5,z6])],[],[(0,[z0,z2,z224,z3,z4,z5,z6]),(0,[z225,z0,z2,z3,z4,z5,z6]),(0,[z226,z0,z2,z3,z4,z5,z6]),(0,[z227,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z228,z5,z6]),(0,[z0,z2,z3,z4,z229,z5,z6])],[(0,[z0,z2,z3,z4,z5,z230,z6]),(0,[z0,z3,z4,z5,z63,z71,z6]),(0,[z39,z0,z2,z3,z4,z210,z6])],[(0,[z0,z2,z3,z4,z5,z27,z6]),(0,[z0,z2,z3,z4,z5,z231,z6]),(0,[z0,z232,z2,z3,z4,z5,z6])],[(0,[z0,z217,z2,z4,z62,z5,z6])],[(0,[z233,z0,z2,z3,z4,z5,z6]),(0,[z234,z0,z2,z3,z4,z5,z6]),(0,[z235,z0,z3,z4,z5,z6,z179])],[(0,[z9,z152,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z236]),(0,[z0,z3,z4,z30,z5,z71,z6]),(0,[z237,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z238])],[(0,[z239,z0,z2,z3,z4,z5,z6]),(0,[z152,z0,z124,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z240,z5,z6]),(0,[z39,z0,z46,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z26,z6]),(0,[z0,z2,z3,z4,z6,z80,z40])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z241]),(0,[z0,z2,z3,z4,z5,z6,z242]),(0,[z243,z0,z2,z3,z102,z5,z6]),(0,[z0,z2,z3,z4,z5,z244,z6])],[(0,[z0,z178,z155,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z245]),(0,[z169,z0,z2,z14,z4,z5,z6])],[(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z30,z5,z6]),(0,[z0,z2,z92,z4,z5,z6,z15])],[(0,[z9,z0,z2,z3,z4,z5,z6])],[],[(0,[z247,z0,z3,z4,z31,z5,z6]),(0,[z248,z0,z2,z3,z4,z5,z6]),(0,[z249,z9,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z250]),(0,[z58,z0,z2,z3,z4,z5,z64])],[(0,[z9,z0,z217,z3,z4,z5,z6]),(0,[z251,z0,z2,z3,z31,z5,z6]),(0,[z252,z0,z2,z3,z4,z5,z6]),(1,[z79,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z253,z5,z6]),(0,[z152,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z4,z62,z200,z5,z6]),(0,[z0,z2,z3,z4,z254,z5,z6])],[(0,[z150,z0,z2,z3,z4,z5,z255]),(0,[z0,z256,z2,z3,z4,z5,z6])],[(0,[z0,z257,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z258,z62,z5,z6])],[(0,[z131,z0,z217,z2,z4,z5,z6]),(0,[z0,z107,z3,z4,z31,z5,z6]),(1,[z0,z46,z4,z62,z5,z6]),(1,[z0,z2,z107,z4,z5,z67]),(0,[z0,z2,z3,z4,z259,z5,z6])],[(0,[z260,z0,z2,z3,z4,z5,z6]),(0,[z9,z16,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z4,z31,z5,z6]),(0,[z103,z0,z2,z92,z4,z5,z6]),(0,[z261,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z262,z4,z5,z6]),(1,[z0,z2,z4,z139,z5,z6])],[(0,[z0,z2,z3,z263,z4,z5,z6]),(0,[z9,z0,z3,z4,z200,z5,z6]),(1,[z0,z73,z3,z4,z5,z71]),(0,[z0,z2,z92,z4,z5,z6,z52])],[(0,[z16,z0,z3,z4,z5,z71,z6]),(0,[z9,z137,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z31,z31,z5,z6])],[(0,[z264,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z265,z3,z4,z5,z6])]],
   [[(0,[z0,z266,z2,z3,z4,z5,z6]),(0,[z267,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z268,z4,z5,z6]),(0,[z9,z0,z107,z3,z4,z5,z6])],[(0,[z0,z92,z3,z4,z31,z5,z6])],[(0,[z0,z46,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z210,z93,z6]),(0,[z176,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z269,z4,z5,z6]),(0,[z270,z0,z2,z3,z4,z5,z6])],[(0,[z169,z0,z2,z33,z4,z5,z6]),(0,[z9,z0,z47,z3,z4,z5,z6]),(0,[z0,z271,z2,z3,z4,z5,z6])],[(0,[z233,z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z272,z5,z6])],[(0,[z0,z2,z186,z3,z4,z5,z6])],[(0,[z16,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z273,z3,z4,z5,z6]),(0,[z0,z2,z3,z274,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z5,z6]),(0,[z0,z2,z276,z3,z4,z5,z6])],[(0,[z277,z0,z2,z3,z4,z5,z6]),(0,[z0,z278,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z279,z5,z6])],[(0,[z9,z169,z0,z3,z4,z5,z6]),(0,[z0,z2,z92,z92,z4,z5,z6]),(0,[z0,z2,z174,z4,z280,z5,z6])],[(0,[z130,z16,z2,z3,z4,z5,z6]),(0,[z0,z281,z2,z3,z4,z5,z6])],[(0,[z282,z0,z2,z3,z4,z5,z6]),(0,[z251,z0,z46,z3,z4,z5,z6])],[(1,[z0,z283,z2,z4,z5,z6]),(0,[z0,z2,z284,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z165,z6]),(0,[z0,z2,z285,z3,z4,z5,z6]),(0,[z0,z2,z3,z286,z4,z5,z6]),(1,[z0,z37,z3,z4,z5,z6])],[(0,[z233,z0,z2,z3,z4,z5,z144]),(0,[z119,z0,z3,z4,z5,z64,z6])],[(0,[z150,z0,z2,z92,z4,z5,z6])],[(0,[z287,z0,z2,z3,z4,z5,z6]),(0,[z288,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z289,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z290,z6]),(0,[z0,z2,z3,z4,z5,z6,z291]),(0,[z0,z2,z4,z5,z6,z292,z80])]],
   [[(0,[z0,z293,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z294,z6]),(0,[z0,z2,z3,z4,z295,z5,z6]),(0,[z0,z2,z92,z4,z34,z5,z6])],[(0,[z296,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z297,z5,z6]),(0,[z0,z2,z3,z298,z4,z5,z6]),(0,[z0,z3,z4,z200,z5,z71,z6])],[(0,[z0,z2,z299,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z300,z6]),(0,[z301,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z20,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z302,z5,z6]),(0,[z9,z0,z3,z102,z4,z5,z6]),(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z58,z0,z2,z3,z4,z78,z6])],[(0,[z0,z178,z2,z4,z62,z5,z6]),(0,[z131,z0,z3,z4,z5,z71,z6]),(0,[z0,z46,z3,z4,z31,z5,z6])],[(0,[z304,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z305,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z255,z6]),(0,[z0,z3,z174,z4,z306,z5,z6]),(1,[z0,z2,z4,z307,z5,z6])],[(0,[z308,z0,z2,z3,z4,z5,z6]),(0,[z0,z178,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z309,z5,z6]),(0,[z169,z0,z2,z3,z4,z34,z6]),(0,[z0,z2,z3,z4,z5,z6,z310])],[(1,[z243,z0,z2,z62,z5,z6])],[(0,[z0,z2,z3,z4,z109,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6])],[(0,[z0,z2,z312,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z210,z6,z80]),(1,[z0,z2,z313,z4,z5,z6]),(0,[z117,z0,z2,z3,z29,z4,z5])],[(0,[z131,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z314,z5,z6]),(0,[z0,z2,z3,z4,z5,z315,z6]),(0,[z0,z2,z316,z3,z4,z5,z6])],[(0,[z317,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z318])],[(0,[z319,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z320,z5,z6])],[(0,[z321,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z322])]],
   [[(0,[z0,z2,z3,z4,z323,z5,z6])],[(0,[z0,z324,z2,z3,z4,z5,z6]),(1,[z0,z124,z3,z4,z5,z6]),(0,[z325,z0,z3,z4,z5,z71,z6])],[(0,[z0,z3,z59,z4,z31,z5,z6]),(0,[z0,z2,z3,z326,z4,z5,z6]),(0,[z327,z0,z2,z3,z4,z5,z6]),(1,[z328,z2,z3,z4,z5,z6])],[(0,[z0,z329,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z330,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z331]),(0,[z0,z2,z3,z4,z5,z6,z292])],[(0,[z0,z3,z33,z4,z31,z5,z6]),(0,[z76,z0,z2,z4,z34,z5,z6])],[(0,[z0,z2,z3,z332,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z333,z6])],[(0,[z9,z0,z17,z3,z4,z5,z6]),(0,[z130,z0,z178,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z334,z6]),(0,[z335,z9,z0,z3,z4,z5,z6]),(0,[z0,z2,z336,z3,z4,z5,z6])],[(0,[z0,z217,z2,z4,z5,z6,z52]),(0,[z0,z2,z3,z4,z5,z337,z6]),(0,[z0,z2,z3,z4,z5,z338,z6])],[(0,[z0,z2,z3,z4,z5,z339,z6]),(0,[z0,z2,z3,z29,z4,z6,z80])],[(1,[z0,z3,z4,z31,z5,z6]),(0,[z0,z46,z3,z4,z5,z64,z6]),(0,[z340,z0,z2,z3,z4,z5,z6]),(0,[z0,z341,z2,z3,z4,z5,z6]),(1,[z235,z0,z3,z4,z5,z6])],[(0,[z342,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z144,z6,z72]),(0,[z0,z2,z92,z4,z5,z6,z72]),(0,[z0,z3,z29,z4,z5,z71,z6])],[],[(0,[z343,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z190,z4,z5,z6])],[(0,[z0,z46,z3,z4,z5,z67,z6])],[(1,[z0,z2,z3,z4,z344,z6])]],
   [[(0,[z0,z2,z3,z4,z345,z5,z6])],[],[(0,[z233,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z346,z5,z6]),(0,[z0,z2,z3,z4,z347,z5,z6])],[(0,[z0,z217,z2,z92,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z6,z179]),(0,[z0,z2,z3,z5,z64,z6,z179])],[(0,[z58,z348,z2,z3,z4,z5,z6])],[(1,[z0,z153,z3,z4,z5,z6]),(0,[z103,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z349,z4,z5,z6])],[(0,[z350,z0,z2,z3,z4,z5,z6])],[(0,[z351,z0,z2,z3,z4,z5,z6]),(0,[z70,z0,z2,z3,z4,z50,z6]),(0,[z0,z352,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z353,z4,z5,z6])],[(0,[z70,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z354,z5,z6]),(0,[z0,z2,z92,z12,z4,z5,z6]),(1,[z0,z4,z62,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z6,z355])],[(0,[z133,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z215]),(0,[z0,z2,z3,z4,z30,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z217,z2,z4,z34,z5,z6]),(0,[z0,z3,z4,z31,z5,z6,z40]),(0,[z356,z0,z2,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z5,z6])],[(1,[z0,z3,z4,z5,z63,z6]),(0,[z0,z3,z59,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z6,z357])],[(0,[z0,z2,z3,z4,z5,z6,z358]),(0,[z0,z2,z92,z4,z206,z5,z6])],[(0,[z0,z2,z3,z4,z5,z359,z6]),(0,[z360,z0,z2,z3,z4,z5,z6])],[(0,[z0,z127,z3,z4,z31,z5,z6])],[(1,[z0,z2,z3,z4,z5,z361]),(0,[z0,z2,z193,z3,z4,z5,z6]),(0,[z0,z2,z362,z3,z4,z5,z6]),(0,[z363,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z364,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z306,z5,z6])],[(1,[z152,z2,z3,z4,z93,z6]),(0,[z0,z61,z2,z3,z4,z5,z6]),(1,[z0,z46,z92,z4,z5,z6]),(0,[z0,z155,z46,z3,z4,z5,z6])],[(0,[z137,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z365,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z366]),(0,[z0,z2,z92,z4,z50,z5,z6]),(0,[z0,z3,z174,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z367,z6])],[(0,[z0,z2,z3,z368,z4,z5,z6]),(0,[z0,z51,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z200,z5,z6])],[(0,[z0,z369,z2,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z30,z6])],[(0,[z370,z0,z2,z3,z4,z5,z6]),(0,[z176,z0,z3,z4,z5,z27,z6]),(0,[z0,z2,z3,z4,z280,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z371])],[(0,[z0,z372,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z5,z64,z6]),(0,[z0,z2,z4,z62,z373,z5,z6]),(0,[z0,z2,z107,z3,z4,z5,z6]),(0,[z374,z0,z2,z3,z4,z5,z6])],[(0,[z150,z0,z2,z216,z4,z5,z6]),(0,[z150,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z72,z179]),(0,[z0,z3,z4,z31,z5,z162,z6]),(0,[z0,z2,z3,z4,z5,z6,z375])],[],[(0,[z0,z2,z47,z3,z4,z5,z6]),(0,[z0,z2,z92,z4,z5,z27,z6])],[(0,[z207,z9,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z174,z4,z6,z40])],[(0,[z0,z2,z47,z107,z4,z5,z6]),(1,[z137,z2,z3,z4,z5,z72]),(0,[z0,z3,z4,z62,z5,z71,z6]),(0,[z0,z2,z4,z62,z5,z67,z6])],[(0,[z16,z0,z2,z92,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z64,z6])],[(0,[z0,z2,z3,z4,z5,z376,z6])],[(0,[z0,z2,z3,z4,z5,z377,z6]),(0,[z70,z133,z2,z3,z4,z5,z6]),(0,[z9,z176,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z322]),(0,[z0,z2,z92,z4,z5,z244,z6])]],
   [[(0,[z58,z0,z2,z3,z4,z5,z179]),(0,[z0,z2,z3,z4,z378,z5,z6])],[(0,[z0,z3,z4,z31,z210,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z379]),(1,[z9,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z5,z6,z179]),(0,[z223,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z380])],[(1,[z0,z2,z4,z21,z5,z6]),(0,[z0,z2,z3,z4,z5,z381,z6]),(0,[z58,z0,z2,z3,z4,z5,z6])],[(0,[z152,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z382,z5,z6]),(0,[z0,z2,z3,z185,z4,z5,z6])],[(1,[z0,z383,z3,z4,z5,z6]),(0,[z243,z0,z2,z3,z4,z5,z6]),(0,[z384,z0,z2,z4,z62,z5,z6])],[(0,[z0,z2,z385,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z386,z6]),(0,[z0,z2,z3,z4,z5,z387,z6])],[(0,[z43,z0,z2,z4,z5,z67,z6]),(0,[z0,z107,z3,z4,z5,z71,z6])],[(0,[z0,z2,z3,z4,z5,z6,z388]),(0,[z76,z0,z46,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z6,z179])],[(0,[z389,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z390,z3,z4,z5,z6]),(0,[z137,z0,z2,z391,z4,z5,z6]),(0,[z0,z392,z46,z3,z4,z5,z6])],[(0,[z393,z0,z2,z3,z4,z5,z6]),(0,[z150,z0,z132,z3,z4,z5,z6]),(0,[z150,z2,z3,z4,z109,z5,z6]),(0,[z0,z2,z3,z394,z4,z5,z6]),(0,[z39,z0,z2,z3,z5,z6,z40])],[(0,[z0,z3,z102,z4,z31,z5,z6]),(0,[z0,z3,z4,z31,z5,z71,z6]),(0,[z0,z2,z3,z102,z4,z5,z6])],[(0,[z152,z0,z2,z4,z62,z5,z6]),(0,[z137,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z32,z5,z6]),(0,[z0,z2,z107,z3,z4,z5,z67])],[(0,[z0,z2,z3,z4,z5,z395,z6]),(0,[z0,z46,z2,z3,z138,z5,z6])],[(0,[z43,z0,z2,z47,z4,z5,z6]),(0,[z0,z3,z4,z31,z5,z6,z80]),(0,[z0,z92,z3,z4,z5,z71,z6]),(0,[z396,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z397,z6])],[(0,[z398,z0,z2,z3,z4,z5,z6])],[]],
   [[(0,[z2,z3,z4,z50,z5,z93,z6])],[(0,[z0,z155,z2,z3,z4,z27,z6]),(0,[z399,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z400,z5,z6]),(0,[z0,z217,z2,z12,z4,z5,z6]),(0,[z248,z9,z0,z3,z4,z5,z6]),(0,[z401,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z387])],[(0,[z131,z0,z2,z92,z4,z5,z6]),(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z119,z9,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z403])],[(0,[z0,z2,z3,z4,z404,z5,z6])],[(0,[z176,z0,z2,z3,z4,z27,z6]),(0,[z0,z2,z3,z4,z405,z5,z6])],[(0,[z406,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z407,z4,z5,z6]),(0,[z9,z0,z61,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z210,z5,z6])],[(0,[z408,z0,z2,z3,z4,z5,z6]),(1,[z282,z0,z3,z4,z5,z6]),(0,[z409,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z410,z6]),(0,[z0,z2,z3,z4,z411,z5,z6])],[(0,[z0,z2,z3,z4,z412,z5,z6]),(0,[z0,z2,z107,z4,z5,z67,z6])],[(0,[z152,z70,z2,z3,z4,z5,z6]),(0,[z413,z0,z2,z3,z4,z5,z6]),(0,[z0,z414,z2,z92,z4,z5,z6])],[(0,[z0,z18,z2,z17,z4,z5,z6]),(1,[z130,z178,z3,z4,z5,z6]),(0,[z131,z0,z61,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z93,z71,z6]),(0,[z0,z46,z92,z3,z4,z5,z6]),(0,[z415,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z125,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z88,z5,z6])],[(0,[z0,z2,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z416,z6]),(0,[z0,z217,z46,z3,z4,z5,z6])],[(0,[z0,z17,z3,z4,z5,z27,z6]),(0,[z0,z2,z3,z417,z4,z5,z6]),(0,[z0,z3,z4,z418,z31,z5,z6]),(0,[z0,z3,z4,z5,z71,z64,z6])],[(0,[z419,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z420,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z421,z5,z6]),(0,[z422,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z71,z6]),(1,[z0,z2,z92,z102,z5,z6]),(1,[z0,z2,z3,z4,z30,z80])],[(0,[z0,z423,z2,z3,z4,z5,z6])],[(0,[z131,z2,z3,z33,z4,z5,z6]),(0,[z424,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z5,z6,z425])],[(0,[z0,z283,z2,z3,z4,z5,z6]),(1,[z0,z2,z426,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z427,z6]),(0,[z0,z2,z3,z4,z5,z6,z428]),(0,[z0,z46,z3,z4,z5,z429,z6]),(0,[z0,z2,z3,z4,z5,z6,z322])],[],[(0,[z43,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z31,z5,z6,z430]),(0,[z0,z2,z3,z4,z30,z5,z80])],[(0,[z0,z2,z190,z138,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z179]),(0,[z117,z0,z2,z3,z4,z5,z80])],[(0,[z0,z2,z92,z4,z109,z5,z6])],[(0,[z133,z0,z2,z3,z20,z5,z6])],[(0,[z9,z0,z3,z4,z31,z5,z6]),(0,[z9,z0,z3,z431,z4,z5,z6]),(0,[z0,z2,z432,z92,z4,z5,z6])],[(0,[z0,z2,z4,z62,z5,z162,z6])],[(0,[z0,z2,z3,z4,z433,z5,z6]),(0,[z130,z0,z17,z3,z4,z5,z6]),(0,[z70,z0,z3,z4,z31,z5,z6]),(0,[z0,z3,z12,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z434])],[(0,[z0,z2,z3,z4,z5,z435,z6])],[(0,[z117,z0,z3,z4,z31,z5,z6])]],
   [[(0,[z0,z3,z33,z4,z5,z71,z6]),(0,[z0,z2,z92,z33,z4,z5,z6]),(0,[z436,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z51,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z437])],[(1,[z0,z2,z4,z5,z6,z438]),(0,[z0,z2,z92,z326,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z439,z6])],[(0,[z169,z0,z2,z47,z4,z5,z6]),(1,[z0,z2,z391,z4,z5,z6]),(0,[z0,z2,z3,z4,z440,z5,z6]),(0,[z0,z2,z3,z4,z5,z26,z6]),(0,[z39,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z14,z4,z62,z5,z6]),(0,[z441,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z188,z5,z6])],[(0,[z0,z2,z442,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z4,z62,z210,z5,z6])],[(0,[z0,z2,z4,z50,z5,z83,z6]),(0,[z0,z61,z2,z107,z4,z5,z6])],[(0,[z16,z0,z46,z3,z4,z5,z6]),(0,[z443,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z31,z5,z93,z6]),(0,[z444,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z445,z5,z6])],[(0,[z0,z2,z3,z446,z4,z5,z6]),(1,[z0,z92,z4,z31,z5,z6]),(0,[z447,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z14,z3,z4,z162,z6]),(0,[z0,z2,z3,z210,z5,z6,z40]),(1,[z58,z0,z2,z3,z5,z179])],[(0,[z0,z2,z3,z448,z4,z5,z6]),(0,[z58,z0,z2,z313,z4,z5,z6])],[(0,[z150,z0,z2,z13,z4,z5,z6]),(1,[z0,z3,z4,z5,z429,z6])],[(0,[z449,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z153,z3,z4,z5,z6]),(1,[z0,z2,z147,z4,z5,z6]),(1,[z0,z4,z31,z62,z5,z6]),(0,[z0,z53,z2,z4,z62,z5,z6]),(0,[z450,z0,z2,z3,z4,z5,z6])],[(0,[z137,z0,z2,z426,z4,z5,z6]),(0,[z0,z2,z48,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z451])],[(0,[z130,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z452,z5,z6]),(0,[z0,z2,z3,z4,z453,z5,z6]),(0,[z0,z2,z3,z174,z4,z210,z6])],[(0,[z233,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z138,z4,z62,z5,z6]),(0,[z0,z2,z4,z62,z5,z71,z6])],[(0,[z454,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z59,z4,z307,z5,z6]),(0,[z455,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z456,z0,z2,z3,z4,z5,z6]),(0,[z243,z0,z2,z3,z62,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z457]),(0,[z0,z2,z3,z4,z5,z63,z6]),(0,[z0,z2,z3,z458,z4,z5,z6])],[(0,[z0,z3,z4,z5,z60,z71,z6])],[(0,[z459,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z6,z40]),(0,[z0,z2,z3,z4,z5,z80,z179])],[(0,[z0,z3,z4,z5,z27,z71,z6]),(0,[z0,z2,z3,z4,z373,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z6]),(1,[z0,z2,z3,z59,z5,z64])],[(0,[z0,z178,z46,z3,z4,z5,z6]),(1,[z131,z2,z33,z4,z5,z6]),(0,[z9,z133,z0,z3,z4,z5,z6]),(0,[z176,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z67,z6]),(0,[z0,z3,z102,z4,z460,z5,z6])],[(0,[z0,z178,z3,z4,z5,z27,z6]),(0,[z0,z2,z4,z5,z6,z236,z72]),(0,[z0,z217,z2,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z306,z5,z6])],[(0,[z0,z2,z3,z461,z4,z5,z6]),(0,[z131,z0,z2,z33,z4,z5,z6]),(0,[z462,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z344,z5,z6]),(1,[z0,z2,z463,z4,z5,z6]),(0,[z0,z104,z3,z174,z4,z5,z6]),(0,[z464,z0,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z31,z5,z144,z6]),(0,[z0,z2,z3,z4,z5,z6,z465]),(0,[z0,z2,z3,z4,z5,z6,z466]),(0,[z0,z2,z92,z4,z30,z5,z6]),(0,[z0,z2,z3,z4,z467,z5,z6])],[(0,[z0,z2,z3,z4,z468,z5,z6]),(0,[z0,z2,z3,z4,z469,z5,z6]),(0,[z470,z0,z2,z3,z4,z5,z6]),(0,[z243,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z471,z6]),(0,[z0,z2,z107,z4,z5,z162,z6]),(0,[z0,z2,z3,z4,z5,z67,z6])],[(0,[z0,z3,z4,z31,z5,z6,z472])],[(0,[z473,z0,z2,z3,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z6,z6]),(0,[z169,z0,z2,z3,z4,z5,z6]),(0,[z474,z0,z2,z3,z4,z5,z6])],[(0,[z131,z0,z46,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z93,z6]),(1,[z251,z0,z3,z31,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z71])],[(0,[z251,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z179]),(0,[z475,z0,z2,z3,z4,z5,z6])],[(0,[z152,z0,z2,z3,z4,z93,z6]),(0,[z0,z3,z4,z31,z62,z5,z6]),(0,[z0,z3,z4,z5,z67,z71,z6]),(0,[z0,z3,z174,z4,z5,z71,z6])]],
   [[(0,[z0,z51,z3,z4,z5,z71,z6]),(1,[z0,z108,z2,z4,z5,z6]),(0,[z0,z265,z2,z3,z4,z5,z6])],[(0,[z0,z2,z4,z109,z62,z5,z6]),(0,[z0,z46,z3,z4,z5,z162,z6]),(0,[z0,z107,z3,z476,z4,z5,z6])],[(0,[z152,z0,z2,z92,z4,z5,z6]),(0,[z137,z0,z2,z3,z4,z5,z72]),(0,[z477,z0,z2,z3,z4,z5,z6]),(0,[z288,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z92,z4,z200,z5,z6]),(0,[z9,z9,z0,z3,z4,z5,z6]),(1,[z0,z2,z276,z4,z5,z6])],[(0,[z9,z0,z51,z3,z4,z5,z6]),(0,[z0,z3,z4,z31,z5,z6,z173]),(0,[z0,z414,z46,z3,z4,z5,z6])],[(0,[z0,z478,z3,z20,z4,z5,z6]),(0,[z137,z233,z2,z3,z4,z5,z6]),(0,[z0,z191,z2,z3,z4,z5,z6])],[(0,[z137,z2,z3,z4,z5,z6,z72]),(0,[z137,z0,z2,z4,z62,z5,z6])],[(0,[z9,z0,z3,z479,z4,z5,z6]),(1,[z0,z3,z4,z460,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z480])],[(0,[z481,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z482,z5,z6])],[(1,[z0,z46,z3,z31,z5,z6])],[(0,[z0,z2,z3,z4,z297,z5,z6]),(0,[z137,z0,z2,z92,z4,z5,z6])],[(0,[z0,z2,z3,z483,z4,z5,z6])],[(0,[z0,z484,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z485,z4,z5,z6]),(1,[z233,z2,z3,z4,z5,z144])],[(0,[z233,z2,z3,z4,z5,z144,z6])],[(0,[z0,z2,z3,z486,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z487])],[(0,[z0,z2,z407,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z488]),(1,[z163,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z489,z6])]],
   [[(0,[z0,z46,z3,z138,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z490,z6]),(0,[z0,z3,z164,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z491,z6]),(0,[z0,z2,z276,z59,z4,z5,z6])],[(0,[z0,z2,z4,z62,z5,z6,z40]),(0,[z0,z492,z2,z3,z4,z5,z6])],[(0,[z0,z493,z2,z3,z4,z5,z6]),(0,[z494,z0,z2,z3,z4,z5,z6]),(1,[z0,z495,z3,z4,z5,z6])],[],[(0,[z0,z2,z3,z496,z4,z5,z6])],[(0,[z0,z3,z4,z5,z71,z71,z6]),(0,[z0,z2,z92,z3,z102,z5,z6]),(1,[z0,z2,z14,z4,z34,z6])],[(0,[z0,z2,z497,z3,z4,z5,z6]),(0,[z0,z46,z3,z59,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z6,z80]),(0,[z0,z2,z3,z4,z5,z6,z498]),(0,[z0,z3,z102,z4,z5,z71,z6]),(0,[z499,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z500,z4,z5,z6]),(0,[z0,z46,z3,z29,z4,z5,z6]),(1,[z116,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z92,z102,z4,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z46,z3,z174,z4,z5,z6])],[(0,[z0,z2,z4,z62,z5,z93,z6]),(0,[z70,z0,z2,z407,z4,z5,z6]),(0,[z0,z46,z3,z501,z4,z5,z6]),(0,[z0,z46,z2,z4,z62,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z173]),(0,[z76,z0,z2,z3,z4,z5,z67]),(0,[z0,z2,z3,z4,z5,z6,z502])],[(0,[z43,z0,z3,z4,z31,z5,z6]),(0,[z0,z46,z128,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z4,z5,z6])],[(0,[z0,z3,z4,z5,z71,z6,z6])],[(0,[z0,z2,z3,z4,z5,z6,z503]),(0,[z0,z2,z3,z4,z5,z504,z6]),(0,[z169,z0,z2,z4,z5,z67,z6]),(0,[z0,z2,z14,z4,z5,z6,z52])],[(0,[z2,z3,z4,z109,z5,z93,z6]),(0,[z0,z2,z3,z4,z505,z5,z6]),(0,[z0,z46,z2,z92,z4,z5,z6]),(0,[z58,z9,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z506,z4,z5,z6]),(0,[z0,z2,z3,z4,z507,z5,z6]),(1,[z117,z0,z2,z3,z29,z4])],[],[(0,[z0,z3,z4,z5,z144,z71,z6]),(0,[z0,z2,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z508,z4,z5,z6]),(0,[z0,z2,z3,z431,z4,z5,z6])],[(0,[z0,z73,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z509,z4,z5,z6])],[(0,[z0,z155,z17,z3,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z162,z6]),(0,[z0,z2,z3,z29,z4,z5,z64])],[(0,[z510,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z194,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z511,z6]),(0,[z58,z0,z2,z305,z4,z5,z6])],[(0,[z0,z2,z3,z4,z50,z6,z40]),(0,[z39,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z512,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z198])],[(0,[z103,z0,z2,z3,z4,z5,z6]),(0,[z131,z0,z2,z14,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z175])],[(0,[z43,z0,z2,z4,z5,z162,z6]),(0,[z0,z61,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z513,z6])],[(0,[z514,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z515,z5,z6]),(1,[z0,z516,z3,z4,z5,z6]),(0,[z0,z2,z14,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z517])],[(0,[z0,z2,z3,z4,z5,z6,z518])],[(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z150,z0,z2,z3,z20,z5,z6]),(0,[z0,z2,z3,z4,z5,z519,z6]),(0,[z0,z2,z3,z520,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z521]),(0,[z0,z522,z2,z3,z4,z5,z6])],[(0,[z9,z0,z3,z4,z210,z5,z6])],[(0,[z0,z523,z2,z3,z4,z5,z6])]],
   [[(0,[z524,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z62,z5,z6]),(1,[z0,z3,z476,z4,z5,z6])],[(0,[z0,z220,z2,z4,z62,z5,z6]),(0,[z0,z2,z14,z4,z34,z5,z6]),(0,[z0,z2,z3,z59,z5,z64,z6]),(1,[z0,z2,z525,z4,z5,z6])],[(0,[z130,z0,z3,z4,z31,z5,z6]),(0,[z0,z46,z3,z4,z5,z6,z526]),(0,[z0,z2,z3,z4,z139,z5,z6]),(0,[z9,z0,z92,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z527,z5,z6]),(0,[z0,z528,z2,z3,z4,z5,z6])],[(0,[z529,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z530,z5,z6])],[(0,[z0,z155,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z487]),(1,[z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z4,z62,z5,z6,z80]),(0,[z0,z2,z3,z531,z4,z5,z6])],[(0,[z0,z3,z20,z4,z297,z5,z6]),(0,[z233,z0,z2,z3,z4,z5,z72]),(0,[z532,z0,z2,z3,z4,z5,z6])],[(0,[z178,z2,z17,z3,z4,z5,z6]),(0,[z130,z178,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z533,z4,z5,z6]),(0,[z0,z2,z3,z4,z534,z5,z6]),(0,[z0,z383,z2,z3,z4,z5,z6]),(0,[z0,z535,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z536]),(1,[z9,z0,z3,z4,z5,z173]),(0,[z0,z2,z3,z4,z5,z6,z537]),(0,[z148,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z538,z6]),(0,[z0,z539,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z71,z6])],[(0,[z0,z2,z3,z4,z5,z6,z540]),(0,[z0,z3,z4,z5,z71,z6,z40])],[(0,[z70,z0,z3,z4,z5,z71,z6]),(0,[z233,z0,z2,z4,z62,z5,z6]),(0,[z0,z3,z12,z4,z5,z71,z6]),(0,[z0,z2,z525,z4,z30,z5,z6]),(0,[z0,z2,z3,z541,z4,z5,z6])],[(0,[z0,z3,z4,z31,z5,z6,z52]),(0,[z58,z0,z3,z4,z31,z5,z6]),(0,[z9,z0,z3,z4,z5,z6,z80]),(1,[z0,z4,z5,z71,z6,z438])],[(0,[z150,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z29,z4,z5,z6]),(0,[z117,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z4,z5,z162,z6,z52])],[(0,[z152,z0,z46,z3,z4,z5,z6])],[(0,[z542,z0,z2,z3,z4,z5,z6]),(0,[z233,z0,z2,z92,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z543,z6]),(0,[z544,z0,z2,z3,z4,z5,z6])],[(1,[z70,z2,z3,z4,z50,z6]),(0,[z0,z2,z3,z4,z5,z545,z6]),(0,[z0,z3,z4,z295,z31,z5,z6]),(0,[z0,z3,z4,z200,z5,z27,z6]),(0,[z0,z155,z3,z4,z200,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z108,z2,z4,z5,z27,z6]),(0,[z9,z0,z2,z4,z62,z5,z6]),(0,[z0,z528,z107,z3,z4,z5,z6])]],
   [[(0,[z546,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z429,z6]),(0,[z0,z2,z3,z4,z5,z6,z547])],[(1,[z0,z2,z3,z4,z197,z6]),(1,[z0,z478,z3,z4,z5,z6]),(0,[z169,z0,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z548,z5,z6]),(0,[z0,z2,z4,z549,z62,z5,z6])],[(0,[z0,z217,z3,z12,z4,z5,z6]),(0,[z9,z0,z3,z4,z530,z5,z6]),(1,[z76,z0,z2,z4,z5,z52])],[(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z251,z0,z3,z4,z31,z5,z6]),(0,[z117,z0,z2,z4,z62,z5,z6])],[(1,[z0,z92,z4,z5,z71,z6]),(0,[z184,z0,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z6,z550])],[(0,[z0,z180,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z551,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z552,z6]),(1,[z150,z2,z3,z109,z5,z6])],[(0,[z0,z553,z2,z3,z4,z5,z6])],[(0,[z76,z0,z2,z3,z4,z5,z6])],[(0,[z16,z2,z17,z3,z4,z5,z6]),(1,[z43,z2,z47,z4,z5,z6]),(0,[z0,z2,z51,z3,z4,z5,z6]),(0,[z0,z392,z2,z3,z4,z5,z6])],[(0,[z76,z0,z2,z107,z4,z5,z6])],[(0,[z0,z2,z3,z554,z4,z5,z6]),(0,[z0,z3,z20,z4,z31,z5,z6]),(1,[z0,z3,z4,z5,z555,z6]),(0,[z0,z3,z4,z31,z34,z5,z6]),(0,[z0,z2,z3,z4,z307,z5,z6])],[(0,[z0,z2,z3,z556,z4,z5,z6]),(0,[z0,z2,z3,z479,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z438]),(0,[z0,z2,z3,z4,z5,z6,z557]),(0,[z169,z0,z2,z4,z5,z162,z6])],[(0,[z0,z2,z558,z3,z4,z5,z6]),(0,[z39,z9,z0,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z559,z4,z5,z6]),(0,[z0,z2,z3,z4,z549,z5,z6]),(0,[z0,z2,z3,z560,z4,z5,z6])],[(0,[z0,z46,z3,z4,z5,z144,z6]),(0,[z0,z2,z3,z4,z258,z5,z6]),(0,[z0,z2,z3,z313,z4,z5,z6])],[(0,[z0,z61,z51,z3,z4,z5,z6])],[(0,[z0,z2,z47,z4,z62,z5,z6]),(0,[z0,z2,z92,z4,z5,z64,z6])],[(0,[z0,z2,z29,z4,z62,z5,z6])],[(0,[z561,z0,z2,z3,z4,z5,z6]),(0,[z0,z562,z2,z3,z4,z5,z6]),(0,[z243,z0,z3,z4,z5,z71,z6])],[(0,[z16,z0,z178,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z66,z5,z6]),(0,[z301,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z563,z4,z5,z6]),(0,[z0,z564,z2,z3,z4,z5,z6])],[(0,[z0,z2,z565,z3,z4,z5,z6]),(0,[z243,z0,z516,z3,z4,z5,z6]),(0,[z566,z0,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z31,z146,z5,z6]),(0,[z0,z46,z3,z4,z62,z5,z6]),(0,[z0,z2,z92,z4,z5,z67,z6]),(0,[z0,z2,z3,z567,z4,z5,z6])],[(0,[z0,z3,z4,z5,z6,z215,z52])],[(0,[z9,z0,z3,z4,z5,z6,z40])],[(0,[z0,z2,z391,z3,z4,z5,z6]),(1,[z9,z0,z3,z4,z5,z71]),(0,[z0,z3,z4,z5,z71,z6,z80]),(0,[z0,z568,z2,z3,z4,z5,z6]),(0,[z79,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z30,z6,z80])],[(0,[z0,z2,z3,z569,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z570,z6]),(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z6,z173]),(0,[z243,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z92,z4,z5,z6,z179]),(0,[z0,z2,z3,z4,z460,z5,z6])],[(0,[z43,z0,z217,z2,z4,z5,z6]),(0,[z0,z46,z3,z20,z4,z5,z6]),(0,[z0,z2,z284,z20,z4,z5,z6]),(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z237,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z573,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z40])],[(0,[z0,z2,z3,z4,z5,z144,z64]),(0,[z9,z0,z155,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z574,z6]),(0,[z0,z2,z3,z4,z5,z575,z6])],[(1,[z0,z2,z3,z4,z5,z255]),(0,[z0,z3,z286,z4,z5,z71,z6]),(0,[z0,z2,z4,z62,z5,z6,z11])],[(0,[z0,z17,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z576,z6]),(0,[z0,z2,z3,z4,z5,z6,z425]),(0,[z0,z2,z107,z3,z4,z5,z52]),(0,[z577,z0,z2,z3,z4,z5,z6])],[(0,[z39,z328,z2,z3,z4,z5,z6]),(1,[z0,z2,z219,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z93,z6])],[(0,[z424,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z202,z4,z5,z6])],[(1,[z0,z217,z12,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z578,z6])],[(0,[z0,z3,z4,z31,z5,z6,z72]),(0,[z0,z2,z3,z4,z579,z5,z6]),(0,[z0,z2,z3,z59,z4,z5,z64])],[(0,[z0,z73,z3,z4,z31,z5,z6]),(0,[z117,z0,z495,z3,z4,z5,z6]),(0,[z0,z2,z495,z3,z4,z5,z6])],[(0,[z580,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z50,z210,z6]),(0,[z0,z2,z3,z4,z5,z6,z581]),(0,[z582,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z583,z3,z4,z5,z6]),(0,[z584,z0,z2,z3,z4,z5,z6])],[(0,[z413,z0,z3,z4,z5,z71,z6])],[(0,[z0,z53,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z162,z6]),(0,[z0,z2,z3,z4,z5,z6,z585])],[(0,[z586,z0,z2,z3,z4,z5,z6]),(0,[z348,z0,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z4,z62,z5,z144,z6]),(0,[z0,z2,z3,z4,z5,z587,z6])]],
   [[(0,[z588,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z92,z62,z5,z6]),(0,[z589,z0,z2,z3,z4,z5,z6])],[(0,[z133,z0,z3,z4,z31,z5,z6])],[(0,[z0,z590,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z591]),(0,[z0,z2,z3,z174,z210,z5,z6])],[(0,[z0,z2,z3,z4,z592,z5,z6]),(1,[z0,z2,z4,z5,z83,z6]),(0,[z0,z2,z3,z4,z5,z593,z6]),(0,[z0,z2,z3,z4,z5,z6,z438]),(1,[z0,z341,z3,z4,z5,z6]),(0,[z0,z3,z59,z4,z254,z5,z6])],[(0,[z0,z2,z3,z4,z210,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z80])],[(0,[z594,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z62,z5,z6])],[(0,[z0,z2,z3,z4,z5,z595,z6]),(0,[z454,z0,z3,z4,z31,z5,z6]),(0,[z9,z0,z3,z138,z4,z5,z6]),(0,[z596,z0,z2,z3,z4,z5,z6])],[(0,[z43,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z197,z6]),(0,[z0,z2,z3,z4,z5,z597,z6]),(0,[z598,z0,z2,z3,z4,z5,z6])],[(0,[z0,z155,z3,z4,z31,z5,z6]),(0,[z0,z2,z92,z3,z4,z5,z6]),(0,[z0,z2,z3,z599,z4,z5,z6]),(1,[z0,z115,z3,z4,z5,z6]),(0,[z0,z2,z125,z174,z4,z5,z6])],[(1,[z0,z3,z4,z5,z122,z6])],[(0,[z0,z2,z4,z62,z5,z6,z173]),(0,[z0,z2,z92,z107,z4,z5,z6])],[(0,[z600,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z41,z5,z6]),(0,[z601,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z62,z5,z6]),(0,[z343,z0,z2,z92,z4,z5,z6]),(0,[z602,z0,z2,z3,z4,z5,z6])],[(0,[z176,z0,z3,z4,z31,z5,z6]),(0,[z9,z0,z3,z59,z4,z5,z6]),(0,[z0,z328,z2,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z6,z40]),(0,[z0,z2,z3,z4,z5,z6,z198])],[(0,[z0,z2,z3,z4,z5,z71,z6]),(1,[z0,z86,z3,z4,z5,z6])],[(0,[z0,z2,z3,z59,z4,z5,z179])]],
   [[(0,[z603,z0,z2,z3,z4,z5,z6]),(0,[z604,z0,z2,z3,z4,z5,z6]),(0,[z43,z0,z2,z4,z62,z5,z6]),(0,[z0,z3,z4,z31,z50,z5,z6]),(0,[z605,z0,z2,z3,z4,z5,z6]),(0,[z119,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z516,z3,z4,z5,z6]),(0,[z0,z2,z3,z29,z4,z5,z179])],[(0,[z0,z2,z92,z4,z31,z5,z6]),(0,[z9,z0,z3,z174,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z6,z173]),(0,[z0,z2,z4,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z80])],[(0,[z9,z0,z3,z20,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z606,z6]),(0,[z0,z2,z3,z29,z4,z5,z6])],[(0,[z169,z0,z217,z2,z4,z5,z6]),(0,[z39,z0,z3,z4,z5,z71,z6])],[(0,[z607,z0,z2,z3,z4,z5,z6]),(0,[z70,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z4,z31,z62,z5,z6]),(0,[z608,z0,z2,z3,z4,z5,z6]),(0,[z166,z0,z2,z3,z4,z5,z6])],[(0,[z70,z0,z2,z3,z4,z93,z6]),(0,[z0,z61,z3,z4,z5,z71,z6]),(0,[z609,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z610,z5,z6]),(0,[z0,z2,z219,z3,z4,z5,z6]),(0,[z58,z116,z2,z3,z4,z5,z6]),(0,[z0,z611,z2,z3,z4,z5,z6])],[(0,[z9,z0,z2,z92,z4,z5,z6])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z137,z0,z46,z3,z4,z5,z6]),(0,[z0,z46,z2,z3,z31,z5,z6]),(0,[z0,z3,z4,z31,z5,z27,z6]),(0,[z0,z2,z3,z4,z5,z612,z6])],[(0,[z0,z178,z2,z3,z4,z5,z6]),(0,[z233,z2,z3,z4,z109,z5,z6]),(0,[z0,z2,z3,z4,z21,z5,z6]),(0,[z70,z0,z2,z92,z4,z5,z6])],[(0,[z0,z2,z3,z4,z613,z5,z6]),(0,[z0,z2,z3,z4,z530,z5,z6]),(1,[z0,z423,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z614,z6]),(0,[z0,z2,z3,z463,z4,z5,z6]),(0,[z0,z73,z2,z3,z4,z5,z71]),(0,[z117,z0,z2,z92,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z615]),(0,[z363,z0,z2,z4,z62,z5,z6])],[(0,[z0,z46,z14,z3,z4,z5,z6]),(0,[z0,z2,z616,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z160,z5,z6])],[(0,[z0,z61,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z617,z5,z6])],[(0,[z130,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z47,z4,z5,z6,z52])],[(0,[z76,z0,z3,z4,z31,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z71,z6,z438])],[(1,[z0,z2,z180,z4,z5,z6]),(0,[z447,z0,z2,z4,z62,z5,z6])],[(0,[z0,z3,z4,z31,z30,z5,z6])],[(0,[z0,z46,z3,z4,z5,z6,z52]),(0,[z0,z2,z107,z4,z62,z5,z6])],[],[(0,[z150,z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z618,z6]),(0,[z0,z2,z3,z4,z619,z5,z6])],[(0,[z130,z0,z2,z4,z62,z5,z6]),(0,[z0,z46,z3,z4,z50,z5,z6]),(1,[z0,z155,z3,z4,z200,z6]),(0,[z58,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z6,z620]),(1,[z0,z528,z3,z4,z5,z6]),(0,[z0,z161,z2,z3,z4,z5,z6])],[(1,[z0,z329,z3,z4,z5,z6]),(0,[z621,z0,z2,z3,z4,z5,z6])],[(0,[z133,z2,z3,z4,z5,z93,z6]),(0,[z0,z3,z4,z34,z5,z71,z6]),(0,[z0,z2,z186,z92,z4,z5,z6]),(0,[z0,z2,z4,z34,z5,z67,z6])],[(0,[z0,z2,z4,z62,z622,z5,z6]),(0,[z39,z0,z2,z3,z174,z5,z6])],[(0,[z0,z2,z47,z92,z4,z5,z6]),(0,[z0,z2,z3,z623,z4,z5,z6]),(1,[z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z624,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z430]),(0,[z0,z46,z81,z3,z4,z5,z6])],[(0,[z0,z46,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z625,z4,z5,z6])],[(0,[z325,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z626,z3,z4,z5,z6]),(0,[z0,z2,z627,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z50,z5,z6]),(0,[z163,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z27,z6]),(1,[z9,z0,z4,z62,z5,z6]),(0,[z169,z0,z3,z4,z5,z71,z6]),(0,[z0,z281,z2,z92,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z361]),(0,[z0,z2,z3,z4,z5,z6,z628]),(0,[z0,z46,z73,z3,z4,z5,z6]),(0,[z58,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z629,z5,z6])],[(0,[z0,z2,z3,z630,z4,z5,z6]),(0,[z0,z631,z2,z3,z4,z5,z6]),(0,[z251,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z632,z6])]],
   [[(1,[z364,z0,z2,z4,z5,z6]),(0,[z233,z0,z329,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z633])],[(0,[z0,z2,z47,z4,z34,z5,z6]),(1,[z9,z0,z92,z4,z5,z6])],[(0,[z0,z3,z4,z5,z71,z6,z173]),(0,[z58,z0,z2,z92,z4,z5,z6]),(0,[z634,z0,z2,z3,z4,z5,z6])],[(0,[z2,z3,z20,z4,z109,z5,z6]),(0,[z0,z2,z3,z4,z5,z555,z6]),(0,[z0,z217,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z5,z387])],[(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z555,z6,z72]),(0,[z243,z0,z2,z92,z4,z5,z6]),(0,[z636,z0,z2,z3,z4,z5,z6])],[(0,[z249,z0,z2,z3,z4,z5,z6]),(0,[z0,z217,z2,z107,z4,z5,z6]),(0,[z251,z0,z2,z147,z4,z5,z6]),(0,[z169,z0,z2,z4,z62,z5,z6])],[(0,[z637,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z34,z5,z6])],[],[(0,[z150,z9,z0,z3,z4,z5,z6]),(0,[z638,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z543,z6]),(0,[z0,z73,z2,z3,z4,z5,z173]),(0,[z0,z2,z59,z4,z62,z5,z6]),(1,[z223,z2,z3,z4,z5,z6])],[(0,[z0,z3,z20,z4,z5,z71,z6]),(0,[z0,z2,z3,z426,z4,z5,z6])],[(0,[z0,z2,z33,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z639,z5,z6]),(0,[z0,z2,z3,z4,z5,z170,z6]),(0,[z0,z2,z4,z205,z62,z5,z6]),(0,[z169,z0,z2,z3,z4,z162,z6])],[(0,[z0,z2,z3,z640,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z93,z6]),(0,[z135,z0,z2,z3,z4,z5,z6])],[],[(0,[z16,z0,z17,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z292])],[],[(0,[z0,z2,z3,z641,z4,z5,z6]),(0,[z0,z2,z3,z642,z4,z5,z6]),(0,[z0,z2,z3,z643,z4,z5,z6]),(0,[z644,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z103,z0,z3,z4,z31,z5,z6])],[(0,[z0,z2,z3,z645,z4,z5,z6]),(1,[z0,z2,z216,z4,z5,z6]),(0,[z364,z0,z2,z4,z5,z6,z72]),(0,[z0,z2,z3,z4,z5,z646,z6]),(1,[z0,z46,z3,z4,z5,z6]),(0,[z251,z0,z2,z463,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z140]),(0,[z0,z2,z4,z62,z5,z6,z52])],[(0,[z131,z0,z2,z4,z5,z67,z6]),(0,[z9,z0,z647,z3,z4,z5,z6])],[(0,[z0,z2,z3,z648,z4,z5,z6]),(0,[z0,z2,z649,z3,z4,z5,z6]),(0,[z650,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z4,z62,z50,z5,z6]),(0,[z9,z251,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z5,z218,z6]),(0,[z0,z651,z2,z3,z4,z5,z6])],[(0,[z0,z2,z92,z3,z62,z5,z6]),(1,[z148,z0,z3,z4,z5,z6])],[(0,[z652,z0,z2,z3,z4,z5,z6]),(0,[z133,z2,z3,z20,z4,z5,z6]),(0,[z0,z2,z647,z3,z4,z5,z6]),(0,[z243,z0,z423,z3,z4,z5,z6]),(0,[z0,z2,z14,z3,z4,z34,z6]),(1,[z0,z2,z3,z4,z160,z6]),(0,[z0,z653,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z654,z6])],[(0,[z655,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z6,z52])],[(0,[z9,z0,z3,z4,z5,z144,z6])],[(0,[z0,z2,z17,z4,z62,z5,z6]),(0,[z131,z0,z2,z47,z4,z5,z6]),(0,[z0,z656,z2,z3,z4,z5,z6]),(0,[z282,z0,z3,z4,z5,z6,z72]),(0,[z0,z2,z3,z657,z4,z5,z6])],[(1,[z0,z111,z3,z4,z5,z6]),(0,[z233,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z144,z179]),(0,[z0,z2,z525,z3,z4,z5,z6])],[(0,[z658,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z236]),(0,[z0,z659,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z5,z27,z6]),(0,[z0,z35,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z144,z6]),(0,[z0,z2,z3,z4,z5,z6,z660]),(0,[z0,z661,z2,z3,z4,z5,z6])],[(0,[z16,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z17,z92,z4,z5,z6]),(0,[z76,z43,z0,z2,z4,z5,z6]),(0,[z598,z0,z3,z4,z31,z5,z6]),(0,[z0,z155,z2,z3,z4,z200,z6]),(0,[z0,z2,z92,z4,z5,z6,z40])],[(0,[z0,z17,z3,z4,z5,z71,z6]),(0,[z0,z47,z3,z4,z31,z5,z6]),(0,[z0,z2,z3,z138,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z472]),(0,[z176,z0,z155,z3,z4,z5,z6]),(1,[z0,z3,z4,z254,z5,z6])],[(0,[z0,z2,z92,z4,z5,z575,z6]),(0,[z117,z0,z2,z3,z4,z210,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z662,z6]),(0,[z0,z46,z3,z4,z5,z6,z72]),(0,[z0,z14,z3,z4,z31,z5,z6]),(0,[z9,z0,z46,z3,z4,z5,z6])],[(0,[z176,z0,z2,z3,z4,z200,z6]),(1,[z0,z265,z3,z4,z5,z6])],[(1,[z0,z132,z3,z4,z5,z6]),(0,[z0,z2,z3,z157,z4,z5,z6])],[(0,[z0,z2,z3,z663,z4,z5,z6]),(0,[z150,z0,z3,z4,z31,z5,z6]),(0,[z0,z664,z2,z3,z4,z5,z6]),(0,[z233,z0,z111,z3,z4,z5,z6]),(0,[z252,z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z62,z5,z6])],[(0,[z117,z0,z46,z3,z4,z5,z6]),(0,[z0,z73,z3,z4,z5,z71,z6]),(0,[z0,z2,z4,z62,z34,z5,z6]),(0,[z0,z2,z3,z59,z4,z5,z6])],[(0,[z9,z117,z0,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z6,z40])],[(0,[z39,z0,z2,z3,z4,z5,z175])],[(0,[z43,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z665,z5,z6])],[(0,[z384,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z284,z4,z5,z6]),(0,[z0,z61,z2,z4,z5,z6,z52]),(0,[z0,z3,z138,z4,z31,z5,z6]),(0,[z9,z243,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z173]),(0,[z0,z2,z180,z3,z4,z5,z6]),(0,[z0,z2,z4,z34,z5,z162,z6]),(0,[z0,z2,z3,z174,z4,z5,z6])],[(0,[z0,z2,z3,z20,z4,z5,z6]),(0,[z150,z0,z2,z3,z4,z344,z6]),(0,[z0,z2,z193,z4,z50,z5,z6]),(0,[z9,z233,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z501,z4,z5,z6]),(0,[z0,z2,z174,z4,z62,z5,z6]),(0,[z0,z2,z3,z476,z4,z5,z6])],[(0,[z0,z2,z666,z3,z4,z5,z6]),(0,[z667,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z418,z5,z6]),(0,[z9,z0,z3,z4,z34,z5,z6]),(0,[z668,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z669]),(0,[z0,z2,z92,z4,z5,z162,z6])],[(0,[z9,z130,z0,z3,z4,z5,z6]),(0,[z0,z73,z2,z4,z62,z5,z6])],[(0,[z0,z178,z3,z4,z31,z5,z6]),(0,[z133,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z3,z4,z670,z5,z6]),(0,[z247,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z671]),(0,[z396,z0,z2,z3,z4,z5,z6])],[(1,[z0,z18,z2,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z50,z6]),(0,[z0,z46,z3,z12,z4,z5,z6]),(0,[z251,z0,z2,z3,z138,z5,z6]),(0,[z39,z0,z2,z4,z62,z5,z6])],[(0,[z43,z0,z61,z2,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z5,z6]),(0,[z9,z76,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z146,z5,z6]),(1,[z169,z0,z2,z4,z162,z6]),(0,[z0,z2,z4,z30,z5,z397,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z672]),(0,[z0,z2,z3,z4,z5,z6,z673]),(0,[z0,z271,z46,z3,z4,z5,z6]),(1,[z0,z2,z4,z280,z5,z6])],[(0,[z674,z0,z2,z3,z4,z5,z6])],[(0,[z675,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z92,z4,z5,z6])],[(0,[z131,z0,z2,z3,z4,z5,z6]),(0,[z0,z46,z3,z33,z4,z5,z6]),(0,[z70,z2,z3,z4,z109,z5,z6])],[(0,[z0,z217,z61,z3,z4,z5,z6]),(0,[z0,z61,z2,z92,z4,z5,z6]),(0,[z0,z2,z92,z4,z210,z5,z6])],[(0,[z676,z0,z2,z3,z4,z5,z6]),(0,[z0,z155,z3,z4,z5,z71,z6]),(0,[z0,z37,z3,z102,z4,z5,z6])],[(0,[z335,z0,z2,z3,z4,z5,z6]),(0,[z0,z478,z2,z3,z4,z5,z6]),(0,[z677,z0,z2,z3,z4,z5,z6]),(0,[z582,z9,z0,z3,z4,z5,z6]),(0,[z532,z0,z3,z4,z5,z71,z6]),(1,[z0,z180,z4,z5,z71,z6])],[(0,[z0,z2,z678,z3,z4,z5,z6])],[(0,[z2,z47,z3,z33,z4,z5,z6]),(0,[z0,z3,z4,z50,z5,z71,z6]),(0,[z103,z9,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z6,z52])],[(0,[z150,z0,z2,z3,z4,z5,z361]),(0,[z9,z70,z0,z3,z4,z5,z6]),(0,[z176,z0,z3,z4,z5,z71,z6]),(0,[z0,z14,z3,z4,z5,z71,z6])],[(0,[z0,z414,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z109,z31,z5,z6]),(0,[z0,z61,z2,z4,z34,z5,z6]),(1,[z119,z0,z3,z4,z5,z6]),(0,[z415,z0,z2,z3,z4,z5,z6])],[(0,[z133,z0,z2,z3,z109,z5,z6]),(0,[z0,z2,z3,z4,z5,z64,z72]),(0,[z0,z679,z2,z3,z4,z5,z6])],[(0,[z130,z0,z2,z92,z4,z5,z6]),(1,[z0,z2,z185,z4,z5,z6]),(0,[z680,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z92,z4,z5,z71,z6])],[(0,[z0,z2,z4,z62,z5,z6,z72]),(0,[z243,z0,z46,z3,z4,z5,z6])],[(0,[z0,z2,z3,z681,z4,z5,z6])]],
   [[(0,[z0,z682,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z683,z5,z6]),(0,[z0,z3,z4,z31,z200,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z526]),(0,[z0,z2,z102,z4,z62,z5,z6]),(0,[z0,z2,z92,z4,z5,z6,z80])],[(0,[z176,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z92,z29,z4,z5,z6])],[(0,[z0,z2,z3,z4,z684,z5,z6]),(0,[z2,z3,z4,z109,z5,z6,z72]),(0,[z0,z2,z3,z4,z685,z5,z6])],[(0,[z9,z401,z0,z3,z4,z5,z6]),(1,[z348,z2,z3,z4,z5,z6])],[(0,[z0,z2,z13,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z6,z72]),(0,[z0,z2,z3,z686,z4,z5,z6])],[(0,[z0,z2,z33,z4,z5,z6,z52]),(0,[z687,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z688,z4,z5,z6])],[(0,[z76,z131,z0,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z622,z5,z6]),(0,[z0,z2,z92,z4,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z689,z6]),(0,[z0,z2,z3,z690,z4,z5,z6]),(1,[z0,z2,z4,z5,z397,z6])],[(0,[z0,z2,z3,z691,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z692,z6]),(0,[z0,z217,z3,z4,z31,z5,z6])],[(0,[z0,z3,z4,z121,z5,z71,z6]),(0,[z0,z2,z3,z4,z5,z6,z693]),(0,[z0,z694,z2,z3,z4,z5,z6]),(0,[z695,z0,z2,z3,z4,z5,z6]),(0,[z235,z0,z2,z3,z4,z5,z6])],[(0,[z696,z0,z2,z3,z4,z5,z6]),(0,[z251,z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z697,z5,z6]),(0,[z0,z2,z3,z4,z698,z5,z6]),(0,[z699,z0,z2,z3,z4,z5,z6]),(0,[z700,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z305,z3,z4,z5,z6])],[(0,[z0,z46,z3,z4,z30,z5,z6]),(0,[z76,z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z432,z3,z4,z5,z6]),(0,[z701,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z702,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z703,z6]),(0,[z169,z0,z2,z92,z4,z5,z6]),(0,[z0,z2,z704,z3,z4,z5,z6]),(0,[z0,z191,z3,z59,z4,z5,z6])],[(0,[z0,z283,z2,z17,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z705]),(0,[z605,z9,z0,z3,z4,z5,z6]),(0,[z0,z341,z3,z4,z5,z6,z52])],[(0,[z150,z0,z383,z3,z4,z5,z6]),(0,[z251,z0,z2,z92,z4,z5,z6]),(0,[z0,z3,z4,z505,z31,z5,z6]),(0,[z0,z324,z46,z3,z4,z5,z6])],[(0,[z706,z0,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z9,z0,z4,z139,z5,z6]),(0,[z636,z0,z2,z3,z6,z40]),(0,[z0,z7,z3,z4,z160,z6])],[(0,[z0,z391,z4,z31,z5,z6]),(0,[z163,z0,z3,z4,z5,z179]),(0,[z0,z46,z4,z5,z707,z6])],[(0,[z137,z364,z2,z4,z5,z72]),(0,[z119,z0,z92,z4,z5,z6])],[(0,[z0,z2,z708,z4,z5,z6]),(0,[z0,z18,z4,z31,z5,z6]),(0,[z0,z709,z2,z4,z5,z6]),(0,[z0,z4,z297,z62,z5,z6]),(0,[z137,z2,z3,z4,z5,z710]),(0,[z163,z0,z3,z4,z5,z6]),(0,[z0,z711,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z64,z712])],[(0,[z713,z2,z3,z4,z5,z6]),(0,[z0,z2,z13,z4,z5,z255]),(0,[z0,z2,z714,z4,z5,z6]),(0,[z169,z0,z4,z31,z162,z6]),(0,[z715,z2,z3,z4,z5,z6]),(0,[z0,z161,z4,z62,z5,z6])],[(0,[z0,z2,z3,z4,z716,z5]),(0,[z2,z3,z4,z5,z6,z717])],[(0,[z0,z2,z3,z4,z5,z718]),(0,[z719,z0,z3,z4,z5,z6]),(0,[z0,z46,z3,z298,z5,z6]),(0,[z0,z59,z31,z62,z5,z6]),(0,[z0,z2,z4,z720,z5,z6]),(0,[z0,z3,z4,z721,z27,z6]),(0,[z9,z722,z3,z4,z5,z6]),(0,[z348,z2,z4,z62,z5,z6]),(0,[z0,z3,z4,z5,z723,z6])],[(0,[z0,z92,z4,z297,z5,z6]),(0,[z0,z46,z219,z4,z5,z6]),(0,[z0,z2,z92,z102,z5,z6]),(0,[z76,z0,z2,z4,z5,z724]),(0,[z0,z2,z3,z4,z5,z724])],[(0,[z0,z161,z92,z4,z5,z6]),(0,[z0,z107,z476,z4,z5,z67])],[(0,[z0,z2,z3,z4,z725,z6]),(0,[z0,z3,z118,z31,z5,z6]),(0,[z0,z3,z4,z31,z30,z80]),(0,[z223,z46,z3,z4,z5,z6]),(0,[z0,z46,z202,z4,z5,z6]),(0,[z0,z2,z107,z4,z5,z724]),(0,[z116,z2,z3,z4,z5,z179]),(0,[z117,z0,z2,z3,z726,z4])],[(0,[z0,z2,z426,z4,z5,z6]),(0,[z169,z0,z2,z4,z294,z6]),(0,[z474,z0,z2,z62,z5,z6]),(0,[z348,z2,z92,z4,z5,z6]),(0,[z727,z0,z3,z4,z5,z6]),(0,[z0,z728,z3,z4,z5,z6])],[(0,[z0,z3,z4,z31,z344,z6]),(0,[z116,z2,z3,z4,z5,z6]),(0,[z0,z729,z3,z4,z5,z6]),(0,[z3,z4,z31,z5,z6,z730]),(0,[z0,z53,z4,z258,z5,z6]),(0,[z0,z4,z254,z307,z5,z6])],[(0,[z0,z2,z731,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z732]),(0,[z176,z0,z4,z62,z27,z6])],[(0,[z0,z46,z4,z5,z6,z292])],[(0,[z0,z3,z4,z733,z5,z6]),(0,[z58,z0,z3,z5,z198,z179])]],
   [[(0,[z0,z3,z4,z734,z5,z6]),(0,[z0,z4,z5,z397,z71,z6])],[(0,[z0,z3,z4,z5,z735,z6]),(0,[z0,z407,z4,z5,z71,z6]),(0,[z0,z107,z4,z5,z67,z71]),(0,[z415,z2,z48,z4,z5,z6])],[(0,[z131,z2,z736,z4,z5,z6]),(0,[z0,z46,z216,z4,z5,z6]),(0,[z3,z737,z4,z5,z71,z6]),(0,[z0,z3,z4,z5,z6,z738])],[(0,[z9,z0,z4,z21,z5,z6]),(0,[z0,z2,z739,z4,z5,z6]),(0,[z58,z0,z46,z3,z5,z179]),(0,[z740,z2,z3,z4,z5,z6])],[(0,[z152,z3,z4,z93,z71,z6]),(0,[z0,z46,z3,z500,z5,z6]),(0,[z0,z104,z4,z62,z5,z6]),(0,[z0,z191,z4,z62,z5,z6]),(0,[z117,z0,z2,z3,z29,z4])],[(0,[z0,z2,z741,z4,z5,z6]),(0,[z0,z2,z4,z742,z5,z6]),(0,[z0,z2,z743,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z744]),(0,[z152,z124,z3,z4,z93,z6]),(0,[z0,z3,z4,z31,z5,z745]),(0,[z0,z220,z4,z146,z5,z6]),(0,[z0,z746,z92,z4,z5,z6])],[(0,[z473,z2,z3,z4,z93,z6]),(0,[z0,z3,z4,z5,z6,z747])],[(0,[z163,z0,z3,z4,z5,z67]),(0,[z247,z0,z3,z4,z6,z472]),(0,[z0,z46,z3,z4,z160,z6]),(0,[z0,z265,z219,z4,z5,z6])],[(0,[z0,z4,z31,z5,z6,z748]),(1,[z0,z2,z749,z5,z6]),(0,[z0,z2,z3,z4,z750,z6]),(0,[z0,z104,z92,z4,z5,z6]),(0,[z0,z3,z4,z751,z5,z6])],[(0,[z401,z178,z3,z4,z5,z6]),(0,[z9,z0,z305,z4,z5,z6]),(0,[z0,z73,z3,z4,z5,z752]),(0,[z0,z2,z4,z205,z34,z6]),(0,[z0,z753,z3,z4,z5,z6]),(0,[z223,z265,z3,z4,z5,z6]),(0,[z0,z265,z202,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z230]),(0,[z0,z2,z4,z5,z6,z748]),(0,[z9,z0,z3,z4,z754,z6]),(0,[z39,z328,z2,z3,z6,z40])],[(0,[z0,z3,z4,z31,z5,z361]),(0,[z0,z3,z4,z5,z6,z198]),(0,[z9,z0,z4,z307,z5,z6]),(0,[z0,z2,z194,z4,z5,z244]),(0,[z0,z191,z3,z59,z5,z64])],[(0,[z0,z3,z4,z5,z71,z6]),(0,[z0,z2,z755,z4,z5,z6]),(0,[z0,z2,z3,z756,z5,z6]),(0,[z0,z46,z4,z5,z6,z236]),(0,[z0,z2,z3,z4,z5,z757]),(0,[z0,z2,z3,z4,z5,z175])],[(0,[z152,z3,z4,z31,z93,z6]),(0,[z0,z2,z758,z4,z5,z6]),(0,[z9,z759,z3,z4,z5,z6]),(0,[z0,z760,z3,z4,z5,z6])],[(0,[z131,z2,z336,z4,z5,z6]),(0,[z0,z2,z639,z62,z5,z6]),(0,[z0,z516,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z761]),(0,[z0,z762,z3,z4,z5,z6])],[(0,[z0,z92,z4,z31,z5,z6]),(0,[z0,z256,z3,z4,z5,z71]),(0,[z9,z0,z313,z4,z5,z6]),(0,[z39,z223,z2,z3,z6,z40]),(0,[z58,z0,z2,z3,z5,z179])]],
   [[(0,[z0,z763,z2,z4,z5,z6]),(0,[z764,z0,z3,z4,z5,z6]),(0,[z58,z0,z2,z62,z5,z179])],[(0,[z0,z2,z3,z4,z344,z361]),(0,[z9,z765,z0,z4,z5,z6]),(0,[z766,z0,z3,z4,z5,z6]),(0,[z0,z4,z62,z5,z122,z6])],[(0,[z0,z767,z3,z4,z5,z6]),(0,[z0,z2,z147,z4,z5,z6]),(0,[z0,z4,z31,z62,z5,z6]),(0,[z176,z0,z108,z4,z27,z6])],[(0,[z0,z132,z216,z4,z5,z6]),(0,[z0,z3,z4,z768,z5,z6])],[(0,[z0,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z769,z6]),(0,[z70,z2,z193,z4,z50,z6]),(0,[z0,z2,z4,z62,z770,z6])],[(0,[z0,z2,z771,z4,z5,z6]),(0,[z0,z772,z3,z4,z5,z6]),(0,[z773,z0,z3,z4,z5,z6]),(0,[z0,z3,z174,z530,z5,z6]),(0,[z0,z3,z4,z774,z5,z6])],[(0,[z0,z202,z4,z31,z5,z6]),(0,[z0,z775,z4,z31,z5,z6]),(0,[z9,z0,z3,z4,z776,z6]),(0,[z0,z2,z92,z610,z5,z6])],[(0,[z0,z3,z4,z530,z5,z6]),(0,[z0,z86,z3,z4,z160,z6])],[(0,[z0,z2,z3,z4,z777,z6]),(0,[z137,z3,z4,z31,z5,z72]),(0,[z0,z778,z4,z5,z71,z6])],[(0,[z0,z2,z779,z4,z5,z6]),(0,[z0,z46,z284,z4,z5,z6]),(0,[z152,z153,z3,z4,z93,z6]),(0,[z0,z2,z780,z4,z5,z6]),(0,[z0,z2,z4,z5,z67,z724])],[(0,[z76,z0,z46,z4,z5,z52]),(0,[z781,z2,z3,z4,z5,z6]),(0,[z0,z2,z782,z4,z5,z6]),(0,[z0,z191,z276,z4,z5,z6])],[(0,[z0,z783,z3,z4,z5,z6]),(0,[z0,z108,z46,z4,z5,z6]),(0,[z0,z4,z5,z6,z322,z784]),(0,[z76,z0,z2,z4,z5,z15]),(0,[z0,z785,z3,z4,z5,z6]),(0,[z0,z2,z3,z59,z5,z64])],[(0,[z131,z2,z33,z4,z5,z6]),(0,[z2,z3,z4,z482,z5,z72]),(0,[z0,z3,z786,z4,z5,z6]),(0,[z0,z3,z4,z5,z787,z6]),(0,[z0,z3,z4,z788,z5,z6])],[(0,[z150,z2,z3,z756,z5,z6]),(0,[z0,z155,z3,z4,z10,z6]),(0,[z0,z789,z3,z4,z5,z6])],[(0,[z43,z47,z4,z31,z5,z6]),(0,[z0,z3,z4,z5,z790,z6]),(0,[z0,z791,z3,z4,z5,z6]),(0,[z0,z2,z792,z4,z5,z6]),(0,[z0,z2,z92,z4,z793,z6]),(0,[z0,z2,z92,z617,z5,z6]),(0,[z794,z0,z2,z4,z5,z6])],[(0,[z0,z3,z4,z5,z795,z6]),(0,[z0,z796,z46,z4,z5,z6]),(0,[z0,z37,z92,z102,z5,z6]),(0,[z797,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z798,z3,z4,z5,z6]),(0,[z0,z2,z799,z4,z5,z6]),(0,[z0,z271,z3,z4,z66,z6]),(0,[z0,z2,z4,z5,z6,z724])],[(0,[z800,z0,z2,z4,z5,z6]),(0,[z364,z0,z4,z5,z71,z6]),(0,[z0,z92,z4,z5,z63,z6]),(0,[z0,z46,z4,z280,z5,z6]),(0,[z9,z0,z190,z4,z5,z6]),(0,[z9,z0,z3,z4,z30,z80]),(0,[z0,z2,z92,z45,z5,z6])],[(0,[z0,z3,z530,z109,z5,z6]),(0,[z0,z801,z3,z4,z5,z6]),(0,[z70,z2,z3,z4,z50,z6]),(0,[z0,z220,z12,z4,z5,z6]),(0,[z2,z802,z3,z4,z5,z6])],[(0,[z393,z0,z3,z31,z5,z6]),(0,[z2,z47,z736,z4,z5,z6]),(0,[z9,z0,z3,z4,z344,z6]),(0,[z0,z803,z4,z5,z71,z6]),(0,[z0,z3,z4,z804,z5,z6])],[(0,[z0,z2,z805,z4,z5,z6]),(0,[z0,z2,z3,z806,z5,z6])],[(0,[z0,z478,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z197,z6]),(0,[z0,z426,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z5,z807]),(0,[z808,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z30,z71,z80]),(0,[z0,z2,z809,z4,z5,z6]),(0,[z577,z0,z2,z3,z29,z4])],[(0,[z0,z2,z778,z4,z5,z6]),(0,[z131,z278,z2,z4,z5,z6]),(0,[z0,z383,z3,z4,z344,z6]),(0,[z76,z0,z2,z4,z5,z52])],[(0,[z713,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z810]),(0,[z0,z2,z811,z4,z5,z6]),(0,[z0,z812,z3,z4,z5,z6]),(0,[z0,z108,z2,z4,z5,z6]),(0,[z0,z3,z4,z813,z5,z6]),(0,[z396,z0,z2,z4,z575,z6]),(0,[z328,z2,z3,z4,z5,z387])],[(0,[z0,z2,z814,z4,z5,z6]),(0,[z0,z775,z4,z5,z63,z6])],[],[(0,[z277,z0,z2,z3,z6,z40]),(0,[z0,z3,z4,z5,z815,z6])],[(0,[z0,z2,z816,z4,z5,z6]),(1,[z2,z736,z4,z5,z6]),(0,[z0,z2,z3,z4,z817,z6]),(0,[z0,z796,z2,z4,z5,z6])],[(0,[z150,z2,z3,z109,z5,z6]),(0,[z0,z3,z4,z818,z5,z6]),(0,[z0,z2,z819,z4,z5,z6])],[(0,[z0,z2,z820,z4,z5,z6]),(0,[z0,z217,z4,z146,z5,z6]),(0,[z0,z92,z4,z5,z429,z6]),(0,[z0,z73,z4,z62,z5,z71])],[(0,[z821,z0,z3,z4,z5,z6]),(0,[z0,z46,z185,z4,z5,z6]),(0,[z0,z3,z4,z31,z5,z387]),(0,[z424,z128,z3,z4,z5,z6]),(0,[z0,z46,z3,z507,z5,z6]),(0,[z0,z822,z2,z4,z5,z6]),(0,[z248,z0,z3,z4,z165,z6]),(0,[z0,z823,z3,z4,z5,z6])],[(0,[z0,z2,z92,z448,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z710]),(0,[z0,z155,z3,z4,z66,z6])],[(0,[z0,z3,z4,z5,z555,z6]),(0,[z0,z2,z824,z4,z5,z6]),(0,[z0,z2,z92,z222,z5,z6]),(0,[z0,z276,z4,z254,z5,z6])],[(0,[z0,z2,z4,z5,z825,z6]),(0,[z9,z0,z3,z4,z5,z526]),(0,[z9,z0,z4,z5,z6,z438]),(0,[z826,z0,z3,z4,z5,z6]),(0,[z116,z2,z313,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z361]),(0,[z0,z827,z2,z4,z5,z6]),(0,[z233,z2,z3,z4,z5,z144]),(0,[z9,z0,z391,z4,z5,z6]),(0,[z249,z35,z3,z4,z5,z6]),(0,[z0,z828,z3,z4,z5,z6]),(0,[z0,z2,z92,z749,z5,z6]),(0,[z0,z3,z4,z5,z829,z175]),(0,[z0,z2,z4,z5,z830,z6])],[(0,[z0,z831,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z710]),(0,[z267,z0,z3,z4,z5,z71]),(0,[z0,z2,z4,z5,z6,z832])],[(0,[z0,z3,z4,z5,z6,z833]),(0,[z0,z3,z4,z295,z5,z63]),(0,[z0,z2,z4,z5,z834,z6]),(0,[z0,z3,z4,z835,z5,z6])],[(0,[z0,z383,z3,z4,z5,z361]),(0,[z0,z2,z836,z4,z5,z6]),(0,[z837,z2,z3,z4,z5,z6]),(0,[z0,z838,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z839]),(0,[z0,z281,z186,z4,z5,z6])],[(0,[z0,z840,z3,z4,z5,z6])],[(0,[z0,z2,z4,z841,z5,z6]),(0,[z695,z2,z47,z4,z5,z6]),(0,[z0,z46,z4,z5,z397,z6])],[(0,[z0,z495,z3,z4,z5,z6]),(0,[z0,z842,z2,z4,z5,z6]),(0,[z0,z843,z3,z4,z5,z6])],[(0,[z0,z3,z4,z31,z716,z5])],[(0,[z0,z2,z4,z844,z5,z6]),(0,[z117,z0,z46,z3,z29,z4]),(0,[z0,z2,z4,z5,z6,z845])],[(0,[z0,z2,z846,z4,z5,z6]),(0,[z0,z2,z4,z847,z5,z6]),(0,[z0,z2,z4,z205,z373,z6]),(0,[z0,z37,z4,z62,z5,z6]),(0,[z0,z2,z14,z4,z34,z6])],[(0,[z0,z3,z4,z848,z5,z6]),(0,[z39,z0,z2,z202,z6,z40])],[(0,[z0,z2,z3,z4,z849,z6])],[(0,[z9,z152,z3,z4,z93,z6]),(0,[z227,z0,z3,z31,z5,z6]),(0,[z9,z0,z3,z4,z5,z71]),(0,[z0,z2,z850,z4,z5,z6]),(0,[z0,z7,z3,z4,z78,z6]),(0,[z0,z2,z4,z851,z5,z6])]],
   [[(0,[z852,z2,z3,z4,z5,z6])],[(0,[z0,z853,z3,z4,z5,z6])],[(0,[z529,z0,z2,z62,z5,z6]),(0,[z0,z2,z3,z5,z6,z712])],[(0,[z0,z854,z3,z4,z5,z6])],[(0,[z0,z46,z13,z4,z5,z6]),(0,[z0,z185,z4,z5,z71,z6]),(0,[z176,z0,z92,z4,z27,z6]),(0,[z348,z86,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z255]),(0,[z0,z3,z4,z344,z71,z6]),(0,[z0,z2,z855,z4,z5,z6]),(0,[z148,z0,z4,z5,z6,z292])],[(0,[z364,z0,z4,z5,z555,z6]),(0,[z0,z2,z856,z4,z5,z6])],[(0,[z243,z0,z423,z62,z5,z6])],[(0,[z0,z61,z81,z4,z5,z6]),(0,[z9,z0,z463,z4,z5,z6]),(0,[z0,z2,z857,z4,z5,z6]),(0,[z0,z3,z4,z5,z858,z6]),(0,[z0,z859,z3,z4,z5,z6])],[(0,[z860,z0,z3,z4,z5,z6]),(0,[z861,z0,z2,z4,z5,z6])],[(0,[z16,z35,z3,z4,z5,z6]),(0,[z0,z3,z4,z862,z5,z6]),(0,[z0,z2,z4,z863,z5,z6]),(0,[z0,z217,z12,z4,z5,z6]),(0,[z0,z155,z3,z4,z721,z6]),(0,[z328,z3,z4,z5,z71,z6]),(0,[z0,z92,z4,z460,z5,z6])],[(0,[z0,z61,z476,z4,z5,z6]),(0,[z163,z0,z3,z4,z5,z430]),(0,[z0,z191,z92,z4,z5,z6])],[(0,[z0,z14,z4,z31,z34,z6]),(0,[z0,z2,z4,z5,z6,z784])],[(0,[z494,z2,z47,z4,z5,z6]),(0,[z0,z864,z3,z4,z5,z6]),(0,[z0,z391,z4,z5,z71,z6]),(0,[z0,z865,z3,z4,z5,z6])],[],[(0,[z0,z18,z4,z5,z71,z6]),(0,[z866,z0,z2,z4,z5,z6]),(0,[z0,z3,z4,z867,z5,z6]),(0,[z0,z868,z3,z4,z5,z6])]],
   [[(0,[z0,z869,z3,z4,z5,z6]),(0,[z0,z525,z4,z31,z5,z6]),(0,[z9,z0,z870,z4,z5,z6]),(0,[z9,z0,z871,z4,z5,z6]),(0,[z872,z2,z3,z4,z5,z6])],[(0,[z0,z124,z4,z62,z5,z6]),(0,[z151,z2,z3,z4,z5,z144]),(0,[z0,z61,z799,z4,z5,z6]),(0,[z0,z61,z647,z4,z5,z6])],[(0,[z0,z4,z21,z5,z71,z6]),(0,[z0,z873,z3,z4,z5,z6]),(0,[z0,z3,z31,z5,z6,z68]),(0,[z0,z3,z286,z31,z5,z6]),(0,[z874,z0,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z875,z6]),(0,[z0,z3,z4,z31,z5,z761]),(0,[z288,z324,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z876]),(0,[z0,z3,z4,z197,z71,z6]),(0,[z2,z3,z4,z756,z5,z6]),(0,[z9,z0,z276,z4,z5,z6]),(0,[z0,z180,z4,z5,z6,z322]),(0,[z0,z877,z4,z5,z71,z6]),(0,[z0,z2,z92,z62,z5,z6])],[(0,[z0,z132,z13,z4,z5,z6]),(0,[z0,z46,z92,z138,z5,z6]),(0,[z878,z0,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z752]),(0,[z0,z2,z4,z30,z292,z80])],[(0,[z43,z2,z4,z188,z5,z6]),(0,[z0,z4,z31,z5,z83,z6]),(0,[z0,z3,z4,z5,z6,z879]),(0,[z0,z46,z3,z4,z78,z6]),(0,[z880,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z387]),(0,[z0,z881,z4,z5,z71,z6]),(0,[z0,z882,z3,z4,z5,z6]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z0,z2,z884,z4,z5,z6])],[(0,[z0,z885,z3,z4,z5,z6]),(0,[z0,z3,z476,z4,z5,z6]),(0,[z0,z3,z4,z886,z5,z6]),(0,[z0,z4,z306,z280,z5,z6])],[(0,[z0,z2,z887,z4,z5,z6]),(0,[z0,z2,z4,z5,z83,z6]),(0,[z0,z2,z888,z4,z5,z6]),(0,[z0,z341,z3,z4,z5,z6]),(0,[z0,z2,z525,z4,z5,z6]),(0,[z0,z2,z3,z4,z175,z40])],[(0,[z408,z0,z3,z4,z5,z71]),(0,[z0,z2,z4,z889,z5,z6]),(0,[z0,z3,z20,z530,z5,z6]),(0,[z0,z2,z4,z5,z6,z890]),(0,[z235,z0,z4,z62,z5,z6])],[(0,[z0,z46,z891,z4,z5,z6]),(1,[z0,z2,z4,z892,z6]),(0,[z893,z0,z3,z4,z5,z6])],[(0,[z0,z2,z92,z4,z5,z6]),(0,[z9,z0,z407,z4,z5,z6]),(0,[z9,z894,z3,z4,z5,z6]),(0,[z0,z4,z280,z5,z71,z6]),(0,[z0,z4,z460,z62,z5,z6]),(0,[z0,z3,z895,z4,z5,z6])],[(0,[z0,z2,z3,z896,z5,z6]),(0,[z0,z2,z4,z897,z5,z6]),(0,[z0,z2,z4,z5,z6,z898]),(0,[z0,z2,z4,z899,z5,z6])],[(0,[z0,z2,z3,z4,z900,z6]),(0,[z0,z3,z4,z5,z901,z6]),(0,[z0,z2,z3,z5,z6,z902]),(0,[z0,z3,z799,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z173]),(0,[z58,z0,z3,z5,z6,z322]),(0,[z0,z2,z903,z4,z5,z6]),(0,[z235,z0,z92,z4,z5,z6]),(0,[z0,z904,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z905])],[(0,[z0,z906,z3,z4,z5,z6]),(0,[z0,z2,z107,z4,z5,z416]),(0,[z0,z219,z4,z31,z5,z6]),(0,[z0,z180,z4,z31,z5,z6]),(0,[z0,z3,z4,z907,z5,z6])],[(0,[z0,z908,z3,z4,z5,z6]),(0,[z0,z2,z909,z4,z5,z6]),(0,[z910,z0,z3,z4,z31,z6]),(0,[z0,z2,z803,z4,z5,z6]),(0,[z0,z2,z4,z911,z5,z6])]],
   [[(0,[z0,z912,z3,z4,z5,z6]),(0,[z0,z913,z3,z4,z5,z6]),(0,[z0,z3,z4,z914,z5,z6]),(0,[z0,z2,z3,z4,z5,z915]),(0,[z0,z92,z62,z5,z71,z6]),(0,[z348,z7,z3,z4,z5,z6])],[(0,[z0,z4,z5,z71,z6,z438]),(0,[z0,z4,z62,z5,z6,z916])],[(0,[z0,z2,z3,z917,z5,z6]),(0,[z137,z2,z426,z4,z5,z72])],[(0,[z918,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z919])],[(0,[z9,z0,z92,z102,z5,z6]),(0,[z0,z3,z4,z920,z71,z6]),(0,[z0,z3,z286,z5,z63,z6])],[(0,[z0,z153,z4,z62,z5,z6]),(0,[z9,z0,z3,z4,z5,z673]),(0,[z58,z0,z3,z31,z5,z179]),(0,[z0,z2,z4,z921,z5,z6]),(0,[z0,z4,z922,z5,z71,z6]),(0,[z2,z4,z62,z5,z6,z923]),(0,[z0,z3,z4,z5,z924,z6]),(0,[z0,z2,z4,z5,z6,z925])],[(0,[z0,z2,z926,z4,z5,z6]),(0,[z0,z2,z927,z4,z5,z6]),(0,[z163,z117,z0,z3,z4,z5]),(0,[z0,z46,z125,z4,z5,z6]),(0,[z0,z928,z3,z4,z5,z6]),(0,[z0,z86,z3,z4,z78,z6])],[(0,[z0,z3,z4,z5,z71,z361]),(0,[z0,z2,z4,z5,z929,z6]),(0,[z0,z2,z3,z4,z5,z930]),(0,[z70,z3,z4,z31,z50,z6]),(0,[z9,z0,z426,z4,z5,z6]),(0,[z0,z2,z4,z931,z5,z6]),(0,[z0,z3,z4,z932,z5,z6]),(0,[z163,z0,z3,z4,z30,z5]),(0,[z0,z2,z3,z933,z5,z6]),(0,[z0,z3,z4,z5,z934,z6]),(0,[z935,z2,z3,z4,z5,z6])],[(0,[z2,z3,z756,z109,z5,z6]),(0,[z0,z2,z3,z936,z5,z6]),(0,[z0,z2,z937,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z545])],[(0,[z0,z2,z938,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z939]),(0,[z0,z153,z92,z4,z5,z6])],[(0,[z0,z92,z4,z5,z6,z198]),(0,[z0,z940,z3,z4,z5,z6])],[(0,[z941,z0,z3,z4,z5,z6]),(0,[z0,z92,z4,z5,z71,z6]),(0,[z0,z942,z4,z5,z6,z322])],[(0,[z0,z2,z3,z4,z943,z6])],[(0,[z0,z944,z3,z4,z5,z6]),(0,[z0,z2,z4,z945,z5,z6]),(0,[z0,z423,z3,z4,z5,z6]),(0,[z9,z0,z4,z5,z71,z438]),(0,[z532,z0,z4,z5,z6,z438]),(0,[z0,z2,z3,z4,z5,z946]),(0,[z0,z947,z3,z4,z5,z6])],[(0,[z0,z3,z4,z948,z31,z5])],[(0,[z0,z2,z3,z4,z5,z949]),(0,[z0,z2,z4,z62,z5,z361]),(0,[z0,z2,z4,z5,z6,z950]),(0,[z237,z0,z2,z4,z5,z15]),(0,[z116,z2,z305,z4,z5,z6])]],
   [[(0,[z0,z951,z3,z4,z5,z6]),(0,[z0,z53,z81,z4,z5,z6]),(0,[z0,z180,z4,z5,z63,z6]),(0,[z0,z952,z4,z5,z71,z6])],[(0,[z152,z2,z4,z62,z93,z6]),(0,[z137,z2,z391,z4,z5,z72]),(0,[z0,z953,z2,z4,z5,z6])],[(0,[z43,z2,z47,z4,z5,z6]),(0,[z954,z0,z3,z4,z5,z6]),(0,[z0,z202,z4,z5,z71,z6]),(0,[z0,z775,z4,z5,z71,z6]),(0,[z169,z0,z2,z4,z892,z6])],[(0,[z910,z0,z2,z3,z4,z6]),(0,[z0,z955,z2,z4,z5,z6])],[(0,[z0,z2,z956,z4,z5,z6]),(0,[z0,z3,z4,z5,z957,z6]),(0,[z137,z3,z4,z5,z71,z72]),(0,[z0,z3,z138,z848,z5,z6]),(0,[z0,z73,z92,z4,z5,z71]),(0,[z0,z2,z4,z527,z162,z6])],[(0,[z0,z2,z4,z958,z5,z6])],[(0,[z0,z51,z4,z5,z6,z438]),(0,[z0,z92,z4,z530,z5,z6]),(0,[z959,z0,z3,z4,z5,z6])],[(0,[z674,z178,z3,z4,z5,z6]),(0,[z348,z46,z3,z4,z5,z6]),(0,[z413,z3,z4,z5,z60,z6]),(0,[z960,z2,z3,z4,z5,z6])],[(0,[z0,z217,z626,z4,z5,z6]),(0,[z364,z0,z46,z4,z5,z6]),(0,[z233,z3,z4,z31,z5,z144]),(0,[z0,z3,z4,z961,z5,z6]),(0,[z0,z31,z62,z5,z6,z179])],[(0,[z0,z3,z4,z505,z200,z6]),(0,[z9,z0,z3,z4,z5,z175]),(0,[z0,z3,z4,z962,z5,z6]),(0,[z0,z3,z4,z963,z5,z6])],[(0,[z0,z2,z3,z4,z5,z964]),(0,[z2,z736,z3,z4,z5,z6]),(0,[z43,z47,z4,z5,z71,z6]),(0,[z0,z13,z4,z31,z5,z6]),(0,[z2,z3,z4,z5,z710,z72]),(0,[z117,z0,z2,z29,z4,z62]),(0,[z0,z2,z92,z174,z210,z6])],[(0,[z0,z329,z3,z4,z5,z6]),(0,[z79,z0,z4,z31,z5,z6]),(0,[z0,z3,z4,z5,z965,z6])],[(0,[z0,z3,z4,z966,z5,z6]),(0,[z0,z827,z153,z4,z5,z6]),(0,[z0,z2,z3,z4,z967,z6]),(0,[z348,z2,z3,z4,z160,z6])],[(0,[z76,z0,z2,z4,z5,z250]),(0,[z0,z968,z3,z4,z5,z6])],[(0,[z0,z51,z4,z41,z5,z6]),(0,[z0,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z969,z5]),(0,[z0,z970,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z971]),(0,[z133,z2,z3,z4,z197,z6]),(0,[z9,z0,z147,z4,z5,z6]),(0,[z9,z328,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z972])]],
   [[(0,[z0,z2,z4,z5,z6,z973]),(0,[z0,z305,z4,z31,z5,z6]),(0,[z0,z2,z4,z922,z5,z6])],[(0,[z0,z426,z4,z5,z71,z6]),(0,[z137,z2,z4,z5,z236,z72]),(0,[z9,z0,z4,z62,z5,z6])],[(0,[z16,z18,z17,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z705]),(0,[z0,z46,z3,z508,z5,z6]),(0,[z0,z2,z974,z4,z5,z6]),(0,[z975,z0,z3,z4,z5,z6]),(0,[z0,z3,z59,z254,z5,z64])],[(0,[z116,z3,z4,z31,z5,z6]),(0,[z0,z37,z92,z4,z5,z6])],[(0,[z364,z0,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z67,z318]),(0,[z0,z383,z4,z62,z5,z6]),(0,[z0,z2,z4,z976,z5,z6]),(0,[z977,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z29,z726,z4])],[(0,[z978,z0,z3,z4,z5,z6]),(0,[z58,z0,z2,z313,z5,z179])],[(0,[z0,z979,z3,z4,z5,z6])],[(0,[z0,z2,z92,z533,z5,z6]),(0,[z0,z2,z980,z4,z5,z6]),(0,[z0,z46,z193,z4,z5,z6]),(0,[z0,z2,z4,z981,z5,z6])],[(0,[z9,z0,z3,z4,z5,z15]),(0,[z9,z0,z3,z59,z5,z64])],[(0,[z0,z3,z4,z982,z5,z6]),(0,[z166,z0,z3,z4,z27,z6])],[(0,[z0,z983,z3,z4,z5,z6]),(0,[z0,z984,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z387]),(0,[z0,z2,z219,z4,z5,z6]),(0,[z0,z3,z4,z985,z5,z6]),(0,[z0,z2,z986,z4,z5,z6]),(0,[z0,z2,z4,z987,z5,z6])],[(0,[z251,z0,z3,z530,z5,z6])],[(0,[z223,z2,z3,z4,z5,z6]),(0,[z0,z2,z202,z4,z5,z6]),(0,[z328,z2,z3,z4,z6,z40]),(0,[z0,z2,z3,z4,z78,z64]),(0,[z117,z0,z495,z3,z29,z4])],[(0,[z70,z3,z4,z50,z71,z6]),(0,[z0,z4,z5,z71,z6,z832]),(0,[z328,z2,z3,z4,z5,z175]),(0,[z0,z3,z4,z988,z5,z6])],[(0,[z327,z2,z33,z4,z5,z6]),(0,[z0,z989,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z990,z6]),(0,[z0,z51,z799,z4,z5,z6])],[(0,[z0,z991,z3,z4,z5,z6]),(0,[z0,z4,z31,z5,z6,z292])]],
   [[(0,[z0,z92,z4,z5,z555,z6]),(0,[z0,z2,z3,z4,z992,z6])],[(0,[z0,z283,z4,z31,z5,z6]),(0,[z0,z2,z65,z62,z5,z6]),(0,[z0,z2,z4,z993,z5,z6]),(0,[z9,z0,z3,z4,z5,z49]),(0,[z9,z0,z3,z806,z5,z6]),(0,[z0,z2,z92,z55,z5,z6]),(0,[z0,z2,z4,z5,z6,z292]),(0,[z0,z2,z4,z994,z5,z6])],[(0,[z9,z0,z3,z4,z197,z6]),(0,[z0,z995,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z387,z40]),(0,[z117,z0,z2,z3,z77,z4])],[(0,[z9,z0,z3,z4,z5,z538]),(0,[z0,z478,z4,z21,z5,z6]),(0,[z0,z217,z326,z4,z5,z6])],[(0,[z251,z0,z463,z31,z5,z6]),(0,[z0,z3,z4,z31,z5,z175]),(0,[z247,z0,z3,z4,z27,z6]),(0,[z0,z2,z62,z5,z6,z238])],[(0,[z0,z46,z3,z4,z5,z6]),(0,[z0,z2,z216,z4,z5,z6]),(0,[z0,z383,z3,z4,z197,z6]),(0,[z0,z2,z996,z4,z5,z6]),(0,[z0,z2,z3,z4,z997,z6]),(0,[z998,z2,z3,z4,z5,z6]),(0,[z328,z2,z4,z62,z5,z6])],[(0,[z0,z999,z2,z4,z5,z6]),(0,[z0,z2,z92,z118,z5,z6]),(0,[z9,z0,z108,z4,z5,z6])],[(0,[z0,z1000,z3,z4,z5,z6]),(0,[z0,z1001,z3,z4,z5,z6]),(0,[z529,z0,z3,z31,z5,z6]),(0,[z0,z46,z3,z530,z5,z6]),(0,[z117,z0,z161,z3,z29,z4])],[(0,[z0,z124,z92,z4,z5,z6]),(0,[z282,z0,z4,z62,z5,z6])],[(0,[z9,z0,z3,z4,z365,z5]),(0,[z0,z2,z92,z89,z5,z6]),(0,[z328,z2,z92,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z752]),(0,[z0,z2,z3,z4,z160,z6])],[(0,[z130,z178,z4,z62,z5,z6])],[(0,[z0,z2,z4,z1002,z5,z6]),(0,[z0,z2,z1003,z4,z5,z6]),(0,[z0,z313,z4,z31,z5,z6]),(0,[z0,z3,z530,z5,z64,z6])],[(0,[z9,z137,z3,z4,z5,z72]),(0,[z0,z4,z31,z5,z6,z236]),(0,[z163,z0,z3,z4,z5,z71]),(0,[z1004,z2,z3,z4,z5,z6])],[(0,[z0,z46,z3,z691,z5,z6]),(0,[z0,z111,z3,z4,z5,z6]),(0,[z0,z2,z4,z1005,z5,z6]),(0,[z0,z1006,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z236]),(0,[z0,z3,z394,z31,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1007,z6]),(0,[z0,z1008,z3,z4,z5,z6]),(0,[z0,z115,z3,z4,z5,z6]),(0,[z0,z46,z4,z5,z26,z6]),(0,[z0,z2,z4,z62,z30,z80]),(0,[z0,z2,z102,z749,z5,z6])],[(0,[z0,z2,z4,z1009,z5,z6]),(0,[z0,z392,z3,z4,z5,z429]),(0,[z0,z3,z4,z5,z122,z6])],[(0,[z0,z293,z3,z31,z5,z6]),(0,[z0,z2,z1010,z4,z5,z6]),(0,[z0,z2,z4,z62,z344,z6])],[(0,[z0,z1011,z3,z4,z5,z6]),(0,[z0,z2,z1012,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1013]),(0,[z0,z2,z4,z5,z6,z1014])],[(0,[z1015,z0,z3,z4,z5,z6]),(0,[z0,z2,z92,z4,z30,z80]),(0,[z0,z3,z1016,z4,z5,z6]),(0,[z0,z104,z4,z280,z5,z6]),(0,[z0,z3,z4,z1017,z5,z6])],[(0,[z70,z2,z407,z4,z50,z6]),(0,[z0,z265,z3,z4,z5,z6]),(0,[z0,z86,z3,z4,z5,z6]),(0,[z9,z76,z0,z4,z5,z52])],[(0,[z0,z132,z3,z4,z5,z6]),(0,[z0,z2,z92,z4,z344,z6]),(0,[z675,z2,z3,z4,z5,z72]),(0,[z0,z4,z5,z71,z6,z748]),(0,[z0,z2,z3,z4,z80,z68])],[(0,[z0,z2,z263,z62,z5,z6]),(0,[z0,z3,z4,z5,z587,z71]),(0,[z9,z0,z92,z4,z5,z244])],[(0,[z0,z1018,z3,z4,z5,z6]),(0,[z0,z1019,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z120])],[(0,[z0,z1020,z2,z4,z5,z6]),(0,[z0,z2,z1021,z4,z5,z6]),(0,[z9,z0,z4,z847,z5,z6]),(0,[z9,z0,z14,z4,z34,z6]),(0,[z0,z2,z1022,z4,z5,z6])],[(1,[z713,z3,z4,z5,z6]),(0,[z0,z217,z4,z5,z6,z215]),(0,[z0,z3,z4,z1023,z31,z6])],[(0,[z0,z46,z107,z4,z5,z67]),(0,[z9,z0,z3,z4,z849,z6])],[(0,[z0,z2,z284,z4,z5,z6]),(0,[z0,z525,z4,z5,z71,z6]),(0,[z0,z2,z1024,z4,z5,z6])],[(0,[z0,z3,z4,z31,z197,z6]),(0,[z277,z2,z3,z109,z5,z6]),(0,[z0,z46,z4,z139,z5,z6])],[(0,[z163,z0,z3,z4,z5,z52]),(0,[z0,z1025,z4,z5,z71,z6])],[(0,[z0,z4,z31,z5,z6,z1026])]],
   [[(0,[z0,z46,z3,z431,z5,z6]),(0,[z0,z2,z92,z4,z5,z745])],[(0,[z251,z0,z3,z848,z5,z6]),(0,[z0,z1027,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1026]),(0,[z176,z0,z3,z4,z543,z6]),(0,[z0,z73,z3,z4,z5,z429]),(0,[z0,z2,z1028,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z255]),(0,[z0,z147,z4,z31,z5,z6]),(0,[z0,z4,z31,z280,z5,z6]),(0,[z0,z1029,z2,z4,z5,z6])],[(0,[z0,z2,z1030,z4,z5,z6]),(0,[z0,z3,z4,z5,z1031,z6]),(0,[z0,z3,z4,z5,z1032,z6]),(0,[z0,z92,z31,z62,z5,z6]),(0,[z135,z0,z3,z530,z5,z6]),(0,[z169,z0,z2,z4,z162,z6]),(0,[z0,z2,z1033,z4,z5,z6])],[(0,[z16,z713,z3,z4,z5,z6]),(0,[z0,z4,z254,z62,z5,z6])],[(0,[z0,z383,z3,z4,z5,z255]),(0,[z9,z0,z3,z4,z229,z5]),(0,[z0,z1034,z3,z4,z5,z6]),(0,[z0,z2,z1035,z4,z5,z6]),(0,[z9,z0,z857,z4,z5,z6]),(0,[z1036,z0,z3,z4,z5,z6]),(0,[z0,z4,z5,z71,z6,z898]),(0,[z0,z7,z313,z4,z5,z6])],[(0,[z0,z2,z3,z4,z6,z1037]),(0,[z0,z2,z1038,z4,z5,z6]),(0,[z0,z2,z92,z4,z5,z361]),(0,[z0,z92,z476,z4,z5,z6])],[(0,[z0,z553,z3,z4,z5,z71]),(0,[z0,z2,z3,z4,z1039,z6]),(0,[z0,z2,z1040,z4,z5,z6]),(0,[z0,z2,z1041,z4,z5,z6]),(0,[z0,z2,z3,z681,z5,z64]),(0,[z1042,z2,z3,z4,z5,z6])],[(0,[z0,z2,z736,z4,z5,z6]),(0,[z152,z2,z92,z4,z93,z6]),(0,[z0,z2,z180,z4,z5,z6]),(0,[z0,z3,z4,z5,z1043,z6])],[(0,[z1044,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1045]),(0,[z0,z2,z4,z5,z67,z291])],[(0,[z150,z2,z3,z109,z344,z6]),(0,[z0,z180,z4,z5,z71,z6]),(0,[z0,z219,z4,z5,z71,z6]),(0,[z0,z3,z4,z30,z122,z80])],[(0,[z131,z661,z2,z4,z5,z6]),(0,[z0,z2,z1046,z4,z5,z6]),(0,[z163,z0,z3,z4,z5,z173]),(0,[z384,z2,z4,z188,z5,z6]),(0,[z0,z2,z1047,z4,z5,z6])],[(0,[z0,z955,z153,z4,z5,z6]),(0,[z0,z2,z775,z4,z5,z6]),(0,[z117,z0,z3,z29,z4,z71]),(0,[z39,z0,z2,z92,z6,z40]),(1,[z0,z2,z4,z5,z724])],[(0,[z0,z2,z4,z1048,z5,z6]),(0,[z0,z528,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z646,z52]),(0,[z0,z3,z4,z1049,z5,z6]),(0,[z0,z46,z3,z848,z5,z6]),(0,[z0,z155,z3,z4,z200,z6])],[(0,[z0,z4,z5,z1050,z71,z6])],[(0,[z0,z2,z4,z1051,z5,z6]),(0,[z137,z2,z4,z62,z5,z72]),(0,[z2,z3,z4,z5,z6,z730]),(0,[z1052,z0,z2,z4,z5,z6])]],
   [[(0,[z415,z2,z47,z4,z5,z6]),(0,[z0,z1053,z3,z4,z5,z6])],[(0,[z0,z2,z1054,z4,z5,z6]),(0,[z0,z2,z185,z4,z5,z6]),(0,[z0,z1055,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1056]),(0,[z58,z0,z3,z5,z71,z179]),(0,[z0,z1057,z3,z4,z5,z6]),(0,[z1058,z0,z2,z4,z5,z6])],[(0,[z0,z14,z4,z34,z71,z6])],[(0,[z0,z2,z3,z4,z197,z361]),(0,[z137,z2,z92,z4,z5,z72]),(0,[z0,z2,z683,z62,z5,z6])],[(0,[z0,z2,z1059,z4,z5,z6]),(0,[z0,z1060,z3,z4,z5,z6])],[(0,[z0,z2,z1061,z4,z5,z6]),(0,[z9,z0,z4,z5,z83,z6]),(0,[z9,z0,z525,z4,z5,z6])],[(0,[z0,z1062,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z707,z6]),(0,[z9,z223,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1063])],[(0,[z0,z3,z4,z5,z6,z1064]),(0,[z0,z46,z4,z307,z5,z6]),(0,[z9,z0,z92,z4,z5,z6]),(0,[z328,z2,z219,z4,z5,z6]),(0,[z0,z2,z1065,z4,z5,z6]),(1,[z0,z2,z3,z726,z4])],[(0,[z0,z2,z3,z4,z1066,z6]),(0,[z9,z0,z3,z4,z5,z416]),(0,[z0,z4,z31,z5,z397,z6]),(0,[z9,z0,z3,z896,z5,z6]),(0,[z0,z2,z3,z4,z5,z712])],[(0,[z150,z2,z3,z109,z5,z361]),(0,[z1067,z0,z3,z4,z5,z6]),(0,[z0,z1068,z2,z4,z5,z6]),(0,[z0,z217,z394,z4,z5,z6]),(0,[z0,z190,z4,z31,z5,z6]),(0,[z0,z2,z4,z5,z6,z1069]),(0,[z328,z2,z202,z4,z5,z6])],[(0,[z0,z383,z92,z4,z5,z6]),(0,[z1070,z0,z2,z3,z5,z6]),(0,[z251,z0,z147,z31,z5,z6]),(0,[z0,z2,z881,z4,z5,z6]),(0,[z0,z2,z4,z1071,z5,z6]),(0,[z0,z2,z4,z5,z397,z6]),(0,[z348,z2,z3,z4,z78,z6])],[(0,[z0,z2,z1072,z4,z5,z6]),(0,[z0,z46,z313,z4,z5,z6]),(0,[z39,z9,z0,z3,z6,z40]),(0,[z0,z2,z3,z4,z1073,z6])],[(0,[z0,z3,z4,z5,z1074,z6]),(0,[z0,z3,z4,z31,z5,z255]),(0,[z0,z2,z1075,z4,z5,z6])],[(0,[z0,z1076,z3,z4,z5,z6]),(0,[z0,z3,z4,z1077,z5,z6]),(0,[z169,z0,z2,z4,z612,z6]),(0,[z1078,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1079]),(0,[z9,z0,z3,z4,z5,z519]),(0,[z9,z0,z3,z917,z5,z6]),(0,[z0,z2,z4,z34,z892,z6])]],
   [[(0,[z0,z2,z1080,z4,z5,z6]),(0,[z0,z2,z213,z62,z5,z6])],[(0,[z0,z1081,z2,z4,z5,z6]),(0,[z223,z3,z4,z31,z5,z6]),(0,[z0,z3,z4,z5,z1082,z6]),(0,[z0,z73,z180,z4,z5,z71]),(0,[z0,z942,z4,z5,z71,z6])],[(0,[z0,z2,z1083,z4,z5,z6]),(0,[z621,z2,z3,z4,z93,z6]),(0,[z0,z2,z1084,z4,z5,z6]),(0,[z1085,z2,z3,z4,z5,z6]),(0,[z1086,z0,z2,z4,z5,z6]),(0,[z0,z746,z3,z4,z5,z6])],[(0,[z0,z3,z1087,z4,z5,z6]),(0,[z0,z2,z3,z4,z344,z255]),(0,[z0,z3,z4,z5,z6,z1088]),(0,[z0,z1089,z4,z5,z71,z6]),(0,[z0,z528,z107,z4,z5,z67]),(0,[z826,z0,z3,z4,z5,z175])],[(0,[z9,z0,z3,z933,z5,z6])],[(0,[z9,z0,z3,z936,z5,z6]),(0,[z0,z1090,z4,z5,z71,z6]),(0,[z0,z2,z4,z62,z5,z387]),(0,[z0,z2,z1091,z4,z5,z6])],[(0,[z0,z13,z4,z5,z71,z6]),(0,[z0,z2,z4,z5,z6,z1092]),(0,[z0,z86,z305,z4,z5,z6])],[(0,[z0,z2,z13,z4,z5,z6]),(0,[z79,z0,z4,z5,z71,z6])],[(0,[z16,z17,z3,z4,z5,z6]),(0,[z0,z2,z432,z4,z206,z6])],[(0,[z0,z2,z3,z4,z1093,z6]),(0,[z70,z2,z4,z50,z83,z6]),(0,[z119,z0,z3,z4,z5,z429]),(0,[z0,z2,z92,z4,z5,z387])],[(0,[z0,z2,z4,z1094,z5,z6]),(0,[z0,z2,z1095,z4,z5,z6]),(0,[z0,z4,z5,z555,z6,z236]),(0,[z0,z4,z5,z429,z6,z890]),(0,[z0,z4,z62,z5,z6,z215]),(0,[z0,z2,z276,z59,z5,z64])],[(0,[z0,z3,z1096,z4,z5,z6])],[(0,[z137,z3,z4,z5,z555,z72]),(0,[z233,z2,z4,z62,z5,z144]),(0,[z0,z1097,z3,z4,z5,z6]),(0,[z0,z414,z501,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z471]),(0,[z148,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1098]),(0,[z0,z305,z4,z5,z71,z6]),(0,[z0,z828,z4,z62,z5,z6]),(0,[z0,z2,z3,z5,z6,z1099]),(0,[z0,z86,z313,z4,z5,z6])],[(0,[z0,z2,z4,z5,z1100,z6]),(0,[z364,z282,z0,z4,z5,z6]),(0,[z0,z1101,z3,z4,z5,z6])],[(0,[z0,z2,z1102,z4,z5,z6]),(0,[z9,z364,z0,z4,z5,z6]),(0,[z0,z46,z190,z4,z5,z6]),(0,[z9,z837,z3,z4,z5,z6]),(0,[z328,z115,z3,z4,z5,z6])],[(0,[z150,z383,z3,z109,z5,z6]),(0,[z282,z0,z92,z4,z5,z6]),(0,[z163,z0,z4,z62,z5,z6]),(0,[z116,z3,z4,z5,z71,z6])]],
   [[(0,[z0,z1103,z3,z4,z5,z6]),(0,[z1104,z0,z2,z4,z5,z6]),(0,[z0,z2,z1105,z4,z5,z6]),(0,[z0,z1106,z3,z4,z5,z6]),(0,[z0,z2,z4,z549,z5,z218]),(0,[z0,z1107,z3,z4,z5,z6])],[(0,[z131,z33,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z1108,z6]),(0,[z1109,z0,z3,z4,z5,z6])],[(0,[z130,z178,z92,z4,z5,z6]),(0,[z0,z51,z4,z683,z5,z6]),(0,[z0,z495,z4,z62,z5,z6]),(0,[z0,z1110,z3,z4,z5,z6]),(0,[z1111,z0,z2,z4,z5,z6])],[(0,[z1112,z0,z2,z3,z4,z6]),(0,[z163,z0,z92,z4,z5,z6]),(0,[z605,z0,z479,z4,z5,z6]),(0,[z0,z2,z1113,z4,z5,z6])],[(0,[z0,z46,z138,z139,z5,z6]),(0,[z0,z2,z525,z4,z30,z80])],[(0,[z0,z3,z4,z5,z6,z1114]),(0,[z0,z3,z4,z254,z5,z6]),(0,[z110,z0,z2,z62,z5,z6]),(0,[z0,z2,z4,z5,z6,z1115])],[(0,[z0,z2,z4,z1116,z5,z6]),(0,[z0,z1117,z2,z4,z5,z6]),(0,[z0,z180,z4,z5,z170,z6])],[(0,[z0,z46,z3,z145,z5,z6]),(0,[z116,z2,z4,z62,z5,z6]),(0,[z0,z2,z3,z4,z78,z179])],[(0,[z0,z2,z92,z253,z5,z6]),(0,[z0,z2,z1118,z4,z5,z6]),(0,[z0,z4,z5,z71,z6,z784]),(0,[z0,z2,z4,z5,z1119,z6])],[(0,[z0,z18,z46,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1120]),(0,[z607,z2,z3,z4,z93,z6]),(0,[z0,z2,z4,z5,z1121,z6]),(0,[z0,z61,z180,z4,z5,z6]),(0,[z9,z0,z3,z4,z967,z6]),(0,[z0,z2,z3,z4,z78,z6]),(0,[z0,z104,z125,z4,z5,z6])],[(0,[z1122,z0,z3,z4,z5,z255]),(0,[z0,z284,z4,z297,z5,z6]),(0,[z169,z0,z2,z4,z574,z6]),(0,[z169,z0,z46,z4,z162,z6]),(0,[z0,z2,z4,z1123,z5,z6]),(0,[z9,z0,z3,z4,z5,z250]),(0,[z169,z0,z2,z4,z575,z6]),(0,[z0,z2,z14,z4,z892,z6])],[(0,[z1124,z0,z3,z4,z5,z6]),(0,[z116,z2,z92,z4,z5,z6]),(0,[z0,z3,z4,z5,z815,z387])],[(0,[z0,z2,z3,z4,z5,z1125]),(0,[z0,z1126,z3,z4,z5,z6])],[(0,[z0,z283,z4,z5,z71,z6])],[(0,[z9,z675,z0,z3,z4,z5]),(0,[z0,z2,z1127,z4,z5,z6]),(0,[z0,z46,z3,z683,z5,z6])],[(0,[z0,z1128,z3,z4,z5,z6]),(0,[z0,z61,z51,z4,z5,z6]),(0,[z0,z2,z4,z1129,z5,z6]),(0,[z1130,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z46,z3,z4,z5,z361]),(0,[z2,z3,z4,z5,z144,z710]),(0,[z0,z3,z4,z5,z71,z175]),(0,[z0,z2,z3,z726,z4,z30])],[(0,[z150,z9,z3,z109,z5,z6]),(0,[z0,z2,z1131,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z916]),(0,[z0,z1132,z3,z4,z5,z6])],[(0,[z152,z46,z3,z4,z93,z6]),(0,[z0,z3,z4,z1133,z5,z6]),(0,[z0,z2,z1134,z4,z5,z6]),(0,[z0,z7,z305,z4,z5,z6])],[(0,[z0,z2,z4,z1135,z5,z6]),(0,[z0,z180,z4,z5,z6,z438]),(0,[z0,z2,z275,z62,z5,z6])],[(0,[z0,z713,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1023,z6]),(0,[z1136,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z750,z6]),(0,[z39,z0,z2,z219,z6,z40])],[(0,[z0,z18,z2,z4,z5,z6]),(0,[z0,z1137,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z923])],[(0,[z243,z0,z62,z5,z71,z6])],[(0,[z9,z0,z219,z4,z5,z6]),(0,[z0,z2,z4,z280,z5,z6]),(0,[z0,z1029,z495,z4,z5,z6])],[(0,[z604,z0,z2,z62,z5,z6]),(0,[z0,z1138,z3,z4,z5,z6]),(0,[z0,z3,z5,z64,z6,z322]),(0,[z0,z313,z4,z5,z71,z6]),(0,[z0,z2,z4,z62,z5,z175])],[(0,[z0,z2,z4,z5,z6,z1139]),(0,[z9,z0,z202,z4,z5,z6]),(0,[z0,z2,z125,z4,z5,z6]),(0,[z0,z2,z749,z62,z5,z6]),(0,[z0,z953,z495,z4,z5,z6])],[(0,[z0,z2,z4,z5,z1140,z6]),(0,[z0,z516,z4,z62,z5,z6])],[(0,[z0,z3,z4,z5,z901,z361]),(0,[z0,z3,z4,z5,z71,z187]),(0,[z0,z2,z1141,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1142,z6]),(0,[z0,z276,z4,z31,z5,z6]),(0,[z0,z2,z92,z4,z5,z175]),(0,[z0,z1143,z3,z4,z5,z6])],[(0,[z39,z0,z2,z3,z6,z1099])],[(0,[z9,z0,z4,z5,z6,z292]),(0,[z0,z516,z92,z4,z5,z6]),(0,[z0,z2,z92,z4,z5,z761]),(0,[z0,z1144,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1145])],[(0,[z459,z2,z3,z109,z5,z6]),(0,[z0,z92,z102,z31,z5,z6]),(0,[z0,z4,z5,z6,z438,z322])]],
   [[(0,[z0,z2,z3,z4,z948,z5]),(0,[z0,z3,z4,z5,z96,z71]),(0,[z0,z3,z4,z5,z6,z752]),(0,[z0,z2,z3,z749,z5,z6]),(0,[z0,z92,z4,z5,z122,z6])],[(0,[z2,z3,z4,z109,z5,z361]),(0,[z441,z2,z3,z4,z50,z6]),(0,[z0,z1146,z2,z4,z5,z6])],[(0,[z9,z0,z216,z4,z5,z6]),(0,[z0,z284,z4,z31,z5,z6]),(0,[z137,z282,z3,z4,z5,z72]),(0,[z119,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1147])],[(0,[z0,z46,z4,z21,z5,z6]),(0,[z1148,z0,z2,z4,z5,z6]),(0,[z0,z2,z394,z62,z5,z6]),(0,[z184,z0,z2,z4,z6,z425]),(0,[z0,z92,z1016,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1149]),(0,[z0,z2,z1150,z4,z5,z6]),(0,[z454,z3,z4,z418,z5,z6]),(0,[z119,z0,z3,z530,z5,z6]),(0,[z9,z0,z92,z62,z5,z6]),(0,[z0,z1151,z3,z4,z5,z6])],[(0,[z0,z383,z216,z4,z5,z6]),(0,[z0,z3,z4,z5,z1152,z6]),(0,[z0,z180,z476,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1153]),(0,[z0,z4,z5,z6,z198,z1154]),(0,[z0,z2,z1155,z4,z5,z6])],[(0,[z0,z3,z530,z5,z6,z40]),(0,[z79,z148,z0,z4,z5,z6])],[(0,[z0,z3,z4,z1156,z5,z6]),(0,[z0,z4,z5,z83,z71,z6]),(0,[z0,z2,z4,z5,z1050,z6]),(0,[z0,z3,z102,z530,z5,z6]),(0,[z9,z0,z3,z4,z5,z752])],[(0,[z0,z161,z3,z4,z5,z6]),(0,[z0,z2,z219,z4,z5,z387]),(0,[z0,z2,z1157,z4,z5,z6]),(0,[z0,z2,z3,z726,z4,z6])],[(0,[z0,z2,z4,z5,z1158,z6]),(0,[z0,z3,z4,z5,z1159,z6]),(0,[z0,z46,z305,z4,z5,z6])],[(0,[z348,z2,z3,z4,z5,z6]),(0,[z0,z2,z202,z4,z5,z387]),(0,[z0,z1160,z3,z4,z5,z6]),(0,[z0,z2,z3,z69,z5,z64])],[(0,[z0,z2,z1161,z4,z5,z6]),(0,[z0,z2,z92,z59,z5,z64]),(0,[z636,z0,z2,z3,z5,z179])],[(0,[z0,z1162,z3,z4,z5,z6]),(0,[z9,z0,z4,z5,z6,z236]),(0,[z0,z4,z139,z5,z71,z6])],[(0,[z0,z3,z4,z5,z1163,z6]),(0,[z0,z3,z4,z1164,z5,z6]),(0,[z184,z0,z2,z4,z162,z6])],[(0,[z70,z2,z4,z62,z50,z6]),(0,[z0,z2,z3,z485,z210,z6]),(0,[z0,z147,z4,z5,z71,z6]),(0,[z0,z2,z62,z5,z410,z6]),(0,[z0,z2,z305,z4,z160,z6])],[(0,[z70,z2,z3,z4,z769,z6]),(0,[z343,z2,z157,z4,z5,z6])]],
   [[(0,[z0,z1165,z4,z31,z5,z6]),(0,[z0,z4,z899,z5,z71,z6])],[(0,[z0,z2,z4,z62,z197,z6]),(0,[z0,z478,z4,z62,z5,z6]),(0,[z0,z2,z4,z5,z6,z1166]),(0,[z0,z2,z4,z5,z6,z1167]),(0,[z58,z0,z3,z530,z5,z6]),(0,[z0,z3,z4,z1168,z5,z6]),(0,[z0,z3,z4,z5,z6,z1169]),(0,[z328,z2,z3,z4,z210,z6])],[(0,[z0,z2,z3,z1170,z5,z6]),(0,[z70,z2,z92,z4,z50,z6]),(0,[z0,z3,z31,z404,z5,z6]),(0,[z0,z3,z520,z31,z5,z6]),(0,[z2,z802,z92,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1171]),(0,[z0,z127,z4,z146,z5,z6]),(0,[z0,z2,z4,z1172,z5,z6]),(0,[z166,z0,z3,z164,z4,z6]),(0,[z0,z1173,z3,z4,z5,z6]),(0,[z1174,z0,z3,z4,z5,z6])],[(0,[z0,z1175,z3,z4,z5,z6]),(0,[z251,z0,z92,z31,z5,z6]),(0,[z39,z0,z46,z3,z6,z40]),(0,[z0,z1176,z3,z4,z5,z6]),(0,[z0,z2,z313,z4,z160,z6])],[(0,[z9,z131,z33,z4,z5,z6]),(0,[z0,z2,z92,z4,z197,z6]),(0,[z0,z1177,z3,z4,z5,z6]),(0,[z0,z478,z92,z4,z5,z6]),(0,[z0,z2,z3,z4,z1178,z6]),(0,[z0,z2,z952,z4,z5,z6])],[(0,[z233,z2,z3,z4,z5,z339]),(0,[z0,z3,z174,z31,z210,z6]),(0,[z328,z46,z3,z4,z5,z6]),(0,[z0,z4,z62,z5,z6,z322]),(0,[z878,z0,z3,z4,z5,z387])],[(0,[z0,z1179,z2,z4,z5,z6]),(0,[z0,z53,z51,z4,z5,z6]),(0,[z252,z0,z3,z4,z543,z6]),(0,[z0,z1180,z2,z4,z5,z6]),(0,[z0,z3,z4,z121,z6,z487])],[(0,[z0,z46,z407,z4,z5,z6]),(0,[z0,z2,z3,z4,z1181,z6]),(0,[z0,z104,z3,z4,z5,z6]),(0,[z0,z2,z1182,z4,z5,z6])],[(0,[z0,z3,z4,z5,z71,z241]),(0,[z76,z0,z2,z4,z5,z457]),(0,[z9,z0,z284,z4,z5,z6]),(0,[z1183,z0,z3,z4,z5,z6]),(0,[z2,z3,z4,z50,z769,z6]),(0,[z598,z3,z4,z88,z5,z6]),(0,[z0,z2,z4,z5,z1184,z6])],[(0,[z598,z17,z3,z4,z5,z6]),(0,[z0,z2,z3,z1185,z5,z6]),(0,[z0,z2,z193,z4,z5,z6]),(0,[z0,z2,z1186,z4,z5,z6])],[(0,[z233,z2,z3,z4,z5,z710]),(0,[z0,z61,z4,z5,z6,z215]),(0,[z0,z2,z1187,z4,z5,z6]),(0,[z0,z3,z4,z5,z1188,z6])],[(0,[z582,z0,z3,z4,z10,z6]),(0,[z363,z2,z4,z622,z5,z6])],[(0,[z0,z2,z1189,z4,z5,z6]),(0,[z0,z2,z1190,z4,z5,z6]),(0,[z998,z3,z4,z31,z5,z6]),(0,[z119,z0,z3,z431,z5,z6]),(0,[z0,z3,z4,z160,z71,z6])],[(0,[z0,z2,z3,z4,z1191,z6]),(0,[z0,z3,z4,z5,z735,z255]),(0,[z0,z3,z4,z5,z6,z1192]),(0,[z0,z115,z3,z4,z5,z387])],[(0,[z0,z3,z4,z1193,z5,z6]),(0,[z0,z3,z690,z4,z5,z71]),(0,[z0,z1194,z3,z4,z5,z6])]],
   [[(0,[z16,z283,z17,z4,z5,z6]),(0,[z0,z46,z92,z31,z5,z6]),(0,[z39,z0,z2,z3,z6,z40]),(0,[z0,z2,z313,z4,z78,z6])],[(0,[z0,z46,z92,z102,z5,z6]),(0,[z0,z46,z3,z4,z30,z80]),(0,[z39,z0,z2,z62,z6,z40]),(0,[z0,z2,z4,z1195,z5,z6])],[(0,[z0,z2,z13,z4,z344,z6]),(0,[z0,z3,z4,z31,z160,z6]),(0,[z9,z1196,z0,z4,z5,z6]),(0,[z9,z1197,z3,z4,z5,z6]),(0,[z1198,z0,z3,z4,z5,z6]),(0,[z76,z0,z4,z5,z215,z52]),(0,[z0,z3,z4,z5,z1199,z6])],[(0,[z0,z2,z216,z4,z344,z6]),(0,[z0,z46,z3,z4,z344,z6]),(0,[z282,z0,z4,z5,z6,z236]),(0,[z0,z2,z3,z4,z1200,z6]),(0,[z233,z2,z92,z4,z5,z144]),(0,[z335,z401,z3,z4,z5,z6]),(0,[z0,z2,z62,z5,z6,z434])],[(0,[z43,z22,z2,z4,z5,z6]),(0,[z0,z2,z877,z4,z5,z6]),(0,[z0,z3,z4,z5,z1201,z6])],[(0,[z0,z2,z1202,z4,z5,z6]),(0,[z759,z2,z3,z4,z5,z6]),(0,[z9,z0,z180,z4,z5,z6])],[(0,[z0,z2,z4,z1203,z5,z6]),(0,[z0,z190,z4,z5,z71,z6]),(0,[z328,z265,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z579,z80])],[(0,[z0,z3,z4,z5,z6,z215]),(0,[z0,z2,z4,z30,z397,z80])],[(0,[z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1204]),(0,[z150,z2,z3,z109,z197,z6]),(0,[z0,z3,z4,z5,z71,z255]),(0,[z0,z4,z530,z62,z5,z6]),(0,[z0,z495,z92,z4,z5,z6])],[(0,[z0,z2,z3,z1205,z4,z5]),(0,[z0,z3,z4,z5,z1206,z6]),(0,[z39,z0,z2,z3,z175,z40])],[(0,[z9,z0,z4,z62,z5,z71])],[(1,[z0,z530,z62,z5,z6]),(0,[z0,z2,z1207,z4,z5,z6]),(0,[z0,z1208,z2,z4,z5,z6])],[(0,[z325,z3,z4,z5,z6,z140]),(0,[z223,z3,z4,z5,z71,z6]),(0,[z0,z4,z5,z71,z6,z292]),(0,[z0,z2,z1209,z4,z5,z6]),(0,[z1210,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z793,z6]),(0,[z9,z0,z185,z4,z5,z6]),(0,[z0,z2,z4,z1211,z5,z6]),(0,[z79,z0,z46,z4,z5,z6]),(0,[z9,z1212,z3,z4,z5,z6]),(0,[z0,z2,z530,z62,z5,z6]),(0,[z0,z2,z3,z726,z4,z5])],[(0,[z9,z0,z92,z4,z5,z71]),(0,[z0,z3,z4,z1213,z71,z6])]],
   [[(0,[z0,z2,z4,z1214,z5,z6]),(0,[z0,z127,z12,z4,z5,z6]),(0,[z0,z2,z891,z4,z5,z6]),(0,[z1215,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z724,z52]),(0,[z0,z1216,z3,z4,z5,z6])],[(0,[z0,z2,z4,z62,z5,z255]),(0,[z0,z4,z31,z5,z26,z6]),(0,[z0,z2,z4,z5,z1217,z6])],[(0,[z0,z2,z13,z4,z5,z361]),(0,[z0,z4,z62,z5,z63,z6]),(0,[z0,z46,z4,z5,z6,z438]),(0,[z0,z3,z4,z42,z5,z71])],[(0,[z0,z2,z216,z4,z5,z361]),(0,[z0,z46,z391,z4,z5,z6]),(0,[z0,z2,z3,z1218,z5,z6]),(0,[z0,z2,z4,z5,z26,z6]),(0,[z0,z854,z92,z4,z5,z6])],[(0,[z0,z132,z3,z4,z344,z6]),(0,[z0,z2,z4,z5,z1219,z6])],[(0,[z0,z2,z92,z4,z5,z255]),(0,[z0,z2,z1220,z4,z5,z6]),(0,[z0,z193,z4,z31,z5,z6]),(0,[z251,z0,z31,z62,z5,z6]),(0,[z0,z3,z4,z1221,z5,z6]),(0,[z0,z2,z4,z5,z6,z1222])],[(0,[z0,z2,z3,z4,z5,z1223]),(0,[z0,z3,z4,z5,z6,z1224])],[(0,[z0,z1225,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1226,z5,z6]),(0,[z0,z2,z1227,z4,z5,z6]),(0,[z0,z61,z186,z4,z5,z6]),(0,[z9,z0,z4,z5,z397,z6])],[(0,[z0,z3,z5,z63,z6,z322]),(0,[z0,z2,z4,z5,z892,z6])],[(0,[z0,z2,z1228,z4,z5,z6]),(0,[z0,z92,z102,z460,z5,z6]),(0,[z79,z0,z2,z4,z5,z6])],[(0,[z0,z2,z4,z5,z6,z1229]),(0,[z0,z2,z201,z62,z5,z6]),(0,[z0,z4,z5,z71,z6,z236]),(0,[z1230,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z71,z752]),(0,[z76,z0,z341,z4,z5,z52]),(0,[z348,z2,z305,z4,z5,z6]),(0,[z0,z2,z59,z307,z5,z64])],[(0,[z0,z2,z1231,z4,z5,z6]),(0,[z0,z46,z147,z4,z5,z6]),(0,[z243,z0,z2,z749,z5,z6]),(0,[z0,z1232,z3,z4,z5,z6])],[(0,[z0,z2,z1233,z4,z5,z6]),(0,[z131,z33,z4,z5,z71,z6]),(0,[z0,z2,z1234,z4,z5,z6]),(0,[z0,z2,z4,z1235,z5,z6])],[(0,[z0,z4,z31,z139,z5,z6]),(0,[z0,z2,z107,z4,z5,z67])],[(0,[z0,z1236,z2,z4,z5,z6]),(0,[z0,z3,z85,z4,z5,z71])]],
   [[(0,[z137,z46,z3,z4,z5,z72]),(0,[z0,z1237,z3,z4,z5,z6]),(0,[z1238,z2,z3,z4,z5,z6]),(0,[z0,z1239,z3,z4,z5,z6]),(0,[z0,z1240,z3,z4,z5,z6])],[(0,[z413,z17,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1241,z6]),(0,[z43,z2,z4,z5,z6,z114]),(0,[z150,z3,z109,z31,z5,z6]),(0,[z0,z46,z31,z62,z5,z6]),(0,[z0,z73,z3,z4,z5,z71]),(0,[z348,z2,z313,z4,z5,z6])],[(0,[z0,z2,z3,z4,z197,z255])],[(0,[z233,z329,z3,z4,z5,z144])],[(0,[z0,z1242,z3,z4,z5,z6]),(0,[z0,z132,z3,z4,z5,z361]),(0,[z9,z0,z13,z4,z5,z6]),(0,[z0,z341,z4,z62,z5,z6]),(0,[z0,z92,z4,z254,z5,z6])],[(0,[z0,z46,z3,z59,z5,z64]),(0,[z0,z4,z307,z5,z71,z6]),(0,[z0,z2,z3,z4,z1243,z6]),(0,[z0,z1244,z3,z4,z5,z6])],[(0,[z130,z3,z4,z418,z5,z6]),(0,[z131,z46,z33,z4,z5,z6]),(0,[z0,z61,z4,z404,z5,z6]),(0,[z0,z2,z4,z892,z162,z6])],[(0,[z0,z2,z1245,z4,z5,z6]),(0,[z0,z383,z13,z4,z5,z6]),(0,[z0,z891,z4,z5,z429,z6])],[(0,[z0,z2,z4,z5,z6,z1246]),(0,[z0,z2,z1247,z4,z5,z6]),(0,[z0,z46,z463,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z618]),(0,[z9,z169,z0,z4,z162,z6]),(0,[z0,z341,z92,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1248])],[(0,[z0,z1249,z2,z4,z5,z6]),(0,[z150,z2,z3,z109,z5,z255]),(0,[z0,z1250,z3,z4,z5,z6]),(0,[z243,z0,z31,z62,z5,z6]),(0,[z9,z0,z4,z62,z5,z173]),(0,[z0,z115,z4,z62,z5,z6])],[(0,[z0,z46,z3,z274,z5,z6]),(0,[z9,z0,z3,z4,z5,z465]),(0,[z9,z0,z3,z4,z160,z6]),(0,[z0,z2,z14,z4,z206,z6])],[(0,[z0,z2,z3,z4,z1251,z6]),(0,[z0,z217,z420,z4,z5,z6]),(0,[z9,z117,z0,z3,z29,z4])],[(0,[z0,z2,z1252,z4,z5,z6]),(0,[z0,z3,z4,z1253,z5,z6]),(0,[z0,z3,z4,z1254,z5,z6]),(0,[z0,z2,z107,z4,z5,z244]),(0,[z0,z2,z4,z5,z6,z1154])],[(0,[z0,z2,z4,z34,z578,z6]),(0,[z0,z3,z59,z31,z5,z64]),(0,[z9,z0,z92,z4,z5,z173]),(0,[z223,z2,z3,z4,z5,z387])],[(0,[z9,z43,z47,z4,z5,z6]),(0,[z0,z1068,z111,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z646]),(1,[z0,z3,z848,z5,z6]),(0,[z0,z1180,z46,z4,z5,z6]),(0,[z0,z3,z4,z1255,z5,z6])],[(0,[z0,z2,z4,z1256,z5,z6]),(0,[z348,z3,z4,z31,z5,z6]),(0,[z0,z46,z3,z209,z5,z6]),(0,[z0,z3,z4,z5,z829,z6])]],
   [[(0,[z0,z1257,z2,z4,z5,z6]),(0,[z0,z2,z3,z848,z5,z6]),(0,[z0,z2,z4,z1258,z5,z6]),(0,[z0,z1259,z3,z4,z5,z6])],[(0,[z0,z107,z4,z31,z5,z67]),(0,[z1260,z0,z2,z4,z5,z6]),(0,[z116,z7,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1261,z5,z6])],[(0,[z130,z3,z4,z5,z6,z140]),(0,[z2,z3,z4,z201,z93,z6]),(0,[z0,z3,z4,z5,z1262,z6]),(0,[z0,z4,z5,z63,z6,z438])],[(0,[z0,z2,z107,z4,z5,z38]),(0,[z0,z2,z3,z4,z1263,z6]),(0,[z0,z2,z1264,z4,z5,z6]),(0,[z0,z3,z4,z505,z32,z6]),(0,[z0,z46,z276,z4,z5,z6]),(0,[z176,z0,z3,z4,z27,z6])],[(0,[z0,z2,z92,z404,z5,z6]),(0,[z1265,z0,z3,z4,z5,z6]),(0,[z0,z2,z1266,z4,z5,z6])],[(0,[z288,z178,z3,z4,z5,z6]),(0,[z0,z46,z3,z4,z5,z387]),(0,[z9,z0,z3,z4,z78,z6])],[(0,[z0,z3,z1267,z4,z5,z6]),(0,[z243,z0,z516,z62,z5,z6]),(0,[z935,z2,z92,z4,z5,z6]),(0,[z1268,z0,z3,z4,z5,z6])],[(0,[z544,z17,z3,z4,z5,z6]),(0,[z163,z233,z0,z3,z4,z5]),(0,[z0,z276,z4,z5,z71,z6])],[(0,[z0,z4,z31,z307,z5,z6]),(0,[z0,z423,z4,z62,z5,z6])],[(0,[z0,z2,z92,z412,z5,z6]),(0,[z0,z1269,z3,z4,z5,z6])],[(0,[z261,z2,z3,z4,z5,z72]),(0,[z0,z191,z3,z4,z5,z6]),(0,[z0,z92,z102,z5,z71,z6]),(0,[z0,z1270,z3,z4,z5,z6]),(0,[z0,z3,z1271,z4,z5,z6])],[(0,[z0,z46,z3,z569,z5,z6]),(0,[z0,z2,z3,z4,z5,z1272]),(0,[z0,z2,z3,z4,z1273,z6]),(0,[z9,z0,z4,z1129,z5,z6])],[(0,[z131,z2,z157,z4,z5,z6]),(0,[z0,z1274,z3,z4,z5,z6]),(0,[z0,z1275,z3,z4,z5,z6]),(0,[z233,z46,z3,z4,z5,z144]),(0,[z0,z423,z92,z4,z5,z6]),(0,[z0,z2,z305,z4,z78,z6])],[(0,[z0,z3,z4,z1276,z5,z6]),(0,[z0,z284,z4,z5,z71,z6]),(0,[z1277,z2,z3,z4,z5,z6]),(0,[z447,z0,z2,z4,z5,z11]),(0,[z0,z2,z1278,z4,z5,z6])],[(0,[z0,z1279,z3,z4,z5,z6]),(0,[z150,z2,z92,z109,z5,z6]),(0,[z0,z217,z479,z4,z5,z6]),(0,[z0,z2,z313,z4,z5,z6]),(0,[z0,z3,z4,z5,z1280,z6]),(0,[z0,z3,z59,z5,z63,z64])]],
   [[(0,[z2,z3,z4,z109,z197,z6]),(0,[z894,z2,z3,z4,z5,z6])],[(0,[z0,z2,z500,z62,z5,z6]),(0,[z0,z125,z4,z31,z5,z6]),(0,[z0,z3,z4,z969,z31,z5]),(0,[z0,z3,z4,z5,z1281,z6])],[(0,[z0,z3,z4,z5,z721,z6]),(0,[z0,z1282,z3,z4,z5,z6])],[(0,[z0,z1283,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1284]),(0,[z0,z61,z4,z5,z439,z6]),(0,[z0,z3,z4,z5,z6,z322])],[(0,[z1285,z0,z3,z4,z5,z6]),(0,[z677,z0,z3,z31,z5,z6]),(0,[z9,z0,z4,z280,z5,z6]),(0,[z0,z2,z4,z5,z6,z1286]),(0,[z0,z2,z4,z1287,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1288]),(0,[z0,z1289,z3,z4,z5,z6]),(0,[z0,z46,z3,z138,z5,z6]),(0,[z0,z3,z4,z295,z5,z71]),(0,[z9,z0,z1035,z4,z5,z6]),(0,[z0,z3,z4,z1290,z5,z6])],[(0,[z233,z111,z3,z4,z5,z144]),(0,[z0,z3,z31,z5,z6,z322]),(0,[z0,z155,z4,z62,z200,z6]),(0,[z9,z0,z125,z4,z5,z6]),(0,[z0,z265,z3,z4,z5,z387])],[(0,[z0,z46,z426,z4,z5,z6]),(0,[z0,z329,z4,z62,z5,z6]),(0,[z76,z0,z4,z31,z5,z52]),(0,[z58,z0,z86,z3,z5,z179]),(0,[z0,z2,z4,z5,z6,z1291])],[(0,[z0,z1292,z3,z4,z5,z6]),(0,[z0,z108,z4,z31,z5,z6]),(0,[z116,z46,z3,z4,z5,z6]),(0,[z0,z2,z1089,z4,z5,z6]),(0,[z148,z0,z3,z4,z30,z80])],[],[(0,[z0,z2,z3,z4,z5,z1293]),(0,[z0,z2,z1294,z4,z5,z6]),(0,[z0,z7,z4,z62,z5,z6])],[(0,[z589,z2,z33,z4,z5,z6]),(0,[z0,z329,z92,z4,z5,z6]),(0,[z0,z3,z530,z62,z5,z6]),(0,[z447,z0,z2,z4,z5,z52]),(0,[z0,z2,z3,z4,z770,z6]),(0,[z0,z1295,z3,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z429]),(0,[z0,z2,z431,z62,z5,z6]),(0,[z0,z3,z4,z5,z6,z1296]),(0,[z79,z0,z4,z5,z122,z6])],[(0,[z235,z0,z3,z4,z5,z6]),(0,[z163,z0,z3,z4,z5,z63]),(0,[z0,z1297,z3,z4,z5,z6]),(0,[z116,z2,z3,z4,z160,z6]),(0,[z58,z0,z7,z3,z5,z179])],[(0,[z0,z1298,z3,z4,z5,z6]),(0,[z0,z2,z4,z1299,z5,z6]),(0,[z0,z3,z4,z1300,z5,z6]),(0,[z0,z2,z1301,z4,z5,z6]),(0,[z765,z0,z2,z4,z5,z6]),(0,[z0,z7,z92,z4,z5,z6]),(0,[z0,z2,z219,z4,z5,z175])],[(0,[z0,z2,z1302,z4,z5,z6]),(0,[z0,z73,z4,z5,z71,z438]),(0,[z0,z3,z4,z1303,z5,z6])]],
   [[(0,[z0,z2,z1304,z4,z5,z6]),(0,[z0,z2,z3,z4,z1305,z6]),(0,[z0,z3,z4,z5,z6,z1306]),(0,[z0,z3,z551,z31,z5,z6]),(0,[z977,z2,z4,z62,z5,z6]),(0,[z223,z2,z3,z4,z5,z175]),(0,[z0,z2,z202,z4,z5,z175])],[(0,[z0,z2,z1307,z4,z5,z6]),(0,[z0,z1308,z3,z4,z5,z6]),(0,[z0,z3,z4,z31,z78,z6]),(0,[z0,z3,z4,z5,z429,z64])],[(0,[z0,z2,z3,z4,z5,z1309]),(0,[z225,z2,z3,z4,z5,z72]),(0,[z1310,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z549,z5,z67]),(0,[z0,z2,z1311,z4,z5,z6])],[(0,[z0,z1312,z3,z4,z5,z6]),(0,[z1085,z3,z4,z5,z71,z6])],[(0,[z363,z2,z33,z4,z5,z6]),(0,[z1313,z0,z3,z4,z5,z6]),(0,[z0,z4,z306,z62,z5,z6]),(0,[z0,z2,z3,z4,z210,z175]),(0,[z0,z2,z4,z1314,z5,z6])],[(0,[z443,z0,z2,z4,z5,z52]),(0,[z0,z4,z297,z21,z5,z6]),(0,[z0,z46,z138,z62,z5,z6]),(0,[z176,z0,z3,z4,z165,z6]),(0,[z0,z2,z3,z4,z1315,z6]),(0,[z0,z2,z3,z4,z259,z80])],[(0,[z39,z0,z3,z31,z6,z40]),(0,[z0,z46,z3,z279,z5,z6]),(0,[z0,z2,z4,z5,z6,z1316])],[(0,[z0,z2,z1317,z4,z5,z6]),(0,[z0,z1318,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z6,z1319]),(0,[z0,z46,z3,z158,z5,z6]),(0,[z9,z0,z1161,z4,z5,z6]),(0,[z9,z0,z92,z4,z5,z15]),(0,[z9,z116,z3,z4,z5,z6]),(0,[z58,z9,z0,z3,z5,z179]),(0,[z223,z2,z4,z62,z5,z6]),(0,[z0,z125,z4,z306,z5,z6]),(0,[z116,z86,z3,z4,z5,z6])],[(0,[z0,z153,z3,z4,z5,z6]),(0,[z0,z1320,z3,z4,z5,z6]),(0,[z0,z2,z92,z298,z5,z6]),(0,[z0,z46,z3,z4,z5,z175]),(0,[z1197,z2,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z75]),(0,[z39,z0,z265,z3,z6,z40])],[(0,[z0,z2,z3,z4,z1321,z6]),(0,[z0,z3,z4,z5,z71,z379]),(0,[z0,z2,z14,z4,z685,z6])],[(0,[z0,z2,z4,z314,z162,z6]),(0,[z0,z799,z12,z4,z5,z6]),(0,[z39,z0,z115,z3,z6,z40])],[(0,[z9,z0,z283,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1322]),(0,[z0,z2,z3,z4,z1323,z6]),(0,[z1324,z0,z2,z4,z5,z6]),(0,[z0,z4,z62,z5,z71,z6]),(0,[z0,z3,z4,z5,z6,z1325]),(0,[z223,z2,z92,z4,z5,z6])],[(0,[z1326,z0,z3,z4,z5,z6]),(0,[z0,z92,z4,z5,z6,z1192])],[(0,[z0,z2,z1327,z4,z5,z6])],[(1,[z0,z3,z4,z721,z6])]],
   [[(0,[z178,z713,z3,z4,z5,z6]),(0,[z0,z1328,z2,z4,z5,z6]),(0,[z9,z874,z0,z4,z5,z6])],[(0,[z9,z233,z3,z4,z5,z144]),(0,[z0,z2,z3,z4,z5,z1329]),(0,[z0,z46,z4,z62,z5,z6]),(0,[z0,z4,z62,z5,z429,z6]),(0,[z0,z2,z3,z4,z721,z6]),(0,[z58,z0,z2,z3,z160,z179])],[(0,[z0,z476,z4,z62,z5,z6])],[(0,[z0,z3,z4,z1330,z5,z6]),(0,[z0,z2,z4,z139,z5,z6])],[(0,[z9,z0,z3,z4,z5,z614]),(0,[z152,z2,z3,z4,z769,z6]),(0,[z0,z3,z4,z306,z5,z6]),(0,[z0,z115,z3,z4,z5,z175])],[(0,[z0,z1146,z111,z4,z5,z6]),(0,[z0,z217,z4,z5,z6,z438]),(0,[z0,z46,z92,z4,z5,z6]),(0,[z2,z3,z737,z4,z5,z6]),(0,[z0,z2,z1331,z4,z5,z6]),(0,[z9,z0,z3,z4,z1181,z6])],[(0,[z9,z0,z3,z4,z5,z457]),(0,[z0,z1332,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z160,z6]),(0,[z0,z92,z4,z5,z6,z215])],[(0,[z0,z283,z46,z4,z5,z6]),(0,[z9,z0,z193,z4,z5,z6]),(0,[z9,z0,z1186,z4,z5,z6]),(0,[z301,z0,z3,z5,z6,z322]),(0,[z0,z2,z1333,z4,z5,z6])],[(0,[z0,z2,z92,z483,z5,z6]),(0,[z0,z216,z4,z31,z5,z6]),(0,[z0,z1334,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z1335,z6]),(0,[z0,z463,z4,z31,z5,z6]),(0,[z58,z235,z0,z3,z5,z179])],[(0,[z0,z3,z31,z5,z6,z466]),(0,[z0,z2,z3,z4,z920,z6]),(0,[z0,z265,z3,z4,z5,z175]),(0,[z1336,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z726,z4,z80])],[(0,[z0,z3,z4,z5,z1337,z6]),(0,[z0,z111,z4,z62,z5,z6])],[(0,[z0,z3,z4,z200,z721,z6])],[(0,[z0,z1338,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1339]),(0,[z58,z0,z2,z3,z78,z179])],[(0,[z0,z111,z92,z4,z5,z6]),(0,[z1340,z2,z3,z4,z5,z6]),(0,[z0,z191,z4,z307,z5,z6])],[(0,[z0,z1341,z3,z4,z5,z6]),(0,[z70,z46,z3,z4,z50,z6]),(0,[z0,z414,z12,z4,z5,z6])]],
   [[(0,[z0,z2,z1342,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1343]),(0,[z0,z2,z92,z4,z1007,z6]),(0,[z0,z115,z92,z4,z5,z6])],[(0,[z0,z3,z640,z31,z5,z6]),(0,[z0,z193,z4,z5,z71,z6]),(0,[z0,z2,z4,z1344,z5,z6]),(0,[z0,z265,z4,z62,z5,z6]),(0,[z0,z86,z4,z62,z5,z6]),(0,[z0,z2,z1345,z4,z5,z6])],[(0,[z0,z132,z4,z62,z5,z6]),(0,[z0,z2,z216,z4,z197,z6]),(0,[z0,z46,z3,z4,z197,z6]),(0,[z1346,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z1347,z5,z6])],[(0,[z0,z283,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z769,z6]),(0,[z0,z37,z3,z4,z5,z6]),(0,[z1348,z2,z3,z4,z5,z6])],[(0,[z0,z4,z31,z21,z5,z6]),(0,[z0,z2,z1349,z4,z5,z6]),(0,[z0,z4,z841,z31,z5,z6]),(0,[z243,z0,z46,z62,z5,z6])],[(0,[z0,z3,z642,z31,z5,z6]),(0,[z169,z0,z4,z162,z71,z6]),(0,[z0,z86,z92,z4,z5,z6]),(0,[z1350,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z892,z6])],[(0,[z0,z2,z4,z21,z5,z6]),(0,[z43,z2,z736,z4,z5,z6]),(0,[z163,z0,z3,z4,z5,z64]),(0,[z1351,z2,z3,z4,z5,z6])],[(0,[z0,z3,z4,z5,z1352,z6]),(0,[z0,z3,z4,z1353,z5,z6]),(0,[z459,z0,z2,z3,z5,z179]),(0,[z0,z12,z4,z412,z5,z6]),(0,[z0,z217,z501,z4,z5,z6]),(0,[z9,z243,z0,z62,z5,z6]),(0,[z0,z4,z62,z813,z5,z6])],[(0,[z0,z3,z4,z297,z5,z6]),(0,[z0,z2,z3,z4,z5,z1354]),(0,[z0,z186,z4,z41,z5,z6]),(0,[z0,z4,z5,z63,z6,z748]),(0,[z0,z2,z4,z34,z6,z19])],[(0,[z150,z2,z216,z109,z5,z6]),(0,[z150,z46,z3,z109,z5,z6]),(0,[z0,z2,z1355,z4,z5,z6]),(0,[z1356,z0,z3,z4,z5,z6])],[(0,[z0,z2,z1357,z4,z5,z6]),(0,[z0,z3,z138,z5,z6,z322])],[(0,[z0,z46,z3,z421,z5,z6]),(0,[z0,z3,z4,z1358,z5,z6]),(0,[z9,z0,z530,z62,z5,z6])],[(0,[z43,z46,z47,z4,z5,z6]),(0,[z9,z0,z3,z702,z4,z5]),(0,[z0,z2,z3,z4,z5,z1359]),(0,[z176,z0,z4,z26,z27,z6]),(0,[z1360,z0,z2,z4,z5,z6]),(0,[z0,z2,z305,z4,z5,z6])],[(0,[z0,z2,z3,z4,z754,z6]),(0,[z150,z3,z109,z5,z71,z6]),(0,[z1361,z0,z3,z4,z5,z6]),(0,[z0,z2,z107,z4,z5,z311])],[(0,[z43,z2,z4,z5,z290,z6]),(0,[z0,z2,z4,z307,z5,z6]),(0,[z116,z2,z3,z4,z5,z64])],[(0,[z0,z2,z3,z4,z5,z1362]),(0,[z119,z0,z3,z4,z5,z526]),(0,[z9,z348,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z870,z4,z5,z6]),(0,[z9,z0,z4,z5,z26,z6]),(0,[z9,z0,z3,z1218,z5,z6]),(0,[z243,z0,z2,z62,z5,z6]),(0,[z117,z0,z2,z92,z29,z4])],[(0,[z0,z3,z592,z31,z5,z6]),(0,[z0,z3,z31,z5,z490,z6]),(0,[z1363,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z6,z1099,z40])],[(0,[z1112,z0,z3,z4,z71,z6])],[(0,[z0,z132,z3,z4,z197,z6]),(0,[z0,z1364,z3,z4,z5,z6]),(0,[z0,z1365,z3,z4,z5,z6])],[(0,[z0,z1366,z3,z4,z5,z6]),(0,[z9,z0,z3,z4,z5,z488])],[(0,[z0,z407,z4,z31,z5,z6])],[],[(0,[z0,z3,z848,z31,z5,z6]),(0,[z0,z3,z1367,z4,z5,z6]),(0,[z0,z2,z4,z5,z1368,z6])],[(0,[z0,z124,z3,z4,z5,z6]),(0,[z117,z0,z3,z29,z4,z31])],[(0,[z0,z2,z3,z4,z776,z6]),(0,[z328,z2,z3,z4,z5,z6]),(0,[z0,z478,z284,z4,z5,z6]),(0,[z0,z46,z14,z4,z34,z6]),(0,[z0,z3,z59,z5,z71,z64]),(0,[z0,z528,z4,z62,z5,z6])],[(0,[z150,z132,z3,z109,z5,z6]),(0,[z0,z974,z4,z5,z71,z6])],[(0,[z9,z0,z107,z4,z5,z67]),(0,[z348,z3,z4,z5,z71,z6]),(0,[z58,z0,z2,z92,z5,z179])],[(0,[z0,z2,z1369,z4,z5,z6]),(0,[z163,z137,z0,z3,z4,z5]),(0,[z1370,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z71,z6,z1037]),(0,[z0,z1371,z3,z4,z5,z6])],[(0,[z0,z1372,z3,z4,z5,z6]),(0,[z0,z155,z92,z4,z200,z6]),(0,[z9,z79,z0,z4,z5,z6]),(0,[z0,z528,z92,z4,z5,z6]),(0,[z223,z2,z202,z4,z5,z6])],[(0,[z0,z3,z4,z1373,z5,z6]),(0,[z0,z1374,z3,z4,z5,z6]),(0,[z0,z2,z4,z1375,z5,z6]),(0,[z0,z46,z190,z138,z5,z6])],[(0,[z130,z178,z3,z4,z5,z6]),(0,[z58,z116,z2,z3,z5,z179]),(0,[z0,z3,z4,z5,z1376,z6])]],
   [[(0,[z0,z3,z4,z31,z5,z6]),(0,[z0,z1377,z3,z4,z5,z6]),(0,[z0,z2,z4,z749,z5,z6])],[(0,[z0,z2,z3,z4,z1378,z6]),(0,[z0,z3,z4,z1379,z5,z6]),(0,[z0,z2,z4,z5,z6,z1380]),(0,[z0,z2,z59,z62,z5,z64])],[(0,[z0,z2,z1090,z4,z5,z6]),(0,[z0,z1381,z3,z4,z5,z6]),(0,[z0,z2,z216,z4,z5,z255]),(0,[z0,z46,z3,z4,z5,z255]),(0,[z0,z4,z1344,z5,z71,z6]),(0,[z58,z0,z2,z3,z5,z712]),(0,[z119,z0,z3,z59,z5,z64])],[(0,[z9,z0,z3,z4,z5,z503]),(0,[z1382,z0,z3,z4,z5,z6]),(0,[z0,z1383,z3,z4,z5,z6]),(0,[z0,z1384,z3,z4,z5,z6])],[(0,[z0,z2,z190,z4,z5,z6]),(0,[z0,z2,z3,z4,z30,z80])],[],[(0,[z0,z2,z3,z4,z344,z6]),(0,[z1385,z0,z3,z4,z5,z6]),(0,[z1212,z2,z3,z4,z5,z6])],[(0,[z0,z1328,z46,z4,z5,z6]),(0,[z0,z4,z5,z26,z71,z6]),(0,[z9,z0,z3,z4,z5,z244])],[(0,[z0,z2,z1386,z4,z5,z6]),(0,[z0,z180,z12,z4,z5,z6]),(0,[z0,z2,z1387,z4,z5,z6]),(0,[z9,z0,z3,z4,z1251,z6])],[(0,[z207,z0,z647,z4,z5,z6])],[(0,[z0,z2,z1025,z4,z5,z6]),(0,[z0,z1388,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z1389,z6]),(0,[z70,z2,z185,z4,z50,z6]),(0,[z9,z0,z3,z4,z5,z581])],[(0,[z116,z2,z3,z4,z78,z6])],[(0,[z0,z2,z4,z1390,z5,z6]),(0,[z0,z4,z5,z71,z6,z1286]),(0,[z0,z125,z4,z5,z71,z6]),(0,[z0,z2,z4,z5,z1391,z6])],[(0,[z1392,z0,z3,z4,z5,z6]),(0,[z0,z4,z62,z5,z6,z198]),(0,[z0,z1393,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z378,z80]),(0,[z0,z4,z5,z122,z6,z292])],[(0,[z0,z1394,z3,z4,z5,z6]),(0,[z0,z115,z219,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1395,z6]),(0,[z0,z2,z3,z4,z5,z745]),(0,[z9,z0,z3,z4,z5,z518]),(0,[z1396,z2,z3,z4,z5,z6])],[(0,[z0,z46,z92,z62,z5,z6]),(0,[z223,z115,z3,z4,z5,z6]),(0,[z0,z115,z202,z4,z5,z6])],[(0,[z9,z0,z3,z4,z5,z334]),(0,[z0,z1397,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z63,z6]),(0,[z0,z92,z4,z5,z6,z322]),(0,[z0,z2,z1398,z4,z5,z6])],[(0,[z0,z2,z1399,z4,z5,z6]),(0,[z9,z0,z18,z4,z5,z6]),(0,[z0,z132,z3,z4,z5,z255]),(0,[z9,z70,z3,z4,z50,z6]),(0,[z0,z2,z4,z5,z1400,z6]),(0,[z0,z4,z31,z5,z6,z438]),(0,[z0,z1401,z2,z4,z5,z6]),(0,[z76,z0,z4,z5,z71,z52]),(0,[z0,z1402,z3,z4,z5,z6])],[(0,[z16,z17,z4,z62,z5,z6]),(0,[z0,z108,z4,z5,z71,z6])],[(0,[z0,z2,z3,z4,z1403,z6]),(0,[z0,z46,z4,z5,z83,z6]),(0,[z364,z0,z4,z31,z5,z6]),(0,[z0,z2,z4,z5,z6,z438]),(0,[z1404,z2,z3,z4,z5,z6]),(0,[z0,z46,z525,z4,z5,z6]),(0,[z0,z1405,z3,z4,z5,z6])],[(0,[z0,z2,z4,z5,z1406,z6]),(0,[z0,z2,z391,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z361]),(0,[z0,z46,z4,z5,z6,z890]),(0,[z0,z1407,z3,z4,z5,z6]),(0,[z79,z0,z2,z4,z30,z80])],[(0,[z0,z2,z92,z534,z5,z6]),(0,[z0,z2,z3,z4,z5,z1408])],[(0,[z16,z17,z92,z4,z5,z6]),(0,[z152,z2,z3,z4,z93,z6]),(0,[z148,z0,z4,z62,z5,z6])],[(0,[z0,z3,z482,z31,z5,z6]),(1,[z0,z2,z3,z5,z712])],[(1,[z2,z3,z4,z769,z6]),(0,[z1409,z0,z3,z4,z31,z5]),(0,[z0,z2,z1410,z4,z5,z6]),(0,[z9,z0,z3,z4,z259,z5]),(0,[z0,z1411,z3,z4,z5,z6])],[(0,[z0,z2,z1412,z4,z5,z6]),(0,[z0,z3,z1413,z4,z5,z6]),(0,[z0,z2,z1414,z4,z5,z6])],[(0,[z0,z1415,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z429,z179]),(0,[z1196,z0,z2,z4,z5,z6]),(0,[z148,z0,z92,z4,z5,z6])],[(0,[z1122,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z78,z71,z6]),(0,[z0,z2,z92,z4,z160,z6])],[(0,[z0,z3,z4,z5,z429,z6]),(0,[z0,z1110,z4,z62,z5,z6]),(0,[z0,z1155,z4,z5,z6,z198])],[(0,[z0,z2,z1416,z4,z5,z6]),(0,[z1313,z0,z3,z4,z5,z361]),(0,[z0,z1165,z2,z4,z5,z6]),(0,[z9,z0,z180,z4,z5,z71])]],
   [[(0,[z1417,z0,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z752,z173])],[(0,[z1418,z0,z3,z4,z5,z6]),(0,[z0,z3,z31,z5,z6,z547]),(0,[z1215,z3,z4,z5,z71,z6]),(0,[z1419,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z405,z5,z52])],[],[(0,[z0,z2,z3,z4,z1420,z6]),(0,[z137,z2,z3,z4,z5,z72]),(0,[z0,z61,z4,z258,z5,z6]),(0,[z0,z2,z3,z4,z1213,z6])],[(0,[z389,z0,z3,z4,z27,z6]),(0,[z0,z2,z13,z4,z197,z6])],[(0,[z0,z2,z1421,z4,z5,z6]),(0,[z16,z128,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z1422,z6]),(0,[z0,z2,z299,z4,z34,z6]),(0,[z0,z1423,z3,z4,z5,z6]),(0,[z0,z2,z4,z62,z78,z6]),(0,[z58,z0,z2,z305,z5,z179])],[(0,[z1424,z2,z3,z4,z5,z6]),(0,[z58,z348,z2,z3,z5,z179]),(0,[z0,z2,z3,z59,z5,z712])],[(0,[z70,z2,z3,z4,z97,z6]),(0,[z0,z46,z3,z412,z5,z6]),(0,[z0,z999,z4,z31,z5,z6])],[(0,[z9,z0,z3,z4,z5,z6]),(0,[z1136,z3,z4,z5,z71,z6]),(0,[z0,z414,z326,z4,z5,z6]),(0,[z0,z265,z92,z4,z5,z6]),(0,[z1425,z0,z2,z4,z5,z6])],[(0,[z0,z132,z92,z4,z5,z6]),(0,[z0,z2,z1426,z4,z5,z6]),(0,[z9,z0,z431,z62,z5,z6]),(0,[z0,z2,z92,z4,z78,z6])],[(0,[z0,z3,z4,z1427,z5,z6]),(0,[z0,z3,z4,z1428,z5,z6]),(0,[z0,z217,z476,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1429])],[(0,[z0,z383,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1430]),(0,[z150,z2,z13,z109,z5,z6]),(0,[z0,z2,z1431,z4,z5,z6]),(1,[z0,z799,z4,z5,z6]),(0,[z0,z2,z463,z4,z5,z6]),(0,[z0,z3,z4,z1432,z5,z6]),(0,[z722,z2,z3,z4,z5,z6])],[(0,[z0,z1433,z3,z4,z5,z6]),(0,[z0,z2,z62,z5,z6,z620])],[(0,[z1434,z0,z2,z4,z5,z6]),(0,[z133,z2,z3,z4,z5,z361]),(0,[z0,z1435,z3,z4,z5,z6]),(0,[z176,z0,z3,z4,z721,z6]),(0,[z9,z0,z1304,z4,z5,z6]),(0,[z0,z2,z560,z62,z5,z6])],[(0,[z1409,z0,z2,z3,z4,z5]),(0,[z0,z1436,z3,z4,z5,z6])],[(0,[z233,z3,z4,z5,z144,z71]),(0,[z0,z3,z617,z31,z5,z6]),(0,[z0,z3,z4,z5,z71,z498])]],
   [[(0,[z0,z2,z3,z4,z1437,z6]),(0,[z0,z3,z4,z5,z1438,z6]),(0,[z0,z1439,z3,z4,z5,z6]),(0,[z0,z217,z799,z4,z5,z6]),(0,[z0,z2,z92,z567,z5,z6])],[(0,[z0,z2,z14,z4,z212,z6]),(0,[z2,z736,z33,z4,z5,z6]),(0,[z251,z0,z3,z31,z5,z6]),(0,[z0,z3,z45,z31,z5,z6])],[(0,[z130,z713,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z1440,z6]),(0,[z0,z46,z180,z4,z5,z6]),(0,[z0,z4,z5,z6,z215,z438]),(0,[z1441,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z712,z179])],[(0,[z0,z2,z871,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z1442]),(0,[z0,z92,z4,z306,z5,z6]),(0,[z0,z3,z1443,z4,z5,z6]),(0,[z0,z1444,z3,z4,z5,z6])],[(0,[z0,z216,z4,z5,z71,z6]),(0,[z0,z2,z1445,z4,z5,z6]),(0,[z0,z4,z62,z5,z555,z6]),(0,[z0,z463,z4,z5,z71,z6]),(0,[z39,z0,z3,z71,z6,z40]),(0,[z0,z2,z4,z5,z6,z1446])],[(0,[z2,z3,z4,z769,z93,z6]),(0,[z0,z3,z4,z1447,z5,z6]),(0,[z0,z1448,z3,z4,z5,z6])],[(0,[z1449,z0,z3,z4,z5,z6]),(0,[z0,z2,z1450,z4,z5,z6]),(1,[z2,z3,z4,z5,z710])],[(0,[z0,z2,z276,z4,z5,z6])],[(0,[z150,z2,z109,z62,z5,z6]),(0,[z0,z185,z4,z31,z5,z6]),(0,[z0,z2,z3,z4,z6,z1099])],[(0,[z0,z2,z3,z4,z5,z1451]),(0,[z0,z2,z3,z4,z5,z387])],[(0,[z0,z1452,z3,z4,z5,z6]),(0,[z0,z1453,z3,z4,z5,z6]),(0,[z0,z2,z4,z1454,z5,z6])],[(0,[z0,z155,z3,z4,z211,z6]),(0,[z0,z3,z4,z460,z5,z6]),(0,[z0,z3,z4,z200,z6,z487]),(0,[z0,z2,z1455,z4,z5,z6])],[(0,[z0,z1456,z3,z4,z5,z6])],[(0,[z0,z61,z666,z4,z5,z6]),(0,[z0,z1457,z3,z4,z5,z6]),(0,[z0,z281,z51,z4,z5,z6]),(0,[z0,z46,z3,z31,z5,z6])],[(0,[z0,z2,z407,z4,z5,z6]),(0,[z0,z1458,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1459]),(0,[z328,z3,z4,z31,z5,z6]),(0,[z119,z0,z4,z62,z5,z6]),(0,[z1460,z0,z3,z4,z5,z6]),(0,[z223,z2,z219,z4,z5,z6])],[(0,[z282,z0,z3,z4,z5,z6]),(0,[z0,z2,z4,z1461,z5,z6]),(0,[z0,z2,z1462,z4,z5,z6]),(0,[z0,z2,z4,z1463,z5,z6]),(0,[z0,z2,z942,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 499) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 499).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 989).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1485).take 67) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1552)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [499, 490, 496, 67] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 132).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 132).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 275).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 409).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [132, 143, 134, 103] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_38965

theorem PEqualNP.Outside.L_meta_38965 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4241026248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4241026248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38965.solve