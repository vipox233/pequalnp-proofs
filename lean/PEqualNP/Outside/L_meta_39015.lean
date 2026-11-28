import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39015

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
  Nat.testBit (4276812992 * 2 ^ 32 + 4241029312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0831af319911b1e5#64 ++ 0x210635e63322363c#64 ++ 0x8873ff319913b3e7#64 ++ 0xd10e7fe63322767c#64 : BitVec 256),
   (0x00846016a066c2a8#64 ++ 0x40108c02d40cd855#64 ++ 0xf98c603fe1ffc3ff#64 ++ 0xbf318c07fc3ff87f#64 : BitVec 256),
   (0x020b81414a181451#64 ++ 0x804170282943028a#64 ++ 0xbe0f83c1fe1c7c7f#64 ++ 0x77c1f0783fc38f8f#64 : BitVec 256),
   (0x057002aa15a06b06#64 ++ 0x00ae005542b40d60#64 ++ 0xfff003fe1fe07f86#64 ++ 0xfffe007fc3fc0ff0#64 : BitVec 256),
   (0x17ded4001fdf0000#64 ++ 0x02fbda8003fbe000#64 ++ 0xd7fffc001fff8005#64 ++ 0xfaffff8003fff000#64 : BitVec 256),
   (0x27ef7bfde0000000#64 ++ 0x04fdef7fbc000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xf98c603fe1ffc3ff 0xbf318c07fc3ff87f

def z1 : W := mkw 0x020b81414a181451 0x804170282943028a 0xbe0f83c1fe1c7c7f 0x77c1f0783fc38f8f

def z2 : W := mkw 0x028fe157ea7ed6f9 0xc051fc2afd4fdadf 0xf98fe03fe1ffc3ff 0xbf31fc07fc3ff87f

def z3 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfff003fe1fe07f86 0xfffe007fc3fc0ff0

def z4 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8873ff319913b3e7 0xd10e7fe63322767c

def z5 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xd7fffc001fff8005 0xfaffff8003fff000

def z6 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z7 : W := mkw 0x08b5ef35b957b1ed 0x6116bde6b72af63d 0x887fff31f91fb3ff 0xd10fffe63f23f67f

def z8 : W := mkw 0x17ded4063fff4208 0x42fbda80c7ffe841 0xf7fffc0e7fffc01d 0xfeffff81cffff803

def z9 : W := mkw 0x0084400620664208 0x40108800c40cc841 0x718c000e60ec4018 0x2e318001cc1d8803

def z10 : W := mkw 0x08318f2119113145 0x210631e423222628 0x00739f0018003000 0x400e73e003000600

def z11 : W := mkw 0x101084021fffc2a8 0x4202108043fff855 0x180000001fffc3fc 0x0300000003fff87f

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe0003c01e007c06 0x77c0007803c00f80

def z13 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xffffffc01ffffc07 0xfffffff803ffff80

def z14 : W := mkw 0x0540008a04a04a02 0x00a8001140940940 0x778000ce06e04c00 0x2ef00019c0dc0980

def z15 : W := mkw 0x0801ad11881190e1 0x210035a23102321c 0x0003fc0180138061 0x00007f803002700c

def z16 : W := mkw 0x1fffff319fdfb1e5 0x23ffffe633fbf63c 0xdfffff319fffb3e7 0xfbffffe633fff67c

def z17 : W := mkw 0x020a80404a181451 0x804150080943028a 0x3e0c00c07e1c7c7c 0x27c180180fc38f8f

def z18 : W := mkw 0x00002010800080a0 0x0000040210001014 0x0000600180138061 0x00000c003002700c

def z19 : W := mkw 0x276b9be94a181451 0x84ed737d2943028a 0x06739fc01e003c00 0x40ce73f803c00780

def z20 : W := mkw 0x00002016a020c2a8 0x40000402d4041855 0xf980003fe1e043fe 0xbf300007fc3c087f

def z21 : W := mkw 0x128fd5414a5f1451 0x8251faa8294be28a 0xbe0fffc1fe1ffc7f 0x77c1fff83fc3ff8f

def z22 : W := mkw 0x07ce500000000000 0x00f9ca0000000000 0xc7fffc0000000001 0xf8ffff8000000000

def z23 : W := mkw 0x37fffffdffdf0000 0x06ffffffbffbe000 0xf7ffffffffff8007 0xfefffffffffff000

def z24 : W := mkw 0x057002a815802906 0x00ae005502b00520 0x0070000000000000 0x000e000000000000

def z25 : W := mkw 0x17def416bfffc2a8 0x42fbde82d7fff855 0xd7fffc3e1fff8385 0xfaffff87c3fff070

def z26 : W := mkw 0x020b81414a181451 0x804170282943028a 0x2e0383c1fe007c7a 0x45c070783fc00f8f

def z27 : W := mkw 0x177a96aa1fb96b06 0x02ef52d543f72d60 0xfff39ffe1fe07f86 0xfffe73ffc3fc0ff0

def z28 : W := mkw 0x000000020066c2a8 0x40000000400cd855 0x1800000001ffc3fc 0x03000000003ff87f

def z29 : W := mkw 0x27fffbffffb87f57 0x84ffff7ffff70fea 0xfffffffffffc7fff 0xffffffffffff8fff

def z30 : W := mkw 0x0a3baf71db19b5f5 0xa14775ee3b6336be 0xbe7ffff1ff1fffff 0xf7cffffe3fe3ffff

def z31 : W := mkw 0x00212b31800080a0 0x0004256630001014 0x8873ff31811383e7 0xd10e7fe63022707c

def z32 : W := mkw 0x27ef7bffe066c2a8 0x44fdef7ffc0cd855 0xffffffffe1ffc3ff 0xfffffffffc3ff87f

def z33 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xff8c63ffffffffff 0xfff18c7fffffffff

def z34 : W := mkw 0x022b2b71c0000000 0x0045656e38000000 0xa67ffff1e0000003 0xf4cffffe3c000000

def z35 : W := mkw 0x022bab71ca181451 0x8045756e3943028a 0xbe7ffff1fe1c7c7f 0xf7cffffe3fc38f8f

def z36 : W := mkw 0x00212b3180000000 0x0004256630000000 0x8073ff3180000003 0xd00e7fe630000000

def z37 : W := mkw 0x2ffffffdf911b1e5 0x25ffffffbf22363c 0xeffffffff913b3e7 0xfdffffffff22767c

def z38 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x418c603fe1ff83f9 0x88318c07fc3ff07f

def z39 : W := mkw 0x1084540000470000 0x02108a800008e000 0x00007c0000038000 0x00000f8000007000

def z40 : W := mkw 0x057183ab1db07b47 0x00ae307563b60f68 0xfff383ff9ff07fe7 0xfffe707ff3fe0ffc

def z41 : W := mkw 0x07cf514140000000 0x00f9ea2828000000 0xe7ffffc1e0000003 0xfcfffff83c000000

def z42 : W := mkw 0x100084000a5f0000 0x02001080014be000 0x00000000001f8000 0x000000000003f000

def z43 : W := mkw 0x020b814148101041 0x0041702829020208 0xae0f83c1f8103067 0x75c1f0783f02060c

def z44 : W := mkw 0x081084001911b1e5 0x210210800322363c 0x080000001913b3e4 0x010000000322767c

def z45 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0073fc31811383e1 0x800e7f863022707c

def z46 : W := mkw 0x27effbfde8101041 0x04fdff7fbd020208 0xeffffffff8103067 0xfdffffffff02060c

def z47 : W := mkw 0x08302e309101a1a4 0x210605c612203434 0x00707c3001038380 0x800e0f8600207070

def z48 : W := mkw 0x0d71afbb9db1fbe7 0x21ae35f773b63f7c 0xfff3ffff9ff3ffe7 0xfffe7ffff3fe7ffc

def z49 : W := mkw 0x0010000215a06b06 0x0002000042b40d60 0x180000001fe07f84 0x0300000003fc0ff0

def z50 : W := mkw 0x228f7955e0000000 0x0451ef2abc000000 0x000ffc01e0000001 0x0001ff803c000000

def z51 : W := mkw 0x020b014142081451 0x804160282841028a 0x3e0c03c1e60c7c7a 0x27c180783cc18f8f

def z52 : W := mkw 0x0084400620664208 0x40108800c40cc841 0xf18c600e61ffc01d 0xbe318c01cc3ff803

def z53 : W := mkw 0x07cfd1414a181451 0x80f9fa282943028a 0xffffffc1fe1c7c7f 0xfffffff83fc38f8f

def z54 : W := mkw 0x00000000000080a0 0x0000000000001014 0x08000000011383e4 0x010000000022707c

def z55 : W := mkw 0x0a3baf71db19b5f5 0xa14775ee3b6336be 0x887fff31f91fb3ff 0xd10fffe63f23f67f

def z56 : W := mkw 0x0a3baf319b19b1e5 0x214775e63363363c 0x9e7fff319f1fb3e7 0xf3cfffe633e3f67c

def z57 : W := mkw 0x08212b318000b1e5 0x210425663000163c 0x08000331800033e2 0x010000663000067c

def z58 : W := mkw 0x17dfd5415fdf1451 0x82fbfaa82bfbe28a 0xffffffc1fffffc7f 0xfffffff83fffff8f

def z59 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x47f003fe1fe03f80 0xc8fe007fc3fc07f0

def z60 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x4180603e01e38380 0x88300c07c03c7070

def z61 : W := mkw 0x020b81414a181451 0x804170282943028a 0x060383c01e003c00 0x40c0707803c00780

def z62 : W := mkw 0x17ded48a1fff4a02 0x02fbda9143ffe940 0xf7fffcce1fffcc05 0xfeffff99c3fff980

def z63 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0x0000600000038000 0x00000c0000007000

def z64 : W := mkw 0x17def416bfffc2a8 0x42fbde82d7fff855 0xfffffc3fffffc3ff 0xffffff87fffff87f

def z65 : W := mkw 0x07ce500000460000 0x00f9ca000008c000 0xd7fffc0001ff8005 0xfaffff80003ff000

def z66 : W := mkw 0x27effbfdea180000 0x04fdff7fbd430000 0xf7fffffffe1c0007 0xfeffffffffc38000

def z67 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xb87fff31f91ff3ff 0xf70fffe63f23fe7f

def z68 : W := mkw 0x028fe155ea5e94f9 0xc051fc2abd4bd29f 0x000fe001e01f8079 0x0001fc003c03f00f

def z69 : W := mkw 0x028fe157ea7ed6f9 0xc051fc2afd4fdadf 0xff8fe3ffffffffff 0xfff1fc7fffffffff

def z70 : W := mkw 0x0000000200204200 0x0000000040040840 0xf980003e01e04386 0xbf300007c03c0870

def z71 : W := mkw 0x05f462beb5e6ebae 0x40be8c57d6bcdd75 0xfffc63ffffffffff 0xffff8c7fffffffff

def z72 : W := mkw 0x0084400000000000 0x0010880000000000 0xc18c600000000001 0xb8318c0000000000

def z73 : W := mkw 0x0001014140001451 0x800020282800028a 0x280003c1e0007c7a 0x050000783c000f8f

def z74 : W := mkw 0x27ef7bfde0001451 0x84fdef7fbc00028a 0xefffffffe0007c7b 0xfdfffffffc000f8f

def z75 : W := mkw 0x0d718fa91d913947 0x21ae31f523b22728 0x06739fc01e003c00 0x40ce73f803c00780

def z76 : W := mkw 0x17ce500006ce0000 0x02f9ca0000d9c000 0xd7fffc0006ec0001 0xfaffff8000dd8000

def z77 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xfffffffffe007c07 0xffffffffffc00f80

def z78 : W := mkw 0x25e47abca0000000 0x04bc8f5794000000 0x41f07c3e00000000 0x883e0f87c0000000

def z79 : W := mkw 0x27ff7bfff5a06b06 0x04ffef7ffeb40d60 0xffffffffffe07f87 0xfffffffffffc0ff0

def z80 : W := mkw 0x0010840019110000 0x0002108003222000 0x8073fc0019138005 0xd00e7f8003227000

def z81 : W := mkw 0x17ce500006ce0000 0x02f9ca0000d9c000 0x578c000006ec0000 0x2af1800000dd8000

def z82 : W := mkw 0x1000000006ce0000 0x0200000000d9c000 0x1000000006ec0000 0x0200000000dd8000

def z83 : W := mkw 0x27ce50ce60664208 0x44f9ca19cc0cc841 0x778c00ce60ec4018 0x2ef18019cc1d8803

def z84 : W := mkw 0x0010000215a06b06 0x0002000042b40d60 0xf980003e1fe07f86 0xbf300007c3fc0ff0

def z85 : W := mkw 0x0830ae309911a1a4 0x210615c613223434 0x8073fc3019138385 0xd00e7f8603227070

def z86 : W := mkw 0x25f47abeb5a06b06 0x04be8f57d6b40d60 0x41f07c3e01e00380 0x883e0f87c03c0070

def z87 : W := mkw 0x020b014140001451 0x804160282800028a 0xae0f83c1e0007c7b 0x75c1f0783c000f8f

def z88 : W := mkw 0x27ef7bffe0206b06 0x04fdef7ffc040d60 0xefffffffe0007f83 0xfdfffffffc000ff0

def z89 : W := mkw 0x0811ad119911b1e5 0x210235a23322363c 0x0803fc019913b3e5 0x01007f803322767c

def z90 : W := mkw 0x020b81414a181451 0x804170282943028a 0x360f83c07e0c7c18 0x66c1f0780fc18f83

def z91 : W := mkw 0x002103eb40207f57 0x8004207d68040fea 0x280003ffe0007ffa 0x0500007ffc000fff

def z92 : W := mkw 0x15d4540015c70000 0x02ba8a8002b8e000 0x41f07c0001e38000 0x883e0f80003c7000

def z93 : W := mkw 0x15d4d4001fdf0000 0x02ba9a8003fbe000 0x51f07c001fff8004 0x8a3e0f8003fff000

def z94 : W := mkw 0x17ced4000edf0000 0x02f9da8001dbe000 0x578ffc0006ff8001 0x2af1ff8000dff000

def z95 : W := mkw 0x00846014a0000000 0x00108c0294000000 0x4180603e00000000 0x88300c07c0000000

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0xd180000001e00004 0xba300000003c0000

def z97 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x41fffc0001ff8001 0x883fff80003ff000

def z98 : W := mkw 0x020a004042080410 0x8041400808410082 0x000c0000600c0018 0x000180000c018003

def z99 : W := mkw 0x0821ab318810b1e5 0x210435663102163c 0x88038331981033e7 0x510070663302067c

def z100 : W := mkw 0x000020128020c2a0 0x0000040250041854 0xf980603f81f3c3e7 0xbf300c07f03e787c

def z101 : W := mkw 0x101084001fdf0000 0x0202108003fbe000 0x9073fc001fff8005 0xd20e7f8003fff000

def z102 : W := mkw 0x008440020066c2a8 0x40108800400cd855 0xd98c600001ffc3fd 0xbb318c00003ff87f

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0xb80c0001e01c407f 0x370180003c03880f

def z104 : W := mkw 0x000080000a181451 0x800010000143028a 0x180000001e1c7c7c 0x0300000003c38f8f

def z105 : W := mkw 0x0831af319b19b5f5 0xa10635e6336336be 0x9873ff319f1fffff 0xd30e7fe633e3ffff

def z106 : W := mkw 0x222babfdea181451 0x8445757fbd43028a 0xbe0f83fffe1c7c7f 0x77c1f07fffc38f8f

def z107 : W := mkw 0x020a004042080410 0x8041400808410082 0x360c00c0660c4c18 0x26c180180cc18983

def z108 : W := mkw 0x27ef7bfde2080410 0x84fdef7fbc410082 0xf7ffffffe60c4c1b 0xfefffffffcc18983

def z109 : W := mkw 0x0d702eba95a1eba6 0x21ae05d752b43d74 0x41f07c3e01e38380 0x883e0f87c03c7070

def z110 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xfffffc01ffffc07f 0xffffff803ffff80f

def z111 : W := mkw 0x0d71afbb9db1fbe7 0x21ae35f773b63f7c 0xc9f3ff3f99f3b3e7 0xd93e7fe7f33e767c

def z112 : W := mkw 0x17de540015c70000 0x02fbca8002b8e000 0xc7fffc0001e38001 0xf8ffff80003c7000

def z113 : W := mkw 0x17fed6aa1fff6b06 0x02ffdad543ffed60 0xd7fffc3e1fff8385 0xfaffff87c3fff070

def z114 : W := mkw 0x081084001911b1e5 0x210210800322363c 0x8873fc001913b3e5 0xd10e7f800322767c

def z115 : W := mkw 0x17def4109fdf80a0 0x02fbde8213fbf014 0xdffffc319fff83e7 0xfbffff8633fff07c

def z116 : W := mkw 0x020b81414a181451 0x804170282943028a 0x8e0383c19e103c67 0x51c0707833c2078c

def z117 : W := mkw 0x27ef7bffe020c2a8 0x44fdef7ffc041855 0xefffffffe00043fb 0xfdfffffffc00087f

def z118 : W := mkw 0x08b5ef37b977f3ed 0x6116bde6f72efe7d 0xf9ffff3ff9fff3ff 0xff3fffe7ff3ffe7f

def z119 : W := mkw 0x20212bffe0206b06 0x0404257ffc040d60 0x280003ffe0007f82 0x0500007ffc000ff0

def z120 : W := mkw 0x27fffffdf9110000 0x04ffffffbf222000 0xe7fffffff9138007 0xfcffffffff227000

def z121 : W := mkw 0x27effbfdea181451 0x84fdff7fbd43028a 0xe7fffffffe003c03 0xfcffffffffc00780

def z122 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xd18c603e01ff8385 0xba318c07c03ff070

def z123 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xf980603e01e3c386 0xbf300c07c03c7870

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000001c407c 0x030000000003880f

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0x360000c006004c00 0x26c0001800c00980

def z126 : W := mkw 0x17de540017cf0000 0x02fbca8002f9e000 0x57fc7c0007ef8000 0xaaff8f8000fdf000

def z127 : W := mkw 0x2fef7bfde000b1e5 0x25fdef7fbc00163c 0xefffffffe00033e3 0xfdfffffffc00067c

def z128 : W := mkw 0x276b9be94a181451 0x84ed737d2943028a 0xbe7f9fc1fe1c7c7f 0x77cff3f83fc38f8f

def z129 : W := mkw 0x1fdffd119fdf90e1 0x23fbffa233fbf21c 0xd7fffc019fff8065 0xfaffff8033fff00c

def z130 : W := mkw 0x002002aa00206b06 0x0004005540040d60 0x280003fe00007f82 0x0500007fc0000ff0

def z131 : W := mkw 0x0550000015800000 0x00aa000002b00000 0xd7f000001fe00004 0xfafe000003fc0000

def z132 : W := mkw 0x27ce50cc60000000 0x04f9ca198c000000 0x678c00ce60000000 0x2cf18019cc000000

def z133 : W := mkw 0x020b014140000000 0x0041602828000000 0x060383c000000000 0x40c0707800000000

def z134 : W := mkw 0x15d4540015c70000 0x02ba8a8002b8e000 0xd7f07c001fe38004 0xfafe0f8003fc7000

def z135 : W := mkw 0x0831af71d911b5f5 0xa10635ee3b2236be 0xa873fff1f913ffff 0xd50e7ffe3f227fff

def z136 : W := mkw 0x155084001fdf0000 0x02aa108003fbe000 0xd7f000001fff8004 0xfafe000003fff000

def z137 : W := mkw 0x0010840019110000 0x0002108003222000 0x0000000019138004 0x0000000003227000

def z138 : W := mkw 0x101084001fdf0000 0x0202108003fbe000 0x100000001fff8004 0x0200000003fff000

def z139 : W := mkw 0x20212bfde0000000 0x0404257fbc000000 0x200003ffe0000002 0x0400007ffc000000

def z140 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0073ff301903b380 0xc00e7fe603207670

def z141 : W := mkw 0x056002a800000000 0x00ac005500000000 0xe7f003fe00000002 0xfcfe007fc0000000

def z142 : W := mkw 0x020b014140000000 0x0041602828000000 0x000f8001e0000001 0x0001f0003c000000

def z143 : W := mkw 0x074a100000000000 0x00e9420000000000 0x06739c0000000000 0x40ce738000000000

def z144 : W := mkw 0x081004001101a1a4 0x2102008002203434 0x0000000001038380 0x0000000000207070

def z145 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x47f3fc001fe38000 0xc8fe7f8003fc7000

def z146 : W := mkw 0x27ef7bffe066c2a8 0x44fdef7ffc0cd855 0xe7ffffffe1e38383 0xfcfffffffc3c7070

def z147 : W := mkw 0x00a462bea066ebae 0x40148c57d40cdd75 0xf98c63ffe1ffffff 0xbf318c7ffc3fffff

def z148 : W := mkw 0x05712bbb95a06b06 0x00ae257772b40d60 0xfff3ffff9fe07f87 0xfffe7ffff3fc0ff0

def z149 : W := mkw 0x020b81434a385651 0x8041702869470aca 0xff8f83fffffc7fff 0xfff1f07fffff8fff

def z150 : W := mkw 0x2f7bbff9d911b1e5 0x25ef77ff3b22363c 0x8e73fff19913b3e7 0xd1ce7ffe3322767c

def z151 : W := mkw 0x0001014140000000 0x0000202828000000 0x200003c1e0000002 0x040000783c000000

def z152 : W := mkw 0x00846014a0000000 0x00108c0294000000 0x000c6001e0000001 0x00018c003c000000

def z153 : W := mkw 0x175a94001f990000 0x02eb528003f32000 0x06739c001e000000 0x40ce738003c00000

def z154 : W := mkw 0x27effbfdea181451 0x84fdff7fbd43028a 0xfffffffffe1c7c7f 0xffffffffffc38f8f

def z155 : W := mkw 0x0000201080000000 0x0000040210000000 0x8000603180000003 0x90000c0630000000

def z156 : W := mkw 0x0084400420000000 0x0010880084000000 0x618c000e60000000 0x2c318001cc000000

def z157 : W := mkw 0x0a3b8f615b193555 0xa14771ec2b6326aa 0xbe7f9fc1fe1c7c7f 0x77cff3f83fc38f8f

def z158 : W := mkw 0x020b81414a181451 0x804170282943028a 0x960f83c01e1c3c05 0x72c1f07803c38780

def z159 : W := mkw 0x0001014140001451 0x800020282800028a 0xb80c03c1e01c7c7f 0x370180783c038f8f

def z160 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0x06739fc000000000 0x40ce73f800000000

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0xe180003e00000002 0xbc300007c0000000

def z162 : W := mkw 0x00a56b35a0000000 0x0014ad66b4000000 0xe1ffff3fe0000003 0xfc3fffe7fc000000

def z163 : W := mkw 0x077a02ea57a86f16 0x80ef405d4af50de2 0xfffc03fe7fec7f9e 0xffff807fcffd8ff3

def z164 : W := mkw 0x07ee52a800000000 0x00fdca5500000000 0xe7fffffe00000003 0xfcffffffc0000000

def z165 : W := mkw 0x20212bfde0000000 0x0404257fbc000000 0xa073ffffe0000003 0xd40e7ffffc000000

def z166 : W := mkw 0x05f462beb5e6ebae 0x40be8c57d6bcdd75 0xf9fc603fe1ffc3ff 0xbf3f8c07fc3ff87f

def z167 : W := mkw 0x08b46e36b167e3ac 0x61168dc6d62cfc75 0xf9fc7c3fe1ffc3ff 0xbf3f8f87fc3ff87f

def z168 : W := mkw 0x0000000620204208 0x40000000c4040841 0x2000000e60004018 0x04000001cc000803

def z169 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x718c603e61efc398 0xae318c07cc3df873

def z170 : W := mkw 0x08012911800090e1 0x210025223000121c 0x0000000180000060 0x000000003000000c

def z171 : W := mkw 0x0d71af319d91b1e5 0x21ae35e633b2363c 0xdff3ff319ff3b3e7 0xfbfe7fe633fe767c

def z172 : W := mkw 0x20012955e0000000 0x0400252abc000000 0x00000001e0000000 0x000000003c000000

def z173 : W := mkw 0x0084400000460000 0x001088000008c000 0xd18c600001ff8005 0xba318c00003ff000

def z174 : W := mkw 0x05e462bea066c2a8 0x40bc8c57d40cd855 0xfffc63ffe1ffc3ff 0xffff8c7ffc3ff87f

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800003001000386 0x9100000600200070

def z176 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0x000c6001e01f8079 0x00018c003c03f00f

def z177 : W := mkw 0x057002a815802906 0x00ae005502b00520 0x067003c01e003c00 0x40ce007803c00780

def z178 : W := mkw 0x17ce500006ce0000 0x02f9ca0000d9c000 0xd78c600007ff8005 0xbaf18c0000fff000

def z179 : W := mkw 0x002022bea020ebae 0x40040457d4041d75 0x280003ffe0007ffa 0x0500007ffc000fff

def z180 : W := mkw 0x075a80001f980000 0x00eb500003f30000 0xd7ff80001ffc0005 0xfafff00003ff8000

def z181 : W := mkw 0x0021ab3188101041 0x0004356631020208 0x8873ff3198103067 0xd10e7fe63302060c

def z182 : W := mkw 0x0d71afb99911b1e5 0x21ae35f73322363c 0xeff3ffff9913b3e7 0xfdfe7ffff322767c

def z183 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0xe7f39ffe00000002 0xfcfe73ffc0000000

def z184 : W := mkw 0x2fff7ffdf101a1a4 0x25ffefffbe203434 0xe7ffffffe1038383 0xfcfffffffc207070

def z185 : W := mkw 0x0550008a15a04a02 0x00aa001142b40940 0xf7f000ce1fe04c04 0xfefe0019c3fc0980

def z186 : W := mkw 0x00212b3180000000 0x0004256630000000 0x0000033180000002 0x0000006630000000

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x060003c01e003c00 0x40c0007803c00780

def z188 : W := mkw 0x0084e016aa7ed6f9 0xc0109c02d54fdadf 0xf98c603fffffffff 0xbf318c07ffffffff

def z189 : W := mkw 0x0540008800000000 0x00a8001100000000 0x678000ce00000000 0x2cf00019c0000000

def z190 : W := mkw 0x08302e309101a1a4 0x210605c612203434 0x88707c31811383e7 0x910e0f863022707c

def z191 : W := mkw 0x07ce7014a0000000 0x00f9ce0294000000 0xe7fffc3fe0000003 0xfcffff87fc000000

def z192 : W := mkw 0x074a00ca46a84e12 0x80e9401948d509c2 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z193 : W := mkw 0x17ded4001fdf1451 0x82fbda8003fbe28a 0xdffffc001ffffc7d 0xfbffff8003ffff8f

def z194 : W := mkw 0x228e504460000000 0x0451ca088c000000 0x000c000060000000 0x000180000c000000

def z195 : W := mkw 0x2feffffde81190e1 0x25fdffffbd02321c 0xe7ffffffe0138063 0xfcfffffffc02700c

def z196 : W := mkw 0x0001810108101041 0x0000302021020208 0x8803830198103067 0x510070603302060c

def z197 : W := mkw 0x0d702eba95a1eba6 0x21ae05d752b43d74 0xfff07ffe1fe3ff86 0xfffe0fffc3fc7ff0

def z198 : W := mkw 0x00b46236b166e3ac 0x40168c46d62cdc75 0xf9fc633ff9fff3ff 0xff3f8c67ff3ffe7f

def z199 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfffc03fffffc7fff 0xffff807fffff8fff

def z200 : W := mkw 0x028f6155e0000000 0x0051ec2abc000000 0xe78fe3ffe0000003 0xfcf1fc7ffc000000

def z201 : W := mkw 0x000000020066c2a8 0x40000000400cd855 0x0000000001e38380 0x00000000003c7070

def z202 : W := mkw 0x028fe155ea181451 0x8051fc2abd43028a 0xff8fe3fffe1c7c7f 0xfff1fc7fffc38f8f

def z203 : W := mkw 0x175a94001fdf0000 0x02eb528003fbe000 0x16739c001fff8004 0x42ce738003fff000

def z204 : W := mkw 0x20212bffe020c2a8 0x4404257ffc041855 0x280003ffe00043fa 0x0500007ffc00087f

def z205 : W := mkw 0x077b83eb5fb87f57 0x80ef707d6bf70fea 0xffff83fffffc7fff 0xfffff07fffff8fff

def z206 : W := mkw 0x35f47ebcb5c70000 0x06be8fd796b8e000 0x41f07c3e01e38000 0x883e0f87c03c7000

def z207 : W := mkw 0x0010000215a06b06 0x0002000042b40d60 0x0000000001e00380 0x00000000003c0070

def z208 : W := mkw 0x27ce50cc62080410 0x84f9ca198c410082 0x778c00ce660c4c18 0x2ef18019ccc18983

def z209 : W := mkw 0x00846016a0204200 0x00108c02d4040840 0xf98c603fe1e04387 0xbf318c07fc3c0870

def z210 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x77f003ce1ee07c00 0x6efe0079c3dc0f80

def z211 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x067ffc001e1f8001 0x40cfff8003c3f000

def z212 : W := mkw 0x05f442ae35e66b0e 0x40be8855c6bccd61 0xfffc03fe7fec7f9e 0xffff807fcffd8ff3

def z213 : W := mkw 0x0094c40019570000 0x00129880032ae000 0xd1fffc0019ff8005 0xfa3fff80033ff000

def z214 : W := mkw 0x17ce500626ee4208 0x42f9ca00c4ddc841 0x778c000e66ec4018 0x2ef18001ccdd8803

def z215 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x41fffc3fe0000001 0x883fff87fc000000

def z216 : W := mkw 0x083086201911b1e5 0x210610c40322363c 0x887003301913b3e6 0xd10e00660322767c

def z217 : W := mkw 0x00846014a0000000 0x00108c0294000000 0xe18c603fe0000003 0xbc318c07fc000000

def z218 : W := mkw 0x08202a308000a1a4 0x2104054610001434 0x0000003000000380 0x0000000600000070

def z219 : W := mkw 0x00312b3191002104 0x0006256632200420 0x8873ff3199003387 0xd10e7fe633200670

def z220 : W := mkw 0x057002a811002104 0x00ae005502200420 0xeff003fe19003386 0xfdfe007fc3200670

def z221 : W := mkw 0x0010000215a06b06 0x0002000042b40d60 0xbe0003c01fe07f86 0x77c0007803fc0ff0

def z222 : W := mkw 0x0000000204a04a02 0x0000000040940940 0x1000000006e04c00 0x0200000000dc0980

def z223 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x47f3fffe00000000 0xc8fe7fffc0000000

def z224 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x41f0003e01e00380 0x883e0007c03c0070

def z225 : W := mkw 0x0000000200204200 0x0000000040040840 0x4180003e01e00380 0x88300007c03c0070

def z226 : W := mkw 0x17dfd5415fdf1451 0x82fbfaa82bfbe28a 0xd7fffc01ffff807d 0xfaffff803ffff00f

def z227 : W := mkw 0x020a80000a180000 0x0041500001430000 0x960f80001e1c0005 0x72c1f00003c38000

def z228 : W := mkw 0x17fed6a81fdf0000 0x02ffdad503fbe000 0xf7fffffe1fff8007 0xfeffffffc3fff000

def z229 : W := mkw 0x25712bfff5a06b06 0x04ae257ffeb40d60 0xfff003ffffe07f86 0xfffe007ffffc0ff0

def z230 : W := mkw 0x002002a800002906 0x0004005500000520 0x000003c000003c00 0x0000007800000780

def z231 : W := mkw 0x08318f211911b1e5 0x210631e42322363c 0x08739f001913b3e4 0x410e73e00322767c

def z232 : W := mkw 0x128ed4000a5f0000 0x0251da80014be000 0x000ffc00001f8001 0x0001ff800003f000

def z233 : W := mkw 0x2ffffffff977f3ed 0x65ffffffff2efe7d 0xfffffffff9fff3ff 0xffffffffff3ffe7f

def z234 : W := mkw 0x076b03e940000000 0x00ed607d28000000 0xe7ff83ffe0000003 0xfcfff07ffc000000

def z235 : W := mkw 0x25e47abca0000000 0x04bc8f5794000000 0xe7f07ffe00000002 0xfcfe0fffc0000000

def z236 : W := mkw 0x020b81414a181451 0x804170282943028a 0x960f8001fe1c007d 0x72c1f0003fc3800f

def z237 : W := mkw 0x081084021977f3ed 0x61021080432efe7d 0x1800000019fff3fc 0x03000000033ffe7f

def z238 : W := mkw 0x27ff7bfdf5800000 0x04ffef7fbeb00000 0xf7ffffffffe00007 0xfefffffffffc0000

def z239 : W := mkw 0x0010000015800000 0x0002000002b00000 0x100000001fe00004 0x0200000003fc0000

def z240 : W := mkw 0x076b83e94a181451 0x80ed707d2943028a 0xffff83fffe1c7c7f 0xfffff07fffc38f8f

def z241 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xffffffffe01c407f 0xfffffffffc03880f

def z242 : W := mkw 0x077b03eb55a06b06 0x00ef607d6ab40d60 0xffff83ffffe07f87 0xfffff07ffffc0ff0

def z243 : W := mkw 0x05612bb980000000 0x00ac257730000000 0xe7f3ffff80000003 0xfcfe7ffff0000000

def z244 : W := mkw 0x021b85415b191451 0x804370a82b63228a 0xbe7fffc1ff1ffc7f 0xf7cffff83fe3ff8f

def z245 : W := mkw 0x07ce500000000000 0x00f9ca0000000000 0x478c000000000000 0x28f1800000000000

def z246 : W := mkw 0x0000000200204200 0x0000000040040840 0xff8003fe1fe07f86 0xfff0007fc3fc0ff0

def z247 : W := mkw 0x276b3bfde0000000 0x04ed677fbc000000 0x26739fffe0000002 0x44ce73fffc000000

def z248 : W := mkw 0x20202abca0000000 0x0404055794000000 0x0000003e00000000 0x00000007c0000000

def z249 : W := mkw 0x020a004042080410 0x8041400808410082 0xbe0c03c07e0c7c1e 0x77c180780fc18f83

def z250 : W := mkw 0x00946016b5e6ebae 0x40128c02d6bcdd75 0xf98c603fffffffff 0xbf318c07ffffffff

def z251 : W := mkw 0x0a1b85415b19b5f5 0xa14370a82b6336be 0xbe0f83c1ff1fffff 0x77c1f0783fe3ffff

def z252 : W := mkw 0x175a94001f990000 0x02eb528003f32000 0xd7f39c001fe00004 0xfafe738003fc0000

def z253 : W := mkw 0x0540008a04a04a02 0x00a8001140940940 0xff8000fe07e04f86 0xbff0001fc0fc09f0

def z254 : W := mkw 0x17fed6aa1fff6b06 0x02ffdad543ffed60 0xfffffffe1fffff87 0xffffffffc3fffff0

def z255 : W := mkw 0x1f7b9f211f993145 0x23ef73e423f32628 0x06739f001e003000 0x40ce73e003c00600

def z256 : W := mkw 0x1df47e3095c7a1a4 0x23be8fc612b8f434 0x41f07c3001e38380 0x883e0f86003c7070

def z257 : W := mkw 0x0010a410991180a0 0x0002148213223014 0x8873fc31991383e7 0xd10e7f863322707c

def z258 : W := mkw 0x081185011911b1e5 0x210230a02322363c 0x880383019913b3e7 0x510070603322767c

def z259 : W := mkw 0x2f7b9fe959113145 0x25ef73fd2b222628 0x06739fc018003000 0x40ce73f803000600

def z260 : W := mkw 0x0084400000460000 0x001088000008c000 0x518c000000ec0000 0x2a318000001d8000

def z261 : W := mkw 0x17ded4001f990000 0x02fbda8003f32000 0xc7fffc001e000001 0xf8ffff8003c00000

def z262 : W := mkw 0x028e6056e26ec6b8 0xc051cc0adc4dd8d7 0xff8c60ffe7ffcfff 0xbff18c1ffcfff9ff

def z263 : W := mkw 0x25f47abeb5a06b06 0x04be8f57d6b40d60 0xfff07ffe1fe07f86 0xfffe0fffc3fc0ff0

def z264 : W := mkw 0x1094e416bfffc2a8 0x42129c82d7fff855 0xf98c603fffffc3ff 0xbf318c07fffff87f

def z265 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x2e7003fe1e007f82 0x45ce007fc3c00ff0

def z266 : W := mkw 0x056002a800000000 0x00ac005500000000 0xfff003fe1e007c06 0xfffe007fc3c00f80

def z267 : W := mkw 0x08a56b37a066f3ed 0x6114ad66f40cde7d 0xf98c633fe1fff3ff 0xbf318c67fc3ffe7f

def z268 : W := mkw 0x08212b37a020f3ed 0x61042566f4041e7d 0x2800033fe00073fa 0x05000067fc000e7f

def z269 : W := mkw 0x17dfd5011fdf1041 0x02fbfaa023fbe208 0xdfffff019fffb067 0xfbffffe033fff60c

def z270 : W := mkw 0x075b81415f981451 0x80eb70282bf3028a 0xffff83c1fffc7c7f 0xfffff0783fff8f8f

def z271 : W := mkw 0x07fe52aa15a06b06 0x00ffca5542b40d60 0xfffffffe1fe07f87 0xffffffffc3fc0ff0

def z272 : W := mkw 0x0000000200664208 0x40000000400cc841 0x1000000000ec4018 0x02000000001d8803

def z273 : W := mkw 0x0001010100001041 0x0000202020000208 0x0800030180003062 0x010000603000060c

def z274 : W := mkw 0x0a3baf71d911b1e5 0x214775ee3b22363c 0xae7ffff1f913b3e7 0xf5cffffe3f22767c

def z275 : W := mkw 0x056002aa04a06b06 0x00ac005540940d60 0x7f8003fe06e07f82 0x2ff0007fc0dc0ff0

def z276 : W := mkw 0x17ffff319fdf0000 0x02ffffe633fbe000 0xd7ffff319fff8007 0xfaffffe633fff000

def z277 : W := mkw 0x27ef7bfde0460000 0x04fdef7fbc08c000 0xf7ffffffe1ff8007 0xfefffffffc3ff000

def z278 : W := mkw 0x27ee7abca0000000 0x04fdcf5794000000 0xc7fffc3e00000001 0xf8ffff87c0000000

def z279 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x59f0003e1fe07f84 0x8b3e0007c3fc0ff0

def z280 : W := mkw 0x0094e416b977c2a8 0x40129c82d72ef855 0xf9fffc3ff9ffc3ff 0xff3fff87ff3ff87f

def z281 : W := mkw 0x00002016a020c2a8 0x40000402d4041855 0x2800003fe00043fa 0x05000007fc00087f

def z282 : W := mkw 0x27ff7bfdf1002104 0x04ffef7fbe200420 0xeffffffff9003387 0xfdffffffff200670

def z283 : W := mkw 0x27ef7bffe4a04a02 0x04fdef7ffc940940 0xf7ffffffe6e04c03 0xfefffffffcdc0980

def z284 : W := mkw 0x0010000215e6ebae 0x4002000042bcdd75 0x180000001ffffffc 0x0300000003ffffff

def z285 : W := mkw 0x00002010800080a0 0x0000040210001014 0x88006031811383e7 0x91000c063022707c

def z286 : W := mkw 0x1fffff37bffff3ed 0x63ffffe6f7fffe7d 0xffffff3ffffff3ff 0xffffffe7fffffe7f

def z287 : W := mkw 0x002002aa00206b06 0x0004005540040d60 0xf98003fe01e07f86 0xbf30007fc03c0ff0

def z288 : W := mkw 0x1094c4001fdf0000 0x0212988003fbe000 0xd18c60001fff8005 0xba318c0003fff000

def z289 : W := mkw 0x27effbfdea181451 0x84fdff7fbd43028a 0xe7ffffffe01c007b 0xfcfffffffc03800f

def z290 : W := mkw 0x17ced4000a5f0000 0x02f9da80014be000 0xc7fffc00001f8001 0xf8ffff800003f000

def z291 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x1e7003c01fe07f84 0x43ce007803fc0ff0

def z292 : W := mkw 0x0830ae309911b1e5 0x210615c61322363c 0x08707c301913b3e4 0x810e0f860322767c

def z293 : W := mkw 0x0030862019112104 0x000610c403222420 0x8873ff301913b387 0xd10e7fe603227670

def z294 : W := mkw 0x057002a815802906 0x00ae005502b00520 0xbe7003c01e007c06 0x77ce007803c00f80

def z295 : W := mkw 0x020b014140000000 0x0041602828000000 0xbe0f83c1fe007c07 0x77c1f0783fc00f80

def z296 : W := mkw 0x0031832119103145 0x0006306423220628 0x88738331991033e7 0xd10e70663322067c

def z297 : W := mkw 0x15d4d4001dd70000 0x02ba9a8003bae000 0xc1f3fc0019f38005 0xd83e7f80033e7000

def z298 : W := mkw 0x27ce50ce64a04a02 0x04f9ca19cc940940 0x778c00ce66e04c00 0x2ef18019ccdc0980

def z299 : W := mkw 0x0d7086aa1db1fbe7 0x21ae10d543b63f7c 0xfff003fe1ff3ffe6 0xfffe007fc3fe7ffc

def z300 : W := mkw 0x0df5efbfbdf7fbef 0x61bebdf7f7beff7d 0xffffffffffffffff 0xffffffffffffffff

def z301 : W := mkw 0x220b194140000000 0x0441632828000000 0x00039c0000000000 0x0000738000000000

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0xa60003c000000002 0x74c0007800000000

def z303 : W := mkw 0x020b81414a181451 0x804170282943028a 0x000f8001e01c0079 0x0001f0003c03800f

def z304 : W := mkw 0x020b014140000000 0x0041602828000000 0xa60f83c1e0000003 0x74c1f0783c000000

def z305 : W := mkw 0x074b81cb4eb85e53 0x80e9703969d70bca 0xff8f83cffefc7c7f 0x7ff1f079ffdf8f8f

def z306 : W := mkw 0x0810a4109911b1e5 0x210214821322363c 0x880060319913b3e7 0x91000c063322767c

def z307 : W := mkw 0x08212b71c000b5f5 0xa104256e380016be 0x280003f1e0007ffa 0x0500007e3c000fff

def z308 : W := mkw 0x0540000004800000 0x00a8000000900000 0x5780000006e00000 0x2af0000000dc0000

def z309 : W := mkw 0x1fffffbb9ffffbe7 0x23fffff773ffff7c 0xffffffff9fffffe7 0xfffffffff3fffffc

def z310 : W := mkw 0x175a94001f990000 0x02eb528003f32000 0x967f9c001e1c0005 0x72cff38003c38000

def z311 : W := mkw 0x274a10c840000000 0x04e9421908000000 0x060000c000000000 0x00c0001800000000

def z312 : W := mkw 0x08312f319101a1a4 0x210625e632203434 0x8073ff3181038383 0xd00e7fe630207070

def z313 : W := mkw 0x00002010800080a0 0x0000040210001014 0xb80c6031e11fc3ff 0xb7018c063c23f87f

def z314 : W := mkw 0x081084021db1fbe7 0x2102108043b63f7c 0x180000001ff3ffe4 0x0300000003fe7ffc

def z315 : W := mkw 0x101084021fff6b06 0x0202108043ffed60 0x180000001fffff84 0x0300000003fffff0

def z316 : W := mkw 0x020b81010a181041 0x0041702021430208 0x9e0f83019e1c3067 0x73c1f06033c3860c

def z317 : W := mkw 0x020b014140000000 0x0041602828000000 0xbe0f83c1e01c407f 0x77c1f0783c03880f

def z318 : W := mkw 0x0f7baffbdfb9fff7 0xa1ef75ff7bf73ffe 0xffffffffffffffff 0xffffffffffffffff

def z319 : W := mkw 0x3ffffffdffdfb1e5 0x27ffffffbffbf63c 0xffffffffffffb3e7 0xfffffffffffff67c

def z320 : W := mkw 0x0d718fab1db17b47 0x21ae31f563b62f68 0xfff39ffe1fe07f86 0xfffe73ffc3fc0ff0

def z321 : W := mkw 0x222b2bfde0000000 0x0445657fbc000000 0xa60f83ffe0000003 0x74c1f07ffc000000

def z322 : W := mkw 0x22af7bfde0000000 0x0455ef7fbc000000 0x200fffffe0000003 0x0401fffffc000000

def z323 : W := mkw 0x020a80000a181451 0x804150000143028a 0x9e0f80001e1c7c7d 0x73c1f00003c38f8f

def z324 : W := mkw 0x27ef7bfde04680a8 0x44fdef7fbc08d015 0xe7ffffffe01f807b 0xfcfffffffc03f00f

def z325 : W := mkw 0x2abfff75f911b1e5 0x2557ffeebf22363c 0x887fff31f913b3e7 0xd10fffe63f22767c

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0x8073fc0000000001 0xd00e7f8000000000

def z327 : W := mkw 0x0570022015802104 0x00ae004402b00420 0xdff003301fe03386 0xfbfe006603fc0670

def z328 : W := mkw 0x27cfd1cd6a181451 0x84f9fa39ad43028a 0xff8f83cffe1c7c7f 0x7ff1f079ffc38f8f

def z329 : W := mkw 0x0084400000460000 0x001088000008c000 0xf98c6001e1ffc07f 0xbf318c003c3ff80f

def z330 : W := mkw 0x08210b2100003145 0x2104216420000628 0x0000030000003000 0x0000006000000600

def z331 : W := mkw 0x27ef5be940000000 0x04fdeb7d28000000 0xc7ffffc000000001 0xf8fffff800000000

def z332 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0xb80c6001e01fc07f 0x37018c003c03f80f

def z333 : W := mkw 0x17dff557ffffd6f9 0xc2fbfeaafffffadf 0xffffffffffffffff 0xffffffffffffffff

def z334 : W := mkw 0x27ef7bfde00080a0 0x04fdef7fbc001014 0xefffffffe11383e7 0xfdfffffffc22707c

def z335 : W := mkw 0x0010040011010000 0x0002008002202000 0x00707c0001038000 0x800e0f8000207000

def z336 : W := mkw 0x08312f319101b1e5 0x210625e63220363c 0x08707f318103b3e2 0x810e0fe63020767c

def z337 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x5980603e01ffc3fc 0x8b300c07c03ff87f

def z338 : W := mkw 0x2831affdf911b1e5 0x250635ffbf22363c 0xa873fffff913b3e7 0xd50e7fffff22767c

def z339 : W := mkw 0x129ed4001fdf0000 0x0253da8003fbe000 0x100ffc001fff8005 0x0201ff8003fff000

def z340 : W := mkw 0x0000800008100000 0x0000100001020000 0x8003800018100005 0x5000700003020000

def z341 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0xa67f9fc1e0000003 0x74cff3f83c000000

def z342 : W := mkw 0x00000000004680a8 0x400000000008d015 0x00000000001f8078 0x000000000003f00f

def z343 : W := mkw 0x00846014a0460000 0x00108c029408c000 0xf18c603fe1ff8007 0xbe318c07fc3ff000

def z344 : W := mkw 0x0001a111881090e1 0x000034223102121c 0x8803e3319913b3e7 0xd1007c663322767c

def z345 : W := mkw 0x00210b2100000000 0x0004216420000000 0x00739f0000000000 0x400e73e000000000

def z346 : W := mkw 0x00846014a0000000 0x00108c0294000000 0xf98c603fe01c407f 0xbf318c07fc03880f

def z347 : W := mkw 0x077b83e95f983d57 0x80ef707d2bf307aa 0xbe7f83c1fe1c7c7f 0x77cff0783fc38f8f

def z348 : W := mkw 0x328ffd55ea5f0000 0x0651ffaabd4be000 0x000ffc01e01f8001 0x0001ff803c03f000

def z349 : W := mkw 0x1550140015810000 0x02aa028002b02000 0x00701c0000000000 0x000e038000000000

def z350 : W := mkw 0x128ef414aa5f80a8 0x4251de82954bf015 0x000ffc01e01f8079 0x0001ff803c03f00f

def z351 : W := mkw 0x1df5ff319dd7b1e5 0x23bebfe633baf63c 0xc9f3ff3199f3b3e7 0xd93e7fe6333e767c

def z352 : W := mkw 0x08318f2119113145 0x210631e423222628 0x88739f3019003386 0xd10e73e603200670

def z353 : W := mkw 0x081084001b19b5f5 0xa1021080036336be 0x180000001f1ffffc 0x0300000003e3ffff

def z354 : W := mkw 0x020a004040000000 0x0041400808000000 0x260c00c060000000 0x24c180180c000000

def z355 : W := mkw 0x08212bbb8020fbe7 0x2104257770041f7c 0x280003ff80007fe2 0x0500007ff0000ffc

def z356 : W := mkw 0x0001814148101451 0x800030282902028a 0xa80383c1f8107c7f 0x550070783f020f8f

def z357 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xf9f0003e01e04386 0xbf3e0007c03c0870

def z358 : W := mkw 0x077a82aa1fb86b06 0x00ef505543f70d60 0xffff83fe1ffc7f87 0xfffff07fc3ff8ff0

def z359 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x578c00001fff8004 0x2af1800003fff000

def z360 : W := mkw 0x121a84001fdf0000 0x0243508003fbe000 0x960f80001fff8005 0x72c1f00003fff000

def z361 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x718c600fe0ffc079 0x2e318c01fc1ff80f

def z362 : W := mkw 0x028e500000000000 0x0051ca0000000000 0x000ffc0000000001 0x0001ff8000000000

def z363 : W := mkw 0x128ef416aa7fc2a8 0x4251de82d54ff855 0xf98ffc3fe1ffc3ff 0xbf31ff87fc3ff87f

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800000180100067 0x110000003002000c

def z365 : W := mkw 0x120a94000a190000 0x0241528001432000 0x00039c0000000000 0x0000738000000000

def z366 : W := mkw 0x00846010804680a0 0x00108c021008d014 0xd98c603181ff83e7 0xbb318c06303ff07c

def z367 : W := mkw 0x17def414bfdf80a8 0x42fbde8297fbf015 0xd7fffc01ffff807d 0xfaffff803ffff00f

def z368 : W := mkw 0x2ffffffdf9113145 0x25ffffffbf222628 0xe7fffffff8003003 0xfcffffffff000600

def z369 : W := mkw 0x17ffd7eb5fff7f57 0x82fffafd6bffefea 0xffffffffffffffff 0xffffffffffffffff

def z370 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x180c6001e1ffc3fd 0x03018c003c3ff87f

def z371 : W := mkw 0x020b81414a181451 0x804170282943028a 0xa60f83c1fe003c03 0x74c1f0783fc00780

def z372 : W := mkw 0x07ef7b3180000000 0x00fdef6630000000 0xc7ffff3180000003 0xf8ffffe630000000

def z373 : W := mkw 0x008440062066c2a8 0x40108800c40cd855 0x798c000e61ffc3fc 0x2f318001cc3ff87f

def z374 : W := mkw 0x000020128066c2a8 0x40000402500cd855 0x9800603181ffc3ff 0x93000c06303ff87f

def z375 : W := mkw 0x055084001d910000 0x00aa108003b22000 0xd7f3fc001ff38005 0xfafe7f8003fe7000

def z376 : W := mkw 0x022b83eb4a387f57 0x8045707d69470fea 0xbe0f83fffe1c7fff 0x77c1f07fffc38fff

def z377 : W := mkw 0x000000020066c2a8 0x40000000400cd855 0xf980003e01ffc3fe 0xbf300007c03ff87f

def z378 : W := mkw 0x028ec0000a5e0000 0x0051d800014bc000 0xd78fe0001fff8005 0xfaf1fc0003fff000

def z379 : W := mkw 0x128ed4000a5f0000 0x0251da80014be000 0xd18ffc0001ff8005 0xba31ff80003ff000

def z380 : W := mkw 0x101084001fdf1451 0x8202108003fbe28a 0x180000001ffffc7c 0x0300000003ffff8f

def z381 : W := mkw 0x37dffd55ffdf0000 0x06fbffaabffbe000 0xd7fffc01ffff8005 0xfaffff803ffff000

def z382 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x080003319913b3e6 0x010000663322767c

def z383 : W := mkw 0x020b81414a180000 0x0041702829430000 0xb60f83c1fe1c0007 0x76c1f0783fc38000

def z384 : W := mkw 0x0030022011002104 0x0006004402200420 0x0070030018003000 0x400e006003000600

def z385 : W := mkw 0x0885ed15a85790e9 0x6110bda2b50af21d 0x000ffc01e01f8079 0x0001ff803c03f00f

def z386 : W := mkw 0x181084001fdfb1e5 0x2302108003fbf63c 0x180000001fffb3e4 0x0300000003fff67c

def z387 : W := mkw 0x003002aa15a06b06 0x0006005542b40d60 0x380003fe1fe07f86 0x0700007fc3fc0ff0

def z388 : W := mkw 0x05f462beb5e6ebae 0x40be8c57d6bcdd75 0x41f0603e01e38380 0x883e0c07c03c7070

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x280003c000007c02 0x0500007800000f80

def z390 : W := mkw 0x0030022011002104 0x0006004402200420 0x8870033019003386 0xd10e006603200670

def z391 : W := mkw 0x0811ad11991190e1 0x210235a23322321c 0x8073fc0199138065 0xd00e7f803322700c

def z392 : W := mkw 0x25e57bfde0000000 0x04bcaf7fbc000000 0x61f07fffe0000002 0x8c3e0ffffc000000

def z393 : W := mkw 0x25612bfde0000000 0x04ac257fbc000000 0xe7f003ffe0000002 0xfcfe007ffc000000

def z394 : W := mkw 0x020a004042080410 0x8041400808410082 0x060000c006000c00 0x00c0001800c00180

def z395 : W := mkw 0x000000020020c2a8 0x4000000040041855 0x08000000000043f8 0x010000000000087f

def z396 : W := mkw 0x000181010a181451 0x800030202143028a 0x980383019e1c7c7f 0x5300706033c38f8f

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c0001e01c0079 0x000180003c03800f

def z398 : W := mkw 0x27ef5bed60000000 0x04fdeb7dac000000 0x67ff9fce60000000 0x6cfff3f9cc000000

def z399 : W := mkw 0x0a0bad51ca1994f1 0xa14175aa3943329e 0x000ffc01e01f8079 0x0001ff803c03f00f

def z400 : W := mkw 0x0885ed17a877d2e9 0x6110bda2f50efa5d 0xf98ffc3fe1ffc3ff 0xbf31ff87fc3ff87f

def z401 : W := mkw 0x020b81414a181451 0x804170282943028a 0xa60f83c1e01c007b 0x74c1f0783c03800f

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0x28000001e000407a 0x050000003c00080f

def z403 : W := mkw 0x05d46016b5e6c2a8 0x40ba8c02d6bcd855 0xfffc603fffffc3ff 0xffff8c07fffff87f

def z404 : W := mkw 0x0550008a15a06b06 0x00aa001142b40d60 0x7f8000ce1fe07f84 0x2ff00019c3fc0ff0

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00c0001e0000003 0x340180003c000000

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0xbe0c03c1fe1c7c7f 0x77c180783fc38f8f

def z407 : W := mkw 0x020b81414a181451 0x804170282943028a 0xbe0383c01e007c06 0x77c0707803c00f80

def z408 : W := mkw 0x25e47abea066c2a8 0x44bc8f57d40cd855 0x41f07c3e01e38380 0x883e0f87c03c7070

def z409 : W := mkw 0x1010040015c70000 0x0202008002b8e000 0x0000000001e38000 0x00000000003c7000

def z410 : W := mkw 0x1fded4001fdfb1e5 0x23fbda8003fbf63c 0xdffffc001fffb3e5 0xfbffff8003fff67c

def z411 : W := mkw 0x028e4046626e4618 0xc051c808cc4dc8c3 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z412 : W := mkw 0x1ffefe309fdfa1a4 0x23ffdfc613fbf434 0xd7fffc301fff8385 0xfaffff8603fff070

def z413 : W := mkw 0x023b83615b183555 0x8047706c2b6306aa 0xbe7f83f1ff1c7fff 0xf7cff07e3fe38fff

def z414 : W := mkw 0x00002016a020c2a8 0x40000402d4041855 0x0000003e00000380 0x00000007c0000070

def z415 : W := mkw 0x22af7b75e0000000 0x0455ef6ebc000000 0x807fff31e0000003 0xd00fffe63c000000

def z416 : W := mkw 0x27ee52ec60000000 0x04fdca5d8c000000 0xe7fc03fe60000002 0xfcff807fcc000000

def z417 : W := mkw 0x057086aa1db16b06 0x00ae10d543b62d60 0xfff3fffe1ff3ff87 0xfffe7fffc3fe7ff0

def z418 : W := mkw 0x07ffe3fffffeffff 0xc0fffc7fffffdfff 0xffffe3ffffffffff 0xfffffc7fffffffff

def z419 : W := mkw 0x0084400420460008 0x401088008408c001 0x000c0000600c0018 0x000180000c018003

def z420 : W := mkw 0x00002014a0000000 0x0000040294000000 0x2000003fe0000002 0x04000007fc000000

def z421 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x280c603fe01fc3fb 0x05018c07fc03f87f

def z422 : W := mkw 0x27ff7bfff5e6ebae 0x44ffef7ffebcdd75 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x0030022211206304 0x0006004442240c60 0xf9f0033e19e07386 0xff3e0067c33c0e70

def z424 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x77f000fe07e04f80 0xaefe001fc0fc09f0

def z425 : W := mkw 0x020b81414a181451 0x804170282943028a 0x360f80c1e61c4c79 0x26c1f0183cc3898f

def z426 : W := mkw 0x228ff955ea181451 0x8451ff2abd43028a 0xbe0fffc1fe1c7c7f 0x77c1fff83fc38f8f

def z427 : W := mkw 0x0084400620664208 0x40108800c40cc841 0x4180000e00e00000 0x08300001c01c0000

def z428 : W := mkw 0x05c4408e24e64a0a 0x40b88811c49cc941 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z429 : W := mkw 0x27ff7bfff5a06b06 0x04ffef7ffeb40d60 0xe7ffffffe1e00383 0xfcfffffffc3c0070

def z430 : W := mkw 0x057103eb55a07f57 0x80ae207d6ab40fea 0xfff003ffffe07ffe 0xfffe007ffffc0fff

def z431 : W := mkw 0x25e47abca0000000 0x04bc8f5794000000 0xe1fc7c3fe0000003 0xbc3f8f87fc000000

def z432 : W := mkw 0x08008400081190e1 0x210010800102321c 0x0000000000138060 0x000000000002700c

def z433 : W := mkw 0x37fffffdffdf1451 0x86ffffffbffbe28a 0xfffffffffffffc7f 0xffffffffffffff8f

def z434 : W := mkw 0x00012157e020d6f9 0xc000242afc041adf 0x280003ffe0007ffa 0x0500007ffc000fff

def z435 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x08739f31980033e2 0x410e73e63300067c

def z436 : W := mkw 0x25e57bbda0000000 0x04bcaf77b4000000 0xc1f3ff3f80000003 0xd83e7fe7f0000000

def z437 : W := mkw 0x37ef7bfde6ce0000 0x06fdef7fbcd9c000 0xf7ffffffe6ec0003 0xfefffffffcdd8000

def z438 : W := mkw 0x020b81414a181451 0x804170282943028a 0xb80f8001e01c407f 0x3701f0003c03880f

def z439 : W := mkw 0x0001810108101041 0x0000302021020208 0xb80f8301f81c707f 0x7701f0603f038e0f

def z440 : W := mkw 0x0000000200204200 0x0000000040040840 0xf98c003fe1fc43ff 0xbf318007fc3f887f

def z441 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xd7f0003e1fe00384 0xfafe0007c3fc0070

def z442 : W := mkw 0x002002a800000000 0x0004005500000000 0x200003fe00000002 0x0400007fc0000000

def z443 : W := mkw 0x07ded40019110000 0x00fbda8003222000 0xc7fffc0019138005 0xf8ffff8003227000

def z444 : W := mkw 0x28212bfde000b1e5 0x2504257fbc00163c 0x280003ffe00033e2 0x0500007ffc00067c

def z445 : W := mkw 0x25601aa800000000 0x04ac035500000000 0x00701c0000000000 0x000e038000000000

def z446 : W := mkw 0x00846016a0664208 0x40108c02d40cc841 0xf18c603fe0ec401b 0xbe318c07fc1d8803

def z447 : W := mkw 0x228f7955e0000000 0x0451ef2abc000000 0xe18ffc3fe0000003 0xbc31ff87fc000000

def z448 : W := mkw 0x00002010800080a0 0x0000040210001014 0x08000031800003e2 0x010000063000007c

def z449 : W := mkw 0x057002a815802906 0x00ae005502b00520 0xe7f003fe1e003c02 0xfcfe007fc3c00780

def z450 : W := mkw 0x1f7bbf319f99b1e5 0x23ef77e633f3363c 0x8e73ff319f13b3e7 0xd1ce7fe633e2767c

def z451 : W := mkw 0x057022beb5a0ebae 0x40ae0457d6b41d75 0xfff003ffffe07ffe 0xfffe007ffffc0fff

def z452 : W := mkw 0x20a56bfde0000000 0x0414ad7fbc000000 0xe18c63ffe0000003 0xbc318c7ffc000000

def z453 : W := mkw 0x00202a3080000000 0x0004054610000000 0x00707c3000000000 0x800e0f8600000000

def z454 : W := mkw 0x020a80000a180000 0x0041500001430000 0xbe0f83c01e1c7c07 0x77c1f07803c38f80

def z455 : W := mkw 0x37ffffffffff6b06 0x06ffffffffffed60 0xffffffffffffff87 0xfffffffffffffff0

def z456 : W := mkw 0x077b83eb5fb87f57 0x80ef707d6bf70fea 0xfff383fe1fe07f86 0xfffe707fc3fc0ff0

def z457 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x57ff9c001eec0000 0x6afff38003dd8000

def z458 : W := mkw 0x27ce70dce0000000 0x04f9ce1b9c000000 0xe78c60ffe0000003 0xbcf18c1ffc000000

def z459 : W := mkw 0x128e5000024e0000 0x0251ca000049c000 0x000c0000000c0000 0x0001800000018000

def z460 : W := mkw 0x0084400620664208 0x40108800c40cc841 0xf98c003e61ec439e 0xbf318007cc3d8873

def z461 : W := mkw 0x0550000015800000 0x00aa000002b00000 0x067000001e000000 0x40ce000003c00000

def z462 : W := mkw 0x17ded4021fffc2a8 0x42fbda8043fff855 0xdffffc001fffc3fd 0xfbffff8003fff87f

def z463 : W := mkw 0x228ff955ea181451 0x8451ff2abd43028a 0x000ffc01e01c0079 0x0001ff803c03800f

def z464 : W := mkw 0x00846014a00080a0 0x00108c0294001014 0xe98c603fe11383e7 0xbd318c07fc22707c

def z465 : W := mkw 0x020b81414a181451 0x804170282943028a 0x0003800000000000 0x0000700000000000

def z466 : W := mkw 0x057002a815802906 0x00ae005502b00520 0xd7f003c01fe03c04 0xfafe007803fc0780

def z467 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0xd18c6001e1ff807d 0xba318c003c3ff00f

def z468 : W := mkw 0x020b81434a7ed6f9 0xc0417028694fdadf 0xbe0f83c1ffffffff 0x77c1f0783fffffff

def z469 : W := mkw 0x37ffffffffffc2a8 0x46fffffffffff855 0xffffffffffffc3ff 0xfffffffffffff87f

def z470 : W := mkw 0x20210be940000000 0x0404217d28000000 0x000003c000000000 0x0000007800000000

def z471 : W := mkw 0x08302e309101a1a4 0x210605c612203434 0x88707f301903b386 0xd10e0fe603207670

def z472 : W := mkw 0x20212bfde0001451 0x8404257fbc00028a 0x280003ffe0007c7a 0x0500007ffc000f8f

def z473 : W := mkw 0x25e47abea066c2a8 0x44bc8f57d40cd855 0xf9fc7c3fe1ffc3ff 0xbf3f8f87fc3ff87f

def z474 : W := mkw 0x129ed4001b5f0000 0x0253da80036be000 0x807ffc00191f8005 0xd00fff800323f000

def z475 : W := mkw 0x0a0bad51ca1994f1 0xa14175aa3943329e 0xbe0fffc1fe1ffc7f 0x77c1fff83fc3ff8f

def z476 : W := mkw 0x0821af318811b1e5 0x210435e63102363c 0x0803ff318013b3e3 0x01007fe63002767c

def z477 : W := mkw 0x00002016a020c2a8 0x40000402d4041855 0xa800603fe113c3ff 0x95000c07fc22787f

def z478 : W := mkw 0x0020022000002104 0x0004004400000420 0x0800033000003382 0x0100006600000670

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x960000001e000004 0x72c0000003c00000

def z480 : W := mkw 0x2df5ffbdb911b1e5 0x25bebff7b722363c 0xc9f3ff3f9913b3e7 0xd93e7fe7f322767c

def z481 : W := mkw 0x057002a815800000 0x00ae005502b00000 0xf7f003fe1fe00006 0xfefe007fc3fc0000

def z482 : W := mkw 0x27ef7bffe0664208 0x44fdef7ffc0cc841 0xf7ffffffe0ec401b 0xfefffffffc1d8803

def z483 : W := mkw 0x0a2bab71ca18b5f5 0xa145756e394316be 0xbe0f83f1fe1c7fff 0x77c1f07e3fc38fff

def z484 : W := mkw 0x000080000a180000 0x0000100001430000 0x100000001e1c0004 0x0200000003c38000

def z485 : W := mkw 0x0831af339db1fbe7 0x210635e673b63f7c 0x9873ff319ff3ffe7 0xd30e7fe633fe7ffc

def z486 : W := mkw 0x0540008804800802 0x00a8001100900100 0x060000c006000c00 0x00c0001800c00180

def z487 : W := mkw 0x0001014140001451 0x800020282800028a 0x00000001e0000078 0x000000003c00000f

def z488 : W := mkw 0x377b9fe95f990000 0x06ef73fd2bf32000 0x06739fc01e000000 0x40ce73f803c00000

def z489 : W := mkw 0x27ef7bffe0204200 0x04fdef7ffc040840 0xffffffffe1e04387 0xfffffffffc3c0870

def z490 : W := mkw 0x27cf51cd60000000 0x04f9ea39ac000000 0xe78f83cfe0000003 0x7cf1f079fc000000

def z491 : W := mkw 0x003022309100a1a4 0x0006044612201434 0x887063319913b3e7 0xd10e0c663322767c

def z492 : W := mkw 0x056002aa00206b06 0x00ac005540040d60 0xeff003fe00007f82 0xfdfe007fc0000ff0

def z493 : W := mkw 0x17ced0000ede0000 0x02f9da0001dbc000 0xd78f80001efc0005 0x7af1f00003df8000

def z494 : W := mkw 0x228f7957e066c2a8 0x4451ef2afc0cd855 0xf98ffc3fe1ffc3ff 0xbf31ff87fc3ff87f

def z495 : W := mkw 0x00856157e066d6f9 0xc010ac2afc0cdadf 0xf98c63ffe1ffffff 0xbf318c7ffc3fffff

def z496 : W := mkw 0x0001014140001451 0x800020282800028a 0xbe0003c1fe007c7e 0x77c000783fc00f8f

def z497 : W := mkw 0x20a56bffe066c2a8 0x4414ad7ffc0cd855 0xf98c63ffe1ffc3ff 0xbf318c7ffc3ff87f

def z498 : W := mkw 0x276b3bf9c0000000 0x04ed677f38000000 0x8673fff180000003 0xd0ce7ffe30000000

def z499 : W := mkw 0x27ce70dee066c2a8 0x44f9ce1bdc0cd855 0xff8c60ffe1ffc3ff 0xbff18c1ffc3ff87f

def z500 : W := mkw 0x0001291180000000 0x0000252230000000 0x0003fc0180000001 0x00007f8030000000

def z501 : W := mkw 0x37ded4cc7fdf0000 0x06fbda998ffbe000 0xf7fffcce7fff8005 0xfeffff99cffff000

def z502 : W := mkw 0x0031af3199110000 0x000635e633222000 0x8073ff3199138007 0xd00e7fe633227000

def z503 : W := mkw 0x05d4400015c60000 0x00ba880002b8c000 0xd7fc60001fff8005 0xfaff8c0003fff000

def z504 : W := mkw 0x17fef6bebfffebae 0x42ffded7d7fffd75 0xffffffffffffffff 0xffffffffffffffff

def z505 : W := mkw 0x057002a815802906 0x00ae005502b00520 0x8e7003f01f003f86 0xd1ce007e03e007f0

def z506 : W := mkw 0x2df47ebcb101a1a4 0x25be8fd796203434 0x41f07c3e01038380 0x883e0f87c0207070

def z507 : W := mkw 0x028fe155ea5e94f9 0xc051fc2abd4bd29f 0xbe0fe3c1fe1ffc7f 0x77c1fc783fc3ff8f

def z508 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000600001138005 0x90000c0000227000

def z509 : W := mkw 0x277b1beb55a06b06 0x04ef637d6ab40d60 0xfff39ffe1fe07f86 0xfffe73ffc3fc0ff0

def z510 : W := mkw 0x17fed6201fdf2104 0x02ffdac403fbe420 0xdfffff301fffb387 0xfbffffe603fff670

def z511 : W := mkw 0x175b95415f991451 0x82eb72a82bf3228a 0xbe7f9fc1fe1c7c7f 0x77cff3f83fc38f8f

def z512 : W := mkw 0x27effbffea7ed6f9 0xc4fdff7ffd4fdadf 0xffffffffffffffff 0xffffffffffffffff

def z513 : W := mkw 0x020a80000a180000 0x0041500001430000 0x000f8000001c0001 0x0001f00000038000

def z514 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x678c03ffe0000002 0x2cf1807ffc000000

def z515 : W := mkw 0x08318f2119113145 0x210631e423222628 0x8073ff001913b005 0xd00e7fe003227600

def z516 : W := mkw 0x056002aa00204200 0x00ac005540040840 0xfff003fe01e04386 0xfffe007fc03c0870

def z517 : W := mkw 0x15d47416b5e7c2a8 0x42ba8e82d6bcf855 0xf9fc7c3fe1ffc3ff 0xbf3f8f87fc3ff87f

def z518 : W := mkw 0x0000008a00204a02 0x0000001140040940 0x200000ce00004c00 0x04000019c0000980

def z519 : W := mkw 0x17de500017ce0000 0x02fbca0002f9c000 0xd7fc00001fec0004 0xfaff800003fd8000

def z520 : W := mkw 0x0540000000000000 0x00a8000000000000 0xc7f0000000000000 0xf8fe000000000000

def z521 : W := mkw 0x0a3baf71db19b5f5 0xa14775ee3b6336be 0x8e73fff19f13bfe7 0xd1ce7ffe33e277fc

def z522 : W := mkw 0x1fffdf211fdf3145 0x23fffbe423fbe628 0xd7ffff001fffb005 0xfaffffe003fff600

def z523 : W := mkw 0x228f7955e04680a8 0x4451ef2abc08d015 0x000ffc01e01f8079 0x0001ff803c03f00f

def z524 : W := mkw 0x000080000a181451 0x800010000143028a 0x000000001e003c00 0x0000000003c00780

def z525 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0x880c6031e11f83ff 0x91018c063c23f07f

def z526 : W := mkw 0x0fffff319911b1e5 0x21ffffe63322363c 0xcfffff319913b3e7 0xf9ffffe63322767c

def z527 : W := mkw 0x0000800008101041 0x0000100001020208 0x0800000018103064 0x010000000302060c

def z528 : W := mkw 0x27ee7afce0000000 0x04fdcf5f9c000000 0x67fc7cfe60000000 0xacff8f9fcc000000

def z529 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xc980603f81f383e7 0x99300c07f03e707c

def z530 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xe7f003fe01e00382 0xfcfe007fc03c0070

def z531 : W := mkw 0x0540008a04a04a02 0x00a8001140940940 0x4180000e00e00000 0x08300001c01c0000

def z532 : W := mkw 0x07ce7016a066c2a8 0x40f9ce02d40cd855 0xfffffc3fe1ffc3ff 0xffffff87fc3ff87f

def z533 : W := mkw 0x15d4540015c70000 0x02ba8a8002b8e000 0xd1fc7c0001ff8005 0xba3f8f80003ff000

def z534 : W := mkw 0x05e462bca0000000 0x00bc8c5794000000 0xe7fc63ffe0000003 0xfcff8c7ffc000000

def z535 : W := mkw 0x020a004042080410 0x8041400808410082 0xbe0c00c1e61c4c7f 0x37c180183cc3898f

def z536 : W := mkw 0x057082aa1fb87f57 0x80ae105543f70fea 0xfff003fe1ffc7ffe 0xfffe007fc3ff8fff

def z537 : W := mkw 0x17ded4021fff4200 0x02fbda8043ffe840 0xfffffc3e1fffc387 0xffffff87c3fff870

def z538 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xbe73fff19f13ffe7 0xf7ce7ffe33e27ffc

def z539 : W := mkw 0x0030022011002104 0x0006004402200420 0x0070003001000380 0x800e000600200070

def z540 : W := mkw 0x15c4500004c60000 0x02b88a000098c000 0x4180000000e00000 0x08300000001c0000

def z541 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x69f003fe01e07f82 0x8d3e007fc03c0ff0

def z542 : W := mkw 0x0d712bbb95a0fbe7 0x21ae257772b41f7c 0xfff003ff9fe07fe6 0xfffe007ff3fc0ffc

def z543 : W := mkw 0x020a80000a180000 0x0041500001430000 0x060380001e000000 0x40c0700003c00000

def z544 : W := mkw 0x05f462beb5a06b06 0x00be8c57d6b40d60 0xfffc63ffffe07f87 0xffff8c7ffffc0ff0

def z545 : W := mkw 0x0540008a04a04a02 0x00a8001140940940 0xff8003ce1ee07c06 0x7ff00079c3dc0f80

def z546 : W := mkw 0x277b1be955802906 0x04ef637d2ab00520 0x06739fc01e003c00 0x40ce73f803c00780

def z547 : W := mkw 0x020b81414a181451 0x804170282943028a 0x060f83c1fe1c3c79 0x40c1f0783fc3878f

def z548 : W := mkw 0x001080021fb87f57 0x8002100043f70fea 0x180000001ffc7ffc 0x0300000003ff8fff

def z549 : W := mkw 0x028f6157e066c2a8 0x4051ec2afc0cd855 0xff8fe3ffe1ffc3ff 0xfff1fc7ffc3ff87f

def z550 : W := mkw 0x27ce50cc60000000 0x04f9ca198c000000 0xe7fffcce60000001 0xfcffff99cc000000

def z551 : W := mkw 0x08018d0108111041 0x210031a021022208 0x00039c0000000000 0x0000738000000000

def z552 : W := mkw 0x00002014a00080a8 0x4000040294001015 0x00000001e0000078 0x000000003c00000f

def z553 : W := mkw 0x128ed4000a5f0000 0x0251da80014be000 0x960ffc001e1f8005 0x72c1ff8003c3f000

def z554 : W := mkw 0x020a000002080000 0x0041400000410000 0x160c0000060c0000 0x22c1800000c18000

def z555 : W := mkw 0x0000000200206b06 0x0000000040040d60 0x0800000000007f80 0x0100000000000ff0

def z556 : W := mkw 0x27ff7bfdf5802906 0x04ffef7fbeb00520 0xe7fffffffe003c03 0xfcffffffffc00780

def z557 : W := mkw 0x0030022011002104 0x0006004402200420 0xbe7003f01f007f86 0xf7ce007e03e00ff0

def z558 : W := mkw 0x0000840008110000 0x0000108001022000 0x0003fc0000138001 0x00007f8000027000

def z559 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xc9f0033e19e03386 0xd93e0067c33c0670

def z560 : W := mkw 0x0821af31881190e1 0x210435e63102321c 0x8073ff3180138063 0xd00e7fe63002700c

def z561 : W := mkw 0x0001810108101041 0x0000302021020208 0x0003800180100061 0x000070003002000c

def z562 : W := mkw 0x020b81414a181451 0x804170282943028a 0x880f8301f81c307f 0x5101f0603f03860f

def z563 : W := mkw 0x0010000011002104 0x0002000002200420 0x0800000019003384 0x0100000003200670

def z564 : W := mkw 0x020a80404a180410 0x8041500809430082 0xb60f80c07e1c4c1d 0x76c1f0180fc38983

def z565 : W := mkw 0x17ded4021fff6b06 0x02fbda8043ffed60 0xdffffc001fffff85 0xfbffff8003fffff0

def z566 : W := mkw 0x0550000015800000 0x00aa000002b00000 0x41f0000001e00000 0x883e0000003c0000

def z567 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x6980603fe1e3c3fa 0x8d300c07fc3c787f

def z568 : W := mkw 0x020a000000000000 0x0041400000000000 0x860f800000000001 0x70c1f00000000000

def z569 : W := mkw 0x17fe52aa17ee6b06 0x02ffca5542fdcd60 0xfffc03fe1fec7f86 0xffff807fc3fd8ff0

def z570 : W := mkw 0x17dfd5415fdf1451 0x82fbfaa82bfbe28a 0xd7ffffc01fffbc05 0xfafffff803fff780

def z571 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xe18c603fe1e38383 0xbc318c07fc3c7070

def z572 : W := mkw 0x0001810108101041 0x0000302021020208 0xbe0383c19e107c67 0x77c0707833c20f8c

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000001e007c04 0x0300000003c00f80

def z574 : W := mkw 0x00846016a020c2a8 0x40108c02d4041855 0xe98c603fe00043fb 0xbd318c07fc00087f

def z575 : W := mkw 0x121b85415fdf1451 0x824370a82bfbe28a 0xbe0f83c1fffffc7f 0x77c1f0783fffff8f

def z576 : W := mkw 0x020b81414a181451 0x804170282943028a 0x1e0383c01e1c7c7c 0x43c0707803c38f8f

def z577 : W := mkw 0x057002aa15e6ebae 0x40ae005542bcdd75 0xfff003fe1ffffffe 0xfffe007fc3ffffff

def z578 : W := mkw 0x020b014142080410 0x8041602828410082 0xb60f83c1e60c4c1b 0x76c1f0783cc18983

def z579 : W := mkw 0x0801ad11881190e1 0x210035a23102321c 0x8803ff019813b067 0x51007fe03302760c

def z580 : W := mkw 0x37ff7ffdf5c70000 0x06ffefffbeb8e000 0xe7ffffffe1e38003 0xfcfffffffc3c7000

def z581 : W := mkw 0x00a56b37a066c2a8 0x4014ad66f40cd855 0xf9ffff3fe1ffc3ff 0xff3fffe7fc3ff87f

def z582 : W := mkw 0x08318f2119113145 0x210631e423222628 0x88739f0198103067 0x510e73e03302060c

def z583 : W := mkw 0x1831af319fdfb1e5 0x230635e633fbf63c 0x9873ff319fffb3e7 0xd30e7fe633fff67c

def z584 : W := mkw 0x0810840019113145 0x2102108003222628 0x0000000018003000 0x0000000003000600

def z585 : W := mkw 0x0abfef77fb7ff7fd 0xe157fdeeff6ffeff 0xffffffffffffffff 0xffffffffffffffff

def z586 : W := mkw 0x2a8ffd55e81190e1 0x2551ffaabd02321c 0x000ffc01e0138061 0x0001ff803c02700c

def z587 : W := mkw 0x00002010800080a0 0x0000040210001014 0x0000603001038380 0x80000c0600207070

def z588 : W := mkw 0x228f7955e0000000 0x0451ef2abc000000 0xa60fffc1e0000003 0x74c1fff83c000000

def z589 : W := mkw 0x0a3b8f615b193555 0xa14771ec2b6326aa 0x06739fc01e003c00 0x40ce73f803c00780

def z590 : W := mkw 0x000000020066c2a8 0x40000000400cd855 0xb80c0001e1ffc3ff 0x370180003c3ff87f

def z591 : W := mkw 0x0010000011000000 0x0002000002200000 0x8070000019000004 0xd00e000003200000

def z592 : W := mkw 0x07de500015800000 0x00fbca0002b00000 0xd7fffc001fe00005 0xfaffff8003fc0000

def z593 : W := mkw 0x08b46e36b167e3ac 0x61168dc6d62cfc75 0x41f07c3e01e38380 0x883e0f87c03c7070

def z594 : W := mkw 0x25c4508c20000000 0x04b88a1184000000 0x4180000e00000000 0x08300001c0000000

def z595 : W := mkw 0x08b5ef37b977f3ed 0x6116bde6f72efe7d 0xc9f3ff3f99f3b3e7 0xd93e7fe7f33e767c

def z596 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0073ff019813b061 0x400e7fe03302760c

def z597 : W := mkw 0x37fffffdff990000 0x06ffffffbff32000 0xe7fffffffe000003 0xfcffffffffc00000

def z598 : W := mkw 0x000080000a181451 0x800010000143028a 0x00000000001c0078 0x000000000003800f

def z599 : W := mkw 0x002002aa00206b06 0x0004005540040d60 0x0000003e00000380 0x00000007c0000070

def z600 : W := mkw 0x27cf79dde0000000 0x04f9ef3bbc000000 0x678ffccfe0000001 0x2cf1ff99fc000000

def z601 : W := mkw 0x0084400000460000 0x001088000008c000 0x4180600001e38000 0x88300c00003c7000

def z602 : W := mkw 0x021a84001b190000 0x0043508003632000 0x967ffc001f1f8005 0xf2cfff8003e3f000

def z603 : W := mkw 0x0000004040000410 0x8000000808000082 0x200000c060004c18 0x040000180c000983

def z604 : W := mkw 0x15f456aa15e76b06 0x02be8ad542bced60 0x41f07c3e01e38380 0x883e0f87c03c7070

def z605 : W := mkw 0x00002016a066c2a8 0x40000402d40cd855 0x3800003fe1ffc3fe 0x07000007fc3ff87f

def z606 : W := mkw 0x028fc1476a7e5659 0xc051f828ed4fcacb 0xff8f83cffefc7c7f 0x7ff1f079ffdf8f8f

def z607 : W := mkw 0x37ffdfe95fdf0000 0x06fffbfd2bfbe000 0xd7ffffc01fff8005 0xfafffff803fff000

def z608 : W := mkw 0x00002016a020c2a8 0x40000402d4041855 0xb80c003fe01c43ff 0x37018007fc03887f

def z609 : W := mkw 0x37ce50cc66ce0000 0x06f9ca198cd9c000 0x778c00ce66ec0000 0x2ef18019ccdd8000

def z610 : W := mkw 0x05f462beb5e6ebae 0x40be8c57d6bcdd75 0xfff063fe1fe3ff86 0xfffe0c7fc3fc7ff0

def z611 : W := mkw 0x17ded4405fdf0410 0x82fbda880bfbe082 0xf7fffcc07fffcc1d 0xfeffff980ffff983

def z612 : W := mkw 0x002002aa00206b06 0x0004005540040d60 0xbe0003fe1e007f86 0x77c0007fc3c00ff0

def z613 : W := mkw 0x000080000a181451 0x800010000143028a 0xbe0003c01e1c7c7e 0x77c0007803c38f8f

def z614 : W := mkw 0x17def414bfdf0000 0x02fbde8297fbe000 0xf7fffc3fffff8007 0xfeffff87fffff000

def z615 : W := mkw 0x080000000000b1e5 0x210000000000163c 0x08000000000033e0 0x010000000000067c

def z616 : W := mkw 0x05c4609ea4e6caaa 0x40b88c13d49cd955 0xff8c60ffe7ffcfff 0xbff18c1ffcfff9ff

def z617 : W := mkw 0x0030022215a06b06 0x0006004442b40d60 0x987003301fe07f86 0xd30e006603fc0ff0

def z618 : W := mkw 0x0084400620664208 0x40108800c40cc841 0xf98c000fe0fc407f 0x3f318001fc1f880f

def z619 : W := mkw 0x37effffdea5f0000 0x06fdffffbd4be000 0xe7ffffffe01f8003 0xfcfffffffc03f000

def z620 : W := mkw 0x0831af339931f3e5 0x210635e673263e7c 0xf9f3ff3f99f3f3e7 0xff3e7fe7f33e7e7c

def z621 : W := mkw 0x0084400000460000 0x001088000008c000 0x000c6000001f8001 0x00018c000003f000

def z622 : W := mkw 0x1fffff71dfdfb5f5 0xa3ffffee3bfbf6be 0xfffffff1ffffffff 0xfffffffe3fffffff

def z623 : W := mkw 0x0010840019110000 0x0002108003222000 0x00739c0018000000 0x400e738003000000

def z624 : W := mkw 0x08b5ef319957b1e5 0x2116bde6332af63c 0xd9ffff3199ffb3e7 0xfb3fffe6333ff67c

def z625 : W := mkw 0x0001014140001451 0x800020282800028a 0x000003c000003c00 0x0000007800000780

def z626 : W := mkw 0x0085e117a876d2e9 0x4010bc22f50eda5d 0xf98fe33ff9fff3ff 0xff31fc67ff3ffe7f

def z627 : W := mkw 0x0000000000460000 0x000000000008c000 0x1000000001ff8004 0x02000000003ff000

def z628 : W := mkw 0x0000000002080410 0x8000000000410082 0x10000000060c4c18 0x0200000000c18983

def z629 : W := mkw 0x17ce508a06ee4a02 0x02f9ca1140ddc940 0x778c00ce06ec4c00 0x2ef18019c0dd8980

def z630 : W := mkw 0x200000cc60000000 0x040000198c000000 0x200000ce60000000 0x04000019cc000000

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c0000001c0005 0x3201800000038000

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0xb800000000004006 0x3700000000000800

def z633 : W := mkw 0x08312b319100b1e5 0x210625663220163c 0x88700331990033e6 0xd10e00663320067c

def z634 : W := mkw 0x05f442aa15e66b06 0x00be885542bccd60 0xfffc63fe1fffff87 0xffff8c7fc3fffff0

def z635 : W := mkw 0x020ba157ea38d6f9 0xc041742afd471adf 0xbe0f83fffe1c7fff 0x77c1f07fffc38fff

def z636 : W := mkw 0x0831afbb9931fbe7 0x210635f773263f7c 0xa873ffff9913ffe7 0xd50e7ffff3227ffc

def z637 : W := mkw 0x17dfd5415fdf0000 0x02fbfaa82bfbe000 0xf7ffffc1ffff8007 0xfefffff83ffff000

def z638 : W := mkw 0x17ce7016a6eec2a8 0x42f9ce02d4ddd855 0xff8c603fe7ffc3ff 0xbff18c07fcfff87f

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z640 : W := mkw 0x174a100006880000 0x02e9420000d10000 0x0600000006000000 0x00c0000000c00000

def z641 : W := mkw 0x08002c10800180a0 0x2100058210003014 0x00007c0000038000 0x00000f8000007000

def z642 : W := mkw 0x0084400200664200 0x00108800400cc840 0xf98c603e01ffc387 0xbf318c07c03ff870

def z643 : W := mkw 0x08300e2011012104 0x210601c402202420 0x00701c0000000000 0x000e038000000000

def z644 : W := mkw 0x000181414a181451 0x800030282943028a 0x380003c1fe1c7c7e 0x070000783fc38f8f

def z645 : W := mkw 0x15f456aa15e76b06 0x02be8ad542bced60 0xfff07ffe1fe3ff86 0xfffe0fffc3fc7ff0

def z646 : W := mkw 0x157086aa1fff6b06 0x02ae10d543ffed60 0xfff003fe1fffff86 0xfffe007fc3fffff0

def z647 : W := mkw 0x175a94001f990000 0x02eb528003f32000 0x8673fc001f138005 0xd0ce7f8003e27000

def z648 : W := mkw 0x028fc1414a5e1451 0x8051f828294bc28a 0xff8fe3c1fffffc7f 0xfff1fc783fffff8f

def z649 : W := mkw 0x020a80000a180000 0x0041500001430000 0xbe0f8001fe1c407f 0x77c1f0003fc3880f

def z650 : W := mkw 0x0020022000000000 0x0004004400000000 0x8070033000000002 0xd00e006600000000

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x300c0000600c4018 0x260180000c018803

def z652 : W := mkw 0x128fd5414a5f1451 0x8251faa8294be28a 0x000ffc01e01f8079 0x0001ff803c03f00f

def z653 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0xe18c603fe01f807b 0xbc318c07fc03f00f

def z654 : W := mkw 0x021b81435fb87f57 0x804370286bf70fea 0xbe0f83c1fffc7fff 0x77c1f0783fff8fff

def z655 : W := mkw 0x0000000200204200 0x0000000040040840 0x7180000e00e04000 0x2e300001c01c0800

def z656 : W := mkw 0x08212b318000b1e5 0x210425663000163c 0x880063318113b3e7 0x91000c663022767c

def z657 : W := mkw 0x08b5ef35b911b1e5 0x2116bde6b722363c 0xe9ffff3ff913b3e7 0xfd3fffe7ff22767c

def z658 : W := mkw 0x0000000000001451 0x800000000000028a 0x0800000000007c78 0x0100000000000f8f

def z659 : W := mkw 0x0831af339977f3ed 0x610635e6732efe7d 0x9873ff3199fff3ff 0xd30e7fe6333ffe7f

def z660 : W := mkw 0x2ffffffffdb1fbe7 0x25ffffffffb63f7c 0xfffffffffff3ffe7 0xfffffffffffe7ffc

def z661 : W := mkw 0x17ce504046ce0410 0x82f9ca0808d9c082 0x778c00c066ec4c18 0x2ef180180cdd8983

def z662 : W := mkw 0x0000000200204200 0x0000000040040840 0x1800000001e04384 0x03000000003c0870

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800030018003006 0x5100006003000600

def z664 : W := mkw 0x20847814a0000000 0x04108f0294000000 0x00007c0000000000 0x00000f8000000000

def z665 : W := mkw 0x27cf7955e0000000 0x04f9ef2abc000000 0xc7fffc01e0000001 0xf8ffff803c000000

def z666 : W := mkw 0x17cfd1414ede1451 0x82f9fa2829dbc28a 0xff8f83c1fefc7c7f 0x7ff1f0783fdf8f8f

def z667 : W := mkw 0x07ced0000a180000 0x00f9da0001430000 0xd7fffc001e1c0005 0xfaffff8003c38000

def z668 : W := mkw 0x0894e416b977f3ed 0x61129c82d72efe7d 0xf98c603ff9fff3ff 0xbf318c07ff3ffe7f

def z669 : W := mkw 0x1abfff319b5fb1e5 0x2357ffe6336bf63c 0x887fff31991fb3e7 0xd10fffe63323f67c

def z670 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x798c003fe0ec43fa 0x2f318007fc1d887f

def z671 : W := mkw 0x0550000215a06b06 0x00aa000042b40d60 0xdff000001fe07f84 0xfbfe000003fc0ff0

def z672 : W := mkw 0x0831af3199113145 0x210635e633222628 0x8073ff3198003003 0xd00e7fe633000600

def z673 : W := mkw 0x000080020a7ed6f9 0xc0001000414fdadf 0x180000001ffffffc 0x0300000003ffffff

def z674 : W := mkw 0x0d71afb99d91b9e7 0x21ae35f733b2373c 0x8e73fff19f13bfe7 0xd1ce7ffe33e277fc

def z675 : W := mkw 0x057022ba95a0eba6 0x00ae045752b41d74 0xfff063ff9ff3ffe7 0xfffe0c7ff3fe7ffc

def z676 : W := mkw 0x077b83e95f983d57 0x80ef707d2bf307aa 0x067383c01e003c00 0x40ce707803c00780

def z677 : W := mkw 0x2ffffffdfb19b5f5 0xa5ffffffbf6336be 0xffffffffff1fffff 0xffffffffffe3ffff

def z678 : W := mkw 0x0550000215a04200 0x00aa000042b40840 0xfff0003e1fe04386 0xfffe0007c3fc0870

def z679 : W := mkw 0x0001810108101041 0x0000302021020208 0x0003830018003000 0x4000706003000600

def z680 : W := mkw 0x000080000a181451 0x800010000143028a 0xb80c0001fe1c7c7f 0x370180003fc38f8f

def z681 : W := mkw 0x37fefebcbfdf0000 0x06ffdfd797fbe000 0xd7fffc3e1fff8005 0xfaffff87c3fff000

def z682 : W := mkw 0x27fe52ee75a06b06 0x04ffca5dceb40d60 0xfffc03fe7fe07f86 0xffff807fcffc0ff0

def z683 : W := mkw 0x0001010100000000 0x0000202020000000 0x8003830180000003 0x5000706030000000

def z684 : W := mkw 0x0011850119111041 0x000230a023222208 0x8873ff019913b067 0xd10e7fe03322760c

def z685 : W := mkw 0x003002aa11206b06 0x0006005542240d60 0xa87003fe19007f86 0xd50e007fc3200ff0

def z686 : W := mkw 0x056002aa04a04a02 0x00ac005540940940 0xf7f003fe06e04c02 0xfefe007fc0dc0980

def z687 : W := mkw 0x020ba151ca1894f1 0x8041742a3943129e 0xbe0fe3f1ff1fffff 0xf7c1fc7e3fe3ffff

def z688 : W := mkw 0x020b81414a181451 0x804170282943028a 0x280f83c1e01c7c7b 0x0501f0783c038f8f

def z689 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x067fffc1e0000001 0x40cffff83c000000

def z690 : W := mkw 0x056002a800000000 0x00ac005500000000 0x41f0003e00000000 0x883e0007c0000000

def z691 : W := mkw 0x1a8ffd118a5f90e1 0x2351ffa2314bf21c 0x000ffc01801f8061 0x0001ff803003f00c

def z692 : W := mkw 0x05c4500000000000 0x00b88a0000000000 0x41f07c0000000000 0x883e0f8000000000

def z693 : W := mkw 0x08212b318000b1e5 0x210425663000163c 0x8873ff31800033e3 0xd10e7fe63000067c

def z694 : W := mkw 0x0801ad11881190e1 0x210035a23102321c 0x8803fc31811383e7 0x91007f863022707c

def z695 : W := mkw 0x0831af37b931f3ed 0x610635e6f7263e7d 0xa873ff3ff913f3ff 0xd50e7fe7ff227e7f

def z696 : W := mkw 0x175b95415f991451 0x82eb72a82bf3228a 0x06739fc01e003c00 0x40ce73f803c00780

def z697 : W := mkw 0x0550000015800000 0x00aa000002b00000 0xfff003c01fe07c06 0xfffe007803fc0f80

def z698 : W := mkw 0x177a96a81f992906 0x02ef52d503f32520 0x06739fc01e003c00 0x40ce73f803c00780

def z699 : W := mkw 0x17fed6a81fdf2906 0x02ffdad503fbe520 0xd7ffffc01fffbc05 0xfafffff803fff780

def z700 : W := mkw 0x056002a800000000 0x00ac005500000000 0x067003c000000000 0x40ce007800000000

def z701 : W := mkw 0x0010000015802906 0x0002000002b00520 0x000000001e003c00 0x0000000003c00780

def z702 : W := mkw 0x101084001f990000 0x0202108003f32000 0x000000001e000000 0x0000000003c00000

def z703 : W := mkw 0x028ee016aa7ec2a8 0x4051dc02d54fd855 0xff8fe03fffffc3ff 0xfff1fc07fffff87f

def z704 : W := mkw 0x0000000200204200 0x0000000040040840 0x2800003e00004382 0x05000007c0000870

def z705 : W := mkw 0x15d47416b5e7c2a8 0x42ba8e82d6bcf855 0x41f07c3e01e38380 0x883e0f87c03c7070

def z706 : W := mkw 0x020b81414a181451 0x804170282943028a 0x180f8001fe1c7c7d 0x0301f0003fc38f8f

def z707 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfff003ff9ff07fe7 0xfffe007ff3fe0ffc

def z708 : W := mkw 0x00212b31800080a0 0x0004256630001014 0x8073ff3181038383 0xd00e7fe630207070

def z709 : W := mkw 0x077b83eb5fb87f57 0x80ef707d6bf70fea 0x41ff803fe1fc03f9 0x883ff007fc3f807f

def z710 : W := mkw 0x0830ae309911b1e5 0x210615c61322363c 0x8873fc301913b3e5 0xd10e7f860322767c

def z711 : W := mkw 0x155084001fdf0000 0x02aa108003fbe000 0xd7f3fc001fff8005 0xfafe7f8003fff000

def z712 : W := mkw 0x17ded4043fdf0008 0x42fbda8087fbe001 0xd7fffc007fff801d 0xfaffff800ffff003

def z713 : W := mkw 0x101084021fff4a02 0x0202108043ffe940 0x100000001fffcc04 0x0200000003fff980

def z714 : W := mkw 0x08318f2119113145 0x210631e423222628 0x8873ff301913b387 0xd10e7fe603227670

def z715 : W := mkw 0x081084021db1fbe7 0x2102108043b63f7c 0x0800000019f3b3e4 0x01000000033e767c

def z716 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0073ff319913b3e1 0xc00e7fe63322767c

def z717 : W := mkw 0x028fe157ea7ed6f9 0xc051fc2afd4fdadf 0x4783e3fe1fe3bf80 0xc8f07c7fc3fc77f0

def z718 : W := mkw 0x0831af319d91b9e7 0x210635e633b2373c 0x8873ff319f13bfe7 0xd10e7fe633e277fc

def z719 : W := mkw 0x101084021fb96b06 0x0202108043f72d60 0x180000001fe07f84 0x0300000003fc0ff0

def z720 : W := mkw 0x05610ba900000000 0x00ac217520000000 0xe7f39ffe00000002 0xfcfe73ffc0000000

def z721 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xc7fffffe00000001 0xf8ffffffc0000000

def z722 : W := mkw 0x2831afbdb911b1e5 0x250635f7b722363c 0x8873ff3f9913b3e7 0xd10e7fe7f322767c

def z723 : W := mkw 0x2fded4cc7911b1e5 0x25fbda998f22363c 0x6f8c00ce7913b3e4 0x2df18019cf22767c

def z724 : W := mkw 0x020b81414a181451 0x804170282943028a 0xbe0fe3c1ff1ffc7f 0xf7c1fc783fe3ff8f

def z725 : W := mkw 0x17ded4881fdf0802 0x02fbda9103fbe100 0xd7fffcc01fff8c05 0xfaffff9803fff180

def z726 : W := mkw 0x001084021db16b06 0x0002108043b62d60 0x180000001ff3ff84 0x0300000003fe7ff0

def z727 : W := mkw 0x00846014a04680a8 0x40108c029408d015 0xbe0c63c1fe1ffc7f 0x77c18c783fc3ff8f

def z728 : W := mkw 0x0a8fed55ea5f94f9 0xe151fdaabd4bf29f 0x000ffc01e01f8079 0x0001ff803c03f00f

def z729 : W := mkw 0x020a004042080410 0x8041400808410082 0xbe0c03c1fe1c7c7f 0x77c180783fc38f8f

def z730 : W := mkw 0x22af7b75e0000000 0x0455ef6ebc000000 0xe1ffff3fe0000003 0xfc3fffe7fc000000

def z731 : W := mkw 0x27ce70dce0000000 0x04f9ce1b9c000000 0xe7fffcffe0000003 0xfcffff9ffc000000

def z732 : W := mkw 0x08312f319101a1a4 0x210625e632203434 0x0073ff3001038380 0xc00e7fe600207070

def z733 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x9873ff319f13ffe7 0xd30e7fe633e27ffc

def z734 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xc7fffc0001ff8001 0xf8ffff80003ff000

def z735 : W := mkw 0x37ded4cc7fdf0410 0x86fbda998ffbe082 0xf7fffcce7fffcc1d 0xfeffff99cffff983

def z736 : W := mkw 0x25e4fabcaa181451 0x84bc9f579543028a 0x59f07c3e1e1c7c7c 0x8b3e0f87c3c38f8f

def z737 : W := mkw 0x056002aa04a06b06 0x00ac005540940d60 0xff8003fe1ee07f86 0x7ff0007fc3dc0ff0

def z738 : W := mkw 0x37ef7bfde6ce0000 0x06fdef7fbcd9c000 0xf7ffffffe7ff8007 0xfefffffffcfff000

def z739 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xff8c60ffe7ffcfff 0xbff18c1ffcfff9ff

def z740 : W := mkw 0x37ef7bfde24e0000 0x06fdef7fbc49c000 0xe7ffffffe00c0003 0xfcfffffffc018000

def z741 : W := mkw 0x00212bb980000000 0x0004257730000000 0xa073ffff80000003 0xd40e7ffff0000000

def z742 : W := mkw 0x0831af71db19b5f5 0xa10635ee3b6336be 0xb873fff1ff1fffff 0xd70e7ffe3fe3ffff

def z743 : W := mkw 0x05f462bcb5c6a9ae 0x40be8c5796b8d535 0x067c63c1fe1fbc79 0x40cf8c783fc3f78f

def z744 : W := mkw 0x1fded4001fdf3145 0x23fbda8003fbe628 0xd7fffc001fffb005 0xfaffff8003fff600

def z745 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xdffffc001ffffc05 0xfbffff8003ffff80

def z746 : W := mkw 0x0d41ad9b8cb1dae3 0x21a835b371963b5c 0x7783fccf86f3cc61 0x2ef07f99f0de798c

def z747 : W := mkw 0x175ab416bfb9c2a8 0x42eb5682d7f73855 0x2e739c3ffe0043fa 0x45ce7387ffc0087f

def z748 : W := mkw 0x0a3a2e70d309a5b4 0xa14745ce1a6134b6 0x367c7cf0670fcf98 0xa6cf8f9e0ce1f9f3

def z749 : W := mkw 0x27ee52ec60000000 0x04fdca5d8c000000 0xe7fffffe60000003 0xfcffffffcc000000

def z750 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x887fff31f91fb3ff 0xd10fffe63f23f67f

def z751 : W := mkw 0x0010a410991180a0 0x0002148213223014 0x8073fc3019138385 0xd00e7f8603227070

def z752 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0873ff019913b3e5 0x410e7fe03322767c

def z753 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xf7ffffffe1e00007 0xfefffffffc3c0000

def z754 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0073fc3001038380 0x800e7f8600207070

def z755 : W := mkw 0x27ef7bfde04680a8 0x44fdef7fbc08d015 0xefffffffe11f83ff 0xfdfffffffc23f07f

def z756 : W := mkw 0x0030022211206304 0x0006004442240c60 0xfff003fe1fe07f86 0xfffe007fc3fc0ff0

def z757 : W := mkw 0x0031af3199112104 0x000635e633222420 0x8873ff319913b387 0xd10e7fe633227670

def z758 : W := mkw 0x0831afb99911b9e7 0x210635f73322373c 0x8873fff19913bfe7 0xd10e7ffe332277fc

def z759 : W := mkw 0x17ce500206ee4208 0x42f9ca0040ddc841 0x578c000006ec4018 0x2af1800000dd8803

def z760 : W := mkw 0x20847816a066c2a8 0x44108f02d40cd855 0xf98c7c3fe1ffc3ff 0xbf318f87fc3ff87f

def z761 : W := mkw 0x081185011911b1e5 0x210230a02322363c 0x8873ff019913b3e7 0xd10e7fe03322767c

def z762 : W := mkw 0x17ded4043fdf0000 0x02fbda8087fbe000 0xf7fffc0e7fff8005 0xfeffff81cffff000

def z763 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8073ff319903b383 0xd00e7fe633207670

def z764 : W := mkw 0x020b81414a181451 0x804170282943028a 0xff8f83fffe1c7c7f 0xfff1f07fffc38f8f

def z765 : W := mkw 0x27ef7bfde2080410 0x84fdef7fbc410082 0xffffffffe61c4c7f 0xfffffffffcc3898f

def z766 : W := mkw 0x2fef7bfde0003145 0x25fdef7fbc000628 0xe7ffffffe0003003 0xfcfffffffc000600

def z767 : W := mkw 0x2fef7bfde000b5f5 0xa5fdef7fbc0016be 0xefffffffe0007ffb 0xfdfffffffc000fff

def z768 : W := mkw 0x17ded4405fdf0000 0x02fbda880bfbe000 0xf7fffcc07fff8005 0xfeffff980ffff000

def z769 : W := mkw 0x157016aa15a16b06 0x02ae02d542b42d60 0xfff01ffe1fe07f86 0xfffe03ffc3fc0ff0

def z770 : W := mkw 0x000000020066c2a8 0x40000000400cd855 0xf98c003fe1ffc3ff 0xbf318007fc3ff87f

def z771 : W := mkw 0x27ef7bfde0001451 0x84fdef7fbc00028a 0xe7ffffffe000007b 0xfcfffffffc00000f

def z772 : W := mkw 0x17ded4001fdf1451 0x82fbda8003fbe28a 0xd7fffc001fff807d 0xfaffff8003fff00f

def z773 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xe7fffffffe003c03 0xfcffffffffc00780

def z774 : W := mkw 0x07ef53e940000000 0x00fdea7d28000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z775 : W := mkw 0x276b3bfde0000000 0x04ed677fbc000000 0xa673ffffe0000003 0xd4ce7ffffc000000

def z776 : W := mkw 0x075a84001f990000 0x00eb508003f32000 0xd7fffc001fff8005 0xfaffff8003fff000

def z777 : W := mkw 0x0030862019112104 0x000610c403222420 0x8073fc3019138385 0xd00e7f8603227070

def z778 : W := mkw 0x08212b338020fbe7 0x2104256670041f7c 0x0800033180007fe2 0x0100006630000ffc

def z779 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x67ffffcfe0000001 0x6cfffff9fc000000

def z780 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xffffffc1fffffc7f 0xfffffff83fffff8f

def z781 : W := mkw 0x17ced4000a5f0000 0x02f9da80014be000 0xd7fffc0001ff8005 0xfaffff80003ff000

def z782 : W := mkw 0x08212b338020f3ed 0x6104256670041e7d 0x08000331800073fa 0x0100006630000e7f

def z783 : W := mkw 0x25e57bfde0000000 0x04bcaf7fbc000000 0xe1f3ffffe0000003 0xdc3e7ffffc000000

def z784 : W := mkw 0x229f7957f5a06b06 0x0453ef2afeb40d60 0x180ffc01ffe07f85 0x0301ff803ffc0ff0

def z785 : W := mkw 0x27ef7bfde00080a0 0x04fdef7fbc001014 0xe7ffffffe1038383 0xfcfffffffc207070

def z786 : W := mkw 0x07cf7155e0000000 0x00f9ee2abc000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z787 : W := mkw 0x12aed6aa0a7f6b06 0x0255dad5414fed60 0x280ffffe001fff83 0x0501ffffc003fff0

def z788 : W := mkw 0x17ded4405fdf0410 0x82fbda880bfbe082 0xffffffc07ffffc1f 0xfffffff80fffff83

def z789 : W := mkw 0x00002010800080a0 0x0000040210001014 0x8873fc31811383e7 0xd10e7f863022707c

def z790 : W := mkw 0x07ce500620664208 0x40f9ca00c40cc841 0x778c000e60ec4018 0x2ef18001cc1d8803

def z791 : W := mkw 0x3031affdffdf0000 0x060635ffbffbe000 0x300003ffffff8006 0x0600007ffffff000

def z792 : W := mkw 0x37ce50ce66ee4208 0x46f9ca19ccddc841 0x778c00ce66ec4018 0x2ef18019ccdd8803

def z793 : W := mkw 0x27ef7bfde0000410 0x84fdef7fbc000082 0xe7ffffffe0004c1b 0xfcfffffffc000983

def z794 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x167ffc001fff8005 0x42cfff8003fff000

def z795 : W := mkw 0x05d4c4001dd70000 0x00ba988003bae000 0xd7fffc001fff8005 0xfaffff8003fff000

def z796 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x67fffffe60000000 0xecffffffcc000000

def z797 : W := mkw 0x0030a6309911a1a4 0x000614c613223434 0x8873ff319913b3e7 0xd10e7fe63322767c

def z798 : W := mkw 0x20a56bfde0000000 0x0414ad7fbc000000 0xe1ffffffe0000003 0xfc3ffffffc000000

def z799 : W := mkw 0x08212bfbc020fff7 0xa104257f78041ffe 0x280003ffe0007ffa 0x0500007ffc000fff

def z800 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xd7f003fe1fe03f84 0xfafe007fc3fc07f0

def z801 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xd7ffffc01fffbc05 0xfafffff803fff780

def z802 : W := mkw 0x28212bffe020fbe7 0x2504257ffc041f7c 0x280003ffe0007fe2 0x0500007ffc000ffc

def z803 : W := mkw 0x0811ad119911b1e5 0x210235a23322363c 0x8873fc019913b3e5 0xd10e7f803322767c

def z804 : W := mkw 0x37ded4cc7fdf0000 0x06fbda998ffbe000 0x778c00ce7fff8004 0x2ef18019cffff000

def z805 : W := mkw 0x05e56bbda0000000 0x00bcad77b4000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z806 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xf7fffc007fffc01d 0xfeffff800ffff803

def z807 : W := mkw 0x37ef7bfde6880000 0x06fdef7fbcd10000 0xe7ffffffe6000003 0xfcfffffffcc00000

def z808 : W := mkw 0x00108400191180a0 0x0002108003223014 0x8873fc00191383e5 0xd10e7f800322707c

def z809 : W := mkw 0x128ff555ea5f94f9 0xc251feaabd4bf29f 0x000ffc01e01f8079 0x0001ff803c03f00f

def z810 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x267fffffe0000003 0x44cffffffc000000

def z811 : W := mkw 0x081084021b7ff7fd 0xe1021080436ffeff 0x180000001ffffffc 0x0300000003ffffff

def z812 : W := mkw 0x15d5554155c71451 0x82baaaa82ab8e28a 0x69f07fc1e1e3fc7a 0x8d3e0ff83c3c7f8f

def z813 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xefffffffe0100067 0xfdfffffffc02000c

def z814 : W := mkw 0x1831af319f99b1e5 0x230635e633f3363c 0x8873ff319f13b3e7 0xd10e7fe633e2767c

def z815 : W := mkw 0x25e57bbda0000000 0x04bcaf77b4000000 0x41f3fc3f80000001 0x883e7f87f0000000

def z816 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xb873ff319913f3e7 0xf70e7fe633227e7c

def z817 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xc7f3ffff80000003 0xd8fe7ffff0000000

def z818 : W := mkw 0x27ef7bfde0001451 0x84fdef7fbc00028a 0xffffffffe01c7c7f 0xfffffffffc038f8f

def z819 : W := mkw 0x0894e414b911b1e5 0x21129c829722363c 0xe98c603ff913b3e7 0xbd318c07ff22767c

def z820 : W := mkw 0x05612bb980000000 0x00ac257730000000 0xc1f3ff3f80000003 0xd83e7fe7f0000000

def z821 : W := mkw 0x020b81414a181451 0x804170282943028a 0xbe7fffc1fe1c7c7f 0xf7cffff83fc38f8f

def z822 : W := mkw 0x15d4540015c70000 0x02ba8a8002b8e000 0xc1f3fc0001e38001 0xd83e7f80003c7000

def z823 : W := mkw 0x0031872119113145 0x000630e423222628 0x8873ff319913b3e7 0xd10e7fe63322767c

def z824 : W := mkw 0x08212bbb8020fbe7 0x2104257770041f7c 0x0800033f800033e2 0x01000067f000067c

def z825 : W := mkw 0x0831af71d911b5f5 0xa10635ee3b2236be 0xbe73fff1ff13ffff 0xf7ce7ffe3fe27fff

def z826 : W := mkw 0x2fef7bfde000a1a4 0x25fdef7fbc001434 0xe7ffffffe0000383 0xfcfffffffc000070

def z827 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xe9f3ff3f9913b3e7 0xfd3e7fe7f322767c

def z828 : W := mkw 0x276b1beb4066c2a8 0x44ed637d680cd855 0x1e739fc001ffc3fc 0x43ce73f8003ff87f

def z829 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0873ff318113b3e3 0x810e7fe63022767c

def z830 : W := mkw 0x020b81414a181451 0x804170282943028a 0x2e0f83c1fe1c7c7b 0x45c1f0783fc38f8f

def z831 : W := mkw 0x07ef7bb980000000 0x00fdef7730000000 0xe7ffffff80000003 0xfcfffffff0000000

def z832 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x57f3fc001fff8004 0xcafe7f8003fff000

def z833 : W := mkw 0x27ef7bfde0002104 0x04fdef7fbc000420 0xefffffffe0003383 0xfdfffffffc000670

def z834 : W := mkw 0x02af6b75e0000000 0x0055ed6ebc000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z835 : W := mkw 0x081084021db17b47 0x2102108043b62f68 0x180000001fe07f84 0x0300000003fc0ff0

def z836 : W := mkw 0x101084021fff6b06 0x0202108043ffed60 0x100000001fff8384 0x0200000003fff070

def z837 : W := mkw 0x08b5cf273977734d 0x6116b9e4e72eee69 0x71ff9f0e78ec7018 0x6e3ff3e1cf1d8e03

def z838 : W := mkw 0x129ed4001b5f0000 0x0253da80036be000 0xd1fffc0019ff8005 0xfa3fff80033ff000

def z839 : W := mkw 0x0031af31991180a0 0x000635e633223014 0x8873ff31991383e7 0xd10e7fe63322707c

def z840 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xd18c603fe1ff83fd 0xba318c07fc3ff07f

def z841 : W := mkw 0x2831af75f911b1e5 0x250635eebf22363c 0x8873ff31f913b3e7 0xd10e7fe63f22767c

def z842 : W := mkw 0x0010840019570000 0x00021080032ae000 0x9073fc0019ff8005 0xd20e7f80033ff000

def z843 : W := mkw 0x101084021fffc2a8 0x4202108043fff855 0x100000001fff8384 0x0200000003fff070

def z844 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x9e73ff319f13b3e7 0xf3ce7fe633e2767c

def z845 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xe18c603fe1ff83fb 0xbc318c07fc3ff07f

def z846 : W := mkw 0x0831af71d911b5f5 0xa10635ee3b2236be 0x8873ff31f913b3ff 0xd10e7fe63f22767f

def z847 : W := mkw 0x276b3bfde0000000 0x04ed677fbc000000 0xa67f9fffe0000003 0x74cff3fffc000000

def z848 : W := mkw 0x27ef7bfde2080410 0x84fdef7fbc410082 0xe7ffffffe6000c03 0xfcfffffffcc00180

def z849 : W := mkw 0x0830ae309911a1a4 0x210615c613223434 0x8873ff301913b387 0xd10e7fe603227670

def z850 : W := mkw 0x0010840019112104 0x0002108003222420 0x8873fc001913b385 0xd10e7f8003227670

def z851 : W := mkw 0x25e57bbda0000000 0x04bcaf77b4000000 0xe1ffff3fe0000003 0xfc3fffe7fc000000

def z852 : W := mkw 0x17ded4001fdf1451 0x82fbda8003fbe28a 0xd7fffc001fffbc05 0xfaffff8003fff780

def z853 : W := mkw 0x27ee7abca0000000 0x04fdcf5794000000 0xe7fffc3fe0000003 0xfcffff87fc000000

def z854 : W := mkw 0x020b81414a181451 0x804170282943028a 0xbe0f83f1ff1c7fff 0xf7c1f07e3fe38fff

def z855 : W := mkw 0x17ded4405fdf0410 0x82fbda880bfbe082 0xd7fffc007fff801d 0xfaffff800ffff003

def z856 : W := mkw 0x27ef5bed60000000 0x04fdeb7dac000000 0xe7ff9fcfe0000003 0x7cfff3f9fc000000

def z857 : W := mkw 0x20212bffe020c2a8 0x4404257ffc041855 0x200003ffe0000382 0x0400007ffc000070

def z858 : W := mkw 0x0550000215a04200 0x00aa000042b40840 0xfff003fe1fe07f86 0xfffe007fc3fc0ff0

def z859 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xd9f3ff3199f3b3e7 0xfb3e7fe6333e767c

def z860 : W := mkw 0x0010840019110000 0x0002108003222000 0x8873fc3019138387 0xd10e7f8603227070

def z861 : W := mkw 0x27cf51cd60000000 0x04f9ea39ac000000 0xe7ffffcfe0000003 0xfcfffff9fc000000

def z862 : W := mkw 0x081084021931fbe7 0x2102108043263f7c 0x080000001913ffe4 0x0100000003227ffc

def z863 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x47fffc001fff8001 0xc8ffff8003fff000

def z864 : W := mkw 0x175a94001fdf0000 0x02eb528003fbe000 0x9673fc001fff8005 0xd2ce7f8003fff000

def z865 : W := mkw 0x081084021931f3ed 0x6102108043263e7d 0x080000001913f3fc 0x0100000003227e7f

def z866 : W := mkw 0x17ded4405fdf1451 0x82fbda880bfbe28a 0xfffffcc07ffffc7d 0xffffff980fffff8f

def z867 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfff003fe1ffc7ffe 0xfffe007fc3ff8fff

def z868 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0x67f39fce00000000 0x6cfe73f9c0000000

def z869 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfff003ffffe07ffe 0xfffe007ffffc0fff

def z870 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x57fffc001eff8001 0x6affff8003dff000

def z871 : W := mkw 0x27ef7bfde0460000 0x04fdef7fbc08c000 0xf7ffffffe0ec0003 0xfefffffffc1d8000

def z872 : W := mkw 0x27ef7bfde0460000 0x04fdef7fbc08c000 0xffffffffe1ffc07f 0xfffffffffc3ff80f

def z873 : W := mkw 0x17ded4001fdf2104 0x02fbda8003fbe420 0xdffffc001fffb385 0xfbffff8003fff670

def z874 : W := mkw 0x101084001dd70000 0x0202108003bae000 0x8073fc0019f38005 0xd00e7f80033e7000

def z875 : W := mkw 0x00846014a0000000 0x00108c0294000000 0xe1fffc3fe0000003 0xfc3fff87fc000000

def z876 : W := mkw 0x27ef5bed60000000 0x04fdeb7dac000000 0xe7ff9ffe60000002 0xfcfff3ffcc000000

def z877 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xdfffff001fffb007 0xfbffffe003fff600

def z878 : W := mkw 0x0831af319b19b5f5 0xa10635e6336336be 0xbe73fff19f1fffff 0xf7ce7ffe33e3ffff

def z879 : W := mkw 0x17ce508e26ee4a0a 0x42f9ca11c4ddc941 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z880 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x57fffc001fef8000 0xeaffff8003fdf000

def z881 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xf7ffffffe01c0007 0xfefffffffc038000

def z882 : W := mkw 0x07ce508800000000 0x00f9ca1100000000 0xe7fffcce00000001 0xfcffff99c0000000

def z883 : W := mkw 0x0831af71d911b1e5 0x210635ee3b22363c 0xa873fff1f913b3e7 0xd50e7ffe3f22767c

def z884 : W := mkw 0x17ce500206ee4a02 0x02f9ca0040ddc940 0x578c000006ec4c00 0x2af1800000dd8980

def z885 : W := mkw 0x08312f319101a1a4 0x210625e632203434 0x8873ff31811383e7 0xd10e7fe63022707c

def z886 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xbe7ffff1ff1fffff 0xf7cffffe3fe3ffff

def z887 : W := mkw 0x07ded4001d910000 0x00fbda8003b22000 0xd7fffc001ff38005 0xfaffff8003fe7000

def z888 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z889 : W := mkw 0x228ff955ea5e94f9 0xc451ff2abd4bd29f 0x000ffc01e01f8079 0x0001ff803c03f00f

def z890 : W := mkw 0x27cf7955e0000000 0x04f9ef2abc000000 0xe7fffc3fe0000003 0xfcffff87fc000000

def z891 : W := mkw 0x17ded4001fdf2906 0x02fbda8003fbe520 0xd7fffc001fffbc05 0xfaffff8003fff780

def z892 : W := mkw 0x08212bbfa020fbef 0x61042577f4041f7d 0x280003ffe0007ffa 0x0500007ffc000fff

def z893 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x7ff003fe1ee07f82 0x6ffe007fc3dc0ff0

def z894 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xf98c603fffffffff 0xbf318c07ffffffff

def z895 : W := mkw 0x00212b35a0000000 0x00042566b4000000 0xa073ff3fe0000003 0xd40e7fe7fc000000

def z896 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xf9fffc3fe1ffc3ff 0xff3fff87fc3ff87f

def z897 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xff8c63ffe1ffc3ff 0xfff18c7ffc3ff87f

def z898 : W := mkw 0x056002a800000000 0x00ac005500000000 0xe7f3fffe00000003 0xfcfe7fffc0000000

def z899 : W := mkw 0x0a0b8d414a191451 0xa14171a82943228a 0xbe0f9fc1fe1c7c7f 0x77c1f3f83fc38f8f

def z900 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0x26739ffe00000002 0x44ce73ffc0000000

def z901 : W := mkw 0x0831af71d911b5f5 0xa10635ee3b2236be 0x8873fff19913bfe7 0xd10e7ffe332277fc

def z902 : W := mkw 0x081084021df7fbef 0x6102108043beff7d 0x180000001ffffffc 0x0300000003ffffff

def z903 : W := mkw 0x002002aa00206b06 0x0004005540040d60 0xff8003fe1fe07f86 0xfff0007fc3fc0ff0

def z904 : W := mkw 0x27ef7bfde0001451 0x84fdef7fbc00028a 0xe7ffffffe0003c03 0xfcfffffffc000780

def z905 : W := mkw 0x17de540015c70000 0x02fbca8002b8e000 0xd7fffc001fe38005 0xfaffff8003fc7000

def z906 : W := mkw 0x17ce50ca46ee4e12 0x82f9ca1948ddc9c2 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z907 : W := mkw 0x1fef7b3186ceb1e5 0x23fdef6630d9d63c 0x5f8c033186ec33e2 0x2bf1806630dd867c

def z908 : W := mkw 0x1094c4001fdf0000 0x0212988003fbe000 0xd1fffc001fff8005 0xfa3fff8003fff000

def z909 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfffc03fe1ffc7f87 0xffff807fc3ff8ff0

def z910 : W := mkw 0x27ef7bfde4800802 0x04fdef7fbc900100 0xe7ffffffe6000c03 0xfcfffffffcc00180

def z911 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xc1fffc0019ff8005 0xd83fff80033ff000

def z912 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xeffffffff8003007 0xfdffffffff000600

def z913 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xd7fffc01ffff807d 0xfaffff803ffff00f

def z914 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfffc03ffffe07f87 0xffff807ffffc0ff0

def z915 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x67fffcffe0000001 0xacffff9ffc000000

def z916 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xff8c603fffffc3ff 0xfff18c07fffff87f

def z917 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x41f3fc0001e38000 0x883e7f80003c7000

def z918 : W := mkw 0x000080000a181451 0x800010000143028a 0xbe0c03c1fe1c7c7f 0x77c180783fc38f8f

def z919 : W := mkw 0x08318f211911b1e5 0x210631e42322363c 0x8873ff001913b3e5 0xd10e7fe00322767c

def z920 : W := mkw 0x222b2bfde0000000 0x0445657fbc000000 0xa67fffffe0000003 0xf4cffffffc000000

def z921 : W := mkw 0x2fef7bfde00090e1 0x25fdef7fbc00121c 0xe7ffffffe0000063 0xfcfffffffc00000c

def z922 : W := mkw 0x001084021977c2a8 0x40021080432ef855 0x1800000019ffc3fc 0x03000000033ff87f

def z923 : W := mkw 0x00312b319100a1a4 0x0006256632201434 0x8873ff319913b3e7 0xd10e7fe63322767c

def z924 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xa87fff31f913b3e7 0xf50fffe63f22767c

def z925 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xf7fffc01ffff8007 0xfeffff803ffff000

def z926 : W := mkw 0x07ced0000a5e0000 0x00f9da00014bc000 0xd7fffc001fff8005 0xfaffff8003fff000

def z927 : W := mkw 0x07ce500000460000 0x00f9ca000008c000 0xc7fffc0001e38001 0xf8ffff80003c7000

def z928 : W := mkw 0x27ef7bfde04680a8 0x44fdef7fbc08d015 0xf7ffffffe1ff807f 0xfefffffffc3ff00f

def z929 : W := mkw 0x27ef7bfde0001041 0x04fdef7fbc000208 0xefffffffe0003063 0xfdfffffffc00060c

def z930 : W := mkw 0x37ce50ce66ee4a02 0x06f9ca19ccddc940 0x778c00ce66ec4c00 0x2ef18019ccdd8980

def z931 : W := mkw 0x00212b3180000000 0x0004256630000000 0xe1f3ff3f80000003 0xfc3e7fe7f0000000

def z932 : W := mkw 0x081084021fb9fff7 0xa102108043f73ffe 0x180000001ffffffc 0x0300000003ffffff

def z933 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x5ff003fe1fe07f84 0xcbfe007fc3fc0ff0

def z934 : W := mkw 0x17de540015c70000 0x02fbca8002b8e000 0xd7fffc0001ff8005 0xfaffff80003ff000

def z935 : W := mkw 0x276b3bfde0000000 0x04ed677fbc000000 0xe7f39fffe0000002 0xfcfe73fffc000000

def z936 : W := mkw 0x1094e414bfdf0000 0x02129c8297fbe000 0xf18c603fffff8007 0xbe318c07fffff000

def z937 : W := mkw 0x101084021fff7f57 0x8202108043ffefea 0x180000001ffffffc 0x0300000003ffffff

def z938 : W := mkw 0x029ec4001b5f0000 0x0053d880036be000 0xd7fffc001fff8005 0xfaffff8003fff000

def z939 : W := mkw 0x17ce508a06ee4a02 0x02f9ca1140ddc940 0x578c000e06ec0000 0x2af18001c0dd8000

def z940 : W := mkw 0x25e47abca0000000 0x04bc8f5794000000 0xc1f3fc3e00000001 0xd83e7f87c0000000

def z941 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xefffffffe000407b 0xfdfffffffc00080f

def z942 : W := mkw 0x27ef7bfde4800000 0x04fdef7fbc900000 0xf7ffffffe6e00003 0xfefffffffcdc0000

def z943 : W := mkw 0x0010000215a06b06 0x0002000042b40d60 0xff8003fe1fe07f86 0xfff0007fc3fc0ff0

def z944 : W := mkw 0x25701aaa15a06b06 0x04ae035542b40d60 0xfff01ffe1fe07f86 0xfffe03ffc3fc0ff0

def z945 : W := mkw 0x15d4d4001dd70000 0x02ba9a8003bae000 0xd1fffc0019ff8005 0xfa3fff80033ff000

def z946 : W := mkw 0x0831af319d91b1e5 0x210635e633b2363c 0x9873ff319ff3b3e7 0xd30e7fe633fe767c

def z947 : W := mkw 0x101084021fffd6f9 0xc202108043fffadf 0x180000001ffffffc 0x0300000003ffffff

def z948 : W := mkw 0x2fef7bfde000b1e5 0x25fdef7fbc00163c 0xefffffffe113b3e7 0xfdfffffffc22767c

def z949 : W := mkw 0x08302e309101a1a4 0x210605c612203434 0x8073fc3001038381 0xd00e7f8600207070

def z950 : W := mkw 0x0831af35b911b1ed 0x610635e6b722363d 0x8873ff31f913b3ff 0xd10e7fe63f22767f

def z951 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xe7f3fffe00000002 0xfcfe7fffc0000000

def z952 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x57fffc0007ff8001 0xaaffff8000fff000

def z953 : W := mkw 0x00212b37a020c2a8 0x40042566f4041855 0x2800033fe00043fa 0x05000067fc00087f

def z954 : W := mkw 0x20212bffe020d6f9 0xc404257ffc041adf 0x280003ffe0007ffa 0x0500007ffc000fff

def z955 : W := mkw 0x081084021977f3ed 0x61021080432efe7d 0x0800000019f3b3e4 0x01000000033e767c

def z956 : W := mkw 0x27ef7bfde0460000 0x04fdef7fbc08c000 0xe7ffffffe1e38003 0xfcfffffffc3c7000

def z957 : W := mkw 0x0001810108101041 0x0000302021020208 0xbe0f83c1fe1c7c7f 0x77c1f0783fc38f8f

def z958 : W := mkw 0x17ded4001fdf1041 0x02fbda8003fbe208 0xdffffc001fffb065 0xfbffff8003fff60c

def z959 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xffffffffe0004007 0xfffffffffc000800

def z960 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x987fff31991fb3e7 0xf30fffe63323f67c

def z961 : W := mkw 0x055084001d910000 0x00aa108003b22000 0xc1f3fc0019f38005 0xd83e7f80033e7000

def z962 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0873ff319813b3e3 0x410e7fe63302767c

def z963 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xe7ffffffe1138007 0xfcfffffffc227000

def z964 : W := mkw 0x27ce50cc60000000 0x04f9ca198c000000 0x67ff9cce60000000 0x6cfff399cc000000

def z965 : W := mkw 0x020b81414a181451 0x804170282943028a 0x3e0c03c1fe1c7c7e 0x27c180783fc38f8f

def z966 : W := mkw 0x020b81414a181451 0x804170282943028a 0x1e0f83c1fe1c7c7d 0x43c1f0783fc38f8f

def z967 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x67ff9fffe0000002 0x6cfff3fffc000000

def z968 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xa873ff31f913f3ff 0xd50e7fe63f227e7f

def z969 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xfffffffffe1c7c7f 0xffffffffffc38f8f

def z970 : W := mkw 0x37ded48c3fdf0000 0x06fbda9187fbe000 0xd7fffc0e1fff8005 0xfaffff81c3fff000

def z971 : W := mkw 0x020a80000a180000 0x0041500001430000 0xbe0f83c1fe1c7c7f 0x77c1f0783fc38f8f

def z972 : W := mkw 0x020b014140000000 0x0041602828000000 0xbe0f83c1fe1c7c7f 0x77c1f0783fc38f8f

def z973 : W := mkw 0x27ce50ce64e64a0a 0x44f9ca19cc9cc941 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z974 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0873ff301913b3e4 0xc10e7fe60322767c

def z975 : W := mkw 0x120b95414a191451 0x824172a82943228a 0xbe0f9fc1fe1c7c7f 0x77c1f3f83fc38f8f

def z976 : W := mkw 0x27ef7bfde0002906 0x04fdef7fbc000520 0xe7ffffffe0003c03 0xfcfffffffc000780

def z977 : W := mkw 0x0f7b8fe95f993d57 0xa1ef71fd2bf327aa 0x06739fc01e003c00 0x40ce73f803c00780

def z978 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xe7ffffffe01c007b 0xfcfffffffc03800f

def z979 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xe1fffc3fe0000003 0xbc3fff87fc000000

def z980 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x41f3fc3e00000000 0x883e7f87c0000000

def z981 : W := mkw 0x276b3bf9c0000000 0x04ed677f38000000 0xe7f3ffff80000003 0xfcfe7ffff0000000

def z982 : W := mkw 0x27ef7bfde2080410 0x84fdef7fbc410082 0xfffffffffe0c7c1f 0xffffffffffc18f83

def z983 : W := mkw 0x2831aff9d911b1e5 0x250635ff3b22363c 0x8873fff19913b3e7 0xd10e7ffe3322767c

def z984 : W := mkw 0x17de540015c70000 0x02fbca8002b8e000 0x41fffc0001e38001 0x883fff80003c7000

def z985 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xe7f003fe1fe03f82 0xfcfe007fc3fc07f0

def z986 : W := mkw 0x27ef7bfde00080a8 0x44fdef7fbc001015 0xe7ffffffe000007b 0xfcfffffffc00000f

def z987 : W := mkw 0x0831af319911b5f5 0xa10635e6332236be 0x8873ff319913ffff 0xd10e7fe633227fff

def z988 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8073fc31991383e5 0xd00e7f863322707c

def z989 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xc7fffc3fe0000001 0xf8ffff87fc000000

def z990 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfff063fe1ff3ff87 0xfffe0c7fc3fe7ff0

def z991 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x698c603fe1ffc3fb 0x8d318c07fc3ff87f

def z992 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xf7ffffffe00c401b 0xfefffffffc018803

def z993 : W := mkw 0x020b81414a181451 0x804170282943028a 0xff8f83c1fffc7c7f 0xfff1f0783fff8f8f

def z994 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xf7fffc3e1fff8007 0xfeffff87c3fff000

def z995 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xf98c63ffe1ffffff 0xbf318c7ffc3fffff

def z996 : W := mkw 0x17ded4405fdf0410 0x82fbda880bfbe082 0xd7fffcc01fff8c05 0xfaffff9803fff180

def z997 : W := mkw 0x17ded4001dd70000 0x02fbda8003bae000 0xc7fffc0019f38005 0xf8ffff80033e7000

def z998 : W := mkw 0x27ef7bfde2081451 0x84fdef7fbc41028a 0xffffffffe60c7c7b 0xfffffffffcc18f8f

def z999 : W := mkw 0x276b1bed60000000 0x04ed637dac000000 0x26739fce60000000 0x44ce73f9cc000000

def z1000 : W := mkw 0x181084021ffff3ed 0x6302108043fffe7d 0x180000001ffff3fc 0x0300000003fffe7f

def z1001 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xcff003fe1fe03f86 0xd9fe007fc3fc07f0

def z1002 : W := mkw 0x27ef7bfde00080a0 0x04fdef7fbc001014 0xe7ffffffe0138063 0xfcfffffffc02700c

def z1003 : W := mkw 0x0831af319911a1a4 0x210635e633223434 0x8073ff3199138387 0xd00e7fe633227070

def z1004 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x61ffffffe0000003 0x8c3ffffffc000000

def z1005 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8073ff31811383e3 0xd00e7fe63022707c

def z1006 : W := mkw 0x020b81414a181451 0x804170282943028a 0x3e0f83c1fe0c7c7a 0x67c1f0783fc18f8f

def z1007 : W := mkw 0x07ef7b35a0000000 0x00fdef66b4000000 0xe7ffff3fe0000003 0xfcffffe7fc000000

def z1008 : W := mkw 0x28212bffe020f3ed 0x6504257ffc041e7d 0x280003ffe00073fa 0x0500007ffc000e7f

def z1009 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x798c003fe1ffc3fe 0x2f318007fc3ff87f

def z1010 : W := mkw 0x17ce504666ee4618 0xc2f9ca08ccddc8c3 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z1011 : W := mkw 0x17ded4001fdf1451 0x82fbda8003fbe28a 0xfffffc01fffffc7f 0xffffff803fffff8f

def z1012 : W := mkw 0x27ce508c20000000 0x04f9ca1184000000 0xc7fffc0e00000001 0xf8ffff81c0000000

def z1013 : W := mkw 0x22af7bfde0000000 0x0455ef7fbc000000 0xa07fffffe0000003 0xd40ffffffc000000

def z1014 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x7f8003fe1fe07f86 0x2ff0007fc3fc0ff0

def z1015 : W := mkw 0x0540008a04a04a02 0x00a8001140940940 0xff8003fe1fe07f86 0xfff0007fc3fc0ff0

def z1016 : W := mkw 0x0001014140001451 0x800020282800028a 0xbe0c03c1fe1c7c7f 0x77c180783fc38f8f

def z1017 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xa873fff19913ffe7 0xd50e7ffe33227ffc

def z1018 : W := mkw 0x27ef7bbda0000000 0x04fdef77b4000000 0xc7ffff3f80000003 0xf8ffffe7f0000000

def z1019 : W := mkw 0x17ded4881fdf0000 0x02fbda9103fbe000 0xf7fffcce1fff8005 0xfeffff99c3fff000

def z1020 : W := mkw 0x0810a4109911b1e5 0x210214821322363c 0x8873fc319913b3e7 0xd10e7f863322767c

def z1021 : W := mkw 0x0831af319b19b5f5 0xa10635e6336336be 0x8873ff31991fb3ff 0xd10e7fe63323f67f

def z1022 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8873ff301903b386 0xd10e7fe603207670

def z1023 : W := mkw 0x25612bfde0000000 0x04ac257fbc000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z1024 : W := mkw 0x00212b338066c2a8 0x40042566700cd855 0x9873ff3181ffc3ff 0xd30e7fe6303ff87f

def z1025 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xdffffc301fff8387 0xfbffff8603fff070

def z1026 : W := mkw 0x27ee7afce0000000 0x04fdcf5f9c000000 0xe7fffcfe60000001 0xfcffff9fcc000000

def z1027 : W := mkw 0x08212b77e020f7fd 0xe104256efc041eff 0x280003ffe0007ffa 0x0500007ffc000fff

def z1028 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x77f003fe1fe07f80 0xeefe007fc3fc0ff0

def z1029 : W := mkw 0x17ded4001fdf0410 0x82fbda8003fbe082 0xd7fffc001fffcc1d 0xfaffff8003fff983

def z1030 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0xe7ff9fffe0000003 0xfcfff3fffc000000

def z1031 : W := mkw 0x08312f319101a1a4 0x210625e632203434 0x0073fc3181038381 0x800e7f8630207070

def z1032 : W := mkw 0x17ce500626ee4208 0x42f9ca00c4ddc841 0x578c000e06ec0000 0x2af18001c0dd8000

def z1033 : W := mkw 0x101084021fff4200 0x0202108043ffe840 0x180000001fffc384 0x0300000003fff870

def z1034 : W := mkw 0x276b3bfde0000000 0x04ed677fbc000000 0x06739ffe00000000 0x40ce73ffc0000000

def z1035 : W := mkw 0x37ef7bfde6ce0410 0x86fdef7fbcd9c082 0xf7ffffffe6ec4c1b 0xfefffffffcdd8983

def z1036 : W := mkw 0x27ef7bfde04680a0 0x04fdef7fbc08d014 0xffffffffe1ff83e7 0xfffffffffc3ff07c

def z1037 : W := mkw 0x25e57bbda0000000 0x04bcaf77b4000000 0x41f3ff3e00000000 0xc83e7fe7c0000000

def z1038 : W := mkw 0x0df46ebeb5e7ebae 0x61be8dd7d6bcfd75 0x41f07c3e01e38380 0x883e0f87c03c7070

def z1039 : W := mkw 0x27ee7abca0000000 0x04fdcf5794000000 0x47f3fc3e00000000 0xc8fe7f87c0000000

def z1040 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8e73fff19f13bfe7 0xd1ce7ffe33e277fc

def z1041 : W := mkw 0x17de540015c70000 0x02fbca8002b8e000 0x47f3fc0001e38000 0xc8fe7f80003c7000

def z1042 : W := mkw 0x27ef5bed60000000 0x04fdeb7dac000000 0x47f39fce00000000 0x48fe73f9c0000000

def z1043 : W := mkw 0x0094c40019570000 0x00129880032ae000 0xc1f3fc0019f38005 0xd83e7f80033e7000

def z1044 : W := mkw 0x057006aa15a16b06 0x00ae00d542b42d60 0xfff07ffe1fe3ff86 0xfffe0fffc3fc7ff0

def z1045 : W := mkw 0x27ef5be940000000 0x04fdeb7d28000000 0xe7fffffe00000003 0xfcffffffc0000000

def z1046 : W := mkw 0x0831af71d911b5f5 0xa10635ee3b2236be 0xb87ffff1f91fffff 0xf70ffffe3f23ffff

def z1047 : W := mkw 0x27ef7bfde0460008 0x44fdef7fbc08c001 0xe7ffffffe00c001b 0xfcfffffffc018003

def z1048 : W := mkw 0x000020128020c2a0 0x0000040250041854 0xf98c603fe1ffc3ff 0xbf318c07fc3ff87f

def z1049 : W := mkw 0x177b97e95f993d57 0x82ef72fd2bf327aa 0x06739fc01e003c00 0x40ce73f803c00780

def z1050 : W := mkw 0x081084001911a1a4 0x2102108003223434 0x8073fc0019138385 0xd00e7f8003227070

def z1051 : W := mkw 0x08212b37a020f3ed 0x61042566f4041e7d 0x0800033f800033e2 0x01000067f000067c

def z1052 : W := mkw 0x15d4d4001dd70000 0x02ba9a8003bae000 0x41f3fc0019e38000 0xc83e7f80033c7000

def z1053 : W := mkw 0x27ef7bfde2080000 0x04fdef7fbc410000 0xf7ffffffe60c0003 0xfefffffffcc18000

def z1054 : W := mkw 0x129ed4001fdf0000 0x0253da8003fbe000 0x907ffc001fff8005 0xd20fff8003fff000

def z1055 : W := mkw 0x07ce500420000000 0x00f9ca0084000000 0xe7fffc0e60000001 0xfcffff81cc000000

def z1056 : W := mkw 0x07ce50020066c2a8 0x40f9ca00400cd855 0xdffffc0001ffc3fd 0xfbffff80003ff87f

def z1057 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xefffffffe1000387 0xfdfffffffc200070

def z1058 : W := mkw 0x27ee7abca0000000 0x04fdcf5794000000 0xe7fffffe00000003 0xfcffffffc0000000

def z1059 : W := mkw 0x25e57bbda0000000 0x04bcaf77b4000000 0xe7f3ffff80000003 0xfcfe7ffff0000000

def z1060 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfffc03fe7fec7f9e 0xffff807fcffd8ff3

def z1061 : W := mkw 0x07ce500000000000 0x00f9ca0000000000 0xe7fffc3e00000003 0xfcffff87c0000000

def z1062 : W := mkw 0x17ce500206ee4200 0x02f9ca0040ddc840 0x778c000e06ec4000 0x2ef18001c0dd8800

def z1063 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xefffffffe0007c03 0xfdfffffffc000f80

def z1064 : W := mkw 0x17ced4000edf0000 0x02f9da8001dbe000 0xd7fffc0006ff8001 0xfaffff8000dff000

def z1065 : W := mkw 0x0831afb99911b1e5 0x210635f73322363c 0xa873ffff9913b3e7 0xd50e7ffff322767c

def z1066 : W := mkw 0x00a56b35a0000000 0x0014ad66b4000000 0xc1f3ff3f80000003 0xd83e7fe7f0000000

def z1067 : W := mkw 0x27ef7bfde0001451 0x84fdef7fbc00028a 0xfffffffffe007c7f 0xffffffffffc00f8f

def z1068 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8073ff301913b385 0xd00e7fe603227670

def z1069 : W := mkw 0x27ef7bfde0460000 0x04fdef7fbc08c000 0xe7ffffffe01f8003 0xfcfffffffc03f000

def z1070 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xf7fffcc01fffcc05 0xfeffff9803fff980

def z1071 : W := mkw 0x07ee52a800000000 0x00fdca5500000000 0xc7fffc3e00000001 0xf8ffff87c0000000

def z1072 : W := mkw 0x0821af318811b1e5 0x210435e63102363c 0x8873ff318013b3e3 0xd10e7fe63002767c

def z1073 : W := mkw 0x020b85414a191451 0x804170a82943228a 0xbe0fffc1fe1ffc7f 0x77c1fff83fc3ff8f

def z1074 : W := mkw 0x220b99414a181451 0x844173282943028a 0xbe0f9fc1fe1c7c7f 0x77c1f3f83fc38f8f

def z1075 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xf7ffffc01fff8007 0xfefffff803fff000

def z1076 : W := mkw 0x15d4d4001fdf0000 0x02ba9a8003fbe000 0xd1f3fc001fff8005 0xda3e7f8003fff000

def z1077 : W := mkw 0x081084021931f3e5 0x2102108043263e7c 0x1800000019f3f3e4 0x03000000033e7e7c

def z1078 : W := mkw 0x27ef7bfde04680a8 0x44fdef7fbc08d015 0xe7ffffffe0038003 0xfcfffffffc007000

def z1079 : W := mkw 0x101084021fff4208 0x4202108043ffe841 0x100000001fffc01c 0x0200000003fff803

def z1080 : W := mkw 0x07ce7014a0000000 0x00f9ce0294000000 0xc7fffc3e00000001 0xf8ffff87c0000000

def z1081 : W := mkw 0x08212b338020f3e5 0x2104256670041e7c 0x2800033f800073e2 0x05000067f0000e7c

def z1082 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xc1ffff3fe0000003 0xd83fffe7fc000000

def z1083 : W := mkw 0x001084001d910000 0x0002108003b22000 0x9073fc001ff38005 0xd20e7f8003fe7000

def z1084 : W := mkw 0x37ded4447fdf0000 0x06fbda888ffbe000 0xd7fffc007fff8005 0xfaffff800ffff000

def z1085 : W := mkw 0x2831affdf911b5f5 0xa50635ffbf2236be 0xa873fffff913ffff 0xd50e7fffff227fff

def z1086 : W := mkw 0x0830ae309911a1a4 0x210615c613223434 0x0073fc3019038380 0xc00e7f8603207070

def z1087 : W := mkw 0x37ef7bfde4c60000 0x06fdef7fbc98c000 0xe7ffffffe0e00003 0xfcfffffffc1c0000

def z1088 : W := mkw 0x27ce50ce60664208 0x44f9ca19cc0cc841 0x678c00ce60e00000 0x2cf18019cc1c0000

def z1089 : W := mkw 0x0021ab31881090e1 0x000435663102121c 0x8873ff319913b3e7 0xd10e7fe63322767c

def z1090 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x8873fc31811383e7 0x910e7f863022707c

def z1091 : W := mkw 0x0811ad11991190e1 0x210235a23322321c 0x8873fc31991383e7 0xd10e7f863322707c

def z1092 : W := mkw 0x101084021fffebae 0x4202108043fffd75 0x180000001ffffffc 0x0300000003ffffff

def z1093 : W := mkw 0x0831af319b19b5f5 0xa10635e6336336be 0x8873ff319f13bfe7 0xd10e7fe633e277fc

def z1094 : W := mkw 0x020b014142081451 0x804160282841028a 0xbe0c03c1fe0c7c7e 0x77c180783fc18f8f

def z1095 : W := mkw 0x27ef7bfde00080a0 0x04fdef7fbc001014 0xefffffffe00003e3 0xfdfffffffc00007c

def z1096 : W := mkw 0x37ded4c85fdf0000 0x06fbda990bfbe000 0xd7fffcc01fff8005 0xfaffff9803fff000

def z1097 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x598c603fe1ffc3fd 0x8b318c07fc3ff87f

def z1098 : W := mkw 0x276b1be940000000 0x04ed637d28000000 0x47f39ffe00000000 0xc8fe73ffc0000000

def z1099 : W := mkw 0x20212bffe020ebae 0x4404257ffc041d75 0x280003ffe0007ffa 0x0500007ffc000fff

def z1100 : W := mkw 0x20212bfde0000000 0x0404257fbc000000 0x20739fffe0000002 0x440e73fffc000000

def z1101 : W := mkw 0x17de540017cf0000 0x02fbca8002f9e000 0xd7fffc0007ef8001 0xfaffff8000fdf000

def z1102 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xd1fffc0001ff8005 0xba3fff80003ff000

def z1103 : W := mkw 0x0830ae309911a1a4 0x210615c613223434 0x8873fc31991383e7 0xd10e7f863322707c

def z1104 : W := mkw 0x07de500015c60000 0x00fbca0002b8c000 0xd7fffc001fff8005 0xfaffff8003fff000

def z1105 : W := mkw 0x08312f319101a1a4 0x210625e632203434 0x8873ff319903b387 0xd10e7fe633207670

def z1106 : W := mkw 0x0831af319b19b1e5 0x210635e63363363c 0x9873ff319f1fb3e7 0xd30e7fe633e3f67c

def z1107 : W := mkw 0x08312f319101b1e5 0x210625e63220363c 0x8873ff318103b3e3 0xd10e7fe63020767c

def z1108 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0x6ff003fe1fe07f82 0xcdfe007fc3fc0ff0

def z1109 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0x51fffc001fff8005 0x8a3fff8003fff000

def z1110 : W := mkw 0x0010840019110000 0x0002108003222000 0xd1f3fc0019f38005 0xfa3e7f80033e7000

def z1111 : W := mkw 0x27ef7bfde04680a8 0x44fdef7fbc08d015 0xffffffffe01fc07f 0xfffffffffc03f80f

def z1112 : W := mkw 0x0830ae309911a1a4 0x210615c613223434 0x0073fc3001138381 0x800e7f8600227070

def z1113 : W := mkw 0x15f476beb5e7ebae 0x42be8ed7d6bcfd75 0x41f07c3e01e38380 0x883e0f87c03c7070

def z1114 : W := mkw 0x076a12a800000000 0x00ed425500000000 0xe7f39ffe00000002 0xfcfe73ffc0000000

def z1115 : W := mkw 0x15d4d4001dd70000 0x02ba9a8003bae000 0x41f3fc0001f38001 0x883e7f80003e7000

def z1116 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x9873ff31991ff3ff 0xd30e7fe63323fe7f

def z1117 : W := mkw 0x056002aa00204200 0x00ac005540040840 0xfff003fe1fe07f86 0xfffe007fc3fc0ff0

def z1118 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xdffffc019fff8067 0xfbffff8033fff00c

def z1119 : W := mkw 0x175a94001f990000 0x02eb528003f32000 0xd7f3fc001ff38005 0xfafe7f8003fe7000

def z1120 : W := mkw 0x0831af35b911b1e5 0x210635e6b722363c 0xa873ff3ff913b3e7 0xd50e7fe7ff22767c

def z1121 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xf7fffffffe000007 0xfeffffffffc00000

def z1122 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xc7f3fc001ff38005 0xd8fe7f8003fe7000

def z1123 : W := mkw 0x27ce50ce626e4618 0xc4f9ca19cc4dc8c3 0x778c00ce66ec4c18 0x2ef18019ccdd8983

def z1124 : W := mkw 0x020b81414a181451 0x804170282943028a 0x360f83c1fe1c7c79 0x66c1f0783fc38f8f

def z1125 : W := mkw 0x0831af319b19b5f5 0xa10635e6336336be 0xb87fff31ff1fffff 0xf70fffe63fe3ffff

def z1126 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0xae73fff19913b3e7 0xf5ce7ffe3322767c

def z1127 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xdffffc001fffc07d 0xfbffff8003fff80f

def z1128 : W := mkw 0x27cf79dde0000000 0x04f9ef3bbc000000 0xe7fffccfe0000001 0xfcffff99fc000000

def z1129 : W := mkw 0x076b2bf9c0000000 0x00ed657f38000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1130 : W := mkw 0x083086201911b1e5 0x210610c40322363c 0x8873ff301913b3e7 0xd10e7fe60322767c

def z1131 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0x47ffffffe0000001 0xc8fffffffc000000

def z1132 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0873ff319903b3e2 0xc10e7fe63320767c

def z1133 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0x718c603fe1ffc3f9 0xae318c07fc3ff87f

def z1134 : W := mkw 0x181084021ffffbe7 0x2302108043ffff7c 0x180000001fffffe4 0x0300000003fffffc

def z1135 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xfffffc001fffc007 0xffffff8003fff800

def z1136 : W := mkw 0x25f47abeb5e6ebae 0x44be8f57d6bcdd75 0x41f07c3e01e38380 0x883e0f87c03c7070

def z1137 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xd7f3fc001fe38004 0xfafe7f8003fc7000

def z1138 : W := mkw 0x0011a511991190e1 0x000234a23322321c 0x8873ff319913b3e7 0xd10e7fe63322767c

def z1139 : W := mkw 0x2831affdf911b1e5 0x250635ffbf22363c 0x280003fff913b3e6 0x0500007fff22767c

def z1140 : W := mkw 0x27ef5bed60000000 0x04fdeb7dac000000 0xe7ffffce60000001 0xfcfffff9cc000000

def z1141 : W := mkw 0x27ef7bfde2080410 0x84fdef7fbc410082 0xe7ffffffe00c001b 0xfcfffffffc018003

def z1142 : W := mkw 0x057002aa15a06b06 0x00ae005542b40d60 0xfff3fffe1fe07f87 0xfffe7fffc3fc0ff0

def z1143 : W := mkw 0x0831af319911b1e5 0x210635e63322363c 0x0873fc319913b3e5 0x810e7f863322767c

def z1144 : W := mkw 0x07ded40019570000 0x00fbda80032ae000 0xd7fffc0019ff8005 0xfaffff80033ff000

def z1145 : W := mkw 0x17ded4405fdf0410 0x82fbda880bfbe082 0xfffffcc1ffffcc7f 0xffffff983ffff98f

def z1146 : W := mkw 0x17ce500006ce0000 0x02f9ca0000d9c000 0xd7fffc0007ff8005 0xfaffff8000fff000

def z1147 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xc98c603fe1ff83ff 0x99318c07fc3ff07f

def z1148 : W := mkw 0x27ef7bfde0000000 0x04fdef7fbc000000 0xf7ffffffe6004c03 0xfefffffffcc00980

def z1149 : W := mkw 0x0d700eaa15a16b06 0x21ae01d542b42d60 0xfff01ffe1fe07f86 0xfffe03ffc3fc0ff0

def z1150 : W := mkw 0x15d4d4001dd70000 0x02ba9a8003bae000 0xd7f3fc001ff38005 0xfafe7f8003fe7000

def z1151 : W := mkw 0x121a84001fdf0000 0x0243508003fbe000 0x967ffc001fff8005 0xf2cfff8003fff000

def z1152 : W := mkw 0x27ee7abca0000000 0x04fdcf5794000000 0x41fffc3e00000001 0x883fff87c0000000

def z1153 : W := mkw 0x0084400000460000 0x001088000008c000 0xd1fffc0001ff8005 0xfa3fff80003ff000

def z1154 : W := mkw 0x07ee72bca0000000 0x00fdce5794000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1155 : W := mkw 0x0821af31881190e1 0x210435e63102321c 0x8873ff31811383e7 0xd10e7fe63022707c

def z1156 : W := mkw 0x00846016a066c2a8 0x40108c02d40cd855 0xf98c633ff9fff3ff 0xff318c67ff3ffe7f

def z1157 : W := mkw 0x27ef7bfde00080a0 0x04fdef7fbc001014 0xffffffffe11fc3ff 0xfffffffffc23f87f

def z1158 : W := mkw 0x20212bbda0000000 0x04042577b4000000 0x8073ff3f80000003 0xd00e7fe7f0000000

def z1159 : W := mkw 0x17ded4001fdf1451 0x82fbda8003fbe28a 0xffffffc01ffffc7f 0xfffffff803ffff8f

def z1160 : W := mkw 0x020b81434a385651 0x8041702869470aca 0xf98f803fe1fc43ff 0xbf31f007fc3f887f

def z1161 : W := mkw 0x0084400200664200 0x00108800400cc840 0xf98c603fe1ffc3ff 0xbf318c07fc3ff87f

def z1162 : W := mkw 0x08212b318000b1e5 0x210425663000163c 0x8873ff318113b3e7 0xd10e7fe63022767c

def z1163 : W := mkw 0x17ded4001fdf0000 0x02fbda8003fbe000 0xc7fffc001fe38001 0xf8ffff8003fc7000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z6]),(0,[z9,z1,z3,z10,z4,z5,z6]),(0,[z0,z1,z3,z4,z11,z5,z6]),(0,[z12,z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z14,z3,z15,z5,z6]),(0,[z0,z1,z3,z4,z5,z16,z6]),(0,[z0,z17,z1,z3,z4,z5,z6])],[(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z19,z6]),(0,[z20,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z5,z6]),(0,[z0,z1,z3,z22,z4,z5,z23])],[(0,[z0,z1,z24,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z25,z6]),(0,[z0,z26,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z27,z5,z6]),(0,[z28,z0,z1,z3,z22,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z29]),(0,[z0,z1,z3,z15,z30,z5,z6])],[(1,[z9,z1,z3,z10,z5,z6]),(0,[z31,z0,z1,z3,z5,z6,z32]),(1,[z33,z1,z3,z4,z5,z6]),(0,[z0,z1,z34,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z37])],[(0,[z12,z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z39,z5,z6]),(0,[z0,z1,z3,z40,z4,z5,z6]),(0,[z0,z1,z3,z41,z4,z5,z6]),(0,[z0,z1,z3,z4,z42,z5,z6]),(0,[z0,z43,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z23])],[(0,[z0,z1,z3,z45,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z46]),(0,[z0,z1,z3,z15,z47,z5,z6]),(0,[z0,z1,z3,z4,z48,z5,z6]),(0,[z49,z0,z1,z4,z5,z50,z6]),(0,[z0,z51,z1,z3,z4,z5,z6]),(0,[z52,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z53,z4,z5,z6])],[(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z5,z6]),(0,[z0,z1,z3,z4,z56,z5,z6]),(0,[z0,z1,z3,z57,z4,z58,z6]),(0,[z0,z1,z3,z15,z4,z5,z6])]],
   [[(1,[z0,z1,z59,z4,z5,z6]),(0,[z60,z61,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z62,z6])],[(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z58,z6]),(0,[z0,z1,z3,z65,z4,z6,z32]),(0,[z0,z1,z3,z4,z5,z6,z66])],[(1,[z0,z1,z3,z67,z5,z6]),(0,[z0,z1,z68,z69,z4,z5,z6]),(0,[z70,z1,z3,z71,z4,z5,z6]),(0,[z72,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z74]),(0,[z0,z1,z3,z4,z75,z5,z6]),(0,[z0,z1,z3,z4,z76,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z77]),(0,[z0,z1,z3,z4,z5,z78,z79]),(0,[z80,z0,z1,z3,z4,z81,z6]),(0,[z0,z1,z3,z4,z82,z5,z6])],[(0,[z0,z1,z3,z4,z67,z5,z6]),(0,[z0,z1,z3,z4,z5,z83,z6]),(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z85,z5,z6]),(0,[z0,z1,z3,z4,z5,z86,z6]),(0,[z0,z87,z1,z3,z4,z5,z6])],[],[(1,[z31,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z88]),(0,[z0,z1,z3,z89,z4,z5,z6])]],
   [[(0,[z0,z90,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z92,z5,z6]),(0,[z0,z1,z3,z4,z93,z5,z6]),(0,[z0,z1,z3,z4,z94,z5,z6])],[(0,[z95,z0,z1,z3,z4,z5,z6]),(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z12,z0,z1,z3,z4,z97,z6]),(0,[z0,z98,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z58,z6]),(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z100,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z101,z5,z6]),(0,[z102,z0,z1,z3,z4,z5,z6])],[(0,[z103,z0,z61,z3,z4,z5,z6]),(0,[z104,z0,z1,z3,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z106,z6])],[(0,[z0,z107,z1,z3,z4,z5,z108]),(0,[z104,z0,z1,z3,z4,z5,z78]),(0,[z0,z1,z3,z4,z109,z5,z6])],[(0,[z0,z1,z3,z4,z5,z110,z6]),(0,[z0,z1,z3,z4,z111,z5,z6]),(0,[z80,z0,z1,z3,z4,z92,z6]),(0,[z104,z0,z1,z3,z4,z112,z6])],[(0,[z0,z1,z3,z4,z5,z113,z6]),(1,[z0,z1,z3,z114,z5,z6])],[(0,[z0,z1,z3,z4,z5,z115,z6]),(0,[z0,z116,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z117])],[(0,[z0,z1,z3,z4,z118,z5,z6]),(0,[z0,z1,z3,z4,z5,z119,z6]),(0,[z0,z1,z3,z4,z5,z6,z120]),(0,[z0,z1,z3,z81,z5,z16,z6]),(0,[z0,z1,z3,z114,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z121]),(0,[z122,z0,z1,z3,z4,z5,z6])],[(0,[z123,z0,z1,z3,z4,z5,z6])],[(0,[z124,z0,z1,z3,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z126,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z127])],[(1,[z70,z1,z71,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z128,z6]),(0,[z0,z1,z3,z4,z5,z129,z6]),(0,[z130,z0,z1,z131,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z132,z6])],[(0,[z0,z133,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z134,z5,z6]),(0,[z73,z0,z1,z3,z135,z5,z6]),(0,[z0,z1,z3,z4,z136,z5,z6])],[(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z37]),(0,[z0,z1,z3,z4,z138,z139,z6])],[(0,[z103,z0,z1,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z5,z78,z32]),(0,[z0,z1,z141,z3,z4,z5,z32]),(0,[z0,z142,z1,z3,z4,z5,z6])],[(0,[z60,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z143,z4,z5,z6]),(0,[z0,z1,z3,z144,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z145,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z146]),(0,[z0,z147,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z148,z4,z5,z6])],[(0,[z0,z1,z149,z3,z4,z5,z6]),(0,[z70,z0,z1,z71,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z150]),(0,[z151,z0,z1,z3,z4,z5,z6])],[(0,[z152,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z153,z5,z64,z6]),(0,[z104,z0,z1,z3,z4,z5,z154])],[(0,[z155,z0,z1,z3,z4,z5,z6]),(0,[z156,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z157,z5,z6]),(0,[z0,z158,z1,z3,z4,z5,z6]),(0,[z159,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z78,z160]),(0,[z0,z1,z141,z3,z4,z5,z160]),(1,[z36,z0,z1,z3,z5,z37])],[(0,[z161,z0,z1,z3,z4,z5,z6]),(0,[z0,z162,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z163,z4,z5,z6]),(1,[z0,z1,z3,z164,z4,z5]),(0,[z0,z1,z3,z4,z5,z6,z79]),(0,[z0,z1,z3,z4,z5,z165,z6])],[(0,[z1,z3,z10,z4,z118,z5,z6]),(0,[z0,z1,z3,z166,z4,z5,z6]),(0,[z0,z1,z3,z4,z167,z5,z6]),(0,[z80,z0,z1,z131,z3,z4,z6]),(0,[z0,z1,z141,z3,z4,z5,z50])],[(0,[z168,z0,z1,z3,z4,z5,z6]),(0,[z80,z9,z0,z1,z3,z5,z6]),(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z154]),(0,[z0,z1,z3,z170,z4,z5,z6]),(0,[z0,z1,z3,z4,z171,z5,z6]),(0,[z0,z1,z3,z4,z5,z172,z6])],[(0,[z80,z173,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z174,z4,z5,z6])]],
   [[(0,[z175,z0,z1,z3,z4,z5,z6]),(0,[z176,z1,z177,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z178,z5,z6]),(0,[z28,z0,z1,z3,z4,z5,z6])],[(0,[z179,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z180,z4,z5,z6]),(0,[z181,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z81,z6])],[(0,[z0,z107,z1,z3,z30,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z182,z5,z6]),(0,[z0,z1,z3,z22,z4,z5,z37])],[(1,[z103,z69,z3,z4,z5,z6]),(0,[z1,z69,z3,z71,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z183]),(1,[z0,z1,z3,z4,z11,z5]),(0,[z0,z1,z3,z4,z5,z6,z184]),(0,[z0,z1,z141,z3,z22,z4,z5])],[(0,[z0,z3,z4,z92,z5,z58,z6]),(0,[z0,z1,z185,z3,z4,z5,z6]),(0,[z186,z0,z1,z3,z4,z5,z6])],[(0,[z187,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z139,z32]),(0,[z0,z188,z1,z3,z4,z5,z6]),(0,[z0,z1,z189,z3,z4,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z37])],[(0,[z0,z1,z3,z190,z4,z5,z6]),(0,[z0,z1,z3,z191,z4,z5,z6]),(0,[z0,z1,z3,z192,z4,z5,z6]),(1,[z0,z1,z3,z4,z193,z6]),(0,[z0,z1,z3,z4,z5,z194,z6]),(0,[z0,z1,z3,z4,z5,z6,z195]),(0,[z0,z1,z3,z4,z101,z132,z6])],[(0,[z196,z0,z107,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z197,z5,z6]),(0,[z0,z198,z1,z3,z4,z5,z6])]],
   [[(0,[z103,z0,z1,z199,z4,z5,z6]),(0,[z0,z1,z200,z3,z4,z5,z6]),(0,[z201,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z11,z5,z64]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z203,z5,z6]),(1,[z0,z1,z3,z4,z204,z6]),(1,[z12,z0,z205,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z206])],[(0,[z70,z0,z1,z3,z4,z5,z6]),(0,[z207,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z92,z6]),(0,[z0,z1,z3,z4,z5,z208,z6]),(0,[z209,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z210,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z139,z160])],[(0,[z0,z1,z3,z4,z211,z5,z6]),(0,[z0,z1,z3,z212,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z204,z6])],[(0,[z0,z1,z69,z3,z4,z5,z6]),(0,[z0,z213,z1,z3,z4,z118,z6]),(0,[z0,z1,z3,z214,z5,z64,z6]),(1,[z0,z1,z3,z4,z5,z215]),(1,[z196,z0,z3,z30,z5,z6]),(0,[z0,z1,z3,z216,z4,z5,z6])],[(0,[z173,z0,z1,z3,z22,z4,z6]),(0,[z217,z0,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z218,z4,z5,z6]),(0,[z219,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z220,z3,z4,z5,z6])],[(0,[z221,z0,z1,z3,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z223,z6]),(0,[z103,z0,z224,z3,z4,z5,z6]),(0,[z225,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z177,z3,z4,z5,z6]),(0,[z0,z1,z3,z118,z30,z5,z6]),(0,[z0,z1,z3,z4,z5,z226,z6]),(0,[z0,z227,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z228,z6]),(0,[z0,z1,z3,z4,z5,z229,z6])]],
   [[(0,[z230,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z231,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z232,z6]),(0,[z0,z1,z4,z5,z50,z6,z79])],[(0,[z103,z60,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z233]),(0,[z0,z1,z3,z234,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z235,z6]),(0,[z0,z236,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z237,z4,z5,z6]),(1,[z0,z1,z3,z214,z5,z6]),(0,[z217,z0,z1,z3,z4,z5,z160]),(0,[z0,z1,z3,z4,z5,z6,z238]),(0,[z239,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z240,z4,z5,z6])],[(1,[z0,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z4,z5,z6,z241]),(0,[z0,z1,z3,z242,z4,z5,z6]),(0,[z0,z1,z243,z3,z4,z5,z6]),(0,[z0,z1,z244,z3,z4,z5,z6]),(0,[z0,z1,z3,z245,z4,z5,z6])],[(0,[z246,z0,z1,z3,z4,z5,z6]),(0,[z60,z1,z3,z71,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z247,z6]),(0,[z0,z107,z3,z47,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z248,z6]),(0,[z0,z249,z1,z3,z4,z5,z6]),(0,[z0,z250,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z251,z5,z6])],[(0,[z0,z1,z3,z4,z252,z5,z6]),(0,[z0,z1,z253,z3,z4,z5,z6]),(0,[z0,z1,z131,z4,z5,z254,z6]),(0,[z0,z1,z3,z4,z5,z255,z6]),(0,[z0,z1,z3,z4,z5,z256,z6])],[(0,[z257,z0,z1,z3,z4,z5,z6]),(1,[z28,z1,z3,z4,z5,z160]),(0,[z0,z1,z3,z85,z4,z5,z6]),(0,[z0,z1,z3,z258,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z259])],[(0,[z0,z1,z3,z47,z5,z132,z6]),(0,[z0,z1,z3,z4,z138,z5,z154])]],
   [[(0,[z260,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z261,z5,z6]),(0,[z0,z1,z262,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z263,z6]),(0,[z0,z1,z3,z4,z264,z5,z6])],[(0,[z0,z1,z265,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z58,z254,z6]),(0,[z0,z1,z266,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z267,z5,z6])],[(1,[z0,z1,z3,z268,z4,z6]),(0,[z217,z0,z1,z3,z22,z4,z5]),(0,[z0,z1,z3,z4,z5,z269,z6]),(0,[z0,z1,z3,z270,z4,z5,z6]),(0,[z0,z1,z3,z271,z4,z5,z6])],[(0,[z103,z0,z1,z3,z4,z5,z241]),(0,[z272,z0,z1,z3,z4,z5,z6]),(0,[z273,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z274,z5,z6]),(0,[z0,z1,z275,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z276,z6])],[(0,[z0,z1,z3,z4,z92,z254,z6])],[(0,[z0,z1,z3,z4,z5,z6,z277]),(0,[z0,z1,z3,z4,z5,z278,z6]),(0,[z0,z1,z279,z3,z4,z5,z6]),(0,[z0,z280,z1,z3,z4,z5,z6])],[(0,[z281,z0,z1,z3,z22,z4,z6]),(0,[z0,z1,z3,z4,z5,z160,z132]),(0,[z0,z1,z3,z4,z5,z6,z282]),(0,[z0,z1,z3,z4,z5,z6,z283])],[(0,[z284,z0,z1,z3,z4,z5,z6]),(0,[z285,z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z4,z5,z286,z6]),(1,[z0,z1,z3,z191,z4,z5]),(0,[z287,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z288,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z289]),(0,[z0,z1,z3,z4,z290,z5,z6])]],
   [[(0,[z0,z1,z291,z3,z4,z5,z6]),(0,[z0,z1,z3,z292,z4,z5,z6]),(0,[z293,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z294,z3,z4,z5,z6]),(0,[z0,z1,z3,z30,z5,z132,z6]),(0,[z0,z1,z3,z4,z5,z6,z74]),(0,[z0,z1,z3,z22,z4,z92,z6]),(0,[z0,z295,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z81,z5,z165])],[(0,[z296,z0,z1,z3,z4,z5,z6])],[(0,[z285,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z165])],[(0,[z0,z1,z3,z205,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z297,z6]),(0,[z0,z1,z3,z22,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z50,z78]),(0,[z0,z1,z3,z4,z5,z298,z6]),(0,[z0,z1,z3,z4,z299,z5,z6])],[(0,[z0,z1,z3,z4,z300,z5,z6]),(0,[z0,z1,z3,z4,z5,z301,z6]),(0,[z302,z0,z1,z3,z4,z5,z6]),(0,[z0,z303,z1,z224,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z108]),(0,[z0,z304,z3,z4,z5,z6,z154]),(0,[z0,z1,z3,z305,z4,z5,z6])],[(1,[z0,z1,z3,z5,z83,z6]),(0,[z0,z1,z3,z306,z4,z5,z6]),(0,[z0,z1,z3,z307,z4,z5,z6]),(0,[z0,z1,z308,z3,z4,z5,z6])],[(0,[z0,z162,z1,z3,z4,z118,z5]),(0,[z0,z1,z3,z44,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z309,z6]),(0,[z0,z1,z141,z3,z4,z5,z79])]],
   [[(0,[z0,z1,z3,z4,z310,z5,z6]),(0,[z0,z1,z3,z4,z5,z311,z6]),(1,[z0,z1,z3,z4,z5,z278]),(0,[z0,z1,z3,z4,z5,z78,z6]),(0,[z0,z1,z3,z312,z4,z5,z6])],[],[(0,[z313,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z314,z4,z48,z5]),(1,[z0,z1,z3,z4,z315,z5]),(0,[z0,z316,z1,z3,z4,z5,z6])],[(0,[z70,z0,z1,z177,z4,z5,z6]),(0,[z0,z317,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z319])],[(1,[z0,z1,z3,z4,z110,z6]),(0,[z0,z1,z3,z4,z320,z5,z6]),(0,[z0,z1,z224,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z321,z6]),(0,[z0,z1,z3,z4,z5,z322,z6]),(0,[z0,z1,z3,z57,z4,z6,z23])],[(1,[z257,z0,z1,z3,z5,z6]),(0,[z0,z3,z47,z4,z30,z5,z6]),(0,[z0,z323,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z324]),(0,[z173,z0,z1,z3,z4,z153,z6]),(0,[z0,z1,z3,z4,z5,z6,z325]),(0,[z326,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z327,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z328,z6])],[(0,[z0,z303,z1,z205,z4,z5,z6]),(0,[z329,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z330,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z331,z6]),(0,[z332,z0,z1,z3,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z333,z6]),(1,[z0,z1,z3,z4,z5,z334]),(0,[z80,z0,z1,z3,z44,z5,z6])],[(0,[z0,z1,z3,z199,z4,z5,z6]),(0,[z0,z1,z68,z3,z4,z5,z6]),(0,[z335,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z336,z4,z5,z6]),(0,[z337,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z6,z338])],[(0,[z28,z0,z1,z3,z44,z4,z5]),(0,[z0,z1,z3,z4,z339,z5,z6])],[(0,[z0,z1,z3,z4,z5,z64,z6]),(0,[z340,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z297,z6]),(1,[z130,z0,z1,z4,z232,z6]),(0,[z130,z0,z1,z3,z57,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z338])],[(0,[z0,z1,z3,z4,z5,z341,z6]),(1,[z0,z1,z3,z237,z4,z5]),(0,[z0,z1,z3,z191,z4,z5,z64]),(0,[z28,z36,z0,z1,z3,z4,z5]),(1,[z0,z303,z224,z4,z5,z6])],[(0,[z342,z0,z1,z3,z4,z5,z6]),(0,[z343,z0,z1,z3,z4,z5,z6])],[(0,[z344,z0,z1,z3,z4,z5,z6]),(0,[z9,z0,z1,z3,z10,z5,z6]),(0,[z345,z0,z1,z3,z4,z5,z6]),(0,[z346,z0,z1,z3,z4,z5,z6]),(0,[z104,z0,z1,z3,z312,z5,z6]),(0,[z0,z1,z3,z4,z5,z139,z6]),(1,[z0,z1,z3,z4,z138,z139])]],
   [[(0,[z173,z0,z1,z3,z4,z64,z6]),(0,[z12,z0,z1,z3,z4,z5,z215])],[(0,[z0,z1,z3,z347,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z348])],[(0,[z0,z1,z3,z4,z349,z5,z6]),(0,[z0,z1,z3,z4,z350,z5,z6]),(0,[z0,z1,z3,z4,z5,z351,z6]),(0,[z104,z0,z3,z4,z5,z78,z6]),(0,[z130,z0,z1,z4,z232,z5,z6])],[(1,[z0,z1,z3,z4,z5,z223]),(0,[z0,z1,z3,z352,z4,z5,z6]),(0,[z173,z0,z1,z3,z4,z139,z6]),(0,[z281,z80,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z353,z4,z5,z6]),(0,[z0,z354,z1,z3,z4,z5,z6]),(0,[z0,z304,z1,z3,z4,z5,z78]),(0,[z0,z1,z3,z355,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z5,z127])],[(0,[z0,z1,z3,z4,z92,z153,z6]),(0,[z0,z1,z15,z4,z48,z5,z6]),(0,[z356,z0,z1,z3,z4,z5,z6])],[(0,[z285,z0,z1,z3,z118,z5,z6]),(0,[z0,z1,z3,z237,z4,z118,z5]),(1,[z104,z0,z3,z4,z5,z78])],[(1,[z60,z61,z3,z4,z5,z6]),(0,[z0,z1,z357,z3,z4,z5,z6]),(0,[z285,z0,z1,z3,z10,z5,z6]),(0,[z0,z1,z3,z358,z4,z5,z6]),(0,[z0,z1,z3,z4,z359,z5,z6])],[(0,[z281,z0,z1,z3,z4,z153,z6]),(0,[z217,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z232,z92,z6]),(0,[z0,z1,z3,z4,z360,z5,z6]),(0,[z361,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z362,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z138,z5]),(1,[z0,z1,z3,z22,z4,z23])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z3,z4,z363,z5,z6]),(0,[z36,z0,z1,z3,z44,z5,z6])],[(0,[z364,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z68,z4,z5,z6]),(0,[z0,z1,z3,z4,z365,z5,z6]),(0,[z0,z1,z3,z10,z30,z5,z6]),(1,[z0,z107,z3,z47,z5,z6]),(0,[z366,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z140,z4,z5,z6]),(0,[z176,z60,z1,z3,z4,z5,z6]),(0,[z73,z0,z3,z4,z92,z5,z6])],[(0,[z0,z1,z3,z4,z5,z367,z6]),(0,[z0,z1,z3,z4,z5,z6,z368]),(0,[z173,z0,z1,z3,z4,z5,z247]),(0,[z173,z1,z3,z4,z5,z64,z6]),(0,[z0,z1,z3,z4,z5,z369,z6]),(0,[z370,z0,z1,z3,z4,z5,z6])],[(0,[z0,z371,z1,z3,z4,z5,z6]),(0,[z0,z303,z224,z3,z4,z5,z6]),(1,[z73,z0,z3,z4,z92,z6]),(0,[z0,z1,z3,z372,z4,z5,z6]),(0,[z373,z0,z1,z3,z4,z5,z6]),(0,[z374,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z22,z4,z6,z23])],[(0,[z12,z70,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z10,z4,z5,z6]),(1,[z0,z1,z375,z3,z4,z6]),(0,[z0,z1,z376,z3,z4,z5,z6]),(0,[z377,z0,z1,z3,z4,z5,z6])],[(0,[z0,z213,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z105,z5,z6])],[(0,[z0,z1,z378,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z379,z5,z6]),(0,[z285,z1,z3,z4,z118,z5,z6]),(0,[z0,z1,z3,z4,z5,z160,z6]),(0,[z0,z1,z3,z4,z380,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z381]),(0,[z0,z1,z3,z382,z4,z5,z6]),(0,[z0,z383,z1,z3,z4,z5,z6])]],
   [[(0,[z103,z0,z1,z3,z4,z5,z6]),(0,[z384,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z385,z5,z6]),(0,[z0,z3,z4,z5,z78,z6,z154]),(0,[z0,z1,z3,z4,z105,z5,z6]),(1,[z0,z1,z3,z4,z112,z6]),(0,[z0,z1,z3,z4,z5,z386,z6]),(0,[z0,z1,z3,z5,z132,z6,z37]),(0,[z387,z0,z1,z3,z4,z5,z6])],[(0,[z281,z0,z1,z3,z4,z64,z6]),(0,[z0,z1,z3,z4,z92,z139,z6])],[(0,[z0,z1,z3,z388,z4,z5,z6]),(0,[z389,z0,z1,z3,z4,z5,z6]),(0,[z0,z304,z1,z3,z4,z5,z154]),(0,[z390,z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z4,z315,z5,z254]),(0,[z0,z1,z3,z391,z4,z5,z6])],[(0,[z0,z1,z3,z268,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z392,z6]),(0,[z0,z1,z3,z4,z5,z393,z6])],[(0,[z0,z394,z1,z3,z4,z5,z6]),(1,[z0,z213,z1,z3,z4,z6]),(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z281,z0,z1,z3,z4,z139,z6]),(1,[z0,z1,z14,z15,z5,z6]),(0,[z396,z0,z1,z3,z4,z5,z6])],[],[(0,[z397,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z398]),(0,[z0,z1,z3,z4,z399,z5,z6]),(0,[z390,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z400,z5,z6]),(0,[z0,z401,z1,z3,z4,z5,z6])],[(0,[z402,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z403,z4,z5,z6]),(0,[z0,z1,z404,z3,z4,z5,z6])]],
   [[(0,[z405,z0,z1,z3,z4,z5,z6]),(0,[z406,z0,z3,z71,z4,z5,z6]),(0,[z0,z407,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z312,z5,z6])],[(0,[z0,z1,z3,z4,z5,z408,z6]),(0,[z0,z1,z3,z4,z409,z5,z6]),(0,[z0,z1,z3,z4,z5,z410,z6])],[(0,[z0,z1,z411,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z412,z6]),(0,[z0,z1,z413,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z6,z23]),(0,[z36,z0,z1,z3,z4,z5,z132])],[(0,[z414,z0,z1,z3,z4,z5,z6]),(0,[z406,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z415,z6]),(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z0,z1,z3,z417,z4,z5,z6])],[(0,[z0,z1,z3,z418,z4,z5,z6]),(0,[z285,z9,z1,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z47,z5,z6])],[(0,[z103,z0,z1,z59,z4,z5,z6]),(0,[z196,z0,z1,z3,z4,z5,z6]),(0,[z293,z0,z1,z3,z5,z254,z6])],[(0,[z419,z0,z1,z3,z4,z5,z6]),(0,[z420,z0,z1,z3,z4,z5,z6]),(1,[z0,z304,z3,z4,z5,z154]),(0,[z421,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z164,z4,z5,z254])],[(0,[z0,z1,z3,z4,z5,z6,z422]),(0,[z423,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z215,z6]),(0,[z0,z1,z424,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z278]),(0,[z0,z425,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z426,z6])]],
   [[(0,[z427,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z428,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z429]),(0,[z73,z0,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z430,z4,z5,z6]),(0,[z0,z1,z4,z232,z5,z254,z6])],[(0,[z0,z1,z3,z4,z5,z431,z6]),(0,[z70,z0,z303,z1,z4,z5,z6]),(0,[z0,z1,z3,z432,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z433])],[(0,[z434,z0,z1,z3,z4,z5,z6]),(0,[z9,z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z435,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z436]),(0,[z0,z1,z3,z314,z4,z5,z6]),(0,[z0,z1,z141,z3,z44,z4,z5]),(0,[z0,z1,z3,z4,z81,z5,z437])],[(0,[z0,z438,z1,z3,z4,z5,z6]),(0,[z439,z0,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z79])],[(0,[z440,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z441,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z437])],[(0,[z0,z1,z3,z22,z4,z5,z6])],[(0,[z0,z1,z224,z71,z4,z5,z6]),(0,[z9,z0,z1,z3,z4,z5,z6]),(0,[z442,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z443,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z444])]],
   [[(0,[z0,z1,z59,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z445,z6]),(0,[z12,z0,z1,z3,z4,z5,z77]),(0,[z446,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z447,z6]),(0,[z448,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z449,z3,z4,z5,z6])],[(0,[z0,z1,z3,z71,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z450,z6])],[(0,[z0,z1,z3,z451,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z452,z6]),(0,[z453,z0,z1,z3,z4,z5,z6]),(0,[z0,z454,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z455]),(0,[z80,z0,z1,z3,z4,z138,z6])],[(0,[z0,z1,z3,z456,z4,z5,z6]),(0,[z0,z1,z3,z4,z457,z5,z6]),(0,[z0,z1,z3,z4,z5,z458,z6]),(0,[z12,z0,z1,z224,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z254,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(1,[z246,z0,z1,z4,z5,z6]),(0,[z0,z227,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z459,z5,z6]),(0,[z460,z0,z1,z3,z4,z5,z6])],[(0,[z176,z0,z1,z3,z4,z5,z183]),(0,[z0,z1,z14,z3,z81,z5,z6])],[(0,[z0,z1,z461,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z462,z6]),(0,[z0,z1,z3,z4,z5,z463,z6]),(0,[z80,z0,z1,z3,z57,z5,z6]),(0,[z464,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z465,z1,z3,z4,z5,z6]),(1,[z0,z162,z1,z3,z4,z5]),(0,[z0,z1,z466,z3,z4,z5,z6]),(0,[z28,z217,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z30,z5,z6]),(0,[z467,z0,z1,z3,z4,z5,z6])],[(0,[z176,z0,z1,z71,z4,z5,z6]),(0,[z0,z1,z468,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z469]),(0,[z0,z1,z3,z4,z5,z470,z6]),(0,[z0,z1,z3,z471,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z472,z6]),(0,[z0,z1,z3,z4,z5,z473,z6]),(0,[z0,z1,z14,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z474,z5,z6]),(0,[z0,z1,z3,z4,z475,z5,z6]),(0,[z0,z1,z3,z476,z4,z5,z6]),(0,[z477,z0,z1,z3,z4,z5,z6])],[(1,[z406,z0,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z47,z5,z6]),(0,[z478,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z141,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z132])],[(0,[z479,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z480]),(0,[z80,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z481,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z482]),(0,[z0,z1,z375,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z483,z5,z6])],[(0,[z70,z176,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z4,z5,z32]),(0,[z12,z0,z1,z205,z4,z5,z6]),(0,[z484,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z485,z5,z6])],[(0,[z0,z1,z486,z3,z4,z5,z6]),(0,[z36,z217,z0,z1,z3,z4,z5]),(0,[z487,z0,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z16,z6]),(1,[z0,z1,z3,z44,z5,z132]),(0,[z0,z1,z3,z4,z5,z6,z488])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z489]),(0,[z0,z1,z3,z4,z5,z490,z6]),(0,[z80,z0,z1,z3,z5,z16,z6])],[(0,[z0,z61,z1,z3,z4,z5,z6]),(0,[z491,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z492,z3,z4,z5,z6])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z217,z0,z1,z3,z44,z4,z5]),(0,[z0,z1,z3,z4,z493,z5,z6]),(0,[z0,z1,z3,z4,z5,z494,z6])],[(0,[z49,z0,z1,z3,z4,z5,z160]),(1,[z0,z1,z3,z85,z5,z6])],[(0,[z173,z0,z1,z3,z4,z5,z277]),(0,[z0,z495,z1,z3,z4,z5,z6]),(0,[z496,z0,z1,z3,z4,z5,z6]),(1,[z49,z0,z1,z4,z5,z50]),(0,[z0,z1,z3,z4,z5,z497,z6])],[(0,[z0,z1,z3,z4,z5,z498,z6]),(0,[z49,z0,z1,z3,z4,z5,z50]),(0,[z0,z1,z3,z4,z5,z499,z6])],[(0,[z0,z1,z3,z4,z5,z50,z154]),(0,[z500,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z501]),(0,[z502,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z503,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z504,z6]),(0,[z0,z1,z505,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z77]),(0,[z36,z0,z1,z3,z30,z5,z6]),(0,[z104,z0,z304,z3,z4,z5,z6]),(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z506])]],
   [[(0,[z0,z1,z507,z3,z4,z5,z6]),(0,[z0,z1,z3,z22,z4,z5,z132])],[(0,[z176,z0,z1,z3,z4,z5,z6]),(0,[z508,z0,z1,z3,z4,z5,z6]),(0,[z9,z0,z1,z3,z118,z5,z6]),(0,[z0,z1,z3,z4,z5,z509,z6]),(0,[z0,z1,z3,z4,z5,z510,z6]),(0,[z0,z1,z3,z4,z5,z6,z23])],[(0,[z0,z1,z3,z4,z511,z5,z6]),(0,[z36,z0,z1,z3,z47,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z512]),(0,[z12,z0,z3,z205,z4,z5,z6]),(0,[z0,z513,z1,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z22,z4,z5]),(0,[z0,z1,z3,z4,z5,z514,z6]),(0,[z80,z0,z1,z3,z5,z6,z37]),(0,[z36,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z132])],[(0,[z0,z1,z3,z515,z4,z5,z6]),(0,[z0,z1,z516,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z517,z5,z6]),(0,[z518,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z519,z5,z6]),(0,[z0,z1,z520,z3,z4,z5,z6])],[(0,[z9,z0,z1,z3,z5,z132,z6]),(0,[z0,z303,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z521,z5,z6]),(0,[z0,z1,z3,z4,z5,z522,z6]),(0,[z0,z1,z3,z4,z5,z523,z6]),(0,[z80,z0,z1,z14,z3,z5,z6])],[(0,[z524,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z247]),(1,[z390,z0,z1,z48,z5,z6]),(0,[z525,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z526,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z160,z23]),(0,[z527,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z528,z6]),(0,[z0,z1,z3,z57,z4,z138,z6])],[(1,[z0,z1,z3,z140,z5,z6]),(0,[z285,z0,z1,z3,z4,z5,z334]),(0,[z529,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z530,z3,z4,z5,z6]),(0,[z0,z1,z131,z3,z57,z4,z6])],[(0,[z217,z1,z3,z4,z5,z6,z32]),(0,[z0,z1,z531,z3,z4,z5,z6]),(0,[z73,z0,z1,z3,z4,z92,z6]),(0,[z0,z1,z3,z532,z4,z5,z6])],[(0,[z0,z1,z3,z4,z533,z5,z6]),(0,[z0,z1,z71,z205,z4,z5,z6]),(0,[z0,z1,z3,z534,z4,z5,z6]),(0,[z0,z535,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z536,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z537,z6]),(0,[z285,z0,z1,z3,z5,z132,z6]),(0,[z0,z1,z3,z4,z538,z5,z6]),(0,[z539,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z540,z5,z6]),(0,[z0,z1,z541,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z135,z5,z6]),(0,[z0,z1,z3,z4,z542,z5,z6])],[(0,[z0,z543,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z544,z4,z5,z6]),(0,[z1,z3,z4,z5,z160,z6,z32]),(0,[z0,z1,z545,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z546,z6]),(1,[z0,z1,z3,z4,z5,z127]),(0,[z0,z1,z3,z57,z81,z5,z6])],[(0,[z0,z547,z1,z3,z4,z5,z6]),(0,[z548,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z549,z3,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z5,z550])],[(0,[z0,z1,z3,z4,z97,z5,z6])]],
   [[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z103,z0,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z551,z4,z5,z6]),(0,[z552,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z553,z5,z6]),(0,[z0,z554,z1,z3,z4,z5,z6]),(0,[z555,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z556]),(0,[z0,z1,z3,z4,z92,z64,z6]),(0,[z557,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z297,z5,z6]),(0,[z0,z1,z3,z4,z58,z139,z6]),(0,[z558,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z5,z6]),(1,[z0,z1,z3,z57,z81,z6])],[(0,[z0,z1,z3,z4,z5,z32,z23]),(0,[z0,z1,z559,z3,z4,z5,z6]),(1,[z0,z1,z243,z3,z4,z5]),(0,[z0,z1,z3,z560,z4,z5,z6]),(0,[z36,z0,z1,z3,z5,z6,z37])],[(0,[z12,z60,z0,z3,z4,z5,z6]),(0,[z561,z0,z1,z3,z4,z5,z6]),(0,[z0,z562,z1,z3,z4,z5,z6])],[(0,[z563,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z57,z4,z16,z6])],[(0,[z0,z1,z3,z4,z153,z5,z6]),(0,[z73,z0,z227,z3,z4,z5,z6]),(1,[z0,z1,z141,z4,z5,z79]),(0,[z0,z564,z1,z3,z4,z5,z6])],[(0,[z38,z0,z1,z3,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z5,z436]),(0,[z0,z1,z3,z4,z5,z565,z6]),(0,[z0,z1,z3,z4,z81,z5,z6])],[(0,[z0,z1,z566,z3,z4,z5,z6]),(0,[z567,z0,z1,z3,z4,z5,z6]),(0,[z0,z227,z1,z3,z4,z92,z6]),(0,[z0,z568,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z569,z6]),(1,[z0,z1,z3,z4,z101,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z570,z6]),(0,[z571,z0,z1,z3,z4,z5,z6]),(0,[z572,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z204,z6,z32]),(0,[z0,z33,z1,z3,z4,z5,z6]),(0,[z573,z0,z1,z3,z4,z5,z6]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z575,z5,z6]),(0,[z0,z1,z3,z5,z139,z6,z338])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z576,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z577,z4,z5,z6]),(0,[z12,z0,z1,z3,z45,z5,z6]),(0,[z0,z578,z1,z3,z4,z5,z6])],[(1,[z0,z1,z199,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z579,z4,z5,z6]),(0,[z0,z227,z3,z4,z5,z58,z6]),(0,[z0,z1,z3,z4,z112,z5,z6])],[(1,[z285,z1,z3,z118,z5,z6]),(0,[z196,z0,z1,z3,z30,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z580]),(0,[z0,z1,z375,z3,z4,z48,z6]),(0,[z0,z581,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z6]),(0,[z0,z1,z3,z114,z5,z139,z6])],[(0,[z0,z1,z3,z582,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z583,z6])],[(0,[z0,z1,z3,z584,z4,z5,z6])],[(0,[z173,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z585,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z586]),(0,[z0,z1,z3,z22,z4,z138,z6])],[(0,[z587,z0,z1,z3,z4,z5,z6]),(0,[z60,z0,z61,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z588,z6]),(0,[z0,z1,z3,z4,z589,z5,z6]),(0,[z590,z0,z1,z3,z4,z5,z6])],[(0,[z591,z0,z1,z3,z4,z5,z6]),(0,[z390,z0,z1,z3,z48,z5,z6]),(0,[z0,z1,z3,z592,z4,z5,z6])],[(0,[z103,z0,z1,z3,z67,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z324]),(0,[z176,z0,z1,z177,z4,z5,z6]),(0,[z0,z1,z3,z4,z593,z5,z6]),(0,[z173,z0,z1,z3,z57,z4,z6]),(0,[z217,z0,z1,z3,z4,z138,z5]),(0,[z0,z1,z3,z4,z5,z594,z6]),(0,[z390,z0,z1,z14,z4,z5,z6])],[(0,[z0,z1,z3,z4,z595,z5,z6]),(0,[z0,z1,z3,z596,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z597])],[(1,[z176,z1,z177,z4,z5,z6]),(1,[z173,z1,z3,z4,z64,z6]),(0,[z598,z0,z1,z3,z4,z5,z6]),(0,[z599,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z600,z6])],[(0,[z60,z0,z69,z3,z4,z5,z6]),(0,[z601,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z334]),(0,[z285,z0,z1,z3,z4,z5,z398]),(0,[z0,z1,z602,z3,z4,z5,z6]),(0,[z603,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z604,z5,z6]),(0,[z49,z0,z1,z141,z4,z5,z6])],[(0,[z28,z0,z1,z3,z4,z138,z5]),(0,[z0,z1,z243,z3,z4,z48,z5]),(1,[z0,z1,z3,z314,z4,z5]),(0,[z605,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z606,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z153,z58,z6]),(0,[z0,z1,z3,z4,z5,z6,z607]),(0,[z0,z1,z131,z3,z4,z232,z6]),(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z44,z81,z5,z6])],[(0,[z103,z0,z1,z3,z4,z110,z6]),(0,[z0,z1,z3,z5,z83,z6,z32]),(0,[z608,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z37]),(0,[z0,z1,z3,z4,z5,z6,z609])],[(0,[z0,z1,z3,z610,z4,z5,z6]),(1,[z0,z1,z3,z4,z611,z6]),(0,[z612,z0,z1,z3,z4,z5,z6]),(0,[z613,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z614,z6]),(0,[z31,z0,z1,z3,z4,z5,z6]),(1,[z80,z0,z1,z3,z16,z6]),(0,[z0,z1,z3,z615,z4,z5,z6])],[(0,[z0,z1,z3,z44,z4,z5,z6])],[(0,[z61,z1,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z611,z6]),(0,[z0,z1,z3,z4,z5,z436,z6]),(0,[z0,z1,z3,z355,z4,z48,z6]),(0,[z0,z1,z3,z616,z4,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z139]),(0,[z617,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z241]),(0,[z618,z0,z1,z3,z4,z5,z6])],[(0,[z285,z36,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z619])]],
   [[(0,[z0,z1,z3,z4,z620,z5,z6]),(0,[z621,z0,z1,z3,z4,z5,z6]),(0,[z281,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z160,z37]),(0,[z0,z1,z3,z4,z5,z622,z6])],[(1,[z0,z1,z3,z45,z5,z6])],[(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z65,z4,z5,z6]),(0,[z104,z0,z1,z3,z4,z193,z6])],[],[(0,[z103,z0,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z624,z5,z6]),(0,[z281,z0,z1,z3,z57,z4,z6]),(0,[z36,z0,z1,z3,z4,z5,z78]),(0,[z36,z0,z1,z141,z3,z4,z5])],[(0,[z625,z0,z1,z3,z4,z5,z6]),(0,[z285,z80,z0,z1,z3,z5,z6]),(0,[z281,z1,z3,z4,z153,z5,z6]),(1,[z0,z1,z3,z4,z13,z6]),(0,[z0,z626,z1,z3,z4,z5,z6])],[(0,[z627,z0,z1,z3,z4,z5,z6]),(0,[z12,z0,z1,z3,z538,z5,z6]),(0,[z628,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z629,z5,z6]),(0,[z0,z1,z3,z4,z5,z630,z6])]],
   [[(0,[z631,z0,z1,z3,z4,z5,z6]),(0,[z103,z0,z1,z3,z4,z5,z223]),(1,[z0,z1,z3,z4,z5,z277]),(0,[z0,z1,z3,z4,z5,z13,z6]),(0,[z0,z1,z3,z4,z5,z50,z6])],[(0,[z632,z0,z1,z3,z4,z5,z6]),(1,[z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z131,z3,z4,z254,z6]),(0,[z0,z1,z3,z4,z629,z5,z6]),(0,[z0,z1,z3,z633,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z32,z37]),(0,[z0,z1,z3,z47,z81,z5,z6]),(0,[z0,z1,z141,z4,z5,z6,z79])],[],[(0,[z0,z1,z3,z634,z4,z5,z6]),(1,[z0,z227,z3,z4,z58,z6]),(0,[z0,z1,z3,z22,z4,z58,z6]),(1,[z0,z1,z3,z4,z5,z74]),(1,[z293,z0,z1,z3,z5,z6]),(0,[z36,z0,z1,z3,z4,z5,z23])],[(0,[z0,z1,z3,z4,z5,z183,z6]),(0,[z0,z1,z635,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z636,z5,z6])],[(0,[z0,z3,z388,z71,z4,z5,z6]),(0,[z0,z1,z3,z47,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z637,z6]),(0,[z0,z1,z14,z3,z48,z5,z6]),(0,[z0,z1,z3,z4,z638,z5,z6]),(1,[z0,z1,z3,z4,z6,z501])],[(0,[z639,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z177,z224,z4,z5,z6]),(0,[z0,z1,z3,z4,z640,z5,z6]),(0,[z0,z1,z3,z641,z4,z5,z6]),(1,[z0,z1,z3,z355,z4,z6]),(0,[z642,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z81,z5,z6,z37]),(0,[z0,z1,z3,z4,z139,z6,z23])]],
   [[(1,[z0,z3,z388,z4,z5,z6]),(0,[z257,z0,z1,z3,z5,z64,z6]),(1,[z0,z1,z3,z4,z5,z108]),(0,[z0,z1,z3,z4,z5,z550,z6])],[(0,[z0,z1,z3,z643,z4,z5,z6]),(0,[z12,z0,z303,z3,z4,z5,z6]),(0,[z644,z0,z1,z3,z4,z5,z6])],[(0,[z176,z1,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z645,z5,z6]),(0,[z0,z1,z3,z4,z5,z154,z79]),(0,[z390,z0,z1,z4,z48,z5,z6]),(0,[z0,z1,z3,z4,z646,z5,z6])],[(0,[z1,z177,z3,z71,z4,z5,z6]),(0,[z80,z130,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z132,z6,z501])],[(0,[z0,z1,z3,z4,z647,z5,z6]),(0,[z0,z1,z648,z3,z4,z5,z6]),(0,[z0,z649,z1,z3,z4,z5,z6]),(0,[z12,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z30,z81,z5,z6]),(0,[z650,z0,z1,z3,z4,z5,z6])],[(0,[z12,z176,z0,z1,z4,z5,z6]),(1,[z0,z1,z3,z4,z97,z6]),(0,[z390,z0,z1,z3,z15,z5,z6])],[(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z60,z0,z224,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z652,z5,z6]),(0,[z653,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z654,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z139])],[(0,[z28,z1,z3,z4,z5,z160,z6]),(0,[z0,z1,z3,z47,z48,z5,z6]),(0,[z0,z1,z3,z4,z232,z5,z6])]],
   [[(0,[z655,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z656,z4,z5,z6]),(0,[z0,z1,z3,z4,z657,z5,z6]),(0,[z658,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z131,z3,z4,z5,z6])],[(0,[z0,z1,z177,z205,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z132,z32]),(0,[z0,z1,z3,z4,z659,z5,z6]),(0,[z196,z0,z3,z4,z30,z5,z6])],[(0,[z0,z107,z1,z3,z47,z5,z6]),(0,[z80,z0,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z5,z6,z660]),(0,[z0,z1,z3,z44,z5,z132,z6])],[(0,[z0,z224,z3,z205,z4,z5,z6]),(0,[z0,z107,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z661,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z154])],[(0,[z662,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z65,z4,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z664,z6]),(0,[z0,z1,z3,z4,z5,z665,z6]),(0,[z0,z1,z3,z4,z666,z5,z6])],[(0,[z246,z0,z1,z69,z4,z5,z6]),(0,[z12,z33,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z538,z5,z6]),(1,[z0,z1,z3,z135,z5,z6]),(0,[z0,z1,z3,z667,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z78]),(0,[z0,z1,z3,z4,z668,z5,z6])],[(1,[z217,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z193,z6]),(0,[z0,z1,z3,z4,z5,z669,z6]),(0,[z670,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z671,z3,z4,z5,z6])],[(0,[z0,z1,z3,z672,z4,z5,z6]),(0,[z0,z304,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z254,z6]),(0,[z0,z1,z141,z3,z4,z138,z5])]],
   [[(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z674,z5,z6])],[(0,[z176,z0,z303,z1,z4,z5,z6]),(0,[z0,z1,z3,z675,z4,z5,z6]),(0,[z0,z1,z3,z676,z4,z5,z6]),(0,[z0,z1,z3,z30,z48,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z677]),(0,[z0,z1,z3,z4,z315,z5,z6])],[(0,[z36,z9,z0,z1,z3,z5,z6]),(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z160,z154]),(1,[z0,z1,z131,z4,z254,z6]),(0,[z0,z1,z3,z4,z5,z6,z437])],[(0,[z103,z12,z0,z3,z4,z5,z6]),(0,[z679,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z32]),(0,[z0,z1,z3,z22,z4,z5,z139])],[(0,[z103,z1,z69,z3,z4,z5,z6])],[(0,[z680,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z23])],[(0,[z0,z1,z3,z268,z4,z118,z6]),(0,[z28,z0,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z6,z681]),(0,[z0,z1,z3,z44,z4,z5,z139]),(0,[z0,z1,z3,z4,z5,z6,z682])],[(0,[z0,z1,z3,z4,z5,z398,z6]),(0,[z683,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z47,z118,z5,z6]),(0,[z684,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z550]),(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z686,z3,z4,z5,z6])],[(0,[z0,z1,z687,z3,z4,z5,z6]),(0,[z0,z1,z3,z47,z10,z5,z6]),(0,[z281,z173,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z214,z5,z6]),(0,[z0,z1,z3,z4,z30,z5,z6]),(0,[z0,z688,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z689,z6]),(0,[z0,z1,z3,z4,z232,z58,z6]),(0,[z0,z1,z3,z22,z4,z5,z78]),(0,[z0,z1,z3,z629,z5,z254,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z28,z0,z1,z3,z4,z5,z160]),(0,[z0,z1,z690,z3,z4,z5,z6]),(0,[z49,z0,z1,z3,z44,z4,z5]),(0,[z0,z1,z3,z4,z5,z691,z6])],[(0,[z176,z0,z1,z3,z4,z5,z324]),(0,[z0,z1,z3,z4,z5,z32,z154]),(0,[z0,z1,z3,z692,z4,z5,z6]),(0,[z80,z390,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6])],[(0,[z0,z1,z3,z694,z4,z5,z6]),(0,[z0,z1,z3,z4,z695,z5,z6]),(0,[z0,z107,z1,z3,z4,z611,z6]),(0,[z0,z1,z3,z4,z696,z5,z6]),(0,[z0,z1,z697,z3,z4,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z78]),(0,[z0,z1,z3,z4,z698,z5,z6]),(0,[z0,z1,z3,z164,z4,z5,z6]),(0,[z49,z36,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z699,z6]),(0,[z0,z1,z700,z3,z4,z5,z6]),(0,[z701,z0,z1,z3,z4,z5,z6]),(1,[z281,z1,z3,z4,z153,z6]),(0,[z0,z1,z3,z4,z702,z5,z6]),(0,[z0,z1,z703,z3,z4,z5,z6])],[(0,[z704,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z705,z5,z6]),(0,[z0,z1,z14,z15,z4,z5,z6]),(0,[z0,z706,z1,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z38,z1,z3,z4,z5,z6]),(0,[z0,z1,z707,z4,z5,z6]),(0,[z103,z69,z3,z140,z5,z6]),(0,[z708,z0,z1,z3,z5,z6]),(0,[z0,z224,z709,z4,z5,z6]),(0,[z0,z1,z3,z710,z5,z6])],[(0,[z104,z0,z3,z4,z112,z78]),(0,[z0,z1,z3,z4,z711,z6]),(0,[z36,z0,z1,z3,z182,z5])],[(0,[z0,z1,z59,z4,z5,z241]),(0,[z0,z1,z3,z4,z712,z6]),(0,[z12,z38,z205,z4,z5,z6]),(0,[z0,z1,z375,z3,z30,z6]),(0,[z390,z0,z1,z375,z48,z6]),(0,[z0,z1,z3,z4,z713,z5])],[(0,[z0,z1,z3,z714,z5,z6]),(0,[z0,z1,z3,z715,z4,z5]),(0,[z293,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z716,z5,z6]),(0,[z36,z0,z1,z3,z5,z334]),(0,[z281,z257,z0,z1,z3,z6])],[(0,[z0,z1,z3,z67,z5,z241]),(0,[z1,z717,z3,z4,z5,z6]),(0,[z0,z1,z3,z718,z5,z6]),(0,[z33,z1,z3,z4,z13,z6])],[(0,[z0,z1,z3,z4,z719,z5]),(0,[z12,z0,z205,z538,z5,z6]),(0,[z0,z1,z3,z355,z4,z6])],[(0,[z80,z0,z1,z3,z115,z6]),(0,[z0,z1,z720,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z108])]],
   [[(0,[z0,z1,z3,z4,z5,z721]),(0,[z246,z1,z71,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z722]),(0,[z0,z1,z3,z164,z629,z5]),(0,[z0,z1,z3,z5,z6,z723])],[(0,[z0,z724,z3,z4,z5,z6]),(0,[z0,z213,z1,z3,z30,z6]),(0,[z0,z1,z3,z65,z4,z23]),(0,[z0,z1,z697,z4,z254,z6]),(0,[z0,z51,z3,z4,z92,z6]),(0,[z104,z0,z3,z312,z5,z78])],[(0,[z0,z1,z3,z4,z725,z6]),(0,[z80,z0,z1,z3,z5,z334]),(0,[z0,z1,z3,z105,z112,z6]),(0,[z726,z0,z1,z3,z4,z5])],[(0,[z727,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z297,z436]),(0,[z0,z1,z375,z243,z3,z4])],[(0,[z0,z1,z4,z728,z5,z6]),(0,[z0,z1,z3,z4,z97,z6])],[(0,[z0,z729,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z730]),(0,[z0,z1,z3,z4,z5,z731]),(0,[z31,z0,z1,z3,z5,z132]),(0,[z0,z1,z3,z732,z5,z6]),(0,[z0,z1,z3,z733,z5,z6]),(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z1,z3,z4,z6,z735]),(0,[z0,z1,z141,z148,z4,z5])],[(0,[z246,z176,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z183]),(0,[z104,z0,z3,z4,z5,z736])]],
   [[(0,[z0,z1,z737,z4,z5,z6]),(0,[z0,z323,z3,z4,z58,z6]),(0,[z80,z0,z1,z3,z351,z6])],[],[(0,[z103,z69,z199,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z738]),(0,[z739,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z740]),(0,[z741,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z742,z5,z6])],[(0,[z0,z1,z3,z312,z5,z78])],[(1,[z1,z743,z4,z5,z6]),(0,[z176,z33,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z744,z6]),(0,[z12,z0,z205,z4,z5,z6]),(0,[z0,z1,z3,z4,z745,z6]),(0,[z0,z1,z3,z135,z5,z6]),(0,[z0,z1,z3,z312,z112,z6])],[(0,[z217,z1,z3,z4,z5,z32]),(0,[z33,z1,z3,z4,z97,z6]),(0,[z0,z1,z131,z4,z315,z254])],[(0,[z293,z0,z1,z3,z58,z6]),(0,[z0,z1,z746,z48,z5,z6]),(0,[z0,z1,z3,z4,z138,z550])],[(0,[z0,z1,z3,z4,z747,z6]),(0,[z196,z0,z3,z748,z5,z6]),(0,[z0,z1,z3,z85,z5,z278]),(0,[z0,z1,z3,z4,z5,z749])]],
   [[(0,[z0,z1,z3,z750,z5,z6]),(0,[z751,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z752,z5,z6]),(0,[z196,z0,z3,z30,z5,z6]),(0,[z0,z107,z3,z47,z5,z436]),(0,[z0,z1,z3,z85,z58,z6]),(0,[z0,z454,z3,z4,z58,z6])],[(0,[z0,z224,z610,z4,z5,z6]),(0,[z406,z60,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z753]),(0,[z406,z0,z3,z754,z5,z6]),(0,[z0,z1,z3,z4,z5,z755])],[(0,[z756,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z112,z154]),(0,[z613,z0,z3,z4,z5,z78]),(0,[z757,z0,z1,z3,z5,z6]),(0,[z326,z0,z1,z3,z4,z23])],[(0,[z0,z1,z3,z758,z5,z6]),(0,[z0,z1,z3,z759,z5,z6]),(0,[z1,z3,z4,z5,z760,z6]),(0,[z0,z1,z3,z761,z5,z6])],[(0,[z1,z3,z4,z153,z747,z6])],[(0,[z0,z1,z3,z4,z762,z6]),(0,[z0,z1,z3,z748,z5,z6]),(0,[z0,z1,z3,z22,z4,z206])],[(0,[z0,z1,z3,z214,z5,z6])],[(0,[z0,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z763,z5,z6]),(0,[z0,z764,z3,z4,z5,z6]),(0,[z406,z0,z224,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z765]),(0,[z0,z1,z3,z4,z5,z766]),(0,[z0,z317,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z767]),(0,[z0,z1,z3,z4,z768,z6]),(0,[z0,z1,z3,z4,z5,z550]),(0,[z0,z1,z3,z57,z81,z437]),(0,[z0,z1,z3,z44,z5,z723])]],
   [[(0,[z0,z1,z4,z769,z5,z6]),(0,[z225,z1,z71,z4,z5,z6]),(0,[z770,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z771]),(0,[z0,z1,z3,z4,z772,z6])],[(0,[z0,z1,z3,z4,z5,z773]),(0,[z9,z0,z213,z1,z3,z6]),(0,[z0,z1,z3,z774,z4,z5]),(0,[z36,z0,z1,z3,z5,z723])],[(0,[z0,z1,z3,z4,z5,z775]),(0,[z28,z1,z3,z4,z5,z160]),(0,[z0,z1,z3,z776,z4,z6]),(0,[z777,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z312,z5,z154]),(0,[z0,z1,z3,z778,z4,z6]),(0,[z0,z1,z3,z5,z723,z37])],[(0,[z1,z69,z199,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z779]),(0,[z406,z0,z3,z4,z780,z6]),(0,[z0,z1,z3,z4,z781,z6]),(0,[z281,z0,z1,z3,z191,z4]),(0,[z0,z1,z3,z782,z4,z6]),(0,[z0,z1,z3,z4,z5,z783])],[(0,[z0,z1,z3,z4,z138,z472]),(0,[z0,z1,z4,z5,z784,z6])],[(0,[z103,z69,z3,z4,z5,z241]),(0,[z0,z1,z3,z4,z5,z785]),(0,[z0,z162,z1,z3,z30,z5])],[(0,[z0,z1,z3,z786,z4,z5]),(0,[z0,z1,z3,z268,z4,z6]),(0,[z0,z1,z4,z787,z254,z6]),(0,[z0,z1,z3,z44,z4,z501])],[(0,[z496,z0,z3,z4,z92,z6])]],
   [[(0,[z31,z0,z1,z3,z204,z6]),(0,[z0,z1,z3,z4,z788,z6]),(0,[z293,z0,z1,z3,z164,z5])],[(0,[z0,z1,z3,z140,z110,z6]),(0,[z103,z68,z69,z4,z5,z6]),(0,[z406,z0,z205,z4,z5,z6]),(0,[z0,z1,z3,z57,z695,z6]),(0,[z0,z1,z3,z81,z62,z6]),(0,[z0,z1,z14,z5,z569,z6]),(0,[z789,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z790,z5,z6]),(0,[z0,z1,z3,z4,z139,z791])],[(0,[z0,z1,z3,z5,z6,z792]),(0,[z0,z1,z3,z4,z5,z793])],[(0,[z9,z1,z3,z10,z5,z6]),(0,[z285,z581,z1,z3,z5,z6]),(0,[z173,z1,z3,z214,z64,z6]),(0,[z0,z3,z47,z748,z5,z6]),(0,[z0,z1,z3,z57,z6,z609])],[(0,[z0,z1,z59,z4,z145,z6]),(0,[z0,z1,z3,z4,z794,z6]),(0,[z0,z1,z3,z795,z4,z6]),(0,[z281,z1,z3,z4,z497,z6]),(0,[z31,z0,z1,z3,z5,z23]),(0,[z0,z1,z375,z3,z47,z6]),(1,[z0,z1,z4,z787,z6])],[(0,[z0,z1,z3,z4,z5,z796]),(0,[z9,z0,z1,z3,z101,z6]),(0,[z0,z535,z3,z47,z5,z6]),(0,[z173,z0,z1,z3,z114,z6]),(0,[z281,z0,z1,z3,z114,z6])],[(0,[z797,z0,z1,z3,z5,z6])],[(0,[z0,z1,z59,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z798]),(0,[z0,z1,z3,z799,z4,z6]),(0,[z36,z0,z1,z3,z5,z677]),(0,[z0,z1,z3,z359,z5,z37])]],
   [[(0,[z0,z1,z800,z4,z5,z6])],[(0,[z0,z1,z3,z45,z5,z215]),(0,[z12,z0,z205,z4,z13,z6]),(0,[z0,z1,z3,z353,z5,z132]),(0,[z73,z0,z3,z4,z92,z74]),(0,[z0,z1,z3,z57,z636,z6])],[(0,[z0,z1,z3,z67,z5,z6]),(0,[z0,z1,z3,z4,z801,z6]),(0,[z0,z1,z3,z22,z4,z277]),(0,[z0,z1,z3,z4,z58,z550]),(0,[z0,z1,z3,z4,z6,z802]),(0,[z0,z1,z3,z803,z5,z6]),(0,[z0,z1,z3,z4,z5,z804])],[(0,[z73,z0,z3,z85,z92,z6]),(0,[z80,z366,z0,z1,z3,z6]),(0,[z0,z1,z3,z114,z138,z6])],[(0,[z0,z1,z743,z4,z5,z6]),(0,[z0,z1,z3,z805,z4,z5]),(0,[z9,z1,z3,z638,z5,z6])],[(0,[z0,z1,z3,z4,z806,z6]),(0,[z0,z1,z3,z4,z5,z807]),(0,[z257,z0,z1,z3,z191,z5]),(0,[z808,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z13,z215]),(0,[z572,z0,z3,z30,z5,z6])],[(0,[z0,z1,z4,z809,z5,z6]),(0,[z0,z1,z3,z4,z5,z810]),(0,[z346,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z315,z5]),(0,[z0,z1,z3,z138,z139,z338])],[(0,[z285,z0,z1,z3,z5,z165])]],
   [[(0,[z0,z1,z3,z4,z110,z6]),(0,[z0,z1,z3,z140,z5,z223]),(0,[z0,z1,z3,z811,z4,z5]),(0,[z0,z3,z4,z92,z812,z6]),(0,[z0,z1,z3,z4,z138,z444])],[(0,[z38,z1,z3,z4,z5,z215]),(0,[z0,z1,z709,z4,z5,z6]),(0,[z326,z0,z1,z3,z5,z37])],[(0,[z0,z1,z3,z4,z5,z813]),(0,[z0,z1,z3,z44,z132,z501])],[(0,[z0,z1,z199,z4,z110,z6]),(0,[z0,z1,z3,z5,z814,z6]),(0,[z0,z1,z3,z4,z5,z815])],[(0,[z0,z1,z3,z816,z5,z6]),(0,[z0,z1,z3,z4,z5,z817]),(0,[z0,z1,z3,z4,z5,z818]),(0,[z0,z1,z3,z4,z819,z5]),(0,[z0,z1,z820,z3,z4,z5]),(0,[z49,z0,z1,z4,z5,z784]),(0,[z0,z821,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z822,z6])],[(0,[z0,z1,z3,z4,z5,z334]),(0,[z0,z1,z3,z65,z4,z139]),(0,[z823,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z824,z4,z6]),(0,[z0,z1,z3,z825,z5,z6]),(0,[z0,z1,z3,z4,z550,z23]),(0,[z0,z1,z3,z5,z165,z338])],[(0,[z31,z0,z1,z141,z3,z5]),(0,[z0,z1,z3,z4,z5,z826])],[(0,[z0,z1,z59,z67,z5,z6]),(0,[z0,z1,z3,z827,z5,z6]),(0,[z1,z3,z4,z5,z160,z828]),(0,[z0,z1,z3,z829,z5,z6]),(0,[z0,z1,z3,z47,z297,z6]),(0,[z80,z0,z1,z3,z4,z437]),(0,[z36,z464,z0,z1,z3,z5])]],
   [[(0,[z60,z3,z166,z4,z5,z6]),(0,[z1,z149,z71,z4,z5,z6]),(0,[z173,z1,z3,z4,z747,z6]),(0,[z0,z1,z3,z4,z297,z6]),(0,[z130,z0,z1,z4,z232,z6]),(0,[z0,z1,z4,z232,z787,z6]),(0,[z0,z1,z3,z22,z5,z338])],[(0,[z0,z830,z3,z4,z5,z6]),(0,[z0,z1,z3,z237,z4,z5]),(0,[z0,z303,z224,z4,z5,z6]),(0,[z12,z0,z205,z4,z97,z6]),(0,[z0,z1,z3,z831,z4,z5])],[(0,[z0,z1,z3,z4,z832,z6]),(0,[z0,z649,z3,z4,z58,z6]),(0,[z0,z1,z3,z85,z92,z6]),(0,[z0,z1,z3,z4,z5,z833])],[(0,[z0,z1,z834,z3,z4,z5]),(0,[z0,z1,z3,z835,z4,z5]),(0,[z31,z217,z1,z3,z5,z32]),(0,[z0,z1,z3,z4,z138,z139])],[(0,[z0,z1,z3,z65,z4,z78]),(0,[z0,z1,z3,z4,z836,z5]),(0,[z80,z0,z1,z3,z6,z319]),(0,[z0,z1,z3,z101,z6,z37])],[(0,[z9,z1,z3,z837,z5,z6]),(0,[z173,z1,z3,z4,z11,z64]),(0,[z0,z1,z3,z5,z160,z338]),(0,[z0,z1,z3,z4,z97,z215]),(0,[z0,z51,z3,z47,z5,z6])],[(0,[z0,z1,z3,z4,z838,z6]),(0,[z839,z0,z1,z3,z5,z6]),(0,[z840,z1,z3,z4,z5,z6]),(0,[z0,z3,z709,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z223]),(0,[z176,z1,z177,z4,z5,z324]),(0,[z0,z1,z3,z44,z659,z5]),(0,[z0,z1,z243,z3,z30,z5]),(0,[z0,z17,z3,z47,z5,z6]),(0,[z0,z1,z3,z5,z6,z841]),(0,[z80,z0,z1,z3,z138,z37])]],
   [[(0,[z12,z33,z205,z4,z5,z6]),(0,[z0,z1,z3,z44,z5,z609])],[(0,[z842,z0,z1,z3,z4,z6])],[(0,[z0,z1,z199,z4,z5,z223]),(0,[z0,z1,z3,z4,z843,z5]),(0,[z217,z1,z3,z4,z204,z32]),(0,[z0,z3,z4,z748,z5,z6]),(0,[z36,z0,z1,z3,z5,z37])],[(0,[z406,z70,z71,z4,z5,z6]),(0,[z0,z1,z3,z844,z5,z6]),(0,[z845,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z846,z5,z6]),(0,[z0,z1,z3,z164,z4,z5])],[(0,[z0,z1,z3,z4,z5,z847]),(0,[z0,z1,z3,z4,z5,z848]),(0,[z217,z0,z1,z3,z65,z4]),(0,[z0,z1,z3,z849,z5,z6]),(0,[z850,z0,z1,z3,z5,z6])],[(0,[z0,z1,z68,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z851]),(0,[z0,z1,z3,z4,z852,z6]),(0,[z0,z1,z3,z538,z5,z215])],[(0,[z0,z1,z3,z4,z110,z241]),(0,[z0,z1,z3,z4,z5,z853]),(0,[z0,z854,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z855,z6])],[(0,[z0,z1,z3,z4,z5,z856]),(0,[z0,z1,z3,z4,z857,z6]),(0,[z0,z162,z1,z3,z47,z5]),(0,[z0,z1,z545,z15,z5,z6]),(0,[z0,z1,z3,z114,z58,z6]),(0,[z130,z0,z1,z4,z542,z6]),(0,[z0,z1,z3,z4,z138,z501])]],
   [[(0,[z0,z1,z858,z4,z5,z6]),(0,[z73,z0,z3,z4,z92,z6])],[(0,[z0,z1,z3,z859,z5,z6]),(0,[z860,z0,z1,z3,z5,z6]),(0,[z31,z0,z1,z3,z5,z334]),(0,[z0,z1,z3,z4,z5,z861]),(0,[z221,z0,z1,z4,z5,z50]),(0,[z0,z1,z3,z862,z4,z5])],[(0,[z103,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z863,z6]),(0,[z0,z1,z3,z4,z864,z6]),(0,[z0,z1,z3,z4,z11,z5]),(0,[z0,z1,z3,z865,z4,z5]),(0,[z0,z1,z3,z4,z866,z6])],[(0,[z0,z1,z867,z4,z5,z6]),(0,[z0,z438,z224,z4,z5,z6]),(0,[z173,z280,z1,z3,z4,z6]),(0,[z0,z295,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z868])],[(0,[z0,z709,z205,z4,z5,z6])],[(0,[z0,z1,z869,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z6])],[(0,[z0,z1,z3,z4,z870,z6]),(0,[z0,z1,z3,z4,z5,z871]),(0,[z329,z1,z3,z4,z64,z6]),(0,[z0,z1,z3,z4,z5,z872]),(0,[z0,z1,z3,z4,z873,z6])],[(0,[z440,z1,z71,z4,z5,z6]),(0,[z0,z1,z3,z837,z5,z6]),(0,[z0,z1,z3,z4,z204,z6]),(0,[z0,z1,z3,z4,z874,z6]),(0,[z0,z1,z14,z375,z3,z6])]],
   [[(1,[z0,z3,z4,z812,z6]),(0,[z875,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z876]),(0,[z0,z1,z3,z4,z877,z6]),(0,[z0,z1,z3,z45,z5,z77]),(0,[z0,z1,z3,z878,z5,z6])],[(0,[z0,z1,z3,z879,z5,z6]),(0,[z313,z1,z3,z118,z5,z6]),(0,[z217,z581,z1,z3,z4,z5]),(0,[z0,z3,z748,z30,z5,z6]),(0,[z293,z0,z1,z3,z315,z5])],[(0,[z0,z1,z3,z4,z880,z6]),(0,[z0,z1,z3,z4,z5,z881]),(0,[z406,z69,z3,z4,z5,z6]),(0,[z0,z213,z162,z1,z3,z4]),(0,[z653,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z215]),(0,[z0,z1,z3,z882,z4,z5]),(0,[z80,z0,z1,z327,z3,z6])],[(0,[z60,z407,z3,z4,z5,z6]),(0,[z0,z1,z3,z65,z83,z6]),(0,[z0,z1,z3,z883,z5,z6])],[(0,[z0,z1,z243,z3,z355,z4]),(0,[z0,z1,z3,z884,z5,z6]),(0,[z0,z1,z3,z114,z138,z139])],[(0,[z285,z1,z3,z118,z5,z398]),(0,[z102,z1,z3,z4,z5,z160]),(0,[z80,z0,z1,z3,z5,z127])],[(0,[z103,z69,z59,z4,z5,z6]),(0,[z0,z1,z3,z885,z5,z6]),(0,[z406,z0,z3,z886,z5,z6]),(0,[z680,z0,z3,z4,z5,z78]),(0,[z0,z107,z3,z47,z611,z6]),(0,[z0,z1,z3,z887,z4,z6])]],
   [[(0,[z717,z69,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z139,z277]),(0,[z257,z173,z0,z1,z3,z6]),(1,[z1,z3,z4,z5,z828]),(0,[z31,z0,z1,z3,z5,z139]),(0,[z0,z3,z4,z5,z736,z6])],[(0,[z0,z1,z3,z4,z5,z888]),(0,[z0,z1,z4,z5,z889,z6]),(0,[z1,z3,z743,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z890]),(0,[z0,z1,z3,z4,z891,z6]),(0,[z1,z3,z4,z837,z5,z6]),(0,[z173,z1,z3,z191,z4,z64]),(0,[z80,z0,z1,z3,z386,z6])],[(0,[z103,z69,z3,z67,z5,z6]),(0,[z0,z1,z3,z892,z4,z6]),(0,[z0,z1,z893,z4,z5,z6]),(0,[z464,z1,z3,z4,z5,z32]),(0,[z894,z1,z3,z4,z5,z6]),(0,[z0,z304,z3,z4,z5,z154])],[(0,[z0,z213,z1,z3,z237,z4])],[(0,[z70,z1,z743,z4,z5,z6]),(0,[z0,z1,z3,z81,z8,z6]),(0,[z895,z0,z1,z3,z4,z5]),(0,[z33,z1,z3,z4,z5,z215]),(0,[z896,z1,z3,z4,z5,z6])],[(0,[z12,z0,z199,z4,z5,z6]),(0,[z897,z1,z3,z4,z5,z6]),(0,[z0,z1,z898,z3,z4,z5])],[(0,[z0,z3,z4,z899,z5,z6]),(0,[z0,z1,z3,z191,z214,z5]),(0,[z0,z1,z3,z4,z5,z900])],[(0,[z0,z1,z3,z901,z5,z6]),(0,[z0,z1,z3,z902,z4,z5]),(0,[z31,z0,z1,z3,z5,z78]),(0,[z343,z0,z1,z3,z22,z4])]],
   [[(0,[z217,z1,z3,z5,z83,z32]),(0,[z0,z1,z3,z4,z297,z108]),(0,[z0,z1,z3,z4,z138,z565])],[(0,[z903,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z904]),(0,[z0,z1,z3,z4,z905,z6]),(0,[z0,z1,z3,z135,z5,z278]),(0,[z0,z1,z3,z4,z5,z437])],[(0,[z0,z1,z3,z906,z5,z6]),(0,[z80,z0,z1,z3,z907,z6]),(0,[z80,z0,z1,z3,z410,z6])],[(0,[z0,z1,z3,z4,z908,z6]),(0,[z80,z0,z1,z3,z412,z6])],[(0,[z0,z1,z909,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z910]),(0,[z608,z1,z3,z4,z153,z6]),(0,[z0,z1,z3,z4,z911,z6])],[(0,[z343,z1,z3,z4,z5,z32]),(0,[z0,z1,z3,z4,z5,z912]),(0,[z0,z1,z3,z57,z4,z437])],[(0,[z0,z1,z3,z4,z913,z6]),(0,[z0,z1,z914,z4,z5,z6]),(0,[z406,z176,z0,z4,z5,z6]),(0,[z0,z1,z3,z191,z4,z5]),(0,[z0,z1,z3,z30,z5,z165]),(0,[z0,z1,z141,z4,z5,z784])],[(0,[z0,z1,z3,z4,z138,z462]),(0,[z0,z1,z3,z4,z288,z139]),(0,[z0,z1,z3,z22,z4,z433])]],
   [[(0,[z0,z1,z3,z4,z5,z915]),(0,[z916,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z784])],[(0,[z246,z0,z1,z4,z5,z6]),(0,[z406,z0,z3,z4,z917,z6]),(0,[z918,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z919,z5,z6]),(0,[z0,z1,z3,z4,z5,z920]),(0,[z0,z1,z3,z47,z5,z165]),(0,[z0,z1,z3,z4,z5,z921]),(0,[z293,z0,z1,z131,z254,z6]),(0,[z922,z0,z1,z3,z4,z5])],[(0,[z0,z1,z3,z67,z145,z6]),(0,[z406,z70,z0,z4,z5,z6]),(0,[z923,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z314,z355,z4]),(0,[z0,z1,z3,z4,z5,z165])],[(0,[z0,z1,z3,z924,z5,z6]),(0,[z0,z1,z3,z4,z925,z6])],[(0,[z0,z1,z3,z926,z4,z6]),(0,[z0,z1,z3,z927,z4,z6]),(0,[z0,z162,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z139,z117]),(0,[z0,z1,z3,z65,z4,z37]),(0,[z0,z1,z3,z4,z5,z928]),(0,[z130,z0,z1,z4,z787,z6])],[(0,[z0,z1,z3,z5,z83,z6]),(0,[z0,z1,z3,z538,z5,z77]),(0,[z0,z1,z3,z4,z5,z929]),(0,[z0,z107,z3,z47,z5,z108]),(0,[z0,z1,z3,z5,z6,z930])],[(0,[z931,z0,z1,z3,z4,z5]),(0,[z0,z213,z1,z3,z47,z6]),(0,[z31,z0,z1,z3,z5,z154]),(0,[z0,z1,z3,z932,z4,z5]),(0,[z0,z1,z3,z4,z380,z139])],[(0,[z0,z1,z933,z4,z5,z6]),(0,[z0,z1,z3,z4,z934,z6]),(0,[z0,z1,z3,z4,z5,z935]),(0,[z0,z1,z3,z4,z936,z5]),(0,[z0,z1,z3,z4,z937,z5]),(0,[z0,z1,z3,z4,z5,z278])]],
   [[(0,[z0,z1,z938,z3,z4,z6]),(0,[z0,z1,z3,z939,z5,z6]),(0,[z0,z1,z3,z4,z5,z940]),(0,[z0,z1,z3,z4,z791,z23])],[(0,[z0,z1,z3,z4,z5,z941]),(0,[z0,z1,z3,z4,z611,z436]),(1,[z0,z3,z4,z5,z736]),(0,[z0,z1,z3,z4,z5,z942])],[(0,[z406,z0,z199,z4,z5,z6]),(0,[z943,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z44,z101,z132])],[(0,[z0,z1,z4,z5,z944,z6])],[(0,[z0,z1,z3,z4,z945,z6]),(0,[z257,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z81,z5,z334]),(0,[z9,z0,z162,z1,z3,z5]),(0,[z0,z1,z3,z946,z5,z6]),(0,[z0,z1,z3,z4,z138,z791])],[(0,[z0,z1,z3,z4,z947,z5]),(0,[z0,z1,z3,z4,z5,z324]),(0,[z0,z1,z3,z4,z5,z948]),(0,[z1,z3,z4,z5,z828,z32]),(0,[z0,z1,z3,z4,z550,z501]),(0,[z0,z1,z3,z949,z5,z6])],[(0,[z0,z1,z3,z950,z5,z6]),(0,[z1,z3,z4,z747,z64,z6])],[(0,[z0,z1,z3,z4,z5,z951]),(0,[z0,z1,z3,z4,z952,z6]),(0,[z0,z1,z3,z30,z297,z6]),(0,[z953,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z828]),(0,[z0,z564,z3,z4,z58,z6]),(0,[z49,z0,z1,z4,z5,z50])],[(0,[z0,z1,z3,z754,z5,z6]),(0,[z0,z1,z3,z5,z6,z338])],[(0,[z0,z1,z3,z4,z954,z6]),(0,[z0,z1,z3,z955,z4,z5])],[(0,[z0,z1,z3,z4,z5,z956]),(0,[z957,z0,z3,z4,z5,z6]),(0,[z281,z1,z3,z4,z747,z6]),(0,[z0,z1,z3,z4,z5,z77]),(0,[z0,z1,z3,z4,z958,z6]),(0,[z0,z227,z3,z4,z812,z6]),(0,[z293,z0,z1,z3,z92,z6])],[(0,[z0,z1,z3,z4,z5,z959]),(0,[z0,z1,z3,z315,z629,z5])],[(0,[z0,z1,z3,z960,z5,z6]),(0,[z0,z1,z961,z3,z4,z6]),(0,[z73,z0,z3,z135,z92,z6]),(0,[z0,z1,z3,z164,z4,z92]),(0,[z80,z0,z1,z3,z171,z6]),(0,[z0,z1,z3,z4,z5,z791])],[(0,[z0,z1,z3,z962,z5,z6]),(0,[z0,z1,z3,z44,z485,z5])],[(0,[z0,z1,z3,z4,z145,z223]),(0,[z272,z36,z0,z1,z3,z5]),(0,[z0,z1,z3,z307,z81,z6]),(0,[z0,z1,z3,z4,z359,z139])]],
   [[(0,[z0,z1,z59,z4,z110,z6]),(0,[z0,z1,z3,z4,z5,z963]),(0,[z0,z1,z3,z4,z5,z964])],[(0,[z0,z965,z3,z4,z5,z6])],[(0,[z0,z966,z3,z4,z5,z6]),(0,[z285,z1,z3,z268,z118,z6]),(0,[z0,z1,z3,z4,z58,z278]),(0,[z0,z1,z3,z57,z81,z127])],[(0,[z0,z1,z3,z67,z110,z6]),(0,[z0,z1,z3,z4,z780,z6]),(0,[z0,z1,z3,z4,z5,z967]),(0,[z0,z1,z3,z4,z5,z247]),(0,[z0,z1,z3,z22,z4,z501])],[(0,[z0,z1,z3,z968,z5,z6]),(0,[z406,z0,z3,z4,z5,z969]),(0,[z0,z1,z3,z11,z214,z5]),(0,[z33,z1,z3,z4,z5,z77]),(0,[z0,z1,z3,z4,z6,z970]),(0,[z0,z107,z3,z748,z5,z6]),(0,[z104,z0,z3,z4,z5,z78]),(1,[z0,z1,z3,z4,z791])],[(0,[z60,z61,z3,z4,z5,z6]),(0,[z0,z971,z3,z4,z5,z6]),(0,[z0,z972,z3,z4,z5,z6]),(0,[z49,z0,z1,z4,z299,z5])],[(0,[z257,z173,z1,z3,z64,z6]),(0,[z0,z1,z3,z22,z4,z23])],[(0,[z0,z1,z3,z5,z973,z6]),(0,[z257,z0,z1,z3,z58,z6])]],
   [[(0,[z0,z1,z199,z140,z5,z6]),(0,[z0,z1,z3,z974,z5,z6]),(0,[z0,z3,z4,z975,z5,z6]),(0,[z176,z1,z2,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z976]),(0,[z31,z217,z0,z1,z3,z5]),(0,[z33,z1,z224,z4,z5,z6]),(0,[z12,z0,z205,z4,z5,z215]),(0,[z0,z107,z3,z47,z5,z6]),(1,[z0,z1,z746,z5,z6])],[(0,[z1,z3,z4,z977,z5,z6])],[(0,[z103,z69,z3,z4,z145,z6]),(0,[z80,z0,z1,z3,z4,z277]),(0,[z0,z1,z3,z5,z32,z338]),(0,[z80,z0,z1,z3,z510,z6]),(0,[z49,z0,z1,z4,z646,z5]),(0,[z0,z1,z3,z57,z81,z550])],[(0,[z0,z1,z3,z4,z5,z978]),(0,[z0,z1,z3,z4,z5,z979]),(0,[z406,z0,z3,z4,z5,z980]),(0,[z0,z1,z3,z22,z4,z614])],[(0,[z246,z60,z0,z4,z5,z6]),(0,[z0,z1,z3,z164,z4,z58]),(0,[z0,z1,z375,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z981]),(0,[z0,z1,z3,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z982]),(0,[z0,z1,z3,z57,z81,z6])],[(0,[z0,z1,z3,z5,z6,z983]),(0,[z217,z1,z3,z532,z4,z5]),(0,[z0,z1,z3,z65,z4,z154]),(0,[z356,z0,z3,z30,z5,z6]),(0,[z0,z1,z3,z4,z984,z6])],[(0,[z0,z1,z59,z4,z5,z223]),(0,[z0,z1,z985,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z986]),(0,[z285,z0,z213,z1,z3,z6]),(0,[z28,z0,z1,z3,z65,z4]),(0,[z31,z0,z1,z3,z5,z37]),(0,[z0,z1,z3,z4,z112,z6]),(0,[z0,z1,z3,z987,z5,z6])]],
   [[(0,[z173,z1,z3,z4,z64,z247]),(0,[z0,z1,z3,z988,z5,z6]),(0,[z0,z1,z3,z4,z5,z989]),(0,[z0,z1,z3,z4,z76,z23]),(0,[z0,z1,z3,z44,z5,z338])],[(0,[z0,z1,z990,z4,z5,z6]),(0,[z991,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z78,z736]),(0,[z0,z1,z141,z4,z5,z79])],[(0,[z0,z1,z3,z67,z5,z223]),(0,[z0,z1,z3,z4,z5,z992]),(0,[z0,z993,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z994,z6]),(0,[z49,z0,z1,z3,z65,z4]),(0,[z33,z1,z205,z4,z5,z6]),(0,[z995,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z746,z5,z6]),(0,[z36,z0,z1,z3,z5,z338])],[(0,[z0,z1,z3,z4,z996,z6]),(0,[z0,z213,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z997,z6]),(0,[z0,z1,z14,z15,z5,z6]),(0,[z0,z1,z375,z3,z314,z4]),(1,[z0,z1,z3,z5,z723])],[(0,[z176,z1,z294,z4,z5,z6]),(0,[z70,z33,z1,z4,z5,z6]),(0,[z36,z0,z1,z3,z657,z5])],[(0,[z103,z246,z0,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z398]),(0,[z0,z1,z3,z4,z5,z998]),(0,[z0,z1,z3,z4,z5,z999]),(0,[z0,z1,z3,z4,z5,z723])],[(0,[z0,z1,z3,z5,z132,z334]),(0,[z28,z1,z3,z4,z668,z5])],[(0,[z0,z1,z3,z4,z5,z1000]),(0,[z0,z1,z3,z45,z97,z6]),(0,[z0,z1,z3,z312,z5,z6]),(0,[z0,z1,z3,z4,z92,z550])]],
   [[(0,[z0,z1,z3,z4,z110,z223]),(0,[z285,z1,z3,z118,z5,z6]),(0,[z0,z1,z3,z4,z13,z77])],[(0,[z0,z1,z1001,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1002]),(0,[z0,z1,z3,z1003,z5,z6]),(0,[z390,z0,z1,z417,z5,z6]),(0,[z80,z0,z1,z3,z44,z23])],[(0,[z60,z224,z71,z4,z5,z6]),(0,[z0,z303,z507,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1004]),(0,[z0,z1,z3,z1005,z5,z6])],[(0,[z0,z1,z3,z140,z5,z241]),(0,[z0,z1006,z3,z4,z5,z6]),(0,[z285,z0,z1,z3,z101,z6]),(0,[z0,z1,z3,z1007,z4,z5]),(0,[z0,z1,z3,z85,z5,z74]),(0,[z0,z1,z3,z44,z5,z208]),(0,[z0,z1,z3,z44,z101,z6])],[(0,[z0,z1,z3,z4,z6,z1008]),(0,[z374,z1,z3,z4,z5,z160]),(0,[z38,z1,z3,z4,z5,z77]),(0,[z0,z1,z14,z746,z5,z6]),(0,[z1009,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z382,z5,z132])],[(0,[z246,z33,z1,z4,z5,z6]),(0,[z285,z1,z3,z237,z118,z5])],[(0,[z0,z1,z3,z1010,z5,z6]),(0,[z12,z176,z60,z4,z5,z6]),(0,[z0,z1,z3,z4,z1011,z6]),(0,[z0,z1,z3,z30,z5,z436]),(0,[z0,z1,z3,z4,z5,z1012]),(0,[z73,z0,z3,z4,z812,z6]),(0,[z0,z1,z3,z4,z5,z1013]),(0,[z0,z1,z1014,z4,z5,z6])],[(0,[z0,z1,z1015,z4,z5,z6]),(0,[z0,z1,z3,z57,z661,z6]),(0,[z0,z1,z3,z81,z6,z444])]],
   [[(0,[z1016,z0,z3,z4,z5,z6]),(0,[z618,z1,z3,z10,z5,z6]),(0,[z0,z1,z3,z191,z4,z92]),(0,[z0,z1,z3,z1017,z5,z6]),(0,[z557,z0,z1,z48,z5,z6])],[(0,[z0,z224,z199,z4,z5,z6]),(0,[z12,z440,z0,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1018]),(0,[z0,z1,z3,z47,z5,z436]),(0,[z0,z1,z3,z4,z1019,z6]),(1,[z0,z1,z4,z5,z784])],[(0,[z0,z1,z3,z1020,z5,z6]),(0,[z0,z1,z3,z1021,z5,z6]),(0,[z0,z1,z3,z4,z5,z436])],[(0,[z60,z1,z199,z4,z5,z6]),(0,[z0,z1,z3,z1022,z5,z6]),(0,[z103,z69,z3,z4,z110,z6]),(0,[z406,z33,z3,z4,z5,z6]),(0,[z0,z1,z3,z538,z13,z6]),(0,[z0,z249,z3,z47,z5,z6]),(0,[z0,z578,z3,z4,z5,z154]),(0,[z0,z1,z3,z4,z5,z1023])],[(0,[z257,z0,z1,z3,z11,z5]),(0,[z1024,z0,z1,z3,z4,z5]),(0,[z370,z1,z3,z4,z5,z160]),(0,[z36,z0,z1,z3,z5,z184])],[(0,[z0,z1,z3,z4,z1025,z6]),(0,[z0,z1,z3,z65,z4,z277]),(0,[z0,z1,z3,z4,z5,z1026]),(0,[z390,z0,z1,z375,z3,z6])],[(0,[z0,z1,z3,z1027,z4,z6]),(0,[z0,z1,z4,z5,z50,z784]),(0,[z80,z0,z1,z3,z583,z6])],[(0,[z1,z3,z4,z5,z828,z6]),(0,[z38,z1,z3,z538,z5,z6]),(0,[z390,z0,z1,z314,z48,z5]),(0,[z80,z0,z1,z3,z16,z6])]],
   [[(0,[z0,z1,z1028,z4,z5,z6]),(0,[z0,z1,z3,z5,z132,z482]),(0,[z9,z1,z3,z5,z499,z6]),(0,[z0,z1,z3,z4,z97,z77])],[(0,[z0,z1,z3,z4,z1029,z6])],[(0,[z0,z1,z3,z4,z5,z1030]),(0,[z173,z0,z1,z3,z4,z550]),(0,[z281,z0,z1,z3,z4,z550]),(0,[z0,z1,z3,z135,z5,z74]),(0,[z0,z87,z3,z4,z5,z154]),(0,[z0,z1,z3,z1031,z5,z6])],[],[(0,[z0,z1,z3,z1032,z5,z6]),(0,[z0,z1,z3,z4,z1033,z5]),(0,[z0,z1,z243,z3,z47,z5]),(0,[z0,z3,z4,z812,z5,z6]),(0,[z0,z1,z3,z4,z5,z1034]),(0,[z0,z1,z3,z4,z5,z1035]),(0,[z0,z1,z3,z4,z5,z1036])],[(0,[z0,z1,z199,z4,z5,z241]),(0,[z0,z1,z3,z4,z5,z1037]),(0,[z0,z1,z3,z45,z5,z6]),(0,[z0,z1,z3,z4,z812,z6])],[(0,[z0,z3,z4,z1038,z5,z6]),(0,[z0,z1,z3,z4,z5,z1039]),(0,[z0,z1,z131,z4,z787,z6])],[(0,[z0,z1,z3,z1040,z5,z6]),(0,[z0,z1,z3,z191,z4,z58]),(0,[z31,z0,z1,z3,z65,z6]),(0,[z0,z1,z3,z4,z1041,z6]),(0,[z0,z1,z3,z4,z5,z1042])]],
   [[(0,[z0,z1043,z1,z3,z4,z6]),(0,[z12,z0,z205,z4,z5,z77]),(0,[z0,z1,z3,z22,z4,z791])],[(0,[z0,z1,z1044,z4,z5,z6])],[(0,[z406,z0,z3,z4,z5,z6]),(0,[z103,z69,z3,z4,z5,z223]),(0,[z0,z1,z3,z4,z5,z1045]),(0,[z0,z1,z3,z1046,z5,z6]),(0,[z0,z1,z4,z746,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1047]),(0,[z1,z177,z743,z4,z5,z6]),(0,[z285,z1,z3,z837,z5,z6]),(0,[z28,z1,z3,z4,z264,z5]),(0,[z0,z1,z3,z538,z97,z6]),(0,[z1048,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z1049,z5,z6]),(0,[z0,z1,z3,z1050,z5,z6]),(0,[z0,z1,z3,z5,z132,z723])],[(0,[z0,z1,z3,z1051,z4,z6]),(0,[z285,z213,z1,z3,z118,z6]),(0,[z0,z1,z3,z4,z1052,z6]),(0,[z0,z1,z3,z4,z5,z277]),(0,[z12,z0,z709,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1053]),(0,[z0,z1,z3,z114,z92,z6]),(0,[z0,z17,z3,z4,z5,z78]),(0,[z0,z1,z3,z4,z1054,z6])],[(0,[z0,z1,z3,z237,z268,z4]),(0,[z0,z1,z3,z1055,z4,z5]),(0,[z0,z1,z3,z1056,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1057]),(0,[z281,z1,z3,z4,z267,z6]),(0,[z33,z1,z3,z45,z5,z6]),(0,[z0,z1,z3,z4,z5,z1058]),(0,[z0,z1,z3,z44,z5,z132])],[(0,[z395,z0,z1,z3,z22,z4]),(0,[z0,z1,z3,z4,z5,z1059]),(0,[z104,z0,z3,z4,z193,z78])]],
   [[(0,[z0,z1,z3,z57,z4,z277]),(1,[z0,z3,z748,z5,z6]),(0,[z0,z227,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z5,z74])],[(0,[z0,z1,z1060,z4,z5,z6]),(0,[z0,z1,z3,z1061,z4,z5]),(0,[z9,z0,z1,z3,z5,z165]),(0,[z80,z0,z1,z3,z622,z6]),(0,[z0,z1,z3,z44,z5,z514])],[(0,[z0,z1,z3,z1062,z5,z6]),(0,[z0,z1,z3,z4,z5,z1063]),(0,[z0,z1,z3,z85,z5,z6]),(0,[z0,z1,z3,z4,z6,z501])],[(0,[z217,z1,z3,z65,z4,z32]),(0,[z0,z1,z3,z4,z1064,z6]),(0,[z0,z1,z3,z1065,z5,z6])],[(0,[z0,z3,z388,z4,z5,z6]),(0,[z0,z1066,z1,z3,z4,z5]),(0,[z644,z0,z3,z4,z5,z78]),(0,[z0,z1,z15,z746,z5,z6]),(0,[z0,z1,z3,z4,z5,z1067])],[(0,[z0,z1,z3,z1068,z5,z6]),(1,[z717,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1069]),(0,[z0,z1,z3,z4,z1070,z6]),(0,[z0,z1,z3,z1071,z4,z5]),(0,[z0,z1,z3,z1072,z5,z6])],[(0,[z518,z80,z0,z1,z3,z6]),(0,[z0,z1073,z3,z4,z5,z6])],[(0,[z0,z1,z3,z886,z5,z6]),(0,[z0,z3,z4,z5,z1074,z6]),(0,[z0,z1,z3,z4,z1075,z6]),(0,[z0,z1,z3,z4,z1076,z6]),(0,[z0,z3,z4,z812,z58,z6]),(0,[z390,z0,z1,z355,z48,z6])]],
   [[(0,[z0,z1,z3,z1077,z4,z5]),(0,[z285,z280,z1,z3,z5,z6]),(0,[z0,z1,z3,z105,z193,z6]),(0,[z0,z1,z3,z4,z112,z78])],[(0,[z0,z1,z3,z4,z5,z1078]),(0,[z0,z1,z3,z4,z1079,z5]),(0,[z173,z1,z3,z4,z64,z277]),(0,[z0,z1,z141,z4,z5,z509]),(0,[z0,z1,z3,z4,z160,z501])],[(0,[z12,z63,z0,z4,z5,z6]),(0,[z0,z1,z3,z1080,z4,z5]),(0,[z0,z1,z3,z1081,z4,z6]),(0,[z0,z1,z3,z4,z5,z1082]),(0,[z0,z1,z131,z417,z4,z6]),(0,[z1083,z0,z1,z3,z4,z6])],[(0,[z332,z1,z177,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z1084])],[(0,[z0,z1,z141,z3,z65,z4]),(0,[z0,z1,z266,z4,z5,z79]),(0,[z0,z1,z3,z5,z6,z1085]),(0,[z293,z0,z1,z131,z3,z6]),(0,[z0,z1,z3,z382,z4,z23])],[(0,[z0,z1,z3,z140,z145,z6]),(0,[z0,z1,z3,z1086,z5,z6])],[(0,[z61,z717,z3,z4,z5,z6]),(0,[z390,z0,z1,z48,z5,z6]),(0,[z130,z293,z0,z1,z3,z6])],[(0,[z0,z1,z3,z306,z5,z132]),(0,[z0,z1,z3,z4,z5,z1087])]],
   [[(0,[z0,z1,z3,z140,z5,z6]),(0,[z0,z1,z3,z5,z1088,z6]),(0,[z0,z1,z3,z65,z4,z6]),(0,[z28,z31,z0,z1,z3,z5]),(0,[z644,z0,z3,z4,z92,z6]),(0,[z0,z1,z3,z81,z5,z127])],[(0,[z1,z3,z10,z837,z5,z6]),(0,[z0,z1,z3,z538,z5,z6])],[(0,[z439,z0,z3,z30,z5,z6]),(0,[z0,z1,z3,z45,z13,z6]),(0,[z0,z1,z3,z312,z193,z6]),(0,[z36,z0,z1,z3,z5,z480])],[(0,[z1089,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z1090,z5,z6]),(0,[z0,z1,z3,z1091,z5,z6]),(0,[z49,z31,z0,z1,z3,z5]),(0,[z0,z1,z3,z4,z32,z501]),(0,[z0,z1,z3,z693,z5,z37])],[(0,[z0,z1,z3,z4,z1092,z5]),(0,[z168,z80,z0,z1,z3,z6]),(0,[z612,z0,z1,z4,z232,z6]),(0,[z0,z1,z3,z4,z5,z127])],[(0,[z0,z1,z3,z138,z5,z338])],[(0,[z0,z1,z3,z1093,z5,z6]),(0,[z38,z1,z3,z45,z5,z6]),(0,[z0,z1,z3,z4,z611,z108]),(0,[z0,z304,z3,z4,z5,z736]),(0,[z0,z1,z3,z4,z5,z736]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z1,z131,z4,z254,z6])],[(0,[z0,z1,z3,z4,z5,z1095]),(0,[z0,z1,z3,z4,z6,z1096]),(0,[z1097,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1098])]],
   [[(0,[z285,z162,z1,z3,z118,z5])],[(0,[z70,z388,z71,z4,z5,z6]),(0,[z0,z1,z3,z4,z917,z6]),(0,[z0,z1,z3,z4,z1099,z6]),(0,[z176,z1,z177,z4,z5,z183]),(0,[z0,z1,z243,z3,z4,z5])],[(0,[z159,z0,z3,z4,z92,z6]),(0,[z33,z1,z3,z538,z5,z6]),(0,[z38,z1,z3,z4,z13,z6]),(0,[z0,z1,z3,z30,z101,z6])],[(0,[z0,z1,z3,z4,z5,z1100]),(0,[z49,z0,z1,z4,z5,z523]),(0,[z0,z1,z3,z4,z1101,z6]),(0,[z0,z1,z3,z57,z907,z6])],[(0,[z0,z1,z3,z4,z1102,z6]),(0,[z0,z1,z3,z1103,z5,z6]),(0,[z0,z1,z3,z1104,z4,z6]),(0,[z176,z1,z743,z4,z5,z6]),(1,[z0,z709,z4,z5,z6]),(0,[z0,z1,z3,z1105,z5,z6]),(0,[z0,z1,z3,z81,z907,z6])],[(0,[z0,z1,z59,z140,z5,z6]),(0,[z1,z3,z4,z747,z5,z6]),(0,[z0,z1,z3,z47,z101,z6]),(0,[z0,z1,z3,z1106,z5,z6]),(0,[z0,z1,z3,z1107,z5,z6]),(0,[z36,z0,z1,z3,z5,z506])],[(0,[z0,z1,z1108,z4,z5,z6]),(0,[z0,z1,z3,z4,z1109,z6]),(0,[z0,z1,z3,z4,z101,z6]),(1,[z0,z1,z3,z907,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z199,z4,z145,z6]),(0,[z1110,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1111]),(0,[z0,z1,z3,z1112,z5,z6]),(0,[z0,z1,z3,z114,z6,z23])]],
   [[(0,[z0,z3,z4,z1113,z5,z6]),(0,[z173,z0,z1,z3,z191,z4]),(0,[z0,z1,z3,z1114,z4,z5]),(0,[z0,z1,z3,z4,z1115,z6]),(0,[z0,z1,z4,z5,z784,z79]),(0,[z0,z1,z3,z4,z907,z6])],[(0,[z0,z1,z3,z1116,z5,z6]),(0,[z0,z1,z1117,z4,z5,z6]),(0,[z0,z1,z3,z5,z907,z6])],[(0,[z0,z1,z199,z4,z5,z6]),(0,[z0,z1,z3,z4,z1118,z6]),(0,[z60,z33,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1119,z6]),(0,[z281,z1,z3,z4,z153,z6]),(0,[z0,z1,z3,z1120,z5,z6])],[(0,[z12,z0,z149,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1121]),(0,[z396,z0,z3,z30,z5,z6]),(0,[z0,z3,z4,z5,z736,z154]),(0,[z0,z1,z3,z22,z4,z681])],[(0,[z390,z0,z1,z243,z48,z5])],[(0,[z0,z717,z3,z4,z5,z6]),(0,[z103,z33,z3,z4,z5,z6]),(0,[z0,z1,z3,z57,z81,z165]),(0,[z36,z0,z1,z3,z4,z501])],[(0,[z0,z1,z3,z4,z1122,z6]),(0,[z0,z1,z3,z5,z1123,z6]),(0,[z0,z1124,z3,z4,z5,z6]),(0,[z0,z1,z3,z1125,z5,z6]),(0,[z0,z1,z3,z1126,z5,z6])],[(0,[z0,z1,z3,z4,z1127,z6]),(0,[z0,z1,z3,z4,z5,z1128]),(0,[z0,z1,z131,z164,z4,z254])]],
   [[(0,[z33,z1,z3,z4,z5,z6]),(0,[z217,z1,z3,z4,z5,z828]),(0,[z0,z1,z3,z1129,z4,z5]),(0,[z73,z0,z3,z4,z92,z278])],[(0,[z80,z0,z1,z3,z624,z6]),(0,[z0,z1,z3,z1130,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1131]),(0,[z0,z1,z3,z1132,z5,z6]),(0,[z0,z1,z3,z65,z4,z132]),(0,[z38,z1,z3,z4,z97,z6]),(0,[z1133,z1,z3,z4,z5,z6]),(0,[z12,z0,z205,z45,z5,z6]),(0,[z0,z1,z3,z4,z5,z1134])],[(0,[z80,z0,z1,z3,z256,z6])],[(0,[z0,z1,z3,z4,z1135,z6]),(0,[z176,z1,z177,z4,z5,z6]),(0,[z0,z3,z4,z5,z1136,z6]),(0,[z173,z1,z3,z4,z64,z6]),(0,[z0,z1,z3,z22,z4,z580]),(0,[z0,z1,z3,z22,z4,z228])],[(0,[z0,z1,z3,z5,z165,z37])],[(0,[z0,z1,z3,z314,z4,z5])],[(0,[z0,z1,z3,z4,z1137,z6]),(0,[z0,z1,z3,z4,z6,z791])]],
   [[(0,[z1138,z0,z1,z3,z5,z6]),(0,[z0,z162,z1,z3,z268,z4]),(0,[z28,z1,z3,z4,z5,z828]),(0,[z0,z1,z3,z4,z5,z1139])],[(0,[z60,z717,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1140]),(0,[z0,z1,z3,z4,z5,z1141]),(0,[z0,z1,z3,z4,z611,z6]),(0,[z0,z107,z3,z47,z297,z6]),(0,[z0,z1,z1142,z4,z5,z6]),(0,[z0,z1,z3,z907,z16,z6])],[(0,[z0,z1,z199,z67,z5,z6]),(0,[z0,z1,z3,z4,z145,z241]),(0,[z285,z0,z162,z1,z3,z5]),(0,[z173,z1,z3,z532,z4,z6]),(0,[z0,z1,z3,z1143,z5,z6]),(0,[z0,z1,z4,z787,z5,z6]),(0,[z0,z1,z141,z271,z4,z5])],[(0,[z31,z0,z1,z3,z5,z6]),(0,[z0,z303,z709,z4,z5,z6]),(0,[z0,z1,z3,z4,z787,z6]),(0,[z0,z1,z3,z4,z138,z514])],[(0,[z103,z717,z3,z4,z5,z6]),(0,[z103,z246,z69,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z969]),(1,[z1,z3,z837,z5,z6]),(0,[z1,z3,z837,z118,z5,z6]),(0,[z0,z1,z3,z1144,z4,z6]),(0,[z0,z1,z3,z4,z1145,z6]),(0,[z0,z1,z3,z44,z5,z165])],[(0,[z0,z1,z3,z4,z5,z241]),(0,[z0,z1,z3,z4,z1146,z6]),(0,[z590,z1,z3,z4,z5,z160]),(0,[z1147,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1148]),(0,[z0,z1,z131,z629,z254,z6])],[(0,[z0,z1,z4,z1149,z5,z6]),(0,[z0,z1,z3,z4,z1150,z6]),(0,[z0,z1,z3,z4,z1151,z6])],[(1,[z1,z3,z4,z747,z6]),(0,[z0,z1,z3,z4,z92,z278]),(0,[z0,z1,z3,z4,z5,z1152]),(0,[z1153,z0,z1,z3,z4,z6])]],
   [[(0,[z1,z743,z71,z4,z5,z6]),(0,[z0,z1,z3,z1154,z4,z5]),(0,[z0,z1,z3,z1155,z5,z6]),(0,[z0,z1,z3,z204,z83,z6]),(0,[z1156,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1157])],[(0,[z0,z1,z3,z4,z5,z1158]),(0,[z0,z1,z3,z114,z5,z6])],[(0,[z390,z0,z1,z746,z5,z6]),(0,[z0,z1,z3,z4,z1159,z6])],[(0,[z0,z1,z1160,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z980])],[(0,[z257,z0,z1,z3,z92,z6]),(0,[z0,z1,z3,z4,z13,z6]),(0,[z1161,z1,z3,z4,z5,z6])],[],[(0,[z285,z1,z3,z118,z5,z334]),(0,[z0,z1,z3,z1162,z5,z6]),(0,[z0,z1,z3,z629,z5,z6])],[(0,[z0,z1,z3,z4,z1163,z6]),(0,[z70,z1,z71,z4,z5,z6]),(0,[z104,z0,z3,z105,z5,z78])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 540) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 540).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1076).take 46) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1122)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [540, 536, 46] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 134).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [134, 122] = true :=
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

end PEqualNP.Outside.L_meta_39015

theorem PEqualNP.Outside.L_meta_39015 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276812992 * 2 ^ 32 + 4241029312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276812992 * 2 ^ 32 + 4241029312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39015.solve