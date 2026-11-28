import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36587

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

theorem tierB {S : ℕ × List W → Bool} {J d K : ℕ} (hK : J + d = K) {L : List (ℕ × List W)} {sizes : List ℕ}
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false)
    (hw : windowsG (chunkB S d) L 0 sizes = true) : FalseAt K L := by
  subst hK
  have hP := windowsG_sound (P := fun c => optB S d c.1 c.2 = false)
    (fun X hX c hc => by have := List.all_eq_true.mp hX c hc; simpa using this) sizes 0 hw
  intro c hc
  exact optB_sound S J hS d c.1 c.2 (hP c (by simpa using hc))

theorem memS {g nb J : ℕ} {bk : List (List (List (ℕ × List W)))} (h : FalseAt J bk.flatten.flatten) :
    ∀ c, (!inB2 g nb bk c) = false → optimized J c.1 c.2 = false := by
  intro c hc
  have hin : inB2 g nb bk c = true := by simpa using hc
  exact h c (inB2_mem hin)

theorem finalF {J : ℕ} {bk : List (List (List (ℕ × List W)))} {sizes : List ℕ}
    (h : windowsF J bk.flatten 0 sizes = true) : FalseAt J bk.flatten.flatten := by
  have := falseAt_of_windowsF sizes 0 h
  simpa using this

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
  Nat.testBit (4008372906 * 2 ^ 32 + 3972587520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 7 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    7 < binaryCost gs := by
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
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 7 inputs nd (lift low run)))

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def rows : List W :=
  [(mkw 0x02cb0a16146d2c28 0x7504241554d8c6c6 0x1fff007e00fffc01 0xff463e3ffef8c7c7),
   (mkw 0x601562aac58e55aa 0x143189999816b5f0 0xe03ffffffffffffe 0x00b9c9d9991ffff8),
   (mkw 0xb540104d76249acd 0xa6c17161e1a0e8ad 0xffc0007fff00ffff 0xffc1f1e1e1e0f8ff),
   (mkw 0xd9a6bb002048e371 0xd8ee00fe017d005b 0xffffff800000ffff 0xfffe01fe01ff00ff),
   (mkw 0x1e38dc71b8f00040 0xe0defe0001eb5b00 0xffffffffffff0000 0x00fffe0001ffff00),
   (mkw 0x1000e001c0800381 0x00fbdbeaaa000000 0x0000000000000000 0x00fffffffe000000)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [12, 13]⟩], 14⟩

def z0 : W := mkw 0x02cb0a16146d2c28 0x7504241554d8c6c6 0x1fff007e00fffc01 0xff463e3ffef8c7c7

def z1 : W := mkw 0x1000e001c0800381 0x00fbdbeaaa000000 0x0000000000000000 0x00fffffffe000000

def z2 : W := mkw 0x1830d820a0c00040 0xc0de8800016b1100 0xffffffffffff0000 0x00ffc80001ffff00

def z3 : W := mkw 0x601562aac58e55aa 0x143189999816b5f0 0xe03ffffffffffffe 0x00b9c9d9991ffff8

def z4 : W := mkw 0xb540104d76249acd 0xa6c17161e1a0e8ad 0xffc0007fff00ffff 0xffc1f1e1e1e0f8ff

def z5 : W := mkw 0xd9a6bb002048e371 0xd8ee00fe017d005b 0xffffff800000ffff 0xfffe01fe01ff00ff

def z6 : W := mkw 0x1e38dc71b8f00040 0xe0defe0001eb5b00 0xffffffffffff0000 0x00b9c00001ffff00

def z7 : W := mkw 0x0a38cc3088d00000 0x401e8e00004b1300 0xe03fffffffff0000 0x00bfce00011fff00

def z8 : W := mkw 0x9f38dc71b8f08241 0xe0defe6001eb5b09 0xffffffffffffffff 0xffffffe001ffffff

def z9 : W := mkw 0x1e38dc71b8f00040 0xe0defe0001eb5b00 0xffffffffffff0000 0x00fffe0001ffff00

def z10 : W := mkw 0x2658447ddeb4188c 0x2611ff01e082fba4 0x0000007fffff0000 0x0001fe01e000ff00

def z11 : W := mkw 0x9faa9d513870a251 0xe8ce766601e94a0b 0x1fc0000000000001 0xff46362600e00007

def z12 : W := mkw 0x2040000c54241888 0x24012101c080e0a4 0xffc0007fff00ffff 0xffc1f1e1e1e0f8ff

def z13 : W := mkw 0xd9a6bb012048e371 0xd8ee52fe237d005b 0xffffff800000ffff 0xfffe37fe67ff00ff

def z14 : W := mkw 0xb749105f76259ecd 0xa7c17561f5a0eead 0xffc0007fffffffff 0xffc1ffe1ffe0ffff

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x00463e3ffe000000

def z16 : W := mkw 0xb540104d76249acd 0xa6c17161e1a0e8ad 0xffc0007fff00ffff 0xffc7ffffffe0f8ff

def z17 : W := mkw 0x0000e001c0800180 0x003bdb8aaa000000 0x0000000000000000 0x003ffe1ffe000000

def z18 : W := mkw 0x1000a00000000301 0x00ea00ea00000000 0x0000000000000000 0x00fe3ffffe000000

def z19 : W := mkw 0x20104028c4841088 0x041189018002b1a0 0xe03ffffffffffffe 0x00b9c9c1811ffff8

def z20 : W := mkw 0xd924b1002000c351 0x88ea00ea01250019 0xffc0ff800000ffff 0xfff801e001e700ff

def z21 : W := mkw 0x7014e0a9c1825383 0x00fbdbeaaa063130 0xe000ff81ff0003fe 0x00ffffffff073838

def z22 : W := mkw 0x02cb0a16146d2c28 0x7504241554d8c6c6 0x1fff007e00fffc01 0xff00000000f8c7c7

def z23 : W := mkw 0x6005228a450e55aa 0x142101999814a4f0 0x000000000000fffe 0x000001d9980000f8

def z24 : W := mkw 0x1010c02180800000 0x00dada0000021100 0xe03fffffffff0000 0x00fffe00011fff00

def z25 : W := mkw 0x0010402080800000 0x0010880000021100 0xe03fffffffff0000 0x00b9c800011fff00

def z26 : W := mkw 0x9540104532208a45 0xa2c0706061a0480d 0x1fc0000000000001 0xff40302060e00007

def z27 : W := mkw 0x601562aac58e55aa 0x143189999816b5f0 0xe03ffffffffffffe 0x00ffffffff1ffff8

def z28 : W := mkw 0xd9a6bb002048e371 0xd8ee00fe017d005b 0xffffff800000ffff 0xffb801c001ff00ff

def z29 : W := mkw 0x1efadc75b8f12840 0xe1defe0445eb5b06 0xffffffffffff0001 0xfffffe2667ffff07

def z30 : W := mkw 0x1010e021c0800381 0x00fbdbeaaa021100 0xe03fffffffff0000 0x00ffffffff1fff00

def z31 : W := mkw 0x14105061b0a00040 0xa0d0f80001a25900 0xffffffffffff0000 0x00f9f80001ffff00

def z32 : W := mkw 0xd9a6bb002048e371 0xd8ee00fe017d005b 0xffffff800000ffff 0xfffe3fffffff00ff

def z33 : W := mkw 0x60c7228e450f7daa 0x1521019ddc14a4f6 0x000000000000ffff 0xff0001fffe0000ff

def z34 : W := mkw 0x1c30f461e89003c1 0x80fbdbeaab231900 0xe000ff81ff000000 0x00ffffffff073800

def z35 : W := mkw 0x6005228a450e57ab 0x142101fbba14a4f0 0x000000000000fffe 0x000001fffe0000f8

def z36 : W := mkw 0x9fbadd71b8f0a251 0xe8defe6601eb5b0b 0xffffffffffff0001 0xfffffe2601ffff07

def z37 : W := mkw 0x1000a00140000381 0x00eb53eaaa000000 0x0000000000000000 0x004637fffe000000

def z38 : W := mkw 0x0e38cc7198f00000 0x601efe0000cb5b00 0x003fffffffff0000 0x003ffe00001fff00

def z39 : W := mkw 0x9920980020408241 0xc0ce006001690009 0xffffff800000ffff 0xfffe01e001ff00ff

def z40 : W := mkw 0x1000c00180800000 0x00dada0000000000 0x0000000000000000 0x00fffe3ffe000000

def z41 : W := mkw 0x4014622080884120 0x1030889800161150 0xe03ffffffffffffe 0x00b9c9d8011ffff8

def z42 : W := mkw 0x1c30d461a8900040 0x80dada0001231900 0xe03fffffffff0000 0x00b9c800011fff00

def z43 : W := mkw 0xb540904d76249acd 0xa6cb7363e3a0e8ad 0xffc0007fff00ffff 0xffc7f7e7e7e0f8ff

def z44 : W := mkw 0x99a299002040a251 0xc8ce00660169000b 0x1fc0000000000001 0xff46002600e00007

def z45 : W := mkw 0x0e385c70b8f00040 0xe014ac0001eb5b00 0xffffffffffff0000 0x00b9c80001ffff00

def z46 : W := mkw 0xb540104d76249acd 0xa6c17161e1a0e8ad 0xffc0007fff00ffff 0xff81c1c001e0f8ff

def z47 : W := mkw 0x2000000844041088 0x040101018000a0a0 0xe000007fff00fffe 0x0081c1c18100f8f8

def z48 : W := mkw 0x0618447198b00000 0x2010fe0000825b00 0xe03fffffffff0000 0x00b9fe00011fff00

def z49 : W := mkw 0x48b7eba281ca6532 0x583e889e185f1552 0x003fff8000ff0000 0x003e081e181f0700

def z50 : W := mkw 0xdbafbb122049e771 0xd9ee04fe157d065b 0xffffff8000ffffff 0xfffe0ffe1fff07ff

def z51 : W := mkw 0x0000e00080800100 0x003a8a8a0a000000 0x0000000000000000 0x003e0e1e1e000000

def z52 : W := mkw 0xa540104c3624984c 0xa600200141a0e8ad 0xffc0007fff00ffff 0xff00000001e0f8ff

def z53 : W := mkw 0x60d762aec58f7daa 0x1531899ddc16b5f6 0xe03fffffffffffff 0xffb9c9ffff1fffff

def z54 : W := mkw 0xb5001049620092c5 0x82c15160a1202829 0xffc00001ff00ffff 0xffc1c1e001e038ff

def z55 : W := mkw 0x225940bed5a71c8a 0x2511ad01dc82f7a4 0x0000007fffff0000 0x0001fe01fe00ff00

def z56 : W := mkw 0xc9a63b002048e170 0xd824009c017d005b 0xffffff800000ffff 0xffb801d801ff00ff

def z57 : W := mkw 0x9500104130208241 0xa0c0706001a04809 0xffc0007fff00ffff 0xffc1f1e001e0f8ff

def z58 : W := mkw 0xa540104c762498cc 0xa6012101c1a0e8ad 0xffc0007fff00ffff 0xff81c1c181e0f8ff

def z59 : W := mkw 0x601562aac58e55aa 0x143189999816b5f0 0xe03ffffffffffffe 0x00b9c1c0011ffff8

def z60 : W := mkw 0x4004220000084120 0x1020009800140050 0xe03fff800000fffe 0x00b801d8011f00f8

def z61 : W := mkw 0x40862a0000486120 0x5024009c005c0052 0xffffff800000ffff 0xfffe01fe01ff00ff

def z62 : W := mkw 0x9f689c553a708a45 0xe2ce766061e94a0d 0x1fc0000000000001 0xff46362060e00007

def z63 : W := mkw 0xa7cb1a5e366dbc6c 0xf704241555f8eeef 0xffff007fffffffff 0xff00000001f8ffff

def z64 : W := mkw 0xcbef1b16346dec78 0xfd04241555fdc6df 0xfffffffe00ffffff 0xff00000001ffc7ff

def z65 : W := mkw 0x1000800100000201 0x00ca526222000000 0x0000000000000000 0x00463e3ffe000000

def z66 : W := mkw 0x1e38dc71b8f00040 0xe0defe0001eb5b00 0xffffffffffff0000 0x00fffe3fffffff00

def z67 : W := mkw 0x429f6ab281cb6522 0x51348c9c1c5e1752 0x003fff8000ff0000 0x003e0e1e1e1f0700

def z68 : W := mkw 0xd10432002008c361 0x90e000f801340059 0xffffff800000ffff 0xfff801f801ff00ff

def z69 : W := mkw 0x1000000140000281 0x00c15160a0000000 0x0000000000000000 0x00c7fffffe000000

def z70 : W := mkw 0x0000200040000381 0x002101eaaa000000 0x0000000000000000 0x00463ffffe000000

def z71 : W := mkw 0x245140efd7a61c8e 0x2611f901f882fda4 0x0000007fffff0000 0x0001f801f800ff00

def z72 : W := mkw 0x1e38dc71b8f00241 0xe0defe6223eb5b00 0xffffffffffff0000 0x00fffe2667ffff00

def z73 : W := mkw 0xe187238a450ef7bb 0x1c2101ff9814a4fb 0x000000000000ffff 0xff0001ff980000ff

def z74 : W := mkw 0x601460a8c1825182 0x0031898888063130 0xe03fffffffff03fe 0x00b9c9c0011fff38

def z75 : W := mkw 0x9f78dc75baf08a45 0xe2defe6061eb5b0d 0xffffffffffff0001 0xfffffe2061ffff07

def z76 : W := mkw 0xe145228e470edfaf 0x162101f9f814a4fd 0x000000000000ffff 0xff0001f9f80000ff

def z77 : W := mkw 0x0218483090e00000 0x6014ac0000ca5300 0xffffffffffff0000 0x00fffe0001ffff00

def z78 : W := mkw 0xd924f101e080c3d1 0x88fbdbeaab250019 0xe000ff80000003fe 0x00ffffffff070038

def z79 : W := mkw 0x00006000c0800180 0x0031898888000000 0x0000000000000000 0x00fffffffe000000

def z80 : W := mkw 0xb500f049e28093c5 0x82fbdbeaab202829 0xe0000001ff0003fe 0x00ffffffff003838

def z81 : W := mkw 0x4abeef3088d86130 0x583e8e9e005f1352 0x003fff8000ff0000 0x003e0e1e001f0700

def z82 : W := mkw 0x601460a8c1825182 0x0031898888063130 0xe000ff81ff0003fe 0x00b9c1c001073838

def z83 : W := mkw 0x0000200040000381 0x002101eaaa000000 0x0000000000000000 0x000001fffe000000

def z84 : W := mkw 0x0e381c7038700040 0xe004240001eb5b00 0xffffffffffff0000 0x0000000001ffff00

def z85 : W := mkw 0x0000e00080800100 0x003a8a8a0a000000 0x0000000000000000 0x007e3e3ffe000000

def z86 : W := mkw 0x62df0abe156f7c2a 0x7504241554def7f6 0xffffffffffffffff 0xff00000001ffffff

def z87 : W := mkw 0x62df6abed5ef7daa 0x7535ad9ddcdef7f6 0xffffffffffffffff 0xffffffffffffffff

def z88 : W := mkw 0x1000e001c0800381 0x00fbdbeaaa000000 0x0000000000000000 0x00b9c1c000000000

def z89 : W := mkw 0xb1001008640492c9 0x84c101618120a0a9 0xffc0007fff00ffff 0xffc1c1e181e0f8ff

def z90 : W := mkw 0x0efb1e763c7d2c68 0xf504241555fbdfc6 0xfffffffffffffc01 0xff00000001ffffc7

def z91 : W := mkw 0x00004001c0800080 0x0011db00aa000000 0x0000000000000000 0x0047fe3ffe000000

def z92 : W := mkw 0x00004001c0800080 0x0011db00aa000000 0x0000000000000000 0x0001fe01fe000000

def z93 : W := mkw 0xc9a61b002048e070 0xd8040014017d005b 0xffffff800000ffff 0xff00000001ff00ff

def z94 : W := mkw 0x9100100020008241 0x80c0006001200009 0xffc000000000ffff 0xffc001e001e000ff

def z95 : W := mkw 0xfde6bb4d766cfbfd 0xfeef71ffe1fde8ff 0xffffffffff00ffff 0xfffff1ffe1fff8ff

def z96 : W := mkw 0x1000800100000201 0x00ca526222000000 0x0000000000000000 0x0046362666000000

def z97 : W := mkw 0x601502aa050e542a 0x140000111016b5f0 0xe03ffffffffffffe 0x00000000011ffff8

def z98 : W := mkw 0x9100f001e08083c1 0x80fbdbeaab200009 0xffc000000000ffff 0xffffffffffe000ff

def bk0_0 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z6,z3,z4,z5])],[],[(0,[z0,z7,z1,z3,z4,z5]),(0,[z0,z1,z3,z8,z4,z5])],[(0,[z0,z1,z9,z10,z3,z4]),(0,[z0,z1,z9,z11,z4,z5])],[(0,[z0,z1,z9,z12,z3,z5]),(0,[z0,z1,z9,z3,z4,z13]),(0,[z0,z1,z9,z3,z14,z5])],[(0,[z15,z0,z9,z3,z16,z5]),(0,[z17,z0,z9,z3,z4,z5]),(0,[z0,z18,z9,z3,z4,z5]),(0,[z0,z1,z9,z19,z4,z5]),(0,[z0,z1,z9,z3,z4,z20]),(0,[z0,z9,z3,z21,z4,z5])],[(0,[z15,z0,z9,z3,z4,z5]),(0,[z22,z0,z23,z3,z4,z5]),(0,[z0,z1,z24,z3,z4,z5])],[(0,[z25,z0,z1,z26,z4,z5])]]

def bk0_1 : List (List (ℕ × List W)) :=
  [[(0,[z15,z22,z9,z3,z4,z5]),(0,[z15,z0,z9,z27,z4,z5]),(0,[z0,z1,z9,z3,z4,z28]),(0,[z0,z1,z29,z3,z4,z5])],[(0,[z0,z30,z9,z3,z4,z5])],[],[(0,[z0,z1,z31,z3,z4,z5])],[(0,[z0,z1,z9,z3,z4,z32]),(0,[z0,z1,z3,z33,z4,z5]),(0,[z0,z34,z9,z3,z4,z5])],[(0,[z0,z1,z35,z3,z4,z5])],[(0,[z15,z25,z0,z3,z4,z5]),(0,[z0,z1,z3,z36,z4,z5])],[]]

def bk0_2 : List (List (ℕ × List W)) :=
  [[(0,[z25,z0,z37,z3,z4,z5]),(0,[z0,z38,z1,z3,z4,z5]),(0,[z0,z1,z9,z3,z39,z4])],[(0,[z0,z40,z9,z3,z4,z5])],[(0,[z25,z0,z1,z23,z4,z5]),(0,[z0,z1,z9,z41,z4,z5])],[(0,[z0,z1,z42,z3,z4,z5]),(0,[z0,z1,z9,z3,z43,z5])],[(0,[z25,z0,z1,z44,z4,z5]),(0,[z0,z45,z1,z3,z4,z5])],[(0,[z15,z0,z9,z3,z46,z5])],[(0,[z25,z0,z1,z47,z4,z5]),(0,[z0,z48,z1,z3,z4,z5]),(0,[z0,z1,z9,z49,z3,z5]),(0,[z0,z1,z9,z3,z4,z50]),(0,[z0,z1,z9,z3,z16,z5])],[(0,[z51,z0,z9,z3,z52,z5]),(0,[z0,z1,z9,z3,z4,z5]),(0,[z0,z1,z9,z53,z4,z5])]]

def bk0_3 : List (List (ℕ × List W)) :=
  [[(0,[z0,z1,z9,z3,z54,z5])],[(0,[z0,z1,z9,z55,z3,z4]),(0,[z0,z1,z9,z3,z4,z56]),(0,[z0,z1,z9,z27,z4,z5])],[],[(0,[z0,z1,z9,z3,z57,z5])],[(0,[z0,z1,z9,z3,z58,z5])],[(0,[z15,z0,z9,z59,z4,z5]),(0,[z25,z0,z1,z60,z4,z5]),(0,[z25,z0,z1,z3,z4,z5])],[(0,[z0,z1,z9,z61,z3,z4])],[(0,[z0,z1,z9,z62,z4,z5])]]

def bk0_4 : List (List (ℕ × List W)) :=
  [[(0,[z0,z9,z3,z63,z4,z5])],[(0,[z22,z0,z9,z3,z4,z5]),(0,[z0,z9,z3,z4,z64,z5])],[],[(0,[z0,z65,z9,z3,z4,z5])],[(0,[z15,z0,z66,z3,z4,z5]),(0,[z0,z1,z9,z67,z3,z5]),(0,[z0,z1,z9,z3,z4,z68])],[(0,[z0,z69,z9,z3,z4,z5])],[(0,[z0,z1,z9,z3,z46,z5])],[]]

def bk0_5 : List (List (ℕ × List W)) :=
  [[(0,[z70,z0,z9,z3,z4,z5]),(0,[z0,z1,z9,z71,z3,z4]),(0,[z0,z1,z72,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z73])],[],[(0,[z0,z1,z9,z74,z4,z5]),(0,[z0,z1,z3,z75,z4,z5]),(0,[z0,z1,z3,z4,z5,z76])],[(0,[z15,z0,z23,z3,z4,z5]),(0,[z25,z0,z30,z3,z4,z5])],[(0,[z77,z0,z1,z3,z4,z5]),(0,[z0,z9,z3,z4,z78,z5])],[(0,[z79,z0,z9,z3,z4,z5])],[(0,[z0,z1,z9,z59,z4,z5])],[(0,[z15,z0,z6,z3,z4,z5]),(0,[z0,z9,z3,z80,z4,z5])]]

def bk0_6 : List (List (ℕ × List W)) :=
  [[],[(0,[z0,z1,z9,z81,z3,z5])],[(0,[z25,z0,z1,z82,z4,z5])],[],[(0,[z83,z0,z84,z3,z4,z5]),(0,[z0,z37,z9,z3,z4,z5])],[(0,[z85,z0,z9,z3,z4,z5]),(0,[z0,z1,z66,z3,z4,z5])],[(0,[z0,z9,z3,z86,z4,z5])],[(0,[z15,z0,z9,z3,z4,z28]),(0,[z25,z0,z1,z87,z4,z5])]]

def bk0_7 : List (List (ℕ × List W)) :=
  [[(0,[z22,z88,z9,z3,z4,z5]),(0,[z0,z1,z9,z3,z89,z5])],[(0,[z0,z90,z9,z3,z4,z5])],[(0,[z91,z0,z9,z3,z4,z5])],[(0,[z15,z0,z9,z3,z4,z32])],[(0,[z0,z1,z23,z3,z4,z5])],[(0,[z92,z0,z9,z3,z4,z93]),(0,[z25,z22,z0,z3,z4,z5]),(0,[z0,z1,z9,z3,z94,z95])],[],[(0,[z0,z96,z9,z97,z4,z5]),(0,[z0,z9,z3,z98,z4,z5])]]

def bk0 : List (List (List (ℕ × List W))) :=
  [bk0_0, bk0_1, bk0_2, bk0_3, bk0_4, bk0_5, bk0_6, bk0_7]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fin0 : chunkOK 5 ((bk0.flatten.drop 0).take 31).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fin1 : chunkOK 5 ((bk0.flatten.drop 31).take 33).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finend : (bk0.flatten.drop 64).isEmpty = true := by
  decide +kernel

theorem winF : windowsF 5 bk0.flatten 0 [31, 33] = true :=
  windowsF_cons fin0 (windowsF_cons fin1 (windowsF_nil finend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pw0 : chunkB (fun c => !inB2 8 64 bk0 c) 2 (((level0 7 rows).drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pwend : ((level0 7 rows).drop 1).isEmpty = true := by
  decide +kernel

theorem winP : windowsG (chunkB (fun c => !inB2 8 64 bk0 c) 2) (level0 7 rows) 0 [1] = true :=
  windowsG_cons pw0 (windowsG_nil pwend)

theorem reject : search 7 rows = false := by
  have h0 : FalseAt 5 bk0.flatten.flatten := finalF winF
  have hP : FalseAt 7 (level0 7 rows) := tierB (by norm_num) (memS h0) winP
  exact search_of_false hP

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
    change 9 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_36587

theorem PEqualNP.Outside.L_meta_36587 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3972587520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3972587520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36587.solve
