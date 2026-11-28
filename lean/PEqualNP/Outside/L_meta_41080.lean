import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41080

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
  Nat.testBit (4276808928 * 2 ^ 32 + 4270377984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x6042b3cc3606de64#64 ++ 0x0c08567986c0dbcc#64 ++ 0x60c7f7cc760ffe63#64 ++ 0xec18fef98ec1ffcc#64 : BitVec 256),
   (0x0119805d88116aa8#64 ++ 0x0023300bb1022d55#64 ++ 0x633988ff8831fffe#64 ++ 0xec67311ff1063fff#64 : BitVec 256),
   (0x8c2e0d06dec1c780#64 ++ 0x1185c1a0dbd838f0#64 ++ 0xdc3e0f0fffc1c787#64 ++ 0x7b87c1e1fff838f0#64 : BitVec 256),
   (0x16c00fa0036a0550#64 ++ 0x22d801f4006d40aa#64 ++ 0xffc00ff00ffe07ff#64 ++ 0xbff801fe01ffc0ff#64 : BitVec 256),
   (0x1bbf50000dbdb000#64 ++ 0x4377ea0001b7b600#64 ++ 0xbffff0000ffff807#64 ++ 0xf7fffe0001ffff00#64 : BitVec 256),
   (0x5ff5eefb60000000#64 ++ 0x8bfebddf6c000000#64 ++ 0xdffffffff0000007#64 ++ 0xdbfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x633988ff8831fffe 0xec67311ff1063fff

def z1 : W := mkw 0x12c002a0012a0050 0x225800540025400a 0x23c000f0003e0078 0x8478001e0007c00f

def z2 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xffc00ff00ffe07ff 0xbff801fe01ffc0ff

def z3 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbffff0000ffff807 0xf7fffe0001ffff00

def z4 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdffffffff0000007 0xdbfffffffe000000

def z5 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x60c7f7cc760ffe63 0xec18fef98ec1ffcc

def z6 : W := mkw 0x9eee0fa6dfebc7d0 0x33ddc1f4dbfd78fa 0xfffe0fffffffc7ff 0xffffc1fffffff8ff

def z7 : W := mkw 0x13915000013c3000 0x42722a0000278600 0x23c1f000003e3800 0x84783e000007c700

def z8 : W := mkw 0x84000d06d2404780 0x108001a0da4808f0 0x40000f0ff0000780 0x080001e1fe0000f0

def z9 : W := mkw 0x8c2c0c02c8c10180 0x1185818059182030 0x9c38080389c00184 0x1387010071380030

def z10 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z11 : W := mkw 0xec6ebfcefec7dfe4 0x1d8dd7f9dfd8fbfc 0xfcffffcfffcfffe7 0xff9ffff9fff9fffc

def z12 : W := mkw 0x0000804c00004a20 0x0000100980000944 0x0001800c0001f800 0x4000300180003f00

def z13 : W := mkw 0x0008000488116aa8 0x0001000091022d55 0x200000000831fff8 0x2400000001063fff

def z14 : W := mkw 0x5ee46ea260000000 0x8bdc8dd44c000000 0x9cc6770070000001 0x1398cee00e000000

def z15 : W := mkw 0x0040038002020440 0x0008007000404088 0x60c007c0060e0663 0xac1800f800c1c0cc

def z16 : W := mkw 0x76c2bfec376edf74 0x2ed857fd86eddbee 0xffc7fffc7fffffff 0xfff8ffff8fffffff

def z17 : W := mkw 0x4559aeffe8116aa8 0x88ab35dffd022d55 0x63398ffff831fffe 0xec6731ffff063fff

def z18 : W := mkw 0x1eee0fa00feb8550 0x23ddc1f401fd70aa 0xfffe0ff00fffc7ff 0xffffc1fe01fff8ff

def z19 : W := mkw 0x5ffdeeffe8116aa8 0x8bffbddffd022d55 0xfffffffff831ffff 0xffffffffff063fff

def z20 : W := mkw 0x0008000488014280 0x0001000091002850 0x000000000801c780 0x20000000010038f0

def z21 : W := mkw 0x76c2bfec3606de64 0x0ed857fd86c0dbcc 0xffc7fffc760ffe67 0xfff8ffff8ec1ffcc

def z22 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x0339883f8831f99c 0x40673107f1063f33

def z23 : W := mkw 0x6000b04820041824 0x0c00160904008304 0x0001f00000003800 0x00003e0000000700

def z24 : W := mkw 0x7bfff3cc3fbffe64 0x4f7ffe7987f7ffcc 0xfffff7cc7ffffe67 0xfffffef98fffffcc

def z25 : W := mkw 0xc440affff2404780 0x988815fffe4808f0 0x40000ffff0000780 0x080001fffe0000f0

def z26 : W := mkw 0x53d1e2f920000000 0x8a7a3c5f24000000 0x03c1f0f000000000 0x80783e1e00000000

def z27 : W := mkw 0x800a01049ec1c780 0x1001402093d838f0 0x000000000fc1c780 0x2000000001f838f0

def z28 : W := mkw 0x0000804800000820 0x0000100900000104 0x200180c000003860 0x840030180000070c

def z29 : W := mkw 0x8c260d0256c08500 0x1184c1a04ad810a0 0x9c06070077c00001 0x1380c0e00ef80000

def z30 : W := mkw 0x0111805900102828 0x0022300b20020505 0x230180f000303878 0x8460301e0006070f

def z31 : W := mkw 0x5ff5eefb60102828 0x8bfebddf6c020505 0xfffffffff030387f 0xdffffffffe06070f

def z32 : W := mkw 0x00000100036a0550 0x20000020006d40aa 0x200000000ffe07f8 0x2400000001ffc0ff

def z33 : W := mkw 0x000200041400c200 0x0000400082801840 0x0006000c7001c000 0x4000c0018e003800

def z34 : W := mkw 0x84000d06d2404780 0x108001a0da4808f0 0xdc000f0fffc00787 0x3b8001e1fff800f0

def z35 : W := mkw 0x800a11049ffdf780 0x5001422093ffbef0 0x200000000fffff80 0x2400000001fffff0

def z36 : W := mkw 0x01198059881128a8 0x0023300b31022515 0x233988f3883039fc 0x8467311e7106073f

def z37 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x9cfff70ff0000001 0x539ffee1fe000000

def z38 : W := mkw 0x1fff5ea00dbdb000 0x43ffebd401b7b600 0xfffffff00ffff807 0xfffffffe01ffff00

def z39 : W := mkw 0x53d1e2f9212a0050 0xaa7a3c5f2425400a 0x23c1f0f0003e0078 0x84783e1e0007c00f

def z40 : W := mkw 0x5ff5effb636a0550 0xabfebdff6c6d40aa 0xfffffffffffe07ff 0xffffffffffffc0ff

def z41 : W := mkw 0x0c240c0240000000 0x0184818048000000 0xdc3e0f0ff0000007 0x5b87c1e1fe000000

def z42 : W := mkw 0x1bb5400000000000 0x0376a80000000000 0x9ffff00000000007 0xd3fffe0000000000

def z43 : W := mkw 0x04000c0240000000 0x0080018048000000 0x40000f0ff0000000 0x080001e1fe000000

def z44 : W := mkw 0x6040b3cc32065e64 0x0c0816798640cbcc 0x60c1f7cc700e3e60 0x8c183ef98e01c7cc

def z45 : W := mkw 0x0111805900000000 0x0022300b20000000 0x030180f000000000 0x8060301e00000000

def z46 : W := mkw 0x4d75eefb60000000 0x89aebddf6c000000 0x403ffffff0000000 0x4807fffffe000000

def z47 : W := mkw 0x4935e05b60000000 0x8926bc0b6c000000 0x003ff00ff0000000 0x4007fe01fe000000

def z48 : W := mkw 0x5ffffefb6dbdb000 0xcbffffdf6db7b600 0xfffffffffffff807 0xffffffffffffff00

def z49 : W := mkw 0x12821000052c9000 0x0250420000a59200 0xbfc7f0000ffff807 0xf7f8fe0001ffff00

def z50 : W := mkw 0x1fb54c3340000000 0x83f6a98668000000 0x9f38083380000004 0x13e7010670000000

def z51 : W := mkw 0x200211041606de64 0x0400422082c0dbcc 0x20000000060ffe60 0x2400000000c1ffcc

def z52 : W := mkw 0x5ffdeefb68112000 0x8bffbddf6d022400 0xfffffffff831f807 0xffffffffff063f00

def z53 : W := mkw 0x0008000488014280 0x0001000091002850 0x4038080f8801c786 0x68070101f10038f0

def z54 : W := mkw 0x8d3f8d5fded1efa8 0x11a7f1abfbda3df5 0xff3f8ffffff1ffff 0xffe7f1fffffe3fff

def z55 : W := mkw 0xe442bfcef646dfe4 0x1c8857f9dec8dbfc 0x60c7ffcff60fffe3 0xec18fff9fec1fffc

def z56 : W := mkw 0x0002100004049000 0x0000420000809200 0x20000000060ff800 0x2400000000c1ff00

def z57 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xdcc00ff007ce07f9 0x1b9801fe00f9c0ff

def z58 : W := mkw 0x0002814c1600ce20 0x0000502982c019c4 0x600787cc7601fe63 0xec00f0f98ec03fcc

def z59 : W := mkw 0x5ff5effb62420550 0xabfebdff6c4840aa 0xdffffffff00007ff 0xdbfffffffe0000ff

def z60 : W := mkw 0x04000c2000400110 0x2080018400080022 0x0000083000000198 0x0000010600000033

def z61 : W := mkw 0x082e00000c818000 0x0105c00001903000 0x9c3e00000fc1c007 0x7387c00001f83800

def z62 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xff3e0ffffff1c7ff 0xffe7c1fffffe38ff

def z63 : W := mkw 0x9eee0fa6dec1c780 0x13ddc1f4dbd838f0 0xdffe0fffffc1c787 0xfbffc1fffff838f0

def z64 : W := mkw 0x04000d0002400500 0x008001a0004800a0 0xdc000f000fc00787 0x3b8001e001f800f0

def z65 : W := mkw 0x16c00ea0012a0050 0x22d801d40025400a 0xffc00ff0003e007f 0x9ff801fe0007c00f

def z66 : W := mkw 0x13935000053cb000 0x42726a0000a79600 0x23c7f000063ff803 0xe478fe0000c7ff00

def z67 : W := mkw 0x011b10000c15b000 0x002362000182b600 0x23fff0000e3ff807 0xe47ffe0001c7ff00

def z68 : W := mkw 0x1aa6500005ac9000 0x4354ca0000b59200 0x9cc6700007ce0001 0x1398ce0000f9c000

def z69 : W := mkw 0x1bbfd05d8dbdfaa8 0x4377fa0bb1b7bf55 0xfffff8ff8fffffff 0xffffff1ff1ffffff

def z70 : W := mkw 0x4c64aefb60000000 0x898c95df6c000000 0xdc3e0ffff0000007 0x5b87c1fffe000000

def z71 : W := mkw 0x7ff5fefb60061864 0x8ffebfdf6c00c30c 0xfffffffff00e3867 0xdffffffffe01c70c

def z72 : W := mkw 0x0c2e0c024c818000 0x0185c18049903000 0xdc3e0f0fffc1c007 0x7b87c1e1fff83800

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x630008f0083007fe 0xac60011e010600ff

def z74 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x00c7f70c760ff801 0x4018fee18ec1ff00

def z75 : W := mkw 0x0119001188112088 0x0023200231022411 0x033808338830019c 0x0067010671060033

def z76 : W := mkw 0x6042338036069444 0x0c08467006c0d288 0x00c67700760e0001 0x0018cee00ec1c000

def z77 : W := mkw 0x5bb5e05b60000000 0x8b76bc0b6c000000 0x9ffff00ff0000007 0xd3fffe01fe000000

def z78 : W := mkw 0xec6eafcefec3cfe4 0x1d8dd5f9dfd879fc 0xdc3e0fcfffc1c7e7 0x7b87c1f9fff838fc

def z79 : W := mkw 0x6040b2c820061864 0x0c0816590400c30c 0x20c1f0c0000e3860 0x84183e180001c70c

def z80 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x63c7fffc7e3fffff 0xec78ffff8fc7ffff

def z81 : W := mkw 0x04400fa002420550 0x208801f4004840aa 0x40000ff0000007f8 0x080001fe000000ff

def z82 : W := mkw 0x093f50000c95b000 0x4127ea000192b600 0x003ff0000001f800 0x4007fe0000003f00

def z83 : W := mkw 0x7bf7f3cc3606de64 0x0f7efe7986c0dbcc 0xfffff7cc760ffe67 0xfffffef98ec1ffcc

def z84 : W := mkw 0x84000d0252400500 0x108001a04a4800a0 0x0000070070000000 0x000000e00e000000

def z85 : W := mkw 0x0c240c0240000000 0x0184818048000000 0x9c06070070000001 0x1380c0e00e000000

def z86 : W := mkw 0x17d90fb18b7b25d8 0x22fb21f6316f64bb 0xfff80ff38ffe07ff 0xbfff01fe71ffc0ff

def z87 : W := mkw 0x604ab3ccbe07dee4 0x0c09567997c0fbdc 0x60ffffcffe0fffe7 0xec1ffff9ffc1fffc

def z88 : W := mkw 0x0119000008112000 0x0023200001022400 0x633988f00831fffe 0xec67311e01063fff

def z89 : W := mkw 0x0002000004008000 0x0000400000801000 0x000600000601c003 0x6000c00000c03800

def z90 : W := mkw 0x16c00ea001680110 0x22d801d4002d0022 0xdfc00ff009f0019f 0x9bf801fe013e0033

def z91 : W := mkw 0x5ff7fefb65ac9000 0xcbfeffdf6cb59200 0xdffffffff7ce0007 0xdbfffffffef9c000

def z92 : W := mkw 0xffffffceffffffe4 0x5ffffff9dffffffc 0xffffffcfffffffe7 0xfffffff9fffffffc

def z93 : W := mkw 0x9fbf5d06dffdf780 0x53f7eba0dbffbef0 0xffffff0fffffff87 0xffffffe1fffffff0

def z94 : W := mkw 0x0119000488116280 0x0023200091022c50 0x6339880f8831ff86 0xec673101f1063ff0

def z95 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x0039800f8001f800 0x40073001f0003f00

def z96 : W := mkw 0x1280000001280000 0x0250000000250000 0xbfc000000ffe0007 0xb7f8000001ffc000

def z97 : W := mkw 0xdfffeffffed1efa8 0x9bfffdffffda3df5 0xfffffffffff1ffff 0xfffffffffffe3fff

def z98 : W := mkw 0x882e0006dc81c280 0x1105c000db903850 0x003e000ff001c000 0x4007c001fe003800

def z99 : W := mkw 0x200211041606de64 0x0400422082c0dbcc 0x20c7f000060ffe63 0xe418fe0000c1ffcc

def z100 : W := mkw 0x4c64aeca60000000 0x098c95d94c000000 0xdcffffcff0000007 0xdb9ffff9fe000000

def z101 : W := mkw 0x1bb7500005ac9000 0x4376ea0000b59200 0x9ffff00007ce0007 0xd3fffe0000f9c000

def z102 : W := mkw 0x7ee67fa276069444 0x8fdccff44ec0d288 0x9cc67700760e0001 0x1398cee00ec1c000

def z103 : W := mkw 0x200a11049e17feec 0x0401422093c2ffdd 0x200000000e3ffff8 0x2400000001c7ffff

def z104 : W := mkw 0x615bb3ddbe17feec 0x0c2b767bb7c2ffdd 0x63fffffffe3fffff 0xec7fffffffc7ffff

def z105 : W := mkw 0x4d35ec5b60000000 0x89a6bd8b6c000000 0xdc3fff0ff0000007 0x5b87ffe1fe000000

def z106 : W := mkw 0x8c2e0d02dec18580 0x1185c1a05bd830b0 0x9c3e0f03ffc00185 0x1387c1e07ff80030

def z107 : W := mkw 0x5ee46fa2636a0550 0xabdc8df44c6d40aa 0x9cc6770077ce0001 0x1398cee00ef9c000

def z108 : W := mkw 0x16c00ea001280000 0x02d801d400250000 0xffc00ff00ffe0007 0xbff801fe01ffc000

def z109 : W := mkw 0x882e01049ec1c780 0x1105c02093d838f0 0x9c3e00000fc1c787 0x7387c00001f838f0

def z110 : W := mkw 0x8c2c0d06dac14780 0x118581a0db5828f0 0xdc380f0ff9c00784 0x1b8701e1ff3800f0

def z111 : W := mkw 0x0111805d00004a20 0x0022300ba0000944 0x633988ff8001fe66 0xec67311ff0003fcc

def z112 : W := mkw 0xac2e1d06dec7dfe4 0x1585c3a0dbd8fbfc 0xfc3e0f0fffcfffe7 0x7f87c1e1fff9fffc

def z113 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0x9cc0070007ce0001 0x139800e000f9c000

def z114 : W := mkw 0x0000805d80004aa8 0x0000100bb0000955 0x400008ff800007f8 0x0800011ff00000ff

def z115 : W := mkw 0x6042338036069444 0x0c08467006c0d288 0x20c7f700760ff803 0xe418fee00ec1ff00

def z116 : W := mkw 0x7ae6f3cc37aede64 0x4f5cde7986f5dbcc 0xfcc7f7cc77cffe63 0xff98fef98ef9ffcc

def z117 : W := mkw 0x4000a05b60000000 0x8800140b6c000000 0x0000000ff0000000 0x00000001fe000000

def z118 : W := mkw 0x04000c0000400100 0x0080018000080020 0x9c00080009c00184 0x1380010001380030

def z119 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x600007cc760ffe60 0x2c0000f98ec1ffcc

def z120 : W := mkw 0xe440afcef2424fe4 0x1c8815f9de4849fc 0x40000fcff00007e0 0x080001f9fe0000fc

def z121 : W := mkw 0x17d98ffd8b7b6ff8 0x22fb31ffb16f6dff 0xfff98fff8fffffff 0xffff31fff1ffffff

def z122 : W := mkw 0x9ee60fa257ea8550 0x33dcc1f44afd50aa 0xffc60ff07ffe07ff 0xbff8c1fe0fffc0ff

def z123 : W := mkw 0x000a10000dbdb000 0x4001420001b7b600 0x200000000ffff800 0x2400000001ffff00

def z124 : W := mkw 0x1bb55000013c3000 0x4376aa0000278600 0xbffff000003e3807 0xd7fffe000007c700

def z125 : W := mkw 0x800a00049c81c280 0x1001400093903850 0x000000000001c000 0x0000000000003800

def z126 : W := mkw 0x1aa4400001a80000 0x4354880000350000 0x9c00000001c00000 0x1380000000380000

def z127 : W := mkw 0x0008000488116aa8 0x0001000091022d55 0x000000000001f800 0x0000000000003f00

def z128 : W := mkw 0x800a01049ec1c780 0x1001402093d838f0 0x4006070c7fc1c783 0x6800c0e18ff838f0

def z129 : W := mkw 0x5ffdeeffe8116aa8 0x8bffbddffd022d55 0xdffffffff001f807 0xdbfffffffe003f00

def z130 : W := mkw 0x13d152a0013e3050 0x627a2a540027c60a 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z131 : W := mkw 0x12800100036a0550 0x22500020006d40aa 0xbfc000000ffe07ff 0xb7f8000001ffc0ff

def z132 : W := mkw 0x6042338036069444 0x0c08467006c0d288 0x60c677c0760e0663 0xac18cef80ec1c0cc

def z133 : W := mkw 0x12c003a0036a0550 0x22580074006d40aa 0x23c000f00ffe07f8 0xa478001e01ffc0ff

def z134 : W := mkw 0xdfffeffffec1c780 0x9bfffdffffd838f0 0xdfffffffffc1c787 0xfbfffffffff838f0

def z135 : W := mkw 0x16800c2001680110 0x22d00184002d0022 0x9f00083009f0019c 0x13e00106013e0033

def z136 : W := mkw 0x4975e2db60000000 0x892ebc5b6c000000 0x40fff7cff0000003 0xc81ffef9fe000000

def z137 : W := mkw 0x000201041600c600 0x0000402082c018c0 0x4006070c7601c603 0x6800c0e18ec038c0

def z138 : W := mkw 0x0002100004049000 0x0000420000809200 0x20c7f000060ff803 0xe418fe0000c1ff00

def z139 : W := mkw 0x1ee65fa007ee9550 0x63dccbf400fdd2aa 0xffc67ff00ffe07ff 0xbff8cffe01ffc0ff

def z140 : W := mkw 0x9fbf4d06dec1c780 0x13f7e9a0dbd838f0 0xdfffff0fffc1c787 0xfbffffe1fff838f0

def z141 : W := mkw 0x493ff05b6c95b000 0xc927fe0b6d92b600 0x003ff00ff001f800 0x4007fe01fe003f00

def z142 : W := mkw 0x0000805d80004aa8 0x0000100bb0000955 0x600188ff8001fffa 0xec00311ff0003fff

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x4038080f80000006 0x48070101f0000000

def z144 : W := mkw 0x493de05fe8116aa8 0x8927bc0bfd022d55 0x633ff8fff831fffe 0xec67ff1fff063fff

def z145 : W := mkw 0x011b905d8dbdfaa8 0x4023720bb1b7bf55 0x633988ff8ffffffe 0xec67311ff1ffffff

def z146 : W := mkw 0x6040a2c820020864 0x0c0814590400410c 0x000000c000000060 0x000000180000000c

def z147 : W := mkw 0x4824600260000000 0x89048c004c000000 0x0006700070000000 0x0000ce000e000000

def z148 : W := mkw 0x4040a2c820000000 0x0808145904000000 0x40c7f7cc70000003 0xc818fef98e000000

def z149 : W := mkw 0x0000010002400500 0x00000020004800a0 0x000000000fc00780 0x2000000001f800f0

def z150 : W := mkw 0x8c260d0256c08500 0x1184c1a04ad810a0 0xdc060f007fc00787 0x3b80c1e00ff800f0

def z151 : W := mkw 0x1280002001280010 0x2250000400250002 0x0300003000300018 0x0060000600060003

def z152 : W := mkw 0x6159a3ddba136eec 0x0c2b347bb7426ddd 0x63398ffff831fffe 0xec6731ffff063fff

def z153 : W := mkw 0x5bbff05b6dbdb000 0xcb77fe0b6db7b600 0xbffff00ffffff807 0xf7fffe01ffffff00

def z154 : W := mkw 0x96c00fa6d36a47d0 0x32d801f4da6d48fa 0xffc00ffffffe07ff 0xbff801ffffffc0ff

def z155 : W := mkw 0x0119805988112088 0x0023300b31022411 0x433988ff8830019e 0xc867311ff1060033

def z156 : W := mkw 0x9eae0d06dfe9c780 0x13d5c1a0dbfd38f0 0xfffe0f0fffffc787 0xffffc1e1fffff8f0

def z157 : W := mkw 0x7ff7feff7404da24 0x8ffeffdfee809b44 0xdffffffff001f807 0xdbfffffffe003f00

def z158 : W := mkw 0x0826500004849000 0x4104ca0000909200 0x0006700000000000 0x0000ce0000000000

def z159 : W := mkw 0x082e00048c81c280 0x0105c00091903850 0xdc3e080f8fc1c787 0x7b87c101f1f838f0

def z160 : W := mkw 0x4440aeffe0004aa8 0x888815dffc000955 0x40000ffff00007f8 0x080001fffe0000ff

def z161 : W := mkw 0x1fbf5c334dbdb000 0xc3f7eb8669b7b600 0xbffff8338ffff807 0xf7ffff0671ffff00

def z162 : W := mkw 0x000a11000fffb550 0x6001422001fff6aa 0x200000000ffffff8 0x2400000001ffffff

def z163 : W := mkw 0x800a01049febc7d0 0x3001402093fd78fa 0x200000000fffc7f8 0x2400000001fff8ff

def z164 : W := mkw 0x8000010492404780 0x10000020924808f0 0x0000000000000780 0x00000000000000f0

def z165 : W := mkw 0x6002b04c3404da24 0x0c00560986809b44 0x20c7f00c760ff803 0xe418fe018ec1ff00

def z166 : W := mkw 0x211b915d9e17feec 0x0423722bb3c2ffdd 0x633988ff8e3ffffe 0xec67311ff1c7ffff

def z167 : W := mkw 0x0111000000000000 0x0022200000000000 0x0339800000000006 0xc067300000000000

def z168 : W := mkw 0x2002110016069444 0x0400422002c0d288 0x00000000060e0000 0x0000000000c1c000

def z169 : W := mkw 0x000211041604d600 0x0000422082c09ac0 0x60c7f70c760ffe03 0xec18fee18ec1ffc0

def z170 : W := mkw 0x7ff7ffff7606de64 0x8ffeffffeec0dbcc 0xfffffffff60ffe67 0xfffffffffec1ffcc

def z171 : W := mkw 0x1ff54fb3436a0550 0xa3fea9f6686d40aa 0xfff80ff38ffe07ff 0xbfff01fe71ffc0ff

def z172 : W := mkw 0x1bbfd05d8dbdfaa8 0x4377fa0bb1b7bf55 0xbffff00f8ffff807 0xf7fffe01f1ffff00

def z173 : W := mkw 0x0119804c08116a20 0x0023300981022d44 0x633980cc0831fe66 0xec67301981063fcc

def z174 : W := mkw 0x000801048b7b6ff8 0x20010020916f6dff 0x200000000ffffff8 0x2400000001ffffff

def z175 : W := mkw 0x0040038002020440 0x0008007000404088 0x63c00ff00e3e07ff 0xac7801fe01c7c0ff

def z176 : W := mkw 0x4440aefb60000000 0x888815df6c000000 0x40000ffff0000000 0x080001fffe000000

def z177 : W := mkw 0x6002b04c3404da24 0x0c00560986809b44 0x0007f00c7001f800 0x4000fe018e003f00

def z178 : W := mkw 0x1bbd400009b92000 0x4377a80001372400 0x9f38000009f00004 0x13e70000013e0000

def z179 : W := mkw 0x6040a3cc32024e64 0x0c081479864049cc 0x400007cc70000660 0x080000f98e0000cc

def z180 : W := mkw 0x4151a2d920000000 0x082a345b24000000 0x43fffffff0000007 0xc87ffffffe000000

def z181 : W := mkw 0x5ee46ea260000000 0x8bdc8dd44c000000 0xdcfe7f0ff0000007 0x5b9fcfe1fe000000

def z182 : W := mkw 0x36c21fa4176edf74 0x26d843f482eddbee 0xffc00ff00fffffff 0xbff801fe01ffffff

def z183 : W := mkw 0x1aa6500005ac9000 0x4354ca0000b59200 0xbfc670000ffe0007 0xb7f8ce0001ffc000

def z184 : W := mkw 0x093d400008912000 0x4127a80001122400 0x0038000000000000 0x0007000000000000

def z185 : W := mkw 0x5ff7fefb64049000 0x8bfeffdf6c809200 0xfffffffff60ff807 0xfffffffffec1ff00

def z186 : W := mkw 0xa00a11049ec7dfe4 0x1401422093d8fbfc 0x200000000fcfffe0 0x2400000001f9fffc

def z187 : W := mkw 0x53d1e2f920000000 0x8a7a3c5f24000000 0x43c7f7fc70000003 0xc878feff8e000000

def z188 : W := mkw 0x093fd05d8c95faa8 0x4127fa0bb192bf55 0x003ff00f8001f800 0x4007fe01f0003f00

def z189 : W := mkw 0x0008000088010080 0x0001000011002010 0x0038080388000184 0x0007010071000030

def z190 : W := mkw 0x8c2e1d06dec5d780 0x1185c3a0dbd8baf0 0xfcffff0fffcfff87 0xff9fffe1fff9fff0

def z191 : W := mkw 0x04080d048a414780 0x008101a0914828f0 0xdc380f0f8fc1c787 0x7b8701e1f1f838f0

def z192 : W := mkw 0x8c2e8d5fdec1cfa8 0x1185d1abfbd839f5 0xdc3e0fffffc1c7ff 0x7b87c1fffff838ff

def z193 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x9ffe70000ffe0005 0x13ffce0001ffc000

def z194 : W := mkw 0x8c2c0c06c8c14380 0x11858180d9182870 0xdc38080f89c1c786 0x7b870101f13838f0

def z195 : W := mkw 0x8c2e0c02ccc18180 0x1185c18059983030 0x9c3e08038fc1c187 0x7387c10071f83830

def z196 : W := mkw 0x0000010002420550 0x20000020004840aa 0x00000000000007f8 0x00000000000000ff

def z197 : W := mkw 0x0000000000000000 0x0000000000000000 0x230000f000300078 0x8460001e0006000f

def z198 : W := mkw 0x9fbfdd5fdffdffa8 0x53f7fbabfbffbff5 0xffffffffffffffff 0xffffffffffffffff

def z199 : W := mkw 0x0111805900000000 0x0022300b20000000 0x433988ff80000006 0xc867311ff0000000

def z200 : W := mkw 0x8d3f0d17ded1e788 0x11a7e1a2fbda3cf1 0xdf3e0f3ffff1c79f 0x7be7c1e7fffe38f3

def z201 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xbfc007f007fe0079 0x97f800fe00ffc00f

def z202 : W := mkw 0x1fff5fa00fffb550 0x63ffebf401fff6aa 0xfffffff00fffffff 0xfffffffe01ffffff

def z203 : W := mkw 0x8d3f5d06ded5f780 0x51a7eba0dbdabef0 0xdc3fff0fffc1ff87 0x7b87ffe1fff83ff0

def z204 : W := mkw 0x7ff7ffff776edf74 0xaffeffffeeeddbee 0xffffffffffffffff 0xffffffffffffffff

def z205 : W := mkw 0x686eb3cc3e87de64 0x0d0dd67987d0fbcc 0xfcfff7cc7fcffe67 0xff9ffef98ff9ffcc

def z206 : W := mkw 0x6002300034049004 0x0c00460006809200 0x0006700070000000 0x0000ce000e000000

def z207 : W := mkw 0x6440afec32424f74 0x2c8815fd864849ee 0x40000ffc700007f8 0x080001ff8e0000ff

def z208 : W := mkw 0x6442bfff7606de64 0x8c8857ffeec0dbcc 0x60c7fffff60ffe63 0xec18fffffec1ffcc

def z209 : W := mkw 0x17d15fa0037e3550 0x62fa2bf4006fc6aa 0xffc1fff00ffe3fff 0xbff83ffe01ffc7ff

def z210 : W := mkw 0x0008804c88116aa8 0x0001100991022d55 0x600180cc0831fffa 0xec00301981063fff

def z211 : W := mkw 0x000a01049e01c680 0x0001402093c038d0 0x403e0f0ffe01c787 0x6807c1e1ffc038f0

def z212 : W := mkw 0x12c002a0012a0050 0x225800540025400a 0x63c008f0083e07fe 0xac78011e0107c0ff

def z213 : W := mkw 0x6040b2c820061864 0x0c0816590400c30c 0x60c7f7cc700e3863 0xcc18fef98e01c70c

def z214 : W := mkw 0x1391d059013c3828 0x42723a0b20278705 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z215 : W := mkw 0x0002100004049000 0x0000420000809200 0x0007f0000001f800 0x4000fe0000003f00

def z216 : W := mkw 0x0c240d0242400500 0x018481a0484800a0 0xdc3e0f0fffc00787 0x7b87c1e1fff800f0

def z217 : W := mkw 0x0111805d80004aa8 0x0022300bb0000955 0x433988ff800007fe 0xc867311ff00000ff

def z218 : W := mkw 0x04000c3340000000 0x8080018668000000 0x0000083380000000 0x0000010670000000

def z219 : W := mkw 0x16800d2003680510 0x22d001a4006d00a2 0xdf000f300ff0079f 0x3be001e601fe00f3

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0x030008300830019c 0x0060010601060033

def z221 : W := mkw 0x004083cc02024e60 0x00081079804049cc 0x60c187cc060ffe63 0xec1830f980c1ffcc

def z222 : W := mkw 0x5ee46fa2636a0550 0xabdc8df44c6d40aa 0xffc67ff07ffe07ff 0xbff8cffe0fffc0ff

def z223 : W := mkw 0x04400fa002420550 0x208801f4004840aa 0x60c00ff0060e07fb 0xac1801fe00c1c0ff

def z224 : W := mkw 0x9bbf51049ffdf780 0x5377ea2093ffbef0 0xbffff0000fffff87 0xf7fffe0001fffff0

def z225 : W := mkw 0x9eec0fa2cbeb05d0 0x33dd81f4597d60ba 0xfff80ff38ffe07ff 0xbfff01fe71ffc0ff

def z226 : W := mkw 0x4042b2c824049000 0x0808565904809200 0x60c7f7cc760ff803 0xec18fef98ec1ff00

def z227 : W := mkw 0x7fffffff7fbffe64 0xcfffffffeff7ffcc 0xfffffffffffffe67 0xffffffffffffffcc

def z228 : W := mkw 0x8c2e1d06dffdf780 0x5185c3a0dbffbef0 0xfc3e0f0fffffff87 0x7f87c1e1fffffff0

def z229 : W := mkw 0x082e10000c859000 0x0105c2000190b200 0xbcfff0000fcff807 0xf79ffe0001f9ff00

def z230 : W := mkw 0x0119000008112000 0x0023200001022400 0x233980000831f806 0xe467300001063f00

def z231 : W := mkw 0x1fbd4c3349b92000 0xc3f7a98669372400 0x9f38083389f00004 0x13e70106713e0000

def z232 : W := mkw 0xdeee6fa6fec1c780 0x9bddcdf4dfd838f0 0xdcfe7f0fffc1c787 0x7b9fcfe1fff838f0

def z233 : W := mkw 0x52c062a020000000 0x8a580c5404000000 0x00c0700000000000 0x00180e0000000000

def z234 : W := mkw 0x5ff56ea260000000 0x8bfeadd44c000000 0x9ffff70070000007 0xd3fffee00e000000

def z235 : W := mkw 0x1280000001280000 0x0250000000250000 0x23c00000003e0000 0x847800000007c000

def z236 : W := mkw 0x1bbf51041fbdf600 0x4377ea2083f7bec0 0xfffff70c7ffffe07 0xfffffee18fffffc0

def z237 : W := mkw 0x5ff5effb636a0550 0xabfebdff6c6d40aa 0xdffffffff7ce0007 0xdbfffffffef9c000

def z238 : W := mkw 0x1bbdc05d88116aa8 0x0377b80bb1022d55 0xfffff8ff8831ffff 0xffffff1ff1063fff

def z239 : W := mkw 0x0119000488116aa8 0x0023200091022d55 0x233980000831fffe 0xe467300001063fff

def z240 : W := mkw 0x6159b2dda8177aec 0x0c2b365bb502ef5d 0x63f9f8ff883ffffe 0xec7f3f1ff107ffff

def z241 : W := mkw 0x5ff5effb62020440 0x8bfebdff6c404088 0xfffffffff60e0667 0xfffffffffec1c0cc

def z242 : W := mkw 0x53d1f2f9213c3000 0xca7a3e5f24278600 0x23c1f0f0003e3800 0x84783e1e0007c700

def z243 : W := mkw 0x1fb54c0240000000 0x03f6a98048000000 0xdfffff0ff0000007 0xdbffffe1fe000000

def z244 : W := mkw 0x011b815d9e11eea8 0x0023702bb3c23dd5 0x633f8ffffe31ffff 0xec67f1ffffc63fff

def z245 : W := mkw 0x57d1eefb60000000 0x8afa3ddf6c000000 0x43c1fffff0000000 0x88783ffffe000000

def z246 : W := mkw 0x4000a04820000000 0x0800140904000000 0x0007f00c70000000 0x4000fe018e000000

def z247 : W := mkw 0x16800d20036a0550 0x22d001a4006d40aa 0xbf0008300ffe07fc 0x37e0010601ffc0ff

def z248 : W := mkw 0x0111805900102828 0x0022300b20020505 0x0001800000003800 0x0000300000000700

def z249 : W := mkw 0x1bbfd0590dbdb828 0x4377fa0b21b7b705 0xbffff0f00ffff87f 0xf7fffe1e01ffff0f

def z250 : W := mkw 0x0040028000000000 0x0008005000000000 0x40c007c000000003 0x881800f800000000

def z251 : W := mkw 0x6977f3df7606de64 0x8d2efe7beec0dbcc 0x60fff7cff60ffe63 0xec1ffef9fec1ffcc

def z252 : W := mkw 0x5fb5ec7b60000000 0x8bf6bd8f6c000000 0x9f3ff83ff0000004 0x53e7ff07fe000000

def z253 : W := mkw 0x96ca0fa49febc7d0 0x32d941f493fd78fa 0xffc00ff00fffc7ff 0xbff801fe01fff8ff

def z254 : W := mkw 0x1399000009392000 0x0273200001272400 0xbff980000ffff807 0xf7ff300001ffff00

def z255 : W := mkw 0x53d1e2f920000000 0x8a7a3c5f24000000 0x43f9f8ff80000006 0xc87f3f1ff0000000

def z256 : W := mkw 0x05598ffd8a536ff8 0x20ab31ffb14a6dff 0x63398fff8831fffe 0xec6731fff1063fff

def z257 : W := mkw 0x0119805908112000 0x0023300b21022400 0x633988ff8831f806 0xec67311ff1063f00

def z258 : W := mkw 0x84000c02c0400180 0x1080018058080030 0x0000080380000180 0x0000010070000030

def z259 : W := mkw 0x85198d5fda516fa8 0x10a331abfb4a2df5 0x63398ffff831fffe 0xec6731ffff063fff

def z260 : W := mkw 0x5bfff2c82dbdb000 0x4b7ffe5905b7b600 0xfffff7cc7ffff807 0xfffffef98fffff00

def z261 : W := mkw 0x0119805d88014280 0x0023300bb1002850 0x433988ff8801c786 0xe867311ff10038f0

def z262 : W := mkw 0x44402ea260000000 0x888805d44c000000 0x0000070070000000 0x000000e00e000000

def z263 : W := mkw 0x56c0aefb60000000 0x8ad815df6c000000 0xdfc00ffff0000007 0x9bf801fffe000000

def z264 : W := mkw 0x015983dd8a136ee8 0x002b307bb1426ddd 0x63f98fff8e3fffff 0xec7f31fff1c7ffff

def z265 : W := mkw 0x882c0002c8810080 0x1105800059102010 0x0038000380000000 0x0007000070000000

def z266 : W := mkw 0x9fbd4c02c9f92180 0x53f7a980593f2430 0x9f38080389f00184 0x13e70100713e0030

def z267 : W := mkw 0x615bb3ddbe17feec 0x0c2b767bb7c2ffdd 0x60fff7cff60ffe63 0xec1ffef9fec1ffcc

def z268 : W := mkw 0x882e0006dc81c280 0x1105c000db903850 0x403e080ff801c786 0x6807c101ff0038f0

def z269 : W := mkw 0x0000804c00004a20 0x0000100980000944 0x600180cc0001fe62 0xec00301980003fcc

def z270 : W := mkw 0x7ffffffffe17feec 0x8fffffffffc2ffdd 0xfffffffffe3fffff 0xffffffffffc7ffff

def z271 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0x63c00ff0003e07f8 0x8c7801fe0007c0ff

def z272 : W := mkw 0x1bbf50000c95b000 0x4377ea000192b600 0x9ffff0000001f807 0xd3fffe0000003f00

def z273 : W := mkw 0x1bbf50118dbdb088 0x4377ea0231b7b611 0xbffff8338ffff99f 0xf7ffff0671ffff33

def z274 : W := mkw 0x5ee4eeea60000000 0x8bdc9ddd4c000000 0xdcc7f7cc70000003 0xdb98fef98e000000

def z275 : W := mkw 0x611bb05dbc15faac 0x0c23760bb782bf55 0x633ff8fff831fffe 0xec67ff1fff063fff

def z276 : W := mkw 0x893f5006dc95f280 0x5127ea00db92be50 0x003ff00ff001f800 0x4007fe01fe003f00

def z277 : W := mkw 0x0c260d065600c600 0x0184c1a0cac018c0 0xdc3e0f0ff601c607 0x7b87c1e1fec038c0

def z278 : W := mkw 0x04000c0000000000 0x0080018000000000 0xdc000f0000000007 0x1b8001e000000000

def z279 : W := mkw 0x0008000009b92000 0x4001000001372400 0x0000000009f00000 0x00000000013e0000

def z280 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x9fc7f7f070000001 0x93f8fefe0e000000

def z281 : W := mkw 0x1fbd4c2009f92110 0x63f7a984013f2422 0x9f38083009f0019c 0x13e70106013e0033

def z282 : W := mkw 0x04400ea000000000 0x008801d400000000 0x40000ff000000000 0x080001fe00000000

def z283 : W := mkw 0x16c20fa4176ac750 0x22d841f482ed58ea 0xffc60ffc7fffc7ff 0xfff8c1ff8ffff8ff

def z284 : W := mkw 0x4551aefb60000000 0x88aa35df6c000000 0x43398ffff0000006 0xc86731fffe000000

def z285 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x403988ff8001fff8 0x4807311ff0003fff

def z286 : W := mkw 0x72c2b3cc372ede64 0x0e58567986e5dbcc 0xffc7f7cc7ffffe67 0xfff8fef98fffffcc

def z287 : W := mkw 0x1bb5400001280000 0x0376a80000250000 0xbffff0000ffe0007 0xf7fffe0001ffc000

def z288 : W := mkw 0x8c2c0c02c8c10180 0x1185818059182030 0xdc3e0f0ff9c00187 0x5b87c1e1ff380030

def z289 : W := mkw 0x0111805900000000 0x0022300b20000000 0x0039800f80000000 0x40073001f0000000

def z290 : W := mkw 0x12c002a0012a0050 0x225800540025400a 0x00c00000000e0000 0x001800000001c000

def z291 : W := mkw 0x9bbf5006ddbdf280 0x5377ea00dbb7be50 0xbffff00ffffff807 0xf7fffe01ffffff00

def z292 : W := mkw 0x16800d0003680500 0x02d001a0006d00a0 0xffc00f000ffe0787 0xbff801e001ffc0f0

def z293 : W := mkw 0x5bf5e2f920000000 0x8b7ebc5f24000000 0x9ffff0f000000007 0xd3fffe1e00000000

def z294 : W := mkw 0x12c003a0032a0450 0x225800740065408a 0x63c007f0063e067b 0xac7800fe00c7c0cf

def z295 : W := mkw 0x00400380036a0550 0x20080070006d40aa 0x60c007c00ffe07fb 0xac1800f801ffc0ff

def z296 : W := mkw 0x1ff54fa0036a0550 0x23fea9f4006d40aa 0xfffffff00ffe07ff 0xfffffffe01ffc0ff

def z297 : W := mkw 0x84020d06d640c780 0x108041a0dac818f0 0x40060f0ff601c783 0x6800c1e1fec038f0

def z298 : W := mkw 0xdee66fa276c08500 0x9bdccdf44ed810a0 0x9cc6770077c00001 0x1398cee00ef80000

def z299 : W := mkw 0x882e0106dec1c780 0x1105c020dbd838f0 0x003e000fffc1c780 0x6007c001fff838f0

def z300 : W := mkw 0x5ff5eefb61680110 0xabfebddf6c2d0022 0xdffffffff9f0019f 0xdbffffffff3e0033

def z301 : W := mkw 0x882e0106de81c680 0x1105c020dbd038d0 0x403e070ff601c603 0x6807c0e1fec038c0

def z302 : W := mkw 0x4440aefb60000000 0x888815df6c000000 0x40c7fffff0000003 0xc818fffffe000000

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x200180000001f802 0xe400300000003f00

def z304 : W := mkw 0x9fff8fffdffbeff8 0x33fff1fffbff7dff 0xffff8fffffffffff 0xfffff1ffffffffff

def z305 : W := mkw 0xec2ebd4efec5dfa4 0x1d85d7a9dfd8bbf4 0xdc3fff0fffc1ff87 0x7b87ffe1fff83ff0

def z306 : W := mkw 0x0119001188112088 0x0023200231022411 0x233988338831f99e 0xe467310671063f33

def z307 : W := mkw 0x1280000001280000 0x0250000000250000 0xffc008f00ffe07ff 0xbff8011e01ffc0ff

def z308 : W := mkw 0x56c0afe8236a0550 0x2ad815fd046d40aa 0xffc7fffc7ffe07ff 0xfff8ffff8fffc0ff

def z309 : W := mkw 0x1bb5400000000000 0x0376a80000000000 0x9f38000000000004 0x13e7000000000000

def z310 : W := mkw 0x200210041404da24 0x0400420082809b44 0x000000000001f800 0x0000000000003f00

def z311 : W := mkw 0x1ee40ea240000000 0x03dc81d448000000 0xdffe0ffff0000007 0xdbffc1fffe000000

def z312 : W := mkw 0x16c00ea000000000 0x02d801d400000000 0xdfc00ff000000007 0x9bf801fe00000000

def z313 : W := mkw 0x9eae0d26dfe9c790 0x33d5c1a4dbfd38f2 0xdf3e0f3ffff1c79f 0x7be7c1e7fffe38f3

def z314 : W := mkw 0x4040a2f920000000 0x8808145f24000000 0x000000f000000000 0x0000001e00000000

def z315 : W := mkw 0x0111805d80106aa8 0x0022300bb0020d55 0x630188ff80303ff8 0x8c60311ff00607ff

def z316 : W := mkw 0x04000d0002400500 0x008001a0004800a0 0xff000ff00ff007ff 0xbfe001fe01fe00ff

def z317 : W := mkw 0x00000100036a0550 0x20000020006d40aa 0x0000000007ce0000 0x0000000000f9c000

def z318 : W := mkw 0x7bff73803fbfb444 0x4f7fee7007f7f688 0xbffff7007ffff807 0xf7fffee00fffff00

def z319 : W := mkw 0x8c2e0c06dc81c280 0x1185c180db903850 0xdc3e0f0ff001c007 0x5b87c1e1fe003800

def z320 : W := mkw 0x2002914c1606de64 0x0400522982c0dbcc 0x600180cc060ffe62 0xec00301980c1ffcc

def z321 : W := mkw 0x0d358c5b40000000 0x01a6b18b68000000 0xdf3f8ffff0000007 0xdbe7f1fffe000000

def z322 : W := mkw 0x5ffffefb6c95b000 0xcbffffdf6d92b600 0xdffffffff001f807 0xdbfffffffe003f00

def z323 : W := mkw 0xdfffefffffebc7d0 0xbbfffdfffffd78fa 0xffffffffffffc7ff 0xfffffffffffff8ff

def z324 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x433988ff8001f806 0xc867311ff0003f00

def z325 : W := mkw 0x76c2bfec376edf74 0x2ed857fd86eddbee 0xfcc7f7cc77cffe63 0xff98fef98ef9ffcc

def z326 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x9c0607007fc1c781 0x3380c0e00ff838f0

def z327 : W := mkw 0x0000000001680110 0x20000000002d0022 0x0000000009f00198 0x00000000013e0033

def z328 : W := mkw 0xdff5effff2404780 0x9bfebdfffe4808f0 0xdffffffff0000787 0xdbfffffffe0000f0

def z329 : W := mkw 0x093fd05d8c95faa8 0x4127fa0bb192bf55 0x633ff8ff8831fffe 0xec67ff1ff1063fff

def z330 : W := mkw 0x082c000008810000 0x0105800001102000 0x9c38000009c00004 0x1387000001380000

def z331 : W := mkw 0x4040a2c820000000 0x0808145904000000 0x00c1f0c000000000 0x80183e1800000000

def z332 : W := mkw 0x1aae50000dad9000 0x4355ca0001b5b200 0x9cfe70000fcfc007 0x739fce0001f9f800

def z333 : W := mkw 0x6042b2cc3404da24 0x0c08565986809b44 0x40c7f7cc7001f803 0xc818fef98e003f00

def z334 : W := mkw 0x811b815d9ed1efa8 0x1023702bb3da3df5 0x633988ff8ff1fffe 0xec67311ff1fe3fff

def z335 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x9ff9f8f380000004 0x93ff3f1e70000000

def z336 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xfffffffff83007ff 0xffffffffff0600ff

def z337 : W := mkw 0x17990c3189792198 0x22f32186312f2433 0x9f38083389f0019c 0x13e70106713e0033

def z338 : W := mkw 0xec66bfce76c6df64 0x1d8cd7f9ced8dbec 0xfcc7f7cc77cffe63 0xff98fef98ef9ffcc

def z339 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x2039800f8831fff8 0x64073001f1063fff

def z340 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x20c1f0c0060ffe60 0xa4183e1800c1ffcc

def z341 : W := mkw 0x000a10048dbdfaa8 0x4001420091b7bf55 0x200000000ffffff8 0x2400000001ffffff

def z342 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x403e0f0ff001c780 0x4807c1e1fe0038f0

def z343 : W := mkw 0x1fb54c3340000000 0x83f6a98668000000 0xdf3e0f3ff0000007 0x5be7c1e7fe000000

def z344 : W := mkw 0x0000804800000000 0x0000100900000000 0x400180cc00000002 0xc800301980000000

def z345 : W := mkw 0x8c260d0256c08500 0x1184c1a04ad810a0 0xdc3e0f0ff7c00007 0x5b87c1e1fef80000

def z346 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xdcc00f000fce0787 0x3b9801e001f9c0f0

def z347 : W := mkw 0x6002b14c3604de24 0x0c00562986c09bc4 0x4007f70c7601fe03 0x6800fee18ec03fc0

def z348 : W := mkw 0x1bbf40000db9a000 0x4377e80001b73400 0x9f3e00000ff1c007 0x73e7c00001fe3800

def z349 : W := mkw 0x0008805d88014aa8 0x0001100bb1002955 0x403808ff8801c7fe 0x6807011ff10038ff

def z350 : W := mkw 0x5bfff2f92dbdb000 0xcb7ffe5f25b7b600 0xbffff0f00ffff807 0xf7fffe1e01ffff00

def z351 : W := mkw 0x7bfff2c82dbfb864 0x4f7ffe5905b7f70c 0xbffff0c00ffff867 0xf7fffe1801ffff0c

def z352 : W := mkw 0x6042b3ddb606deec 0x0c08567bb6c0dbdd 0x60c7fffff60ffffb 0xec18fffffec1ffff

def z353 : W := mkw 0x6040b2cc20065a64 0x0c0816598400cb4c 0x60c1f0cc000ffe62 0xec183e198001ffcc

def z354 : W := mkw 0x72c0b2e8212e1874 0x2e58165d0425c30e 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z355 : W := mkw 0x5ff7efff7600c600 0x8bfefdffeec018c0 0xdffffffff601c607 0xfbfffffffec038c0

def z356 : W := mkw 0x0119001188112088 0x0023200231022411 0x0038000380000000 0x0007000070000000

def z357 : W := mkw 0x0826000004808000 0x0104c00000901000 0x9c06000007c00001 0x1380c00000f80000

def z358 : W := mkw 0x4111e05920000000 0x88223c0b24000000 0x0001f00000000000 0x00003e0000000000

def z359 : W := mkw 0x1bbf51000fffb550 0x6377ea2001fff6aa 0xbffff0000fffffff 0xf7fffe0001ffffff

def z360 : W := mkw 0xe82eb04efc85daa4 0x1d05d609df90bb54 0x003ff00ff001f800 0x4007fe01fe003f00

def z361 : W := mkw 0x4935e05b60000000 0x8926bc0b6c000000 0x433ff8fff0000006 0xc867ff1ffe000000

def z362 : W := mkw 0x8c2e0d06ded1efa8 0x1185c1a0dbda3df5 0xfc3e0f0ffff1ffff 0x7f87c1e1fffe3fff

def z363 : W := mkw 0x7ee6ffee7606de64 0x8fdcdffdcec0dbcc 0xfcc7f7cc760ffe63 0xff98fef98ec1ffcc

def z364 : W := mkw 0x0042138006069440 0x0008427000c0d288 0x60c7f7c0060ffe63 0xec18fef800c1ffcc

def z365 : W := mkw 0x0000000000102828 0x0000000000020505 0x2000000000303878 0x040000000006070f

def z366 : W := mkw 0x011b10000dbdb000 0x4023620001b7b600 0x233980000ffff806 0xe467300001ffff00

def z367 : W := mkw 0x0119815d8b7b6ff8 0x2023302bb16f6dff 0x633988ff8ffffffe 0xec67311ff1ffffff

def z368 : W := mkw 0x04400fa002420550 0x208801f4004840aa 0xdc000ff00fc007ff 0x3b8001fe01f800ff

def z369 : W := mkw 0x0119805908112828 0x0023300b21022505 0x233980f00831f87e 0xe467301e01063f0f

def z370 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x2339800f8831f806 0xe4673001f1063f00

def z371 : W := mkw 0x0000805d80004aa8 0x0000100bb0000955 0x630008ff883007fe 0xac60011ff10600ff

def z372 : W := mkw 0x093f50000c95b000 0x4127ea000192b600 0x9c3ff0000fc1f807 0x7387fe0001f83f00

def z373 : W := mkw 0x6040a3cc32024e64 0x0c081479864049cc 0x40c7f7cc70000663 0xc818fef98e0000cc

def z374 : W := mkw 0x5ffffeffedbdfaa8 0xcbffffdffdb7bf55 0xffffffffffffffff 0xffffffffffffffff

def z375 : W := mkw 0x0111001100102008 0x0022200220020401 0x0300003000300018 0x0060000600060003

def z376 : W := mkw 0x8c6e0f86dec3c7c0 0x118dc1f0dbd878f8 0xfcfe0fcfffcfc7e7 0xff9fc1f9fff9f8fc

def z377 : W := mkw 0x6042b3c836069c64 0x0c08567906c0d38c 0x20c7f7c0760e3861 0x8418fef80ec1c70c

def z378 : W := mkw 0x1280000001280000 0x0250000000250000 0x9f00000009f00004 0x13e00000013e0000

def z379 : W := mkw 0x5ff5fefb613c3000 0xcbfebfdf6c278600 0xfffffffff03e3807 0xdffffffffe07c700

def z380 : W := mkw 0x04000d0002400500 0x008001a0004800a0 0x9c00070007c00001 0x138000e000f80000

def z381 : W := mkw 0x16c00ea000000000 0x02d801d400000000 0xffc00ff0083007ff 0xbff801fe010600ff

def z382 : W := mkw 0x6442bfcc3646df64 0x0c8857f986c8dbec 0xfcc7ffcc7fcfffe7 0xff98fff98ff9fffc

def z383 : W := mkw 0x5ee67ea265ac9000 0xcbdccfd44cb59200 0x9cc6770077ce0001 0x1398cee00ef9c000

def z384 : W := mkw 0x72c2b3ec372ede74 0x2e58567d86e5dbce 0x63c7f7fc763ffe7b 0xec78feff8ec7ffcf

def z385 : W := mkw 0x16c21fa0076e9550 0x22d843f400edd2aa 0xffc7fff00fffffff 0xfff8fffe01ffffff

def z386 : W := mkw 0x1fb54c3341680110 0xa3f6a986682d0022 0x9f38083389f0019c 0x13e70106713e0033

def z387 : W := mkw 0x7ae6738037ae9444 0x4f5cce7006f5d288 0x9cc6770077ce0001 0x1398cee00ef9c000

def z388 : W := mkw 0x73d1f2c8213e3864 0x4e7a3e590427c70c 0x23c1f0c0003e3860 0x84783e180007c70c

def z389 : W := mkw 0x840a0d049ec1c780 0x108141a093d838f0 0xdc000f000fc1c787 0x3b8001e001f838f0

def z390 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x23fff000003ff800 0xc47ffe000007ff00

def z391 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x9c3e070ff7c1c001 0x5387c0e1fef83800

def z392 : W := mkw 0x8826000254808000 0x1104c0004a901000 0x0006000070000000 0x0000c0000e000000

def z393 : W := mkw 0x1bbfd04c0dbdfa20 0x4377fa0981b7bf44 0xfffff0cc0ffffe67 0xfffffe1981ffffcc

def z394 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xdf000ff009f007fc 0x1be001fe013e00ff

def z395 : W := mkw 0x0000000001280000 0x0000000000250000 0x200000000ffe0000 0x2400000001ffc000

def z396 : W := mkw 0x1bbf40000c818000 0x0377e80001903000 0x9ffff0000fc1c007 0xf3fffe0001f83800

def z397 : W := mkw 0x5ff5eefb612a0050 0xabfebddf6c25400a 0xfffffffff03e007f 0xdffffffffe07c00f

def z398 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xdfc00ff007ce0007 0x9bf801fe00f9c000

def z399 : W := mkw 0x57d1eff9236a0550 0xaafa3dff246d40aa 0xffc1fff00ffe07ff 0xbff83ffe01ffc0ff

def z400 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x9cfff00007cff801 0x539ffe0000f9ff00

def z401 : W := mkw 0x6042a3cc3602ce64 0x0c08547986c059cc 0x400607cc7601c663 0x6800c0f98ec038cc

def z402 : W := mkw 0x1bb5c05900000000 0x0376b80b20000000 0xdffff8ff80000007 0xdbffff1ff0000000

def z403 : W := mkw 0x1bbd400008112000 0x0377a80001022400 0xbffff0000831f807 0xf7fffe0001063f00

def z404 : W := mkw 0x1ff54eb340000000 0x83fea9d668000000 0xdff80ff380000007 0x9bff01fe70000000

def z405 : W := mkw 0x0008804c88014aa0 0x0001100991002954 0x603988cf8801ffe6 0xec073119f1003ffc

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x400008f0000007f8 0x0800011e000000ff

def z407 : W := mkw 0x0119000008112000 0x0023200001022400 0x003980000001f800 0x4007300000003f00

def z408 : W := mkw 0x1bbf50048dbdf280 0x4377ea0091b7be50 0xfffff80f8fffff87 0xffffff01f1fffff0

def z409 : W := mkw 0x0000000480004280 0x0000000090000850 0x4000080f80000780 0x08000101f00000f0

def z410 : W := mkw 0x082e00000c818000 0x0105c00001903000 0x003e00000001c000 0x4007c00000003800

def z411 : W := mkw 0x16c08fec036a4f70 0x22d811fd806d49ee 0xffc18ffc0fffffff 0xfff831ff81ffffff

def z412 : W := mkw 0x04000d0002400500 0x008001a0004800a0 0x40000f0000000780 0x080001e0000000f0

def z413 : W := mkw 0x84400fa6d24247d0 0x308801f4da4848fa 0x40000ffff00007f8 0x080001fffe0000ff

def z414 : W := mkw 0x1bbdc05d89b96aa8 0x4377b80bb1372d55 0xff3988ff89f1fffe 0xffe7311ff13e3fff

def z415 : W := mkw 0x4042a3cc3600c600 0x0808547986c018c0 0x40c7f7cc7601c603 0xe818fef98ec038c0

def z416 : W := mkw 0x04400f8002420540 0x008801f0004840a8 0xfcc00fc00fce07e7 0xbf9801f801f9c0fc

def z417 : W := mkw 0x13d982fd893b6af8 0x227b305fb1276d5f 0x63f988ff883ffffe 0xec7f311ff107ffff

def z418 : W := mkw 0x1fbdcc7fc8116aa8 0x83f7b98ff9022d55 0xff3988ff8831fffe 0xffe7311ff1063fff

def z419 : W := mkw 0x1bb7500005bcb000 0x4376ea0000b79600 0xbfc7f00007fe3801 0x97f8fe0000ffc700

def z420 : W := mkw 0x611bb05dbc15faac 0x0c23760bb782bf55 0x003ff00ff001f800 0x4007fe01fe003f00

def z421 : W := mkw 0x0000804c00004a20 0x0000100980000944 0x630188fc0831fffe 0xec60311f81063fff

def z422 : W := mkw 0x2000010412024e64 0x04000020824049cc 0x0000000000000660 0x00000000000000cc

def z423 : W := mkw 0x0d3d8c5fc8116aa8 0x01a7b18bf9022d55 0xff3f8ffff831ffff 0xffe7f1ffff063fff

def z424 : W := mkw 0x882e0006dc81c280 0x1105c000db903850 0x9c3e000fffc1c007 0x7387c001fff83800

def z425 : W := mkw 0x16800c2001680110 0x22d00184002d0022 0xbfc008300ffe019f 0xb7f8010601ffc033

def z426 : W := mkw 0x16c00ea000000000 0x02d801d400000000 0x9cc0070000000001 0x139800e000000000

def z427 : W := mkw 0x0111000000102000 0x0022200000020400 0x2301800000303800 0x8460300000060700

def z428 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xbfc007000ffe0007 0xb7f800e001ffc000

def z429 : W := mkw 0x0119001588116aa8 0x00232002b1022d55 0x233808338831fffc 0x2467010671063fff

def z430 : W := mkw 0x5ee46ea260000000 0x8bdc8dd44c000000 0xdfc67ff070000007 0x9bf8cffe0e000000

def z431 : W := mkw 0x093f50000dbdb000 0x4127ea0001b7b600 0x203ff0000ffff800 0x6407fe0001ffff00

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0x430008f000000006 0x8860011e00000000

def z433 : W := mkw 0x0002100005ac9000 0x4000420000b59200 0x0000000007ce0000 0x0000000000f9c000

def z434 : W := mkw 0x17d98efd88116aa8 0x02fb31dfb1022d55 0xfff98fff8831ffff 0xffff31fff1063fff

def z435 : W := mkw 0x6042b2c824069864 0x0c0856590480d30c 0x20c7f0c0060ff863 0xe418fe1800c1ff0c

def z436 : W := mkw 0x84080d06da414780 0x108101a0db4828f0 0x40380f0ff801c786 0x680701e1ff0038f0

def z437 : W := mkw 0x9fbf5d025ffdb500 0x53f7eba04bffb6a0 0xbffff7007ffff807 0xf7fffee00fffff00

def z438 : W := mkw 0x0000010002020440 0x0000002000404088 0x20000000060e0660 0x2400000000c1c0cc

def z439 : W := mkw 0x0000010412004600 0x00000020824008c0 0x4000070c70000600 0x080000e18e0000c0

def z440 : W := mkw 0x8d3d0c13c8d12188 0x11a7a182791a2431 0x9f38083389f0019c 0x13e70106713e0033

def z441 : W := mkw 0x1bbd400009b92000 0x4377a80001372400 0xbff800000ffe0007 0xb7ff000001ffc000

def z442 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000083007f8 0x24000000010600ff

def z443 : W := mkw 0x7ff7fffb76069444 0x8ffeffff6ec0d288 0xdffffffff60e0007 0xdbfffffffec1c000

def z444 : W := mkw 0x1fbd4c33c8112088 0x83f7a98679022411 0x9f3808338830019c 0x13e7010671060033

def z445 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xfffff8f00fffffff 0xffffff1e01ffffff

def z446 : W := mkw 0x1bbd500009bd3000 0x4377aa000137a600 0xbff9f00009fe3804 0x97ff3e00013fc700

def z447 : W := mkw 0x0008000008010000 0x0001000001002000 0x003800000801c006 0x6007000001003800

def z448 : W := mkw 0x5ff5eeffe0004aa8 0x8bfebddffc000955 0xdffffffff00007ff 0xdbfffffffe0000ff

def z449 : W := mkw 0x0002100004049000 0x0000420000809200 0x00c67000060e0001 0x0018ce0000c1c000

def z450 : W := mkw 0x0c2e0d000ec18500 0x0185c1a001d830a0 0xdc3e0f000fc1c787 0x7b87c1e001f838f0

def z451 : W := mkw 0x6040a3cc32024e64 0x0c081479864049cc 0x60c007cc760e0663 0xac1800f98ec1c0cc

def z452 : W := mkw 0x5ffdefffeb7b6ff8 0xabffbdfffd6f6dff 0xffffffffffffffff 0xffffffffffffffff

def z453 : W := mkw 0x9fbf4d06dff9e780 0x53f7e9a0dbff3cf0 0xdf3e0f0ffff1c787 0x7be7c1e1fffe38f0

def z454 : W := mkw 0x1bbd400009b92000 0x4377a80001372400 0x9ffff00009f00007 0xd3fffe00013e0000

def z455 : W := mkw 0x17d90fa00b7b2550 0x22fb21f4016f64aa 0xfff98ff00fffffff 0xffff31fe01ffffff

def z456 : W := mkw 0x6442bfec3646df74 0x2c8857fd86c8dbee 0x60c7fffc760ffffb 0xec18ffff8ec1ffff

def z457 : W := mkw 0x0824000240000000 0x0104800048000000 0x003e000ff0000000 0x4007c001fe000000

def z458 : W := mkw 0x1bff53800fbfb440 0x437fea7001f7f688 0xfffff7c00ffffe67 0xfffffef801ffffcc

def z459 : W := mkw 0x8c2e0c06dcc1c380 0x1185c180db983870 0x9c3e080ff9c1c184 0x5387c101ff383830

def z460 : W := mkw 0x0000804c00004a20 0x0000100980000944 0x400000cc00000660 0x08000019800000cc

def z461 : W := mkw 0x9eae5d06dfedd780 0x53d5cba0dbfdbaf0 0xdcfe7f0fffcfc787 0x7b9fcfe1fff9f8f0

def z462 : W := mkw 0x16800c2001680110 0x22d00184002d0022 0xff0008f009f007fe 0xbfe0011e013e00ff

def z463 : W := mkw 0x004002a000020050 0x200800540000400a 0x000000f000000078 0x0000001e0000000f

def z464 : W := mkw 0x7ff5efff72024e64 0x8ffebdffee4049cc 0xdffffffff0000667 0xdbfffffffe0000cc

def z465 : W := mkw 0x0040038002020440 0x0008007000404088 0x00c00700060e0001 0x001800e000c1c000

def z466 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x433808ff883007fc 0x0867011ff10600ff

def z467 : W := mkw 0x80000006d0004280 0x10000000da000850 0x0000000ff0000000 0x00000001fe000000

def z468 : W := mkw 0x0935401340000000 0x8126a80268000000 0x0038000380000000 0x0007000070000000

def z469 : W := mkw 0x12c00380032a0440 0x0258007000654088 0xffc007c00ffe0667 0xbff800f801ffc0cc

def z470 : W := mkw 0x9fbd4c33c8c10180 0x93f7a98679182030 0x9f38083389c00184 0x13e7010671380030

def z471 : W := mkw 0x7fffffec3fffff74 0x6ffffffd87ffffee 0xfffffffc7fffffff 0xffffffff8fffffff

def z472 : W := mkw 0xcd3fed5ffec1c780 0x99a7fdabffd838f0 0xdc3fff0fffc1c787 0x7b87ffe1fff838f0

def z473 : W := mkw 0x1bff52a00dbfb050 0x637fea5401b7f60a 0xbffff0f00ffff87f 0xf7fffe1e01ffff0f

def z474 : W := mkw 0x4440affb62420550 0xa88815ff6c4840aa 0x40000ffff00007f8 0x080001fffe0000ff

def z475 : W := mkw 0x0000010002000400 0x0000002000400080 0x4000070006000603 0x280000e000c000c0

def z476 : W := mkw 0x84008d5fd2404fa8 0x108011abfa4809f5 0x40000ffff00007f8 0x080001fffe0000ff

def z477 : W := mkw 0x093f805d8c91eaa8 0x0127f00bb1923d55 0xff3f88ff8ff1ffff 0xffe7f11ff1fe3fff

def z478 : W := mkw 0x5fffeefb6c818000 0x8bfffddf6d903000 0xdfffffffffc1c007 0xfbfffffffff83800

def z479 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbf3800000ffff804 0x37e7000001ffff00

def z480 : W := mkw 0x0008000488116aa8 0x0001000091022d55 0x630008f00831fffe 0xac60011e01063fff

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x2300000008300006 0xa460000001060000

def z482 : W := mkw 0xed7fbfdffed7ffec 0x1daff7fbffdafffd 0xffffffffffffffff 0xffffffffffffffff

def z483 : W := mkw 0x8c2c0d02cac10580 0x118581a0595820b0 0xdc380f038fc00787 0x3b8701e071f800f0

def z484 : W := mkw 0x200211041606de64 0x0400422082c0dbcc 0x6006070c760ffe63 0x6c00c0e18ec1ffcc

def z485 : W := mkw 0x8c6e0fa6dec3c7d0 0x318dc1f4dbd878fa 0xdc3e0fffffc1c7ff 0x7b87c1fffff838ff

def z486 : W := mkw 0x00001000013c3000 0x4000020000278600 0x20000000003e3800 0x040000000007c700

def z487 : W := mkw 0x1391403100000000 0x8272280620000000 0x0300003000000000 0x0060000600000000

def z488 : W := mkw 0x604233843606de64 0x0c08467086c0dbcc 0x20c67700760ffe61 0x2418cee00ec1ffcc

def z489 : W := mkw 0x4159a2dda8116aa8 0x082b345bb5022d55 0x63fffffff831ffff 0xec7fffffff063fff

def z490 : W := mkw 0x8c240c0240c00100 0x1184818048180020 0x9c00000001c00000 0x1380000000380000

def z491 : W := mkw 0x9fff5fa6dffff7d0 0x73ffebf4dbfffefa 0xffffffffffffffff 0xffffffffffffffff

def z492 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x9f3ff00009f1f804 0x53e7fe00013e3f00

def z493 : W := mkw 0x04400fa002420550 0x208801f4004840aa 0x63000ff0083007fe 0xac6001fe010600ff

def z494 : W := mkw 0x5ff5eefb61280000 0x8bfebddf6c250000 0xfffffffffffe0007 0xffffffffffffc000

def z495 : W := mkw 0x04020d041640c700 0x008041a082c818e0 0xdc060f0c7fc1c787 0x7b80c1e18ff838f0

def z496 : W := mkw 0x8c240d06d2404780 0x118481a0da4808f0 0xdc3e0f0ff0000787 0x5b87c1e1fe0000f0

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z498 : W := mkw 0x093f50000c95b000 0x4127ea000192b600 0x233ff0000831f806 0xe467fe0001063f00

def z499 : W := mkw 0x05198d5d8a516fa8 0x00a331abb14a2df5 0xff398fff8ff1ffff 0xffe731fff1fe3fff

def z500 : W := mkw 0x6c66bfce7606de64 0x0d8cd7f9cec0dbcc 0xfcffffcff60ffe67 0xff9ffff9fec1ffcc

def z501 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0x9fc00f300ffe019d 0x13f801e601ffc033

def z502 : W := mkw 0x697ff3cc3e97fe64 0x4d2ffe7987d2ffcc 0x60fff7cc760ffe63 0xec1ffef98ec1ffcc

def z503 : W := mkw 0x56c0aee820000000 0x0ad815dd04000000 0xdfc7fffc70000007 0xdbf8ffff8e000000

def z504 : W := mkw 0xfffffffffec7dfe4 0x9fffffffffd8fbfc 0xffffffffffcfffe7 0xfffffffffff9fffc

def z505 : W := mkw 0x0000000480004aa8 0x0000000090000955 0x00000000000007f8 0x00000000000000ff

def z506 : W := mkw 0x0935400000000000 0x0126a80000000000 0x003ff00000000000 0x4007fe0000000000

def z507 : W := mkw 0xcc6eafcefec1c780 0x198dd5f9dfd838f0 0xdcffffcfffc1c787 0xfb9ffff9fff838f0

def z508 : W := mkw 0x0c240c0240000000 0x0184818048000000 0x9c38080380000004 0x1387010070000000

def z509 : W := mkw 0x800a01049ec1c780 0x1001402093d838f0 0x4038080f8fc1c786 0x68070101f1f838f0

def z510 : W := mkw 0x5bf5e2fb60000000 0x8b7ebc5f6c000000 0x03fff0fff0000000 0xc07ffe1ffe000000

def z511 : W := mkw 0x8d3f8d5fdec1c780 0x11a7f1abfbd838f0 0xdf3f8fffffc1c787 0xfbe7f1fffff838f0

def z512 : W := mkw 0x8c2e8d4edec1cfa0 0x1185d1a9dbd839f4 0xfc3f8fcfffc1ffe7 0xff87f1f9fff83ffc

def z513 : W := mkw 0x0002010016008400 0x0000402002c01080 0x0006070076000001 0x0000c0e00ec00000

def z514 : W := mkw 0x6000a04c30004a24 0x0c00140986000944 0x0000000c70000000 0x000000018e000000

def z515 : W := mkw 0x0008000488014280 0x0001000091002850 0x633808ff8831c7fe 0xec67011ff10638ff

def z516 : W := mkw 0x6042b3c836069444 0x0c08567906c0d288 0x40c7f7cc760e0003 0xc818fef98ec1c000

def z517 : W := mkw 0x6151b2d92016386c 0x0c2a365b2402c70d 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z518 : W := mkw 0x1fffdffd8ffffff8 0x63fffbffb1ffffff 0xffffffff8fffffff 0xfffffffff1ffffff

def z519 : W := mkw 0x8d3f0d06ded1e780 0x11a7e1a0dbda3cf0 0xff3f8f0ffff1ff87 0xffe7f1e1fffe3ff0

def z520 : W := mkw 0x128a10000dbdb000 0x4251420001b7b600 0xbfc000000ffff807 0xb7f8000001ffff00

def z521 : W := mkw 0x76c0afec336a4f74 0x2ed815fd866d49ee 0xffc00ffc7ffe07ff 0xbff801ff8fffc0ff

def z522 : W := mkw 0x9ea65d0257ec9500 0x53d4cba04afd92a0 0x9cc6770077ce0001 0x1398cee00ef9c000

def z523 : W := mkw 0x0000805900000000 0x0000100b20000000 0x400008ff80000000 0x0800011ff0000000

def z524 : W := mkw 0x12805000012c1000 0x42500a0000258200 0x00c07000000e0000 0x00180e000001c000

def z525 : W := mkw 0x16800c2000000000 0x02d0018400000000 0x9f00083000000004 0x13e0010600000000

def z526 : W := mkw 0xc93fe05ffc81c280 0x9927fc0bff903850 0x003ff00ff001c000 0x4007fe01fe003800

def z527 : W := mkw 0x16800c2001680110 0x22d00184002d0022 0x9c00000001c00000 0x1380000000380000

def z528 : W := mkw 0x8c260d0656c0c700 0x1184c1a0cad818e0 0xdc06070c77c1c603 0x7b80c0e18ef838c0

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x20c00000060e0003 0xa418000000c1c000

def z530 : W := mkw 0x840a0d06dec1c780 0x108141a0dbd838f0 0x40000f0fffc1c780 0x280001e1fff838f0

def z531 : W := mkw 0x1ffd4fa00bfb2550 0x63ffa9f4017f64aa 0xfff80ff00ffe07ff 0xbfff01fe01ffc0ff

def z532 : W := mkw 0x04408ffd82424ff8 0x208811ffb04849ff 0x40000fff800007f8 0x080001fff00000ff

def z533 : W := mkw 0x1280000001280000 0x0250000000250000 0x9cc0000007ce0001 0x1398000000f9c000

def z534 : W := mkw 0x1aa6500005ac9000 0x4354ca0000b59200 0xbcc7f00007cff803 0xf798fe0000f9ff00

def z535 : W := mkw 0x5ffdeefbe8112088 0x8bffbddf7d022411 0xdffffffff830019f 0xdbffffffff060033

def z536 : W := mkw 0x604ab3ccbe17feec 0x0c09567997c2ffdd 0x60c7f7cc7e3ffffb 0xec18fef98fc7ffff

def z537 : W := mkw 0x011b905d8c15faa8 0x0023720bb182bf55 0x63fff8ff8e3fffff 0xec7fff1ff1c7ffff

def z538 : W := mkw 0x7bbff04c3dbdfa24 0x4f77fe0987b7bf44 0xbffff00c7ffff807 0xf7fffe018fffff00

def z539 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x603980cf8001fe62 0xec073019f0003fcc

def z540 : W := mkw 0x9eac0c22c9e90190 0x33d58184593d2032 0x9f38083389f0019c 0x13e70106713e0033

def z541 : W := mkw 0x0008000008112000 0x0001000001022400 0x200000000831f800 0x2400000001063f00

def z542 : W := mkw 0x0111001100000000 0x0022200220000000 0x0338083380000004 0x0067010670000000

def z543 : W := mkw 0x76c23fa0376e9554 0x2ed847f406edd2aa 0x9cc6770077ce0001 0x1398cee00ef9c000

def z544 : W := mkw 0x16ca1fa00fffb550 0x62d943f401fff6aa 0xffc00ff00fffffff 0xbff801fe01ffffff

def z545 : W := mkw 0x9eee0fa6dfebc7d0 0x33ddc1f4dbfd78fa 0xdcfe0f0fffcfc787 0x7b9fc1e1fff9f8f0

def z546 : W := mkw 0x5fff7ea26dbdb000 0xcbffefd44db7b600 0xbffff7007ffff807 0xf7fffee00fffff00

def z547 : W := mkw 0x76c23fa0376e9554 0x2ed847f406edd2aa 0xffc67ff07ffe07ff 0xbff8cffe0fffc0ff

def z548 : W := mkw 0x8c2e0d06dfebc7d0 0x3185c1a0dbfd78fa 0xfc3e0f0fffffc7ff 0x7f87c1e1fffff8ff

def z549 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x4039880f8801ff86 0x68073101f1003ff0

def z550 : W := mkw 0x2000100000061864 0x040002000000c30c 0x20000000000e3860 0x040000000001c70c

def z551 : W := mkw 0x1fbf5c024dbdb000 0x43f7eb8049b7b600 0xffffff0ffffff807 0xffffffe1ffffff00

def z552 : W := mkw 0x5ffdeeffe8014280 0x8bffbddffd002850 0xdffffffff801c787 0xfbffffffff0038f0

def z553 : W := mkw 0x082e10000dbdb000 0x4105c20001b7b600 0xbc3e00000ffff807 0x7787c00001ffff00

def z554 : W := mkw 0x6153b3dd3616fe6c 0x0c2a767ba6c2dfcd 0x63c7f7fc763ffe7b 0xec78feff8ec7ffcf

def z555 : W := mkw 0x0111805d00106a28 0x0022300ba0020d45 0x630180fc0031fe7a 0xec60301f80063fcf

def z556 : W := mkw 0x04400fa002420550 0x208801f4004840aa 0x0000070000000000 0x000000e000000000

def z557 : W := mkw 0xdff7effb76c08500 0x9bfefdff6ed810a0 0xdffffffff7c00007 0xdbfffffffef80000

def z558 : W := mkw 0x204213841606de64 0x0408427082c0dbcc 0x60c007c0060ffe63 0xac1800f800c1ffcc

def z559 : W := mkw 0x139b50000dbdb000 0x42736a0001b7b600 0x23c1f0000ffff800 0xa4783e0001ffff00

def z560 : W := mkw 0x73d1f2f920061864 0x8e7a3e5f2400c30c 0x23c1f0f0000e3860 0x84783e1e0001c70c

def z561 : W := mkw 0x8008000088c10180 0x1001000011182030 0x0000000009c00180 0x0000000001380030

def z562 : W := mkw 0x9fbf5c02cdfdb180 0x53f7eb8059bfb630 0xbffff8038ffff987 0xf7ffff0071ffff30

def z563 : W := mkw 0x0000001180000088 0x0000000230000011 0x0000083380000198 0x0000010670000033

def z564 : W := mkw 0x6937f05f7404da24 0x8d26fe0bee809b44 0x003ff00ff001f800 0x4007fe01fe003f00

def z565 : W := mkw 0x6440afff72024e64 0x8c8815ffee4049cc 0x40000ffff0000660 0x080001fffe0000cc

def z566 : W := mkw 0x76c0bfe8236e1d74 0x2ed817fd046dc3ae 0xffc1fff00ffe3fff 0xbff83ffe01ffc7ff

def z567 : W := mkw 0x0c2c0c06c8014280 0x01858180d9002850 0xdc3e0f0ff801c787 0x7b87c1e1ff0038f0

def z568 : W := mkw 0x0111805900102828 0x0022300b20020505 0x630188f008303ffe 0xac60311e010607ff

def z569 : W := mkw 0x0008805d88116aa8 0x0001100bb1022d55 0x600008ff8831fff8 0x2c00011ff1063fff

def z570 : W := mkw 0x73d3f3cc373efe64 0x4e7a7e7986e7dfcc 0x63c7f7cc763ffe63 0xec78fef98ec7ffcc

def z571 : W := mkw 0x6040328020061044 0x0c0806500400c208 0x00c07000000e0000 0x00180e000001c000

def z572 : W := mkw 0xfeeebfeeffefdff4 0x3fddd7fddffdfbfe 0xffffffffffffffff 0xffffffffffffffff

def z573 : W := mkw 0x13d182f9013a2878 0x227a305f2027450f 0x23c180f0003e3878 0x8478301e0007c70f

def z574 : W := mkw 0x1ea44c2240000000 0x83d4898448000000 0x9c00000000000000 0x1380000000000000

def z575 : W := mkw 0x17998c7d89796bb8 0x22f3318fb12f2d77 0xff3988ff89f1fffe 0xffe7311ff13e3fff

def z576 : W := mkw 0x1fbf5d000ffdb500 0x43f7eba001ffb6a0 0xffffff000fffff87 0xffffffe001fffff0

def z577 : W := mkw 0x1aa4400000000000 0x0354880000000000 0x9cc6700000000001 0x1398ce0000000000

def z578 : W := mkw 0x1bbd400009b92000 0x4377a80001372400 0xbf39800009f1f806 0xf7e73000013e3f00

def z579 : W := mkw 0x1fb54c3340000000 0x83f6a98668000000 0x9ffff83380000007 0xd3ffff0670000000

def z580 : W := mkw 0xec6e3f86fec7d7c4 0x1d8dc7f0dfd8faf8 0xdcfe7f0fffcfc787 0x7b9fcfe1fff9f8f0

def z581 : W := mkw 0x8d3d8c5fc8d16ba8 0x11a7b18bf91a2d75 0xff3988ff89f1fffe 0xffe7311ff13e3fff

def z582 : W := mkw 0x6002b04c3404da24 0x0c00560986809b44 0x6007f0cc7001fe62 0xec00fe198e003fcc

def z583 : W := mkw 0xcc6eaffffec1c780 0x998dd5ffffd838f0 0xdc3e0fffffc1c787 0x7b87c1fffff838f0

def z584 : W := mkw 0x000201041600c600 0x0000402082c018c0 0x000000000601c600 0x2000000000c038c0

def z585 : W := mkw 0x8c260d06d6c0c780 0x1184c1a0dad818f0 0xdc060f0ff7c00781 0x1b80c1e1fef800f0

def z586 : W := mkw 0x1fbf5c200dfdb110 0x63f7eb8401bfb622 0xbffff8300ffff99f 0xf7ffff0601ffff33

def z587 : W := mkw 0x04000d00036a0550 0x208001a0006d40aa 0xfc000f000ffe07ff 0x3f8001e001ffc0ff

def z588 : W := mkw 0x0000000400004a20 0x0000000080000944 0x200000000001fe60 0x2400000000003fcc

def z589 : W := mkw 0x04400fa0036a0550 0x208801f4006d40aa 0x60000ff00ffe07f8 0x2c0001fe01ffc0ff

def z590 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xbcc007000ffe07f9 0x379800e001ffc0ff

def z591 : W := mkw 0x000a10000c95b000 0x400142000192b600 0x000000000001f800 0x0000000000003f00

def z592 : W := mkw 0x00000000012a0050 0x200000000025400a 0x20000000003e0078 0x040000000007c00f

def z593 : W := mkw 0xdffffffffffdf780 0xdbffffffffffbef0 0xffffffffffffff87 0xfffffffffffffff0

def z594 : W := mkw 0x6040a3cc32024e64 0x0c081479864049cc 0x600187cc7001fe62 0xec0030f98e003fcc

def z595 : W := mkw 0x1fff5fa00fffb550 0x63ffebf401fff6aa 0xbffff7000ffff807 0xf7fffee001ffff00

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x4006070c70000003 0x4800c0e18e000000

def z597 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x230180f00831fff8 0xa460301e01063fff

def z598 : W := mkw 0x16c00ea0016a0150 0x22d801d4002d402a 0xbfc008f009fe01fc 0x97f8011e013fc03f

def z599 : W := mkw 0x0119000008112000 0x0023200001022400 0x0338000008300004 0x0067000001060000

def z600 : W := mkw 0x1bbfd0590dbdb000 0x4377fa0b21b7b600 0xfffff8ff8ffff807 0xffffff1ff1ffff00

def z601 : W := mkw 0x6153b3dd3606de64 0x0c2a767ba6c0dbcc 0x63fffffff60ffe67 0xec7ffffffec1ffcc

def z602 : W := mkw 0x1fb5cc7b40000000 0x83f6b98f68000000 0xdf3988ff80000006 0xdbe7311ff0000000

def z603 : W := mkw 0x53d1e2f920102828 0x8a7a3c5f24020505 0x23c1f0f000303878 0x84783e1e0006070f

def z604 : W := mkw 0x1280000000000000 0x0250000000000000 0x9fc0000000000007 0x93f8000000000000

def z605 : W := mkw 0x73d3f3fd3606de64 0x8e7a7e7fa6c0dbcc 0x63c7f7fc760ffe63 0xec78feff8ec1ffcc

def z606 : W := mkw 0x1aae50000dbdb000 0x4355ca0001b7b600 0xbcc670000ffff801 0x3798ce0001ffff00

def z607 : W := mkw 0x12c002a000000000 0x0258005400000000 0x03c000f000000000 0x8078001e00000000

def z608 : W := mkw 0xdfffeefffc81c280 0x9bfffddfff903850 0xdffffffff001c007 0xdbfffffffe003800

def z609 : W := mkw 0x1bbd401189b92088 0x4377a80231372411 0x9f38083389f0019c 0x13e70106713e0033

def z610 : W := mkw 0x9ee60fa257ea8550 0x33dcc1f44afd50aa 0x9cc6070077ce0001 0x1398c0e00ef9c000

def z611 : W := mkw 0x17d18ef900000000 0x02fa31df20000000 0xdff98fff80000007 0xdbff31fff0000000

def z612 : W := mkw 0x0040038002020440 0x0008007000404088 0x400007c000000660 0x080000f8000000cc

def z613 : W := mkw 0x0111805900000000 0x0022300b20000000 0x633988ff883007fe 0xec67311ff10600ff

def z614 : W := mkw 0x1aae00000da98000 0x0355c00001b53000 0xbffe00000fffc007 0xf7ffc00001fff800

def z615 : W := mkw 0x3bbf51041fbffe64 0x4777ea2083f7ffcc 0xbffff0000ffffe67 0xf7fffe0001ffffcc

def z616 : W := mkw 0x16c80fa48b6b47d0 0x22d901f4916d68fa 0xfff80fff8fffc7ff 0xffff01fff1fff8ff

def z617 : W := mkw 0x800a01049ed1efa8 0x1001402093da3df5 0x200000000ff1fff8 0x2400000001fe3fff

def z618 : W := mkw 0x57d1eef920000000 0x8afa3ddf24000000 0xdfc1fff000000007 0x9bf83ffe00000000

def z619 : W := mkw 0x4040a2cc20004a20 0x0808145984000944 0x60c7f7cc7001fe63 0xec18fef98e003fcc

def z620 : W := mkw 0x000a10000dbdb000 0x4001420001b7b600 0x20c7f0000ffff803 0xe418fe0001ffff00

def z621 : W := mkw 0x8d3f8d5fded1efa8 0x11a7f1abfbda3df5 0xdc3f8f0fffc1ff87 0x7b87f1e1fff83ff0

def z622 : W := mkw 0x5ffffffb6fffb550 0xebffffff6dfff6aa 0xffffffffffffffff 0xffffffffffffffff

def z623 : W := mkw 0x12c002a0012a0050 0x225800540025400a 0xbfc000f00ffe007f 0xb7f8001e01ffc00f

def z624 : W := mkw 0x0008000088112088 0x0001000011022411 0x0000000008300198 0x0000000001060033

def z625 : W := mkw 0x0000100000041000 0x0000020000008200 0x20c1f000000e3800 0x84183e000001c700

def z626 : W := mkw 0x13915000013c3000 0x42722a0000278600 0xbfc1f0000ffe3807 0xb7f83e0001ffc700

def z627 : W := mkw 0x16c00fa002420550 0x22d801f4004840aa 0xdfc00ff0000007ff 0x9bf801fe000000ff

def z628 : W := mkw 0x200a11041fbffe64 0x4401422083f7ffcc 0x200000000ffffe60 0x2400000001ffffcc

def z629 : W := mkw 0xdffdeefbe8c10180 0x9bffbddf7d182030 0xdffffffff9c00187 0xdbffffffff380030

def z630 : W := mkw 0x0000805900000828 0x0000100b20000105 0x000000f000000078 0x0000001e0000000f

def z631 : W := mkw 0x0824000000000000 0x0104800000000000 0x9c3e000000000007 0x5387c00000000000

def z632 : W := mkw 0x0000805d80004aa8 0x0000100bb0000955 0x0000000f80000000 0x00000001f0000000

def z633 : W := mkw 0xe86eb3cefe87dee4 0x1d0dd679dfd0fbdc 0x60fff7cff60ffe63 0xec1ffef9fec1ffcc

def z634 : W := mkw 0x0008000488014280 0x0001000091002850 0x0038000f8001c000 0x40070001f0003800

def z635 : W := mkw 0x00000100036a0550 0x20000020006d40aa 0x630008f00ffe07fe 0xac60011e01ffc0ff

def z636 : W := mkw 0x5ff5eeff60004a20 0x8bfebddfec000944 0xfffffffff001fe67 0xfffffffffe003fcc

def z637 : W := mkw 0x1391400000000000 0x0272280000000000 0x03c1f00000000000 0x80783e0000000000

def z638 : W := mkw 0x16c00fa002020440 0x02d801f400404088 0xffc00ff0060e0667 0xbff801fe00c1c0cc

def z639 : W := mkw 0xec663f8276c69544 0x1d8cc7f04ed8d2a8 0x9cc6770077ce0001 0x1398cee00ef9c000

def z640 : W := mkw 0x615bb3cc3e17fe64 0x0c2b767987c2ffcc 0x63fff7cc7e3ffe67 0xec7ffef98fc7ffcc

def z641 : W := mkw 0x17d18ff9036a0550 0x22fa31ff206d40aa 0xfff98fff8ffe07ff 0xffff31fff1ffc0ff

def z642 : W := mkw 0x6040a3ddb2024eec 0x0c08147bb64049dd 0x40000ffff00007f8 0x080001fffe0000ff

def z643 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xfcc007c007ce0663 0xbf9800f800f9c0cc

def z644 : W := mkw 0x5ff5effb62400500 0x8bfebdff6c4800a0 0xdfffffffffc00787 0xfbfffffffff800f0

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c7f00000000003 0xc018fe0000000000

def z646 : W := mkw 0x0111500000143000 0x40222a0000028600 0x0001f00000003800 0x00003e0000000700

def z647 : W := mkw 0x6040b3c822061c64 0x0c0816790440c38c 0x60c1f7c0060e3e63 0xac183ef800c1c7cc

def z648 : W := mkw 0x5ffdeefb69b92000 0xcbffbddf6d372400 0xdffffffff9f00007 0xdbffffffff3e0000

def z649 : W := mkw 0x8002010016c08500 0x1000402002d810a0 0x0000000007c00000 0x0000000000f80000

def z650 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x4007f7cc7001fe60 0x4800fef98e003fcc

def z651 : W := mkw 0x56c0affb636a0550 0xaad815ff6c6d40aa 0xffc00ffffffe07ff 0xbff801ffffffc0ff

def z652 : W := mkw 0x6042b3cc376edf74 0x2c08567986eddbee 0x60c7f7cc7ffffffb 0xec18fef98fffffff

def z653 : W := mkw 0x5bf5e2c820000000 0x0b7ebc5904000000 0xdffff7cc70000007 0xdbfffef98e000000

def z654 : W := mkw 0x4040228020000000 0x0808045004000000 0x00c6770070000001 0x0018cee00e000000

def z655 : W := mkw 0x604233843606d644 0x0c08467086c0dac8 0x40c6770c760fc603 0x6818cee18ec1f8c0

def z656 : W := mkw 0x000a00000c818000 0x0001400001903000 0x000000000fc1c000 0x2000000001f83800

def z657 : W := mkw 0x16c00fa002400500 0x02d801f4004800a0 0xdfc00ff00fc00787 0xbbf801fe01f800f0

def z658 : W := mkw 0x1bbf50048dbdfaa8 0x4377ea0091b7bf55 0xbffff0000fffffff 0xf7fffe0001ffffff

def z659 : W := mkw 0x5ff56eb360000000 0x8bfeadd66c000000 0x9ffe7f33f0000005 0x13ffcfe67e000000

def z660 : W := mkw 0x0002904c0404da20 0x0000520980809b44 0x60c7f0cc060ffe63 0xec18fe1980c1ffcc

def z661 : W := mkw 0x1ff54ea000000000 0x03fea9d400000000 0xdffffff000000007 0xdbfffffe00000000

def z662 : W := mkw 0x0008000488116aa8 0x0001000091022d55 0x6038080f8831fffe 0x6c070101f1063fff

def z663 : W := mkw 0x7bfff3ddbfbffeec 0x4f7ffe7bb7f7ffdd 0xffffffffffffffff 0xffffffffffffffff

def z664 : W := mkw 0x4040a3c822020440 0x0808147904404088 0x60c7f7cc760e0663 0xec18fef98ec1c0cc

def z665 : W := mkw 0x0040028000020040 0x0008005000004008 0x20c000c0000e0060 0x841800180001c00c

def z666 : W := mkw 0x604ab3cc3fbffe64 0x4c09567987f7ffcc 0x60c7f7cc7ffffe63 0xec18fef98fffffcc

def z667 : W := mkw 0x16c80fa48b7b6ff8 0x22d901f4916f6dff 0xffc00ff00fffffff 0xbff801fe01ffffff

def z668 : W := mkw 0x0000000400004200 0x0000000080000840 0x4000000c0001c602 0x68000001800038c0

def z669 : W := mkw 0x6042b2cc3406da64 0x0c0856598680db4c 0x20c7f0cc700ff860 0xc418fe198e01ff0c

def z670 : W := mkw 0x893f805fdc91eaa8 0x1127f00bfb923d55 0x003f800ff001f800 0x4007f001fe003f00

def z671 : W := mkw 0x1399d05d893d7aa8 0x42733a0bb127af55 0x63f9f8ff883ffffe 0xec7f3f1ff107ffff

def z672 : W := mkw 0x0119001588116288 0x00232002b1022c51 0x4338083f8831c79e 0x68670107f10638f3

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000c000000662 0xac000018000000cc

def z674 : W := mkw 0x093f00000c91a000 0x0127e00001923400 0xbf3f80000ff1f807 0xf7e7f00001fe3f00

def z675 : W := mkw 0x893f805fdc91eaa8 0x1127f00bfb923d55 0x633f88fff831fffe 0xec67f11fff063fff

def z676 : W := mkw 0x0111805900102828 0x0022300b20020505 0x633988ff8030387e 0xcc67311ff006070f

def z677 : W := mkw 0x77dbbffdbf7ffffc 0x2efb77ffb7efffff 0xffffffffffffffff 0xffffffffffffffff

def z678 : W := mkw 0x1399805d89396aa8 0x0273300bb1272d55 0xfff988ff8fffffff 0xffff311ff1ffffff

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c0000000fc00007 0x3380000001f80000

def z680 : W := mkw 0x0119001188112088 0x0023200231022411 0x633808f3883007fe 0xac67011e710600ff

def z681 : W := mkw 0x4040a2c820000000 0x0808145904000000 0x400007cc70000000 0x080000f98e000000

def z682 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x40c677cc760e0661 0x0818cef98ec1c0cc

def z683 : W := mkw 0x6040238032020444 0x0c08047006404088 0x0000070070000000 0x000000e00e000000

def z684 : W := mkw 0x6002b14c3606de64 0x0c00562986c0dbcc 0x2007f00c760ffe60 0x6400fe018ec1ffcc

def z685 : W := mkw 0x093f50000c95b000 0x4127ea000192b600 0x20fff000060ff803 0xe41ffe0000c1ff00

def z686 : W := mkw 0x004203841602c640 0x0008407082c058c8 0x60c607cc760fc663 0xec18c0f98ec1f8cc

def z687 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdf380ffff0000004 0x1be701fffe000000

def z688 : W := mkw 0x693ff04c3c95fa24 0x4d27fe098792bf44 0x003ff00c7001f800 0x4007fe018e003f00

def z689 : W := mkw 0x082e01041e81c600 0x0105c02083d038c0 0xdc3e070c7fc1c607 0x7b87c0e18ff838c0

def z690 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x9c3808038fc1c784 0x3387010071f838f0

def z691 : W := mkw 0x53d9e2fda8116aa8 0x8a7b3c5fb5022d55 0x63f9f8ff8831fffe 0xec7f3f1ff1063fff

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000080008000786 0x28000100010000f0

def z693 : W := mkw 0x16c08ffd836a4ff8 0x22d811ffb06d49ff 0xffc00fff8ffe07ff 0xbff801fff1ffc0ff

def z694 : W := mkw 0x1bb7500004049000 0x0376ea0000809200 0xbffff000060ff807 0xf7fffe0000c1ff00

def z695 : W := mkw 0x9fbf4d37dec1c780 0x93f7e9a6fbd838f0 0xdf3e0f3fffc1c787 0x7be7c1e7fff838f0

def z696 : W := mkw 0xe04ab3ccbec7dfe4 0x1c09567997d8fbfc 0x60c7f7cc7fcfffe3 0xec18fef98ff9fffc

def z697 : W := mkw 0x1ee65fa007ee9550 0x63dccbf400fdd2aa 0x9cc6770007ce0001 0x1398cee000f9c000

def z698 : W := mkw 0x5ee4eefb60000000 0x8bdc9ddf6c000000 0xdcc67ffff0000001 0x1b98cffffe000000

def z699 : W := mkw 0x8c2e0d025ec18500 0x1185c1a04bd830a0 0x9c3e07007fc1c007 0x7387c0e00ff83800

def z700 : W := mkw 0x493de05fe8116aa8 0x8927bc0bfd022d55 0x003ff00ff001f800 0x4007fe01fe003f00

def z701 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x233980ff8031f878 0xc467301ff0063f0f

def z702 : W := mkw 0x1391400001382000 0x4272280000270400 0x0300000000300000 0x0060000000060000

def z703 : W := mkw 0x17d18ff9037a2d78 0x22fa31ff206f45af 0xffc18ff00ffe3fff 0xbff831fe01ffc7ff

def z704 : W := mkw 0x13995000093d3000 0x42732a000127a600 0x23f9f000083ff806 0xe47f3e000107ff00

def z705 : W := mkw 0x20021104176edf74 0x2400422082eddbee 0x200000000ffffff8 0x2400000001ffffff

def z706 : W := mkw 0x1ee40fa2436a0550 0x23dc81f4486d40aa 0xfffe0ffffffe07ff 0xffffc1ffffffc0ff

def z707 : W := mkw 0x8c2e0d06dec1cfa0 0x1185c1a0dbd839f4 0xfc3e0f0fffc1ffe7 0x7f87c1e1fff83ffc

def z708 : W := mkw 0x04400f8002420540 0x008801f0004840a8 0xffc00ff00ffe07ff 0xbff801fe01ffc0ff

def z709 : W := mkw 0x6042338036069444 0x0c08467006c0d288 0x60c7f7c0760ffe63 0xec18fef80ec1ffcc

def z710 : W := mkw 0x200a11049e17feec 0x0401422093c2ffdd 0x20000000060ffe60 0x2400000000c1ffcc

def z711 : W := mkw 0x5ff56eb360000000 0x8bfeadd66c000000 0xdffe7f3ff0000007 0x5bffcfe7fe000000

def z712 : W := mkw 0x5ee4eeea60000000 0x8bdc9ddd4c000000 0xdcffffcff0000007 0xdb9ffff9fe000000

def z713 : W := mkw 0x6042b2cc3406da64 0x0c0856598680db4c 0x60c7f7cc700ff863 0xcc18fef98e01ff0c

def z714 : W := mkw 0x0c260d065640c700 0x0184c1a0cac818e0 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z715 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xfff80fff8ffe07ff 0xffff01fff1ffc0ff

def z716 : W := mkw 0x53d1f2f9213e3050 0xea7a3e5f2427c60a 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z717 : W := mkw 0x5bf5e2db60000000 0x8b7ebc5b6c000000 0xdffff7cff0000007 0xdbfffef9fe000000

def z718 : W := mkw 0x1aa6d05d85acdaa8 0x4354da0bb0b59b55 0xdcc678ff87ce07f9 0x1b98cf1ff0f9c0ff

def z719 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x9c3e0f0fffc1c185 0x5387c1e1fff83830

def z720 : W := mkw 0x9aee02a6ddabc2d0 0x335dc054dbb5785a 0x23fe00fff03fc078 0xc47fc01ffe07f80f

def z721 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x9ffff70ff0000007 0xd3fffee1fe000000

def z722 : W := mkw 0x1bbf50110dbdb000 0x4377ea0221b7b600 0xbffff8338ffff807 0xf7ffff0671ffff00

def z723 : W := mkw 0x6440afcc32424f64 0x0c8815f9864849ec 0x40000fcc700007e0 0x080001f98e0000fc

def z724 : W := mkw 0x4d75aedb60000000 0x09aeb5db6c000000 0xdffffffff0000007 0xdbfffffffe000000

def z725 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xff000ff00ffe07fc 0x3fe001fe01ffc0ff

def z726 : W := mkw 0xe93fb05ffc95faac 0x1d27f60bff92bf55 0x003ff00ff001f800 0x4007fe01fe003f00

def z727 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e0f0ff7c1c007 0x5b87c1e1fef83800

def z728 : W := mkw 0x16800c2001680110 0x22d00184002d0022 0xffc008f00ffe07ff 0xbff8011e01ffc0ff

def z729 : W := mkw 0x604233843606d644 0x0c08467086c0dac8 0x60c7f70c760ffe03 0xec18fee18ec1ffc0

def z730 : W := mkw 0x1aae50000dad9000 0x4355ca0001b5b200 0xbcfff0000fcff807 0xf79ffe0001f9ff00

def z731 : W := mkw 0x5ff5eefb60000820 0x8bfebddf6c000104 0xfffffffff0003867 0xdffffffffe00070c

def z732 : W := mkw 0x8c240c0240c00100 0x1184818048180020 0xdc3e0f0ff1c00007 0x5b87c1e1fe380000

def z733 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc380f0fffc1c784 0x3b8701e1fff838f0

def z734 : W := mkw 0x5ff5eefb61680110 0xabfebddf6c2d0022 0xfffffffff9f007ff 0xffffffffff3e00ff

def z735 : W := mkw 0x6042b3fd3606de64 0x8c08567fa6c0dbcc 0x60c7f7fc760ffe63 0xec18feff8ec1ffcc

def z736 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdffffffff830019f 0xdbffffffff060033

def z737 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xfffff80f8ffff807 0xffffff01f1ffff00

def z738 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdcffff0fffc1c787 0xfb9fffe1fff838f0

def z739 : W := mkw 0x444abefb6dbdb000 0xc88957df6db7b600 0x60000ffffffff800 0x2c0001ffffffff00

def z740 : W := mkw 0x200a11049fbffeec 0x4401422093f7ffdd 0x200000000ffffff8 0x2400000001ffffff

def z741 : W := mkw 0xd3dbe3fdbec1c780 0x9a7b7c7fb7d838f0 0x03c1f0f00fc1c780 0xa0783e1e01f838f0

def z742 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x633f8ffff831ffff 0xec67f1ffff063fff

def z743 : W := mkw 0x093f10000c95b000 0x0127e2000192b600 0xbffff0000ffff807 0xf7fffe0001ffff00

def z744 : W := mkw 0x76c02fa0336a0554 0x2ed805f4066d40aa 0xffc00ff07ffe07ff 0xbff801fe0fffc0ff

def z745 : W := mkw 0x4864a2ca60000000 0x090c94594c000000 0x40fff7cff0000003 0xc81ffef9fe000000

def z746 : W := mkw 0x16c00fa2436a0550 0x22d801f4486d40aa 0xffc00ffffffe07ff 0xbff801ffffffc0ff

def z747 : W := mkw 0x53d1e2f921280000 0x8a7a3c5f24250000 0x23c1f0f0003e0000 0x84783e1e0007c000

def z748 : W := mkw 0x128a10000dbdb000 0x4251420001b7b600 0xbfc7f0000ffff807 0xf7f8fe0001ffff00

def z749 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x20c7f7c0760ffe61 0xa418fef80ec1ffcc

def z750 : W := mkw 0x5eec6ea6e8116aa8 0x8bdd8dd4dd022d55 0xbcc677007831fff9 0x3798cee00f063fff

def z751 : W := mkw 0x8c2e0d06ded1e780 0x1185c1a0dbda3cf0 0xfc3e0f0ffff1ff87 0x7f87c1e1fffe3ff0

def z752 : W := mkw 0x8d378d5b56d0ad28 0x11a6f1ab6ada15a5 0xbf0787f077f03879 0x97e0f0fe0efe070f

def z753 : W := mkw 0x8c2e0d06ded1efa8 0x1185c1a0dbda3df5 0xff3e0ffffff1ffff 0xffe7c1fffffe3fff

def z754 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x63c7fffc760ffe67 0xec78ffff8ec1ffcc

def z755 : W := mkw 0x0c240c0240000000 0x0184818048000000 0xdc3e0f0fffc00007 0x7b87c1e1fff80000

def z756 : W := mkw 0x9fbd4c22c9f92190 0x73f7a984593f2432 0x9f38083389f0019c 0x13e70106713e0033

def z757 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdcfff7cff0000003 0xdb9ffef9fe000000

def z758 : W := mkw 0x1bbf50200dbdb010 0x6377ea0401b7b602 0xbffff0300ffff81f 0xf7fffe0601ffff03

def z759 : W := mkw 0x97915d06d37c7780 0x52f22ba0da6f8ef0 0x63c1ff0ff03e3f80 0x8c783fe1fe07c7f0

def z760 : W := mkw 0x04000d00036a0550 0x208001a0006d40aa 0xff000ff00ffe07ff 0xbfe001fe01ffc0ff

def z761 : W := mkw 0x56c02fa2636a0550 0xaad805f44c6d40aa 0xffc00ff07ffe07ff 0xbff801fe0fffc0ff

def z762 : W := mkw 0x615b3391be17b4cc 0x0c2b667237c2f699 0x03fe7f33fe3e019d 0x007fcfe67fc7c033

def z763 : W := mkw 0x4935e15b636a0550 0xa926bc2b6c6d40aa 0x203ff00ffffe07f8 0x6407fe01ffffc0ff

def z764 : W := mkw 0x5ff5eefb60020050 0xabfebddf6c00400a 0xdffffffff000007f 0xdbfffffffe00000f

def z765 : W := mkw 0x4975e2db60000000 0x892ebc5b6c000000 0x43fffffff0000007 0xc87ffffffe000000

def z766 : W := mkw 0x1bbd400009392000 0x0377a80001272400 0xbffff0000ffff807 0xf7fffe0001ffff00

def z767 : W := mkw 0x12821000052c9000 0x0250420000a59200 0xbcc7f00007cff803 0xf798fe0000f9ff00

def z768 : W := mkw 0x8c2e0d06dec1cfa8 0x1185c1a0dbd839f5 0xdc3e0f0fffc1c7ff 0x7b87c1e1fff838ff

def z769 : W := mkw 0x4119a05da8116aa8 0x0823340bb5022d55 0x633ff8fff831fffe 0xec67ff1fff063fff

def z770 : W := mkw 0x1bbf50310dbdb000 0xc377ea0621b7b600 0xbffff0300ffff807 0xf7fffe0601ffff00

def z771 : W := mkw 0x5ff5eefb61680110 0xabfebddf6c2d0022 0xdffffffff1c00007 0xdbfffffffe380000

def z772 : W := mkw 0x8c2e1d06ded5f780 0x5185c3a0dbdabef0 0xdc3e0f0fffc1ff87 0x7b87c1e1fff83ff0

def z773 : W := mkw 0x7bfde3cc3bbb6e64 0x4f7fbc7987776dcc 0xdf3807cc79f00664 0x1be700f98f3e00cc

def z774 : W := mkw 0xec6cbecae8c719e4 0x1d8d97d95d18e33c 0xbcf9f8c389ce39e4 0x979f3f187139c73c

def z775 : W := mkw 0x5ff5eefb60102000 0x8bfebddf6c020400 0xfffffffff0303807 0xdffffffffe060700

def z776 : W := mkw 0x5ee4eefb60000000 0x8bdc9ddf6c000000 0xdcfe7ffff0000007 0x5b9fcffffe000000

def z777 : W := mkw 0x12800100036a0550 0x22500020006d40aa 0xffc008f00ffe07ff 0xbff8011e01ffc0ff

def z778 : W := mkw 0x6042b3dd3606de64 0x0c08567ba6c0dbcc 0x60c7fffff60ffe63 0xec18fffffec1ffcc

def z779 : W := mkw 0x0119805908112000 0x0023300b21022400 0x633988ff8831fffe 0xec67311ff1063fff

def z780 : W := mkw 0xa00a11049e87dee4 0x1401422093d0fbdc 0x20000000060ffe60 0x2400000000c1ffcc

def z781 : W := mkw 0xac2e1d06dec5dfa4 0x1585c3a0dbd8bbf4 0xdc3e0f0fffc1ff87 0x7b87c1e1fff83ff0

def z782 : W := mkw 0x5ff5eeca60000000 0x0bfebdd94c000000 0xdfffffcff0000007 0xdbfffff9fe000000

def z783 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xfffffffff030007f 0xdffffffffe06000f

def z784 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdffe7ffff0000005 0x1bffcffffe000000

def z785 : W := mkw 0x8c260d0256c08500 0x1184c1a04ad810a0 0x9c3e070ff7c00001 0x5387c0e1fef80000

def z786 : W := mkw 0x3fb75d375606de64 0x87f6eba6eac0dbcc 0xbf380833860ffe64 0x37e7010670c1ffcc

def z787 : W := mkw 0x1bbf50024dbdb000 0x4377ea0049b7b600 0xbffff00ffffff807 0xf7fffe01ffffff00

def z788 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x40c7f7cc760ffe61 0x4818fef98ec1ffcc

def z789 : W := mkw 0x84080d06da414780 0x108101a0db4828f0 0xdc380f0fffc1c787 0x7b8701e1fff838f0

def z790 : W := mkw 0x0c2e0c06cc81c280 0x0185c180d9903850 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z791 : W := mkw 0x9fbd4c33c9f92180 0xd3f7a986793f2430 0x9f38083389f00184 0x13e70106713e0030

def z792 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbffff0f00ffff87f 0xf7fffe1e01ffff0f

def z793 : W := mkw 0x7682bc6c356cdb34 0x2ed0578d86ad9b66 0x9f07f83c79f1f99c 0x53e0ff078f3e3f33

def z794 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xff3e0f0ffff1c787 0xffe7c1e1fffe38f0

def z795 : W := mkw 0x57d1aef920000000 0x0afa35df24000000 0xdffffffff0000007 0xdbfffffffe000000

def z796 : W := mkw 0x0d7f5fa00ed7b550 0x61afebf401daf6aa 0x403ffff00001fff8 0x4807fffe00003fff

def z797 : W := mkw 0x6119a05db8116aac 0x0c23340bb7022d55 0x633988fff831fffe 0xec67311fff063fff

def z798 : W := mkw 0x040a0d049e41c780 0x008141a093c838f0 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z799 : W := mkw 0x800a11049fedd780 0x5001422093fdbaf0 0x000000000fcfc780 0x2000000001f9f8f0

def z800 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xfffff8f00ffff807 0xffffff1e01ffff00

def z801 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xfc3f8f0fffc1ff87 0xff87f1e1fff83ff0

def z802 : W := mkw 0x4d75eefb60000000 0x89aebddf6c000000 0xdc3ffffff0000007 0x5b87fffffe000000

def z803 : W := mkw 0xe440affff2424fe4 0x9c8815fffe4849fc 0x40000ffff00007e0 0x080001fffe0000fc

def z804 : W := mkw 0x4d75eefb60000000 0x89aebddf6c000000 0x003ff70ff0000000 0x4007fee1fe000000

def z805 : W := mkw 0x12c00380032a0440 0x0258007000654088 0xffc00ff00ffe07ff 0xbff801fe01ffc0ff

def z806 : W := mkw 0x4042328024049000 0x0808465004809200 0x20c7f700760ff803 0xe418fee00ec1ff00

def z807 : W := mkw 0x1fbd4c3349f92110 0xe3f7a986693f2422 0x9f38083389f0019c 0x13e70106713e0033

def z808 : W := mkw 0x5ff5eefb612a0050 0xabfebddf6c25400a 0xfffffffffffe007f 0xffffffffffffc00f

def z809 : W := mkw 0x5fb5ec7b60000000 0x8bf6bd8f6c000000 0xdf3fff3ff0000007 0x5be7ffe7fe000000

def z810 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbcfff0000ffff801 0x779ffe0001ffff00

def z811 : W := mkw 0x7ee67fa2776e9554 0xafdccff44eedd2aa 0x9cc6770077ce0001 0x1398cee00ef9c000

def z812 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x9ffff7fff0000001 0xd3fffefffe000000

def z813 : W := mkw 0x9ee65fa257ee9550 0x73dccbf44afdd2aa 0x9cc6770077ce0001 0x1398cee00ef9c000

def z814 : W := mkw 0x53d1f2f9212c1000 0xca7a3e5f24258200 0x03c1f0f0000e0000 0x80783e1e0001c000

def z815 : W := mkw 0x4d75eefb60000000 0x89aebddf6c000000 0x40fffffff0000003 0xc81ffffffe000000

def z816 : W := mkw 0xfee63fa277ee9554 0x3fdcc7f44efdd2aa 0x9cc6770077ce0001 0x1398cee00ef9c000

def z817 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xffc60ffc7ffe07ff 0xfff8c1ff8fffc0ff

def z818 : W := mkw 0x8c2e0d06ded1e788 0x1185c1a0dbda3cf1 0xdc3e0f0ffff1c79f 0x7b87c1e1fffe38f3

def z819 : W := mkw 0x5ff5eefb612a0050 0xabfebddf6c25400a 0xfffffffff83e07ff 0xffffffffff07c0ff

def z820 : W := mkw 0x0119000488116280 0x0023200091022c50 0x633988ff8831fffe 0xec67311ff1063fff

def z821 : W := mkw 0x17d98ffd8b7b6ff8 0x22fb31ffb16f6dff 0x9cf9870f87cff801 0x539f30e1f0f9ff00

def z822 : W := mkw 0x8c2e1d06dec5d780 0x1185c3a0dbd8baf0 0xdcfe7f0fffcfc787 0x7b9fcfe1fff9f8f0

def z823 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdfffffffffc00007 0xfbfffffffff80000

def z824 : W := mkw 0x0c260c0244808000 0x0184c18048901000 0xdc3e0f0ff7c00007 0x5b87c1e1fef80000

def z825 : W := mkw 0x1bb75000052c9000 0x0376ea0000a59200 0xbffff0000ffff807 0xf7fffe0001ffff00

def z826 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbcfff00007cff803 0xf79ffe0000f9ff00

def z827 : W := mkw 0x9bbf5002cdbdb080 0x5377ea0059b7b610 0xbffff0038ffff807 0xf7fffe0071ffff00

def z828 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x60c7ffcc7e0fffe7 0xec18fff98fc1fffc

def z829 : W := mkw 0x0c2c0d06ca414780 0x018581a0d94828f0 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z830 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdffffffff8000787 0xfbffffffff0000f0

def z831 : W := mkw 0x0111805d00004a20 0x0022300ba0000944 0x633988ff8831fffe 0xec67311ff1063fff

def z832 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x9ffff0000ffff805 0x53fffe0001ffff00

def z833 : W := mkw 0x4d75eefb60000000 0x89aebddf6c000000 0x433ffffff0000006 0xc867fffffe000000

def z834 : W := mkw 0x4119e05da8116aa8 0x88233c0bb5022d55 0x6339f8ff8831fffe 0xec673f1ff1063fff

def z835 : W := mkw 0x6040b2cc20065a64 0x0c0816598400cb4c 0x60c7f7cc700ffe63 0xec18fef98e01ffcc

def z836 : W := mkw 0x4d35ec5b60000000 0x89a6bd8b6c000000 0xdf3ffffff0000007 0xdbe7fffffe000000

def z837 : W := mkw 0x53d1e2f920000000 0x8a7a3c5f24000000 0x43fffffff0000007 0xc87ffffffe000000

def z838 : W := mkw 0x6042b3ec3606de74 0x2c08567d86c0dbce 0x60c7f7fc760ffe7b 0xec18feff8ec1ffcf

def z839 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xfc3e0fcfffc1c7e7 0xff87c1f9fff838fc

def z840 : W := mkw 0x6042b3ddb606deec 0x0c08567bb6c0dbdd 0x63c7fffffe3fffff 0xec78ffffffc7ffff

def z841 : W := mkw 0x1aa6500005ac9000 0x4354ca0000b59200 0xbfc7f0000ffff807 0xf7f8fe0001ffff00

def z842 : W := mkw 0x5ff5eefb61382000 0xcbfebddf6c270400 0xdffffffff0300007 0xdbfffffffe060000

def z843 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x9ffff00007cff807 0xd3fffe0000f9ff00

def z844 : W := mkw 0x6042b3ccb606deec 0x0c08567996c0dbdd 0x60c7f7cc760ffffb 0xec18fef98ec1ffff

def z845 : W := mkw 0x5ff5eefb61a80000 0xcbfebddf6c350000 0xdffffffff1c00007 0xdbfffffffe380000

def z846 : W := mkw 0x1ea44c0240000000 0x03d4898048000000 0xdcfe7f0ff0000007 0x5b9fcfe1fe000000

def z847 : W := mkw 0x1aa6500005ac9000 0x4354ca0000b59200 0x9cc7f00007cff801 0x5398fe0000f9ff00

def z848 : W := mkw 0x5ff5eefb61280000 0x8bfebddf6c250000 0xfffffffffffe07ff 0xffffffffffffc0ff

def z849 : W := mkw 0x0826100004849000 0x0104c20000909200 0xbcc7f00007cff803 0xf798fe0000f9ff00

def z850 : W := mkw 0xa00a11049ed7ffec 0x1401422093dafffd 0x200000000ffffff8 0x2400000001ffffff

def z851 : W := mkw 0x693ff05dbc95faac 0x4d27fe0bb792bf55 0x003ff00ff001f800 0x4007fe01fe003f00

def z852 : W := mkw 0x8c2e0c06dc81c280 0x1185c180db903850 0xdc3e0f0fffc1c007 0x7b87c1e1fff83800

def z853 : W := mkw 0x5fb5ec5b60000000 0x8bf6bd8b6c000000 0xdfffff0ff0000007 0xdbffffe1fe000000

def z854 : W := mkw 0x5ff5eefb612a0050 0xabfebddf6c25400a 0xdffffffff00e0007 0xdbfffffffe01c000

def z855 : W := mkw 0x4975e2db60000000 0x892ebc5b6c000000 0x00fff70ff0000001 0x401ffee1fe000000

def z856 : W := mkw 0x8c2c0d02cac10580 0x118581a0595820b0 0xdc3e0f0fffc00787 0x7b87c1e1fff800f0

def z857 : W := mkw 0x53d1e2f921382000 0xca7a3c5f24270400 0x03c1f0f000300000 0x80783e1e00060000

def z858 : W := mkw 0x73d1f2d9213e386c 0x4e7a3e5b2427c70d 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z859 : W := mkw 0x8c2c0d06dac14780 0x118581a0db5828f0 0xdc380f0fffc00787 0x3b8701e1fff800f0

def z860 : W := mkw 0x082e10000dbdb000 0x4105c20001b7b600 0xbcfff0000ffff807 0xf79ffe0001ffff00

def z861 : W := mkw 0x8c2e0c02ccc18180 0x1185c18059983030 0xdc3e0f0fffc1c187 0x7b87c1e1fff83830

def z862 : W := mkw 0x8c2e0d025ec18500 0x1185c1a04bd830a0 0xdc3e0f0fffc1c007 0x7b87c1e1fff83800

def z863 : W := mkw 0x1ff54ea240000000 0x03fea9d448000000 0xdffffffff0000007 0xdbfffffffe000000

def z864 : W := mkw 0x5ee4aeea60000000 0x0bdc95dd4c000000 0xdffffffff0000007 0xdbfffffffe000000

def z865 : W := mkw 0x53d1e2f921280010 0xaa7a3c5f24250002 0x03c1f0f000300018 0x80783e1e00060003

def z866 : W := mkw 0x1bbf50008dbdb088 0x4377ea0011b7b611 0xbffff0000ffff99f 0xf7fffe0001ffff33

def z867 : W := mkw 0x5ff5eefb61280000 0x8bfebddf6c250000 0xfffffffff03e0007 0xdffffffffe07c000

def z868 : W := mkw 0x53d1e2f9212a0050 0xaa7a3c5f2425400a 0x03c1f0f0000e0000 0x80783e1e0001c000

def z869 : W := mkw 0x604233843606de64 0x0c08467086c0dbcc 0x20c7f700760ffe63 0xe418fee00ec1ffcc

def z870 : W := mkw 0xe440afce72424f64 0x1c8815f9ce4849ec 0x400007cc70000660 0x080000f98e0000cc

def z871 : W := mkw 0x4c642e8260000000 0x098c85d04c000000 0xdcfe7f0ff0000007 0x5b9fcfe1fe000000

def z872 : W := mkw 0xac2e0d06dec3cfe4 0x1585c1a0dbd879fc 0xdc3e0f0fffc1c7e7 0x7b87c1e1fff838fc

def z873 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xfffffffff0000667 0xfffffffffe0000cc

def z874 : W := mkw 0x5ee46ea260000000 0x8bdc8dd44c000000 0xdffe7ffff0000007 0xdbffcffffe000000

def z875 : W := mkw 0x6042b3cc3646df64 0x0c08567986c8dbec 0x60c7f7cc7fcfffe3 0xec18fef98ff9fffc

def z876 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdf3e0fffffc1c787 0xfbe7c1fffff838f0

def z877 : W := mkw 0x139b50000dbdb000 0x42736a0001b7b600 0xbfc1f0000ffff807 0xb7f83e0001ffff00

def z878 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x20c7f7cc760ff861 0xc418fef98ec1ff0c

def z879 : W := mkw 0x6042b3ccb606dee4 0x0c08567996c0dbdc 0x60c7ffcff60fffe3 0xec18fff9fec1fffc

def z880 : W := mkw 0x6440afff72424f74 0xac8815ffee4849ee 0x40000ffff00007f8 0x080001fffe0000ff

def z881 : W := mkw 0x8c2e1d06dec5d780 0x1185c3a0dbd8baf0 0xfc3e0f0fffcfff87 0x7f87c1e1fff9fff0

def z882 : W := mkw 0x0c2e0d024ec18500 0x0185c1a049d830a0 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z883 : W := mkw 0x093f50000c95b000 0x4127ea000192b600 0xbcfff0000fcff807 0xf79ffe0001f9ff00

def z884 : W := mkw 0x4042b3cc3604d600 0x0808567986c09ac0 0x60c7f7cc760ffe03 0xec18fef98ec1ffc0

def z885 : W := mkw 0x1aae10000dad9000 0x0355c20001b5b200 0xbffff0000ffff807 0xf7fffe0001ffff00

def z886 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xfffffffff001f807 0xfffffffffe003f00

def z887 : W := mkw 0x8c2c0d06dac14780 0x118581a0db5828f0 0xdc380f0ff9c1c786 0x7b8701e1ff3838f0

def z888 : W := mkw 0x1bbf50134dbdb000 0xc377ea0269b7b600 0xbffff0038ffff807 0xf7fffe0071ffff00

def z889 : W := mkw 0x200211041606de64 0x0400422082c0dbcc 0x60c7f70c760ffe63 0xec18fee18ec1ffcc

def z890 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x60c7fffc760ffffb 0xec18ffff8ec1ffff

def z891 : W := mkw 0x5ee67fa267ee9550 0xebdccff44cfdd2aa 0x9cc6770077ce0001 0x1398cee00ef9c000

def z892 : W := mkw 0x0002110016049400 0x0000422002c09280 0x20c7f700760ff803 0xe418fee00ec1ff00

def z893 : W := mkw 0x53d1f2f9213c3828 0xca7a3e5f24278705 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z894 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbffff0000fffffff 0xf7fffe0001ffffff

def z895 : W := mkw 0xe440afdff2424fec 0x1c8815fbfe4849fd 0x40000ffff00007f8 0x080001fffe0000ff

def z896 : W := mkw 0x5ff5eefb60400100 0x8bfebddf6c080020 0xdffffffff9c00187 0xdbffffffff380030

def z897 : W := mkw 0x1bbf50000c859000 0x0377ea000190b200 0xbffff0000fcff807 0xf7fffe0001f9ff00

def z898 : W := mkw 0x800a11049ffff7d0 0x7001422093fffefa 0x200000000ffffff8 0x2400000001ffffff

def z899 : W := mkw 0x6440affdb2424ffc 0x2c8815ffb64849ff 0x40000ffff00007f8 0x080001fffe0000ff

def z900 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e0f0fffc00785 0x1b87c1e1fff800f0

def z901 : W := mkw 0x6042b3c836069444 0x0c08567906c0d288 0x60c7f7cc760ff803 0xec18fef98ec1ff00

def z902 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x60ffffcff60ffe67 0xec1ffff9fec1ffcc

def z903 : W := mkw 0x4975e2db60000000 0x892ebc5b6c000000 0x403ff7cff0000000 0x4807fef9fe000000

def z904 : W := mkw 0x200a11049e07dee4 0x0401422093c0fbdc 0x200000000e0fffe0 0x2400000001c1fffc

def z905 : W := mkw 0x12c002a0012a0050 0x225800540025400a 0xffc008f00ffe07ff 0xbff8011e01ffc0ff

def z906 : W := mkw 0x0002914c1604de20 0x0000522982c09bc4 0x60c7f7cc760ffe63 0xec18fef98ec1ffcc

def z907 : W := mkw 0x16800d20036a0550 0x22d001a4006d40aa 0xff0008f00ffe07fe 0xbfe0011e01ffc0ff

def z908 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x9c3e070fffc1c781 0x7387c0e1fff838f0

def z909 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdcffff0ff0000007 0x5b9fffe1fe000000

def z910 : W := mkw 0xac2e1d06ded7ffec 0x1585c3a0dbdafffd 0xfc3e0f0fffffffff 0x7f87c1e1ffffffff

def z911 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x633988ff8031fff8 0xcc67311ff0063fff

def z912 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x63fff8ff8831ffff 0xec7fff1ff1063fff

def z913 : W := mkw 0x9bbf50025dbdb000 0x5377ea004bb7b600 0xbffff0007ffff807 0xf7fffe000fffff00

def z914 : W := mkw 0x1bbf50118dbdb088 0x4377ea0231b7b611 0xbffff0038ffff807 0xf7fffe0071ffff00

def z915 : W := mkw 0x6042338036069444 0x0c08467006c0d288 0x00c7f700760ff801 0x4018fee00ec1ff00

def z916 : W := mkw 0x5ff5eefb60102828 0x8bfebddf6c020505 0xfffffffff8303fff 0xffffffffff0607ff

def z917 : W := mkw 0x4d35ec5b60000000 0x89a6bd8b6c000000 0x9c3ff70ff0000001 0x5387fee1fe000000

def z918 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdffffffff00007ff 0xdbfffffffe0000ff

def z919 : W := mkw 0x8c260d06d6c0c780 0x1184c1a0dad818f0 0xdc3e0f0ff7c00787 0x5b87c1e1fef800f0

def z920 : W := mkw 0x4042b2cc2404da20 0x0808565984809b44 0x60c7f7cc760ffe63 0xec18fef98ec1ffcc

def z921 : W := mkw 0xe042b3cc36c6df64 0x1c08567986d8dbec 0x60c7f7cc77cffe63 0xec18fef98ef9ffcc

def z922 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x63f988ff8e3fffff 0xec7f311ff1c7ffff

def z923 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e070ff7c1c603 0x7b87c0e1fef838c0

def z924 : W := mkw 0x8c260d0656c0c700 0x1184c1a0cad818e0 0xdc3e0f0ff7c1c607 0x7b87c1e1fef838c0

def z925 : W := mkw 0x1bb7500005bcb000 0x4376ea0000b79600 0xbfc7f00007fff803 0xf7f8fe0000ffff00

def z926 : W := mkw 0x4551aefb60000000 0x88aa35df6c000000 0x43fffffff0000007 0xc87ffffffe000000

def z927 : W := mkw 0xe042b3ccb646dfe4 0x1c08567996c8dbfc 0x60c7f7cc760fffe3 0xec18fef98ec1fffc

def z928 : W := mkw 0x8c2e0d06ded1efa8 0x1185c1a0dbda3df5 0xdc3e0f0fffc1ff87 0x7b87c1e1fff83ff0

def z929 : W := mkw 0x1fbd4c2249b92000 0xc3f7a98449372400 0x9f38000009f00004 0x13e70000013e0000

def z930 : W := mkw 0x0119001188112088 0x0023200231022411 0x633988f38831fffe 0xec67311e71063fff

def z931 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x40c7f7cc760ff803 0xc818fef98ec1ff00

def z932 : W := mkw 0x0008804c88014aa0 0x0001100991002954 0x633988ff8831fffe 0xec67311ff1063fff

def z933 : W := mkw 0xac2e1d06dec7dfe4 0x1585c3a0dbd8fbfc 0xfcffff0fffcfffe7 0xff9fffe1fff9fffc

def z934 : W := mkw 0x5ff5eefb613a2878 0xabfebddf6c27450f 0xfffffffff03e387f 0xdffffffffe07c70f

def z935 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e0f0ff9c1c784 0x5b87c1e1ff3838f0

def z936 : W := mkw 0x4d75eedb60000000 0x89aebddb6c000000 0xdcffffcff0000007 0xdb9ffff9fe000000

def z937 : W := mkw 0x0c240c0240000000 0x0184818048000000 0xdcffff0ff0000007 0xdb9fffe1fe000000

def z938 : W := mkw 0x9fbd4c0249f92100 0x53f7a980493f2420 0x9f38000009f00004 0x13e70000013e0000

def z939 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xfcfe0f0fffcfc787 0xff9fc1e1fff9f8f0

def z940 : W := mkw 0x73d1b2f9213e387c 0x2e7a365f2427c70f 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z941 : W := mkw 0x0d354c0240000000 0x01a6a98048000000 0xdc3fff0ff0000007 0x5b87ffe1fe000000

def z942 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e0f0ff7c1c781 0x5b87c1e1fef838f0

def z943 : W := mkw 0x13935000053cb000 0x42726a0000a79600 0xbfc7f0000ffff807 0xf7f8fe0001ffff00

def z944 : W := mkw 0x8c2e0d02dec18580 0x1185c1a05bd830b0 0xdc3e0f0fffc00187 0x5b87c1e1fff80030

def z945 : W := mkw 0x53d1e2f9213a2878 0xaa7a3c5f2427450f 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z946 : W := mkw 0x56c02fa0236a0550 0x2ad805f4046d40aa 0xffc67ff07ffe07ff 0xbff8cffe0fffc0ff

def z947 : W := mkw 0x5ff5eefb60102828 0x8bfebddf6c020505 0xdffffffff0003807 0xdbfffffffe000700

def z948 : W := mkw 0x5bf5e2fb60000000 0x8b7ebc5f6c000000 0x43fff7fff0000003 0xc87ffefffe000000

def z949 : W := mkw 0x5ee46ea260000000 0x8bdc8dd44c000000 0x9cfe770ff0000001 0x539fcee1fe000000

def z950 : W := mkw 0xa00a11049fffffe4 0x5401422093fffffc 0x200000000fffffe0 0x2400000001fffffc

def z951 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xfc3e0f0ffff1c7ff 0x7f87c1e1fffe38ff

def z952 : W := mkw 0x0c240d0242400500 0x018481a0484800a0 0xdc3e0f0ff7c00007 0x5b87c1e1fef80000

def z953 : W := mkw 0x5ff5eefb60000828 0x8bfebddf6c000105 0xdffffffff000007f 0xdbfffffffe00000f

def z954 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x63c7f7cc7e3ffe67 0xec78fef98fc7ffcc

def z955 : W := mkw 0x6002b14c3604de24 0x0c00562986c09bc4 0x60c7f70c760ffe03 0xec18fee18ec1ffc0

def z956 : W := mkw 0xa00a11049fefdff4 0x3401422093fdfbfe 0x200000000ffffff8 0x2400000001ffffff

def z957 : W := mkw 0x1aae50000dbdb000 0x4355ca0001b7b600 0xbcc7f0000ffff803 0xf798fe0001ffff00

def z958 : W := mkw 0x4c24ac4a60000000 0x098495894c000000 0xdc3fff0ff0000007 0x5b87ffe1fe000000

def z959 : W := mkw 0x7ff5eefb60020864 0x8ffebddf6c00410c 0xdffffffff0000067 0xdbfffffffe00000c

def z960 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xffc18ff00fffffff 0xfff831fe01ffffff

def z961 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xbfc008f00ffe07fc 0xb7f8011e01ffc0ff

def z962 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x9fffff3ff0000005 0x53ffffe7fe000000

def z963 : W := mkw 0x8c2e5d06dec5d780 0x5185cba0dbd8baf0 0xdc3e7f0fffc1c787 0x7b87cfe1fff838f0

def z964 : W := mkw 0x8c2c0c06c8c14380 0x11858180d9182870 0xdc3e0f0ff9c1c787 0x7b87c1e1ff3838f0

def z965 : W := mkw 0x1bbf50110dbdb008 0x4377ea0221b7b601 0xbffff0300ffff81f 0xf7fffe0601ffff03

def z966 : W := mkw 0x8c2e0d06dec3c7d0 0x3185c1a0dbd878fa 0xdc3e0f0fffc1c7ff 0x7b87c1e1fff838ff

def z967 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xdfc00ff00ffe07fd 0x1bf801fe01ffc0ff

def z968 : W := mkw 0x004213841606d640 0x0008427082c0dac8 0x60c7f7cc760ffe63 0xec18fef98ec1ffcc

def z969 : W := mkw 0x6042b2cc3404da24 0x0c08565986809b44 0x60c7f7cc760ff803 0xec18fef98ec1ff00

def z970 : W := mkw 0xa00a11049ec7d7c4 0x1401422093d8faf8 0x000000000fcfc780 0x2000000001f9f8f0

def z971 : W := mkw 0x5ff5eefb61280010 0xabfebddf6c250002 0xdffffffff030001f 0xdbfffffffe060003

def z972 : W := mkw 0x800a11049ec5d780 0x1001422093d8baf0 0x200000000fcfff80 0x2400000001f9fff0

def z973 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbffff00007fff801 0xd7fffe0000ffff00

def z974 : W := mkw 0x082e01049e81c680 0x0105c02093d038d0 0xdc3e0f0fffc1c787 0x7b87c1e1fff838f0

def z975 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x433988ff8831fffc 0x4867311ff1063fff

def z976 : W := mkw 0x8c2e0d06dec3c7c0 0x1185c1a0dbd878f8 0xfc3e0f0fffcfc7e7 0x7f87c1e1fff9f8fc

def z977 : W := mkw 0x0c240c0240400100 0x0184818048080020 0xdc3e0f0ff9c00187 0x5b87c1e1ff380030

def z978 : W := mkw 0x4c246c0260000000 0x89848d804c000000 0xdc3e7f0ff0000007 0x5b87cfe1fe000000

def z979 : W := mkw 0x5ff5eefb60400110 0xabfebddf6c080022 0xdffffffff000019f 0xdbfffffffe000033

def z980 : W := mkw 0x1bbf50118dbdb088 0x4377ea0231b7b611 0xfffff8f38fffffff 0xffffff1e71ffffff

def z981 : W := mkw 0x1fbd4c0249b92000 0x43f7a98049372400 0x9f38080389f00004 0x13e70100713e0000

def z982 : W := mkw 0x4042b3c826069440 0x0808567904c0d288 0x60c7f7cc760ffe63 0xec18fef98ec1ffcc

def z983 : W := mkw 0xa00a11049ec5dfa4 0x1401422093d8bbf4 0x000000000fc1ff80 0x2000000001f83ff0

def z984 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbfc7f0000ffff801 0xb7f8fe0001ffff00

def z985 : W := mkw 0x9fbd4c13c9f92188 0x53f7a982793f2431 0x9f38083389f0019c 0x13e70106713e0033

def z986 : W := mkw 0x1bbf50008dbdb080 0x4377ea0011b7b610 0xbffff8038ffff987 0xf7ffff0071ffff30

def z987 : W := mkw 0x5ff5eefb616a0150 0xabfebddf6c2d402a 0xfffffffff9fe01ff 0xdfffffffff3fc03f

def z988 : W := mkw 0x4440afffe2424ff8 0xa88815fffc4849ff 0x40000ffff00007f8 0x080001fffe0000ff

def z989 : W := mkw 0x16800d0003680500 0x02d001a0006d00a0 0xffc00ff00ffe07ff 0xbff801fe01ffc0ff

def z990 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdf3e0f3ffff1c79f 0x7be7c1e7fffe38f3

def z991 : W := mkw 0x4040a2c820000000 0x0808145904000000 0x40ffffcff0000007 0xc81ffff9fe000000

def z992 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x60c7f7cc700ffe60 0xcc18fef98e01ffcc

def z993 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xfffff70c7ffff807 0xfffffee18fffff00

def z994 : W := mkw 0x6042b3ddb606deec 0x0c08567bb6c0dbdd 0x60c7f7cff60ffe63 0xec18fef9fec1ffcc

def z995 : W := mkw 0x5ff5eefb61280000 0x8bfebddf6c250000 0xdffffffff7ce0007 0xdbfffffffef9c000

def z996 : W := mkw 0x5bf5e2d920000000 0x0b7ebc5b24000000 0xdffffffff0000007 0xdbfffffffe000000

def z997 : W := mkw 0x5ff5eefb61280000 0x8bfebddf6c250000 0xdffffffff9f00007 0xdbffffffff3e0000

def z998 : W := mkw 0x1fbd4c33c9792198 0xa3f7a986792f2433 0x9f38083389f0019c 0x13e70106713e0033

def z999 : W := mkw 0x893fd05fdc95faa8 0x5127fa0bfb92bf55 0x003ff00ff001f800 0x4007fe01fe003f00

def z1000 : W := mkw 0x5ff5eefb60102008 0x8bfebddf6c020401 0xdffffffff030001f 0xdbfffffffe060003

def z1001 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbff9f0000ffff804 0xb7ff3e0001ffff00

def z1002 : W := mkw 0x12c003a0036a0550 0x22580074006d40aa 0xbfc000f00ffe07ff 0xb7f8001e01ffc0ff

def z1003 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x60c7f7cc7e3ffffb 0xec18fef98fc7ffff

def z1004 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdcfffffff0000001 0x5b9ffffffe000000

def z1005 : W := mkw 0x8c2c0c02c8c10180 0x1185818059182030 0xdc380f0ff9c00184 0x1b8701e1ff380030

def z1006 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xfffff8000fffff87 0xffffff0001fffff0

def z1007 : W := mkw 0x493ff05fec95faa8 0xc927fe0bfd92bf55 0x003ff00ff001f800 0x4007fe01fe003f00

def z1008 : W := mkw 0x5ff56ea260000000 0x8bfeadd44c000000 0xdfffff0ff0000007 0xdbffffe1fe000000

def z1009 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x20c7f70c760ffe61 0x6418fee18ec1ffcc

def z1010 : W := mkw 0x800a11049ffdffa8 0x5001422093ffbff5 0x200000000ffffff8 0x2400000001ffffff

def z1011 : W := mkw 0x56c06fa0236a0550 0xaad80df4046d40aa 0xffc07ff00ffe07ff 0xbff80ffe01ffc0ff

def z1012 : W := mkw 0x5ff5eefb61680110 0xabfebddf6c2d0022 0xfffffffffffe019f 0xffffffffffffc033

def z1013 : W := mkw 0x6042b3dd3606de6c 0x0c08567ba6c0dbcd 0x60c7f7fc760ffe7b 0xec18feff8ec1ffcf

def z1014 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xffc7fff00ffe07ff 0xfff8fffe01ffc0ff

def z1015 : W := mkw 0x8c2e0d26dec1c790 0x3185c1a4dbd838f2 0xdc3e0f3fffc1c79f 0x7b87c1e7fff838f3

def z1016 : W := mkw 0xdff5eefb60c00100 0x9bfebddf6c180020 0xdffffffff1c00007 0xdbfffffffe380000

def z1017 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xdf3ffffff0000004 0x5be7fffffe000000

def z1018 : W := mkw 0x6042b3cc3646df74 0x2c08567986c8dbee 0x60c7f7cc760ffffb 0xec18fef98ec1ffff

def z1019 : W := mkw 0x73d1f2f9213e3864 0xce7a3e5f2427c70c 0x23c1f0f0003e3860 0x84783e1e0007c70c

def z1020 : W := mkw 0x5ff5eefb60020040 0x8bfebddf6c004008 0xfffffffff00e0067 0xdffffffffe01c00c

def z1021 : W := mkw 0x0c2e0d065e81c600 0x0185c1a0cbd038c0 0xdc3e0f0fffc1c607 0x7b87c1e1fff838c0

def z1022 : W := mkw 0x4c64aefb60000000 0x898c95df6c000000 0xdcfffffff0000007 0xdb9ffffffe000000

def z1023 : W := mkw 0x6440afec32424f74 0x2c8815fd864849ee 0x400007cc70000660 0x080000f98e0000cc

def z1024 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x63c7f7fc763ffe7b 0xec78feff8ec7ffcf

def z1025 : W := mkw 0x16c00ea001280000 0x02d801d400250000 0xffc00ff00ffe07ff 0xbff801fe01ffc0ff

def z1026 : W := mkw 0x13995000093d3000 0x42732a000127a600 0xbff9f0000ffff807 0xf7ff3e0001ffff00

def z1027 : W := mkw 0x1fb54c3340000000 0x83f6a98668000000 0xdfffff3ff0000007 0xdbffffe7fe000000

def z1028 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xfffff0c00ffffe67 0xfffffe1801ffffcc

def z1029 : W := mkw 0x139b10000d3db000 0x0273620001a7b600 0xbffff0000ffff807 0xf7fffe0001ffff00

def z1030 : W := mkw 0x73d1f2f9212e1874 0xae7a3e5f2425c30e 0x23c1f0f0003e3878 0x84783e1e0007c70f

def z1031 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0xbffff8300ffff99f 0xf7ffff0601ffff33

def z1032 : W := mkw 0x200a11049f7ffffc 0x2401422093efffff 0x200000000ffffff8 0x2400000001ffffff

def z1033 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0x43fffffff0000000 0xc87ffffffe000000

def z1034 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0xdc3e0fffffc1c7ff 0x7b87c1fffff838ff

def z1035 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0xff3988ff8ff1ffff 0xffe7311ff1fe3fff

def z1036 : W := mkw 0x8c2e1d06dec5d780 0x1185c3a0dbd8baf0 0xdc3fff0fffc1ff87 0x7b87ffe1fff83ff0

def z1037 : W := mkw 0x4151a2d920000000 0x082a345b24000000 0x40fff7cff0000003 0xc81ffef9fe000000

def z1038 : W := mkw 0x8c240d06d2404780 0x118481a0da4808f0 0xdc3e0f0fffc00787 0x7b87c1e1fff800f0

def z1039 : W := mkw 0x6042b3c836069c64 0x0c08567906c0d38c 0x20c7f7c0760ff863 0xe418fef80ec1ff0c

def z1040 : W := mkw 0xac2e1d06dec7d7c4 0x1585c3a0dbd8faf8 0xdc3e0f0fffcfc787 0x7b87c1e1fff9f8f0

def z1041 : W := mkw 0x0c2c0c0248810000 0x0185818049102000 0xdc3e0f0ff9c00007 0x5b87c1e1ff380000

def z1042 : W := mkw 0x800a11049ed5f780 0x5001422093dabef0 0x000000000fc1ff80 0x2000000001f83ff0

def z1043 : W := mkw 0xe440afeef2424ff4 0x3c8815fdde4849fe 0x40000ffff00007f8 0x080001fffe0000ff

def z1044 : W := mkw 0x4d35ec5b60000000 0x89a6bd8b6c000000 0x403fff0ff0000000 0x4807ffe1fe000000

def z1045 : W := mkw 0x1bbf50000dbdb000 0x4377ea0001b7b600 0x9cfff0000fcff807 0x739ffe0001f9ff00

def z1046 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0xfcc7f7cc7fcffe67 0xff98fef98ff9ffcc

def z1047 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x233988f38831fffc 0xa467311e71063fff

def z1048 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xfffffffff60e0007 0xfffffffffec1c000

def z1049 : W := mkw 0x8c260d0256c08500 0x1184c1a04ad810a0 0xdc3e0f0fffc00787 0x7b87c1e1fff800f0

def z1050 : W := mkw 0x0002100004049000 0x0000420000809200 0x60c7f70c760ff803 0xec18fee18ec1ff00

def z1051 : W := mkw 0x5ff5eefb60000000 0x8bfebddf6c000000 0xfffffffff8300007 0xffffffffff060000

def z1052 : W := mkw 0x0002100004049000 0x0000420000809200 0xbcc7f0000fcff807 0xf798fe0001f9ff00

def z1053 : W := mkw 0x4040a3cc22024e60 0x08081479844049cc 0x60c7f7cc760ffe63 0xec18fef98ec1ffcc

def z1054 : W := mkw 0x96c00fa2536a0550 0x32d801f44a6d40aa 0xffc00ff07ffe07ff 0xbff801fe0fffc0ff

def z1055 : W := mkw 0x0119805d88116aa8 0x0023300bb1022d55 0x633808ff8831fffc 0x2c67011ff1063fff

def z1056 : W := mkw 0x4935e05b60000000 0x8926bc0b6c000000 0x403ff70ff0000003 0x4807fee1fe000000

def z1057 : W := mkw 0x8c2e0d06dec1c780 0x1185c1a0dbd838f0 0x9c3e070fffc1c007 0x7387c0e1fff83800

def z1058 : W := mkw 0x1bb7500005ac9000 0x4376ea0000b59200 0xbffff00007cff807 0xf7fffe0000f9ff00

def z1059 : W := mkw 0x8c2c0d06dac14780 0x118581a0db5828f0 0xdc3e0f0ff9c00787 0x5b87c1e1ff3800f0

def z1060 : W := mkw 0x882e0106de81c680 0x1105c020dbd038d0 0xdc3e070fffc1c607 0x7b87c0e1fff838c0

def z1061 : W := mkw 0x6042b2c824069864 0x0c0856590480d30c 0x60c7f7cc760ff863 0xec18fef98ec1ff0c

def z1062 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x20c7f70c760ff803 0xe418fee18ec1ff00

def z1063 : W := mkw 0x8c2e0c06dcc1c380 0x1185c180db983870 0xdc3e0f0ff9c1c187 0x5b87c1e1ff383830

def z1064 : W := mkw 0x16c00fa0036a0550 0x22d801f4006d40aa 0xbfc007f00ffe07f9 0xb7f800fe01ffc0ff

def z1065 : W := mkw 0x0119001588116aa8 0x00232002b1022d55 0x633808f38831fffe 0xac67011e71063fff

def z1066 : W := mkw 0x0008000488116aa8 0x0001000091022d55 0x633808ff8831fffe 0xec67011ff1063fff

def z1067 : W := mkw 0x1fbd4c33c9b92088 0xc3f7a98679372411 0x9f38083389f0019c 0x13e70106713e0033

def z1068 : W := mkw 0x1fb5cc5b40000000 0x03f6b98b68000000 0xdffffffff0000007 0xdbfffffffe000000

def z1069 : W := mkw 0x6042b3cc3606de64 0x0c08567986c0dbcc 0x40c7f70c760ffe03 0x6818fee18ec1ffc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z8]),(0,[z0,z2,z3,z4,z9,z10,z11])],[(0,[z12,z0,z2,z3,z4,z5,z10]),(1,[z13,z2,z3,z14,z5,z10]),(1,[z15,z0,z3,z4,z16,z10]),(0,[z0,z2,z3,z17,z4,z5,z10]),(0,[z0,z2,z3,z18,z4,z5,z10])],[(0,[z0,z2,z3,z4,z19,z5,z10]),(0,[z20,z0,z2,z3,z4,z5,z10]),(0,[z13,z0,z2,z3,z14,z5,z10]),(0,[z0,z2,z3,z4,z5,z21,z10]),(0,[z22,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z23,z5,z10]),(0,[z0,z2,z3,z4,z5,z24,z10]),(0,[z0,z2,z3,z4,z5,z10,z25]),(1,[z0,z2,z3,z26,z5,z27])],[(0,[z28,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z29,z10]),(0,[z30,z0,z2,z3,z31,z5,z10]),(0,[z32,z0,z2,z3,z4,z5,z10]),(0,[z33,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z34,z10]),(0,[z0,z2,z3,z4,z5,z35,z10]),(0,[z36,z0,z2,z3,z4,z5,z10])],[(1,[z0,z2,z3,z37,z5,z10]),(0,[z0,z2,z3,z38,z4,z5,z10]),(0,[z0,z2,z3,z39,z4,z40,z5]),(0,[z0,z41,z2,z42,z3,z5,z10]),(0,[z0,z43,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z44,z5,z10])],[(0,[z45,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z46,z4,z5,z10]),(0,[z0,z2,z3,z47,z48,z5,z10]),(1,[z0,z49,z2,z4,z5,z10]),(0,[z0,z2,z3,z50,z51,z4,z10])],[(0,[z0,z2,z3,z4,z52,z5,z10]),(0,[z53,z0,z2,z3,z4,z5,z54]),(0,[z0,z2,z3,z26,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z10,z55])]],
   [[(1,[z0,z2,z3,z31,z5,z10]),(0,[z56,z0,z2,z3,z4,z5,z10])],[(0,[z0,z57,z2,z3,z4,z5,z10]),(0,[z58,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z59,z5,z10]),(0,[z0,z60,z2,z3,z4,z5,z10]),(0,[z0,z61,z41,z2,z3,z4,z5]),(1,[z0,z2,z3,z50,z51,z10])],[(0,[z0,z2,z3,z4,z5,z10,z62]),(0,[z0,z2,z3,z4,z5,z10,z63]),(0,[z0,z64,z41,z2,z3,z4,z5]),(0,[z0,z65,z2,z3,z4,z5,z10]),(0,[z0,z66,z2,z3,z4,z5,z10])],[(0,[z0,z67,z2,z3,z4,z5,z10])],[(0,[z2,z68,z3,z69,z4,z5,z10]),(0,[z0,z2,z3,z70,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z71,z10])],[(1,[z0,z72,z2,z3,z4,z5])],[(0,[z73,z0,z2,z3,z4,z74,z10]),(0,[z75,z2,z3,z4,z76,z5,z10]),(0,[z0,z2,z3,z77,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z78]),(0,[z0,z2,z3,z4,z79,z5,z11])],[(0,[z73,z0,z2,z3,z4,z80,z10]),(1,[z0,z81,z82,z4,z5,z10]),(0,[z0,z2,z3,z51,z47,z5,z10]),(0,[z0,z2,z3,z4,z5,z83,z10]),(0,[z0,z61,z2,z3,z4,z5,z8])]],
   [[(0,[z0,z2,z3,z4,z5,z84,z10]),(0,[z0,z85,z2,z3,z4,z5,z10]),(0,[z0,z2,z86,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z87,z10]),(0,[z88,z0,z2,z3,z4,z5,z10]),(0,[z89,z0,z2,z3,z4,z5,z10]),(0,[z0,z90,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z91,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z92]),(1,[z0,z61,z2,z4,z5,z93]),(0,[z94,z0,z2,z3,z4,z5,z10])],[(0,[z95,z0,z96,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z97]),(0,[z0,z1,z3,z4,z5,z98,z10]),(0,[z0,z2,z3,z99,z4,z5,z10]),(0,[z0,z2,z3,z100,z4,z5,z10])],[(0,[z0,z2,z101,z3,z4,z5,z10]),(0,[z13,z2,z3,z14,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z102,z10])],[(0,[z0,z2,z3,z103,z5,z104,z10]),(1,[z0,z2,z3,z105,z5,z10])],[(0,[z0,z2,z3,z4,z5,z106,z10]),(0,[z0,z2,z3,z107,z4,z5,z10]),(0,[z0,z108,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z109,z10]),(0,[z0,z2,z3,z4,z5,z110,z10]),(0,[z111,z0,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z5,z112])],[(1,[z95,z113,z3,z4,z5,z10]),(0,[z114,z0,z2,z3,z4,z115,z10])],[(0,[z0,z2,z3,z4,z5,z116,z10]),(0,[z0,z2,z3,z117,z4,z5,z10]),(0,[z0,z118,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z119,z5,z10]),(0,[z0,z2,z4,z5,z10,z120,z11]),(0,[z0,z2,z3,z4,z79,z9,z10])]],
   [[(0,[z95,z0,z121,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z122]),(0,[z0,z81,z2,z3,z4,z5,z10]),(0,[z123,z0,z41,z2,z3,z5,z10]),(0,[z0,z2,z124,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z125,z10]),(0,[z0,z72,z2,z3,z4,z5,z10])],[(0,[z0,z2,z126,z3,z4,z5,z10]),(0,[z0,z2,z3,z14,z40,z5,z10]),(0,[z0,z82,z2,z3,z4,z5,z10]),(0,[z0,z96,z2,z3,z46,z5,z10])],[(0,[z127,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z128,z10])],[(0,[z0,z2,z3,z4,z129,z5,z10]),(0,[z0,z130,z2,z3,z4,z5,z10]),(0,[z0,z131,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z132,z5,z10]),(0,[z0,z2,z3,z40,z48,z5,z10]),(0,[z0,z3,z4,z5,z98,z10,z6]),(0,[z0,z2,z3,z105,z4,z5,z10]),(0,[z0,z133,z2,z3,z4,z5,z10]),(1,[z0,z41,z2,z3,z5,z134])],[(0,[z0,z135,z2,z3,z136,z5,z10]),(0,[z137,z138,z0,z2,z3,z4,z10])],[(0,[z0,z2,z3,z139,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z140]),(0,[z0,z2,z3,z141,z4,z5,z10]),(0,[z142,z0,z2,z3,z4,z5,z10])]],
   [[(0,[z143,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z144,z4,z5,z10]),(0,[z0,z145,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z146,z5,z10]),(0,[z0,z41,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z79,z9])],[(0,[z0,z2,z3,z147,z4,z5,z10]),(0,[z0,z2,z3,z148,z40,z5,z10]),(0,[z149,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z150,z10]),(0,[z0,z151,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z152,z10])],[(0,[z13,z0,z2,z3,z19,z5,z10]),(0,[z0,z2,z3,z4,z40,z5,z10]),(0,[z0,z2,z3,z153,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z154]),(0,[z155,z0,z2,z3,z4,z5,z10])],[(0,[z138,z0,z2,z69,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z156]),(0,[z0,z2,z3,z4,z5,z10,z134])],[(1,[z0,z2,z3,z4,z115,z10]),(0,[z0,z2,z3,z4,z5,z157,z10]),(0,[z0,z2,z42,z3,z4,z5,z10]),(0,[z0,z2,z3,z50,z4,z5,z10])],[(0,[z0,z158,z2,z3,z4,z5,z10]),(0,[z0,z72,z2,z3,z4,z48,z5])],[(0,[z0,z159,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z160,z4,z5,z10]),(1,[z30,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z98,z10]),(0,[z0,z2,z3,z161,z4,z5,z10])]],
   [[(0,[z162,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z163,z10]),(0,[z0,z2,z3,z4,z5,z164,z10])],[(0,[z0,z2,z3,z4,z165,z5,z10]),(0,[z0,z2,z3,z166,z4,z5,z10])],[(0,[z167,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z168,z4,z5,z10]),(0,[z0,z2,z42,z4,z48,z5,z10]),(0,[z169,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z148,z4,z170,z10]),(0,[z0,z2,z3,z171,z4,z5,z10])],[(0,[z0,z2,z3,z172,z4,z5,z10]),(0,[z173,z0,z2,z3,z4,z5,z10])],[(0,[z174,z0,z2,z3,z4,z5,z10]),(0,[z175,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z176,z40,z5,z10]),(0,[z15,z0,z2,z3,z4,z177,z10]),(0,[z0,z2,z176,z4,z48,z5,z10]),(0,[z0,z2,z178,z4,z179,z5,z10])],[(0,[z95,z113,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z180,z5,z104,z10]),(1,[z0,z2,z3,z181,z5,z10]),(0,[z0,z2,z4,z5,z8,z10,z93]),(0,[z0,z2,z3,z182,z4,z5,z10])],[(0,[z0,z2,z183,z3,z4,z5,z10]),(0,[z0,z184,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z185,z5,z10]),(0,[z0,z2,z3,z5,z10,z186,z11]),(0,[z0,z2,z3,z187,z4,z5,z10])],[]],
   [[(0,[z0,z188,z3,z69,z4,z5,z10]),(0,[z189,z0,z2,z3,z4,z5,z10]),(0,[z53,z0,z2,z3,z4,z5,z10]),(0,[z0,z81,z2,z4,z179,z5,z10]),(0,[z0,z2,z3,z47,z4,z5,z10]),(0,[z138,z0,z2,z3,z4,z5,z190])],[(0,[z0,z191,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z192]),(0,[z0,z2,z193,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z194,z10]),(0,[z0,z2,z3,z4,z5,z195,z10])],[(1,[z137,z0,z2,z3,z4,z11])],[(0,[z196,z0,z2,z3,z4,z5,z10])],[(0,[z197,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z198]),(0,[z199,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z200]),(0,[z0,z201,z2,z3,z4,z5,z10]),(1,[z0,z96,z202,z4,z5,z10]),(0,[z0,z81,z82,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z203]),(0,[z0,z2,z3,z4,z5,z204,z10]),(1,[z0,z2,z3,z4,z5,z110]),(0,[z0,z2,z3,z4,z5,z205,z10])],[(0,[z0,z2,z3,z4,z206,z5,z10]),(0,[z0,z2,z3,z4,z5,z207,z10]),(0,[z0,z2,z3,z4,z5,z208,z10]),(0,[z0,z2,z209,z3,z4,z5,z10]),(0,[z210,z0,z2,z3,z4,z5,z10])],[(0,[z211,z0,z2,z3,z4,z5,z10]),(0,[z0,z212,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z213,z5,z10])],[(0,[z0,z214,z2,z3,z4,z5,z10]),(0,[z215,z0,z2,z3,z4,z5,z10]),(0,[z0,z216,z2,z3,z4,z40,z5]),(0,[z0,z41,z1,z2,z3,z4,z5]),(0,[z217,z0,z2,z3,z4,z5,z10]),(0,[z0,z218,z2,z3,z4,z5,z10]),(0,[z0,z219,z2,z3,z4,z5,z10])]],
   [[(0,[z220,z0,z2,z3,z4,z5,z10]),(0,[z221,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z222,z4,z5,z10]),(0,[z0,z41,z2,z3,z4,z5,z29]),(0,[z0,z82,z96,z2,z4,z5,z10]),(0,[z15,z0,z3,z4,z5,z16,z10]),(0,[z0,z223,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z224]),(0,[z0,z2,z3,z4,z5,z10,z225])],[(1,[z0,z2,z3,z226,z4,z10]),(0,[z0,z2,z3,z4,z5,z227,z10]),(0,[z0,z2,z3,z4,z5,z10,z228]),(0,[z0,z229,z2,z4,z5,z10,z11])],[(0,[z230,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z231,z4,z48,z10]),(1,[z0,z2,z3,z100,z5,z10])],[(0,[z0,z2,z3,z4,z5,z10,z232]),(0,[z0,z2,z3,z233,z4,z5,z10]),(0,[z0,z61,z2,z4,z5,z10,z93])],[(0,[z0,z2,z3,z234,z4,z5,z10]),(0,[z0,z235,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z236,z4,z5,z10])],[(0,[z0,z2,z121,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z237,z5,z10]),(0,[z0,z2,z3,z14,z5,z27,z10]),(0,[z0,z2,z238,z3,z4,z5,z10]),(0,[z239,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z240,z10])],[(0,[z0,z2,z3,z4,z241,z5,z10]),(0,[z0,z2,z3,z242,z4,z5,z10]),(1,[z0,z2,z3,z243,z5,z10]),(0,[z0,z244,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z98,z29]),(0,[z0,z2,z3,z245,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z120])]],
   [[(0,[z0,z82,z2,z68,z4,z5,z10]),(0,[z0,z2,z3,z246,z4,z5,z10]),(0,[z0,z247,z2,z3,z4,z5,z10])],[(0,[z248,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z249,z4,z5,z10]),(0,[z250,z0,z2,z3,z4,z5,z10])],[(1,[z0,z188,z3,z4,z5,z10]),(0,[z0,z2,z3,z202,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z251,z10]),(0,[z0,z2,z3,z252,z4,z5,z10]),(0,[z138,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z253]),(0,[z0,z2,z3,z4,z79,z5,z9])],[(0,[z0,z2,z3,z4,z74,z5,z10]),(0,[z0,z2,z69,z4,z179,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z4,z5,z8,z9])],[(0,[z0,z254,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z255,z4,z5,z10]),(0,[z0,z256,z2,z3,z4,z5,z10]),(0,[z257,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z258,z10]),(0,[z0,z2,z3,z4,z5,z259,z10]),(0,[z0,z2,z3,z260,z4,z5,z10]),(0,[z0,z2,z3,z148,z5,z27,z10]),(0,[z261,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z262,z4,z5,z10]),(0,[z0,z2,z3,z263,z4,z5,z10]),(0,[z0,z264,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z265,z10]),(0,[z0,z2,z3,z4,z5,z10,z266])],[(0,[z0,z2,z3,z4,z5,z267,z10]),(0,[z0,z2,z3,z4,z5,z268,z10]),(0,[z269,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z148,z47,z5,z10]),(0,[z138,z0,z2,z3,z4,z24,z10]),(0,[z0,z2,z3,z4,z5,z27,z10])],[(0,[z0,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z270,z10]),(0,[z0,z271,z2,z3,z4,z5,z10])]],
   [[(0,[z53,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z272,z3,z4,z5,z10])],[(0,[z0,z2,z3,z273,z4,z5,z10]),(1,[z0,z2,z42,z48,z5,z10]),(0,[z123,z0,z2,z3,z5,z27,z10]),(0,[z0,z2,z3,z51,z148,z4,z10])],[(0,[z0,z2,z68,z202,z4,z5,z10]),(0,[z0,z2,z3,z274,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z275,z10]),(0,[z0,z2,z3,z4,z5,z276,z10]),(0,[z0,z277,z2,z3,z4,z5,z10])],[(0,[z0,z278,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z242,z4,z48,z5]),(0,[z279,z0,z2,z3,z4,z5,z10])],[(1,[z0,z2,z3,z4,z5,z62]),(0,[z0,z2,z3,z280,z4,z5,z10]),(0,[z0,z2,z3,z281,z4,z5,z10]),(0,[z0,z282,z2,z3,z4,z5,z10]),(0,[z123,z0,z2,z42,z4,z5,z10])],[(0,[z0,z2,z178,z3,z4,z9,z10]),(1,[z169,z0,z2,z3,z4,z10]),(0,[z0,z2,z283,z3,z4,z5,z10])],[(0,[z0,z2,z3,z284,z4,z5,z10])],[(0,[z285,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z286,z10]),(0,[z0,z2,z287,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z288,z10])]],
   [[(0,[z289,z0,z2,z3,z4,z5,z10]),(0,[z0,z290,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z51,z5,z170,z10]),(0,[z0,z2,z3,z51,z5,z27,z10])],[(0,[z0,z2,z3,z176,z47,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z291]),(0,[z0,z292,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z293,z4,z5,z10]),(0,[z0,z294,z2,z3,z4,z5,z10])],[(1,[z0,z2,z3,z46,z5,z10]),(0,[z138,z0,z81,z2,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z8,z11]),(0,[z295,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z296,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z297,z10]),(0,[z0,z2,z3,z4,z5,z10,z298]),(0,[z0,z2,z3,z26,z4,z5,z9])],[(0,[z0,z2,z3,z69,z4,z5,z10]),(0,[z0,z2,z3,z4,z76,z16,z10]),(0,[z0,z2,z3,z4,z5,z299,z10]),(0,[z0,z135,z2,z3,z300,z5,z10]),(0,[z0,z2,z3,z4,z5,z301,z10]),(0,[z0,z2,z3,z302,z4,z5,z10])],[(0,[z303,z0,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z231,z4,z10]),(0,[z0,z2,z178,z3,z50,z4,z10])],[(0,[z0,z2,z3,z4,z5,z10,z304]),(0,[z75,z0,z2,z3,z4,z76,z10]),(0,[z0,z2,z3,z4,z5,z10,z305]),(0,[z306,z0,z2,z3,z4,z5,z10])],[(0,[z0,z307,z3,z69,z4,z5,z10]),(0,[z0,z2,z3,z308,z4,z5,z10])]],
   [[(0,[z0,z2,z309,z3,z4,z5,z10])],[(0,[z0,z2,z3,z310,z4,z5,z10]),(0,[z0,z2,z3,z4,z177,z5,z10]),(0,[z0,z2,z3,z311,z4,z5,z10])],[(0,[z30,z0,z2,z3,z4,z5,z54]),(0,[z0,z312,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z313]),(0,[z0,z2,z3,z314,z4,z5,z10]),(0,[z315,z0,z2,z3,z4,z5,z10])],[(0,[z0,z316,z2,z3,z4,z5,z10])],[(0,[z317,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z318,z10]),(0,[z0,z2,z3,z4,z5,z319,z10]),(0,[z137,z0,z2,z3,z4,z5,z9])],[(1,[z0,z2,z3,z4,z80,z10]),(0,[z0,z2,z3,z320,z4,z5,z10]),(0,[z0,z321,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z322,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z323]),(0,[z324,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z325,z10]),(0,[z0,z2,z3,z4,z5,z326,z10]),(0,[z327,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z231,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z328])],[(0,[z230,z0,z2,z69,z4,z5,z10]),(0,[z0,z41,z2,z3,z40,z5,z10])]],
   [[(0,[z230,z0,z2,z68,z4,z5,z10]),(0,[z13,z0,z2,z3,z148,z5,z10]),(0,[z13,z0,z2,z3,z51,z5,z10]),(0,[z0,z41,z2,z3,z14,z5,z10]),(0,[z2,z3,z4,z5,z29,z10,z54]),(0,[z0,z2,z3,z4,z5,z10,z54]),(0,[z138,z0,z96,z2,z4,z5,z10]),(0,[z0,z329,z2,z3,z4,z5,z10]),(0,[z0,z330,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z331,z4,z5,z10])],[(0,[z0,z2,z332,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z333,z5,z10]),(0,[z0,z135,z2,z3,z4,z16,z10])],[(0,[z0,z2,z3,z4,z76,z5,z10]),(0,[z0,z2,z3,z5,z27,z10,z134]),(0,[z0,z2,z3,z26,z4,z5,z11]),(0,[z0,z2,z3,z4,z5,z334,z10]),(0,[z0,z2,z3,z335,z4,z5,z10])],[(0,[z73,z0,z2,z3,z336,z5,z10]),(0,[z0,z2,z337,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z338]),(0,[z0,z96,z2,z202,z4,z5,z10]),(0,[z339,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z340,z5,z10])],[(0,[z341,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z342,z10]),(1,[z0,z135,z3,z4,z177,z10]),(0,[z0,z2,z3,z343,z4,z5,z10])],[(0,[z344,z0,z2,z3,z4,z5,z10]),(0,[z13,z0,z2,z3,z4,z5,z345]),(0,[z0,z346,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z347,z5,z10]),(0,[z0,z2,z348,z3,z4,z5,z10])],[(0,[z349,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z350,z4,z5,z10])],[(0,[z0,z2,z178,z3,z4,z179,z10]),(0,[z0,z2,z3,z4,z5,z351,z10])]],
   [[(0,[z114,z0,z2,z3,z4,z352,z10]),(1,[z114,z2,z68,z4,z5,z10]),(0,[z138,z0,z2,z68,z4,z5,z10])],[(0,[z0,z2,z3,z4,z353,z5,z10]),(0,[z0,z2,z3,z4,z5,z354,z10]),(0,[z0,z2,z3,z4,z355,z5,z10])],[(0,[z356,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z115,z5,z10]),(0,[z0,z2,z3,z243,z4,z5,z10])],[(0,[z73,z0,z113,z3,z4,z5,z10]),(0,[z0,z357,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z358,z4,z5,z10]),(0,[z0,z2,z3,z51,z4,z5,z288]),(0,[z137,z0,z2,z3,z4,z5,z11])],[(0,[z0,z2,z3,z359,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z360]),(0,[z0,z229,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z361,z4,z5,z10]),(0,[z13,z0,z2,z3,z4,z5,z362]),(0,[z0,z2,z3,z4,z5,z363,z10]),(0,[z0,z2,z3,z50,z4,z170,z10])],[(1,[z0,z2,z3,z4,z5,z345]),(0,[z364,z0,z2,z3,z4,z5,z10])],[(0,[z365,z0,z2,z3,z4,z5,z10]),(0,[z0,z366,z2,z3,z4,z5,z10]),(0,[z0,z3,z47,z4,z40,z5,z10]),(0,[z0,z367,z2,z3,z4,z5,z10]),(0,[z0,z135,z2,z3,z4,z5,z10]),(0,[z0,z368,z2,z3,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z47,z14,z5,z10]),(0,[z369,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z345,z10]),(0,[z370,z0,z2,z3,z4,z5,z10]),(0,[z371,z0,z2,z3,z4,z5,z10]),(0,[z0,z372,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z373,z5,z10]),(0,[z0,z41,z2,z3,z26,z5,z10])],[(0,[z0,z2,z3,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z374,z5,z10]),(0,[z375,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z376])],[(0,[z73,z2,z121,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z377,z5,z10]),(0,[z0,z378,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z379,z5,z10])],[(0,[z199,z0,z2,z3,z14,z5,z10]),(0,[z53,z30,z2,z3,z4,z5,z10])],[(0,[z0,z380,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z104,z16,z10]),(1,[z138,z0,z2,z4,z24,z10])],[(0,[z0,z381,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z5,z362]),(0,[z0,z2,z3,z4,z5,z382,z10]),(0,[z0,z2,z3,z4,z5,z10,z186])],[(0,[z0,z2,z3,z4,z5,z10,z362]),(0,[z0,z2,z178,z3,z4,z76,z10]),(0,[z0,z2,z3,z383,z4,z5,z10]),(0,[z0,z2,z3,z4,z48,z5,z10])]],
   [[(0,[z0,z2,z3,z4,z5,z384,z10]),(0,[z0,z2,z385,z3,z4,z5,z10])],[(0,[z95,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z386,z4,z5,z10]),(0,[z138,z0,z2,z178,z4,z5,z10])],[(0,[z0,z2,z68,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z29,z6]),(1,[z0,z2,z3,z136,z5,z10]),(0,[z123,z0,z2,z3,z48,z5,z10]),(0,[z0,z2,z3,z4,z5,z387,z10]),(0,[z0,z2,z3,z4,z5,z388,z10]),(0,[z0,z2,z3,z4,z5,z9,z10])],[(0,[z0,z82,z3,z202,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z389,z10]),(0,[z0,z41,z2,z3,z148,z5,z10]),(0,[z0,z41,z2,z3,z51,z5,z10])],[(0,[z0,z2,z390,z3,z4,z5,z10])],[(0,[z73,z0,z2,z3,z4,z5,z10]),(0,[z73,z0,z2,z3,z4,z5,z391]),(0,[z0,z2,z3,z4,z5,z392,z10]),(0,[z0,z2,z3,z393,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z9,z93])],[(0,[z0,z394,z2,z3,z4,z5,z10])],[(1,[z0,z307,z3,z4,z5,z10]),(0,[z395,z0,z2,z3,z4,z5,z10]),(0,[z0,z49,z2,z3,z4,z5,z10]),(1,[z0,z1,z3,z4,z5,z98]),(0,[z0,z2,z396,z3,z4,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z397,z5,z10])],[(0,[z0,z41,z2,z3,z19,z5,z10])],[(0,[z0,z398,z2,z3,z4,z5,z10]),(0,[z30,z2,z3,z4,z5,z29,z10]),(0,[z0,z2,z3,z39,z4,z5,z10]),(0,[z0,z2,z3,z399,z4,z5,z10])],[(0,[z73,z0,z2,z400,z4,z5,z10]),(1,[z0,z2,z3,z103,z5,z10]),(0,[z0,z2,z3,z4,z401,z5,z10])],[(0,[z0,z2,z402,z3,z4,z5,z10]),(0,[z0,z2,z403,z3,z4,z5,z10]),(0,[z0,z41,z2,z3,z47,z5,z10]),(0,[z0,z2,z3,z404,z4,z5,z10]),(0,[z0,z64,z3,z4,z5,z10,z6]),(0,[z0,z41,z2,z3,z4,z5,z9]),(0,[z405,z0,z2,z3,z4,z5,z10])],[(0,[z406,z0,z2,z3,z4,z5,z10]),(0,[z407,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z408,z4,z5,z10]),(0,[z32,z0,z2,z3,z40,z5,z10]),(0,[z138,z0,z61,z2,z4,z5,z10])],[(0,[z409,z0,z2,z3,z4,z5,z10]),(1,[z0,z216,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z300,z5,z10])],[(0,[z0,z2,z3,z4,z336,z5,z10]),(0,[z75,z0,z2,z273,z4,z5,z10]),(0,[z0,z410,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z148,z5,z170,z10])]],
   [[(0,[z0,z2,z411,z3,z4,z5,z10]),(0,[z0,z412,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z413,z10]),(0,[z0,z2,z414,z3,z4,z5,z10]),(0,[z0,z2,z3,z415,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z10,z10]),(0,[z0,z1,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z170,z10]),(0,[z0,z416,z2,z3,z4,z5,z10])],[(0,[z230,z2,z3,z69,z4,z5,z10]),(0,[z75,z0,z2,z3,z4,z104,z10]),(0,[z0,z417,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z179,z5,z10]),(0,[z0,z2,z3,z418,z4,z5,z10]),(0,[z0,z2,z3,z26,z4,z5,z134])],[(0,[z0,z2,z419,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z5,z288])],[(0,[z0,z2,z3,z4,z5,z420,z10]),(0,[z53,z2,z3,z4,z5,z10,z54]),(0,[z421,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z422,z4,z5,z10]),(0,[z0,z7,z2,z3,z4,z5,z10])],[(0,[z0,z2,z4,z5,z207,z16,z10]),(0,[z0,z423,z2,z3,z4,z5,z10])],[(1,[z0,z2,z4,z5,z207,z10])],[(0,[z0,z2,z3,z4,z5,z424,z10]),(0,[z0,z2,z3,z136,z4,z5,z10]),(0,[z0,z425,z2,z3,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z4,z5,z80,z10]),(0,[z0,z426,z2,z3,z4,z5,z10]),(0,[z427,z0,z2,z3,z4,z5,z10]),(0,[z0,z428,z2,z3,z4,z5,z10]),(0,[z0,z41,z7,z2,z3,z4,z5])],[(0,[z0,z2,z3,z47,z19,z5,z10]),(1,[z0,z2,z3,z180,z5,z10]),(0,[z0,z1,z2,z3,z26,z4,z5]),(0,[z429,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z430,z4,z5,z10]),(0,[z13,z199,z2,z3,z4,z5,z10]),(0,[z0,z431,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z26,z4,z5,z27])],[(0,[z432,z0,z2,z3,z4,z5,z10]),(0,[z0,z96,z2,z3,z4,z5,z10]),(0,[z0,z41,z2,z3,z4,z5,z11])],[(0,[z433,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z434,z3,z4,z5,z10]),(0,[z0,z7,z2,z3,z26,z4,z5]),(0,[z0,z2,z3,z4,z435,z5,z10]),(0,[z0,z2,z3,z26,z5,z27,z10])],[(0,[z199,z0,z2,z3,z19,z5,z10]),(0,[z32,z0,z3,z47,z4,z5,z10]),(0,[z138,z0,z2,z3,z4,z179,z10])],[(0,[z0,z2,z3,z4,z5,z436,z10]),(0,[z0,z2,z3,z4,z5,z10,z437])],[(0,[z73,z95,z2,z3,z4,z5,z10]),(0,[z438,z0,z2,z3,z4,z5,z10]),(0,[z439,z0,z2,z3,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z14,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z440]),(0,[z0,z2,z441,z3,z4,z5,z10]),(1,[z0,z2,z178,z4,z179,z10]),(0,[z0,z2,z3,z243,z5,z10,z93])],[(0,[z442,z0,z2,z3,z4,z5,z10]),(0,[z73,z0,z82,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z443,z10]),(0,[z0,z64,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z444,z4,z5,z10]),(0,[z0,z2,z3,z226,z4,z48,z10])],[(0,[z0,z2,z3,z445,z4,z5,z10]),(0,[z0,z2,z446,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z79,z5,z10])],[(0,[z447,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z448,z5,z10]),(0,[z449,z0,z2,z3,z4,z5,z10]),(0,[z0,z450,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z8,z10])],[(0,[z0,z2,z3,z4,z451,z5,z10]),(0,[z0,z2,z42,z3,z176,z5,z10])],[(0,[z0,z2,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z452,z5,z10]),(0,[z114,z0,z2,z69,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z453]),(0,[z0,z2,z454,z3,z4,z5,z10])],[(1,[z0,z2,z3,z4,z74,z10]),(0,[z0,z2,z455,z3,z4,z5,z10]),(0,[z114,z0,z2,z68,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z456,z10]),(0,[z0,z457,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z458,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z459,z10]),(0,[z0,z1,z2,z3,z4,z5,z98]),(0,[z0,z2,z3,z148,z4,z5,z10])]],
   [[(0,[z460,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z461]),(0,[z0,z462,z2,z3,z4,z5,z10]),(0,[z463,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z464,z10]),(1,[z0,z2,z3,z5,z10,z186])],[(0,[z465,z0,z2,z3,z4,z5,z10]),(0,[z0,z307,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z4,z5,z10]),(0,[z466,z0,z2,z3,z4,z5,z10])],[(1,[z0,z2,z273,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z467,z10]),(0,[z0,z468,z2,z3,z4,z5,z10]),(0,[z0,z469,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z470])],[(0,[z0,z2,z3,z4,z5,z471,z10]),(0,[z0,z2,z3,z4,z5,z10,z472]),(0,[z0,z2,z3,z473,z4,z5,z10]),(0,[z0,z41,z2,z3,z5,z10,z134])],[(0,[z0,z2,z3,z474,z4,z5,z10]),(0,[z475,z0,z2,z3,z4,z5,z10]),(0,[z123,z0,z2,z3,z4,z5,z10])],[(0,[z138,z0,z2,z3,z4,z76,z10]),(0,[z0,z2,z3,z4,z5,z476,z10]),(1,[z0,z2,z3,z242,z4,z5]),(0,[z0,z477,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z478,z5,z10]),(0,[z0,z2,z479,z3,z4,z5,z10])],[(0,[z73,z0,z2,z445,z4,z5,z10]),(0,[z480,z0,z2,z3,z4,z5,z10]),(0,[z137,z0,z2,z3,z4,z79,z10])],[(0,[z481,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z37,z4,z5,z10]),(0,[z269,z75,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z482]),(0,[z0,z2,z3,z4,z5,z483,z10]),(0,[z0,z2,z3,z484,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z40,z19,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z485]),(0,[z486,z0,z2,z3,z4,z5,z10]),(0,[z0,z487,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z488,z5,z10]),(0,[z269,z0,z2,z3,z4,z76,z10]),(0,[z0,z2,z3,z489,z4,z5,z10])],[(0,[z95,z0,z113,z3,z4,z5,z10]),(0,[z32,z0,z2,z3,z47,z5,z10]),(0,[z0,z2,z3,z176,z4,z5,z10])],[(0,[z0,z2,z178,z3,z4,z104,z10]),(0,[z0,z2,z3,z4,z5,z490,z10]),(0,[z0,z96,z2,z4,z179,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z491]),(0,[z0,z2,z492,z3,z4,z5,z10]),(0,[z138,z0,z2,z3,z4,z5,z110]),(0,[z0,z2,z3,z51,z4,z5,z10])],[],[(0,[z0,z2,z3,z4,z5,z391,z10]),(0,[z0,z493,z2,z3,z4,z5,z10]),(0,[z0,z96,z2,z3,z494,z5,z10])],[(0,[z0,z495,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z496,z10])],[(0,[z497,z0,z2,z3,z4,z5,z10]),(0,[z0,z498,z2,z3,z4,z5,z10]),(0,[z0,z499,z2,z3,z4,z5,z10]),(0,[z138,z0,z2,z4,z5,z8,z10]),(0,[z137,z0,z2,z178,z3,z4,z10]),(0,[z0,z2,z3,z4,z5,z500,z10])]],
   [[(0,[z75,z0,z2,z3,z4,z5,z10]),(0,[z0,z501,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z300,z5,z10]),(0,[z0,z2,z3,z100,z5,z10,z11])],[(1,[z0,z2,z3,z336,z5,z10]),(0,[z0,z81,z96,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z502,z10]),(0,[z0,z2,z3,z503,z4,z5,z10]),(1,[z0,z2,z3,z148,z170,z10]),(0,[z0,z2,z3,z4,z5,z10,z504])],[(0,[z505,z0,z2,z3,z4,z5,z10]),(0,[z0,z506,z2,z3,z4,z5,z10]),(0,[z0,z2,z178,z3,z148,z4,z10]),(0,[z0,z2,z3,z4,z10,z266,z93]),(0,[z0,z2,z3,z4,z5,z10,z507])],[(0,[z0,z508,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z509,z10]),(0,[z0,z41,z2,z3,z4,z5,z54]),(0,[z0,z216,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z510,z4,z5,z10]),(0,[z0,z2,z4,z179,z5,z8,z10])],[(0,[z0,z2,z3,z4,z5,z10,z511]),(0,[z0,z2,z3,z4,z5,z10,z512]),(0,[z513,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z514,z5,z10]),(0,[z0,z135,z2,z3,z4,z177,z10]),(0,[z515,z0,z2,z3,z4,z5,z10])],[],[(0,[z73,z0,z2,z3,z37,z5,z10]),(0,[z0,z2,z3,z4,z516,z5,z10]),(0,[z0,z2,z3,z4,z5,z517,z10])]],
   [[(0,[z0,z113,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z518,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z519]),(0,[z0,z2,z69,z202,z4,z5,z10]),(0,[z0,z520,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z521,z10]),(0,[z0,z2,z3,z4,z5,z10,z522]),(0,[z169,z0,z2,z3,z4,z10,z93])],[(0,[z523,z0,z2,z3,z4,z5,z10]),(0,[z0,z524,z2,z3,z4,z5,z10]),(0,[z0,z525,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z5,z190]),(0,[z0,z2,z3,z4,z5,z10,z526])],[(0,[z0,z527,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z352,z10]),(0,[z0,z2,z3,z4,z5,z528,z10]),(0,[z529,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z530,z10]),(0,[z0,z2,z3,z4,z5,z10,z190]),(0,[z0,z2,z3,z531,z4,z5,z10])],[(0,[z0,z532,z2,z3,z4,z5,z10]),(0,[z0,z533,z2,z3,z4,z5,z10]),(0,[z75,z0,z2,z534,z4,z5,z10]),(0,[z0,z2,z534,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z535,z5,z10]),(0,[z0,z2,z3,z4,z494,z5,z10]),(0,[z0,z41,z2,z3,z4,z5,z134])],[(0,[z114,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z536,z10]),(0,[z0,z2,z3,z4,z177,z76,z10]),(0,[z0,z537,z2,z3,z4,z5,z10])],[(0,[z0,z188,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z538,z10]),(1,[z123,z0,z2,z176,z5,z10])],[(0,[z0,z2,z400,z3,z4,z5,z10]),(0,[z0,z312,z2,z3,z47,z5,z10]),(0,[z539,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z540]),(0,[z0,z2,z3,z226,z4,z5,z10]),(0,[z138,z0,z2,z3,z4,z9,z10])],[(0,[z541,z0,z2,z3,z4,z5,z10])]],
   [[(0,[z0,z64,z1,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z93,z11])],[(0,[z542,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z543,z10]),(0,[z0,z2,z544,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z10,z545]),(0,[z13,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z546,z5,z10]),(0,[z0,z2,z3,z4,z5,z547,z10]),(0,[z0,z2,z3,z4,z5,z10,z548]),(0,[z549,z0,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z397,z5,z10]),(0,[z0,z2,z3,z550,z4,z5,z10]),(0,[z0,z2,z3,z551,z4,z5,z10])],[(0,[z0,z2,z3,z50,z148,z5,z10]),(0,[z0,z2,z3,z50,z51,z5,z10]),(0,[z0,z41,z2,z3,z4,z5,z27])],[],[(0,[z0,z2,z3,z4,z552,z5,z10]),(0,[z0,z553,z2,z3,z4,z5,z10])],[(0,[z30,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z26,z4,z5,z54]),(0,[z0,z2,z3,z4,z5,z554,z10]),(0,[z138,z0,z2,z3,z50,z4,z10]),(0,[z555,z0,z2,z3,z4,z5,z10])],[(0,[z0,z556,z2,z3,z4,z5,z10]),(1,[z269,z2,z3,z4,z104,z10]),(0,[z2,z3,z4,z76,z5,z104,z10]),(0,[z0,z2,z3,z4,z5,z10,z557]),(0,[z0,z2,z3,z558,z4,z5,z10])]],
   [[(0,[z114,z230,z2,z3,z4,z5,z10]),(1,[z0,z64,z3,z4,z5,z6]),(0,[z0,z559,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z560,z10]),(0,[z0,z2,z3,z4,z5,z561,z10])],[(1,[z0,z2,z3,z39,z4,z5]),(0,[z0,z2,z42,z3,z5,z27,z10]),(0,[z0,z2,z3,z4,z5,z10,z562])],[(1,[z0,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z5,z391]),(0,[z563,z0,z2,z3,z4,z5,z10]),(1,[z32,z0,z3,z47,z5,z10]),(0,[z0,z2,z3,z4,z5,z564,z10]),(0,[z0,z2,z3,z4,z5,z565,z10]),(0,[z0,z2,z3,z4,z5,z566,z10])],[(0,[z0,z567,z2,z3,z4,z5,z10]),(0,[z568,z0,z2,z3,z4,z5,z10]),(0,[z569,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z570,z10])],[(0,[z0,z2,z3,z4,z571,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z572])],[(0,[z0,z573,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z574,z4,z5,z10]),(0,[z0,z2,z575,z3,z4,z5,z10]),(0,[z0,z2,z3,z576,z4,z5,z10])],[(0,[z0,z2,z577,z3,z4,z5,z10]),(0,[z0,z2,z578,z3,z4,z5,z10]),(0,[z0,z2,z3,z579,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z93]),(1,[z0,z2,z3,z4,z10,z266])]],
   [[(0,[z0,z2,z3,z4,z5,z10,z580]),(0,[z0,z2,z3,z4,z5,z10,z581])],[(1,[z0,z2,z400,z4,z5,z10]),(0,[z0,z2,z3,z4,z582,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z583]),(0,[z0,z2,z178,z3,z4,z5,z10]),(0,[z584,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z585,z10]),(0,[z199,z0,z2,z3,z148,z5,z10]),(0,[z199,z0,z2,z3,z51,z5,z10]),(1,[z75,z2,z3,z4,z76,z10]),(0,[z0,z2,z3,z586,z4,z5,z10]),(0,[z0,z1,z2,z3,z105,z5,z10]),(0,[z138,z0,z2,z4,z5,z24,z10]),(0,[z0,z7,z2,z3,z4,z5,z93]),(0,[z0,z587,z2,z3,z4,z5,z10])],[(1,[z73,z121,z3,z4,z5,z10]),(0,[z73,z0,z96,z3,z4,z5,z10]),(0,[z588,z0,z2,z3,z4,z5,z10]),(0,[z0,z589,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z112])],[(0,[z0,z590,z2,z3,z4,z5,z10]),(0,[z591,z0,z2,z3,z4,z5,z10]),(0,[z592,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z593])],[(0,[z0,z2,z3,z4,z594,z5,z10]),(0,[z0,z2,z68,z4,z179,z5,z10]),(0,[z0,z2,z3,z47,z5,z27,z10]),(0,[z0,z2,z178,z3,z4,z24,z10])],[(0,[z0,z2,z3,z595,z4,z5,z10]),(1,[z0,z2,z534,z4,z5,z10]),(0,[z596,z0,z2,z3,z4,z5,z10]),(0,[z597,z0,z2,z3,z4,z5,z10]),(0,[z0,z598,z2,z3,z4,z5,z10])],[(0,[z599,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z600,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z601,z10]),(0,[z269,z2,z3,z4,z5,z104,z10]),(0,[z0,z2,z3,z602,z4,z5,z10]),(0,[z0,z2,z4,z179,z5,z24,z10])]],
   [[(0,[z95,z0,z82,z3,z4,z5,z10]),(0,[z0,z2,z3,z603,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z104,z10]),(0,[z0,z604,z2,z3,z4,z5,z10]),(0,[z15,z0,z2,z3,z4,z16,z10]),(0,[z0,z2,z3,z4,z5,z605,z10]),(1,[z0,z229,z2,z4,z5,z10])],[(0,[z73,z0,z121,z3,z4,z5,z10]),(0,[z0,z2,z606,z3,z4,z5,z10]),(0,[z138,z0,z2,z3,z4,z104,z10]),(0,[z0,z607,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z608]),(0,[z123,z0,z2,z3,z176,z5,z10])],[(0,[z0,z2,z609,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z610])],[(0,[z0,z2,z611,z3,z4,z5,z10]),(0,[z612,z0,z2,z3,z4,z5,z10]),(0,[z613,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z614,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z397,z5,z10]),(0,[z0,z2,z3,z615,z4,z5,z10]),(1,[z0,z2,z4,z5,z10,z120])],[(0,[z0,z2,z616,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z617,z10]),(0,[z0,z312,z2,z3,z40,z5,z10]),(0,[z0,z2,z3,z618,z4,z5,z10]),(0,[z123,z0,z2,z176,z4,z5,z10])],[(0,[z0,z2,z3,z619,z4,z5,z10]),(0,[z269,z0,z2,z3,z4,z104,z10]),(0,[z0,z2,z3,z103,z4,z5,z10])],[(0,[z0,z2,z3,z4,z31,z5,z10]),(0,[z30,z0,z2,z3,z4,z5,z29]),(0,[z0,z61,z2,z3,z4,z5,z10]),(0,[z620,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z10,z621]),(0,[z0,z2,z3,z4,z622,z5,z10]),(0,[z0,z312,z3,z4,z40,z5,z10]),(0,[z0,z3,z4,z177,z5,z16,z10]),(0,[z0,z64,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z5,z35,z10,z93])]],
   [[(0,[z138,z0,z2,z3,z148,z4,z10]),(0,[z0,z61,z7,z2,z4,z5,z10]),(0,[z0,z623,z2,z3,z4,z5,z10])],[(0,[z624,z0,z2,z3,z4,z5,z10]),(1,[z53,z2,z3,z4,z5,z54]),(0,[z625,z0,z2,z3,z4,z5,z10]),(0,[z0,z61,z2,z3,z4,z5,z93])],[],[(0,[z0,z626,z2,z3,z4,z5,z10]),(0,[z0,z627,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z628,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z629])],[(0,[z630,z0,z2,z3,z4,z5,z10]),(0,[z30,z0,z2,z3,z181,z5,z10]),(1,[z0,z2,z3,z494,z5,z10]),(0,[z0,z631,z2,z3,z4,z5,z10])],[(0,[z632,z0,z2,z3,z4,z5,z10]),(0,[z15,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z633]),(0,[z0,z61,z2,z3,z26,z4,z5])],[(0,[z634,z0,z2,z3,z4,z5,z10]),(0,[z635,z0,z2,z3,z4,z5,z10]),(0,[z0,z135,z3,z4,z177,z5,z10]),(0,[z0,z64,z2,z3,z26,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z636,z5,z10]),(0,[z0,z81,z2,z202,z4,z5,z10]),(0,[z0,z637,z2,z3,z4,z5,z10]),(0,[z0,z638,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z639])],[(0,[z0,z2,z3,z4,z5,z640,z10]),(0,[z0,z2,z641,z3,z4,z5,z10]),(0,[z2,z3,z14,z4,z19,z5,z10]),(0,[z0,z2,z3,z4,z642,z5,z10]),(0,[z0,z643,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z644,z5,z10]),(0,[z645,z0,z2,z3,z4,z5,z10])],[(0,[z646,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z51,z40,z5,z10]),(0,[z0,z2,z3,z4,z647,z5,z10]),(0,[z0,z2,z3,z4,z648,z5,z10])],[(0,[z0,z2,z3,z4,z5,z649,z10]),(0,[z0,z2,z3,z4,z650,z5,z10]),(0,[z0,z2,z3,z651,z4,z5,z10]),(1,[z0,z2,z3,z5,z35,z10])],[(0,[z0,z2,z3,z40,z5,z27,z10]),(0,[z0,z2,z3,z4,z5,z652,z10]),(0,[z0,z2,z3,z653,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z352,z10]),(0,[z0,z2,z3,z654,z4,z5,z10]),(0,[z0,z2,z3,z181,z4,z5,z10]),(0,[z0,z2,z3,z4,z655,z5,z10])],[(0,[z656,z0,z2,z3,z4,z5,z10]),(0,[z0,z657,z2,z3,z4,z5,z10])],[(0,[z114,z2,z68,z3,z4,z5,z10]),(0,[z199,z2,z3,z4,z19,z5,z10]),(0,[z0,z2,z3,z658,z4,z5,z10]),(0,[z0,z2,z3,z659,z4,z5,z10]),(0,[z0,z2,z3,z26,z4,z5,z10])]],
   [[(0,[z660,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z177,z104,z10]),(0,[z0,z2,z3,z661,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z16,z10]),(0,[z662,z0,z2,z3,z4,z5,z10])],[(0,[z113,z2,z121,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z663,z10]),(0,[z0,z2,z3,z4,z5,z54,z6]),(0,[z0,z2,z3,z664,z4,z5,z10]),(0,[z665,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z666,z10])],[(0,[z0,z2,z667,z3,z4,z5,z10]),(0,[z668,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z669,z5,z10])],[(0,[z0,z2,z3,z4,z5,z670,z10]),(0,[z0,z671,z2,z3,z4,z5,z10]),(0,[z672,z0,z2,z3,z4,z5,z10])],[(1,[z0,z2,z445,z4,z5,z10]),(0,[z673,z0,z2,z3,z4,z5,z10]),(0,[z0,z674,z2,z3,z4,z5,z10]),(0,[z0,z96,z3,z202,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z675,z10]),(0,[z676,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z677,z10]),(0,[z0,z678,z2,z3,z4,z5,z10]),(0,[z679,z0,z2,z3,z4,z5,z10]),(0,[z32,z0,z312,z3,z4,z5,z10]),(0,[z680,z0,z2,z3,z4,z5,z10]),(0,[z0,z64,z2,z3,z4,z5,z98]),(0,[z0,z2,z3,z681,z4,z5,z10]),(0,[z0,z2,z3,z51,z4,z5,z112])],[(0,[z0,z2,z3,z4,z682,z5,z10]),(0,[z0,z2,z3,z4,z683,z5,z10]),(0,[z0,z2,z3,z180,z4,z5,z10]),(0,[z0,z2,z3,z4,z684,z5,z10]),(0,[z15,z0,z135,z3,z4,z5,z10]),(0,[z0,z61,z2,z4,z179,z5,z10]),(0,[z137,z0,z2,z3,z4,z10,z11])],[(0,[z0,z685,z2,z3,z4,z5,z10]),(0,[z686,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z687,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z688,z10]),(0,[z0,z689,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z690,z10]),(0,[z0,z2,z3,z691,z4,z5,z10])]],
   [[(0,[z692,z0,z2,z3,z4,z5,z10]),(0,[z137,z0,z2,z3,z4,z5,z10])],[(0,[z0,z2,z693,z3,z4,z5,z10]),(0,[z0,z2,z3,z19,z5,z27,z10]),(0,[z0,z7,z2,z4,z5,z8,z10]),(0,[z0,z2,z694,z3,z4,z5,z10])],[],[(0,[z0,z2,z42,z3,z48,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z695]),(0,[z0,z2,z3,z4,z5,z10,z696])],[(1,[z230,z2,z69,z4,z5,z10]),(0,[z0,z82,z2,z69,z4,z5,z10]),(1,[z199,z2,z3,z19,z5,z10]),(0,[z0,z2,z3,z697,z4,z5,z10]),(0,[z0,z81,z82,z2,z4,z5,z10]),(1,[z0,z312,z3,z40,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z11])],[(0,[z0,z2,z3,z698,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z699,z10]),(0,[z0,z2,z3,z700,z4,z5,z10]),(0,[z0,z49,z2,z4,z5,z16,z10])],[(0,[z73,z0,z2,z3,z4,z5,z62]),(0,[z0,z2,z3,z4,z5,z5,z10]),(0,[z0,z2,z3,z4,z5,z98,z54]),(0,[z701,z0,z2,z3,z4,z5,z10]),(0,[z0,z702,z2,z3,z4,z5,z10]),(1,[z0,z7,z2,z4,z5,z8])],[(0,[z0,z2,z703,z3,z4,z5,z10]),(0,[z0,z704,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z705,z4,z5,z10]),(0,[z0,z2,z3,z706,z4,z5,z10])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z73,z121,z400,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z707]),(0,[z0,z708,z3,z4,z5,z10]),(0,[z0,z72,z2,z3,z40,z5])],[(0,[z0,z2,z445,z336,z5,z10]),(0,[z0,z2,z3,z4,z709,z10]),(0,[z0,z2,z3,z710,z5,z10]),(0,[z0,z2,z3,z711,z5,z10]),(0,[z466,z2,z3,z4,z76,z10]),(0,[z0,z41,z2,z3,z5,z134])],[(0,[z0,z2,z3,z712,z5,z10]),(0,[z0,z2,z3,z4,z713,z10]),(0,[z169,z0,z61,z2,z4,z10]),(0,[z0,z229,z2,z4,z5,z93])],[(0,[z0,z714,z2,z3,z4,z5]),(0,[z123,z0,z2,z5,z10,z224])],[(0,[z0,z2,z3,z4,z74,z62]),(0,[z0,z715,z3,z4,z5,z10]),(0,[z0,z2,z3,z5,z27,z228]),(0,[z0,z2,z3,z4,z79,z9])],[(0,[z0,z2,z3,z4,z80,z62]),(0,[z0,z2,z3,z716,z4,z5]),(0,[z0,z2,z3,z717,z5,z10]),(0,[z138,z0,z2,z4,z24,z110]),(0,[z169,z0,z61,z2,z4,z93])],[(0,[z230,z2,z718,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z719]),(0,[z0,z41,z2,z3,z644,z5]),(0,[z0,z229,z2,z26,z4,z5])]],
   [[(0,[z53,z2,z3,z4,z5,z54]),(0,[z0,z3,z4,z5,z98,z720])],[],[(0,[z0,z2,z3,z721,z5,z10])],[(0,[z0,z2,z722,z4,z5,z10]),(0,[z0,z2,z3,z51,z536,z10]),(0,[z0,z2,z4,z5,z723,z10])],[],[(0,[z0,z2,z42,z242,z48,z5]),(0,[z0,z72,z2,z3,z231,z4])],[(0,[z0,z2,z3,z724,z5,z10]),(0,[z0,z725,z3,z4,z5,z10])],[(0,[z0,z3,z4,z5,z10,z726])]],
   [[(0,[z0,z2,z3,z4,z5,z727]),(0,[z0,z728,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z729,z10])],[(0,[z0,z2,z3,z181,z5,z10]),(0,[z0,z2,z730,z4,z5,z10])],[(0,[z0,z2,z3,z731,z5,z10]),(0,[z0,z2,z3,z103,z5,z732]),(0,[z0,z2,z3,z4,z5,z733]),(0,[z0,z2,z3,z5,z35,z10])],[],[(0,[z0,z2,z3,z734,z5,z10]),(0,[z0,z2,z3,z4,z735,z10]),(0,[z138,z0,z2,z4,z387,z10])],[(0,[z0,z2,z3,z736,z5,z10]),(0,[z0,z2,z737,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z738]),(0,[z0,z2,z739,z48,z5,z10])],[(0,[z0,z212,z3,z4,z5,z98]),(0,[z0,z2,z3,z47,z5,z288]),(0,[z137,z0,z2,z3,z4,z11])],[]],
   [[(0,[z0,z2,z3,z740,z5,z10]),(0,[z0,z41,z2,z3,z5,z232]),(0,[z0,z96,z202,z4,z5,z10]),(0,[z0,z2,z3,z5,z10,z741])],[(0,[z742,z2,z3,z4,z5,z10])],[(0,[z0,z743,z2,z4,z5,z10])],[(0,[z0,z2,z445,z4,z5,z10]),(0,[z0,z2,z445,z4,z5,z391]),(0,[z0,z3,z4,z5,z744,z10]),(0,[z0,z2,z3,z745,z5,z10]),(0,[z0,z746,z3,z4,z5,z10])],[(0,[z0,z2,z3,z747,z494,z5]),(0,[z0,z748,z2,z4,z5,z10])],[(0,[z13,z2,z3,z166,z5,z10]),(0,[z0,z1,z3,z4,z5,z720]),(0,[z0,z2,z3,z226,z4,z10])],[(0,[z0,z2,z3,z4,z749,z10]),(1,[z2,z3,z750,z5,z10]),(0,[z0,z2,z3,z100,z5,z10])],[(0,[z0,z2,z3,z4,z5,z751])]],
   [[(0,[z199,z2,z3,z750,z5,z10]),(0,[z53,z2,z3,z4,z5,z752]),(0,[z0,z2,z3,z39,z5,z27]),(0,[z0,z2,z3,z4,z5,z753]),(0,[z0,z2,z3,z35,z10,z266])],[(0,[z0,z2,z3,z4,z754,z10])],[(0,[z597,z2,z3,z14,z5,z10]),(0,[z0,z216,z2,z3,z148,z5]),(0,[z0,z2,z3,z243,z5,z10])],[(0,[z73,z121,z445,z4,z5,z10]),(0,[z0,z2,z3,z603,z5,z27]),(0,[z2,z3,z4,z5,z10,z752]),(0,[z0,z755,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z10,z756]),(0,[z0,z312,z3,z40,z5,z10]),(0,[z0,z61,z2,z4,z5,z190])],[(0,[z0,z2,z3,z757,z5,z10]),(0,[z371,z2,z68,z4,z5,z10]),(0,[z0,z2,z758,z4,z5,z10])],[],[(0,[z0,z2,z3,z148,z601,z10]),(0,[z0,z2,z3,z50,z648,z10]),(0,[z0,z2,z3,z4,z5,z759]),(0,[z0,z2,z3,z243,z10,z266])],[(0,[z0,z760,z3,z4,z5,z10]),(0,[z0,z2,z178,z161,z4,z10])]],
   [[(0,[z0,z7,z2,z4,z5,z759])],[(0,[z0,z3,z761,z4,z5,z10]),(0,[z2,z3,z4,z762,z104,z10]),(0,[z0,z2,z3,z181,z5,z29])],[(0,[z0,z3,z763,z4,z5,z10])],[(0,[z0,z2,z3,z764,z5,z10]),(0,[z0,z41,z2,z396,z3,z5])],[(0,[z0,z2,z3,z37,z5,z391]),(0,[z0,z2,z3,z765,z5,z10]),(0,[z0,z2,z3,z226,z40,z10])],[(0,[z0,z2,z766,z4,z5,z10]),(0,[z0,z767,z2,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z768]),(0,[z2,z68,z718,z4,z5,z10]),(0,[z2,z3,z769,z4,z5,z10]),(0,[z0,z135,z3,z300,z177,z10]),(0,[z0,z64,z3,z706,z4,z5]),(0,[z0,z2,z770,z4,z5,z10])],[(0,[z0,z2,z3,z771,z5,z10]),(0,[z0,z2,z69,z4,z115,z10]),(0,[z0,z2,z3,z4,z5,z772]),(1,[z0,z2,z4,z773,z10]),(1,[z0,z2,z3,z4,z774])],[(0,[z0,z82,z307,z4,z5,z10]),(0,[z0,z2,z68,z4,z115,z10]),(0,[z169,z0,z2,z3,z243,z10])]],
   [[(0,[z0,z2,z3,z4,z5,z62]),(0,[z0,z2,z3,z775,z5,z10]),(0,[z0,z2,z3,z776,z5,z10]),(0,[z0,z777,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z778,z10]),(0,[z779,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z5,z10,z780]),(0,[z0,z229,z2,z4,z5,z8]),(0,[z0,z41,z2,z3,z5,z298]),(0,[z0,z2,z3,z26,z5,z186]),(0,[z0,z2,z100,z5,z10,z120])],[(0,[z88,z2,z69,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z781]),(0,[z32,z0,z3,z763,z5,z10]),(0,[z169,z0,z2,z3,z4,z10]),(0,[z0,z2,z3,z782,z5,z10])],[(0,[z0,z2,z400,z37,z5,z10]),(0,[z0,z2,z3,z783,z5,z10]),(0,[z0,z2,z3,z784,z5,z10]),(0,[z0,z96,z202,z494,z5,z10]),(0,[z138,z0,z2,z4,z773,z10])],[(0,[z0,z307,z202,z4,z5,z10]),(0,[z2,z3,z4,z5,z752,z54])],[(0,[z73,z121,z3,z37,z5,z10]),(0,[z0,z2,z3,z4,z5,z785]),(0,[z0,z72,z2,z3,z4,z5])],[(0,[z0,z2,z176,z739,z5,z10]),(0,[z0,z2,z3,z786,z4,z10])],[(0,[z0,z81,z82,z4,z5,z10])],[(0,[z0,z82,z445,z4,z5,z10]),(0,[z0,z2,z787,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z4,z788,z10]),(0,[z0,z2,z3,z4,z5,z789]),(0,[z0,z790,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z10,z791]),(0,[z0,z61,z2,z4,z5,z93])],[],[(0,[z0,z2,z792,z4,z5,z10]),(0,[z0,z2,z178,z3,z180,z10]),(0,[z0,z135,z3,z4,z793,z10]),(0,[z0,z2,z3,z786,z170,z10])],[(0,[z0,z2,z3,z4,z5,z794]),(0,[z0,z2,z3,z795,z5,z10]),(0,[z114,z2,z68,z4,z352,z10])],[(0,[z0,z2,z3,z4,z5,z112])],[(0,[z0,z796,z2,z4,z5,z10]),(0,[z2,z3,z4,z5,z797,z10])],[],[(0,[z0,z798,z2,z3,z4,z5]),(0,[z0,z2,z3,z5,z799,z10]),(0,[z0,z61,z2,z4,z266,z93])]],
   [[(0,[z0,z2,z3,z4,z9,z453])],[(0,[z0,z2,z3,z4,z80,z10]),(0,[z0,z2,z800,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z801]),(0,[z515,z2,z3,z4,z5,z54])],[(0,[z0,z2,z3,z802,z5,z10])],[],[(0,[z0,z2,z4,z5,z10,z803])],[(0,[z0,z307,z3,z804,z5,z10]),(0,[z0,z805,z3,z4,z5,z10]),(0,[z0,z2,z3,z806,z4,z10]),(0,[z0,z796,z202,z4,z5,z10]),(0,[z0,z2,z3,z807,z4,z10]),(0,[z0,z2,z3,z808,z5,z10]),(0,[z0,z2,z3,z4,z9,z774])],[(0,[z13,z2,z3,z750,z5,z10]),(0,[z0,z2,z3,z809,z5,z10])],[(0,[z0,z2,z810,z4,z5,z10]),(1,[z0,z3,z4,z793,z10]),(0,[z0,z3,z4,z5,z793,z10])]],
   [[(0,[z0,z135,z3,z4,z177,z10])],[(0,[z662,z2,z3,z4,z5,z54]),(0,[z2,z3,z4,z5,z811,z10]),(0,[z0,z2,z3,z4,z773,z10])],[(0,[z0,z2,z3,z812,z5,z10]),(0,[z2,z3,z4,z76,z762,z10]),(0,[z2,z3,z4,z5,z10,z813]),(0,[z0,z2,z3,z51,z10,z696])],[(0,[z0,z2,z3,z814,z4,z5]),(0,[z0,z2,z3,z815,z5,z10]),(0,[z2,z3,z4,z5,z10,z816]),(0,[z0,z817,z3,z4,z5,z10])],[(0,[z114,z2,z68,z4,z5,z10]),(0,[z0,z2,z3,z4,z115,z10]),(0,[z0,z2,z3,z4,z5,z818]),(0,[z0,z2,z3,z819,z5,z10]),(0,[z820,z2,z3,z4,z5,z10])],[(1,[z821,z3,z4,z5,z10]),(0,[z0,z108,z3,z40,z5,z10]),(0,[z0,z2,z4,z5,z8,z190])],[(0,[z0,z2,z3,z4,z5,z822]),(0,[z30,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z823,z5,z10]),(1,[z0,z2,z4,z5,z759])],[(0,[z0,z824,z2,z3,z4,z5]),(0,[z0,z2,z825,z4,z5,z10]),(0,[z0,z3,z4,z793,z16,z10])]],
   [[(0,[z0,z2,z826,z4,z5,z10]),(0,[z0,z2,z3,z750,z5,z10])],[(0,[z269,z2,z3,z4,z762,z10]),(0,[z0,z2,z4,z5,z10,z827])],[(0,[z0,z2,z3,z4,z828,z10]),(0,[z95,z329,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z345]),(1,[z0,z2,z3,z5,z741]),(0,[z137,z0,z229,z2,z4,z11])],[(0,[z0,z829,z2,z3,z4,z5]),(0,[z0,z41,z2,z3,z5,z186])],[(0,[z142,z2,z3,z4,z104,z10]),(0,[z0,z2,z3,z4,z10,z774])],[(0,[z0,z2,z445,z37,z5,z10]),(0,[z0,z2,z3,z830,z5,z10])],[(0,[z821,z121,z3,z4,z5,z10]),(0,[z831,z2,z3,z4,z5,z10])],[(0,[z0,z2,z832,z4,z5,z10]),(0,[z0,z2,z3,z833,z5,z10]),(0,[z2,z3,z750,z19,z5,z10]),(0,[z2,z3,z834,z4,z5,z10])]],
   [[(0,[z0,z2,z3,z4,z835,z10])],[(0,[z0,z2,z3,z336,z5,z62]),(0,[z0,z2,z3,z836,z5,z10]),(0,[z0,z2,z3,z837,z5,z10]),(0,[z0,z2,z3,z4,z838,z10]),(1,[z0,z2,z3,z786,z10])],[(0,[z0,z2,z3,z4,z5,z839]),(0,[z0,z2,z3,z4,z5,z732])],[(0,[z0,z216,z2,z3,z19,z5]),(0,[z0,z2,z3,z4,z840,z10]),(0,[z0,z2,z3,z4,z5,z110])],[(0,[z0,z2,z841,z4,z5,z10]),(0,[z0,z2,z3,z4,z9,z190])],[],[(0,[z0,z2,z3,z136,z5,z10]),(0,[z0,z2,z3,z842,z5,z10])],[(0,[z486,z0,z41,z2,z3,z5])]],
   [[(0,[z0,z2,z843,z4,z5,z10]),(0,[z0,z2,z3,z4,z844,z10]),(0,[z0,z2,z3,z845,z5,z10]),(0,[z0,z2,z3,z846,z5,z10]),(0,[z0,z2,z534,z4,z76,z10]),(0,[z0,z7,z2,z3,z243,z5])],[(0,[z0,z2,z4,z179,z773,z10])],[(0,[z0,z2,z847,z4,z5,z10]),(0,[z169,z0,z2,z3,z4,z190])],[(0,[z0,z307,z3,z4,z5,z10]),(0,[z0,z307,z3,z848,z5,z10]),(0,[z269,z2,z3,z103,z104,z10]),(0,[z0,z849,z2,z4,z5,z10]),(0,[z0,z1,z3,z4,z5,z98])],[(0,[z676,z2,z3,z19,z5,z10]),(0,[z0,z2,z3,z5,z10,z850])],[(0,[z0,z3,z4,z5,z851,z10]),(0,[z0,z2,z3,z4,z5,z852]),(0,[z0,z2,z3,z853,z5,z10]),(0,[z15,z0,z49,z4,z16,z10])],[(0,[z0,z2,z3,z854,z5,z10]),(0,[z0,z2,z3,z855,z5,z10]),(0,[z0,z2,z3,z4,z5,z856]),(0,[z0,z2,z3,z857,z4,z5])],[(0,[z0,z2,z3,z4,z5,z858]),(0,[z0,z2,z3,z103,z5,z10]),(0,[z0,z2,z3,z4,z5,z859]),(0,[z0,z90,z3,z40,z5,z10]),(0,[z0,z216,z2,z3,z51,z5]),(0,[z0,z860,z2,z4,z5,z10])]],
   [[(0,[z0,z520,z2,z176,z5,z10])],[(0,[z0,z2,z3,z336,z74,z10]),(0,[z0,z188,z3,z4,z5,z10]),(0,[z0,z3,z763,z40,z5,z10]),(0,[z0,z2,z3,z4,z5,z861]),(0,[z0,z61,z2,z4,z5,z759]),(0,[z0,z2,z3,z5,z186,z112])],[(0,[z0,z2,z3,z336,z80,z10]),(0,[z0,z2,z3,z37,z5,z62]),(0,[z0,z216,z2,z3,z4,z5]),(0,[z0,z3,z47,z763,z5,z10]),(0,[z0,z3,z4,z5,z10,z720])],[(0,[z0,z2,z3,z4,z5,z862])],[(0,[z0,z2,z3,z863,z5,z10]),(0,[z0,z2,z3,z864,z5,z10]),(0,[z0,z2,z3,z865,z300,z5])],[(0,[z0,z2,z866,z4,z5,z10]),(0,[z30,z2,z3,z181,z5,z29]),(0,[z0,z2,z3,z867,z5,z10]),(0,[z0,z796,z96,z4,z5,z10])],[(0,[z0,z2,z3,z868,z4,z5]),(0,[z15,z0,z3,z4,z793,z10]),(0,[z0,z229,z2,z100,z5,z10])],[(0,[z0,z2,z3,z4,z869,z10]),(0,[z0,z2,z4,z5,z10,z870]),(0,[z0,z2,z3,z4,z5,z288])]],
   [[(0,[z0,z2,z3,z871,z5,z10]),(0,[z0,z2,z42,z48,z5,z10])],[(0,[z114,z2,z718,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z872])],[(0,[z0,z2,z3,z873,z5,z10]),(0,[z0,z2,z3,z874,z5,z10]),(0,[z0,z2,z4,z5,z207,z10]),(0,[z0,z2,z3,z4,z875,z10])],[(0,[z0,z247,z3,z47,z5,z10])],[],[(0,[z0,z2,z3,z4,z5,z876]),(0,[z0,z2,z3,z747,z4,z5]),(0,[z0,z796,z3,z4,z5,z10]),(0,[z0,z877,z2,z4,z5,z10]),(0,[z0,z2,z3,z26,z379,z5])],[(0,[z0,z2,z3,z4,z878,z10])],[(0,[z0,z2,z3,z4,z879,z10])]],
   [[(0,[z0,z2,z3,z50,z786,z10])],[(0,[z0,z2,z400,z4,z5,z62]),(0,[z635,z0,z3,z47,z5,z10]),(0,[z0,z2,z3,z46,z5,z10]),(0,[z0,z41,z2,z3,z39,z5]),(0,[z0,z2,z4,z5,z880,z10]),(0,[z0,z1,z3,z399,z4,z5]),(0,[z0,z2,z3,z148,z185,z10])],[(0,[z0,z2,z3,z4,z5,z881]),(0,[z0,z2,z3,z50,z51,z112]),(0,[z137,z0,z2,z4,z120,z11])],[(0,[z0,z2,z3,z37,z80,z10]),(0,[z73,z121,z3,z4,z5,z62]),(0,[z0,z882,z2,z3,z4,z5]),(0,[z0,z883,z2,z4,z5,z10]),(0,[z0,z72,z2,z3,z226,z4]),(0,[z0,z2,z3,z884,z4,z10]),(0,[z0,z229,z2,z4,z9,z10])],[(0,[z0,z2,z885,z4,z5,z10]),(0,[z0,z2,z3,z231,z4,z10])],[(0,[z0,z2,z3,z886,z5,z10])],[(0,[z0,z2,z3,z4,z5,z887])],[(0,[z0,z821,z3,z4,z5,z10]),(0,[z0,z2,z888,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z720]),(0,[z137,z0,z2,z3,z100,z11])]],
   [[(0,[z0,z41,z2,z3,z5,z472]),(0,[z0,z2,z4,z5,z10,z759])],[(0,[z466,z2,z68,z4,z5,z10]),(0,[z0,z72,z2,z42,z3,z5]),(0,[z0,z2,z3,z4,z340,z9]),(0,[z0,z2,z3,z26,z5,z741])],[(0,[z0,z2,z739,z4,z5,z10]),(0,[z138,z0,z2,z236,z4,z10])],[(0,[z0,z2,z3,z4,z74,z10]),(0,[z0,z2,z3,z4,z74,z391]),(0,[z0,z2,z3,z889,z4,z10])],[(0,[z0,z2,z3,z4,z890,z10]),(0,[z0,z2,z3,z4,z80,z391]),(0,[z0,z133,z3,z47,z5,z10])],[(0,[z2,z3,z891,z4,z5,z10])],[(0,[z0,z2,z273,z4,z5,z10]),(0,[z0,z2,z3,z243,z5,z9])],[(0,[z892,z0,z2,z3,z4,z10])]],
   [[(0,[z0,z2,z3,z893,z4,z5]),(0,[z0,z381,z3,z40,z5,z10]),(0,[z13,z2,z3,z14,z5,z345])],[(0,[z0,z2,z400,z4,z74,z10]),(0,[z0,z2,z894,z4,z5,z10]),(0,[z306,z2,z69,z4,z5,z10])],[(0,[z0,z2,z400,z4,z80,z10]),(0,[z0,z2,z4,z5,z10,z895]),(0,[z0,z2,z3,z896,z5,z10]),(0,[z138,z0,z2,z4,z24,z190]),(0,[z0,z2,z897,z4,z5,z10])],[(0,[z73,z121,z3,z4,z74,z10]),(0,[z138,z0,z2,z4,z663,z10]),(0,[z30,z2,z3,z31,z5,z29]),(0,[z0,z2,z3,z5,z898,z10])],[(0,[z73,z121,z3,z4,z80,z10]),(0,[z0,z2,z4,z5,z899,z10]),(0,[z0,z2,z3,z4,z5,z900]),(0,[z0,z2,z3,z4,z901,z10]),(0,[z0,z2,z3,z4,z902,z10]),(0,[z0,z2,z3,z903,z5,z10])],[(0,[z75,z2,z273,z4,z76,z10]),(0,[z0,z2,z3,z904,z5,z10])],[(0,[z0,z905,z3,z4,z5,z10])],[(0,[z906,z0,z2,z3,z4,z10]),(0,[z0,z907,z3,z4,z5,z10]),(0,[z0,z41,z2,z3,z5,z507])]],
   [[(0,[z75,z2,z3,z4,z762,z10]),(0,[z0,z49,z2,z4,z76,z10]),(0,[z0,z2,z3,z39,z397,z5])],[(0,[z0,z2,z3,z4,z5,z908]),(0,[z0,z2,z3,z909,z5,z10]),(0,[z0,z2,z3,z804,z5,z10]),(0,[z0,z2,z3,z103,z5,z910]),(0,[z0,z2,z3,z26,z5,z617]),(0,[z911,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z148,z251,z10]),(0,[z912,z2,z3,z4,z5,z10])],[(0,[z0,z2,z4,z5,z10,z913]),(0,[z0,z2,z914,z4,z5,z10]),(0,[z0,z2,z3,z14,z5,z345]),(0,[z0,z2,z3,z4,z915,z10]),(0,[z0,z2,z3,z916,z5,z10]),(0,[z169,z0,z2,z4,z8,z10]),(0,[z0,z2,z3,z5,z27,z741])],[(0,[z0,z2,z3,z917,z5,z10]),(0,[z0,z2,z4,z5,z8,z759])],[(0,[z230,z307,z69,z4,z5,z10]),(0,[z0,z2,z534,z4,z104,z10]),(0,[z0,z2,z3,z300,z5,z10])],[(0,[z0,z2,z3,z918,z5,z10]),(0,[z0,z2,z3,z243,z5,z11]),(0,[z169,z0,z2,z3,z4,z9])],[(0,[z0,z2,z3,z4,z5,z919]),(0,[z0,z2,z609,z4,z179,z10]),(0,[z0,z2,z3,z920,z4,z10])],[(0,[z0,z2,z3,z4,z10,z921]),(0,[z922,z2,z3,z4,z5,z10]),(0,[z0,z82,z796,z4,z5,z10]),(0,[z0,z72,z2,z3,z47,z5]),(0,[z0,z2,z3,z4,z774,z11])]],
   [[(1,[z0,z796,z4,z5,z10]),(0,[z0,z96,z385,z4,z5,z10])],[(0,[z95,z821,z3,z4,z5,z10]),(0,[z0,z2,z3,z26,z397,z5])],[(0,[z0,z2,z3,z4,z5,z923]),(0,[z230,z188,z69,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z924])],[(0,[z0,z2,z925,z4,z5,z10]),(0,[z0,z61,z2,z5,z35,z93])],[(0,[z0,z2,z445,z4,z5,z62]),(0,[z0,z2,z3,z926,z5,z10]),(1,[z0,z3,z4,z5,z720]),(0,[z138,z0,z2,z4,z24,z10])],[(0,[z0,z2,z3,z4,z5,z362]),(0,[z2,z3,z4,z5,z29,z752]),(0,[z0,z1,z3,z397,z5,z98]),(0,[z0,z2,z3,z4,z10,z927])],[(0,[z0,z2,z3,z4,z352,z10]),(0,[z0,z2,z3,z4,z5,z752]),(0,[z0,z2,z3,z484,z4,z11])],[(0,[z0,z2,z3,z4,z5,z928]),(0,[z0,z2,z3,z929,z4,z10]),(0,[z0,z96,z202,z46,z5,z10])]],
   [[(0,[z930,z2,z3,z4,z5,z10]),(0,[z0,z2,z42,z551,z5,z10])],[(0,[z0,z2,z3,z4,z931,z10]),(0,[z2,z3,z14,z750,z5,z10]),(0,[z0,z65,z3,z40,z5,z10]),(0,[z932,z2,z3,z4,z5,z10]),(0,[z0,z2,z42,z226,z48,z10]),(0,[z0,z2,z4,z5,z8,z78]),(0,[z0,z61,z2,z3,z243,z5])],[(0,[z0,z3,z4,z177,z793,z10]),(0,[z0,z2,z3,z4,z5,z933])],[(0,[z0,z2,z3,z934,z5,z10]),(0,[z421,z2,z3,z4,z104,z10]),(0,[z0,z2,z3,z4,z5,z935])],[(0,[z0,z41,z2,z3,z5,z557]),(0,[z0,z2,z3,z936,z5,z10]),(0,[z123,z0,z72,z2,z3,z5]),(0,[z169,z0,z2,z3,z4,z11]),(0,[z0,z41,z2,z3,z5,z741])],[(0,[z0,z2,z42,z739,z5,z10]),(0,[z0,z937,z2,z3,z5,z10])],[(0,[z114,z2,z68,z4,z115,z10]),(0,[z0,z2,z3,z4,z10,z938]),(0,[z0,z2,z3,z4,z5,z939])],[(0,[z0,z2,z3,z4,z5,z940])]],
   [[(0,[z0,z941,z2,z3,z5,z10])],[(0,[z0,z2,z3,z4,z5,z942]),(0,[z138,z0,z2,z3,z180,z10]),(0,[z0,z943,z2,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z944]),(0,[z0,z2,z3,z786,z148,z10])],[(0,[z0,z2,z3,z945,z4,z5]),(0,[z0,z3,z946,z4,z5,z10]),(0,[z269,z2,z3,z4,z104,z10]),(0,[z0,z2,z4,z179,z456,z10]),(0,[z0,z61,z2,z243,z5,z93])],[(0,[z0,z2,z445,z4,z74,z10]),(0,[z0,z2,z3,z947,z5,z10]),(0,[z0,z41,z2,z3,z5,z97]),(0,[z0,z2,z3,z948,z5,z10]),(0,[z0,z64,z3,z4,z5,z6]),(0,[z0,z1,z3,z105,z5,z98]),(0,[z0,z2,z3,z949,z5,z10]),(0,[z0,z2,z3,z5,z10,z950])],[(0,[z0,z2,z445,z4,z80,z10]),(0,[z0,z2,z3,z4,z5,z951]),(0,[z0,z952,z2,z3,z4,z5]),(0,[z0,z2,z3,z50,z51,z288])],[(0,[z73,z678,z3,z4,z5,z10]),(0,[z0,z2,z3,z953,z5,z10]),(0,[z0,z2,z178,z4,z642,z10])],[(0,[z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z954,z10]),(0,[z0,z2,z3,z848,z5,z10]),(0,[z480,z2,z3,z14,z5,z10]),(1,[z2,z3,z4,z5,z752]),(0,[z32,z0,z3,z47,z5,z10]),(0,[z0,z312,z3,z39,z40,z5]),(0,[z0,z61,z2,z551,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z955,z10]),(0,[z0,z41,z2,z3,z5,z112])],[(0,[z138,z0,z2,z4,z116,z10])],[(0,[z0,z2,z3,z5,z10,z956]),(0,[z0,z2,z3,z226,z242,z4])],[(0,[z0,z2,z3,z19,z5,z345]),(0,[z15,z0,z4,z207,z16,z10]),(0,[z138,z0,z689,z2,z4,z10])],[(0,[z0,z96,z445,z4,z5,z10]),(0,[z0,z2,z957,z4,z5,z10]),(0,[z269,z2,z3,z180,z104,z10])],[(0,[z0,z2,z3,z958,z5,z10]),(0,[z0,z2,z3,z5,z959,z10])],[(0,[z0,z960,z3,z4,z5,z10]),(0,[z75,z2,z3,z4,z76,z10]),(0,[z0,z961,z3,z4,z5,z10])],[(0,[z0,z2,z3,z962,z5,z10]),(0,[z0,z2,z3,z4,z5,z963]),(0,[z0,z2,z3,z4,z5,z964]),(0,[z0,z2,z965,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z966])]],
   [[(0,[z0,z967,z3,z4,z5,z10]),(0,[z0,z2,z3,z180,z5,z10]),(0,[z568,z2,z3,z4,z5,z29]),(0,[z968,z0,z2,z3,z4,z10]),(0,[z0,z2,z3,z4,z969,z10])],[(0,[z0,z2,z3,z5,z10,z970]),(0,[z0,z2,z3,z971,z5,z10]),(0,[z0,z2,z3,z5,z972,z10]),(0,[z0,z66,z2,z4,z5,z8])],[(0,[z0,z2,z973,z4,z5,z10]),(0,[z0,z2,z534,z4,z5,z10]),(0,[z0,z974,z2,z3,z4,z5]),(0,[z975,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z976]),(0,[z0,z977,z2,z3,z300,z5]),(0,[z123,z0,z2,z739,z5,z10]),(0,[z0,z2,z3,z4,z79,z774])],[(0,[z0,z2,z3,z978,z5,z10]),(0,[z0,z2,z3,z979,z5,z10]),(0,[z0,z2,z980,z4,z5,z10]),(0,[z0,z2,z3,z4,z435,z9]),(0,[z0,z2,z3,z981,z4,z10])],[(0,[z0,z2,z3,z982,z4,z10]),(0,[z0,z2,z3,z5,z10,z983]),(0,[z0,z41,z2,z3,z397,z5])],[(0,[z0,z2,z3,z37,z74,z10]),(0,[z0,z2,z42,z231,z48,z10]),(0,[z137,z0,z2,z3,z4,z774])],[(0,[z0,z307,z4,z179,z5,z10])],[(0,[z0,z2,z178,z4,z179,z10]),(0,[z0,z2,z4,z5,z10,z120])]],
   [[(0,[z2,z718,z69,z4,z5,z10]),(0,[z0,z2,z984,z4,z5,z10])],[(0,[z0,z2,z3,z4,z10,z985]),(0,[z75,z2,z534,z4,z76,z10]),(0,[z0,z2,z986,z4,z5,z10]),(0,[z0,z2,z3,z865,z4,z5]),(0,[z0,z41,z2,z3,z5,z629])],[(0,[z0,z64,z3,z4,z5,z720])],[(0,[z0,z81,z796,z4,z5,z10]),(0,[z0,z81,z4,z5,z521,z10]),(0,[z0,z2,z3,z226,z47,z10]),(0,[z0,z2,z178,z4,z773,z10])],[(0,[z0,z49,z2,z4,z104,z10]),(0,[z0,z2,z3,z987,z5,z10])],[],[],[(0,[z0,z2,z988,z4,z5,z10]),(0,[z0,z82,z172,z4,z5,z10]),(0,[z0,z989,z3,z4,z5,z10]),(0,[z0,z2,z3,z5,z10,z186])]],
   [[(0,[z0,z2,z3,z4,z5,z990]),(1,[z2,z718,z4,z5,z10]),(0,[z0,z2,z3,z991,z5,z10]),(0,[z0,z316,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z992,z10]),(0,[z0,z2,z993,z4,z5,z10]),(0,[z0,z229,z41,z2,z4,z5])],[(0,[z0,z2,z3,z4,z994,z10]),(0,[z0,z2,z3,z995,z5,z10]),(0,[z0,z462,z3,z4,z177,z10]),(0,[z0,z2,z3,z494,z5,z10]),(0,[z0,z2,z3,z4,z5,z774])],[(0,[z0,z755,z2,z3,z494,z5]),(0,[z0,z312,z3,z763,z5,z10])],[(0,[z0,z2,z3,z996,z5,z10]),(0,[z0,z2,z3,z997,z5,z10])],[(0,[z0,z2,z3,z998,z4,z10]),(0,[z0,z3,z4,z5,z999,z10]),(0,[z0,z2,z3,z1000,z5,z10]),(0,[z0,z977,z2,z3,z4,z5]),(0,[z0,z2,z3,z242,z4,z5]),(0,[z0,z2,z1001,z4,z5,z10])],[(0,[z0,z1002,z3,z4,z5,z10])],[(0,[z0,z2,z3,z231,z242,z4]),(0,[z138,z0,z2,z4,z205,z10])],[(0,[z0,z307,z445,z4,z5,z10]),(0,[z0,z2,z3,z4,z1003,z10])]],
   [[(0,[z0,z2,z4,z179,z10,z55])],[(0,[z0,z2,z3,z1004,z5,z10])],[(0,[z0,z2,z3,z386,z51,z10]),(0,[z0,z2,z3,z4,z5,z1005])],[(0,[z0,z2,z1006,z4,z5,z10]),(0,[z0,z3,z1007,z4,z5,z10]),(0,[z0,z2,z3,z1008,z5,z10]),(0,[z13,z2,z3,z14,z5,z362]),(0,[z0,z216,z312,z3,z40,z5]),(0,[z0,z131,z3,z47,z5,z10])],[(0,[z0,z2,z3,z4,z1009,z10]),(0,[z137,z0,z2,z3,z4,z190]),(0,[z0,z229,z2,z5,z10,z186])],[(0,[z0,z2,z3,z5,z1010,z10]),(0,[z0,z3,z1011,z4,z5,z10]),(0,[z0,z2,z4,z5,z773,z10]),(0,[z0,z2,z3,z1012,z5,z10]),(0,[z0,z2,z3,z51,z786,z10])],[(0,[z2,z821,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z1013,z10]),(0,[z0,z937,z2,z3,z5,z190])],[]],
   [[(0,[z0,z2,z3,z336,z5,z10]),(0,[z0,z2,z3,z336,z5,z391]),(0,[z0,z2,z3,z763,z5,z10]),(0,[z0,z2,z3,z148,z170,z10])],[(0,[z0,z2,z3,z4,z5,z910]),(0,[z0,z2,z287,z48,z5,z10])],[],[(0,[z0,z1014,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z1015])],[(0,[z175,z0,z3,z4,z16,z10]),(0,[z0,z2,z3,z5,z10,z1016]),(0,[z0,z2,z3,z1017,z5,z10]),(0,[z0,z2,z3,z4,z1018,z10]),(0,[z138,z0,z2,z4,z8,z9])],[(0,[z0,z2,z400,z336,z5,z10]),(0,[z2,z718,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z1019]),(0,[z138,z0,z2,z4,z258,z10])],[(0,[z0,z2,z3,z1020,z5,z10]),(0,[z0,z1021,z2,z3,z4,z5]),(0,[z0,z2,z3,z1022,z5,z10]),(0,[z137,z0,z229,z2,z4,z10])]],
   [[(0,[z73,z121,z3,z336,z5,z10]),(0,[z0,z2,z4,z5,z1023,z10]),(0,[z230,z2,z69,z4,z5,z10]),(0,[z199,z2,z3,z19,z5,z10]),(0,[z0,z2,z3,z4,z5,z190])],[(0,[z0,z2,z3,z4,z1024,z10]),(0,[z0,z2,z3,z5,z27,z112])],[(0,[z0,z1025,z3,z4,z5,z10]),(0,[z30,z2,z3,z4,z5,z752]),(1,[z0,z2,z739,z5,z10]),(0,[z0,z7,z2,z4,z5,z8])],[(0,[z0,z1026,z2,z4,z5,z10]),(0,[z0,z2,z3,z1027,z5,z10]),(0,[z0,z2,z4,z5,z759,z93])],[(0,[z0,z2,z1028,z4,z5,z10]),(0,[z0,z1029,z2,z4,z5,z10]),(0,[z0,z216,z2,z3,z14,z5]),(0,[z0,z2,z3,z4,z5,z1030]),(0,[z123,z0,z2,z176,z5,z10])],[(0,[z13,z2,z3,z14,z5,z10]),(0,[z15,z0,z3,z4,z16,z10])],[(0,[z0,z2,z1031,z4,z5,z10]),(0,[z0,z2,z3,z1032,z5,z10]),(0,[z2,z3,z4,z5,z762,z10]),(0,[z0,z2,z3,z1033,z5,z10]),(0,[z0,z2,z3,z26,z5,z27]),(0,[z137,z0,z2,z3,z186,z11])],[(0,[z0,z2,z3,z4,z5,z1034]),(0,[z680,z2,z3,z4,z76,z10]),(0,[z0,z2,z3,z4,z793,z10])]],
   [[(0,[z73,z821,z3,z4,z5,z10]),(0,[z0,z2,z3,z181,z5,z54]),(0,[z1035,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z37,z5,z10]),(0,[z199,z2,z3,z489,z5,z10]),(0,[z138,z0,z2,z4,z286,z10]),(0,[z0,z2,z3,z4,z5,z1036]),(0,[z0,z2,z3,z397,z5,z10])],[(0,[z0,z2,z3,z1037,z5,z10]),(0,[z0,z493,z82,z4,z5,z10]),(0,[z0,z49,z2,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z1038]),(0,[z0,z2,z3,z5,z972,z190])],[(0,[z0,z2,z3,z4,z1039,z10]),(0,[z0,z2,z3,z4,z5,z1040]),(0,[z0,z1041,z2,z3,z4,z5])],[(0,[z0,z2,z3,z31,z5,z10]),(0,[z0,z2,z3,z4,z762,z10]),(0,[z0,z2,z3,z5,z1042,z10]),(0,[z0,z2,z4,z5,z10,z1043]),(0,[z0,z2,z3,z1044,z5,z10])],[(0,[z0,z2,z1045,z4,z5,z10]),(0,[z0,z2,z3,z4,z1046,z10]),(0,[z0,z229,z2,z4,z5,z190]),(0,[z0,z2,z3,z50,z51,z10]),(0,[z0,z2,z3,z4,z5,z741])],[],[(0,[z0,z7,z2,z350,z4,z5]),(0,[z1047,z2,z3,z4,z5,z10])]],
   [[(0,[z113,z821,z3,z4,z5,z10]),(0,[z0,z2,z3,z148,z5,z345]),(0,[z0,z2,z3,z51,z5,z345]),(0,[z0,z2,z3,z1048,z5,z10]),(0,[z138,z0,z2,z260,z4,z10])],[(0,[z0,z2,z3,z4,z5,z1049]),(0,[z138,z0,z307,z4,z5,z10]),(0,[z0,z2,z3,z39,z4,z5]),(0,[z0,z2,z3,z40,z5,z288]),(0,[z1050,z0,z2,z3,z4,z10]),(0,[z0,z2,z5,z10,z186,z120])],[(0,[z0,z2,z3,z4,z5,z391]),(0,[z0,z2,z3,z1051,z5,z10]),(0,[z1052,z0,z2,z4,z5,z10]),(0,[z0,z2,z3,z786,z5,z10])],[],[(0,[z0,z2,z3,z1053,z4,z10]),(0,[z169,z0,z2,z3,z35,z10])],[(0,[z0,z3,z4,z5,z10,z1054]),(1,[z0,z3,z763,z5,z10]),(0,[z1055,z2,z3,z4,z5,z10]),(0,[z0,z2,z178,z4,z10,z562]),(0,[z0,z2,z3,z1056,z5,z10])],[(0,[z2,z3,z750,z4,z5,z10]),(0,[z138,z0,z2,z4,z318,z10]),(0,[z0,z2,z3,z4,z10,z266])],[(0,[z0,z135,z3,z136,z177,z10]),(0,[z0,z72,z2,z42,z48,z5]),(0,[z0,z2,z3,z5,z741,z134])]],
   [[(0,[z0,z2,z400,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z1057]),(0,[z0,z2,z400,z4,z5,z391]),(0,[z0,z2,z1058,z4,z5,z10]),(0,[z0,z2,z3,z105,z5,z10]),(0,[z0,z2,z3,z4,z5,z1059]),(0,[z0,z2,z4,z773,z24,z10]),(0,[z0,z41,z2,z3,z478,z5])],[(0,[z0,z2,z3,z4,z5,z1060]),(0,[z0,z3,z4,z5,z720,z6]),(0,[z0,z2,z3,z4,z1061,z10])],[(0,[z73,z121,z3,z4,z5,z10]),(0,[z95,z113,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z1062,z10]),(0,[z73,z121,z3,z4,z5,z391]),(0,[z0,z2,z718,z4,z5,z10]),(0,[z597,z2,z3,z4,z5,z29])],[(0,[z0,z2,z3,z4,z5,z1063])],[(0,[z0,z1064,z3,z4,z5,z10]),(0,[z613,z2,z3,z19,z5,z10]),(0,[z1065,z2,z3,z4,z5,z10]),(0,[z0,z41,z2,z3,z5,z140])],[(1,[z2,z3,z4,z762,z10]),(0,[z1066,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z739,z5,z10])],[(0,[z0,z2,z3,z1067,z4,z10]),(0,[z0,z2,z3,z1068,z5,z10]),(0,[z0,z2,z3,z148,z500,z10])],[(0,[z0,z2,z3,z4,z1069,z10]),(0,[z0,z229,z2,z4,z5,z10])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 558) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 558).take 484) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1042)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [558, 484] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 186).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 186).take 70).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [186, 70] = true :=
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

end PEqualNP.Outside.L_meta_41080

theorem PEqualNP.Outside.L_meta_41080 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4270377984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4270377984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41080.solve