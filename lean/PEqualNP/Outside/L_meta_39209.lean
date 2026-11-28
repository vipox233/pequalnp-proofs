import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39209

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4205373576) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00004111019a1aa2#64 ++ 0x28000208880cd0d5#64 ++ 0xe024d33307fe3fff#64 ++ 0xf7012699983ff1ff#64 : BitVec 256),
   (0x00490444c444c544#64 ++ 0x900248222622262a#64 ++ 0xf8db2cccc447c7ef#64 ++ 0xefc6d96666223e3f#64 : BitVec 256),
   (0x231c30f058696989#64 ++ 0x2118e18782c34b4c#64 ++ 0xa71c30f0f879f99d#64 ++ 0x5d38e18787c3cfcc#64 : BitVec 256),
   (0x0de03f00ae81b611#64 ++ 0xc06f01f805740db0#64 ++ 0xafe03f00ff81fe1b#64 ++ 0x3d7f01f807fc0ff0#64 : BitVec 256),
   (0x16ffc000f776001e#64 ++ 0x00b7fe0007bbb000#64 ++ 0x97ffc000fffe0018#64 ++ 0xfcbffe0007fff000#64 : BitVec 256),
   (0x07b6baaa00000000#64 ++ 0x003db5d550000000#64 ++ 0xdfffffff00000007#64 ++ 0xfefffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0xc024d33300000007 0xf601269998000000

def z1 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x2000000007fe3ff8 0x01000000003ff1ff

def z2 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8db2cccc447c7ef 0xefc6d96666223e3f

def z3 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfffffff00000007 0xfefffffff8000000

def z4 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe03f00ff81fe1b 0x3d7f01f807fc0ff0

def z5 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffc000fffe0018 0xfcbffe0007fff000

def z6 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c30f0f879f99d 0x5d38e18787c3cfcc

def z7 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe024d33307fe3fff 0xf7012699983ff1ff

def z8 : W := mkw 0x14e3c000a7160016 0x00a71e000538b000 0x90e7c00007fe0018 0xf4873e00003ff000

def z9 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x0724c0003bb80010 0x1039260001ddc000

def z10 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xffffecccffffc7ff 0xffffff6667fffe3f

def z11 : W := mkw 0x210030f008096981 0x2108018780404b4c 0x200030f00001f985 0x0100018780000fcc

def z12 : W := mkw 0x000004440000c540 0x900000222000062a 0x68002ccc0001c7e7 0x0340016660000e3f

def z13 : W := mkw 0x125d4000f776001e 0x0092ea0007bbb000 0x871c0000fffe0018 0x5c38e00007fff000

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8db2ccc00000007 0xeec6d96660000000

def z15 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x0724d33300000000 0x1039269998000000

def z16 : W := mkw 0x031c30e040404100 0x0018e18702020208 0xa71c30f0c041c18d 0x5d38e18786020e0c

def z17 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0x072013003b803810 0x1039009801dc01c0

def z18 : W := mkw 0x0ff6bfaaae81b611 0xc07fb5fd55740db0 0xffffffffff81fe1f 0xfffffffffffc0ff0

def z19 : W := mkw 0x121fc0005176000e 0x0090fe00028bb000 0x101fc000007e0000 0xc080fe000003f000

def z20 : W := mkw 0x231eb0fa58696989 0x2118f587d2c34b4c 0xf71ff0fff879f99d 0xdfb8ff87ffc3cfcc

def z21 : W := mkw 0x2b5c35f0fee9ff99 0xe15ae1af87f74ffc 0xa71c30f0fff9ff9d 0x5d38e18787ffcffc

def z22 : W := mkw 0x0000410101921222 0x08000208080c9091 0x4020c30307860662 0xa2010618183c3033

def z23 : W := mkw 0x00490400c4448404 0x8002482006222420 0xb8db2c00c447c60b 0xedc6d96006223e30

def z24 : W := mkw 0x06fc0000f6600018 0x0037e00007b30000 0x87fc0000fff80018 0x7c3fe00007ffc000

def z25 : W := mkw 0x09003f000881b601 0xc04801f800440db0 0xaf003f00f801fe1b 0x1d7801f807c00ff0

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000000044607ef 0xe70000000022303f

def z27 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe03f00ffc7ffff 0xff7f01f807fe3fff

def z28 : W := mkw 0x09003f110889bea1 0xe84801f888444df5 0x68003f330001ffe7 0x034001f998000fff

def z29 : W := mkw 0x0de07f11af9bbeb3 0xe86f03f88d7cddf5 0xefe4ff33ffffffff 0xff7f27f99fffffff

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x48002ccc00000007 0x0240016660000000

def z31 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0002000c001c009 0x0d00010006000e00

def z32 : W := mkw 0x000000aa00000000 0x0000000550000000 0x400000ff00000004 0x02000007f8000000

def z33 : W := mkw 0x04e04111a79a1ab2 0x282702088d3cd0d5 0xe7e4d333fffe3fff 0xff3f26999ffff1ff

def z34 : W := mkw 0x17fffbbbf7fe1abe 0x28bfffdddfbff0d5 0xfffffffffffe3fff 0xfffffffffffff1ff

def z35 : W := mkw 0x16b6800032200018 0x00b5b40001910000 0x0700000038000000 0x0038000001c00000

def z36 : W := mkw 0x10494000f776001e 0x00824a0007bbb000 0x8024c000fffe0018 0xf401260007fff000

def z37 : W := mkw 0x231c3afa58696989 0x2118e1d7d2c34b4c 0xef1c3ffff879f99f 0x5f78e1ffffc3cfcc

def z38 : W := mkw 0x00490444c444c544 0x900248222622262a 0x38db2cccc447c7e8 0x09c6d96666223e3f

def z39 : W := mkw 0x16ff8000f664001c 0x00b7fc0007b32000 0x17db0000f8000000 0x08bed80007c00000

def z40 : W := mkw 0x021c000050600008 0x0010e00002830000 0x871c0000f8780018 0x5c38e00007c3c000

def z41 : W := mkw 0x37fff0f0ff7f699f 0x21bfff8787fbfb4c 0xb7fff0f0fffff99d 0xfdbfff8787ffffcc

def z42 : W := mkw 0x0000400001120002 0x0000020000089000 0x8024c00007fe0018 0xf4012600003ff000

def z43 : W := mkw 0x08400500ae81b611 0xc042002805740db0 0x20000000ff81fe18 0x0100000007fc0ff0

def z44 : W := mkw 0x0de03f44ae81f751 0xd06f01fa25740fba 0xefe03fccff81ffff 0x3f7f01fe67fc0fff

def z45 : W := mkw 0x16ffc404f776845e 0x90b7fe2027bbb422 0xdfffcc0cfffe067a 0xfefffe6067fff033

def z46 : W := mkw 0x16bec0007372001a 0x00b5f600039b9000 0x873cc000fbf80018 0x5c39e60007dfc000

def z47 : W := mkw 0x01003aaa00000000 0x000801d550000000 0x48003fff00000007 0x024001fff8000000

def z48 : W := mkw 0x221c005058696989 0x2110e00282c34b4c 0xa71c0000f879f998 0x5d38e00007c3cfcc

def z49 : W := mkw 0x17fff0a0f776001e 0x00bfff8507bbb000 0x97fff0f0fffe001d 0xfcbfff8787fff000

def z50 : W := mkw 0x0000410101921222 0x08000208080c9091 0xc024c30307fe067a 0xf6012618183ff033

def z51 : W := mkw 0x00490544c4c4d744 0x9002482a262626ba 0xf8fb3fccc7c7ffff 0xffc7d9fe663e3fff

def z52 : W := mkw 0x08404511af9bbeb3 0xe84202288d7cddf5 0x20000000fffffff8 0x0100000007ffffff

def z53 : W := mkw 0x0de83f40eec1f711 0xc06f41fa07760fb8 0xaff83fc0ffc1ff9f 0x7d7fc1fe07fe0ffc

def z54 : W := mkw 0x00490444c444c544 0x900248222622262a 0xa8c02c00c447c7eb 0x2d46016006223e3f

def z55 : W := mkw 0x210031f108897ba1 0x2908018f88444bdd 0x600033f30001ffe7 0x0300019f98000fff

def z56 : W := mkw 0x231c71f159fb7bab 0x2918e38f8acfdbdd 0xe73cf3f3ffffffff 0xff39e79f9fffffff

def z57 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0x8fe03f003b803813 0x3c7f01f801dc01c0

def z58 : W := mkw 0x0de93f44eec5f755 0xd06f49fa27762fba 0xfffb3fccffc7ffff 0xffffd9fe67fe3fff

def z59 : W := mkw 0x221c00f050684988 0x2110e0078283424c 0x001c00f000780184 0x4000e0078003c00c

def z60 : W := mkw 0x27b6baba18292889 0x213db5d5d0c14944 0x0724d33338383810 0x1039269999c1c1c0

def z61 : W := mkw 0x0000010000801200 0x0000000800040090 0x0020130003803810 0x10010098001c01c0

def z62 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8ffffffc447c7ef 0xffc7fffffe223e3f

def z63 : W := mkw 0x221c40f1517a49aa 0x2910e2078a8bd24d 0x401cc0f3007e01e4 0xc200e6079803f00f

def z64 : W := mkw 0x37bef0f07b7b699b 0x21bdf78783dbdb4c 0xa73cf0f0fbf9f99d 0x5d39e78787dfcfcc

def z65 : W := mkw 0x16ffc040f776411e 0x00b7fe0207bbb208 0xb7ffe0c0ffffc19d 0xfdbfff0607fffe0c

def z66 : W := mkw 0x0002800a00000000 0x0000140050000000 0x5003c00f00000000 0x82801e0078000000

def z67 : W := mkw 0x17fffaaaf776001e 0x00bfffd557bbb000 0xdffffffffffe001f 0xfefffffffffff000

def z68 : W := mkw 0x2ffc3ff0fee9ff99 0xe17fe1ff87f74ffc 0xaffc3ff0fff9ff9f 0x7d7fe1ff87ffcffc

def z69 : W := mkw 0x00490444c444c544 0x900248222622262a 0x18db2cccc001c000 0x08c6d96666000e00

def z70 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0x9fffecccffffc018 0xfcffff6667fffe00

def z71 : W := mkw 0x0216c0bb011a08a2 0x2810b605d808d045 0x501fc0ff007e01e4 0xc280fe07f803f00f

def z72 : W := mkw 0x0000010000801200 0x0000000800040090 0xa020130007803e1b 0x35010098003c01f0

def z73 : W := mkw 0x221c00f050684988 0x2110e0078283424c 0xa01c10f00078399d 0x5500e0878003c1cc

def z74 : W := mkw 0x27bebafa58696989 0x213df5d7d2c34b4c 0xfffffffff879f99f 0xffffffffffc3cfcc

def z75 : W := mkw 0x231430b018292889 0x2118a18580c14944 0x0704103038383810 0x1038208181c1c1c0

def z76 : W := mkw 0x235d34f4dc6dedcd 0xb11ae9a7a6e36f6e 0xffdf3cfcfc7fffff 0xfffef9e7e7e3ffff

def z77 : W := mkw 0x335d70f0ff7f699f 0x219aeb8787fbfb4c 0xa71c30f0fffff99d 0x5d38e18787ffffcc

def z78 : W := mkw 0x04a28a0a00000000 0x0025145050000000 0x58e3cf0f00000002 0xa2c71e7878000000

def z79 : W := mkw 0x09403500ae81b611 0xc04a01a805740db0 0xa7003000ff81fe19 0x1d38018007fc0ff0

def z80 : W := mkw 0x210030f008096981 0x2108018780404b4c 0xa70030f0f801f99d 0x1d38018787c00fcc

def z81 : W := mkw 0x06b68aaa00000000 0x0035b45550000000 0x58ffcfff00000006 0xe2c7fe7ff8000000

def z82 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe71c30f0fc7fffff 0xff38e18787e3ffff

def z83 : W := mkw 0x121fc0445176414e 0x1090fe02228bb20a 0x501fc0cc007e01e4 0xc280fe066003f00f

def z84 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x0fe03f00fb81f810 0x187f01f807dc0fc0

def z85 : W := mkw 0x16bfc0007376001e 0x00b5fe00039bb000 0x173fc0003bfe0010 0xd0b9fe0001dff000

def z86 : W := mkw 0x04e00400a6008410 0x8027002005300420 0xafe02c00ff81c61b 0x3d7f016007fc0e30

def z87 : W := mkw 0x01007111099b3aa3 0x28080388884cd9d5 0xe724f333ffffffff 0xff3927999fffffff

def z88 : W := mkw 0x0009004440444144 0x100048022202220a 0xf01b20ccc047c1ed 0xcf80d90666023e0f

def z89 : W := mkw 0x00004011011a08a2 0x280002008808d045 0x00000000007e01e0 0x000000000003f00f

def z90 : W := mkw 0x04e00000a6000010 0x0027000005300000 0x07c00000f8000000 0x083e000007c00000

def z91 : W := mkw 0x0de03e00ae01a411 0xc06f01f005700d20 0x8fe02c00ff81c018 0x3c7f016007fc0e00

def z92 : W := mkw 0x09003f000881b601 0xc04801f800440db0 0x28003f000001fe03 0x014001f800000ff0

def z93 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xfffb3fccff81fe1f 0xffffd9fe67fc0ff0

def z94 : W := mkw 0x0008004040404100 0x0000400202020208 0x20000000c041c188 0x0100000006020e0c

def z95 : W := mkw 0x17ffbaaaf664001c 0x00bffdd557b32000 0x1fdb2cccf8000000 0x08fed96667c00000

def z96 : W := mkw 0x0fb6bfaa0881b601 0xc07db5fd50440db0 0xffffffff0001fe07 0xfffffffff8000ff0

def z97 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0x6000133300003fe7 0x03000099980001ff

def z98 : W := mkw 0x0040040084008400 0x8002002004200420 0xa8c02c00c401c60b 0x2d46016006200e30

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z100 : W := mkw 0x0de07f11af9bbeb3 0xe86f03f88d7cddf5 0xafe4ff33ffb9fe1b 0x3d7f27f99ffdcff0

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x58c30c0c00000002 0xa2c6186060000000

def z102 : W := mkw 0x00004011011a08a2 0x280002008808d045 0x4004c033007e01e4 0xc20026019803f00f

def z103 : W := mkw 0x0de07f01af93b633 0xc86f03f80d7c9db1 0xefe0ff03ff87fe7b 0xbf7f07f81ffc3ff3

def z104 : W := mkw 0x231c30e058616109 0x0118e18702c30b08 0x071820c0f801c000 0x0838c10607c00e00

def z105 : W := mkw 0x000004440000c540 0x900000222000062a 0x200000000001c7e0 0x0100000000000e3f

def z106 : W := mkw 0x0041040484048444 0x9002082024202422 0x58c30c0c04060662 0xa2c6186060203033

def z107 : W := mkw 0x01003a0000000000 0x000801d000000000 0x08003f0000000003 0x004001f800000000

def z108 : W := mkw 0x021680aa00000000 0x0010b40550000000 0x501fc0ff00000004 0xc280fe07f8000000

def z109 : W := mkw 0x1fffff00fff7b61f 0xc0fffff807ffbdb0 0xbfffff00fffffe1b 0xfdfffff807fffff0

def z110 : W := mkw 0x00490444c444c544 0x900248222622262a 0x701b00ccc447c7ec 0xc380d80666223e3f

def z111 : W := mkw 0x16bfc0005176000e 0x00b5fe00028bb000 0x97ffc000007e0000 0xfcbffe000003f000

def z112 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x1fdb2ccc00000000 0x08fed96660000000

def z113 : W := mkw 0x0100300008012001 0x0008018000400900 0xa7003000f801f819 0x1d38018007c00fc0

def z114 : W := mkw 0x0ce00f00a6809610 0xc0670078053404b0 0xa8e01f0007803e1b 0x354700f8003c01f0

def z115 : W := mkw 0x010030a000000000 0x0008018500000000 0x000030f000000005 0x0000018780000000

def z116 : W := mkw 0x05a03aaa00000000 0x002d01d550000000 0xcfe03fff00000007 0x3e7f01fff8000000

def z117 : W := mkw 0x231c30e058616109 0x0118e18702c30b08 0xa71830c0f801f819 0x1d38c18607c00fc0

def z118 : W := mkw 0x00490444c444c544 0x900248222622262a 0x20000000c447c7e8 0x0100000006223e3f

def z119 : W := mkw 0x0009415541de5be6 0x38004a0aaa0ef2df 0xf03fd3ff07fe3fff 0xf781fe9ff83ff1ff

def z120 : W := mkw 0x035d34e4c444c544 0x901ae9a72622262a 0xffdf3cfcc447c7ef 0xfffef9e7e6223e3f

def z121 : W := mkw 0x2de83f50fee9ff99 0xe16f41fa87f74ffc 0xafe03f00fff9ff9b 0x3d7f01f807ffcffc

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000000000007e7 0x030000000000003f

def z123 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x8724c0003ffe0018 0xf439260001fff000

def z124 : W := mkw 0x0de03e00ae01a411 0xc06f01f005700d20 0x0fc02c00f801c000 0x087e016007c00e00

def z125 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5ffbefcf00000002 0xaaffdf7e78000000

def z126 : W := mkw 0x2008415159fb7bab 0x2900420a8acfdbdd 0x20000000fffffff8 0x0100000007ffffff

def z127 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xdfffecccfffe001f 0xfeffff6667fff000

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000000400060b 0x2500000000200030

def z129 : W := mkw 0x07b6fbbb019a1aa2 0x283db7ddd80cd0d5 0xffffffff07fe3fff 0xfffffffff83ff1ff

def z130 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fdfecff00000004 0xcafeff67f8000000

def z131 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x8fe4ff3300000003 0x3c7f27f998000000

def z132 : W := mkw 0x21003afa08096981 0x210801d7d0404b4c 0x68003fff0001f987 0x034001fff8000fcc

def z133 : W := mkw 0x0100300008012001 0x0008018000400900 0x07002000f801c000 0x0838010007c00e00

def z134 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x97ffc0003bb80010 0xfcbffe0001ddc000

def z135 : W := mkw 0x07f7beae84048444 0x903fbdf574202422 0xdfffffff04060667 0xfefffffff8203033

def z136 : W := mkw 0x0ce00f00a6809610 0xc0670078053404b0 0x08e00f0007800602 0x20470078003c0030

def z137 : W := mkw 0x2008005058696989 0x2100400282c34b4c 0x20000000f879f998 0x0100000007c3cfcc

def z138 : W := mkw 0x04e00000a6000010 0x0027000005300000 0x87e00000ff800018 0x3c3f000007fc0000

def z139 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x1fffffff00000000 0x18fffffff8000000

def z140 : W := mkw 0x0100301008092881 0x2008018080404944 0xa7043030f879f99d 0x5d38218187c3cfcc

def z141 : W := mkw 0x0ce04f11a79a9eb2 0xe86702788d3cd4f5 0xe8e4df3307fe3fff 0xf74726f9983ff1ff

def z142 : W := mkw 0x37ffb0e0fe65611d 0x01bffd8707f32b08 0x17db20c0f801c000 0x08bed90607c00e00

def z143 : W := mkw 0x00494555c5dedfe6 0xb8024a2aae2ef6ff 0xf8ffffffc7ffffff 0xffc7fffffe3fffff

def z144 : W := mkw 0x07ffbeeec444c544 0x903ffdf77622262a 0xffffffffc447c7ef 0xfffffffffe223e3f

def z145 : W := mkw 0x231d30f4586d69cd 0x3118e987a2c36b4e 0xf71f30fcf87ff9fd 0xdfb8f987e7c3ffcf

def z146 : W := mkw 0x17b6faaa3332001a 0x00bdb7d551999000 0x0724d3333bb80010 0x1039269999ddc000

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8ffffff00000007 0xfec7fffff8000000

def z148 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x0024d33303b83810 0x10012699981dc1c0

def z149 : W := mkw 0x09003f000881b601 0xc04801f800440db0 0xa8203f000781fe1b 0x354101f8003c0ff0

def z150 : W := mkw 0x0041000084040004 0x0002080004202000 0x10c3000004060000 0xa086180000203000

def z151 : W := mkw 0x0de2bf0aae81b611 0xc06f15f855740db0 0xffe3ff0fff81fe1b 0xbfff1ff87ffc0ff0

def z152 : W := mkw 0x0ce04f01a7929632 0xc86702780d3c94b1 0x48e0cf0307860662 0xa2470678183c3033

def z153 : W := mkw 0x031430a008012001 0x0018a18500400900 0xa71c30f0f801f81d 0x5d38e18787c00fc0

def z154 : W := mkw 0x10494000f776001e 0x00824a0007bbb000 0x00000000fffe0018 0x0000000007fff000

def z155 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffd333fffe001f 0xfebffe999ffff000

def z156 : W := mkw 0x14e3c404a7168456 0x90a71e202538b422 0x58e3cc0c07860662 0xa2c71e60603c3033

def z157 : W := mkw 0x04eb8e4ec444c544 0x90275c727622262a 0xf8fbefcfc447c7ef 0xefc7df7e7e223e3f

def z158 : W := mkw 0x17fffaaaf776001e 0x00bfffd557bbb000 0x97ffd333fffe0018 0xfcbffe999ffff000

def z159 : W := mkw 0x0214000010200008 0x0010a00000810000 0x0704000038380010 0x1038200001c1c000

def z160 : W := mkw 0x05a03a0000000000 0x002d01d000000000 0xdffb3fcc00000007 0xfeffd9fe60000000

def z161 : W := mkw 0x221c41f151fa5baa 0x2910e20f8a8fd2dd 0xe03cd3f307fe3fff 0xf701e69f983ff1ff

def z162 : W := mkw 0x36ffc050ff7f699f 0x21b7fe0287fbfb4c 0xb7ffc000fffff998 0xfdbffe0007ffffcc

def z163 : W := mkw 0x235d34f4dc6dedcd 0xb11ae9a7a6e36f6e 0xbfdf3cfcf879f99d 0x5dfef9e7e7c3cfcc

def z164 : W := mkw 0x0de03e00ae01a411 0xc06f01f005700d20 0x8fe03f00f801c003 0x3c7f01f807c00e00

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0xe024d333044607ef 0xf70126999822303f

def z166 : W := mkw 0x07b6fbbb019a1aa2 0x283db7ddd80cd0d5 0xe724d33307fe3fff 0xf7392699983ff1ff

def z167 : W := mkw 0x27bc3af058696989 0x213de1d782c34b4c 0xaffc3ff0f879f99f 0x7d7fe1ff87c3cfcc

def z168 : W := mkw 0x200000f000084980 0x210000078000424c 0x000000f000000184 0x000000078000000c

def z169 : W := mkw 0x14e3c000a7160016 0x00a71e000538b000 0x10e3c00007860000 0xa0871e00003c3000

def z170 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe4ff33ff81fe1f 0xff7f27f99ffc0ff0

def z171 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271820c0f879f998 0x0938c10607c3cfcc

def z172 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x27041030f879f998 0x1138208187c3cfcc

def z173 : W := mkw 0x05a03b0000801200 0x002d01d800040090 0xafe03f0007803e1b 0x3d7f01f8003c01f0

def z174 : W := mkw 0x08400500ae81b611 0xc042002805740db0 0xa0201300ff81fe1b 0x3501009807fc0ff0

def z175 : W := mkw 0x07b6ba0000000000 0x003db5d000000000 0x9fffff0000000003 0xfcfffff800000000

def z176 : W := mkw 0x16ff8444f664c55c 0x90b7fc2227b3262a 0x1fdb2cccf801c000 0x08fed96667c00e00

def z177 : W := mkw 0x27fc30f0fe696999 0x213fe18787f34b4c 0xa7fc30f0fff9f99d 0x7d3fe18787ffcfcc

def z178 : W := mkw 0x321fc0f0517e498e 0x2190fe07828bf24c 0x101fc0f0007e0184 0xc080fe078003f00c

def z179 : W := mkw 0x0009004440444144 0x100048022202220a 0x00000000004601e0 0x000000000002300f

def z180 : W := mkw 0x16ffc0aaf776001e 0x00b7fe0557bbb000 0xd7ffc0fffffe001c 0xfebffe07fffff000

def z181 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe73cf3f3f879f99f 0xff39e79f9fc3cfcc

def z182 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xf8ffffff07fe3fff 0xffc7fffff83ff1ff

def z183 : W := mkw 0x025f84eec444c544 0x9012fc277622262a 0xf8dfecffc447c7ef 0xefc6ff67fe223e3f

def z184 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6004d333007e3fe7 0xc30026999803f1ff

def z185 : W := mkw 0x231430b018292889 0x2118a18580c14944 0xa70410303878399d 0x5538208181c3c1cc

def z186 : W := mkw 0x231c31f058e97b89 0x2118e18f82c74bdc 0xa73c33f0fff9ff9f 0x7d39e19f87ffcffc

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x8020130000000003 0x3401009800000000

def z188 : W := mkw 0x00490444c444c544 0x900248222622262a 0xd8db2cccc001c007 0xeec6d96666000e00

def z189 : W := mkw 0x17fffaaaf776001e 0x00bfffd557bbb000 0x9fffecccfffe0018 0xfcffff6667fff000

def z190 : W := mkw 0x07b6faaa01120002 0x003db7d550089000 0xdfffffff07fe001f 0xfefffffff83ff000

def z191 : W := mkw 0x08404511af9bbeb3 0xe84202288d7cddf5 0xe024d333ffffffff 0xf70126999fffffff

def z192 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfdb2ccc00000007 0xeefed96660000000

def z193 : W := mkw 0x10494444f776c55e 0x90824a2227bbb62a 0x20000000ffffc7f8 0x0100000007fffe3f

def z194 : W := mkw 0x0ce00500ae81b611 0xc067002805740db0 0xa7e00000ff81fe18 0x3d3f000007fc0ff0

def z195 : W := mkw 0x231430f008096981 0x2118a18780404b4c 0xa71c30f00001f985 0x5d38e18780000fcc

def z196 : W := mkw 0x221c00e050604108 0x0110e00702830208 0x001800c000000000 0x0000c00600000000

def z197 : W := mkw 0x0de03f10ae89be91 0xe06f01f885744df4 0xafe43f30fff9ff9f 0x7d7f21f987ffcffc

def z198 : W := mkw 0x000004440000c540 0x900000222000062a 0xe8002ccc0447c7ef 0xe740016660223e3f

def z199 : W := mkw 0x0008415141da5ba2 0x2800420a8a0ed2dd 0xe03cf3f3c7ffffff 0xff01e79f9e3fffff

def z200 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x4024d33307be3e72 0xb2012699983df1f3

def z201 : W := mkw 0x0000001000080880 0x2000000080004044 0xe024d3330078399f 0xf70126999803c1cc

def z202 : W := mkw 0x1de3ff00af97b617 0xc0ef1ff8057cbdb0 0xbfe3ff00ff87fe1b 0xbdff1ff807fc3ff0

def z203 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x4024c33307fe07e6 0xe2012619983ff03f

def z204 : W := mkw 0x08400500ae81b611 0xc042002805740db0 0xa8c02c00ff81fe1b 0x2d46016007fc0ff0

def z205 : W := mkw 0x27b6baba18292889 0x213db5d5d0c14944 0xdfffffff38383817 0xfefffffff9c1c1c0

def z206 : W := mkw 0x0ce28f0aa6809610 0xc0671478553404b0 0x58e3cf0f07800602 0xa2c71e78783c0030

def z207 : W := mkw 0x07b6fbbb019a1aa2 0x283db7ddd80cd0d5 0xdfffffff03b83817 0xfefffffff81dc1c0

def z208 : W := mkw 0x37fff4f4ff7feddf 0xb1bfffa7a7fbff6e 0xfffffcfcffffffff 0xffffffe7e7ffffff

def z209 : W := mkw 0x05a03a0000000000 0x002d01d000000000 0x8fe03f0000000003 0x3c7f01f800000000

def z210 : W := mkw 0x27bebaea58616109 0x013df5d752c30b08 0x1fdb2cccf801c000 0x08fed96667c00e00

def z211 : W := mkw 0x031c300058612009 0x0018e18002c30900 0xa71c3000f879f819 0x5d38e18007c3cfc0

def z212 : W := mkw 0x00490000c4440004 0x0002480006222000 0xd8db2cccc446000f 0xeec6d96666223000

def z213 : W := mkw 0x37fff1f1ffff7bbf 0x29bfff8f8ffffbdd 0xf7fff3f3ffffffff 0xffbfff9f9fffffff

def z214 : W := mkw 0x10414000a7160016 0x00820a000538b000 0x0000000007860000 0x00000000003c3000

def z215 : W := mkw 0x16ffc111f7fe1abe 0x28b7fe088fbff0d5 0xb7ffc000fffe3ff8 0xfdbffe0007fff1ff

def z216 : W := mkw 0x04a28a0a00000000 0x0025145050000000 0xd8fbefcf00000007 0xeec7df7e78000000

def z217 : W := mkw 0x04a00a0000000000 0x0025005000000000 0x08e00f0000000002 0x2047007800000000

def z218 : W := mkw 0x08490544eec5f755 0xd042482a27762fba 0xf8db2cccffc7ffff 0xefc6d96667fe3fff

def z219 : W := mkw 0x231c71f159fb7bab 0x2918e38f8acfdbdd 0xa73cf3f3fbf9f99d 0x5d39e79f9fdfcfcc

def z220 : W := mkw 0x0de03f11ae89beb1 0xe86f01f88d744df5 0xefe03f33ff81ffff 0x3f7f01f99ffc0fff

def z221 : W := mkw 0x0000001000080880 0x2000000080004044 0xa00410300078399d 0x550020818003c1cc

def z222 : W := mkw 0x18494500fff7b61f 0xc0c24a2807ffbdb0 0x20000000fffffe18 0x0100000007fffff0

def z223 : W := mkw 0x06b68a0a00000000 0x0035b45050000000 0xdfffcf0f00000002 0xfefffe7878000000

def z224 : W := mkw 0x16ff8000f664001c 0x00b7fc0007b32000 0x97ffc000f8000000 0xfcbffe0007c00000

def z225 : W := mkw 0x1fffff11ffffbebf 0xe8fffff88ffffdf5 0xffffff33ffffffff 0xfffffff99fffffff

def z226 : W := mkw 0x16ffc111f7fe1abe 0x28b7fe088fbff0d5 0xf7ffd333fffe3fff 0xffbffe999ffff1ff

def z227 : W := mkw 0x0100300008012001 0x0008018000400900 0x0700100038003810 0x1038008001c001c0

def z228 : W := mkw 0x16ff8000f664001c 0x00b7fc0007b32000 0x97df0000f8780018 0x5cbef80007c3c000

def z229 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xffdf3cfcf879f99f 0xfffef9e7e7c3cfcc

def z230 : W := mkw 0x14a2c00023120012 0x00a5160001189000 0x0020c00003800000 0x00010600001c0000

def z231 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x873cf3f300000005 0x5c39e79f98000000

def z232 : W := mkw 0x06b680aa00000000 0x0035b40550000000 0xd7ffc0ff00000004 0xfebffe07f8000000

def z233 : W := mkw 0x0000410101921222 0x08000208080c9091 0x0020c30303800000 0x00010618181c0000

def z234 : W := mkw 0x17fffeeef776c55e 0x90bffff777bbb62a 0xffffffffffffc7ff 0xfffffffffffffe3f

def z235 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0xa7203300fb81f819 0x1d39019807dc0fc0

def z236 : W := mkw 0x14e94000f776001e 0x00a74a0007bbb000 0x87e00000fffe0018 0x3c3f000007fff000

def z237 : W := mkw 0x06ff8444c444c544 0x9037fc222622262a 0xffffecccc447c7ef 0xffffff6666223e3f

def z238 : W := mkw 0x09493f44ccc5f745 0xd04a49fa26662fba 0xf8db3fccc447ffef 0xefc6d9fe66223fff

def z239 : W := mkw 0x07b6baaa08012001 0x003db5d550400900 0xfffffffff801f81f 0xffffffffffc00fc0

def z240 : W := mkw 0x07bebaaa50600008 0x003df5d552830000 0xdffffffff878001f 0xfeffffffffc3c000

def z241 : W := mkw 0x0000004000004100 0x0000000200000208 0x200020c00001c185 0x0100010600000e0c

def z242 : W := mkw 0x16b6c11133ba1aba 0x28b5b608899dd0d5 0xe724d3333ffe3fff 0xf739269999fff1ff

def z243 : W := mkw 0x2108305058696989 0x2108418282c34b4c 0xa7003000f879f999 0x1d38018007c3cfcc

def z244 : W := mkw 0x00004011011a08a2 0x280002008808d045 0xe004d033007e39fd 0xd70026819803f1cf

def z245 : W := mkw 0x05e03e0084008400 0x802f01f004200420 0xafe03f00c401c60b 0x3d7f01f806200e30

def z246 : W := mkw 0x0000010000801200 0x0000000800040090 0xe020130007c63fff 0xf7010098003e31ff

def z247 : W := mkw 0x231430f018296989 0x2118a18780c14b4c 0x270430f03839f995 0x1138218781c1cfcc

def z248 : W := mkw 0x210830f048496981 0x2108418782424b4c 0xa01830f0c041f98d 0x4d00c18786020fcc

def z249 : W := mkw 0x0000011000881a80 0x20000008800440d4 0xa024133007f83f9f 0x75012099803fc1fc

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000004601e4 0xc20000000002300f

def z251 : W := mkw 0x0000001000080880 0x2000000080004044 0x0004003000780184 0x400020018003c00c

def z252 : W := mkw 0x121fc011517e08ae 0x2890fe008a8bf045 0x501fc033007e01e4 0xc280fe019803f00f

def z253 : W := mkw 0x021c40005172000a 0x0010e200028b9000 0x873cc000fffe0018 0xfc39e60007fff000

def z254 : W := mkw 0x04a0000022000010 0x0025000001100000 0x072000003b800010 0x1039000001dc0000

def z255 : W := mkw 0x121fc0005176000e 0x0090fe00028bb000 0x903fc00007fe0018 0xf481fe00003ff000

def z256 : W := mkw 0x00490044c4444144 0x100248022622220a 0xd0db00ccc44601ec 0xee86d8066622300f

def z257 : W := mkw 0x01003aaa00000000 0x000801d550000000 0x08002ccc00000000 0x0040016660000000

def z258 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x071c20f0f879c184 0x4838e10787c3ce0c

def z259 : W := mkw 0x0009004440444144 0x100048022202220a 0x501b00cc004601e4 0xc280d8066002300f

def z260 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fe7df3f00000002 0xb2ff3ef9f8000000

def z261 : W := mkw 0x17fffa00f776001e 0x00bfffd007bbb000 0x9fffff00fffe001b 0xfcfffff807fff000

def z262 : W := mkw 0x09003faa0881b601 0xc04801fd50440db0 0x68003fff0001fe07 0x034001fff8000ff0

def z263 : W := mkw 0x00400000a6000010 0x0002000005300000 0x00000000ff800018 0x0000000007fc0000

def z264 : W := mkw 0x00490444c444c544 0x900248222622262a 0x58db2cccc047c1e4 0xcac6d96666023e0f

def z265 : W := mkw 0x07b6baba00080880 0x203db5d5d0004044 0xffffffff0078399f 0xfffffffff803c1cc

def z266 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2cccc001c7e7 0x0bc6d96666000e3f

def z267 : W := mkw 0x210030f008096981 0x2108018780404b4c 0xa00430f00079f99d 0x550021878003cfcc

def z268 : W := mkw 0x00004011011a08a2 0x280002008808d045 0xc024c03307fe01fc 0xf6012601983ff00f

def z269 : W := mkw 0x04a2cb0b01921222 0x08251658580c9091 0x58e3cf0f07860662 0xa2c71e78783c3033

def z270 : W := mkw 0x231471b119bb3aab 0x2918a38d88cdd9d5 0xe724d3333ffe3fff 0xf739269999fff1ff

def z271 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6020c30307fe3ffa 0xa3010618183ff1ff

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000044607e8 0x010000000022303f

def z273 : W := mkw 0x0000410001921202 0x00000208000c9090 0xa024d30007fe3e1b 0xf5012698003ff1f0

def z274 : W := mkw 0x0000400001120002 0x0000020000089000 0x0004c000007e0000 0xc00026000003f000

def z275 : W := mkw 0x0de03b00ae813211 0x406f01d805740990 0x87e01300ff803818 0x3c3f009807fc01c0

def z276 : W := mkw 0x0ff6beaaae01a411 0xc07fb5f555700d20 0x1fdb2cccf801c000 0x08fed96667c00e00

def z277 : W := mkw 0x04e00000a6000010 0x0027000005300000 0x00e0000007800000 0x20070000003c0000

def z278 : W := mkw 0x1fffbe00fe65a41d 0xc0fffdf007f32d20 0x1fdb2c00f801c000 0x08fed96007c00e00

def z279 : W := mkw 0x2de03ff0ae89ff91 0xe16f01ff85744ffc 0xafe03ff0ff81ff9f 0x3d7f01ff87fc0ffc

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000133300000007 0x0200009998000000

def z281 : W := mkw 0x07ffffffc5dedfe6 0xb83ffffffe2ef6ff 0xffffffffc7ffffff 0xfffffffffe3fffff

def z282 : W := mkw 0x231c30f050684988 0x2118e1878283424c 0x871c30f000780185 0x5c38e1878003c00c

def z283 : W := mkw 0x210030b008092881 0x2108018580404944 0x0000103000003800 0x00000081800001c0

def z284 : W := mkw 0x14e3ca0aa7160016 0x00a71e505538b000 0x58e3cf0f07860002 0xa2c71e78783c3000

def z285 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa004103007fe3ffd 0x55002081803ff1ff

def z286 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17dfc000f87e0000 0xc8befe0007c3f000

def z287 : W := mkw 0x04e04000a7120012 0x0027020005389000 0x87e4c000fffe0018 0xfc3f260007fff000

def z288 : W := mkw 0x1ce3cf00a7969616 0xc0e71e78053cb4b0 0x18e3cf0007860602 0xa0c71e78003c3030

def z289 : W := mkw 0x07ffbeeec444c544 0x903ffdf77622262a 0xffdb2cccc447c7ef 0xeffed96666223e3f

def z290 : W := mkw 0x16ffc111f7fe1abe 0x28b7fe088fbff0d5 0x97ffd333fffe3818 0xfcbffe999ffff1c0

def z291 : W := mkw 0x16ffc044f776415e 0x10b7fe0227bbb20a 0xd7ffc0ccfffe01fc 0xfebffe0667fff00f

def z292 : W := mkw 0x0ce00e00a6008410 0xc067007005300420 0x08c00c0000000000 0x0046006000000000

def z293 : W := mkw 0x01003aaa00000000 0x000801d550000000 0xc824ffff00000007 0xf64127fff8000000

def z294 : W := mkw 0x031430a000000000 0x0018a18500000000 0x871c30f000000005 0x5c38e18780000000

def z295 : W := mkw 0x0de93f44eec5f755 0xd06f49fa27762fba 0xafe03f00ffc7fffb 0x3d7f01f807fe3fff

def z296 : W := mkw 0x0040040084008400 0x8002002004200420 0xf8db2cccc401c60f 0xefc6d96666200e30

def z297 : W := mkw 0x00494555c5dedfe6 0xb8024a2aae2ef6ff 0xf8db2cccc7ffffff 0xefc6d966663fffff

def z298 : W := mkw 0x0000001000080880 0x2000000080004044 0x2000000000783998 0x010000000003c1cc

def z299 : W := mkw 0x0008004040404100 0x0000400202020208 0xa01820c0c041c18d 0x4d00c10606020e0c

def z300 : W := mkw 0x0de03faaae81b611 0xc06f01fd55740db0 0xefe03fffff81fe1f 0x3f7f01fffffc0ff0

def z301 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x0700000000000000 0x0038000000000000

def z302 : W := mkw 0x04a28a0a00000000 0x0025145050000000 0x18c30c0c00000000 0x00c6186060000000

def z303 : W := mkw 0x0de07f00af93b613 0xc06f03f8057c9db0 0xafe4ff00fffffe1b 0xfd7f27f807fffff0

def z304 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0x0000133300003800 0x00000099980001c0

def z305 : W := mkw 0x07bebaea40404100 0x003df5d752020208 0xffffffffc041c18f 0xfffffffffe020e0c

def z306 : W := mkw 0x05a03a0000000000 0x002d01d000000000 0xcfe4ff3300000007 0xfe7f27f998000000

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x501b00cc00000004 0xc280d80660000000

def z308 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x2024d33307fe3ff8 0x11012699983ff1ff

def z309 : W := mkw 0x16f7c000b736001e 0x00b7be0005b9b000 0x17e7c0003fbe0010 0xb0bf3e0001fdf000

def z310 : W := mkw 0x2ffd3ff4feedffdd 0xf17fe9ffa7f76ffe 0xffff3ffcffffffff 0xfffff9ffe7ffffff

def z311 : W := mkw 0x01003aaa00000000 0x000801d550000000 0xd8db3fff00000007 0xeec6d9fff8000000

def z312 : W := mkw 0x2fbc3bf07ae97b99 0x617de1df83d74bdc 0xa73c33f0fbf9f99d 0x5d39e19f87dfcfcc

def z313 : W := mkw 0x14e3c111a79e1ab6 0x28a71e088d3cf0d5 0xf0e7d33307fe3fff 0xf7873e99983ff1ff

def z314 : W := mkw 0x00490404c4448444 0x9002482026222422 0xd8db0c0cc446066a 0xeec6d86066223033

def z315 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x071c30f0f839f810 0x1838e18787c1cfc0

def z316 : W := mkw 0x09003e000801a401 0xc04801f000400d20 0x08002c000001c000 0x0040016000000e00

def z317 : W := mkw 0x00490444c444c544 0x900248222622262a 0x58db2cccc407c662 0xaac6d96666203e33

def z318 : W := mkw 0x0de13f04ae85b655 0xd06f09f825742db2 0xffe33f0cff87fe7b 0xbfff19f867fc3ff3

def z319 : W := mkw 0x00490444c444c544 0x900248222622262a 0x68002cccc447c7ef 0x0340016666223e3f

def z320 : W := mkw 0x06f68000a6000010 0x0037b40005300000 0x97ffc000ff800018 0xfcbffe0007fc0000

def z321 : W := mkw 0x06b6800000000000 0x0035b40000000000 0x97ffc00000000000 0xfcbffe0000000000

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000000007 0xe600000000000000

def z323 : W := mkw 0x01003bbb00881aa0 0x280801ddd80440d5 0x68003fff00003fe7 0x034001fff80001ff

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004000000780018 0x540020000003c000

def z325 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x27201300ff81fe18 0x1139009807fc0ff0

def z326 : W := mkw 0x210071f1099b7ba3 0x2908038f884cdbdd 0xe024f3f307ffffff 0xf701279f983fffff

def z327 : W := mkw 0x00490454c44ccdc4 0xb0024822a622666e 0xf8df3cfcc47fffff 0xffc6f9e7e623ffff

def z328 : W := mkw 0x0ff43fa0ae81b611 0xc07fa1fd05740db0 0xaffc3ff0ff81fe1f 0x7d7fe1ff87fc0ff0

def z329 : W := mkw 0x000804444040c540 0x900040222202062a 0xe8182cccc041c7ef 0x4f40c16666020e3f

def z330 : W := mkw 0x00494545c5d6d766 0x98024a2a2e2eb6bb 0xf8fbefcfc7c7c7ef 0xefc7df7e7e3e3e3f

def z331 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x0724c000fffe0018 0x1039260007fff000

def z332 : W := mkw 0x10494111f7fe1abe 0x28824a088fbff0d5 0xe024d333fffe3fff 0xf70126999ffff1ff

def z333 : W := mkw 0x0000410101921222 0x08000208080c9091 0xc024d33307860667 0xf6012699983c3033

def z334 : W := mkw 0x00490000c4440004 0x0002480006222000 0x90db0000c4460008 0xec86d80006223000

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x18db2ccc00000000 0x08c6d96660000000

def z336 : W := mkw 0x28480550fee9ff99 0xe142402a87f74ffc 0x20000000fff9ff98 0x0100000007ffcffc

def z337 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xc724d33300000007 0xf639269998000000

def z338 : W := mkw 0x231471b119bb3aab 0x2918a38d88cdd9d5 0x0724d3333bb83810 0x1039269999ddc1c0

def z339 : W := mkw 0x04a28a0a00000000 0x0025145050000000 0xd8e7df3f00000007 0xf6c73ef9f8000000

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x801820c000000005 0x4c00c10600000000

def z341 : W := mkw 0x08400400ae01a411 0xc042002005700d20 0x00000000f801c000 0x0000000007c00e00

def z342 : W := mkw 0x06be800050600008 0x0035f40002830000 0x97ffc000f8780018 0xfcbffe0007c3c000

def z343 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x0fe02f00ff81c602 0x287f017807fc0e30

def z344 : W := mkw 0x231430b018292889 0x2118a18580c14944 0x871c30f038383815 0x5c38e18781c1c1c0

def z345 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x573fd3ff00000004 0xd2b9fe9ff8000000

def z346 : W := mkw 0x0de93e44ee45e555 0xd06f49f227722f2a 0x1fdb2cccf801c000 0x08fed96667c00e00

def z347 : W := mkw 0x0de07f11af9bbeb3 0xe86f03f88d7cddf5 0xafe03f00fffffffb 0x3d7f01f807ffffff

def z348 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271830f0f801f985 0x0938c18787c00fcc

def z349 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020c30300000002 0xa201061818000000

def z350 : W := mkw 0x121f80005064000c 0x0090fc0002832000 0x101b000000000000 0x0080d80000000000

def z351 : W := mkw 0x1ffffe00ff77a41f 0xc0fffff007fbbd20 0x9fffec00ffffc018 0xfcffff6007fffe00

def z352 : W := mkw 0x1ffffb00fff7321f 0x40ffffd807ffb990 0x97ffd300fffe3818 0xfcbffe9807fff1c0

def z353 : W := mkw 0x0100300008012001 0x0008018000400900 0x200030000001f801 0x0100018000000fc0

def z354 : W := mkw 0x14ebc000e7560016 0x00a75e00073ab000 0x90fbc000c7c60008 0xec87de00063e3000

def z355 : W := mkw 0x16ffca0af776001e 0x00b7fe5057bbb000 0xdfffcf0ffffe001a 0xfefffe787ffff000

def z356 : W := mkw 0x0000000000000000 0x0000000000000000 0x88c02c0000000003 0x2c46016000000000

def z357 : W := mkw 0x04a0000000000000 0x0025000000000000 0x87e0000000000000 0x3c3f000000000000

def z358 : W := mkw 0x16ffc555f7fedffe 0xb8b7fe2aafbff6ff 0xffffffffffffffff 0xffffffffffffffff

def z359 : W := mkw 0x210030e008016101 0x0108018700400b08 0x000020c00001c000 0x0000010600000e00

def z360 : W := mkw 0x0fffbfeeeec5f755 0xd07ffdff77762fba 0xffffffffffc7ffff 0xfffffffffffe3fff

def z361 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0xe000133304463fef 0xe7000099982231ff

def z362 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0xe020133307803fff 0x37010099983c01ff

def z363 : W := mkw 0x00000011000808a0 0x2800000088004045 0x40000033000001e4 0x020000019800000f

def z364 : W := mkw 0x214934f4cc4dedc5 0xb10a49a7a6626f6e 0xf8db3cfcc447ffef 0xefc6d9e7e6223fff

def z365 : W := mkw 0x0100310008813201 0x0008018800440990 0xa7203300ff81fe1b 0x3d39019807fc0ff0

def z366 : W := mkw 0x0108304048416101 0x0008418202420b08 0xa71830c0f841f99d 0x5d38c18607c20fcc

def z367 : W := mkw 0x0041040484048444 0x9002082024202422 0xd8db2ccc04060667 0xeec6d96660203033

def z368 : W := mkw 0x37b6f0b03b3b289b 0x21bdb78581d9d944 0x0724d0303bb83810 0x1039268181ddc1c0

def z369 : W := mkw 0x37ffb0f0fe6d699d 0x21bffd8787f36b4c 0xb7df30f0f879f99d 0x5dbef98787c3cfcc

def z370 : W := mkw 0x30494050ff7f699f 0x21824a0287fbfb4c 0x20000000fffff998 0x0100000007ffffcc

def z371 : W := mkw 0x00490000c4440004 0x0002480006222000 0xf0db0000c44607ef 0xef86d8000622303f

def z372 : W := mkw 0x0040040084008400 0x8002002004200420 0x08c00c0004000602 0x2046006000200030

def z373 : W := mkw 0x05a2ba0a00000000 0x002d15d050000000 0xdfe3ff0f00000003 0xbeff1ff878000000

def z374 : W := mkw 0x36ffc0f0f77e499e 0x21b7fe0787bbf24c 0x97ffc0f0fffe019c 0xfcbffe0787fff00c

def z375 : W := mkw 0x16ff8444f664c55c 0x90b7fc2227b3262a 0xffdb2cccfc47c7ef 0xeffed96667e23e3f

def z376 : W := mkw 0x37fff0e0ff77611f 0x01bfff8707fbbb08 0x97ffe0c0ffffc018 0xfcbfff0607fffe00

def z377 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6024d33303b83ff7 0x13012699981dc1ff

def z378 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xf7ffc000fffe07ff 0xffbffe0007fff03f

def z379 : W := mkw 0x06ff8000c4440004 0x0037fc0006222000 0x97ffc000c4460008 0xfcbffe0006223000

def z380 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa024d33307b83e1b 0x35012699983dc1f0

def z381 : W := mkw 0x0000410101921222 0x08000208080c9091 0xe020d30307863e7b 0xb7010698183c31f3

def z382 : W := mkw 0x0000410101921222 0x08000208080c9091 0xe020c30307c607ef 0xe7010618183e303f

def z383 : W := mkw 0x0000010000801200 0x0000000800040090 0x0020030007800602 0x20010018003c0030

def z384 : W := mkw 0x07b6b0a000000000 0x003db58500000000 0x97fff0f000000005 0xfcbfff8780000000

def z385 : W := mkw 0x0da07b112b9b3ab3 0x686d03d8895cd9d5 0xe724d3333ffe3fff 0xf739269999fff1ff

def z386 : W := mkw 0x0000010100801220 0x0800000808040091 0x4000030300000662 0x0200001818000033

def z387 : W := mkw 0x00404511859a9ea2 0xa80202288c2cd4f5 0xe8e4ff33c7ffffff 0xff4727f99e3fffff

def z388 : W := mkw 0x031430a000000000 0x0018a18500000000 0xdfdf3cfc00000007 0xfefef9e7e0000000

def z389 : W := mkw 0x1fffbf00fee5b61d 0xc0fffdf807f72db0 0xbffb3f00ff81fe1b 0x3dffd9f807fc0ff0

def z390 : W := mkw 0x0000004400004140 0x100000022000020a 0x400000cc000001e4 0x020000066000000f

def z391 : W := mkw 0x17fff000ff77201f 0x00bfff8007fbb900 0xb7fff000fffff819 0xfdbfff8007ffffc0

def z392 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fdb3fff00000007 0x0afed9fff8000000

def z393 : W := mkw 0x08400500a6809610 0xc0420028053404b0 0x0000000007800600 0x00000000003c0030

def z394 : W := mkw 0x210830f058696989 0x2108418782c34b4c 0x200030f0f879f99d 0x0100018787c3cfcc

def z395 : W := mkw 0x00490000c4440004 0x0002480006222000 0x10db0000c0000000 0x0886d80006000000

def z396 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x071c10f038783994 0x5038e08781c3c1cc

def z397 : W := mkw 0x080005000881b601 0xc040002800440db0 0x200000000001fe00 0x0100000000000ff0

def z398 : W := mkw 0x16ff8000f664001c 0x00b7fc0007b32000 0x97fb0000ff800018 0x3cbfd80007fc0000

def z399 : W := mkw 0x07bfbaee40444144 0x103dfdd77202220a 0xdfffffff004601e7 0xfefffffff802300f

def z400 : W := mkw 0x09403f008c81b601 0xc04a01f804640db0 0xa8c03f00c401fe0b 0x2d4601f806200ff0

def z401 : W := mkw 0x0ff6ffbbaf9bbeb3 0xe87fb7fddd7cddf5 0xffffffffffffffff 0xffffffffffffffff

def z402 : W := mkw 0x0da03f002a81b611 0xc06d01f801540db0 0x2f203f003b81fe13 0x117901f801dc0ff0

def z403 : W := mkw 0x0ce00f00a6809610 0xc0670078053404b0 0xa8e02f00c781c60b 0x2d470178063c0e30

def z404 : W := mkw 0x05e03a00a6000010 0x002f01d005300000 0x8fe03f00ff80001b 0x3c7f01f807fc0000

def z405 : W := mkw 0x01007bbb019a1aa2 0x280803ddd80cd0d5 0xe824ffff07fe3fff 0xf74127fff83ff1ff

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000000040018d 0x450000000002000c

def z407 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xb7ffc000ffffc7f8 0xfdbffe0007fffe3f

def z408 : W := mkw 0x01003aaa00000000 0x000801d550000000 0x0000133300000000 0x0000009998000000

def z409 : W := mkw 0x1fffff44fff7f75f 0xd0fffffa27ffbfba 0xffffffccffffffff 0xfffffffe67ffffff

def z410 : W := mkw 0x05a07b11019a1aa2 0x282d03d8880cd0d5 0xefe4ff3307fe3fff 0xff7f27f9983ff1ff

def z411 : W := mkw 0x0ce90f44e6c4d754 0xd067487a273626ba 0xf8fb2fccc7c7c7ef 0xefc7d97e663e3e3f

def z412 : W := mkw 0x27bebaea58616109 0x013df5d752c30b08 0xdffffffff801c007 0xfeffffffffc00e00

def z413 : W := mkw 0x27b6bafa08096981 0x213db5d7d0404b4c 0xffffffff0001f987 0xfffffffff8000fcc

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x8020000007800018 0x34010000003c0000

def z415 : W := mkw 0x221d00f4506c49cc 0x3110e807a283624e 0x501f00fc007e01e4 0xc280f807e003f00f

def z416 : W := mkw 0x01493444cc45e545 0x900a49a226622f2a 0xffdb3cccfc47ffff 0xfffed9e667e23fff

def z417 : W := mkw 0x00004010011a0882 0x200002008008d044 0xa024d03007fe399d 0xf5012681803ff1cc

def z418 : W := mkw 0x231430b018292889 0x2118a18580c14944 0xa7043030f839f819 0x1d38218187c1cfc0

def z419 : W := mkw 0x231c34f45869edc9 0xb118e1a7a2c34f6e 0xef1c3cfcf879ffff 0x5f78e1e7e7c3cfff

def z420 : W := mkw 0x0000400001120002 0x0000020000089000 0x0024c00003b80010 0x10012600001dc000

def z421 : W := mkw 0x0ce00f00ae81b611 0xc067007805740db0 0x28e00f00ff81fe1a 0x2147007807fc0ff0

def z422 : W := mkw 0x27bebafa58696989 0x213df5d7d2c34b4c 0xbfdf3cfcf879f99d 0x5dfef9e7e7c3cfcc

def z423 : W := mkw 0x0000001000080880 0x2000000080004044 0x0004103000383810 0x100020818001c1c0

def z424 : W := mkw 0x231c31f158e97ba9 0x2918e18f8ac74bdd 0xe71c33f3f879ffff 0x5f38e19f9fc3cfff

def z425 : W := mkw 0x07b6fbab01921222 0x083db7dd580c9091 0xdfffffff07860667 0xfefffffff83c3033

def z426 : W := mkw 0x03143aaa00000000 0x0018a1d550000000 0xcf1c3fff00000007 0x5e78e1fff8000000

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000004460008 0xe400000000223000

def z428 : W := mkw 0x0008004040404100 0x0000400202020208 0xe01820c0c447c7ef 0xef00c10606223e3f

def z429 : W := mkw 0x00490444c444c544 0x900248222622262a 0xb8db2cccc041c18d 0x4dc6d96666020e0c

def z430 : W := mkw 0x0de03e00ae01a411 0xc06f01f005700d20 0xafc03c00f801f819 0x1d7e01e007c00fc0

def z431 : W := mkw 0x05a2baaa00000000 0x002d15d550000000 0x58e3ffff00000007 0xa2c71ffff8000000

def z432 : W := mkw 0x0041450585969666 0x98020a282c2cb4b3 0x58e3cf0f07860662 0xa2c71e78783c3033

def z433 : W := mkw 0x16ffc101f7f6123e 0x08b7fe080fbfb091 0xd7ffc303fffe067a 0xfebffe181ffff033

def z434 : W := mkw 0x231c70f0597b698b 0x2118e38782cbdb4c 0xa73cf0f0fffff99d 0xfd39e78787ffffcc

def z435 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17fbc000ff860000 0xa8bfde0007fc3000

def z436 : W := mkw 0x021680aa00000000 0x0010b40550000000 0xd8dfecff00000007 0xeec6ff67f8000000

def z437 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fc02c00ff81fe18 0x097e016007fc0ff0

def z438 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17db0000fffe0018 0x08bed80007fff000

def z439 : W := mkw 0x231c30e058616109 0x0118e18702c30b08 0x871c30f0f801c005 0x5c38e18787c00e00

def z440 : W := mkw 0x0001000400040044 0x1000080020002002 0x5003000c00060060 0x8280180060003003

def z441 : W := mkw 0x100040003332001a 0x0080020001999000 0x000000003bb80010 0x0000000001ddc000

def z442 : W := mkw 0x080001002a813211 0x4040000801540990 0x000000003b803810 0x0000000001dc01c0

def z443 : W := mkw 0x2fb43bb03aa93a99 0x617da1dd81d549d4 0x072413303bb83810 0x1039209981ddc1c0

def z444 : W := mkw 0x05a03a0000000000 0x002d01d000000000 0x0fc02c0000000000 0x087e016000000000

def z445 : W := mkw 0x0ca00b0022801210 0x4065005801140090 0x0020030003800000 0x00010018001c0000

def z446 : W := mkw 0x04a2cb1b019a1aa2 0x28251658d80cd0d5 0xf8e7df3f07fe3fff 0xf7c73ef9f83ff1ff

def z447 : W := mkw 0x04e90444e644c554 0x902748222732262a 0xfffb2cccffc7c7ff 0xffffd96667fe3e3f

def z448 : W := mkw 0x00490000c4440004 0x0002480006222000 0x00000000c4460008 0x0000000006223000

def z449 : W := mkw 0x05a03a0000000000 0x002d01d000000000 0x0720130000000000 0x1039009800000000

def z450 : W := mkw 0x00490444c444c544 0x900248222622262a 0xa01820c0c447c7ed 0x4d00c10606223e3f

def z451 : W := mkw 0x16f7c000a7160016 0x00b7be000538b000 0x97ffc00007860000 0xfcbffe00003c3000

def z452 : W := mkw 0x0ce00f00a6809610 0xc0670078053404b0 0x8fe00f00ff80061a 0x3c7f007807fc0030

def z453 : W := mkw 0x09003b0008813201 0x404801d800440990 0x0000130000003800 0x00000098000001c0

def z454 : W := mkw 0x0008000040400000 0x0000400002020000 0x80180000c0400008 0x4c00c00006020000

def z455 : W := mkw 0x01003eee0000c540 0x900801f77000062a 0x68003fff0001c7e7 0x034001fff8000e3f

def z456 : W := mkw 0x021c411151fa1aaa 0x2810e2088a8fd0d5 0xe73cd333fffe3fff 0xff39e6999ffff1ff

def z457 : W := mkw 0x0008004040404100 0x0000400202020208 0x001820c0c001c000 0x0800c10606000e00

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8db2ccc044607ef 0xefc6d9666022303f

def z459 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xffffffff044607ef 0xfffffffff822303f

def z460 : W := mkw 0x0040050084809600 0x80020028042404b0 0xa8e03f00c781fe1b 0x3d4701f8063c0ff0

def z461 : W := mkw 0x0de03e00ae01a411 0xc06f01f005700d20 0xafc02c00fc01c60b 0x2d7e016007e00e30

def z462 : W := mkw 0x17ffbaaaf664001c 0x00bffdd557b32000 0xdffffffff8000007 0xfeffffffffc00000

def z463 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x4024d33303fe39f4 0xd2012699981ff1cf

def z464 : W := mkw 0x07ffbaaac4440004 0x003ffdd556222000 0xdfffffffc446000f 0xfefffffffe223000

def z465 : W := mkw 0x2000005008096981 0x2100000280404b4c 0x200000000001f980 0x0100000000000fcc

def z466 : W := mkw 0x0de97f55efdffff7 0xf86f4bfaaf7effff 0xffffffffffffffff 0xffffffffffffffff

def z467 : W := mkw 0x27befbfb59fb7bab 0x293df7dfdacfdbdd 0xffffffffffffffff 0xffffffffffffffff

def z468 : W := mkw 0x1ff6ff00bfb3b61b 0xc0ffb7f805fd9db0 0xafe4ff00ffb9fe1b 0x3d7f27f807fdcff0

def z469 : W := mkw 0x0ff6bfaaa6809610 0xc07fb5fd553404b0 0xdfffffff07800607 0xfefffffff83c0030

def z470 : W := mkw 0x231430a018212009 0x0118a18500c10900 0x0700000038000000 0x0038000001c00000

def z471 : W := mkw 0x121fc11151fe1aae 0x2890fe088a8ff0d5 0xf03fd33307fe3fff 0xf781fe99983ff1ff

def z472 : W := mkw 0x1216c0001132000a 0x0090b60000899000 0x0004c00000380000 0x000026000001c000

def z473 : W := mkw 0x06b6800000000000 0x0035b40000000000 0xdfffeccc00000007 0xfeffff6660000000

def z474 : W := mkw 0x021c004050604108 0x0010e00202830208 0xa71c20c0f879c19d 0x5d38e10607c3ce0c

def z475 : W := mkw 0x07b6bbbb00881aa0 0x283db5ddd80440d5 0xffffffff00003fe7 0xfffffffff80001ff

def z476 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x201c30f00079f985 0x4100e1878003cfcc

def z477 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6020d33307863fe7 0xa3010699983c31ff

def z478 : W := mkw 0x27ffbefedc6dedcd 0xb13ffdf7f6e36f6e 0xfffffffffc7fffff 0xffffffffffe3ffff

def z479 : W := mkw 0x0009004440444144 0x100048022202220a 0xd8db2ccc004601e7 0xeec6d9666002300f

def z480 : W := mkw 0x07b6fbbb019a1aa2 0x283db7ddd80cd0d5 0x0724d33303b83810 0x10392699981dc1c0

def z481 : W := mkw 0x00490444c444c544 0x900248222622262a 0x98db2cccc447c008 0xecc6d96666223e00

def z482 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x9fffeccc00000000 0xfcffff6660000000

def z483 : W := mkw 0x00490444c444c544 0x900248222622262a 0xb8db2cccc401c60b 0x2dc6d96666200e30

def z484 : W := mkw 0x025d0000d464000c 0x0012e80006a32000 0x97df0000fc7e0018 0xfcbef80007e3f000

def z485 : W := mkw 0x225d04f4d46ccdcc 0xb112e827a6a3666e 0xf8df2cfcc47fc7ef 0xefc6f967e623fe3f

def z486 : W := mkw 0x021c000050600008 0x0010e00002830000 0x07180000f8000000 0x0838c00007c00000

def z487 : W := mkw 0x004004448400c540 0x900200222420062a 0xe8c02cccc401c7ef 0x2f46016666200e3f

def z488 : W := mkw 0x0ff6bfaaae81b611 0xc07fb5fd55740db0 0xbffb3fccff81fe1b 0x3dffd9fe67fc0ff0

def z489 : W := mkw 0x08490544eec5f755 0xd042482a27762fba 0x20000000ffc7fff8 0x0100000007fe3fff

def z490 : W := mkw 0x20490454dc6dedcd 0xb1024822a6e36f6e 0xf8db2cccfc7fffff 0xefc6d96667e3ffff

def z491 : W := mkw 0x00094055415e49e6 0x38004a02aa0af24f 0x501fc0ff007e01e4 0xc280fe07f803f00f

def z492 : W := mkw 0x07ffbeeec444c544 0x903ffdf77622262a 0xdfffffffc001c007 0xfefffffffe000e00

def z493 : W := mkw 0x04a28a0a00000000 0x0025145050000000 0x0020c30300000000 0x0001061818000000

def z494 : W := mkw 0x00414515859e9ee6 0xb8020a28ac2cf4f7 0xf8e7df3f07fe3fff 0xf7c73ef9f83ff1ff

def z495 : W := mkw 0x1fffffaafff7b61f 0xc0fffffd57ffbdb0 0xfffffffffffffe1f 0xfffffffffffffff0

def z496 : W := mkw 0x00490444c444c544 0x900248222622262a 0x58db0ccc044607e6 0xe2c6d8666022303f

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x87000000f8000018 0x1c38000007c00000

def z498 : W := mkw 0x2ffc3fe0fee1f719 0xc17fe1ff07f70fb8 0xaff83fc0ff81fe1b 0x3d7fc1fe07fc0ff0

def z499 : W := mkw 0x2ff43fb0bea9be99 0xe17fa1fd85f54df4 0xafe43f30ffb9fe1b 0x3d7f21f987fdcff0

def z500 : W := mkw 0x00494555c5dedfe6 0xb8024a2aae2ef6ff 0x20000000c7fffff8 0x01000000063fffff

def z501 : W := mkw 0x1fb6fb003bb3321b 0x40fdb7d801dd9990 0x0724d3003bb83810 0x1039269801ddc1c0

def z502 : W := mkw 0x0de93e44ee45e555 0xd06f49f227722f2a 0xffdb2cccfc47c7ef 0xeffed96667e23e3f

def z503 : W := mkw 0x0000001000080880 0x2000000080004044 0x2000103000003985 0x01000081800001cc

def z504 : W := mkw 0x000004440000c540 0x900000222000062a 0xf8db2ccc0001c7e7 0xefc6d96660000e3f

def z505 : W := mkw 0x1de97f00fff7b61f 0xc0ef4bf807ffbdb0 0xafe03f00fffffe1b 0x3d7f01f807fffff0

def z506 : W := mkw 0x221e80fa50684988 0x2110f407d283424c 0x501fc0ff00780184 0xc280fe07f803c00c

def z507 : W := mkw 0x1003c00001160006 0x00801e000008b000 0x1003c00000060000 0x80801e0000003000

def z508 : W := mkw 0x210034f40809edc1 0xb10801a7a0404f6e 0x68003cfc0001ffe7 0x034001e7e0000fff

def z509 : W := mkw 0x021400a000000000 0x0010a00500000000 0x001c00f000000004 0x4000e00780000000

def z510 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17ffc000fbb80010 0x18bffe0007ddc000

def z511 : W := mkw 0x0008005040484980 0x200040028202424c 0xa01c30f0c079f99d 0x5d00e1878603cfcc

def z512 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa024c00007fe3ff8 0xf5012600003ff1ff

def z513 : W := mkw 0x16f6c000b732001a 0x00b7b60005b99000 0x87e4c000ffb80018 0x3c3f260007fdc000

def z514 : W := mkw 0x2008005050684988 0x210040028283424c 0x0000000000780180 0x000000000003c00c

def z515 : W := mkw 0x0041040484048444 0x9002082024202422 0xf8c32c0cc407c66b 0xafc6196066203e33

def z516 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xc024d33303b83817 0xf6012699981dc1c0

def z517 : W := mkw 0x0000040000008400 0x8000002000000420 0x28002c000001c603 0x0140016000000e30

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004103000000005 0x5400208180000000

def z519 : W := mkw 0x235d34e4dc65e54d 0x911ae9a726e32f2a 0xffdb2cccfc47c7ef 0xeffed96667e23e3f

def z520 : W := mkw 0x0316baaa00000000 0x0018b5d550000000 0x581fffff00000007 0xc2c0fffff8000000

def z521 : W := mkw 0x0000010000801200 0x0000000800040090 0x2000130000003e03 0x01000098000001f0

def z522 : W := mkw 0x025d0444d464c54c 0x9012e82226a3262a 0xffdf2cccfc7fc7ff 0xfffef96667e3fe3f

def z523 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x28e03f000781fe03 0x214701f8003c0ff0

def z524 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0xa72013003f803e1b 0x3539009801fc01f0

def z525 : W := mkw 0x16ffc400f776841e 0x80b7fe2007bbb420 0xbfffec00ffffc61b 0xfdffff6007fffe30

def z526 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x4f24ffff00000007 0x127927fff8000000

def z527 : W := mkw 0x0ff6bf00ae81b611 0xc07fb5f805740db0 0xbfffff00ff81fe1b 0xfdfffff807fc0ff0

def z528 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0xe024d33300003fe7 0xf7012699980001ff

def z529 : W := mkw 0x29003ff00889ff81 0xe14801ff80444ffc 0x28003ff00001ff87 0x014001ff80000ffc

def z530 : W := mkw 0x00490040c4444104 0x0002480206222208 0xb0db20c0c447c18d 0xed86d90606223e0c

def z531 : W := mkw 0x0009004440444144 0x100048022202220a 0xf01b00cc044607ef 0xe780d8066022303f

def z532 : W := mkw 0x0000400001120002 0x0000020000089000 0x0020c00007860000 0xa0010600003c3000

def z533 : W := mkw 0x00004011011a08a2 0x280002008808d045 0x0004c03300380000 0x000026019801c000

def z534 : W := mkw 0x231c30e058616109 0x0118e18702c30b08 0xa71820c0f841c18d 0x4d38c10607c20e0c

def z535 : W := mkw 0x031430a000000000 0x0018a18500000000 0x071820c000000000 0x0838c10600000000

def z536 : W := mkw 0x0000400101120022 0x0800020008089001 0x4000c00300060060 0x8200060018003003

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x90db000000000000 0xec86d80000000000

def z538 : W := mkw 0x0216c1bb019a1aa2 0x2810b60dd80cd0d5 0xf03fd3ff07fe3fff 0xf781fe9ff83ff1ff

def z539 : W := mkw 0x000904444044c544 0x900048222202262a 0x781b2ccc0047c7e7 0xc3c0d96660023e3f

def z540 : W := mkw 0x00004011011a08a2 0x280002008808d045 0xc024d333007e01e7 0xf60126999803f00f

def z541 : W := mkw 0x2ffc3ee0fe61e519 0xc17fe1f707f30f28 0x0fd82cc0f801c000 0x087ec16607c00e00

def z542 : W := mkw 0x0000001000080880 0x2000000080004044 0xe0041030047e3fff 0xf70020818023f1ff

def z543 : W := mkw 0x17f7faaaa7160016 0x00bfbfd55538b000 0xdfffffff07860007 0xfefffffff83c3000

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x0024d33300000000 0x1001269998000000

def z545 : W := mkw 0x04e00100a6801210 0x0027000805340090 0xa7e01300ff803e1b 0x3d3f009807fc01f0

def z546 : W := mkw 0x04e38e0e84048444 0x90271c7074202422 0x58e3cf0f04060662 0xa2c71e7878203033

def z547 : W := mkw 0x10494000f776001e 0x00824a0007bbb000 0x90db0000fffe0018 0xec86d80007fff000

def z548 : W := mkw 0x0de93f44eec5f755 0xd06f49fa27762fba 0xbffb3fccff81fe1b 0x3dffd9fe67fc0ff0

def z549 : W := mkw 0x231c71f159fb7bab 0x2918e38f8acfdbdd 0xa71c30f0fffffffd 0x5d38e18787ffffff

def z550 : W := mkw 0x07f6beaa84008400 0x803fb5f554200420 0xffffffffc401c60f 0xfffffffffe200e30

def z551 : W := mkw 0x0000400001120002 0x0000020000089000 0xe024c00007fe07ff 0xf7012600003ff03f

def z552 : W := mkw 0x00004555019adfe2 0xb800022aa80cd6ff 0xe824ffff07ffffff 0xf74127fff83fffff

def z553 : W := mkw 0x125fc000f776001e 0x0092fe0007bbb000 0x101fc000fffe0018 0xc080fe0007fff000

def z554 : W := mkw 0x05a03a0008012001 0x002d01d000400900 0xafe03f00f801f81b 0x3d7f01f807c00fc0

def z555 : W := mkw 0x14e3c000a7160016 0x00a71e000538b000 0x97e3c000ff860018 0xbcbf1e0007fc3000

def z556 : W := mkw 0x17b6faaa3332001a 0x00bdb7d551999000 0xdfffffff3bb80017 0xfefffffff9ddc000

def z557 : W := mkw 0x021c000050600008 0x0010e00002830000 0x001c000000780000 0x4000e0000003c000

def z558 : W := mkw 0x04e90000e6440014 0x0027480007322000 0x97fb0000ffc60018 0xfcbfd80007fe3000

def z559 : W := mkw 0x235d30f0dc6d698d 0x211ae98786e36b4c 0xb7df30f0fc7ff99d 0xfdbef98787e3ffcc

def z560 : W := mkw 0x0008000050600008 0x0000400002830000 0x00000000f8780018 0x0000000007c3c000

def z561 : W := mkw 0x0009004440444144 0x100048022202220a 0x101b00cc00000000 0x0080d80660000000

def z562 : W := mkw 0x10494111f7fe1abe 0x28824a088fbff0d5 0x20000000fffe3ff8 0x0100000007fff1ff

def z563 : W := mkw 0x235d34f4dc6dedcd 0xb11ae9a7a6e36f6e 0xa71c30f0fc7ffffd 0x5d38e18787e3ffff

def z564 : W := mkw 0x00490444c444c544 0x900248222622262a 0xe0000000c447c7ef 0xe700000006223e3f

def z565 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000100000003819 0x15000080000001c0

def z566 : W := mkw 0x07ffbeeec444c544 0x903ffdf77622262a 0x1fdb2cccc001c000 0x08fed96666000e00

def z567 : W := mkw 0x021f80ee40444144 0x1010fc077202220a 0x501fc0ff004601e4 0xc280fe07f802300f

def z568 : W := mkw 0x221c00f050684988 0x2110e0078283424c 0x871c00f0f878019c 0x5c38e00787c3c00c

def z569 : W := mkw 0x0000410101921222 0x08000208080c9091 0x0000000007860660 0x00000000003c3033

def z570 : W := mkw 0x021680aa00000000 0x0010b40550000000 0x101b00cc00000000 0x0080d80660000000

def z571 : W := mkw 0x125fc000d576000e 0x0092fe0006abb000 0x90dfc000c47e0008 0xec86fe000623f000

def z572 : W := mkw 0x031430a000000000 0x0018a18500000000 0xc73cf3f300000007 0xfe39e79f98000000

def z573 : W := mkw 0x221400b010280888 0x2110a00580814044 0x0004003000380000 0x000020018001c000

def z574 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6004c03307fe3ffc 0xc3002601983ff1ff

def z575 : W := mkw 0x06b6800000000000 0x0035b40000000000 0x17db000000000000 0x08bed80000000000

def z576 : W := mkw 0x2000001018292889 0x2100000080c14944 0x0000000038383810 0x0000000001c1c1c0

def z577 : W := mkw 0x0fb6bbaa2a813211 0x407db5dd51540990 0xdfffffff3b803817 0xfefffffff9dc01c0

def z578 : W := mkw 0x0008004040404100 0x0000400202020208 0xf8db2cccc041c18f 0xefc6d96666020e0c

def z579 : W := mkw 0x00494555c5dedfe6 0xb8024a2aae2ef6ff 0xe024d333c7ffffff 0xf70126999e3fffff

def z580 : W := mkw 0x0040040084008400 0x8002002004200420 0xe8c02c00c447c7ef 0xef46016006223e3f

def z581 : W := mkw 0x37fff0b0ff7f289f 0x21bfff8587fbf944 0x97ffd030fffe3818 0xfcbffe8187fff1c0

def z582 : W := mkw 0x0fb6bbaa2a813211 0x407db5dd51540990 0x0724d3333b803810 0x1039269999dc01c0

def z583 : W := mkw 0x2008005058696989 0x2100400282c34b4c 0xa0041030f879f99d 0x5500208187c3cfcc

def z584 : W := mkw 0x100940005176000e 0x00804a00028bb000 0x00000000007e0000 0x000000000003f000

def z585 : W := mkw 0x331ff0f0597f698f 0x2198ff8782cbfb4c 0xb71ff0f0f87ff99d 0xddb8ff8787c3ffcc

def z586 : W := mkw 0x05e03000ae012011 0x002f018005700900 0xa7e03000ff81f819 0x3d3f018007fc0fc0

def z587 : W := mkw 0x00490444c444c544 0x900248222622262a 0x00000000c001c000 0x0000000006000e00

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x8024c00000000000 0xf401260000000000

def z589 : W := mkw 0x221c00f058696989 0x2110e00782c34b4c 0x201c00f0f879f99c 0x4100e00787c3cfcc

def z590 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x0000000003b83810 0x00000000001dc1c0

def z591 : W := mkw 0x07f6baaaa6000010 0x003fb5d555300000 0xdfffffffff80001f 0xfefffffffffc0000

def z592 : W := mkw 0x00494444c556c546 0x90024a22262ab62a 0xf8ffecccc7ffc7ff 0xffc7ff66663ffe3f

def z593 : W := mkw 0x021680aa00000000 0x0010b40550000000 0xd03fd3ff00000007 0xf681fe9ff8000000

def z594 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa024d33303f8399d 0x55012699981fc1cc

def z595 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0x2000000000003fe0 0x01000000000001ff

def z596 : W := mkw 0x2ffc7ff1fffbffbb 0xe97fe3ff8fffdffd 0xeffcfff3ffffffff 0xff7fe7ff9fffffff

def z597 : W := mkw 0x16ffc011f77e08be 0x28b7fe008fbbf045 0xd7ffc033fffe01fc 0xfebffe019ffff00f

def z598 : W := mkw 0x0040000084000000 0x0002000004200000 0x80c00000c4000008 0x2c06000006200000

def z599 : W := mkw 0x00490444c444c544 0x900248222622262a 0xb0db0000c447c7e8 0xed86d80006223e3f

def z600 : W := mkw 0x0040040084008400 0x8002002004200420 0x08c02c00c001c000 0x0846016006000e00

def z601 : W := mkw 0x06b6800000000000 0x0035b40000000000 0xd7ffd33300000007 0xfebffe9998000000

def z602 : W := mkw 0x00494111c5de1aa6 0x28024a088e2ef0d5 0xf0ffd333c7fe3fff 0xff87fe999e3ff1ff

def z603 : W := mkw 0x05e93e44c444c544 0x902f49f22622262a 0xfffb3fccc447c7ef 0xffffd9fe66223e3f

def z604 : W := mkw 0x1effc500fff7b61f 0xc0f7fe2807ffbdb0 0xb7ffc000fffffe18 0xfdbffe0007fffff0

def z605 : W := mkw 0x14e3c101a7961236 0x08a71e080d3cb091 0x50e3c30307860662 0xa2871e18183c3033

def z606 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa020130007fe3ffb 0x35010098003ff1ff

def z607 : W := mkw 0x0214000000000000 0x0010a00000000000 0x871c000000000000 0x5c38e00000000000

def z608 : W := mkw 0x0ffc3f00fee1b619 0xc07fe1f807f70db0 0xaffc3f00fff9fe1b 0x7d7fe1f807ffcff0

def z609 : W := mkw 0x04a2800000000000 0x0025140000000000 0x10e3c00000000000 0xa0871e0000000000

def z610 : W := mkw 0x08000f0000809600 0xc0400078000404b0 0x08000f0000000602 0x0040007800000030

def z611 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x97ffd33300000000 0xfcbffe9998000000

def z612 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fc03f00f801fe03 0x097e01f807c00ff0

def z613 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x10ffc00007fe0000 0xe087fe00003ff000

def z614 : W := mkw 0x0008004040404100 0x0000400202020208 0x001800c000400184 0x4000c0060002000c

def z615 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x8024d33307fe3818 0xf4012699983ff1c0

def z616 : W := mkw 0x235c34f0dc69ed89 0xa11ae1a786e34f6c 0xafdc3cf0fc79ff9f 0x7d7ee1e787e3cffc

def z617 : W := mkw 0x031430a000000000 0x0018a18500000000 0x0704103000000000 0x1038208180000000

def z618 : W := mkw 0x0316b0aa00000000 0x0018b58550000000 0xd71ff0ff00000005 0xdeb8ff87f8000000

def z619 : W := mkw 0x0ce10f04a6849654 0xd0670878253424b2 0x58e30f0c07860662 0xa2c71878603c3033

def z620 : W := mkw 0x07b43aa000000000 0x003da1d500000000 0x8ffc3ff000000007 0x7c7fe1ff80000000

def z621 : W := mkw 0x231c70f1597b69ab 0x2918e3878acbdb4d 0xe71cf0f3f87ff9fd 0xdf38e7879fc3ffcf

def z622 : W := mkw 0x27bebafa50684988 0x213df5d7d283424c 0xdfffffff00780187 0xfefffffff803c00c

def z623 : W := mkw 0x27bebafa58696989 0x213df5d7d2c34b4c 0xa73cf3f3f879f99d 0x5d39e79f9fc3cfcc

def z624 : W := mkw 0x20490454dc6dedcd 0xb1024822a6e36f6e 0x20000000fc7ffff8 0x0100000007e3ffff

def z625 : W := mkw 0x121fc0aa5176000e 0x0090fe05528bb000 0x501fc0ff007e0004 0xc280fe07f803f000

def z626 : W := mkw 0x2008415159fb7bab 0x2900420a8acfdbdd 0xe024d333ffffffff 0xf70126999fffffff

def z627 : W := mkw 0x221c00f050684988 0x2110e0078283424c 0xa01c20f0c079c18d 0x4d00e1078603ce0c

def z628 : W := mkw 0x0de93f00eec5b615 0xc06f49f807762db0 0xbffb3f00ffc7fe1b 0xfdffd9f807fe3ff0

def z629 : W := mkw 0x235d34e4dc65e54d 0x911ae9a726e32f2a 0x1fdb2cccf801c000 0x08fed96667c00e00

def z630 : W := mkw 0x0000010000801200 0x0000000800040090 0xe024d33307803e1f 0xf7012699983c01f0

def z631 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78c30c0cc447c7ea 0xa3c6186066223e3f

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004c03300000004 0xc200260198000000

def z633 : W := mkw 0x07b6bbaa00801200 0x003db5dd50040090 0xffffffff07803e1f 0xfffffffff83c01f0

def z634 : W := mkw 0x021c001050680888 0x2010e00082834044 0xa71c1030f878399d 0x5d38e08187c3c1cc

def z635 : W := mkw 0x2008005058696989 0x2100400282c34b4c 0xa01820c0f879f99d 0x4d00c10607c3cfcc

def z636 : W := mkw 0x231c30b058692889 0x2118e18582c34944 0x871c1030f8783818 0x5c38e08187c3c1c0

def z637 : W := mkw 0x14ebc444e756c556 0x90a75e22273ab62a 0xf8fbecccc7c7c7ef 0xefc7df66663e3e3f

def z638 : W := mkw 0x1effcf00f7f6961e 0xc0f7fe7807bfb4b0 0x9fffcf00fffe061a 0xfcfffe7807fff030

def z639 : W := mkw 0x06b6c00001120002 0x0035b60000089000 0x97ffc00007fe0018 0xfcbffe00003ff000

def z640 : W := mkw 0x0da07b112b9b3ab3 0x686d03d8895cd9d5 0x0724d3333bb83810 0x1039269999ddc1c0

def z641 : W := mkw 0x07b6beee0000c540 0x903db5f77000062a 0xffffffff0001c7e7 0xfffffffff8000e3f

def z642 : W := mkw 0x0000040400008440 0x9000002020000422 0x48000c0c00000662 0x0240006060000033

def z643 : W := mkw 0x27beb0f058696989 0x213df58782c34b4c 0xb7fff0f0f879f99d 0xfdbfff8787c3cfcc

def z644 : W := mkw 0x00000a0a00000000 0x0000005050000000 0x48000f0f00000002 0x0240007878000000

def z645 : W := mkw 0x2ffebffafee9ff99 0xe17ff5ffd7f74ffc 0xfffffffffff9ff9f 0xffffffffffffcffc

def z646 : W := mkw 0x14e38000a6040014 0x00a71c0005302000 0x10c3000000000000 0x0086180000000000

def z647 : W := mkw 0x00004011011a08a2 0x280002008808d045 0xe004c033047e07ef 0xe70026019823f03f

def z648 : W := mkw 0x0000400001120002 0x0000020000089000 0xc024d33307fe001f 0xf6012699983ff000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000004060662 0xa200000000203033

def z650 : W := mkw 0x0da03a002a012011 0x406d01d001500900 0x0700000038000000 0x0038000001c00000

def z651 : W := mkw 0x0009000040440004 0x0000480002022000 0x101b000000460000 0xc080d80000023000

def z652 : W := mkw 0x17bffaaa5176000e 0x00bdffd5528bb000 0xdfffffff007e0007 0xfefffffff803f000

def z653 : W := mkw 0x09007f11099bbea3 0xe84803f8884cddf5 0xe824ff3307ffffff 0xf74127f9983fffff

def z654 : W := mkw 0x0040040084008400 0x8002002004200420 0x20000000c401c608 0x0100000006200e30

def z655 : W := mkw 0x2008004058616109 0x0100400202c30b08 0x00000000f801c000 0x0000000007c00e00

def z656 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6000133307fe3fff 0x03000099983ff1ff

def z657 : W := mkw 0x10490000f664001c 0x0082480007b32000 0x00000000f8000000 0x0000000007c00000

def z658 : W := mkw 0x07b6fabb011a08a2 0x283db7d5d808d045 0xdfffffff007e01e7 0xfefffffff803f00f

def z659 : W := mkw 0x031471b1019a1aa2 0x2818a38d880cd0d5 0xe73cf3f307fe3fff 0xff39e79f983ff1ff

def z660 : W := mkw 0x000005550088dfe0 0xb800002aa80446ff 0x68003fff0001ffe7 0x034001fff8000fff

def z661 : W := mkw 0x0ff6beaaae01a411 0xc07fb5f555700d20 0xdffffffff801c007 0xfeffffffffc00e00

def z662 : W := mkw 0x0ff6bfaaae81b611 0xc07fb5fd55740db0 0xafe4ff33ff81fe1b 0x3d7f27f99ffc0ff0

def z663 : W := mkw 0x021680aa00000000 0x0010b40550000000 0x0004c03300000000 0x0000260198000000

def z664 : W := mkw 0x09003f440881f741 0xd04801fa20440fba 0x68003fcc0001ffe7 0x034001fe60000fff

def z665 : W := mkw 0x10494444f776c55e 0x90824a2227bbb62a 0xf8db2cccffffc7ff 0xefc6d96667fffe3f

def z666 : W := mkw 0x031c30a050600008 0x0018e18502830000 0x871c30f0f878001d 0x5c38e18787c3c000

def z667 : W := mkw 0x37fffafaff7f699f 0x21bfffd7d7fbfb4c 0xfffffffffffff99f 0xffffffffffffffcc

def z668 : W := mkw 0x00494455c55ecde6 0xb8024a22ae2af66f 0xf8dfecffc47fc7ef 0xefc6ff67fe23fe3f

def z669 : W := mkw 0x00490555c4ccdfe4 0xb802482aae2666ff 0xf8db3fffc447ffef 0xefc6d9fffe223fff

def z670 : W := mkw 0x0041040484048444 0x9002082024202422 0xf8c30c0c044607ef 0xe7c618606022303f

def z671 : W := mkw 0x16ffc100f7f6121e 0x00b7fe0807bfb090 0xb7ffd300fffe3e1b 0xfdbffe9807fff1f0

def z672 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x9ffb3fcc00000003 0x3cffd9fe60000000

def z673 : W := mkw 0x014034008c01a401 0x800a01a004600d20 0xafc03c00fc01fe1b 0x3d7e01e007e00ff0

def z674 : W := mkw 0x004104448404c544 0x900208222420262a 0x78c32ccc0407c7e7 0xa3c6196660203e3f

def z675 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x9fdf3cfc00000005 0x5cfef9e7e0000000

def z676 : W := mkw 0x16ff8000f664001c 0x00b7fc0007b32000 0x97db0000fc460008 0xecbed80007e23000

def z677 : W := mkw 0x16ffc010f77e089e 0x20b7fe0087bbf044 0xb7ffd030fffe399d 0xfdbffe8187fff1cc

def z678 : W := mkw 0x06b6800000000000 0x0035b40000000000 0x0724c00000000000 0x1039260000000000

def z679 : W := mkw 0x125fc444d576c54e 0x9092fe2226abb62a 0xf8dfecccc47fc7ef 0xefc6ff666623fe3f

def z680 : W := mkw 0x031430b000080880 0x2018a18580004044 0xa71c30f00078399d 0x5d38e1878003c1cc

def z681 : W := mkw 0x235d75f5ddffffef 0xb91aebafaeefffff 0xffffffffffffffff 0xffffffffffffffff

def z682 : W := mkw 0x00480440c440c500 0x8002402206220628 0xa8d82cc0c441c78f 0x6d46c16606220e3c

def z683 : W := mkw 0x0216800000000000 0x0010b40000000000 0x101fc00000000000 0xc080fe0000000000

def z684 : W := mkw 0x06b6c111019a1aa2 0x2835b608880cd0d5 0xf7ffd33307fe3fff 0xffbffe99983ff1ff

def z685 : W := mkw 0x00494000c5560006 0x00024a00062ab000 0x90ffc000c7fe0018 0xfc87fe00063ff000

def z686 : W := mkw 0x0041040484048444 0x9002082024202422 0x18c30c0c00000000 0x00c6186060000000

def z687 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe000000007fe3fff 0xe7000000003ff1ff

def z688 : W := mkw 0x09403f00ae81b611 0xc04a01f805740db0 0x28003f00ff81fe1b 0x014001f807fc0ff0

def z689 : W := mkw 0x231c30e058616109 0x0118e18702c30b08 0x871c20c0f879c018 0x5c38e10607c3ce00

def z690 : W := mkw 0x0de03f00a6809610 0xc06f01f8053404b0 0x8fe03f0007800603 0x3c7f01f8003c0030

def z691 : W := mkw 0x3ffffff0ffffff9f 0xe1ffffff87fffffc 0xbffffff0ffffff9f 0xfdffffff87fffffc

def z692 : W := mkw 0x0000010000801200 0x0000000800040090 0x2000000007803e18 0x01000000003c01f0

def z693 : W := mkw 0x0da03f000881b601 0xc06d01f800440db0 0xafe03f000001fe03 0x3d7f01f800000ff0

def z694 : W := mkw 0x2ffc3ef0fe69ed99 0xe17fe1f787f34f6c 0xafdc3cf0f879f99d 0x5d7ee1e787c3cfcc

def z695 : W := mkw 0x16b6c11133ba1aba 0x28b5b608899dd0d5 0x0724d3333bb83810 0x1039269999ddc1c0

def z696 : W := mkw 0x121fc0005176000e 0x0090fe00028bb000 0x971fc000f87e0018 0xdcb8fe0007c3f000

def z697 : W := mkw 0x0000000008012001 0x0000000000400900 0x20000000f801f818 0x0100000007c00fc0

def z698 : W := mkw 0x14ebc000f776001e 0x00a75e0007bbb000 0x10e3c000fffe0018 0xa0871e0007fff000

def z699 : W := mkw 0x0000011100881aa0 0x28000008880440d5 0xe004133300783fff 0x570020999803c1ff

def z700 : W := mkw 0x0041040484048444 0x9002082024202422 0x0000000004060660 0x0000000000203033

def z701 : W := mkw 0x0000400001120002 0x0000020000089000 0x0000000007fe0018 0x00000000003ff000

def z702 : W := mkw 0x0100300000000000 0x0008018000000000 0x8700300000000001 0x1c38018000000000

def z703 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x0fe01f003f803e12 0x307f00f801fc01f0

def z704 : W := mkw 0x2b1c3ff058e9ff89 0xe158e1ff82c74ffc 0xaf1c3ff0f879ff9f 0x5d78e1ff87c3cffc

def z705 : W := mkw 0x000004440000c540 0x900000222000062a 0x08002ccc0001c000 0x0040016660000e00

def z706 : W := mkw 0x01493eeec444c544 0x900a49f77622262a 0xf8db3fffc447c7ef 0xefc6d9fffe223e3f

def z707 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffc000fbb80010 0xfcbffe0007ddc000

def z708 : W := mkw 0x16ffc044f776415e 0x10b7fe0227bbb20a 0xf7ffc0ccfffe07ff 0xffbffe0667fff03f

def z709 : W := mkw 0x0de2bf0aae81b611 0xc06f15f855740db0 0xffe7ff3fff81fe1f 0xffff3ff9fffc0ff0

def z710 : W := mkw 0x16ffc404f776845e 0x90b7fe2027bbb422 0x97ffc000fffe0678 0xfcbffe0007fff033

def z711 : W := mkw 0x35e3f0f0af1f6997 0x21af1f878578fb4c 0x30e3f0f00787f985 0xa1871f87803c3fcc

def z712 : W := mkw 0x0100310008813201 0x0008018800440990 0xa7203300fb81f819 0x1d39019807dc0fc0

def z713 : W := mkw 0x07b6fbbb019a1aa2 0x283db7ddd80cd0d5 0x3fdb2ccc07fe3ff8 0x09fed966603ff1ff

def z714 : W := mkw 0x16fec000f772001a 0x00b7f60007bb9000 0x87fcc000fff80018 0x7c3fe60007ffc000

def z715 : W := mkw 0x06fd0000f664001c 0x0037e80007b32000 0x97ff0000fffe0018 0xfcbff80007fff000

def z716 : W := mkw 0x17b6baaa32200018 0x00bdb5d551910000 0xdfffffff38000007 0xfefffffff9c00000

def z717 : W := mkw 0x16f7c000b736001e 0x00b7be0005b9b000 0x0724c0003fbe0010 0x1039260001fdf000

def z718 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271830f0f879f99d 0x0938c18787c3cfcc

def z719 : W := mkw 0x16b6c4443332c55a 0x90b5b6222199962a 0x6f24eccc3bb9c7f7 0x1379276661ddce3f

def z720 : W := mkw 0x0ce00500ae81b611 0xc067002805740db0 0x27200000ff81fe18 0x1139000007fc0ff0

def z721 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe71c30f0f879ffff 0x5f38e18787c3cfff

def z722 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97df0000fffe0018 0x5cbef80007fff000

def z723 : W := mkw 0x16ff8111f6ec1abc 0x28b7fc088fb760d5 0x77db1333f8003fe7 0x0bbed8999fc001ff

def z724 : W := mkw 0x16ffc040f776411e 0x00b7fe0207bbb208 0xb7ffc000ffffc198 0xfdbffe0007fffe0c

def z725 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe03f00ffc7fe1b 0xfd7f01f807fe3ff0

def z726 : W := mkw 0x14e94000f776001e 0x00a74a0007bbb000 0x07200000fffe0018 0x1039000007fff000

def z727 : W := mkw 0x11497aaaf776001e 0x008a4bd557bbb000 0x48003ffffffe001f 0x024001fffffff000

def z728 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe4ff33ffc7ffff 0xff7f27f99ffe3fff

def z729 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe03f00ff81fe1f 0xff7f01f807fc0ff0

def z730 : W := mkw 0x04e04400a7128412 0x8027022005389420 0xefe4ec00ffffc7ff 0xff7f276007fffe3f

def z731 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffd300fffe001b 0xfcbffe9807fff000

def z732 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfffffff0078001f 0xfefffffff803c000

def z733 : W := mkw 0x231d30f4586d69cd 0x3118e987a2c36b4e 0xa71c30f0f87ff9fd 0x5d38e18787c3ffcf

def z734 : W := mkw 0x06fc0440f660c518 0x8037e02207b30628 0xaffc2cc0fff9c79f 0x7d7fe16607ffce3c

def z735 : W := mkw 0x16f7c404b736845e 0x90b7be2025b9b422 0x5fe7cc0c3fbe0672 0xb2ff3e6061fdf033

def z736 : W := mkw 0x29003f500889ff81 0xe14801fa80444ffc 0x28003f000001ff83 0x014001f800000ffc

def z737 : W := mkw 0x231430b018292889 0x2118a18580c14944 0xa7043030f879f99d 0x5d38218187c3cfcc

def z738 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271c10f0f879f99c 0x5138e08787c3cfcc

def z739 : W := mkw 0x125d4444f776c55e 0x9092ea2227bbb62a 0xa71c20c0ffffc7fd 0x5d38e10607fffe3f

def z740 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xdfffecccffffc01f 0xfeffff6667fffe00

def z741 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0xdfffeccc3bb80017 0xfeffff6661ddc000

def z742 : W := mkw 0x16bfc0447376415e 0x10b5fe02239bb20a 0x573fc0cc3bfe01f4 0xd2b9fe0661dff00f

def z743 : W := mkw 0x125d4000f776001e 0x0092ea0007bbb000 0x07040000fffe0018 0x1038200007fff000

def z744 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17fbc000fffe0018 0xa8bfde0007fff000

def z745 : W := mkw 0x0100310008813201 0x0008018800440990 0xa7003000ff81fe19 0x1d38018007fc0ff0

def z746 : W := mkw 0x0da93b446ac57355 0x506d49da23562b9a 0x573b13cc3bc639f4 0xd2b9d89e61de31cf

def z747 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c30f0fc7ff99d 0xfd38e18787e3ffcc

def z748 : W := mkw 0x16ffc040f776411e 0x00b7fe0207bbb208 0x97ffc0c0fffe019c 0xfcbffe0607fff00c

def z749 : W := mkw 0x0314300018212009 0x0018a18000c10900 0xa7043000f839f819 0x1d38218007c1cfc0

def z750 : W := mkw 0x16ffc040f776411e 0x00b7fe0207bbb208 0xf7ffe0c0ffffc7ff 0xffbfff0607fffe3f

def z751 : W := mkw 0x16b6ca0a3332001a 0x00b5b65051999000 0x5fe7cf0f3bb80012 0xb2ff3e7879ddc000

def z752 : W := mkw 0x231eb0f058696989 0x2118f58782c34b4c 0xb71ff0f0f879f99d 0xddb8ff8787c3cfcc

def z753 : W := mkw 0x10494555f7fedffe 0xb8824a2aafbff6ff 0x20000000fffffff8 0x0100000007ffffff

def z754 : W := mkw 0x235534b49c2daccd 0xb11aa9a5a4e16d66 0x5fc71c3c3c3e3e72 0xb2fe38e1e1e1f1f3

def z755 : W := mkw 0x0de2bf0aae81b611 0xc06f15f855740db0 0xfffbffcfff81fe1f 0xffffdffe7ffc0ff0

def z756 : W := mkw 0x04e00000a6000010 0x0027000005300000 0x87e40000fff80018 0x7c3f200007ffc000

def z757 : W := mkw 0x16bec0007372001a 0x00b5f600039b9000 0x0724c000fbf80018 0x1039260007dfc000

def z758 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2ccc0447c7e7 0xe3c6d96660223e3f

def z759 : W := mkw 0x231430f018296989 0x2118a18780c14b4c 0xa70430f0f839f99d 0x1d38218787c1cfcc

def z760 : W := mkw 0x231c30e058616109 0x0118e18702c30b08 0xa71c30c0f879f819 0x5d38e18607c3cfc0

def z761 : W := mkw 0x2108305058696989 0x2108418282c34b4c 0x27001000f879f998 0x1138008007c3cfcc

def z762 : W := mkw 0x09493f55cccdffe5 0xf84a49faae666fff 0xf8db3fffc447ffef 0xefc6d9fffe223fff

def z763 : W := mkw 0x231c71e159f3732b 0x0918e38f0acf9b99 0x4738e3c3ff87c662 0xaa39c71e1ffc3e33

def z764 : W := mkw 0x210031b108893aa1 0x2908018d884449d5 0x6000133300003fe7 0x03000099980001ff

def z765 : W := mkw 0x06b6800000000000 0x0035b40000000000 0xdfffffff00000007 0xfefffffff8000000

def z766 : W := mkw 0x09403f118c89bea1 0xe84a01f88c644df5 0xe8c03f33c447ffef 0xef4601f99e223fff

def z767 : W := mkw 0x0de07e11af1bacb3 0xe86f03f08d78dd65 0x4fc4ec33f87fc1e4 0xca7e27619fc3fe0f

def z768 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2cccc407c7e7 0xabc6d96666203e3f

def z769 : W := mkw 0x031430a000000000 0x0018a18500000000 0xdfffffff00000007 0xfefffffff8000000

def z770 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x17ffc0003bb80010 0x18bffe0001ddc000

def z771 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fe01f00ff81fe1a 0x317f00f807fc0ff0

def z772 : W := mkw 0x321fc0fa517e498e 0x2190fe07d28bf24c 0x501fc0ff007e0184 0xc280fe07f803f00c

def z773 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffc000fbf80018 0x5cbffe0007dfc000

def z774 : W := mkw 0x331fb0f0586d698d 0x2198fd8782c36b4c 0xb71f30f0f879f99d 0x5db8f98787c3cfcc

def z775 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x27000000ff81fe18 0x0138000007fc0ff0

def z776 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfffffff0446000f 0xfefffffff8223000

def z777 : W := mkw 0x16f6c000b732001a 0x00b7b60005b99000 0x0724c000ffb80018 0x1039260007fdc000

def z778 : W := mkw 0x210830f058696989 0x2108418782c34b4c 0xa70030f0f879f99d 0x1d38018787c3cfcc

def z779 : W := mkw 0x16bec0007372001a 0x00b5f600039b9000 0x873cc000fffe0018 0xfc39e60007fff000

def z780 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xbffb3f00ff81fe1b 0xfdffd9f807fc0ff0

def z781 : W := mkw 0x0108305048496981 0x2008418282424b4c 0xa71c30f0f879f99d 0x5d38e18787c3cfcc

def z782 : W := mkw 0x16ffc400f776841e 0x80b7fe2007bbb420 0xffffecccffffc61f 0xffffff6667fffe30

def z783 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x873cc0003bb80010 0x5c39e60001ddc000

def z784 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x9fffffff00000005 0x5cfffffff8000000

def z785 : W := mkw 0x05a03a0000000000 0x002d01d000000000 0xdfffffff00000007 0xfefffffff8000000

def z786 : W := mkw 0x125d4000f776001e 0x0092ea0007bbb000 0x07180000fffe0018 0x0838c00007fff000

def z787 : W := mkw 0x16f6c000b732001a 0x00b7b60005b99000 0x07e4c0003fb80010 0x303f260001fdc000

def z788 : W := mkw 0x121fc055517e49ee 0x3890fe02aa8bf24f 0x501fc0ff007e01e4 0xc280fe07f803f00f

def z789 : W := mkw 0x221c00f058696989 0x2110e00782c34b4c 0xa71c00f0f879f99c 0x5d38e00787c3cfcc

def z790 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe03fccff81fe1f 0x3f7f01fe67fc0ff0

def z791 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa73cf0f0f879f99d 0xfd39e78787c3cfcc

def z792 : W := mkw 0x0ce00500ae81b611 0xc067002805740db0 0xa7e01300ff81fe1b 0x3d3f009807fc0ff0

def z793 : W := mkw 0x221c005058696989 0x2110e00282c34b4c 0xa71c1030f879f99d 0x5d38e08187c3cfcc

def z794 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0x07203300fb81f810 0x1839019807dc0fc0

def z795 : W := mkw 0x025d4444d576c54e 0x9012ea2226abb62a 0xffffecccffffc7ff 0xffffff6667fffe3f

def z796 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x173fc0003bb80010 0xd0b9fe0001ddc000

def z797 : W := mkw 0x29003bf008897b81 0x614801df80444bdc 0x200033f00001f985 0x0100019f80000fcc

def z798 : W := mkw 0x16ffc404f776845e 0x90b7fe2027bbb422 0xffffec0cffffc67b 0xffffff6067fffe33

def z799 : W := mkw 0x321fc0f1517e49ae 0x2990fe078a8bf24d 0x501fc0f3007e01e4 0xc280fe079803f00f

def z800 : W := mkw 0x231d30f4586d69cd 0x3118e987a2c36b4e 0xffdf3cfcf87ff9ff 0xfffef9e7e7c3ffcf

def z801 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xb7ffc000fffe07f8 0xfdbffe0007fff03f

def z802 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fffffff00000004 0xdafffffff8000000

def z803 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2f203f00ff81fe1b 0x117901f807fc0ff0

def z804 : W := mkw 0x01003aaa00000000 0x000801d550000000 0xd8ffffff00000007 0xfec7fffff8000000

def z805 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xdfffccccfffe07fe 0xfefffe6667fff03f

def z806 : W := mkw 0x04a0400023120012 0x0025020001189000 0x0724c0003bb80010 0x1039260001ddc000

def z807 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x0724c0003bfe0010 0xd039260001dff000

def z808 : W := mkw 0x0ce04f00a7929612 0xc0670278053c94b0 0x08e0cf0007860602 0xa0470678003c3030

def z809 : W := mkw 0x231ebafa58696989 0x2118f5d7d2c34b4c 0xff1ffffff879f99f 0xdff8ffffffc3cfcc

def z810 : W := mkw 0x06b68aaa00000000 0x0035b45550000000 0xd8ffefff00000007 0xeec7ff7ff8000000

def z811 : W := mkw 0x2efc0ff0f6e8df98 0xe177e07f87b746fc 0x08fc0ff007f80786 0x6047e07f803fc03c

def z812 : W := mkw 0x125d4000f776001e 0x0092ea0007bbb000 0x873cc000fffe0018 0xfc39e60007fff000

def z813 : W := mkw 0x2008005058696989 0x2100400282c34b4c 0xa7000000f879f998 0x1d38000007c3cfcc

def z814 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffc000ffb80018 0x3cbffe0007fdc000

def z815 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x0fc02c00fb81f810 0x087e016007dc0fc0

def z816 : W := mkw 0x16ffc0a0f776001e 0x00b7fe0507bbb000 0x97ffc0f0fffe001c 0xfcbffe0787fff000

def z817 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271c30f0f839f995 0x1938e18787c1cfcc

def z818 : W := mkw 0x27b6fbbb19bb3aab 0x293db7ddd8cdd9d5 0x0724d3333bb83810 0x1039269999ddc1c0

def z819 : W := mkw 0x231430b018292889 0x2118a18580c14944 0x07043030f839f810 0x1838218187c1cfc0

def z820 : W := mkw 0x0de2bf0aae81b611 0xc06f15f855740db0 0xafe0ff03ff81fe1b 0x3d7f07f81ffc0ff0

def z821 : W := mkw 0x07b6baaa10200008 0x003db5d550810000 0xdfffffff38380017 0xfefffffff9c1c000

def z822 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0xe724c0003ffe07ff 0xf739260001fff03f

def z823 : W := mkw 0x16b6c0aa3332001a 0x00b5b60551999000 0x0724c0333bb80010 0x1039260199ddc000

def z824 : W := mkw 0x00490444c444c544 0x900248222622262a 0xffdb2cccfc47c7ff 0xfffed96667e23e3f

def z825 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8db3cccc447ffff 0xffc6d9e666223fff

def z826 : W := mkw 0x221c40f0517a498a 0x2110e207828bd24c 0x001cc0f0007e0184 0xc000e6078003f00c

def z827 : W := mkw 0x04e00500a6809610 0x80270028053404b0 0xafe03f00ff81fe1b 0x3d7f01f807fc0ff0

def z828 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x87e4c000fffe0018 0x3c3f260007fff000

def z829 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffc303fffe001a 0xfebffe181ffff000

def z830 : W := mkw 0x021c40405172410a 0x0010e202028b9208 0xe73ce0c0ffffc7ff 0xff39e70607fffe3f

def z831 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97db0000fffe0018 0xecbed80007fff000

def z832 : W := mkw 0x06fc4000f772001a 0x0037e20007bb9000 0x87fcc000fffe0018 0xfc3fe60007fff000

def z833 : W := mkw 0x16ffc0aaf776001e 0x00b7fe0557bbb000 0x97ffc033fffe0018 0xfcbffe019ffff000

def z834 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x0724d3333bb80010 0x1039269999ddc000

def z835 : W := mkw 0x24aa8a5a58696989 0x21255452d2c34b4c 0x78e3cf0ff879f99a 0xa3c71e787fc3cfcc

def z836 : W := mkw 0x014035008c81b601 0x800a01a804640db0 0xafe03f00ff81fe1b 0x3d7f01f807fc0ff0

def z837 : W := mkw 0x16ffc400f776841e 0x80b7fe2007bbb420 0x9fffec00ffffc018 0xfcffff6007fffe00

def z838 : W := mkw 0x16bfc0007376001e 0x00b5fe00039bb000 0x973fc000fbfe0018 0xdcb9fe0007dff000

def z839 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xbffb3fccff81fe1b 0x3dffd9fe67fc0ff0

def z840 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xf03fd3ff07fe3fff 0xf781fe9ff83ff1ff

def z841 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xb7ffe0c0ffffc7fd 0xfdbfff0607fffe3f

def z842 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6024d33307fe3ffa 0xb3012699983ff1ff

def z843 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17e7c000fffe0018 0xb0bf3e0007fff000

def z844 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17dfc000fffe0018 0xc8befe0007fff000

def z845 : W := mkw 0x16f7c000b736001e 0x00b7be0005b9b000 0x17e7c0003bb80010 0x10bf3e0001ddc000

def z846 : W := mkw 0x07ffbeeec444c544 0x903ffdf77622262a 0x2724d333c447c7e8 0x113926999e223e3f

def z847 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfffffff04060667 0xfefffffff8203033

def z848 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffd333fffe0018 0xfcbffe999ffff000

def z849 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xdfffcc0cfffe001a 0xfefffe6067fff000

def z850 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe024f333c7ffffff 0xff0127999e3fffff

def z851 : W := mkw 0x0de03faaae81b611 0xc06f01fd55740db0 0xfffb3fffff81fe1f 0xffffd9fffffc0ff0

def z852 : W := mkw 0x1ce2cf00a7929612 0xc0e71678053c94b0 0x08e0cf0007800602 0x20470678003c0030

def z853 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fe03f00ff81fe18 0x197f01f807fc0ff0

def z854 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe71c30f0f87ff9fd 0xdf38e18787c3ffcf

def z855 : W := mkw 0x231c3afa58696989 0x2118e1d7d2c34b4c 0xef3cfffff879f99f 0xff79e7ffffc3cfcc

def z856 : W := mkw 0x16bfc0007376001e 0x00b5fe00039bb000 0x97ffc0003bfe0010 0xfcbffe0001dff000

def z857 : W := mkw 0x10494000f776001e 0x00824a0007bbb000 0x87000000fffe0018 0x1c38000007fff000

def z858 : W := mkw 0x16b6c0aa3332001a 0x00b5b60551999000 0x573fc0ff3bb80014 0xd2b9fe07f9ddc000

def z859 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0x1fffecccfbb9c010 0x18ffff6667ddce00

def z860 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x0724c0003fbe0010 0xb039260001fdf000

def z861 : W := mkw 0x1ce3cf04a7969656 0xd0e71e78253cb4b2 0x58e3cf0c07860662 0xa2c71e78603c3033

def z862 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe03f00ffc1ff9f 0x7d7f01f807fe0ffc

def z863 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x8724c000fffe0018 0xf439260007fff000

def z864 : W := mkw 0x321fc0f4517e49ce 0x3190fe07a28bf24e 0x501fc0fc007e01e4 0xc280fe07e003f00f

def z865 : W := mkw 0x09003f000881b601 0xc04801f800440db0 0xaf203f00ff81fe1b 0x3d7901f807fc0ff0

def z866 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffc0ccfffe001c 0xfebffe0667fff000

def z867 : W := mkw 0x06b68aaa00000000 0x0035b45550000000 0xdfffcfff00000006 0xfefffe7ff8000000

def z868 : W := mkw 0x1effce00f776841e 0xc0f7fe7007bbb420 0x9fffcc00fffe0018 0xfcfffe6007fff000

def z869 : W := mkw 0x0ce00f00ae81b611 0xc067007805740db0 0xafe00f00ff81fe1a 0x3d7f007807fc0ff0

def z870 : W := mkw 0x04e04000a7120012 0x0027020005389000 0x87e00000fffe0018 0x3c3f000007fff000

def z871 : W := mkw 0x021c40005172000a 0x0010e200028b9000 0x873cc000fbf80018 0x5c39e60007dfc000

def z872 : W := mkw 0x06f6c000a7120012 0x0037b60005389000 0x97ffc000fffe0018 0xfcbffe0007fff000

def z873 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xf8e7df3f07fe3fff 0xf7c73ef9f83ff1ff

def z874 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa024d33307fe3ffd 0x55012699983ff1ff

def z875 : W := mkw 0x16f7c000b736001e 0x00b7be0005b9b000 0x97ffc0003fbe0010 0xfcbffe0001fdf000

def z876 : W := mkw 0x031c304058616109 0x0018e18202c30b08 0xa71c30c0f879f99d 0x5d38e18607c3cfcc

def z877 : W := mkw 0x0de03f0aae81b611 0xc06f01f855740db0 0xefe03f0fff81fe1b 0x3f7f01f87ffc0ff0

def z878 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe43f30ff81fe1f 0x7d7f21f987fc0ff0

def z879 : W := mkw 0x321d40f0517e498e 0x2190ea07828bf24c 0x001c00f0007e0184 0x4000e0078003f00c

def z880 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x9fffecccfffe0018 0xfcffff6667fff000

def z881 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xa7201300ff81fe1b 0x3539009807fc0ff0

def z882 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe0ff03ff81fe1b 0xbf7f07f81ffc0ff0

def z883 : W := mkw 0x16ffc004f776005e 0x10b7fe0027bbb002 0xd7ffc00cfffe0078 0xfebffe0067fff003

def z884 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c30f0fc7ffffd 0x5d38e18787e3ffff

def z885 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8df3cfcc447c7ef 0xffc6f9e7e6223e3f

def z886 : W := mkw 0x14e94000f776001e 0x00a74a0007bbb000 0x97fb0000fffe0018 0xfcbfd80007fff000

def z887 : W := mkw 0x16ffc00af776001e 0x00b7fe0057bbb000 0xd7ffc00ffffe0018 0xfebffe007ffff000

def z888 : W := mkw 0x16ffcaaaf776001e 0x00b7fe5557bbb000 0xdfffcffffffe001e 0xfefffe7ffffff000

def z889 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8fb2cccc7c7c7ff 0xffc7d966663e3e3f

def z890 : W := mkw 0x0de03f04ae81b651 0xd06f01f825740db2 0xefe03f0cff81fe7b 0x3f7f01f867fc0ff3

def z891 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c20c0f879f998 0x5d38e10607c3cfcc

def z892 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa7043030f879f999 0x1d38218187c3cfcc

def z893 : W := mkw 0x09403f00ae81b611 0xc04a01f805740db0 0xaf003f00ff81fe1b 0x1d7801f807fc0ff0

def z894 : W := mkw 0x0fb6baaa2a012011 0x407db5d551500900 0xdfffffff38000007 0xfefffffff9c00000

def z895 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xb7ffe000ffffc019 0xfdbfff0007fffe00

def z896 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffc000fffe001f 0xfebffe0007fff000

def z897 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2cccc447c7ef 0x0bc6d96666223e3f

def z898 : W := mkw 0x210831f148c97ba1 0x2908418f8a464bdd 0xe01833f3c447ffef 0xef00c19f9e223fff

def z899 : W := mkw 0x231c305058696989 0x2118e18282c34b4c 0xa71c3000f879f999 0x5d38e18007c3cfcc

def z900 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xffdb2cccffffc7ff 0xeffed96667fffe3f

def z901 : W := mkw 0x0100300008012001 0x0008018000400900 0xa7043000f879f819 0x5d38218007c3cfc0

def z902 : W := mkw 0x16ffc4eef776c55e 0x90b7fe2777bbb62a 0xffffecffffffc7ff 0xffffff67fffffe3f

def z903 : W := mkw 0x09403500ae81b611 0xc04a01a805740db0 0xafc03c00ff81fe1b 0x3d7e01e007fc0ff0

def z904 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x4024d33307fe3ff6 0xf2012699983ff1ff

def z905 : W := mkw 0x021c000058612009 0x0010e00002c30900 0xa71c0000f879f818 0x5d38e00007c3cfc0

def z906 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x070000003bb80010 0x0038000001ddc000

def z907 : W := mkw 0x125d4000f776001e 0x0092ea0007bbb000 0x97df0000fffe0018 0xfcbef80007fff000

def z908 : W := mkw 0x09403500ae81b611 0xc04a01a805740db0 0xa7203300ff81fe1b 0x3d39019807fc0ff0

def z909 : W := mkw 0x29003fb00889be81 0xe14801fd80444df4 0x28003f300001fe03 0x014001f980000ff0

def z910 : W := mkw 0x210031f108897ba1 0x2908018f88444bdd 0x200030f00001ffe5 0x0100018780000fff

def z911 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xb7ffd000fffe3819 0xfdbffe8007fff1c0

def z912 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8df2cccc47fc7ff 0xffc6f9666623fe3f

def z913 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x9fffec00fffe001b 0xfcffff6007fff000

def z914 : W := mkw 0x125fc000f776001e 0x0092fe0007bbb000 0x971fc000fffe0018 0xdcb8fe0007fff000

def z915 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x871c30f0f879f818 0x5c38e18787c3cfc0

def z916 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xffffffffffffc7ff 0xfffffffffffffe3f

def z917 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8db3fffc447c7ef 0xefc6d9fffe223e3f

def z918 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffd030fffe001d 0xfcbffe8187fff000

def z919 : W := mkw 0x221c005058696989 0x2110e00282c34b4c 0x27180000f879f998 0x0938c00007c3cfcc

def z920 : W := mkw 0x14e94444f776c55e 0x90a74a2227bbb62a 0xafe02c00ffffc7fb 0x3d7f016007fffe3f

def z921 : W := mkw 0x1b1fff0059f7b60f 0xc0d8fff802cfbdb0 0x381fff00007ffe03 0xc1c0fff80003fff0

def z922 : W := mkw 0x0de3bf0eae85b655 0xd06f1df875742db2 0xffe3ff0fff87fe7b 0xbfff1ff87ffc3ff3

def z923 : W := mkw 0x06b68aaa00000000 0x0035b45550000000 0xd8ffdfff00000007 0xf6c7fefff8000000

def z924 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0x27201300fb81f818 0x1139009807dc0fc0

def z925 : W := mkw 0x16ffc044f776415e 0x10b7fe0227bbb20a 0x97ffc000fffe01f8 0xfcbffe0007fff00f

def z926 : W := mkw 0x231430b018292889 0x2118a18580c14944 0x27041030f839f818 0x1138208187c1cfc0

def z927 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2cccc447c7ea 0xabc6d96666223e3f

def z928 : W := mkw 0x021c40005172000a 0x0010e200028b9000 0x871c0000fffe0018 0x5c38e00007fff000

def z929 : W := mkw 0x231c3af058696989 0x2118e1d782c34b4c 0xaf1c3ff0f879f99f 0x5d78e1ff87c3cfcc

def z930 : W := mkw 0x121fc0005176000e 0x0090fe00028bb000 0x973fc000fffe0018 0xfcb9fe0007fff000

def z931 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xf71f30fcf879f99d 0xdfb8f987e7c3cfcc

def z932 : W := mkw 0x16bec0007372001a 0x00b5f600039b9000 0x97ffc000fbf80018 0xfcbffe0007dfc000

def z933 : W := mkw 0x29003bb008893a81 0x614801dd804449d4 0x0000133000003800 0x00000099800001c0

def z934 : W := mkw 0x20494555ddffffef 0xb9024a2aaeefffff 0x20000000fffffff8 0x0100000007ffffff

def z935 : W := mkw 0x0de03faaae81b611 0xc06f01fd55740db0 0xafe03f33ff81fe1b 0x3d7f01f99ffc0ff0

def z936 : W := mkw 0x16b7c0003336001e 0x00b5be000199b000 0x1727c0003bbe0010 0x90b93e0001ddf000

def z937 : W := mkw 0x05a03b0008813201 0x002d01d800440990 0xafe03f00ff81fe1b 0x3d7f01f807fc0ff0

def z938 : W := mkw 0x0a5685aaae81b611 0xc052b42d55740db0 0x701fc0ffff81fe1c 0xc380fe07fffc0ff0

def z939 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x8fe03f00fb81f813 0x3c7f01f807dc0fc0

def z940 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fc03f00ff81fe1b 0x097e01f807fc0ff0

def z941 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xa7e01300ff81fe18 0x3d3f009807fc0ff0

def z942 : W := mkw 0x00494555c5dedfe6 0xb8024a2aae2ef6ff 0x18ffffffc3b9f810 0x18c7fffffe1dcfc0

def z943 : W := mkw 0x2108305058696989 0x2108418282c34b4c 0xa7043030f879f99d 0x5d38218187c3cfcc

def z944 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xaff83fc0ff81fe1f 0x7d7fc1fe07fc0ff0

def z945 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x0724c0003ffe0018 0x1039260001fff000

def z946 : W := mkw 0x06fd0444f664c55c 0x9037e82227b3262a 0xffff2cccffffc7ff 0xfffff96667fffe3f

def z947 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17ffc000fbfe0010 0xd8bffe0007dff000

def z948 : W := mkw 0x06bec0005172000a 0x0035f600028b9000 0x97ffc000fffe0018 0xfcbffe0007fff000

def z949 : W := mkw 0x231430b018292889 0x2118a18580c14944 0xa71c30f0f839f81d 0x5d38e18787c1cfc0

def z950 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xffffffff0040018f 0xfffffffff802000c

def z951 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xffffffffff81fe1f 0xfffffffffffc0ff0

def z952 : W := mkw 0x16f6c000b732001a 0x00b7b60005b99000 0x97ffc000ffb80018 0xfcbffe0007fdc000

def z953 : W := mkw 0x05a030002a012011 0x002d018001500900 0xa7203000fb81f819 0x1d39018007dc0fc0

def z954 : W := mkw 0x00490444c444c544 0x900248222622262a 0xe024d333c447c7ef 0xf70126999e223e3f

def z955 : W := mkw 0x021c005050684988 0x2010e0028283424c 0xa71c30f0f879f99d 0x5d38e18787c3cfcc

def z956 : W := mkw 0x16ffc0aaf776001e 0x00b7fe0557bbb000 0xd7ffd3fffffe001f 0xfebffe9ffffff000

def z957 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe824ffff07fe3fff 0xf74127fff83ff1ff

def z958 : W := mkw 0x231c3afa58696989 0x2118e1d7d2c34b4c 0xa71c33f3f879f99d 0x5d38e19f9fc3cfcc

def z959 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0x2724c000ffffc7f8 0x1139260007fffe3f

def z960 : W := mkw 0x16f6c400b732841a 0x80b7b62005b99420 0xafe4ec00ffb9c61b 0x3d7f276007fdce30

def z961 : W := mkw 0x16ffca00f776001e 0x00b7fe5007bbb000 0x9fffcf00fffe001a 0xfcfffe7807fff000

def z962 : W := mkw 0x16ffc404f776845e 0x90b7fe2027bbb422 0x9fffcc0cfffe0018 0xfcfffe6067fff000

def z963 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8fb3fccc447c7ef 0xffc7d9fe66223e3f

def z964 : W := mkw 0x0de13f04ae85b655 0xd06f09f825742db2 0xffe33f0cffc7ffff 0xffff19f867fe3fff

def z965 : W := mkw 0x16f6c000b732001a 0x00b7b60005b99000 0x87e4c000fffe0018 0xfc3f260007fff000

def z966 : W := mkw 0x16ff8000f664001c 0x00b7fc0007b32000 0x97ff0000fff80018 0x7cbff80007ffc000

def z967 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5ffbffff00000007 0xaaffdffff8000000

def z968 : W := mkw 0x04e04000a7120012 0x0027020005389000 0x87e4c000ffb80018 0x3c3f260007fdc000

def z969 : W := mkw 0x221c40f1517a49aa 0x2910e2078a8bd24d 0x001cc0f300780184 0x4000e6079803c00c

def z970 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xffdf3cfcfc7fffff 0xfffef9e7e7e3ffff

def z971 : W := mkw 0x16bec0407372411a 0x00b5f602039b9208 0xa73ce0c0fbf9c19d 0x5d39e70607dfce0c

def z972 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xb7df30f0f879f99d 0xfdbef98787c3cfcc

def z973 : W := mkw 0x07b6baaa08012001 0x003db5d550400900 0xdfffffff38003817 0xfefffffff9c001c0

def z974 : W := mkw 0x125d4444f776c55e 0x9092ea2227bbb62a 0xffdf2cccffffc7ff 0xfffef96667fffe3f

def z975 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xdffffffffffe001f 0xfefffffffffff000

def z976 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafc03c00ff81fe19 0x1d7e01e007fc0ff0

def z977 : W := mkw 0x0008004040404100 0x0000400202020208 0xf8db2cccc447c7ef 0xefc6d96666223e3f

def z978 : W := mkw 0x2100301018292889 0x2108018080c14944 0xa7003000f839f819 0x1d38018007c1cfc0

def z979 : W := mkw 0x07b6baaa08012001 0x003db5d550400900 0xffffffff0001f807 0xfffffffff8000fc0

def z980 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xa7203300ff81fe19 0x1d39019807fc0ff0

def z981 : W := mkw 0x121c40007372001a 0x0090e200039b9000 0x871c0000fbf80018 0x5c38e00007dfc000

def z982 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xffffffffc001c00f 0xfffffffffe000e00

def z983 : W := mkw 0x0316baaa00000000 0x0018b5d550000000 0xd8dfffff00000007 0xeec6fffff8000000

def z984 : W := mkw 0x0100311108893aa1 0x28080188884449d5 0x600033330001ffe7 0x0300019998000fff

def z985 : W := mkw 0x0fb6fbbb2b9b3ab3 0x687db7ddd95cd9d5 0x0724d3333bb83810 0x1039269999ddc1c0

def z986 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x270430f0f879f99d 0x1138218787c3cfcc

def z987 : W := mkw 0x01403000ae012011 0x000a018005700900 0xa7003000ff81f819 0x1d38018007fc0fc0

def z988 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6024d33307fe3fe7 0xe3012699983ff1ff

def z989 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe71c33f3f879f99f 0x5f38e19f9fc3cfcc

def z990 : W := mkw 0x0000400001120002 0x0000020000089000 0x8724c000fffe0018 0xfc39260007fff000

def z991 : W := mkw 0x0100301008092881 0x2008018080404944 0xa7043030f839f819 0x1d38218187c1cfc0

def z992 : W := mkw 0x16ffc0eef776415e 0x10b7fe0777bbb20a 0xd7ffc0fffffe01fc 0xfebffe07fffff00f

def z993 : W := mkw 0x0de03500ae81b611 0xc06f01a805740db0 0xa7e03000ff81fe19 0x3d3f018007fc0ff0

def z994 : W := mkw 0x16ffc040f776411e 0x00b7fe0207bbb208 0x97ffe0c0ffffc018 0xfcbfff0607fffe00

def z995 : W := mkw 0x16ffca0af776001e 0x00b7fe5057bbb000 0x97ffc303fffe0018 0xfcbffe181ffff000

def z996 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xf8db2ccc07fe3fff 0xefc6d966603ff1ff

def z997 : W := mkw 0x021440001132000a 0x0010a20000899000 0x0724c0003bb80010 0x1039260001ddc000

def z998 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xbfdf3cfcf879f99d 0x5dfef9e7e7c3cfcc

def z999 : W := mkw 0x16ffc404f776845e 0x90b7fe2027bbb422 0xdfffecccfffe067f 0xfeffff6667fff033

def z1000 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17ffc000ffbe0010 0xb8bffe0007fdf000

def z1001 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2cccc447c7ec 0xcbc6d96666223e3f

def z1002 : W := mkw 0x031430b008092881 0x2018a18580404944 0xa71c30f0f879f99d 0x5d38e18787c3cfcc

def z1003 : W := mkw 0x0ce2cf0ba7929632 0xc86716785d3c94b1 0x58e3cf0f07860662 0xa2c71e78783c3033

def z1004 : W := mkw 0x09403500ae81b611 0xc04a01a805740db0 0x27001000ff81fe18 0x1138008007fc0ff0

def z1005 : W := mkw 0x1ce3c500a7969616 0xc0e71e28053cb4b0 0x10e3c00007860600 0xa0871e00003c3030

def z1006 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17ffc000fffe0000 0xe8bffe0007fff000

def z1007 : W := mkw 0x16ffca0af776001e 0x00b7fe5057bbb000 0x9fffcc0cfffe0018 0xfcfffe6067fff000

def z1008 : W := mkw 0x210031b108893aa1 0x2908018d884449d5 0x0000133300003800 0x00000099980001c0

def z1009 : W := mkw 0x16ffc040f776411e 0x00b7fe0207bbb208 0xffffecccffffc19f 0xffffff6667fffe0c

def z1010 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x17e7c0003bb80010 0xb0bf3e0001ddc000

def z1011 : W := mkw 0x04e94000e7560016 0x00274a00073ab000 0x97ffc000fffe0018 0xfcbffe0007fff000

def z1012 : W := mkw 0x16bfc0007376001e 0x00b5fe00039bb000 0x973fc0003ffe0018 0xf4b9fe0001fff000

def z1013 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xbfffecccffffc61b 0xfdffff6667fffe30

def z1014 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe73cf3f3fc7fffff 0xff39e79f9fe3ffff

def z1015 : W := mkw 0x06bc000072600018 0x0035e00003930000 0x873c0000fbf80018 0x5c39e00007dfc000

def z1016 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x8724c0003bb80010 0xf439260001ddc000

def z1017 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6024d33307fe3ffc 0xd3012699983ff1ff

def z1018 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xffffffff000007e7 0xfffffffff800003f

def z1019 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271c20f0f879f99c 0x4938e10787c3cfcc

def z1020 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffc033fffe001c 0xfebffe019ffff000

def z1021 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fe02f00ff81fe1a 0x297f017807fc0ff0

def z1022 : W := mkw 0x231c3afa58696989 0x2118e1d7d2c34b4c 0xffdf3ffff879f99f 0xfffef9ffffc3cfcc

def z1023 : W := mkw 0x0de13f04ae85b655 0xd06f09f825742db2 0xfffb3fccff87fe7f 0xffffd9fe67fc3ff3

def z1024 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x07201300fb81f810 0x1039009807dc0fc0

def z1025 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xf0ffd33307fe3fff 0xff87fe99983ff1ff

def z1026 : W := mkw 0x0de2bf0aae81b611 0xc06f15f855740db0 0xbfe33f0cff81fe1b 0x3dff19f867fc0ff0

def z1027 : W := mkw 0x14a040003332001a 0x00a5020001999000 0x072000003bb80010 0x1039000001ddc000

def z1028 : W := mkw 0x16ffc044f776415e 0x10b7fe0227bbb20a 0xf7ffe0ccffffc1fd 0xffbfff0667fffe0f

def z1029 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe4ff33ff81fe1b 0x3d7f27f99ffc0ff0

def z1030 : W := mkw 0x29003ff40889ffc1 0xf14801ffa0444ffe 0x68003ffc0001ffe7 0x034001ffe0000fff

def z1031 : W := mkw 0x221c005058696989 0x2110e00282c34b4c 0xa71c20c0f879f99d 0x5d38e10607c3cfcc

def z1032 : W := mkw 0x0de2bf00ae81b611 0xc06f15f805740db0 0xbfe3ff00ff81fe1b 0xbdff1ff807fc0ff0

def z1033 : W := mkw 0x321fc050517e498e 0x2190fe02828bf24c 0x101fc000007e0180 0xc080fe000003f00c

def z1034 : W := mkw 0x231c30f4586969c9 0x3118e187a2c34b4e 0xe71c30fcf879f9fd 0x5f38e187e7c3cfcf

def z1035 : W := mkw 0x14e3c505a7969676 0x98a71e282d3cb4b3 0x58e3cf0f07860662 0xa2c71e78783c3033

def z1036 : W := mkw 0x231eb0fa58696989 0x2118f587d2c34b4c 0xb71f30fcf879f99d 0x5db8f987e7c3cfcc

def z1037 : W := mkw 0x090031002a813211 0x4048018801540990 0xa7003000fb81f819 0x1d38018007dc0fc0

def z1038 : W := mkw 0x025c0000f6600018 0x0012e00007b30000 0x871c0000fff80018 0x5c38e00007ffc000

def z1039 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fffefff00000006 0xeaffff7ff8000000

def z1040 : W := mkw 0x2108305058696989 0x2108418282c34b4c 0x27002000f879f998 0x0938010007c3cfcc

def z1041 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xdfffecccffffc67a 0xfeffff6667fffe33

def z1042 : W := mkw 0x16ffce0ef776845e 0x90b7fe7077bbb422 0xdfffcf0ffffe067a 0xfefffe787ffff033

def z1043 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fe03f00ff81fe03 0x297f01f807fc0ff0

def z1044 : W := mkw 0x121440003332001a 0x0090a20001999000 0x070400003bb80010 0x1038200001ddc000

def z1045 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe02c00ff81fe18 0x3d7f016007fc0ff0

def z1046 : W := mkw 0x09003f100889be81 0xe04801f880444df4 0x28003f300001ff87 0x014001f980000ffc

def z1047 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe03f00ffc7fffb 0x3d7f01f807fe3fff

def z1048 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0x97ffc000ffffc018 0xfcbffe0007fffe00

def z1049 : W := mkw 0x16bec0007372001a 0x00b5f600039b9000 0x073cc000fbb80010 0x1839e60007ddc000

def z1050 : W := mkw 0x04a0400023120012 0x0025020001189000 0x8724c0003ffe0018 0xf439260001fff000

def z1051 : W := mkw 0x1ce3cf0aa7969616 0xc0e71e78553cb4b0 0x58e3cf0f07860602 0xa2c71e78783c3030

def z1052 : W := mkw 0x16ffc400f776841e 0x80b7fe2007bbb420 0xffffec00ffffc7ff 0xffffff6007fffe3f

def z1053 : W := mkw 0x0de03faaae81b611 0xc06f01fd55740db0 0xafe03fccff81fe1b 0x3d7f01fe67fc0ff0

def z1054 : W := mkw 0x231eb0fa58696989 0x2118f587d2c34b4c 0xa71cf0f3f879f99d 0x5d38e7879fc3cfcc

def z1055 : W := mkw 0x231d30f0586d698d 0x2118e98782c36b4c 0xb71f30f0f87ff99d 0xddb8f98787c3ffcc

def z1056 : W := mkw 0x04e80000f6600018 0x0027400007b30000 0x87e00000fff80018 0x3c3f000007ffc000

def z1057 : W := mkw 0x06fe8000f6600018 0x0037f40007b30000 0x97ffc000fff80018 0xfcbffe0007ffc000

def z1058 : W := mkw 0x031c301058692889 0x2018e18082c34944 0xa71c3030f879f99d 0x5d38e18187c3cfcc

def z1059 : W := mkw 0x214935f5cccdffe5 0xb90a49afae666fff 0xf8db3fffc447ffef 0xefc6d9fffe223fff

def z1060 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0x6024d33307fe3fff 0x13012699983ff1ff

def z1061 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xf7ffd333fffe07ff 0xffbffe999ffff03f

def z1062 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x8fe03f00ff81f818 0x3c7f01f807fc0fc0

def z1063 : W := mkw 0x231c30b058692889 0x2118e18582c34944 0xa71c3030f879f819 0x5d38e18187c3cfc0

def z1064 : W := mkw 0x16f7c000b736001e 0x00b7be0005b9b000 0x97e7c000ffbe0018 0xbcbf3e0007fdf000

def z1065 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe03f00ff87fe7b 0xbf7f01f807fc3ff3

def z1066 : W := mkw 0x0ce00500ae81b611 0xc067002805740db0 0xafe02c00ff81fe1b 0x3d7f016007fc0ff0

def z1067 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97ffe0c0fffe001d 0xfcbfff0607fff000

def z1068 : W := mkw 0x321ec0f0517a498a 0x2190f607828bd24c 0x001cc0f000780184 0x4000e6078003c00c

def z1069 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x9fffffff00000000 0xfcfffffff8000000

def z1070 : W := mkw 0x05e03400ae01a411 0x802f01a005700d20 0xafe03c00ff81fe1b 0x3d7f01e007fc0ff0

def z1071 : W := mkw 0x0de03b00ae813211 0x406f01d805740990 0xa7e03300ff81f819 0x3d3f019807fc0fc0

def z1072 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271c30f0f879f998 0x1938e18787c3cfcc

def z1073 : W := mkw 0x14e94000f776001e 0x00a74a0007bbb000 0x07c00000fffe0018 0x083e000007fff000

def z1074 : W := mkw 0x0100301008092881 0x2008018080404944 0xa7003000f879f999 0x1d38018007c3cfcc

def z1075 : W := mkw 0x1ce3cf01a7969636 0xc8e71e780d3cb4b1 0x58e3cf0307860662 0xa2c71e78183c3033

def z1076 : W := mkw 0x16ffc044f776415e 0x10b7fe0227bbb20a 0x97ffc0ccfffe0018 0xfcbffe0667fff000

def z1077 : W := mkw 0x210031f008897b81 0x2108018f80444bdc 0x200033f00001ff87 0x0100019f80000ffc

def z1078 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x173fc000fffe0018 0xd0b9fe0007fff000

def z1079 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xfffffffff879f99f 0xffffffffffc3cfcc

def z1080 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xffffecccfffe07ff 0xffffff6667fff03f

def z1081 : W := mkw 0x05e03100ae813211 0x002f018805740990 0xa7e03300ff81fe1b 0x3d3f019807fc0ff0

def z1082 : W := mkw 0x1de3bf00ae85b615 0xc0ef1df805742db0 0xbfe33f00ff81fe1b 0x3dff19f807fc0ff0

def z1083 : W := mkw 0x0de13f04ae85b655 0xd06f09f825742db2 0xafe03f00ff87fe7b 0x3d7f01f807fc3ff3

def z1084 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c30f0f839f819 0x1d38e18787c1cfc0

def z1085 : W := mkw 0x14ebc000f776001e 0x00a75e0007bbb000 0x97e3c000fffe0018 0xbcbf1e0007fff000

def z1086 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x871c30f0f839f815 0x5c38e18787c1cfc0

def z1087 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe71cf0f3f879f99d 0xdf38e7879fc3cfcc

def z1088 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x58ffffff00000007 0xe2c7fffff8000000

def z1089 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x97ffc0003ffe0018 0xfcbffe0001fff000

def z1090 : W := mkw 0x16ffc400f776841e 0x80b7fe2007bbb420 0xb7ffc000ffffc618 0xfdbffe0007fffe30

def z1091 : W := mkw 0x14e94444f776c55e 0x90a74a2227bbb62a 0xfffb2cccffffc7ff 0xffffd96667fffe3f

def z1092 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe4ff00ff81fe1b 0xfd7f27f807fc0ff0

def z1093 : W := mkw 0x221c40f1517a49aa 0x2910e2078a8bd24d 0x001c00f0007e01e4 0x4000e0078003f00f

def z1094 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xbfffecccffffc19d 0xfdffff6667fffe0c

def z1095 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17ffc0003ffe0010 0xf0bffe0001fff000

def z1096 : W := mkw 0x031c30a058612009 0x0018e18502c30900 0xa71c30f0f879f81d 0x5d38e18787c3cfc0

def z1097 : W := mkw 0x0de2bfaaae81b611 0xc06f15fd55740db0 0xffe3ffffff81fe1f 0xbfff1ffffffc0ff0

def z1098 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17db0000fbb80010 0x08bed80007ddc000

def z1099 : W := mkw 0x16ffc400f776841e 0x80b7fe2007bbb420 0x9fffcc00fffe061a 0xfcfffe6007fff030

def z1100 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfffffff0780001f 0xfefffffff83c0000

def z1101 : W := mkw 0x06b4000032200018 0x0035a00001910000 0x072400003bb80010 0x1039200001ddc000

def z1102 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdffffffff800001f 0xfeffffffffc00000

def z1103 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafc02c00ff81fe1b 0x2d7e016007fc0ff0

def z1104 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe724d333fffe3fff 0xff3926999ffff1ff

def z1105 : W := mkw 0x36ffc0e0f776411e 0x01b7fe0707bbb208 0x97ffc0c0fffe0018 0xfcbffe0607fff000

def z1106 : W := mkw 0x16ffc0aaf776001e 0x00b7fe0557bbb000 0xdfffecfffffe001f 0xfeffff67fffff000

def z1107 : W := mkw 0x16b6ca0a3332001a 0x00b5b65051999000 0x0724c3033bb80010 0x1039261819ddc000

def z1108 : W := mkw 0x08494555efdffff7 0xf8424a2aaf7effff 0x20000000fffffff8 0x0100000007ffffff

def z1109 : W := mkw 0x231eb0fa58696989 0x2118f587d2c34b4c 0xffdffcfff879f99f 0xfffeffe7ffc3cfcc

def z1110 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x8724c000fbb80018 0x1c39260007ddc000

def z1111 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fffffff00000007 0x1afffffff8000000

def z1112 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe03f00fb81f819 0x1d7f01f807dc0fc0

def z1113 : W := mkw 0x0ce04f01a7929632 0xc86702780d3c94b1 0x08e0cf0307800602 0x20470678183c0030

def z1114 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x0724c000fbb80010 0x1039260007ddc000

def z1115 : W := mkw 0x00490444c444c544 0x900248222622262a 0x78db2cccc047c7e7 0xcbc6d96666023e3f

def z1116 : W := mkw 0x09003b1108893aa1 0x684801d8884449d5 0x6000133300003fe7 0x03000099980001ff

def z1117 : W := mkw 0x00490444c444c544 0x900248222622262a 0xb8db2cccc447c7eb 0x2dc6d96666223e3f

def z1118 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xfffb3fccffc7ffff 0xffffd9fe67fe3fff

def z1119 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xdfffecccffffc1fc 0xfeffff6667fffe0f

def z1120 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa7041030f879f99d 0x5538208187c3cfcc

def z1121 : W := mkw 0x09003b1108893aa1 0x684801d8884449d5 0x0000133300003800 0x00000099980001c0

def z1122 : W := mkw 0x210031f108897ba1 0x2908018f88444bdd 0x200033f30001f985 0x0100019f98000fcc

def z1123 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fffdfff00000006 0xf2fffefff8000000

def z1124 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x87e4c0003bb80010 0x3c3f260001ddc000

def z1125 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa024d33307fe3ffb 0x35012699983ff1ff

def z1126 : W := mkw 0x210030f008096981 0x2108018780404b4c 0xa70430f0f879f99d 0x5d38218787c3cfcc

def z1127 : W := mkw 0x0da03f002a81b611 0xc06d01f801540db0 0xaf203f00fb81fe1b 0x1d7901f807dc0ff0

def z1128 : W := mkw 0x221c005058696989 0x2110e00282c34b4c 0x27040000f879f998 0x1138200007c3cfcc

def z1129 : W := mkw 0x05e03a00ae012011 0x002f01d005700900 0xafe03f00ff81f81b 0x3d7f01f807fc0fc0

def z1130 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xb7ffc000fffe061b 0xfdbffe0007fff030

def z1131 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x2fe03f00fb81fe13 0x197f01f807dc0ff0

def z1132 : W := mkw 0x1ce14f00a7969616 0xc0e70a78053cb4b0 0x08e00f0007860602 0x20470078003c3030

def z1133 : W := mkw 0x16ffc404f776845e 0x90b7fe2027bbb422 0xffffcc0cfffe07ff 0xfffffe6067fff03f

def z1134 : W := mkw 0x290035f00889ff81 0xe14801af80444ffc 0x200030f00001ff85 0x0100018780000ffc

def z1135 : W := mkw 0x16bec0007372001a 0x00b5f600039b9000 0x073cc0003bf80010 0x5039e60001dfc000

def z1136 : W := mkw 0x231eb0fa58696989 0x2118f587d2c34b4c 0xf73ff3fff879f99f 0xffb9ff9fffc3cfcc

def z1137 : W := mkw 0x0040040084008400 0x8002002004200420 0xf8db2cccc447c7ef 0xefc6d96666223e3f

def z1138 : W := mkw 0x0ce04f01a7929632 0xc86702780d3c94b1 0x08e00f0007860662 0x20470078003c3033

def z1139 : W := mkw 0x231c3afa58696989 0x2118e1d7d2c34b4c 0xaf1c3cfcf879f99d 0x5d78e1e7e7c3cfcc

def z1140 : W := mkw 0x0de03faaae81b611 0xc06f01fd55740db0 0xefe4ffffff81fe1f 0xff7f27fffffc0ff0

def z1141 : W := mkw 0x14e04000b732001a 0x00a7020005b99000 0x87e00000ffb80018 0x3c3f000007fdc000

def z1142 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xe71c30f0f879f99f 0xff38e18787c3cfcc

def z1143 : W := mkw 0x025d4000d576000e 0x0012ea0006abb000 0x97ffc000fffe0018 0xfcbffe0007fff000

def z1144 : W := mkw 0x021c000050600008 0x0010e00002830000 0x873c0000fff80018 0x7c39e00007ffc000

def z1145 : W := mkw 0x16f7c000b736001e 0x00b7be0005b9b000 0x97e7c0003ffe0018 0xf4bf3e0001fff000

def z1146 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71830c0f879f999 0x1d38c18607c3cfcc

def z1147 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fdfffff00000007 0xcafefffff8000000

def z1148 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xffffffff0400060f 0xfffffffff8200030

def z1149 : W := mkw 0x09003f110889bea1 0xe84801f888444df5 0x28003f000001ffe3 0x014001f800000fff

def z1150 : W := mkw 0x0de03e00ae01a411 0xc06f01f005700d20 0xafe03c00ff81f819 0x3d7f01e007fc0fc0

def z1151 : W := mkw 0x16ffce4ef776c55e 0x90b7fe7277bbb62a 0xffffefcfffffc7ff 0xffffff7e7ffffe3f

def z1152 : W := mkw 0x004104448404c544 0x900208222420262a 0xf8db2ccc0407c7e7 0xefc6d96660203e3f

def z1153 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa73cf3f3f879f99d 0x5d39e79f9fc3cfcc

def z1154 : W := mkw 0x00490444c444c544 0x900248222622262a 0x58db2cccc447c7e6 0xeac6d96666223e3f

def z1155 : W := mkw 0x0108300058612009 0x0008418002c30900 0xa7003000f879f819 0x1d38018007c3cfc0

def z1156 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffc000fffe067a 0xfebffe0007fff033

def z1157 : W := mkw 0x221ec0fb517a49aa 0x2910f607da8bd24d 0x501fc0ff007e01e4 0xc280fe07f803f00f

def z1158 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xef1c3cfcf879f99f 0x5f78e1e7e7c3cfcc

def z1159 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c30f0fc79ff9f 0x7d38e18787e3cffc

def z1160 : W := mkw 0x16ffc044f776415e 0x10b7fe0227bbb20a 0xdfffecccfffe01ff 0xfeffff6667fff00f

def z1161 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xdfffffff004601e7 0xfefffffff802300f

def z1162 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x97fb0000fffe0018 0x3cbfd80007fff000

def z1163 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8dfecffc447c7ef 0xefc6ff67fe223e3f

def z1164 : W := mkw 0x210035f50889ffe1 0xb90801afa8444fff 0x68003fff0001ffe7 0x034001fff8000fff

def z1165 : W := mkw 0x00490444c444c544 0x900248222622262a 0xb8db2cccc447c7ed 0x4dc6d96666223e3f

def z1166 : W := mkw 0x231d30f4586d69cd 0x3118e987a2c36b4e 0xf71f30fcfc7fffff 0xffb8f987e7e3ffff

def z1167 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x071820c0f839f810 0x0838c10607c1cfc0

def z1168 : W := mkw 0x00490444d464c54c 0x9002482226a3262a 0xf8db2cccfc7fc7ff 0xefc6d96667e3fe3f

def z1169 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x17ffc000fffe0018 0x18bffe0007fff000

def z1170 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe03f00ff81ffff 0x3f7f01f807fc0fff

def z1171 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0x3fdb2cccffffc7f8 0x09fed96667fffe3f

def z1172 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xafe43f00fff9fe1b 0x7d7f21f807ffcff0

def z1173 : W := mkw 0x231fb0fe586d69cd 0x3118fd87f2c36b4e 0xf71ff0fff87ff9fd 0xdfb8ff87ffc3ffcf

def z1174 : W := mkw 0x05a2baaa00000000 0x002d15d550000000 0xd8fbffff00000007 0xeec7dffff8000000

def z1175 : W := mkw 0x0ce14f05a7969676 0xd8670a782d3cb4b3 0x58e3cf0f07860662 0xa2c71e78783c3033

def z1176 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa73c30f0fff9f99d 0x7d39e18787ffcfcc

def z1177 : W := mkw 0x021440001132000a 0x0010a20000899000 0x8724c0003ffe0018 0xf439260001fff000

def z1178 : W := mkw 0x29003ffa0889ff81 0xe14801ffd0444ffc 0x68003fff0001ff87 0x034001fff8000ffc

def z1179 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xffffcc0cffffc7fa 0xfffffe6067fffe3f

def z1180 : W := mkw 0x04e94444e756c556 0x90274a22273ab62a 0xffffecccffffc7ff 0xffffff6667fffe3f

def z1181 : W := mkw 0x16f6c000b732001a 0x00b7b60005b99000 0x07e4c000fbb80010 0x183f260007ddc000

def z1182 : W := mkw 0x2108305058696989 0x2108418282c34b4c 0xa71830c0f879f99d 0x5d38c18607c3cfcc

def z1183 : W := mkw 0x16fd4000f776001e 0x00b7ea0007bbb000 0x87fc0000fffe0018 0x7c3fe00007fff000

def z1184 : W := mkw 0x09003f110889bea1 0xe84801f888444df5 0x28003f330001fe03 0x014001f998000ff0

def z1185 : W := mkw 0x10490444f664c55c 0x9082482227b3262a 0xf8db2cccfc47c7ef 0xefc6d96667e23e3f

def z1186 : W := mkw 0x231c30fa58696989 0x2118e187d2c34b4c 0xe71c30fff879f99d 0x5f38e187ffc3cfcc

def z1187 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x07041030f839f810 0x1038208187c1cfc0

def z1188 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x873cc000fffe0018 0x5c39e60007fff000

def z1189 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x27000000f879f998 0x0138000007c3cfcc

def z1190 : W := mkw 0x00490444c444c544 0x900248222622262a 0xb8db2cccc447c7e8 0xedc6d96666223e3f

def z1191 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xf7ffc0ccffffc7fc 0xffbffe0667fffe3f

def z1192 : W := mkw 0x27b6baaa18212009 0x013db5d550c10900 0xdfffffff38000007 0xfefffffff9c00000

def z1193 : W := mkw 0x231d30f4586d69cd 0x3118e987a2c36b4e 0xb71f30fcf879f99d 0x5db8f987e7c3cfcc

def z1194 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xafdc3cf0f879f99f 0x7d7ee1e787c3cfcc

def z1195 : W := mkw 0x29483ff0ccc9ff81 0xe14a41ff86664ffc 0xa8d83ff0c441ff8f 0x6d46c1ff86220ffc

def z1196 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x071c30f0f879f994 0x5838e18787c3cfcc

def z1197 : W := mkw 0x0de03f01ae81b631 0xc86f01f80d740db1 0xefe03f03ff81fe7b 0x3f7f01f81ffc0ff3

def z1198 : W := mkw 0x09403500ae81b611 0xc04a01a805740db0 0x27002000ff81fe18 0x0938010007fc0ff0

def z1199 : W := mkw 0x021680aa00000000 0x0010b40550000000 0xd8ffffff00000007 0xfec7fffff8000000

def z1200 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xffe33f0cff81fe1b 0xbfff19f867fc0ff0

def z1201 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0x271c30f0f879f985 0x4938e18787c3cfcc

def z1202 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0xffffffff0000381f 0xfffffffff80001c0

def z1203 : W := mkw 0x14e3c000a7160016 0x00a71e000538b000 0x97e7c000fffe0018 0xfcbf3e0007fff000

def z1204 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x8724c0003bf80018 0x5439260001dfc000

def z1205 : W := mkw 0x29493ff4cccdffc5 0xf14a49ffa6666ffe 0xf8db3ffcc447ffef 0xefc6d9ffe6223fff

def z1206 : W := mkw 0x08400500ae81b611 0xc042002805740db0 0xa7000000ff81fe18 0x1d38000007fc0ff0

def z1207 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0x0fe03f00ff81fe12 0x387f01f807fc0ff0

def z1208 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xbfffecccffffc7f8 0xfdffff6667fffe3f

def z1209 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8ffecccc447c7ef 0xffc7ff6666223e3f

def z1210 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71c1030f879f998 0x5d38e08187c3cfcc

def z1211 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x9fffffff00000003 0x3cfffffff8000000

def z1212 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xb7ffc000fffe019d 0xfdbffe0007fff00c

def z1213 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0x07000000fffe0018 0x0038000007fff000

def z1214 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0xa7203300ff81fe1b 0x3d39019807fc0ff0

def z1215 : W := mkw 0x21003bfb08897ba1 0x290801dfd8444bdd 0x68003fff0001ffe7 0x034001fff8000fff

def z1216 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe03cf3f307fe3fff 0xff01e79f983ff1ff

def z1217 : W := mkw 0x000004440000c540 0x900000222000062a 0xf8db2ccc0447c7ef 0xefc6d96660223e3f

def z1218 : W := mkw 0x29003ff10889ffa1 0xe94801ff88444ffd 0x68003ff30001ffe7 0x034001ff98000fff

def z1219 : W := mkw 0x16ffc001f776003e 0x08b7fe000fbbb001 0xd7ffc003fffe0078 0xfebffe001ffff003

def z1220 : W := mkw 0x16ffca0af776001e 0x00b7fe5057bbb000 0xdfffdf3ffffe001f 0xfefffef9fffff000

def z1221 : W := mkw 0x0de13f04ae85b655 0xd06f09f825742db2 0xbfe33f0cff81fe1b 0x3dff19f867fc0ff0

def z1222 : W := mkw 0x0de03f00ae81b611 0xc06f01f805740db0 0xefe03f33ff81fe1f 0x3f7f01f99ffc0ff0

def z1223 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xa024d33307fe3ff8 0xf5012699983ff1ff

def z1224 : W := mkw 0x04a28a0a00000000 0x0025145050000000 0xd8ffffff00000007 0xfec7fffff8000000

def z1225 : W := mkw 0x09003fbb0889bea1 0xe84801fdd8444df5 0x68003fff0001ffe7 0x034001fff8000fff

def z1226 : W := mkw 0x231c30f1586969a9 0x2918e1878ac34b4d 0xe71c30f3f879f9fd 0x5f38e1879fc3cfcf

def z1227 : W := mkw 0x0100300008012001 0x0008018000400900 0xa7203000ff81f819 0x3d39018007fc0fc0

def z1228 : W := mkw 0x07b6baaa22000010 0x003db5d551100000 0xdfffffff3b800017 0xfefffffff9dc0000

def z1229 : W := mkw 0x16ffc440f776c51e 0x80b7fe2207bbb628 0xbfffecc0ffffc79f 0xfdffff6607fffe3c

def z1230 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xf7ffc000ffffc7ff 0xffbffe0007fffe3f

def z1231 : W := mkw 0x0da03b002a813211 0x406d01d801540990 0xafe03f00fb81f81b 0x3d7f01f807dc0fc0

def z1232 : W := mkw 0x06f40000b6200018 0x0037a00005b10000 0x87e40000ffb80018 0x3c3f200007fdc000

def z1233 : W := mkw 0x16ffca0af776001e 0x00b7fe5057bbb000 0xdfffefcffffe001f 0xfeffff7e7ffff000

def z1234 : W := mkw 0x00490444e644c554 0x900248222732262a 0xf8db2cccffc7c7ff 0xefc6d96667fe3e3f

def z1235 : W := mkw 0x000904444044c544 0x900048222202262a 0xf8db2ccc0047c7e7 0xefc6d96660023e3f

def z1236 : W := mkw 0x07b6baaa00000000 0x003db5d550000000 0x5fffffff00000002 0xbafffffff8000000

def z1237 : W := mkw 0x09003f550889ffe1 0xf84801faa8444fff 0x68003fff0001ffe7 0x034001fff8000fff

def z1238 : W := mkw 0x14e94000f776001e 0x00a74a0007bbb000 0x87e4c000fffe0018 0xfc3f260007fff000

def z1239 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa73c33f0f879f99f 0x7d39e19f87c3cfcc

def z1240 : W := mkw 0x00490444c444c544 0x900248222622262a 0xf8fbefcfc447c7ef 0xefc7df7e7e223e3f

def z1241 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0xc724d3333bb80017 0xf639269999ddc000

def z1242 : W := mkw 0x231c30f058696989 0x2118e18782c34b4c 0xa71820c0f879f99d 0x4d38c10607c3cfcc

def z1243 : W := mkw 0x16bfc0007376001e 0x00b5fe00039bb000 0x173fc0003bb80010 0x10b9fe0001ddc000

def z1244 : W := mkw 0x16ffc444f776c55e 0x90b7fe2227bbb62a 0xbfffec00ffffc7fb 0xfdffff6007fffe3f

def z1245 : W := mkw 0x07b6baaa08012001 0x003db5d550400900 0xdffffffff801c007 0xfeffffffffc00e00

def z1246 : W := mkw 0x00004111019a1aa2 0x28000208880cd0d5 0xe8e4ff3307fe3fff 0xff4727f9983ff1ff

def z1247 : W := mkw 0x0de03fa0ae81b611 0xc06f01fd05740db0 0xafe03ff0ff81fe1f 0x3d7f01ff87fc0ff0

def z1248 : W := mkw 0x221d40f5517e49ee 0x3910ea07aa8bf24f 0x501fc0ff007e01e4 0xc280fe07f803f00f

def z1249 : W := mkw 0x16ffc0aaf776001e 0x00b7fe0557bbb000 0x97ffc0ccfffe0018 0xfcbffe0667fff000

def z1250 : W := mkw 0x0ce00500ae81b611 0xc067002805740db0 0x27c00000ff81fe18 0x093e000007fc0ff0

def z1251 : W := mkw 0x0de13f00ae85b615 0xc06f09f805742db0 0xbfe33f00ff87fe1b 0xbdff19f807fc3ff0

def z1252 : W := mkw 0x04e00000ae012011 0x0027000005700900 0xa7e00000ff81f818 0x3d3f000007fc0fc0

def z1253 : W := mkw 0x16bfc0007376001e 0x00b5fe00039bb000 0x0724c0003bfe0010 0x1039260001dff000

def z1254 : W := mkw 0x16ffc000f776001e 0x00b7fe0007bbb000 0xd7ffc000fffe01fc 0xfebffe0007fff00f

def z1255 : W := mkw 0x16b6c0003332001a 0x00b5b60001999000 0x8724c0003fb80018 0x3439260001fdc000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z8,z5,z6]),(0,[z7,z2,z3,z4,z9,z10,z6]),(0,[z7,z2,z3,z4,z10,z11,z6]),(0,[z12,z7,z2,z3,z4,z9,z6]),(1,[z7,z2,z3,z4,z13,z6])],[(0,[z14,z7,z2,z15,z4,z5,z6]),(0,[z7,z2,z16,z3,z4,z5,z6]),(0,[z7,z2,z3,z17,z4,z9,z6]),(0,[z7,z2,z3,z18,z19,z5,z6]),(1,[z7,z2,z3,z4,z5,z20]),(0,[z7,z2,z3,z4,z5,z6,z21])],[(0,[z22,z7,z2,z3,z4,z9,z6]),(0,[z7,z23,z2,z3,z4,z5,z6]),(1,[z7,z2,z24,z3,z4,z6]),(0,[z7,z2,z3,z25,z4,z5,z6])],[],[(0,[z26,z7,z2,z3,z27,z5,z6]),(0,[z7,z2,z3,z28,z4,z29,z6]),(0,[z30,z7,z2,z3,z4,z5,z6]),(0,[z31,z7,z2,z3,z4,z5,z6]),(0,[z32,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z33,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z34,z6]),(0,[z12,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z35,z9,z6])],[(0,[z7,z2,z3,z4,z36,z5,z6]),(1,[z7,z2,z3,z4,z5,z37])],[(0,[z0,z7,z38,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z39,z10,z6]),(0,[z22,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z18,z9,z6]),(1,[z7,z2,z40,z3,z4,z41])]],
   [[(0,[z42,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z43,z17,z5,z6]),(0,[z7,z2,z3,z4,z44,z5,z6]),(1,[z7,z2,z3,z4,z45,z6]),(1,[z7,z2,z3,z4,z46,z6]),(0,[z7,z2,z47,z3,z4,z5,z48]),(0,[z7,z2,z3,z4,z5,z49,z6]),(0,[z50,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z51,z3,z4,z5,z6]),(0,[z7,z2,z3,z52,z4,z5,z6]),(0,[z7,z2,z3,z4,z53,z5,z6]),(0,[z7,z54,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z55,z6,z56]),(0,[z7,z2,z3,z57,z4,z5,z6]),(0,[z7,z3,z17,z4,z58,z5,z6]),(0,[z7,z2,z3,z4,z9,z59,z6]),(0,[z7,z2,z3,z4,z5,z6,z60])],[(0,[z61,z7,z2,z3,z4,z5,z6]),(1,[z7,z62,z3,z4,z5,z6]),(0,[z7,z2,z3,z43,z29,z5,z6])],[(0,[z7,z2,z3,z5,z63,z6,z56]),(0,[z7,z2,z3,z4,z9,z6,z64]),(0,[z7,z2,z3,z4,z5,z65,z6]),(0,[z7,z2,z3,z4,z18,z5,z6]),(0,[z7,z66,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z67,z11,z6]),(0,[z7,z2,z3,z4,z5,z6,z68])],[(0,[z7,z69,z2,z3,z4,z70,z6]),(0,[z0,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z71,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z10,z6]),(0,[z72,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z73,z6]),(0,[z7,z2,z3,z4,z5,z56,z74]),(0,[z7,z3,z4,z5,z75,z6,z76]),(0,[z7,z2,z3,z4,z5,z6,z77]),(0,[z7,z2,z78,z3,z79,z5,z6]),(0,[z7,z2,z3,z4,z5,z80,z6]),(0,[z7,z2,z81,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z82]),(0,[z72,z2,z3,z4,z29,z5,z6]),(0,[z7,z2,z3,z4,z83,z5,z6])],[(0,[z7,z2,z3,z84,z4,z5,z6]),(0,[z7,z2,z3,z4,z85,z5,z6]),(0,[z7,z2,z86,z3,z4,z10,z6]),(0,[z7,z2,z47,z3,z4,z10,z6]),(0,[z7,z2,z87,z3,z4,z5,z6]),(0,[z7,z88,z2,z3,z4,z5,z6])]],
   [[(0,[z89,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z90,z3,z4,z5,z6]),(0,[z7,z2,z3,z91,z4,z5,z6]),(0,[z7,z2,z3,z92,z4,z10,z6])],[(1,[z7,z2,z3,z93,z5,z6]),(0,[z7,z94,z2,z3,z4,z5,z6]),(0,[z7,z2,z40,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z95,z6]),(0,[z7,z2,z3,z4,z96,z5,z6])],[(0,[z72,z7,z2,z3,z4,z5,z6]),(0,[z97,z7,z2,z3,z4,z10,z6]),(0,[z7,z98,z2,z3,z4,z5,z6])],[(0,[z99,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z100,z5,z6]),(0,[z101,z7,z2,z3,z4,z5,z6])],[(0,[z102,z7,z2,z3,z5,z59,z6]),(0,[z7,z2,z3,z4,z103,z5,z6]),(0,[z7,z2,z3,z4,z9,z104,z6]),(0,[z105,z7,z2,z3,z4,z5,z6]),(0,[z7,z106,z2,z3,z4,z10,z6]),(0,[z7,z2,z107,z3,z4,z5,z6]),(0,[z7,z2,z108,z3,z43,z5,z6])],[(0,[z7,z2,z3,z4,z9,z109,z6]),(0,[z7,z110,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z111,z5,z6])],[(1,[z1,z2,z112,z4,z5,z6]),(0,[z72,z7,z2,z113,z3,z5,z6]),(0,[z7,z2,z3,z114,z4,z5,z6]),(0,[z7,z2,z115,z3,z4,z5,z6]),(0,[z7,z2,z116,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z117,z6]),(0,[z7,z2,z24,z3,z4,z5,z6])]],
   [[(0,[z7,z118,z2,z3,z4,z9,z6]),(0,[z7,z119,z2,z3,z4,z5,z6]),(0,[z7,z2,z120,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z121])],[(0,[z122,z7,z2,z3,z4,z5,z6]),(0,[z7,z69,z2,z3,z4,z123,z6]),(1,[z102,z2,z3,z124,z5,z6]),(0,[z7,z2,z125,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z126,z6]),(0,[z7,z2,z3,z4,z5,z104,z74]),(0,[z14,z7,z2,z3,z4,z127,z6]),(0,[z7,z2,z3,z4,z5,z6,z76])],[(0,[z128,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z15,z129,z4,z5,z6]),(0,[z7,z2,z130,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z6]),(0,[z7,z2,z131,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z132,z6]),(0,[z7,z2,z113,z3,z5,z6,z68])],[(0,[z7,z2,z133,z3,z4,z5,z6]),(0,[z7,z118,z2,z3,z4,z134,z6]),(0,[z7,z2,z3,z135,z4,z5,z6]),(0,[z7,z2,z3,z136,z4,z5,z137]),(0,[z7,z2,z138,z3,z4,z11,z6])],[(0,[z7,z2,z139,z3,z4,z5,z6]),(0,[z7,z2,z140,z3,z4,z5,z6]),(0,[z97,z7,z2,z40,z3,z4,z6]),(0,[z7,z2,z3,z17,z18,z5,z6]),(0,[z7,z2,z3,z141,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z142])],[(0,[z26,z2,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z145]),(0,[z12,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z146,z6])],[(0,[z69,z2,z143,z3,z4,z5,z6]),(0,[z147,z7,z2,z143,z4,z5,z6]),(0,[z148,z69,z2,z3,z4,z5,z6]),(0,[z97,z42,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z17,z4,z10,z6]),(0,[z7,z3,z4,z9,z5,z10,z6])],[(0,[z7,z2,z3,z149,z4,z5,z6]),(0,[z22,z7,z2,z3,z4,z10,z6]),(0,[z7,z150,z2,z3,z4,z5,z6]),(0,[z7,z2,z78,z3,z151,z5,z6])]],
   [[(1,[z7,z2,z3,z152,z4,z5]),(0,[z7,z2,z153,z3,z4,z5,z6]),(0,[z7,z2,z47,z3,z4,z154,z6])],[(0,[z0,z7,z2,z3,z4,z155,z6]),(0,[z7,z2,z3,z4,z156,z5,z6]),(0,[z7,z2,z157,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z158,z6]),(0,[z7,z2,z159,z3,z4,z5,z6])],[(0,[z7,z2,z160,z3,z4,z5,z6]),(0,[z7,z2,z113,z3,z136,z5,z6]),(0,[z7,z2,z3,z4,z5,z161,z6])],[(0,[z7,z2,z3,z4,z18,z10,z6]),(0,[z7,z2,z3,z4,z5,z6,z162])],[(0,[z7,z2,z3,z4,z5,z6,z163]),(0,[z7,z2,z3,z164,z4,z5,z6]),(0,[z165,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z166,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z167]),(0,[z7,z2,z3,z4,z5,z168,z6]),(1,[z7,z2,z3,z92,z19,z6]),(1,[z7,z2,z113,z3,z5,z68]),(1,[z7,z2,z3,z4,z169,z11])],[(0,[z0,z7,z2,z3,z170,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z171]),(1,[z7,z2,z3,z4,z5,z172]),(0,[z7,z2,z3,z4,z83,z10,z6])],[(0,[z7,z2,z3,z4,z170,z5,z6]),(0,[z7,z2,z173,z3,z4,z5,z6]),(0,[z7,z2,z3,z174,z4,z5,z6]),(0,[z7,z2,z3,z124,z4,z9,z6]),(0,[z7,z2,z175,z3,z4,z5,z6])]],
   [[(0,[z7,z69,z3,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z176,z5,z6]),(0,[z7,z2,z3,z4,z5,z10,z6]),(0,[z7,z2,z3,z4,z5,z6,z177]),(1,[z7,z2,z3,z5,z6,z178])],[(0,[z7,z2,z3,z43,z4,z9,z6]),(1,[z7,z2,z138,z3,z109,z6])],[(0,[z72,z7,z2,z3,z4,z10,z6]),(0,[z7,z179,z2,z3,z4,z5,z6]),(0,[z7,z98,z2,z3,z4,z10,z6]),(1,[z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z180,z6])],[(0,[z0,z7,z2,z3,z4,z5,z181]),(0,[z14,z182,z2,z3,z4,z5,z6]),(0,[z99,z7,z2,z3,z4,z10,z6]),(1,[z7,z2,z3,z4,z65,z6]),(0,[z7,z2,z183,z3,z4,z5,z6]),(0,[z184,z7,z2,z3,z4,z5,z6])],[(1,[z148,z69,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z185,z6]),(0,[z7,z2,z3,z4,z5,z6,z186]),(0,[z7,z2,z3,z4,z169,z11,z6])],[(0,[z187,z7,z2,z3,z4,z5,z6]),(0,[z7,z188,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z189,z6]),(0,[z102,z2,z3,z124,z4,z5,z6]),(0,[z7,z2,z3,z190,z4,z5,z6]),(0,[z7,z2,z3,z191,z4,z5,z6]),(0,[z7,z2,z40,z3,z4,z5,z137])],[(0,[z7,z2,z192,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z6,z74]),(0,[z7,z2,z3,z4,z193,z5,z6]),(0,[z7,z106,z2,z3,z4,z5,z75]),(0,[z7,z2,z3,z43,z4,z5,z6]),(0,[z7,z2,z3,z194,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z195,z6])],[(1,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z196,z6]),(0,[z7,z2,z3,z4,z197,z5,z6]),(0,[z7,z2,z3,z4,z5,z56,z76]),(1,[z7,z2,z3,z5,z63,z6]),(0,[z7,z98,z2,z3,z17,z5,z6]),(0,[z7,z2,z3,z4,z58,z5,z6]),(0,[z7,z2,z3,z19,z5,z59,z6])]],
   [[(0,[z7,z2,z3,z4,z27,z5,z6]),(0,[z198,z7,z2,z3,z4,z5,z6]),(0,[z7,z199,z2,z3,z4,z5,z6]),(0,[z200,z7,z2,z3,z4,z5,z6]),(0,[z201,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z202,z6])],[(0,[z203,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z113,z3,z4,z169,z5]),(0,[z7,z2,z3,z136,z4,z169,z5])],[(0,[z7,z2,z3,z204,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z145]),(0,[z7,z2,z3,z4,z5,z6,z205]),(0,[z7,z2,z3,z206,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z59,z6])],[(0,[z7,z2,z3,z207,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z208]),(0,[z7,z2,z209,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z11,z6]),(0,[z7,z2,z3,z4,z5,z6,z210]),(0,[z7,z2,z211,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z104,z6,z56]),(0,[z7,z2,z3,z4,z5,z6,z64]),(1,[z7,z106,z3,z4,z5,z75]),(0,[z7,z2,z108,z3,z4,z180,z6]),(0,[z7,z2,z3,z43,z19,z5,z6]),(0,[z7,z212,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z37])],[(0,[z7,z2,z3,z29,z58,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z213]),(0,[z14,z7,z3,z144,z4,z5,z6]),(0,[z7,z2,z209,z4,z18,z5,z6]),(0,[z7,z2,z3,z4,z214,z5,z6])],[(0,[z26,z7,z69,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z215,z6]),(0,[z7,z2,z3,z92,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z137,z76]),(0,[z7,z2,z216,z3,z4,z5,z6]),(0,[z7,z2,z217,z3,z4,z5,z6]),(0,[z7,z2,z3,z218,z4,z5,z6])],[(0,[z26,z7,z2,z139,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z219]),(0,[z7,z2,z3,z4,z220,z5,z6]),(0,[z221,z2,z3,z4,z5,z6,z56]),(0,[z7,z2,z3,z18,z5,z59,z6]),(0,[z7,z2,z3,z4,z5,z137,z6]),(0,[z7,z2,z3,z4,z5,z222,z6]),(0,[z7,z2,z223,z3,z4,z5,z6])]],
   [[(0,[z26,z7,z2,z3,z4,z5,z82]),(0,[z7,z2,z3,z4,z224,z5,z6]),(0,[z7,z2,z3,z4,z5,z225,z6]),(0,[z7,z2,z3,z4,z226,z10,z6]),(0,[z7,z2,z227,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z228,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z229]),(0,[z7,z2,z3,z4,z230,z5,z6]),(0,[z7,z2,z231,z3,z4,z5,z6]),(1,[z7,z2,z78,z4,z5,z137]),(0,[z7,z2,z232,z3,z4,z5,z6])],[(0,[z233,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z234,z6]),(0,[z7,z106,z2,z3,z235,z5,z6]),(0,[z7,z2,z108,z3,z4,z236,z6]),(0,[z7,z2,z237,z3,z4,z5,z6]),(0,[z7,z2,z3,z19,z5,z109,z6]),(0,[z7,z2,z3,z238,z4,z5,z6]),(0,[z7,z2,z113,z239,z4,z5,z6]),(0,[z7,z2,z3,z240,z4,z5,z6])],[(0,[z7,z2,z112,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z55,z6]),(0,[z7,z2,z3,z4,z5,z104,z76]),(0,[z241,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z242,z5,z6]),(1,[z7,z2,z3,z4,z5,z243]),(0,[z244,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z155,z6]),(0,[z7,z2,z3,z4,z5,z104,z6]),(0,[z7,z2,z245,z3,z4,z5,z6]),(0,[z7,z118,z2,z15,z4,z5,z6]),(0,[z246,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z247,z6]),(0,[z7,z2,z3,z4,z9,z248,z6]),(0,[z249,z7,z2,z3,z4,z5,z6])],[(0,[z250,z7,z2,z3,z4,z5,z6]),(0,[z147,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z118,z2,z4,z5,z6]),(0,[z1,z7,z118,z2,z4,z5,z6]),(0,[z7,z2,z3,z152,z4,z5,z6]),(0,[z251,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z252,z5,z6]),(1,[z7,z2,z253,z3,z4,z6]),(0,[z7,z2,z254,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z109,z6]),(1,[z7,z2,z211,z3,z4,z5])],[(0,[z14,z1,z7,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z255,z5,z6]),(0,[z7,z256,z2,z3,z4,z5,z6])],[(0,[z7,z2,z257,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z258,z6]),(0,[z7,z259,z2,z3,z17,z5,z6]),(0,[z7,z2,z260,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z261,z6]),(0,[z7,z2,z3,z262,z4,z5,z6]),(0,[z7,z263,z2,z3,z4,z5,z6]),(0,[z7,z2,z40,z3,z4,z154,z6]),(0,[z7,z2,z40,z3,z4,z169,z6]),(0,[z7,z2,z3,z5,z6,z178,z41])]],
   [[(0,[z7,z264,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z265,z4,z5,z6]),(0,[z7,z2,z3,z4,z176,z10,z6]),(1,[z7,z2,z3,z4,z5,z48]),(0,[z7,z2,z3,z4,z169,z5,z11])],[(1,[z7,z38,z3,z4,z5,z6]),(0,[z102,z7,z2,z3,z124,z5,z6]),(0,[z7,z266,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z267,z6]),(0,[z268,z7,z2,z3,z4,z5,z6])],[(0,[z148,z2,z3,z129,z4,z5,z6]),(0,[z7,z2,z269,z3,z4,z5,z6]),(0,[z7,z2,z3,z124,z18,z5,z6]),(0,[z7,z2,z254,z3,z4,z5,z6]),(0,[z7,z2,z3,z17,z5,z59,z6]),(0,[z7,z2,z3,z4,z5,z270,z6]),(0,[z271,z7,z2,z3,z4,z5,z6])],[(0,[z272,z7,z2,z3,z4,z5,z6]),(0,[z273,z7,z2,z3,z4,z5,z6])],[(0,[z26,z7,z2,z3,z4,z5,z6]),(0,[z274,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z124,z4,z10,z6]),(0,[z7,z2,z3,z275,z4,z5,z6]),(0,[z7,z2,z3,z4,z276,z5,z6]),(0,[z7,z2,z277,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z278,z6]),(0,[z7,z2,z3,z4,z5,z6,z279])],[(0,[z280,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z92,z4,z19,z6])],[(0,[z7,z2,z3,z281,z4,z5,z6]),(0,[z7,z15,z3,z144,z4,z5,z6]),(0,[z7,z2,z3,z43,z4,z10,z6]),(0,[z7,z2,z3,z4,z193,z10,z6]),(0,[z7,z2,z3,z4,z5,z282,z6])],[(0,[z2,z143,z3,z129,z4,z5,z6]),(0,[z7,z2,z129,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z127,z6]),(0,[z7,z2,z3,z4,z58,z10,z6]),(1,[z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z283,z6]),(1,[z12,z7,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z9,z242,z6]),(0,[z7,z2,z3,z4,z284,z5,z6]),(0,[z285,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z286,z5,z6]),(1,[z7,z2,z287,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z137,z56]),(0,[z7,z2,z78,z3,z4,z5,z74]),(0,[z7,z2,z3,z4,z5,z288,z6]),(0,[z7,z2,z113,z81,z4,z5,z6])],[(0,[z148,z7,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z289,z4,z5,z6]),(1,[z7,z2,z3,z4,z180,z6])],[(0,[z7,z2,z15,z112,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z6,z41])],[(0,[z7,z2,z3,z4,z5,z290,z6]),(1,[z97,z2,z3,z4,z39,z6]),(0,[z7,z2,z3,z4,z5,z291,z6]),(0,[z7,z2,z4,z5,z137,z6,z74]),(0,[z7,z2,z113,z138,z3,z5,z6])],[(0,[z7,z2,z3,z292,z4,z5,z6]),(0,[z7,z2,z293,z3,z4,z5,z6]),(1,[z7,z2,z294,z4,z5,z74])],[(0,[z7,z2,z3,z4,z295,z5,z6]),(0,[z7,z296,z2,z3,z4,z5,z6]),(0,[z7,z2,z47,z3,z194,z5,z6])],[(0,[z7,z2,z297,z3,z4,z5,z6]),(0,[z298,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z229]),(0,[z7,z299,z106,z3,z4,z5,z6]),(1,[z7,z2,z3,z300,z5,z6]),(0,[z7,z2,z138,z3,z92,z5,z6])],[(0,[z26,z148,z2,z3,z4,z5,z6]),(0,[z7,z69,z2,z3,z4,z5,z6]),(0,[z7,z2,z301,z3,z4,z5,z6]),(0,[z7,z2,z302,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z303,z5,z6]),(0,[z304,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z305,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z181]),(0,[z7,z2,z306,z3,z4,z5,z6]),(0,[z307,z7,z2,z3,z4,z5,z6]),(0,[z7,z98,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z10,z6,z76]),(0,[z7,z299,z3,z4,z5,z6,z76]),(0,[z7,z2,z4,z154,z5,z67,z6]),(0,[z7,z2,z3,z4,z169,z5,z74])],[(1,[z308,z2,z3,z4,z5,z6]),(0,[z99,z7,z2,z3,z4,z9,z6]),(1,[z7,z2,z3,z4,z309,z6])],[(0,[z7,z2,z3,z4,z154,z226,z6]),(0,[z7,z2,z3,z4,z5,z6,z310]),(0,[z7,z2,z311,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z9,z137,z6])],[(0,[z7,z2,z112,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z312]),(0,[z7,z2,z3,z4,z313,z5,z6]),(0,[z7,z314,z2,z3,z4,z5,z6])],[(1,[z7,z259,z3,z17,z5,z6])],[(1,[z7,z2,z3,z4,z5,z315]),(0,[z148,z7,z69,z3,z4,z5,z6]),(0,[z7,z2,z3,z316,z4,z5,z6]),(0,[z97,z2,z3,z4,z39,z5,z6]),(0,[z7,z317,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z318,z5,z6]),(0,[z7,z319,z2,z3,z4,z5,z6])],[(0,[z7,z2,z320,z3,z4,z5,z6]),(0,[z7,z2,z321,z3,z4,z5,z6]),(0,[z7,z2,z24,z3,z4,z6,z68])],[(0,[z322,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z323,z3,z4,z5,z6]),(0,[z324,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z325,z5,z6]),(0,[z7,z2,z311,z3,z4,z5,z6]),(1,[z7,z2,z47,z4,z154,z6]),(0,[z7,z2,z3,z4,z5,z326,z6])]],
   [[(0,[z7,z2,z112,z3,z4,z10,z6]),(0,[z7,z2,z327,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z328,z5,z6]),(0,[z7,z329,z2,z3,z4,z5,z6])],[(0,[z7,z2,z330,z3,z4,z5,z6]),(0,[z14,z7,z2,z3,z4,z331,z6]),(0,[z7,z2,z3,z4,z332,z5,z6]),(0,[z333,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z55,z6]),(0,[z7,z334,z3,z4,z5,z10,z6])],[(0,[z335,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z155,z6]),(0,[z7,z2,z3,z144,z4,z9,z6]),(0,[z7,z2,z113,z3,z4,z5,z74]),(0,[z7,z2,z3,z4,z5,z6,z336])],[(0,[z7,z2,z337,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z338,z6]),(0,[z7,z2,z339,z3,z4,z5,z6]),(0,[z340,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z341,z4,z5,z6]),(0,[z7,z2,z342,z3,z4,z5,z6])],[(0,[z0,z7,z2,z129,z4,z5,z6]),(0,[z1,z7,z2,z129,z4,z5,z6]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z7,z2,z3,z343,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z344,z6]),(0,[z7,z2,z345,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z346,z5,z6]),(0,[z7,z2,z3,z4,z9,z11,z6])],[(0,[z7,z2,z3,z4,z347,z5,z6]),(0,[z7,z2,z3,z4,z5,z348,z6]),(0,[z7,z2,z3,z4,z10,z10,z6]),(0,[z7,z2,z40,z3,z4,z67,z6])]],
   [[(1,[z7,z2,z3,z170,z5,z6]),(0,[z349,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z171]),(0,[z7,z2,z3,z4,z350,z5,z6]),(0,[z7,z2,z3,z4,z5,z351,z6]),(0,[z7,z2,z3,z4,z5,z352,z6]),(0,[z7,z2,z159,z3,z4,z9,z6]),(0,[z7,z2,z353,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z354,z5,z6]),(0,[z7,z2,z3,z4,z5,z355,z6])],[(0,[z7,z2,z3,z4,z10,z6,z56]),(0,[z356,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z357,z3,z4,z5,z6]),(0,[z7,z2,z138,z3,z4,z5,z6])],[(0,[z148,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z358,z6]),(0,[z7,z2,z62,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z359,z6]),(0,[z7,z182,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z360,z5,z6]),(0,[z361,z7,z2,z3,z4,z9,z6]),(0,[z362,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z40,z3,z136,z4,z5])],[(0,[z363,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z248,z6]),(0,[z7,z2,z3,z92,z4,z154,z6]),(0,[z7,z2,z3,z79,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z364,z6])],[(1,[z7,z2,z3,z4,z5,z181]),(0,[z7,z2,z3,z124,z58,z5,z6]),(1,[z7,z2,z365,z3,z5,z6]),(0,[z7,z259,z2,z3,z4,z5,z6]),(0,[z7,z2,z366,z3,z4,z5,z6])],[(1,[z26,z143,z3,z4,z5,z6]),(0,[z42,z7,z2,z3,z4,z11,z6]),(0,[z12,z7,z3,z4,z9,z5,z6]),(0,[z7,z367,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z368])],[(0,[z7,z2,z3,z4,z5,z6,z369]),(0,[z7,z2,z47,z4,z154,z5,z6]),(0,[z7,z2,z3,z4,z151,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z370])]],
   [[(0,[z7,z2,z143,z3,z4,z9,z6]),(0,[z7,z371,z2,z3,z4,z5,z6]),(0,[z7,z372,z2,z3,z4,z5,z6]),(0,[z7,z259,z2,z3,z4,z5,z145]),(0,[z361,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z92,z4,z109,z6]),(0,[z7,z2,z373,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z374])],[(0,[z7,z2,z3,z4,z375,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z376]),(0,[z377,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z59,z6])],[(0,[z7,z2,z3,z4,z5,z378,z6]),(0,[z26,z7,z2,z3,z4,z5,z315]),(0,[z7,z2,z379,z3,z4,z5,z6]),(0,[z380,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z291,z6]),(0,[z7,z2,z3,z4,z10,z6,z208]),(0,[z381,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z84,z5,z6]),(0,[z382,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z78,z3,z4,z5,z6])],[(0,[z383,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z384,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z169,z5,z41])],[(0,[z26,z7,z143,z3,z4,z5,z6]),(0,[z7,z2,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z58,z9,z6]),(0,[z7,z2,z3,z385,z4,z5,z6]),(1,[z7,z2,z3,z235,z5,z6]),(0,[z7,z2,z78,z4,z18,z5,z6])],[(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z386,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z15,z3,z4,z5,z6]),(0,[z7,z2,z321,z3,z4,z10,z6])],[(0,[z7,z2,z3,z17,z124,z5,z6]),(0,[z7,z387,z2,z3,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z4,z134,z6]),(0,[z7,z2,z388,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z389,z6]),(1,[z221,z2,z3,z4,z5,z56]),(0,[z390,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z234,z6]),(0,[z7,z2,z209,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z391,z6])],[(0,[z7,z2,z392,z3,z4,z5,z6]),(0,[z7,z106,z3,z4,z5,z75,z6]),(0,[z7,z2,z3,z393,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z394,z6])],[(0,[z7,z395,z2,z3,z4,z5,z6]),(0,[z221,z7,z2,z3,z136,z4,z5]),(0,[z7,z2,z253,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z396,z6]),(0,[z7,z2,z3,z397,z4,z5,z6]),(0,[z7,z2,z3,z4,z169,z5,z6])],[(0,[z7,z2,z3,z4,z398,z5,z6]),(0,[z7,z2,z3,z399,z4,z5,z6]),(0,[z7,z2,z3,z400,z4,z9,z6]),(0,[z7,z2,z3,z4,z9,z67,z6])],[(0,[z7,z2,z3,z4,z401,z5,z6]),(0,[z7,z2,z3,z402,z4,z5,z6])],[(0,[z7,z2,z3,z403,z4,z5,z6]),(0,[z7,z2,z404,z3,z4,z5,z6]),(0,[z7,z2,z405,z3,z4,z5,z6])],[(0,[z406,z7,z2,z3,z4,z5,z6]),(1,[z7,z334,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z10,z75,z6]),(0,[z7,z2,z3,z4,z230,z9,z6])]],
   [[(0,[z7,z2,z3,z144,z4,z10,z6]),(0,[z7,z118,z2,z3,z4,z407,z6]),(0,[z7,z2,z408,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z409,z6])],[(0,[z2,z112,z3,z129,z4,z5,z6]),(0,[z7,z2,z3,z400,z4,z5,z6])],[(0,[z7,z2,z138,z3,z4,z10,z6]),(0,[z7,z299,z2,z3,z4,z5,z76]),(0,[z7,z2,z410,z3,z4,z5,z6]),(0,[z7,z2,z3,z411,z4,z5,z6])],[(0,[z148,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z39,z67,z6]),(0,[z7,z2,z3,z4,z5,z6,z412]),(0,[z7,z2,z3,z4,z5,z6,z413])],[(0,[z414,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z156,z10,z6]),(0,[z7,z2,z3,z4,z5,z415,z6]),(0,[z7,z2,z294,z3,z4,z5,z74]),(0,[z7,z2,z416,z3,z4,z5,z6]),(0,[z417,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z9,z226,z6]),(1,[z7,z2,z3,z4,z5,z418]),(0,[z7,z259,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z6,z419]),(0,[z420,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z113,z3,z4,z5,z76]),(0,[z7,z2,z3,z136,z4,z5,z76]),(0,[z7,z2,z3,z421,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z422]),(0,[z7,z2,z113,z3,z4,z5,z6])],[(0,[z423,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z424]),(0,[z7,z2,z78,z3,z4,z13,z6])]],
   [[(0,[z7,z2,z3,z425,z4,z5,z6]),(1,[z7,z2,z3,z4,z355,z6]),(0,[z7,z2,z426,z3,z4,z5,z6])],[(0,[z427,z7,z2,z3,z4,z5,z6]),(0,[z7,z428,z2,z3,z4,z5,z6]),(0,[z7,z429,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z430,z4,z5,z6]),(0,[z14,z7,z2,z3,z93,z5,z6]),(0,[z7,z2,z431,z3,z4,z5,z6])],[(0,[z26,z7,z2,z3,z4,z9,z6]),(0,[z7,z432,z2,z3,z4,z5,z6]),(0,[z420,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z433,z6]),(0,[z7,z2,z2,z3,z4,z9,z6])],[(0,[z7,z2,z3,z4,z5,z6,z434]),(0,[z7,z2,z3,z4,z435,z5,z6]),(0,[z7,z2,z436,z3,z4,z5,z6]),(0,[z7,z2,z78,z3,z4,z10,z6]),(0,[z7,z2,z47,z3,z4,z67,z6]),(0,[z7,z2,z211,z3,z4,z5,z109])],[(0,[z0,z7,z2,z3,z437,z5,z6]),(0,[z7,z2,z3,z4,z438,z5,z6]),(0,[z7,z2,z3,z4,z5,z439,z6]),(0,[z7,z440,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z441,z9,z6]),(0,[z7,z2,z3,z92,z4,z67,z6]),(0,[z7,z2,z113,z3,z19,z5,z6])],[(0,[z7,z2,z143,z3,z4,z10,z6]),(0,[z42,z7,z2,z3,z4,z226,z6]),(0,[z7,z2,z3,z442,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z443])],[(0,[z7,z2,z444,z3,z4,z5,z6]),(1,[z7,z2,z3,z28,z4,z6]),(0,[z2,z3,z4,z39,z5,z226,z6]),(0,[z7,z2,z15,z3,z4,z10,z6]),(0,[z7,z2,z3,z445,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z6,z68]),(0,[z7,z2,z446,z3,z4,z5,z6]),(0,[z7,z2,z447,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z11,z6])],[(0,[z7,z2,z2,z3,z4,z5,z6]),(0,[z7,z448,z2,z3,z4,z5,z6]),(0,[z7,z2,z449,z3,z4,z5,z6]),(0,[z7,z450,z2,z3,z4,z5,z6]),(0,[z7,z2,z40,z138,z3,z4,z6])]],
   [[(0,[z7,z2,z3,z4,z451,z5,z6]),(0,[z7,z2,z3,z452,z4,z5,z6])],[(1,[z7,z2,z3,z4,z378,z6]),(0,[z7,z2,z3,z4,z441,z5,z6]),(0,[z7,z2,z3,z453,z4,z5,z6]),(0,[z7,z2,z40,z3,z4,z5,z41])],[(0,[z7,z454,z2,z3,z4,z5,z6])],[(0,[z1,z2,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z70,z6]),(0,[z7,z2,z455,z3,z4,z5,z6]),(0,[z7,z2,z456,z3,z4,z5,z6])],[(0,[z7,z457,z2,z3,z4,z5,z6]),(0,[z458,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z209,z3,z18,z5,z6]),(0,[z7,z2,z294,z4,z5,z6,z74])],[(0,[z7,z2,z3,z459,z4,z5,z6]),(0,[z7,z460,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z461,z4,z5,z6]),(0,[z7,z69,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z462,z6]),(0,[z463,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z464,z4,z5,z6])],[(0,[z7,z2,z253,z3,z4,z6,z56]),(0,[z7,z98,z2,z3,z58,z5,z6]),(0,[z7,z2,z209,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z243,z6]),(0,[z7,z2,z3,z4,z5,z465,z6]),(1,[z7,z2,z3,z79,z5,z6])],[(0,[z7,z2,z3,z4,z466,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z467]),(0,[z7,z2,z108,z209,z4,z5,z6]),(0,[z7,z2,z3,z4,z13,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z29,z5,z6]),(0,[z7,z2,z3,z4,z9,z468,z6]),(0,[z7,z2,z3,z4,z469,z5,z6])],[(0,[z7,z2,z3,z4,z5,z470,z6]),(0,[z72,z7,z2,z3,z5,z59,z6]),(0,[z7,z2,z3,z4,z471,z5,z6])],[(0,[z0,z14,z7,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z472,z5,z6]),(0,[z7,z2,z473,z3,z4,z5,z6]),(0,[z7,z2,z474,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z236,z6]),(0,[z7,z2,z294,z78,z4,z5,z6])],[(0,[z72,z102,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z475,z4,z5,z6]),(0,[z308,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z46,z5,z6]),(0,[z7,z2,z43,z4,z18,z5,z6]),(0,[z7,z2,z3,z4,z5,z476,z6]),(0,[z477,z7,z2,z3,z4,z5,z6])],[(0,[z7,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z478]),(0,[z7,z2,z321,z3,z4,z9,z6]),(0,[z7,z479,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z480,z4,z5,z6]),(0,[z7,z481,z2,z3,z4,z5,z6]),(0,[z7,z2,z482,z3,z4,z5,z6])],[(0,[z7,z483,z2,z3,z4,z5,z6]),(0,[z14,z7,z2,z3,z4,z5,z172]),(0,[z7,z2,z484,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z485,z6])],[(0,[z7,z2,z486,z3,z4,z5,z6]),(0,[z22,z7,z2,z3,z136,z4,z5]),(0,[z7,z487,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z488,z5,z6]),(0,[z221,z7,z2,z3,z4,z5,z104]),(0,[z7,z2,z3,z489,z4,z5,z6]),(0,[z7,z2,z78,z4,z5,z137,z6]),(0,[z7,z2,z3,z4,z5,z490,z6]),(0,[z7,z2,z3,z4,z5,z288,z109])],[(0,[z7,z491,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z28,z4,z5,z6])],[(0,[z7,z2,z3,z492,z4,z5,z6]),(0,[z7,z2,z287,z3,z4,z29,z6]),(0,[z14,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z493,z3,z4,z5,z6]),(0,[z7,z494,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z495,z6]),(0,[z7,z496,z2,z3,z4,z5,z6])],[(0,[z7,z2,z113,z3,z17,z5,z6])],[(0,[z7,z2,z3,z4,z5,z67,z6]),(0,[z497,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z498]),(0,[z7,z2,z3,z4,z5,z6,z499])],[(1,[z7,z2,z500,z4,z5,z6]),(0,[z7,z2,z3,z136,z4,z5,z74]),(0,[z7,z2,z3,z4,z5,z501,z6])],[(0,[z26,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z502,z5,z6]),(0,[z503,z7,z2,z3,z4,z5,z6]),(0,[z14,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z2,z3,z4,z10,z6]),(0,[z7,z2,z294,z3,z4,z5,z6])]],
   [[(0,[z7,z259,z2,z3,z4,z291,z6]),(0,[z7,z2,z138,z3,z4,z9,z6]),(0,[z504,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z505,z6]),(0,[z7,z2,z3,z4,z5,z506,z6]),(1,[z7,z2,z3,z151,z5,z6]),(0,[z7,z2,z3,z4,z507,z5,z6]),(0,[z7,z2,z40,z3,z4,z5,z11])],[(0,[z148,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z154,z39,z6]),(0,[z7,z2,z3,z453,z4,z10,z6])],[(0,[z7,z2,z3,z4,z5,z508,z6]),(0,[z7,z2,z509,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z510,z6]),(0,[z7,z259,z2,z3,z4,z9,z6])],[(0,[z7,z511,z2,z3,z4,z5,z6]),(0,[z2,z3,z124,z4,z29,z5,z6]),(0,[z42,z7,z2,z138,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z418,z6]),(0,[z7,z2,z113,z40,z3,z4,z5])],[(0,[z0,z7,z2,z3,z4,z438,z6]),(0,[z7,z2,z3,z4,z5,z226,z6]),(0,[z7,z2,z3,z4,z9,z5,z6]),(0,[z7,z2,z321,z4,z5,z67,z6]),(0,[z512,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z513,z5,z6]),(0,[z7,z2,z3,z4,z5,z514,z6]),(0,[z7,z2,z40,z3,z92,z4,z6]),(0,[z7,z515,z2,z3,z4,z5,z6])],[(0,[z516,z7,z2,z3,z4,z5,z6]),(0,[z517,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z315,z6]),(0,[z518,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z10,z6]),(1,[z7,z2,z140,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z6,z519]),(1,[z7,z3,z4,z9,z10,z6]),(0,[z7,z2,z3,z4,z9,z6,z41]),(0,[z7,z2,z520,z3,z4,z5,z6])],[(0,[z7,z38,z2,z3,z4,z5,z6]),(0,[z521,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z127,z6]),(0,[z7,z2,z78,z3,z4,z9,z6]),(0,[z7,z2,z108,z3,z4,z5,z20]),(0,[z7,z2,z522,z3,z4,z5,z6]),(0,[z7,z2,z3,z523,z4,z5,z6])],[(0,[z7,z2,z3,z524,z4,z5,z6]),(0,[z7,z69,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z525,z6]),(0,[z7,z2,z3,z43,z58,z5,z6]),(1,[z7,z2,z3,z4,z513,z6]),(0,[z7,z2,z526,z3,z4,z5,z6]),(0,[z7,z2,z473,z3,z4,z10,z6]),(0,[z7,z2,z474,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z527,z5,z6]),(0,[z528,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z6,z529,z68]),(0,[z7,z530,z2,z3,z4,z5,z6])],[(0,[z7,z2,z113,z3,z4,z5,z59]),(0,[z7,z2,z3,z136,z4,z5,z59])],[(1,[z7,z2,z3,z27,z5,z6]),(0,[z7,z2,z3,z152,z4,z29,z5]),(0,[z7,z531,z2,z3,z4,z5,z6]),(0,[z532,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z226,z67,z6]),(0,[z7,z2,z15,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z137,z75])],[(0,[z7,z2,z3,z43,z5,z59,z6])],[(0,[z533,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z534,z6]),(0,[z7,z2,z535,z3,z4,z5,z6]),(0,[z536,z7,z2,z3,z4,z5,z6]),(0,[z97,z7,z2,z138,z3,z4,z6]),(0,[z537,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z407,z6]),(0,[z7,z2,z538,z3,z4,z5,z6]),(0,[z7,z539,z2,z3,z4,z5,z6])],[(0,[z22,z2,z3,z4,z5,z104,z6]),(0,[z7,z2,z3,z325,z4,z5,z6]),(1,[z7,z2,z3,z4,z85,z6]),(0,[z540,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z138,z3,z4,z19,z6]),(0,[z7,z2,z3,z4,z5,z6,z541])]],
   [[(0,[z542,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z40,z3,z4,z5,z74]),(0,[z7,z2,z3,z4,z5,z543,z6])],[(0,[z544,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z129,z4,z9,z6]),(0,[z7,z2,z545,z3,z4,z5,z6]),(0,[z221,z7,z2,z3,z4,z5,z56]),(0,[z7,z2,z546,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z547,z5,z6]),(0,[z7,z2,z3,z4,z10,z137,z6]),(0,[z7,z2,z3,z4,z169,z9,z6]),(0,[z7,z2,z3,z92,z4,z11,z6])],[(1,[z7,z2,z459,z4,z5,z6]),(0,[z7,z2,z500,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z548,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z549]),(0,[z7,z2,z3,z4,z5,z75,z104]),(0,[z14,z7,z2,z144,z4,z5,z6])],[(0,[z7,z69,z118,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z4,z5,z6]),(0,[z97,z7,z2,z3,z4,z11,z6]),(0,[z7,z2,z3,z550,z4,z5,z6]),(0,[z7,z259,z2,z3,z4,z5,z418]),(0,[z551,z7,z2,z3,z4,z5,z6]),(0,[z7,z552,z2,z3,z4,z5,z6]),(0,[z7,z2,z209,z3,z43,z5,z6]),(0,[z7,z2,z113,z3,z4,z5,z68]),(0,[z7,z2,z3,z136,z4,z5,z68])],[(0,[z7,z334,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z553,z5,z6]),(0,[z7,z2,z47,z3,z4,z5,z6]),(0,[z7,z2,z554,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z555,z5,z6])],[(0,[z102,z7,z2,z3,z29,z5,z6]),(0,[z7,z2,z3,z4,z9,z556,z6]),(0,[z7,z2,z557,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z123,z6]),(0,[z7,z2,z3,z129,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z104,z6]),(0,[z7,z2,z558,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z559]),(0,[z7,z560,z2,z3,z4,z5,z6]),(1,[z7,z2,z81,z4,z5,z6])],[(0,[z7,z561,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z562,z5,z6]),(0,[z14,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z6,z563]),(0,[z7,z2,z294,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z10,z109,z6])]],
   [[(0,[z26,z7,z2,z3,z4,z510,z6]),(0,[z7,z564,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z9,z6]),(0,[z7,z2,z3,z4,z5,z468,z6]),(0,[z7,z106,z2,z3,z4,z5,z76])],[(0,[z565,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z172,z6]),(0,[z7,z2,z3,z566,z4,z5,z6]),(0,[z7,z2,z567,z3,z4,z5,z6]),(0,[z7,z334,z2,z3,z4,z5,z6]),(0,[z7,z299,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z19,z5,z6]),(0,[z7,z2,z3,z4,z5,z568,z6])],[(0,[z7,z2,z3,z437,z4,z5,z6]),(0,[z569,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z570,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z571,z5,z6]),(0,[z7,z299,z2,z3,z4,z65,z6])],[(0,[z7,z2,z572,z3,z4,z5,z6]),(0,[z7,z2,z3,z235,z4,z5,z6]),(0,[z7,z2,z138,z3,z18,z5,z6])],[(0,[z7,z2,z365,z3,z4,z5,z6]),(0,[z22,z7,z2,z3,z4,z5,z104]),(0,[z7,z2,z3,z4,z5,z573,z6]),(0,[z7,z2,z113,z3,z4,z9,z6]),(0,[z7,z2,z3,z136,z4,z9,z6])],[(0,[z574,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z5,z6])],[(1,[z7,z2,z3,z437,z5,z6]),(0,[z7,z2,z575,z3,z4,z5,z6]),(0,[z72,z7,z2,z3,z124,z5,z6]),(0,[z42,z2,z3,z4,z5,z226,z6]),(0,[z14,z7,z2,z3,z4,z5,z229]),(0,[z7,z2,z3,z4,z5,z576,z6]),(0,[z7,z2,z3,z4,z577,z5,z6]),(0,[z7,z299,z2,z3,z4,z5,z6]),(0,[z7,z578,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z136,z5,z59])],[(0,[z7,z2,z579,z3,z4,z5,z6])]],
   [[(0,[z7,z118,z143,z3,z4,z5,z6]),(0,[z7,z580,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z6,z56]),(0,[z14,z7,z118,z3,z4,z5,z6])],[(0,[z14,z308,z2,z3,z4,z5,z6]),(0,[z7,z118,z15,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z283,z6]),(0,[z7,z2,z3,z4,z5,z6,z581]),(0,[z7,z2,z3,z4,z582,z5,z6]),(0,[z7,z2,z3,z136,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z583,z6]),(0,[z7,z2,z3,z4,z584,z5,z6]),(0,[z7,z2,z321,z3,z4,z154,z6]),(0,[z7,z2,z3,z4,z5,z6,z585]),(0,[z7,z2,z586,z3,z4,z5,z6])],[(0,[z26,z7,z2,z3,z84,z5,z6]),(0,[z7,z587,z2,z3,z4,z5,z6]),(0,[z588,z7,z2,z3,z4,z5,z6]),(0,[z42,z7,z2,z3,z92,z4,z6]),(0,[z7,z2,z3,z17,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z589,z6])],[(0,[z7,z2,z108,z4,z5,z6,z74])],[(0,[z590,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z78,z3,z4,z5,z137]),(0,[z7,z2,z3,z591,z4,z5,z6])],[(0,[z7,z2,z592,z3,z4,z5,z6]),(0,[z7,z2,z3,z239,z4,z5,z6])],[(0,[z26,z7,z2,z459,z4,z5,z6]),(0,[z7,z2,z3,z4,z35,z5,z6]),(0,[z7,z2,z593,z3,z4,z5,z6]),(0,[z14,z7,z2,z3,z325,z5,z6]),(0,[z594,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z595,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z596]),(0,[z7,z2,z3,z4,z5,z597,z6]),(1,[z7,z2,z3,z194,z5,z6])],[(0,[z7,z598,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z525,z6]),(0,[z7,z599,z2,z3,z4,z5,z6])],[(0,[z7,z2,z108,z78,z4,z5,z6])],[(0,[z7,z600,z2,z3,z4,z5,z6]),(0,[z7,z2,z601,z3,z4,z5,z6]),(0,[z221,z22,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z75,z56]),(0,[z7,z2,z602,z3,z4,z5,z6]),(0,[z551,z7,z2,z3,z4,z10,z6]),(0,[z7,z2,z603,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z604,z6]),(0,[z7,z2,z3,z4,z5,z6,z529])],[(0,[z7,z143,z3,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z605,z5,z6]),(0,[z7,z2,z3,z4,z9,z39,z6]),(0,[z606,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z607,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z608,z5,z6])],[(0,[z7,z2,z3,z4,z510,z5,z6]),(0,[z7,z2,z3,z4,z5,z5,z6]),(0,[z97,z7,z2,z3,z92,z4,z6]),(1,[z7,z2,z3,z4,z407,z6]),(0,[z7,z2,z3,z58,z18,z5,z6]),(0,[z7,z2,z609,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z169,z5,z137]),(0,[z7,z2,z3,z610,z4,z5,z6])],[(0,[z7,z2,z3,z129,z4,z10,z6]),(0,[z7,z2,z3,z4,z29,z9,z6]),(0,[z7,z2,z140,z3,z4,z29,z5]),(0,[z7,z2,z3,z4,z169,z10,z6]),(0,[z7,z2,z611,z3,z4,z5,z6]),(0,[z7,z2,z47,z3,z4,z5,z37]),(0,[z7,z2,z138,z3,z4,z154,z6])],[(0,[z7,z2,z3,z29,z18,z5,z6]),(0,[z7,z2,z3,z612,z4,z5,z6]),(0,[z42,z7,z2,z40,z3,z4,z6]),(0,[z7,z2,z3,z4,z9,z6,z74]),(0,[z7,z2,z3,z4,z613,z5,z6]),(0,[z7,z2,z3,z5,z59,z6,z68])]],
   [[(0,[z7,z2,z3,z4,z472,z9,z6]),(0,[z7,z2,z3,z4,z5,z6,z41])],[(0,[z0,z7,z62,z3,z4,z5,z6]),(0,[z0,z7,z2,z112,z4,z5,z6]),(0,[z1,z7,z2,z112,z4,z5,z6]),(0,[z7,z614,z2,z3,z4,z5,z6]),(0,[z7,z334,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z19,z10,z6]),(0,[z615,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z171,z6]),(0,[z97,z7,z2,z3,z4,z226,z6]),(0,[z221,z7,z2,z113,z3,z4,z5]),(0,[z7,z2,z108,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z300,z5,z6]),(0,[z7,z2,z138,z3,z4,z109,z6])],[(0,[z102,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z6,z616]),(0,[z7,z2,z408,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z10,z67,z6]),(0,[z7,z2,z47,z3,z300,z5,z6]),(0,[z7,z2,z40,z3,z4,z5,z6])],[(0,[z0,z2,z3,z129,z4,z5,z6]),(0,[z42,z7,z2,z3,z4,z39,z6]),(0,[z7,z2,z617,z3,z4,z5,z6]),(1,[z7,z299,z3,z4,z5,z76]),(0,[z7,z2,z618,z3,z4,z5,z6])],[(0,[z22,z7,z2,z3,z4,z5,z56]),(0,[z7,z98,z2,z3,z4,z85,z6]),(0,[z7,z2,z3,z619,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z10,z6]),(0,[z7,z2,z3,z4,z9,z75,z6]),(0,[z7,z106,z2,z3,z4,z45,z6]),(0,[z7,z106,z2,z3,z4,z46,z6]),(0,[z7,z2,z620,z3,z4,z5,z6])],[(0,[z7,z2,z500,z143,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z621]),(0,[z7,z259,z98,z3,z4,z5,z6]),(0,[z7,z299,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z236,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z622]),(0,[z7,z2,z40,z3,z4,z6,z41])],[(0,[z7,z2,z108,z3,z4,z5,z6]),(0,[z7,z2,z113,z3,z18,z5,z6])]],
   [[(0,[z102,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z93,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z623]),(0,[z7,z2,z3,z4,z5,z624,z6]),(0,[z7,z2,z3,z4,z625,z5,z6]),(0,[z7,z2,z3,z4,z5,z626,z6]),(0,[z7,z2,z113,z3,z4,z5,z137])],[(0,[z7,z2,z3,z4,z331,z5,z6]),(1,[z7,z98,z3,z58,z5,z6]),(0,[z7,z2,z3,z4,z5,z627,z6]),(0,[z7,z2,z113,z3,z4,z10,z6]),(0,[z7,z2,z3,z136,z4,z10,z6]),(0,[z7,z2,z3,z4,z318,z5,z6])],[(0,[z7,z2,z3,z43,z124,z5,z6]),(0,[z7,z118,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z628,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z629]),(0,[z7,z2,z3,z4,z5,z75,z74]),(0,[z630,z7,z2,z3,z4,z5,z6]),(0,[z7,z631,z2,z3,z4,z5,z6])],[(0,[z632,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z633,z4,z5,z6]),(0,[z7,z2,z634,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z635,z6]),(0,[z7,z2,z3,z4,z5,z636,z6]),(0,[z7,z2,z3,z4,z637,z5,z6])],[(0,[z102,z7,z2,z113,z3,z5,z6]),(0,[z7,z2,z3,z4,z134,z5,z6]),(0,[z7,z2,z3,z4,z5,z638,z6]),(0,[z7,z2,z3,z4,z11,z6,z41])],[(0,[z7,z2,z639,z3,z4,z5,z6]),(0,[z7,z2,z3,z640,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z358,z6]),(0,[z7,z2,z3,z641,z4,z5,z6]),(0,[z642,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z294,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z556,z6]),(0,[z7,z2,z3,z4,z5,z6,z643]),(0,[z644,z7,z2,z3,z4,z5,z6])],[(0,[z97,z7,z2,z3,z4,z39,z6]),(0,[z221,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z6,z645])],[(1,[z7,z2,z139,z4,z5,z6]),(1,[z7,z2,z3,z4,z438,z6]),(0,[z7,z2,z3,z4,z646,z5,z6]),(0,[z647,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z309,z5,z6]),(0,[z7,z106,z2,z3,z318,z5,z6]),(0,[z648,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z48,z6]),(0,[z7,z2,z586,z3,z5,z6,z41])]],
   [[(1,[z7,z2,z3,z4,z5,z82]),(0,[z649,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z650,z4,z5,z6]),(0,[z7,z651,z2,z3,z4,z5,z6]),(0,[z7,z259,z2,z3,z4,z513,z6]),(0,[z7,z299,z2,z3,z4,z309,z6]),(0,[z7,z2,z3,z4,z5,z652,z6])],[(0,[z26,z7,z2,z3,z4,z378,z6]),(0,[z7,z259,z2,z3,z58,z5,z6]),(0,[z7,z2,z138,z3,z5,z59,z6])],[(0,[z7,z2,z138,z3,z43,z5,z6]),(0,[z7,z2,z321,z3,z4,z67,z6]),(0,[z7,z2,z3,z653,z4,z5,z6])],[(1,[z147,z7,z2,z4,z5,z6]),(0,[z7,z2,z3,z17,z29,z5,z6]),(0,[z221,z7,z2,z3,z4,z5,z6]),(0,[z7,z654,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z9,z6]),(0,[z7,z2,z108,z3,z4,z5,z243])],[(0,[z7,z2,z3,z4,z5,z655,z6]),(0,[z7,z259,z3,z17,z4,z5,z6]),(0,[z7,z2,z3,z4,z9,z6,z68]),(0,[z656,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z288]),(1,[z7,z2,z586,z3,z5,z6])],[(0,[z7,z2,z3,z4,z657,z5,z6]),(0,[z7,z2,z3,z658,z4,z5,z6]),(0,[z7,z2,z659,z3,z4,z5,z6])],[(0,[z660,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z661,z5,z6])],[(1,[z72,z2,z3,z29,z5,z6]),(0,[z7,z2,z3,z4,z662,z5,z6]),(0,[z7,z2,z663,z3,z4,z5,z6]),(1,[z7,z2,z108,z43,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z123,z5,z6]),(1,[z42,z2,z3,z4,z226,z6]),(0,[z7,z2,z3,z4,z5,z6,z56]),(0,[z7,z2,z3,z664,z4,z5,z6]),(0,[z7,z2,z47,z321,z4,z5,z6]),(0,[z7,z2,z3,z4,z665,z5,z6])],[(1,[z0,z2,z129,z4,z5,z6]),(0,[z7,z2,z3,z124,z4,z5,z6]),(1,[z7,z2,z3,z4,z331,z6]),(0,[z7,z2,z3,z4,z5,z45,z6]),(0,[z7,z2,z666,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z667]),(1,[z7,z2,z3,z4,z6,z529])],[(0,[z7,z2,z668,z3,z4,z5,z6]),(0,[z42,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z669,z3,z4,z5,z6]),(0,[z7,z670,z2,z3,z4,z5,z6]),(0,[z7,z2,z40,z3,z4,z10,z6]),(1,[z7,z2,z239,z4,z5,z6])],[(0,[z7,z2,z287,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z137,z104]),(0,[z7,z2,z3,z4,z5,z6,z20]),(0,[z7,z2,z138,z3,z5,z109,z6])],[(1,[z7,z2,z3,z4,z70,z6]),(0,[z7,z2,z3,z4,z5,z671,z6]),(0,[z7,z2,z672,z3,z4,z5,z6]),(0,[z7,z118,z2,z144,z4,z5,z6]),(0,[z7,z2,z673,z3,z4,z5,z6]),(0,[z7,z2,z108,z3,z18,z5,z6]),(0,[z7,z674,z2,z3,z4,z5,z6])],[(0,[z7,z2,z675,z3,z4,z5,z6]),(0,[z7,z2,z138,z3,z4,z67,z6])],[(0,[z7,z2,z3,z4,z676,z5,z6]),(0,[z72,z7,z2,z3,z29,z5,z6]),(0,[z7,z2,z3,z4,z39,z5,z6]),(0,[z7,z98,z2,z3,z4,z525,z6]),(0,[z7,z2,z108,z3,z4,z10,z6]),(1,[z7,z2,z321,z4,z67,z6]),(0,[z7,z2,z3,z4,z5,z6,z178])]],
   [[(0,[z0,z7,z2,z3,z4,z9,z6]),(0,[z1,z7,z2,z3,z4,z9,z6]),(0,[z102,z7,z2,z3,z4,z10,z6]),(0,[z42,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z677,z6]),(0,[z7,z299,z2,z3,z4,z5,z75])],[(0,[z7,z2,z365,z3,z5,z6,z56]),(0,[z7,z2,z3,z4,z9,z6,z76]),(0,[z7,z2,z678,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z679,z5,z6])],[(0,[z7,z2,z680,z3,z4,z5,z6]),(0,[z7,z118,z2,z3,z4,z10,z6]),(0,[z12,z7,z334,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z409,z6]),(0,[z7,z2,z47,z3,z4,z9,z6])],[(0,[z7,z2,z3,z4,z5,z6,z681]),(0,[z7,z2,z3,z58,z5,z59,z6]),(0,[z7,z2,z113,z3,z4,z5,z75]),(0,[z7,z2,z3,z136,z4,z5,z75]),(0,[z7,z682,z2,z3,z4,z5,z6])],[(0,[z304,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z683,z3,z4,z5,z6])],[(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z97,z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z684,z3,z4,z5,z6])],[(0,[z7,z2,z685,z3,z4,z5,z6]),(0,[z7,z686,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z63,z6]),(0,[z22,z7,z2,z113,z3,z4,z5]),(0,[z687,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z678,z3,z4,z5,z6]),(0,[z7,z2,z3,z688,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z689,z6]),(0,[z7,z2,z86,z3,z4,z5,z6]),(0,[z7,z106,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z19,z9,z6]),(0,[z7,z2,z3,z4,z5,z76,z74]),(0,[z7,z2,z3,z4,z5,z6,z74]),(0,[z7,z2,z3,z690,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z691])]],
   [[(0,[z692,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z693,z4,z5,z6]),(0,[z7,z2,z3,z92,z4,z5,z6])],[(0,[z7,z2,z4,z18,z5,z6,z74]),(0,[z7,z2,z294,z3,z4,z5,z137])],[(0,[z7,z2,z3,z4,z5,z6,z694]),(0,[z97,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z695,z5,z6]),(0,[z7,z2,z113,z3,z58,z5,z6]),(0,[z7,z2,z3,z4,z696,z5,z6])],[(0,[z221,z7,z2,z3,z4,z10,z6]),(1,[z14,z7,z144,z4,z5,z6]),(0,[z7,z2,z108,z43,z4,z5,z6]),(0,[z697,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z698,z5,z6]),(0,[z699,z7,z2,z3,z4,z5,z6])],[(0,[z7,z700,z2,z3,z4,z5,z6]),(0,[z7,z106,z2,z3,z4,z5,z6])],[(0,[z7,z2,z112,z3,z4,z5,z6]),(0,[z701,z7,z2,z3,z4,z5,z6]),(0,[z7,z98,z3,z4,z58,z5,z6]),(0,[z7,z2,z3,z4,z5,z75,z6]),(0,[z7,z2,z702,z3,z4,z5,z6]),(1,[z7,z2,z209,z18,z5,z6]),(0,[z7,z2,z3,z136,z5,z59,z6])],[(1,[z182,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z703,z4,z5,z6]),(0,[z7,z2,z113,z3,z43,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z704]),(0,[z7,z2,z3,z92,z19,z5,z6])],[(0,[z705,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z706,z3,z4,z5,z6]),(0,[z7,z2,z78,z3,z4,z355,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z2,z3,z4,z707,z6]),(0,[z7,z2,z3,z4,z708,z6]),(0,[z7,z2,z3,z709,z5,z6]),(0,[z7,z2,z3,z4,z710,z6]),(0,[z7,z98,z3,z58,z5,z6]),(0,[z7,z2,z3,z194,z5,z48])],[(0,[z7,z2,z139,z4,z9,z6]),(0,[z26,z143,z3,z4,z510,z6]),(0,[z182,z2,z3,z4,z5,z229]),(0,[z7,z2,z239,z4,z5,z75])],[(0,[z7,z2,z78,z79,z5,z137]),(0,[z7,z2,z3,z4,z169,z711])],[(0,[z7,z2,z712,z3,z5,z6])],[(0,[z7,z2,z3,z27,z510,z6]),(0,[z2,z112,z713,z4,z5,z6]),(0,[z7,z2,z3,z152,z4,z5]),(0,[z102,z2,z3,z5,z161,z6]),(0,[z14,z7,z144,z93,z5,z6]),(0,[z7,z2,z3,z4,z714,z6]),(0,[z7,z237,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z13,z74])],[(0,[z147,z7,z2,z4,z9,z6]),(0,[z7,z2,z113,z3,z197,z5]),(0,[z7,z2,z715,z3,z4,z6]),(0,[z7,z2,z4,z9,z716,z6]),(0,[z7,z2,z40,z3,z4,z667]),(0,[z7,z2,z3,z4,z717,z6])],[(0,[z7,z2,z139,z4,z5,z6]),(0,[z7,z2,z3,z4,z438,z6]),(0,[z7,z2,z3,z4,z5,z718]),(0,[z7,z3,z4,z719,z10,z6]),(0,[z7,z2,z3,z720,z9,z6]),(0,[z7,z2,z3,z4,z9,z288]),(0,[z7,z2,z586,z3,z9,z6]),(0,[z7,z2,z3,z79,z355,z6])],[(0,[z7,z2,z3,z4,z5,z82]),(0,[z7,z2,z3,z4,z5,z721]),(0,[z7,z2,z3,z4,z722,z6]),(0,[z97,z2,z3,z4,z723,z6]),(0,[z182,z2,z3,z93,z5,z6]),(0,[z7,z2,z3,z4,z331,z172]),(0,[z7,z2,z3,z4,z724,z6]),(0,[z7,z2,z138,z3,z222,z6])]],
   [[(0,[z7,z2,z3,z725,z5,z6])],[(0,[z72,z2,z3,z29,z9,z6]),(0,[z7,z2,z339,z4,z5,z137]),(0,[z7,z2,z3,z4,z726,z6]),(0,[z7,z2,z108,z43,z9,z6]),(0,[z7,z2,z211,z3,z4,z9])],[(0,[z7,z2,z459,z4,z510,z6]),(0,[z26,z143,z3,z27,z5,z6]),(0,[z147,z7,z2,z4,z5,z6]),(0,[z182,z2,z3,z325,z5,z6]),(0,[z7,z2,z3,z400,z19,z6]),(0,[z7,z2,z47,z4,z727,z6])],[(0,[z0,z2,z129,z4,z9,z6]),(0,[z7,z2,z3,z728,z5,z6]),(0,[z7,z2,z3,z4,z169,z248]),(0,[z7,z2,z3,z4,z727,z6]),(0,[z7,z2,z586,z3,z5,z6])],[(0,[z7,z2,z3,z729,z5,z6]),(0,[z7,z264,z3,z4,z10,z6]),(0,[z72,z2,z3,z28,z29,z6]),(0,[z7,z2,z730,z3,z4,z6])],[(0,[z7,z2,z3,z4,z731,z6]),(0,[z7,z2,z732,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z733]),(0,[z7,z2,z734,z3,z4,z6]),(0,[z7,z2,z239,z4,z9,z6]),(0,[z7,z2,z138,z3,z109,z6])],[(0,[z7,z62,z112,z4,z5,z6]),(0,[z72,z2,z3,z29,z5,z6]),(0,[z7,z2,z3,z4,z735,z6]),(0,[z7,z2,z3,z4,z6,z736])],[(0,[z7,z2,z3,z4,z5,z737]),(0,[z2,z713,z129,z4,z5,z6]),(0,[z42,z2,z3,z4,z226,z6]),(0,[z7,z2,z3,z4,z5,z738]),(0,[z7,z2,z3,z79,z5,z137])]],
   [[(0,[z148,z69,z3,z4,z5,z6]),(0,[z26,z143,z459,z4,z5,z6]),(0,[z0,z2,z129,z4,z5,z6]),(0,[z7,z2,z3,z4,z739,z6])],[(0,[z2,z3,z713,z4,z5,z6]),(0,[z7,z2,z3,z4,z740,z6]),(0,[z7,z2,z3,z4,z741,z6]),(0,[z7,z2,z3,z4,z742,z6]),(0,[z7,z2,z3,z4,z743,z6]),(0,[z7,z2,z3,z4,z6,z529])],[(0,[z7,z2,z3,z4,z744,z6]),(0,[z7,z2,z745,z3,z5,z6]),(0,[z7,z3,z746,z58,z5,z6]),(0,[z7,z2,z436,z43,z5,z6]),(0,[z7,z2,z78,z4,z5,z243])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z459,z27,z5,z6]),(0,[z7,z2,z3,z4,z5,z747]),(0,[z7,z2,z3,z4,z748,z6]),(0,[z7,z299,z3,z4,z10,z76])],[(0,[z7,z2,z749,z3,z4,z9]),(0,[z7,z2,z78,z151,z5,z137])],[(0,[z7,z2,z3,z4,z750,z6]),(0,[z7,z2,z3,z4,z751,z6])],[(0,[z7,z2,z3,z437,z5,z171]),(0,[z7,z2,z3,z4,z5,z752])],[(0,[z7,z2,z4,z753,z10,z6]),(0,[z7,z106,z3,z4,z5,z754]),(0,[z7,z2,z3,z755,z5,z6]),(0,[z7,z2,z47,z194,z154,z6])]],
   [[(0,[z7,z98,z3,z58,z10,z6]),(0,[z7,z106,z3,z4,z5,z75]),(0,[z7,z2,z3,z194,z154,z6])],[(0,[z7,z2,z756,z3,z4,z6]),(0,[z14,z7,z144,z4,z5,z172]),(0,[z7,z2,z3,z4,z757,z6]),(0,[z7,z758,z3,z4,z5,z6]),(0,[z7,z2,z138,z239,z5,z6])],[(0,[z7,z2,z3,z4,z5,z759]),(0,[z7,z530,z3,z4,z10,z6]),(0,[z504,z7,z3,z4,z9,z6]),(0,[z7,z2,z81,z43,z5,z6]),(0,[z7,z2,z232,z4,z67,z6])],[(0,[z7,z2,z3,z437,z5,z181]),(0,[z7,z2,z3,z4,z5,z760]),(0,[z7,z2,z3,z4,z5,z761])],[(0,[z7,z2,z3,z762,z4,z6]),(0,[z2,z3,z4,z5,z6,z763]),(0,[z182,z2,z3,z4,z5,z172]),(0,[z7,z2,z47,z4,z193,z6]),(0,[z7,z2,z3,z4,z764,z6])],[(0,[z7,z2,z765,z4,z5,z6]),(0,[z7,z2,z3,z766,z4,z6]),(0,[z102,z2,z3,z767,z5,z6]),(0,[z7,z768,z3,z4,z5,z6]),(0,[z14,z7,z144,z4,z9,z6]),(0,[z7,z3,z218,z4,z10,z6]),(0,[z7,z299,z3,z4,z309,z76])],[(0,[z7,z2,z139,z4,z10,z6]),(0,[z7,z2,z769,z4,z5,z6]),(0,[z7,z2,z3,z4,z770,z6]),(0,[z7,z2,z3,z771,z5,z6]),(0,[z7,z2,z113,z3,z5,z645]),(0,[z7,z2,z3,z5,z6,z772])],[(0,[z7,z2,z3,z4,z10,z82]),(0,[z7,z2,z3,z4,z773,z6]),(0,[z7,z2,z3,z4,z5,z774]),(0,[z7,z2,z209,z18,z9,z6]),(0,[z7,z2,z3,z4,z5,z243])]],
   [[(0,[z7,z2,z3,z775,z5,z6]),(0,[z7,z2,z253,z3,z63,z6]),(0,[z182,z2,z3,z4,z9,z6]),(1,[z7,z2,z211,z138,z3])],[(0,[z7,z2,z776,z4,z5,z6]),(0,[z7,z2,z253,z3,z4,z6]),(0,[z7,z3,z238,z4,z10,z6]),(0,[z7,z2,z3,z4,z777,z6]),(0,[z7,z2,z24,z3,z59,z6])],[(0,[z147,z7,z2,z4,z10,z6]),(0,[z0,z38,z129,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z778])],[(1,[z143,z459,z4,z5,z6]),(0,[z7,z2,z3,z4,z779,z6]),(0,[z7,z2,z140,z3,z43,z5]),(0,[z7,z2,z3,z780,z5,z6]),(0,[z7,z3,z4,z10,z146,z6]),(0,[z7,z2,z586,z3,z10,z6]),(0,[z7,z2,z3,z4,z9,z20])],[(0,[z7,z2,z781,z3,z4,z5]),(0,[z7,z2,z209,z18,z5,z6]),(0,[z7,z2,z3,z4,z782,z6]),(0,[z7,z2,z3,z4,z783,z6]),(1,[z7,z2,z40,z586,z3])],[(0,[z7,z38,z3,z4,z5,z6]),(0,[z7,z2,z784,z4,z5,z6]),(0,[z7,z2,z3,z4,z156,z11]),(0,[z7,z2,z113,z3,z5,z177])],[(0,[z7,z2,z785,z4,z5,z6]),(0,[z72,z2,z3,z29,z10,z6]),(0,[z7,z2,z287,z3,z18,z6]),(0,[z7,z2,z3,z28,z152,z4]),(0,[z7,z2,z3,z4,z786,z6]),(0,[z7,z2,z3,z4,z787,z6])],[(0,[z7,z2,z3,z788,z5,z6]),(0,[z165,z2,z129,z4,z5,z6]),(0,[z7,z479,z3,z17,z5,z6]),(0,[z7,z2,z3,z4,z230,z248]),(0,[z7,z2,z3,z9,z6,z178]),(0,[z7,z2,z3,z4,z5,z789]),(0,[z7,z2,z3,z4,z13,z6])]],
   [[(0,[z148,z69,z3,z4,z10,z6]),(0,[z0,z2,z129,z4,z10,z6]),(0,[z7,z2,z3,z790,z5,z6]),(0,[z7,z2,z116,z18,z5,z6]),(0,[z7,z2,z108,z43,z180,z6]),(0,[z7,z2,z40,z3,z4,z77])],[(0,[z7,z2,z3,z4,z5,z791]),(0,[z7,z2,z3,z792,z5,z6]),(0,[z7,z2,z3,z4,z5,z793]),(0,[z7,z2,z3,z794,z5,z6])],[(0,[z2,z3,z4,z39,z723,z6]),(0,[z7,z2,z795,z3,z4,z6]),(0,[z7,z2,z3,z4,z796,z6]),(0,[z7,z2,z113,z81,z5,z68]),(0,[z7,z2,z3,z4,z711,z41])],[(0,[z7,z2,z3,z4,z10,z6]),(1,[z182,z144,z4,z5,z6]),(0,[z7,z3,z17,z746,z5,z6]),(0,[z7,z2,z3,z4,z6,z797]),(0,[z12,z7,z3,z4,z9,z6]),(0,[z7,z2,z211,z138,z3,z109]),(0,[z7,z2,z3,z4,z798,z6])],[(0,[z7,z2,z139,z4,z5,z315]),(0,[z7,z2,z287,z3,z4,z6]),(0,[z7,z2,z3,z5,z6,z799]),(0,[z7,z2,z3,z4,z5,z800])],[(0,[z7,z2,z3,z4,z801,z6]),(0,[z7,z2,z802,z4,z5,z6]),(0,[z7,z2,z3,z27,z378,z6]),(0,[z7,z2,z4,z5,z716,z6]),(0,[z7,z62,z3,z4,z9,z6]),(0,[z7,z299,z3,z4,z5,z754]),(0,[z7,z2,z3,z4,z5,z37])],[(0,[z72,z2,z140,z3,z29,z5]),(0,[z7,z2,z3,z9,z63,z6]),(0,[z7,z2,z108,z43,z236,z6])],[(0,[z7,z2,z3,z93,z5,z172]),(0,[z7,z2,z3,z803,z5,z6]),(0,[z7,z2,z3,z4,z331,z229]),(0,[z7,z2,z3,z4,z46,z6]),(0,[z7,z2,z3,z4,z45,z6]),(0,[z7,z2,z804,z4,z9,z6]),(0,[z7,z2,z3,z4,z805,z6])]],
   [[(0,[z102,z7,z2,z140,z3,z5]),(0,[z7,z2,z806,z3,z4,z6]),(0,[z7,z2,z3,z4,z807,z6]),(0,[z7,z2,z3,z808,z4,z5]),(0,[z7,z106,z3,z4,z10,z75]),(0,[z7,z2,z294,z4,z5,z74]),(0,[z7,z2,z3,z4,z5,z809])],[(0,[z7,z2,z3,z4,z11,z424])],[(0,[z7,z62,z3,z4,z5,z6]),(0,[z544,z2,z129,z4,z5,z6]),(0,[z308,z2,z3,z4,z331,z6]),(0,[z7,z2,z810,z4,z5,z6]),(0,[z7,z2,z3,z300,z5,z6]),(0,[z7,z2,z3,z4,z5,z811])],[(0,[z7,z2,z3,z4,z812,z6]),(0,[z7,z2,z3,z152,z4,z10]),(0,[z221,z7,z2,z365,z3,z5]),(0,[z7,z2,z3,z93,z9,z6]),(0,[z7,z2,z3,z4,z5,z813])],[(0,[z7,z2,z3,z4,z814,z6]),(0,[z7,z2,z3,z815,z5,z6]),(0,[z7,z106,z3,z4,z45,z75]),(0,[z7,z106,z3,z4,z46,z75]),(0,[z7,z2,z3,z4,z816,z6])],[(0,[z7,z2,z3,z4,z5,z817]),(0,[z7,z3,z4,z5,z6,z818]),(0,[z7,z2,z3,z4,z5,z819]),(0,[z7,z2,z3,z55,z63,z6]),(0,[z7,z2,z3,z820,z5,z6]),(0,[z7,z2,z3,z4,z309,z6]),(0,[z7,z2,z765,z4,z10,z6])],[(0,[z7,z2,z821,z4,z9,z6])],[(0,[z7,z2,z3,z4,z822,z6]),(0,[z7,z2,z3,z170,z438,z6]),(0,[z7,z2,z3,z4,z438,z171]),(0,[z7,z2,z3,z4,z10,z243]),(0,[z7,z2,z3,z4,z823,z6]),(0,[z7,z2,z81,z4,z5,z137]),(0,[z7,z824,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z112,z4,z9,z6]),(0,[z7,z825,z3,z4,z5,z6]),(0,[z7,z2,z3,z5,z826,z6]),(0,[z7,z2,z3,z93,z5,z6]),(0,[z7,z2,z3,z325,z331,z6]),(0,[z7,z2,z3,z194,z67,z6])],[(0,[z7,z2,z3,z4,z5,z315]),(0,[z147,z7,z144,z4,z5,z6]),(0,[z458,z7,z144,z4,z5,z6]),(0,[z7,z2,z3,z318,z5,z6])],[(0,[z7,z2,z827,z3,z5,z6]),(0,[z7,z2,z3,z4,z828,z6]),(0,[z14,z7,z144,z4,z10,z6]),(0,[z7,z299,z3,z4,z65,z76]),(0,[z7,z2,z3,z5,z59,z585])],[(0,[z7,z2,z3,z4,z829,z6]),(0,[z102,z2,z3,z124,z9,z6]),(0,[z7,z2,z830,z3,z4,z6])],[(0,[z7,z2,z3,z4,z831,z6]),(0,[z7,z2,z3,z4,z438,z181]),(0,[z7,z2,z832,z3,z4,z6]),(0,[z7,z2,z3,z4,z833,z6]),(0,[z7,z2,z209,z18,z10,z6]),(0,[z7,z2,z81,z79,z5,z6])],[(0,[z26,z143,z139,z4,z5,z6]),(0,[z1,z62,z3,z4,z5,z6]),(0,[z7,z38,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z834,z6]),(0,[z7,z2,z78,z4,z5,z835])],[(0,[z7,z2,z836,z3,z5,z6]),(0,[z7,z2,z3,z4,z837,z6]),(0,[z458,z7,z3,z4,z10,z6]),(0,[z7,z317,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z838,z6]),(0,[z304,z2,z3,z4,z176,z6]),(0,[z7,z106,z3,z318,z5,z75])],[(0,[z7,z2,z3,z839,z5,z6]),(0,[z7,z327,z3,z4,z10,z6]),(0,[z840,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z788,z10,z6]),(0,[z361,z2,z3,z4,z35,z6]),(0,[z7,z2,z321,z4,z727,z6]),(0,[z7,z2,z3,z4,z841,z6]),(0,[z7,z2,z40,z3,z4,z162]),(0,[z7,z2,z239,z4,z169,z5])]],
   [[(0,[z102,z2,z3,z124,z5,z6]),(0,[z842,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z843,z6]),(0,[z7,z2,z473,z4,z234,z6]),(0,[z7,z2,z3,z136,z5,z202])],[(0,[z7,z2,z3,z4,z844,z6]),(0,[z0,z2,z129,z4,z5,z171]),(0,[z7,z2,z3,z4,z845,z6]),(0,[z14,z7,z144,z4,z5,z229]),(0,[z14,z7,z846,z4,z5,z6]),(0,[z7,z2,z113,z3,z5,z21]),(0,[z7,z2,z138,z3,z391,z6])],[(0,[z7,z2,z139,z84,z5,z6]),(0,[z7,z2,z847,z4,z5,z6]),(0,[z7,z2,z3,z4,z848,z6]),(1,[z62,z129,z4,z5,z6]),(1,[z2,z713,z4,z5,z6]),(0,[z7,z2,z3,z4,z849,z6]),(0,[z850,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z851,z5,z6]),(0,[z7,z2,z3,z4,z5,z852]),(0,[z7,z2,z3,z4,z180,z20])],[(0,[z7,z2,z3,z853,z5,z6]),(0,[z7,z2,z3,z4,z5,z854]),(0,[z7,z2,z3,z84,z5,z82]),(1,[z2,z3,z767,z5,z6]),(0,[z7,z2,z3,z4,z5,z855]),(0,[z7,z2,z3,z4,z856,z6]),(0,[z12,z7,z3,z4,z719,z6]),(0,[z7,z2,z40,z3,z4,z177]),(0,[z7,z2,z81,z4,z857,z6])],[(0,[z335,z7,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z171]),(0,[z647,z2,z3,z124,z5,z6]),(0,[z540,z2,z3,z124,z5,z6]),(0,[z182,z2,z15,z4,z5,z6]),(0,[z7,z2,z3,z4,z858,z6]),(0,[z7,z2,z3,z4,z5,z754])],[(0,[z7,z2,z3,z4,z9,z82]),(0,[z7,z2,z3,z4,z859,z6]),(0,[z7,z2,z3,z4,z860,z6]),(0,[z7,z2,z3,z4,z5,z861]),(0,[z7,z2,z3,z4,z10,z37])],[(0,[z7,z2,z3,z862,z5,z6]),(0,[z7,z2,z3,z4,z863,z6]),(0,[z0,z2,z129,z4,z5,z181]),(0,[z182,z118,z3,z4,z5,z6]),(0,[z7,z2,z3,z10,z6,z864]),(1,[z7,z2,z4,z727,z6])],[(0,[z7,z2,z3,z865,z5,z6]),(0,[z7,z2,z3,z4,z866,z6]),(0,[z7,z2,z113,z3,z9,z68]),(0,[z7,z2,z867,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z868,z6]),(0,[z7,z2,z365,z3,z5,z76]),(0,[z7,z670,z3,z4,z5,z75]),(0,[z7,z2,z3,z4,z9,z172]),(0,[z7,z2,z3,z4,z236,z20]),(0,[z7,z2,z3,z869,z5,z6])],[],[(0,[z1,z2,z192,z4,z5,z6]),(0,[z7,z62,z3,z4,z10,z6]),(0,[z7,z2,z870,z3,z4,z6]),(0,[z14,z7,z144,z325,z5,z6]),(0,[z7,z2,z3,z300,z10,z6]),(0,[z7,z2,z254,z3,z468,z6]),(0,[z7,z2,z3,z4,z5,z835]),(0,[z7,z2,z211,z3,z92,z4])],[(0,[z7,z2,z871,z3,z4,z6]),(0,[z7,z2,z872,z3,z4,z6]),(0,[z2,z3,z767,z29,z5,z6]),(0,[z873,z2,z3,z4,z5,z6]),(0,[z874,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z875,z6]),(0,[z7,z2,z239,z58,z5,z6]),(0,[z7,z2,z876,z3,z4,z10]),(0,[z7,z2,z3,z877,z5,z6])],[(0,[z62,z3,z129,z4,z5,z6]),(0,[z7,z2,z3,z878,z5,z6]),(0,[z7,z2,z4,z727,z5,z6]),(0,[z7,z2,z3,z300,z5,z37]),(0,[z7,z2,z3,z5,z6,z879]),(0,[z7,z2,z3,z92,z19,z6]),(0,[z7,z2,z113,z3,z5,z68]),(1,[z7,z2,z3,z5,z811]),(0,[z7,z2,z3,z4,z169,z11])],[(0,[z7,z2,z3,z4,z880,z6]),(0,[z221,z2,z3,z4,z5,z763]),(0,[z7,z2,z3,z4,z5,z172]),(0,[z7,z2,z408,z4,z193,z6]),(0,[z7,z2,z311,z4,z154,z6])],[(0,[z148,z69,z3,z4,z9,z6]),(0,[z7,z2,z3,z881,z5,z6]),(0,[z7,z2,z3,z882,z5,z6]),(0,[z7,z2,z3,z5,z59,z621]),(0,[z7,z3,z846,z4,z5,z6]),(0,[z7,z2,z3,z4,z883,z6])],[(0,[z7,z2,z3,z84,z5,z6]),(0,[z7,z2,z3,z4,z5,z884]),(0,[z7,z885,z3,z4,z5,z6]),(0,[z7,z2,z306,z18,z5,z6]),(0,[z7,z2,z3,z4,z886,z6]),(0,[z7,z2,z113,z3,z5,z310]),(0,[z7,z2,z40,z3,z4,z64]),(0,[z7,z2,z3,z4,z887,z6]),(0,[z7,z2,z3,z5,z6,z178]),(0,[z7,z2,z81,z4,z888,z6]),(0,[z7,z2,z3,z4,z11,z711])]],
   [[(0,[z7,z889,z3,z4,z5,z6]),(0,[z7,z2,z3,z93,z10,z6]),(0,[z7,z2,z3,z890,z5,z6]),(0,[z7,z447,z3,z4,z9,z6]),(0,[z7,z2,z3,z235,z5,z76])],[(0,[z7,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z10,z315]),(0,[z7,z2,z3,z4,z5,z891]),(0,[z7,z2,z3,z4,z5,z892]),(0,[z7,z2,z3,z235,z5,z6]),(0,[z7,z2,z3,z318,z10,z6]),(0,[z7,z2,z3,z893,z5,z6])],[(0,[z7,z2,z4,z894,z5,z6]),(0,[z7,z2,z3,z4,z895,z6]),(0,[z7,z2,z827,z3,z10,z6]),(0,[z7,z2,z3,z4,z65,z6]),(0,[z7,z2,z113,z3,z608,z5])],[(0,[z7,z2,z3,z4,z896,z6]),(0,[z7,z897,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z898,z6]),(0,[z7,z2,z3,z4,z5,z899])],[(0,[z7,z2,z3,z437,z155,z6]),(0,[z7,z2,z3,z4,z900,z6]),(0,[z7,z2,z901,z3,z4,z5]),(0,[z7,z2,z3,z4,z9,z145]),(0,[z7,z2,z3,z4,z902,z6])],[(0,[z1,z2,z112,z4,z10,z6]),(0,[z7,z2,z3,z903,z5,z6]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z318,z45,z6]),(0,[z7,z2,z3,z318,z46,z6]),(0,[z7,z2,z905,z3,z4,z5])],[(0,[z7,z62,z3,z4,z906,z6]),(0,[z7,z38,z3,z4,z5,z171]),(0,[z7,z2,z3,z5,z63,z6]),(0,[z2,z3,z4,z723,z226,z6]),(0,[z7,z106,z3,z4,z9,z75]),(0,[z7,z106,z3,z235,z5,z75]),(0,[z7,z2,z3,z206,z5,z59])],[(0,[z7,z2,z3,z93,z5,z229]),(0,[z7,z2,z3,z4,z907,z6]),(0,[z7,z2,z321,z4,z556,z6])]],
   [[(0,[z7,z2,z3,z908,z5,z6]),(0,[z102,z2,z3,z124,z10,z6]),(0,[z7,z2,z3,z4,z6,z909]),(0,[z7,z2,z113,z3,z5,z121])],[(0,[z7,z2,z3,z4,z910,z6]),(0,[z7,z2,z3,z4,z911,z6]),(0,[z7,z912,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z913,z6]),(0,[z14,z7,z144,z4,z127,z6]),(0,[z7,z2,z3,z4,z5,z145]),(0,[z7,z2,z3,z4,z156,z283]),(0,[z7,z2,z3,z4,z914,z6])],[(0,[z7,z2,z3,z4,z5,z915]),(0,[z7,z2,z3,z4,z916,z6]),(0,[z7,z917,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z918,z6]),(0,[z7,z2,z3,z4,z5,z919]),(0,[z308,z2,z3,z93,z5,z6]),(0,[z7,z2,z3,z4,z920,z6]),(0,[z7,z2,z4,z5,z6,z835]),(0,[z7,z2,z138,z3,z921,z6])],[(0,[z542,z2,z3,z4,z5,z56]),(0,[z7,z2,z3,z922,z5,z6]),(0,[z7,z334,z3,z4,z10,z6]),(0,[z7,z2,z3,z151,z355,z6]),(0,[z7,z2,z113,z3,z507,z5])],[(0,[z458,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z171]),(0,[z7,z2,z923,z4,z5,z6]),(0,[z182,z2,z3,z4,z127,z6]),(0,[z7,z2,z3,z43,z5,z243]),(0,[z7,z2,z3,z924,z5,z6])],[(0,[z7,z2,z3,z4,z925,z6]),(0,[z7,z2,z3,z4,z9,z243]),(0,[z7,z2,z3,z4,z5,z926])],[(0,[z7,z62,z3,z4,z155,z6]),(0,[z7,z927,z3,z4,z5,z6]),(0,[z7,z2,z928,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z929])],[(0,[z7,z2,z3,z4,z930,z6]),(0,[z7,z2,z3,z4,z5,z931]),(0,[z7,z2,z3,z4,z932,z6]),(0,[z7,z2,z3,z4,z6,z933]),(0,[z7,z2,z40,z3,z178,z41])]],
   [[(0,[z7,z2,z139,z4,z378,z6]),(0,[z7,z2,z4,z5,z934,z6]),(0,[z7,z2,z3,z935,z5,z6]),(0,[z7,z2,z78,z4,z5,z137]),(0,[z7,z2,z3,z4,z936,z6])],[(0,[z7,z2,z3,z4,z378,z82]),(0,[z7,z2,z937,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z418]),(0,[z7,z2,z209,z938,z5,z6])],[(0,[z7,z2,z3,z939,z5,z6]),(0,[z7,z2,z3,z940,z5,z6]),(0,[z7,z2,z3,z941,z5,z6]),(0,[z7,z2,z3,z453,z83,z6]),(0,[z7,z2,z3,z4,z9,z48])],[(0,[z942,z143,z3,z4,z5,z6]),(0,[z7,z62,z3,z170,z5,z6]),(0,[z7,z62,z3,z4,z5,z171]),(0,[z7,z38,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z943]),(0,[z221,z2,z253,z3,z4,z56]),(0,[z7,z2,z3,z944,z5,z6]),(0,[z7,z416,z3,z4,z10,z6])],[(0,[z7,z2,z3,z4,z945,z6]),(0,[z7,z2,z113,z3,z10,z68]),(0,[z7,z2,z211,z3,z4,z5]),(0,[z7,z2,z946,z3,z4,z6])],[(0,[z7,z2,z3,z4,z10,z172]),(0,[z7,z479,z3,z4,z10,z6])],[(0,[z7,z2,z3,z4,z947,z6]),(0,[z7,z2,z948,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z949]),(0,[z7,z2,z3,z92,z625,z6]),(0,[z7,z2,z3,z4,z169,z132])],[(0,[z7,z2,z950,z4,z5,z6]),(0,[z147,z7,z2,z951,z5,z6]),(0,[z7,z2,z3,z136,z103,z5]),(0,[z7,z2,z3,z4,z952,z6]),(0,[z7,z2,z953,z3,z5,z6]),(0,[z7,z2,z3,z4,z5,z48])]],
   [[(0,[z7,z62,z3,z4,z5,z181]),(0,[z7,z954,z2,z4,z5,z6])],[(0,[z7,z2,z955,z3,z4,z5]),(0,[z7,z2,z365,z3,z5,z74]),(0,[z7,z2,z3,z4,z719,z6]),(0,[z7,z2,z3,z235,z10,z6])],[(0,[z7,z2,z3,z28,z4,z6]),(0,[z7,z2,z3,z4,z956,z6]),(0,[z957,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z958]),(0,[z7,z3,z4,z10,z364,z6]),(0,[z7,z2,z138,z3,z495,z6])],[(0,[z7,z2,z3,z4,z959,z6]),(0,[z7,z2,z3,z4,z960,z6]),(0,[z7,z2,z3,z4,z9,z37]),(0,[z7,z2,z3,z4,z961,z6]),(0,[z7,z2,z3,z262,z19,z6])],[(0,[z147,z7,z118,z4,z5,z6]),(0,[z7,z2,z3,z4,z962,z6]),(0,[z7,z963,z3,z4,z5,z6]),(0,[z7,z2,z113,z3,z5,z186]),(0,[z7,z2,z3,z964,z5,z6])],[(0,[z7,z2,z3,z4,z378,z6]),(0,[z7,z2,z3,z4,z965,z6]),(0,[z72,z2,z87,z3,z5,z6]),(0,[z7,z2,z3,z4,z966,z6]),(0,[z7,z2,z967,z4,z5,z6]),(0,[z7,z2,z3,z235,z45,z6]),(0,[z7,z2,z3,z235,z46,z6])],[(0,[z7,z2,z968,z3,z4,z6]),(0,[z7,z2,z3,z5,z969,z6]),(0,[z7,z2,z3,z4,z5,z970]),(0,[z7,z2,z3,z4,z971,z6]),(0,[z7,z2,z294,z4,z9,z74]),(0,[z7,z2,z113,z18,z5,z74])],[(0,[z2,z143,z459,z4,z5,z6]),(0,[z308,z2,z3,z4,z5,z172]),(0,[z7,z2,z3,z4,z5,z972]),(0,[z7,z2,z973,z4,z5,z6]),(0,[z7,z2,z749,z3,z4,z5]),(0,[z7,z2,z3,z4,z974,z6]),(0,[z7,z2,z3,z921,z109,z6])]],
   [[(0,[z147,z7,z2,z4,z975,z6]),(0,[z7,z2,z3,z951,z5,z6]),(0,[z7,z2,z3,z976,z5,z6]),(0,[z7,z2,z3,z4,z9,z229]),(0,[z7,z2,z3,z300,z9,z6]),(0,[z7,z2,z3,z4,z180,z6]),(0,[z7,z2,z138,z3,z505,z6])],[(0,[z198,z7,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z10,z145])],[(0,[z7,z118,z62,z4,z5,z6]),(0,[z7,z977,z3,z4,z5,z6]),(0,[z97,z2,z3,z4,z39,z6]),(0,[z7,z2,z3,z4,z5,z978]),(0,[z7,z2,z979,z4,z5,z6]),(0,[z7,z2,z40,z239,z4,z5])],[(0,[z308,z2,z3,z4,z9,z6]),(0,[z7,z2,z3,z980,z5,z6]),(0,[z7,z2,z3,z4,z981,z6]),(0,[z7,z2,z982,z4,z5,z6]),(0,[z7,z2,z983,z4,z9,z6]),(0,[z7,z522,z3,z4,z9,z6]),(0,[z249,z7,z2,z113,z3,z5])],[(0,[z7,z2,z140,z3,z4,z9]),(0,[z7,z2,z4,z5,z243,z74]),(0,[z7,z2,z3,z136,z5,z506]),(0,[z7,z2,z78,z4,z13,z137]),(0,[z7,z2,z431,z4,z5,z137]),(0,[z7,z2,z984,z3,z4,z6])],[(0,[z7,z2,z3,z84,z5,z315]),(0,[z143,z129,z144,z4,z5,z6]),(0,[z7,z3,z4,z985,z5,z6]),(0,[z361,z2,z3,z4,z39,z6]),(0,[z7,z2,z3,z4,z5,z229]),(0,[z7,z2,z3,z325,z5,z172]),(0,[z7,z2,z3,z4,z5,z986]),(0,[z7,z2,z987,z3,z5,z6]),(0,[z988,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z989]),(1,[z2,z3,z4,z723,z6]),(0,[z7,z259,z3,z17,z9,z6]),(0,[z7,z2,z3,z4,z236,z6]),(0,[z7,z2,z3,z92,z6,z279]),(0,[z990,z7,z2,z3,z4,z6])],[(0,[z7,z2,z3,z4,z9,z315]),(0,[z7,z2,z991,z3,z4,z5]),(0,[z72,z2,z3,z767,z5,z6]),(0,[z7,z2,z3,z4,z992,z6]),(0,[z7,z2,z3,z318,z9,z6]),(0,[z7,z2,z3,z993,z5,z6]),(0,[z7,z2,z4,z5,z137,z835])]],
   [[(0,[z308,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z994,z6]),(0,[z7,z2,z3,z4,z995,z6]),(0,[z7,z2,z983,z4,z5,z6]),(0,[z7,z2,z3,z935,z10,z6]),(0,[z7,z2,z78,z4,z10,z137]),(0,[z7,z2,z3,z18,z5,z243]),(0,[z7,z2,z211,z138,z3,z4])],[(0,[z7,z62,z3,z4,z916,z6]),(0,[z7,z996,z2,z4,z5,z6]),(0,[z7,z2,z997,z3,z4,z6]),(0,[z7,z2,z3,z325,z9,z6]),(0,[z7,z2,z3,z92,z921,z6]),(0,[z7,z2,z113,z3,z5,z811])],[(0,[z7,z2,z139,z4,z510,z6]),(0,[z7,z2,z3,z4,z5,z998]),(0,[z7,z2,z3,z4,z906,z6]),(0,[z7,z2,z3,z4,z999,z6])],[(0,[z7,z2,z3,z4,z510,z82]),(0,[z7,z2,z3,z4,z1000,z6]),(0,[z7,z2,z253,z3,z4,z137]),(0,[z7,z259,z3,z17,z5,z6]),(0,[z7,z2,z160,z18,z5,z6]),(0,[z7,z2,z474,z3,z4,z41]),(0,[z7,z2,z4,z154,z727,z6]),(0,[z7,z2,z586,z3,z169,z5])],[(0,[z7,z143,z459,z4,z5,z6]),(0,[z7,z1001,z3,z4,z5,z6]),(0,[z7,z3,z480,z4,z10,z6]),(0,[z7,z2,z1002,z3,z4,z5]),(0,[z551,z2,z3,z4,z358,z6]),(0,[z7,z2,z3,z4,z180,z243])],[(0,[z7,z2,z3,z1003,z4,z5]),(0,[z7,z2,z159,z3,z4,z64]),(0,[z7,z2,z3,z1004,z5,z6]),(0,[z7,z2,z3,z4,z5,z1005])],[(0,[z7,z2,z3,z4,z1006,z6]),(0,[z7,z2,z3,z325,z5,z6]),(0,[z7,z259,z3,z17,z5,z145]),(0,[z7,z2,z3,z17,z5,z418]),(0,[z7,z2,z47,z4,z154,z6])],[(0,[z26,z942,z3,z4,z5,z6]),(0,[z0,z2,z129,z4,z155,z6]),(0,[z7,z2,z3,z4,z1007,z6]),(0,[z7,z2,z140,z287,z3,z4]),(0,[z7,z2,z3,z4,z1008,z6]),(0,[z7,z2,z3,z4,z10,z48]),(0,[z7,z2,z938,z4,z5,z6]),(0,[z7,z2,z520,z4,z154,z6])]],
   [[(0,[z7,z2,z3,z851,z9,z6]),(0,[z7,z2,z3,z4,z9,z852])],[(0,[z26,z143,z3,z4,z5,z82]),(0,[z7,z2,z3,z4,z55,z6]),(0,[z7,z2,z3,z4,z1009,z6]),(0,[z7,z2,z3,z4,z1010,z6]),(0,[z7,z2,z3,z4,z13,z137]),(0,[z7,z2,z586,z3,z11,z6])],[(0,[z7,z2,z500,z4,z5,z6]),(0,[z7,z2,z1011,z3,z4,z6]),(0,[z7,z2,z3,z4,z155,z6]),(0,[z7,z2,z3,z170,z9,z6]),(0,[z7,z2,z3,z4,z9,z171]),(0,[z7,z2,z3,z4,z10,z958]),(0,[z7,z2,z3,z4,z236,z243]),(0,[z7,z2,z40,z3,z4,z370])],[(0,[z7,z2,z139,z27,z5,z6]),(0,[z7,z2,z3,z4,z1012,z6]),(0,[z7,z2,z3,z4,z1013,z6]),(0,[z7,z2,z3,z235,z5,z75])],[(0,[z7,z2,z3,z27,z5,z82]),(0,[z0,z2,z129,z170,z5,z6]),(0,[z7,z118,z297,z4,z5,z6]),(0,[z7,z182,z144,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1014]),(0,[z7,z2,z1015,z3,z4,z6]),(0,[z7,z2,z3,z400,z472,z6]),(1,[z7,z2,z4,z5,z835]),(0,[z7,z2,z113,z239,z5,z68])],[(0,[z7,z2,z140,z3,z18,z5]),(0,[z7,z2,z3,z300,z5,z48]),(0,[z7,z2,z431,z4,z154,z6]),(0,[z7,z2,z3,z79,z13,z6])],[(0,[z7,z2,z3,z4,z510,z6]),(0,[z7,z2,z3,z170,z5,z6]),(0,[z7,z2,z3,z4,z1016,z6]),(0,[z7,z2,z3,z4,z9,z181]),(0,[z7,z2,z365,z3,z9,z6]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z92,z83,z6]),(0,[z7,z2,z211,z3,z19,z5])]],
   [[(0,[z7,z69,z459,z4,z5,z6]),(0,[z7,z2,z1018,z4,z5,z6]),(0,[z26,z143,z3,z4,z9,z6]),(0,[z7,z2,z3,z4,z5,z1019]),(0,[z7,z2,z3,z4,z1020,z6]),(0,[z7,z2,z3,z1021,z5,z6]),(0,[z7,z2,z678,z4,z556,z6]),(0,[z7,z2,z138,z3,z468,z6]),(0,[z7,z3,z4,z5,z754,z76])],[(0,[z42,z2,z456,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z1022]),(0,[z7,z2,z3,z1023,z5,z6])],[(0,[z7,z2,z459,z4,z5,z82]),(0,[z7,z2,z3,z1024,z5,z6]),(0,[z7,z2,z294,z4,z5,z835])],[(0,[z1025,z2,z3,z4,z5,z6]),(0,[z7,z2,z294,z4,z10,z74]),(0,[z7,z2,z223,z4,z67,z6])],[(0,[z7,z2,z3,z4,z5,z181]),(0,[z7,z2,z3,z1026,z5,z6]),(0,[z7,z2,z365,z3,z5,z6]),(0,[z7,z3,z4,z9,z10,z6])],[(0,[z26,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z84,z9,z6]),(0,[z7,z2,z3,z10,z63,z6]),(0,[z14,z182,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z127,z6]),(0,[z7,z2,z3,z4,z10,z229]),(0,[z7,z2,z3,z4,z1027,z6]),(0,[z7,z2,z3,z4,z921,z6]),(0,[z7,z2,z3,z4,z1028,z6])],[(0,[z7,z2,z3,z1029,z5,z6]),(0,[z2,z62,z129,z4,z5,z6]),(0,[z7,z2,z601,z4,z67,z6]),(0,[z7,z2,z3,z4,z513,z6]),(0,[z7,z2,z3,z4,z6,z1030]),(0,[z7,z329,z3,z4,z9,z6])],[(0,[z7,z2,z140,z3,z58,z5]),(0,[z7,z2,z3,z4,z5,z1031]),(0,[z7,z2,z3,z235,z9,z6]),(0,[z7,z2,z3,z1032,z5,z6]),(0,[z7,z2,z47,z4,z154,z48]),(0,[z7,z2,z3,z5,z6,z1033])]],
   [[(0,[z7,z2,z3,z27,z5,z6]),(0,[z7,z592,z3,z4,z9,z6]),(0,[z308,z2,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z1034]),(0,[z7,z2,z3,z4,z154,z48])],[(0,[z7,z2,z3,z4,z1035,z5]),(0,[z7,z2,z3,z4,z291,z6])],[(1,[z942,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1036]),(0,[z536,z7,z2,z113,z3,z5]),(0,[z7,z2,z3,z79,z5,z74])],[(0,[z7,z2,z3,z4,z378,z315]),(0,[z7,z2,z138,z3,z303,z6]),(0,[z221,z2,z3,z4,z9,z56]),(0,[z7,z2,z3,z1037,z5,z6]),(0,[z7,z259,z3,z17,z10,z6]),(0,[z7,z2,z113,z3,z5,z312]),(0,[z7,z2,z211,z3,z4,z10]),(0,[z420,z2,z3,z4,z242,z6]),(0,[z7,z2,z1038,z3,z4,z6]),(0,[z7,z2,z520,z43,z5,z6]),(0,[z7,z2,z3,z19,z921,z6])],[(0,[z7,z38,z3,z4,z155,z6]),(0,[z7,z2,z1039,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1040]),(0,[z42,z2,z33,z3,z4,z6]),(0,[z7,z2,z3,z4,z1041,z6]),(0,[z7,z2,z3,z4,z1042,z6]),(0,[z7,z2,z3,z4,z291,z145])],[(0,[z7,z2,z3,z437,z438,z6]),(0,[z7,z2,z3,z1043,z5,z6]),(0,[z7,z2,z3,z4,z1044,z6]),(0,[z7,z2,z938,z18,z5,z6]),(0,[z7,z2,z373,z18,z5,z6])],[(0,[z7,z2,z459,z4,z5,z6]),(0,[z7,z2,z3,z1045,z5,z6]),(0,[z7,z2,z3,z1046,z4,z6]),(0,[z7,z2,z3,z4,z5,z763]),(0,[z7,z2,z3,z325,z10,z6]),(0,[z7,z3,z746,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z711])],[(0,[z7,z2,z3,z1047,z5,z6]),(0,[z7,z2,z3,z4,z1048,z6]),(0,[z7,z2,z3,z4,z1049,z6]),(0,[z308,z2,z3,z4,z5,z229]),(0,[z7,z2,z3,z4,z134,z6]),(0,[z7,z2,z1050,z3,z4,z6]),(0,[z7,z212,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z5,z1051]),(1,[z7,z2,z3,z4,z711])]],
   [[(0,[z7,z2,z3,z4,z1052,z6]),(0,[z221,z2,z3,z4,z5,z56]),(0,[z221,z2,z3,z5,z63,z56]),(0,[z7,z2,z955,z3,z4,z10]),(0,[z7,z2,z47,z4,z154,z37]),(0,[z7,z2,z3,z151,z13,z6]),(0,[z7,z2,z211,z138,z3,z6])],[(0,[z7,z38,z3,z4,z1016,z6]),(0,[z7,z38,z3,z170,z5,z6]),(0,[z7,z2,z3,z1053,z5,z6]),(0,[z14,z7,z144,z4,z331,z6]),(0,[z7,z2,z3,z4,z5,z1054]),(0,[z7,z2,z3,z4,z5,z1055]),(0,[z7,z334,z3,z4,z719,z6]),(0,[z7,z2,z3,z5,z6,z811])],[(0,[z7,z2,z500,z4,z10,z6]),(0,[z7,z531,z3,z17,z5,z6]),(0,[z7,z98,z3,z58,z525,z6]),(0,[z7,z2,z113,z3,z5,z499]),(0,[z7,z2,z1056,z3,z4,z6])],[(0,[z7,z62,z129,z4,z5,z6]),(0,[z7,z2,z713,z4,z5,z6]),(1,[z7,z3,z4,z5,z754]),(0,[z7,z2,z1057,z3,z4,z6]),(0,[z7,z2,z113,z3,z5,z336])],[(0,[z7,z2,z3,z767,z5,z6]),(0,[z7,z2,z1058,z3,z4,z5]),(0,[z7,z2,z3,z4,z1059,z6]),(0,[z182,z2,z3,z4,z331,z6]),(0,[z1060,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1061,z6]),(0,[z7,z2,z211,z138,z3,z5])],[(0,[z7,z2,z3,z1062,z5,z6]),(0,[z7,z2,z3,z325,z5,z229]),(0,[z7,z2,z3,z4,z5,z1063]),(0,[z7,z2,z3,z4,z1064,z6]),(0,[z7,z2,z108,z43,z5,z20]),(0,[z7,z2,z47,z300,z154,z6])],[(0,[z7,z38,z3,z4,z5,z181]),(0,[z7,z2,z40,z3,z4,z434]),(0,[z7,z2,z78,z4,z9,z137])],[(0,[z7,z2,z3,z170,z10,z6]),(0,[z0,z2,z129,z437,z5,z6]),(0,[z2,z3,z4,z5,z763,z56]),(0,[z7,z2,z3,z4,z9,z418])]],
   [[(0,[z7,z2,z3,z1065,z5,z6]),(0,[z308,z2,z3,z325,z5,z6]),(0,[z7,z2,z3,z1066,z5,z6]),(0,[z7,z2,z3,z4,z10,z861]),(0,[z7,z674,z3,z4,z9,z6])],[(0,[z148,z2,z459,z4,z5,z6]),(0,[z7,z2,z3,z4,z1067,z6]),(0,[z7,z2,z3,z9,z6,z1068]),(0,[z7,z2,z618,z4,z5,z74]),(0,[z7,z2,z40,z3,z4,z391])],[(0,[z7,z2,z1069,z4,z5,z6]),(0,[z7,z2,z473,z4,z67,z6]),(0,[z7,z2,z1070,z3,z5,z6]),(0,[z7,z2,z3,z1071,z5,z6]),(0,[z7,z2,z3,z136,z5,z59])],[(0,[z7,z2,z3,z4,z5,z1072]),(0,[z1,z182,z2,z4,z5,z6]),(0,[z7,z88,z3,z4,z5,z76])],[(0,[z165,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z10,z181]),(0,[z7,z2,z3,z4,z1073,z6]),(0,[z7,z2,z365,z3,z10,z6]),(0,[z7,z3,z4,z10,z501,z6])],[(0,[z26,z143,z3,z4,z10,z6]),(0,[z7,z2,z1074,z3,z4,z5]),(0,[z7,z2,z3,z4,z5,z1075]),(0,[z7,z2,z953,z3,z9,z6]),(0,[z7,z3,z4,z637,z9,z6])],[(0,[z1,z118,z143,z4,z5,z6]),(0,[z7,z2,z3,z4,z1076,z6]),(0,[z1,z2,z713,z4,z5,z6]),(0,[z7,z2,z3,z4,z1077,z6]),(0,[z72,z2,z3,z152,z29,z5]),(0,[z7,z2,z3,z4,z1078,z6])],[(0,[z147,z7,z2,z4,z5,z1079]),(0,[z7,z2,z3,z4,z1080,z6]),(0,[z7,z2,z1081,z3,z5,z6]),(0,[z7,z2,z3,z5,z1082,z6]),(0,[z22,z7,z2,z365,z3,z5]),(0,[z7,z2,z3,z1083,z5,z6]),(0,[z7,z496,z3,z17,z5,z6]),(0,[z7,z2,z3,z4,z355,z6]),(1,[z7,z2,z3,z921,z6])]],
   [[(0,[z7,z2,z3,z27,z10,z6]),(0,[z7,z2,z3,z4,z5,z1084]),(0,[z7,z515,z3,z58,z5,z6]),(0,[z7,z2,z3,z4,z1085,z6])],[(0,[z7,z2,z3,z4,z5,z1086]),(0,[z7,z2,z3,z4,z5,z1087]),(0,[z7,z2,z3,z152,z4,z9]),(0,[z7,z2,z3,z938,z5,z6]),(0,[z7,z2,z1088,z4,z5,z6])],[(0,[z7,z2,z3,z84,z10,z6]),(0,[z7,z2,z3,z4,z1089,z6]),(0,[z7,z2,z3,z4,z1090,z6]),(0,[z7,z2,z3,z4,z1091,z6]),(0,[z7,z2,z3,z4,z169,z638]),(0,[z7,z2,z40,z586,z3,z4])],[(0,[z7,z2,z3,z1092,z5,z6]),(0,[z7,z2,z3,z5,z1093,z6]),(0,[z7,z2,z572,z4,z5,z74]),(0,[z7,z2,z3,z4,z1094,z6]),(0,[z7,z2,z3,z4,z1095,z6]),(0,[z7,z2,z138,z3,z288,z109])],[(0,[z7,z2,z3,z746,z5,z6]),(0,[z7,z2,z3,z194,z5,z6]),(0,[z7,z2,z1096,z3,z4,z5])],[(0,[z7,z2,z3,z4,z510,z315]),(0,[z7,z51,z3,z4,z10,z6]),(0,[z201,z2,z3,z4,z5,z56]),(0,[z7,z23,z3,z4,z10,z6]),(0,[z7,z2,z113,z40,z138,z3])],[(0,[z7,z2,z459,z4,z10,z6]),(0,[z7,z2,z3,z1097,z5,z6])],[(0,[z272,z143,z3,z4,z5,z6]),(0,[z7,z3,z4,z10,z6,z368]),(0,[z7,z314,z3,z4,z10,z6])]],
   [[(0,[z7,z2,z140,z3,z28,z4]),(0,[z221,z2,z3,z4,z10,z56]),(0,[z7,z2,z3,z4,z1098,z6]),(0,[z7,z2,z3,z79,z9,z6]),(0,[z7,z2,z3,z4,z11,z704])],[(0,[z1,z2,z579,z4,z5,z6]),(0,[z7,z2,z3,z4,z407,z6]),(0,[z7,z2,z3,z4,z1099,z6]),(0,[z7,z2,z388,z4,z5,z74]),(0,[z7,z2,z3,z5,z59,z811])],[(0,[z7,z2,z3,z93,z127,z6]),(0,[z7,z3,z4,z665,z9,z6])],[(0,[z26,z143,z3,z4,z5,z315]),(0,[z7,z2,z3,z4,z155,z171]),(0,[z7,z2,z1100,z4,z5,z6]),(0,[z7,z2,z1101,z3,z4,z6]),(0,[z7,z2,z1102,z4,z5,z6])],[(0,[z7,z266,z3,z4,z9,z6]),(0,[z648,z2,z3,z4,z226,z6]),(0,[z7,z2,z3,z19,z6,z374])],[(0,[z7,z2,z3,z1103,z5,z6]),(0,[z7,z2,z140,z3,z17,z5]),(0,[z7,z2,z3,z79,z5,z6]),(0,[z1104,z2,z3,z4,z5,z6]),(0,[z7,z2,z113,z24,z3,z4])],[(0,[z7,z2,z3,z27,z5,z315]),(0,[z7,z2,z3,z4,z6,z1105]),(0,[z7,z259,z3,z17,z291,z6]),(0,[z7,z2,z3,z4,z1106,z6]),(0,[z7,z2,z3,z4,z1107,z6])],[(0,[z7,z2,z1108,z4,z5,z6]),(0,[z7,z2,z365,z3,z55,z6])]],
   [[(0,[z147,z182,z2,z4,z5,z6]),(0,[z7,z2,z3,z170,z5,z171]),(0,[z7,z2,z3,z4,z155,z181]),(0,[z7,z2,z3,z4,z5,z1109]),(0,[z7,z2,z3,z1066,z10,z6]),(0,[z7,z2,z40,z3,z4,z711])],[(0,[z7,z2,z3,z4,z1110,z6])],[(0,[z7,z2,z1111,z4,z5,z6]),(0,[z7,z2,z3,z1112,z5,z6]),(0,[z7,z2,z3,z1113,z4,z5]),(0,[z7,z2,z3,z4,z1114,z6]),(0,[z7,z481,z3,z4,z10,z6]),(0,[z7,z2,z1070,z3,z10,z6]),(0,[z7,z2,z81,z4,z5,z74])],[(0,[z143,z3,z459,z4,z5,z6]),(0,[z7,z1115,z3,z4,z5,z6]),(0,[z2,z3,z4,z767,z5,z6]),(0,[z182,z3,z144,z4,z5,z6]),(0,[z7,z2,z3,z1116,z4,z6])],[(0,[z7,z2,z459,z4,z5,z315]),(0,[z7,z2,z3,z4,z975,z6]),(0,[z7,z1117,z3,z4,z5,z6]),(0,[z7,z2,z3,z1118,z5,z6]),(0,[z7,z2,z3,z4,z1119,z6]),(0,[z246,z2,z3,z29,z5,z6]),(0,[z630,z2,z3,z29,z5,z6]),(0,[z7,z2,z3,z4,z10,z418]),(0,[z7,z2,z3,z4,z857,z6])],[(0,[z7,z2,z3,z4,z5,z1120]),(0,[z7,z2,z3,z170,z5,z181]),(0,[z7,z2,z3,z1121,z4,z6])],[(0,[z7,z2,z3,z4,z1122,z6]),(0,[z551,z2,z3,z4,z226,z6]),(0,[z7,z2,z365,z3,z5,z75]),(0,[z7,z2,z1123,z4,z5,z6]),(0,[z7,z2,z3,z4,z1124,z6]),(0,[z7,z2,z40,z3,z610,z4])],[(0,[z7,z2,z86,z3,z109,z6]),(0,[z7,z2,z3,z5,z811,z68])]],
   [[(0,[z7,z2,z500,z4,z9,z6]),(0,[z0,z2,z129,z4,z438,z6]),(1,[z7,z3,z746,z5,z6]),(1,[z7,z3,z4,z719,z6]),(0,[z7,z2,z3,z4,z1035,z10]),(0,[z7,z2,z216,z4,z5,z137])],[(0,[z7,z62,z3,z437,z5,z6]),(0,[z2,z3,z4,z723,z5,z6]),(0,[z1125,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1126]),(0,[z528,z2,z3,z4,z39,z6]),(0,[z7,z2,z3,z1127,z5,z6]),(0,[z7,z2,z3,z151,z9,z6])],[(0,[z7,z2,z3,z84,z510,z6]),(0,[z7,z2,z287,z3,z43,z6]),(0,[z97,z2,z3,z653,z4,z6]),(0,[z221,z2,z3,z4,z55,z56]),(0,[z7,z98,z3,z58,z85,z6]),(0,[z7,z2,z40,z586,z3,z41])],[(0,[z7,z2,z593,z43,z5,z6]),(0,[z7,z2,z3,z194,z10,z6]),(0,[z7,z2,z3,z4,z9,z1128]),(0,[z7,z2,z1129,z3,z5,z6])],[(0,[z7,z2,z3,z4,z1130,z6]),(0,[z7,z2,z3,z1131,z5,z6]),(0,[z7,z2,z3,z4,z5,z1132]),(0,[z7,z2,z113,z3,z5,z443])],[(0,[z7,z2,z3,z4,z1133,z6]),(0,[z7,z2,z79,z18,z5,z6]),(0,[z7,z2,z3,z4,z6,z1134]),(0,[z7,z2,z3,z194,z5,z37])],[(0,[z14,z7,z62,z4,z5,z6]),(0,[z7,z2,z3,z4,z127,z172]),(0,[z7,z2,z3,z4,z9,z1022]),(0,[z7,z2,z3,z151,z5,z6]),(0,[z7,z2,z113,z24,z3,z68]),(0,[z7,z2,z3,z4,z1135,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z1136]),(0,[z7,z2,z365,z253,z3,z6]),(0,[z7,z2,z3,z619,z5,z59]),(0,[z7,z2,z3,z720,z5,z6]),(0,[z7,z2,z3,z4,z5,z288]),(0,[z7,z2,z3,z4,z888,z6])],[(0,[z26,z143,z3,z84,z5,z6]),(0,[z7,z1137,z3,z4,z5,z6]),(0,[z7,z2,z3,z1138,z4,z5]),(0,[z7,z259,z3,z17,z5,z418]),(0,[z7,z367,z3,z4,z10,z6]),(0,[z7,z2,z3,z10,z6,z178]),(0,[z7,z2,z3,z4,z5,z1128]),(0,[z7,z2,z3,z5,z6,z1068])],[(0,[z7,z2,z3,z4,z5,z1139]),(0,[z7,z2,z3,z1140,z5,z6]),(0,[z7,z2,z3,z4,z1141,z6]),(0,[z7,z3,z4,z9,z719,z6]),(0,[z7,z2,z40,z586,z3,z6])],[(0,[z7,z2,z3,z4,z5,z1142]),(0,[z7,z2,z1143,z3,z4,z6]),(0,[z7,z2,z1144,z3,z4,z6]),(0,[z7,z2,z846,z4,z5,z6]),(0,[z7,z2,z108,z43,z5,z6])],[(0,[z7,z371,z3,z4,z10,z6]),(0,[z7,z2,z3,z5,z6,z864]),(0,[z7,z578,z3,z4,z5,z76])],[(0,[z7,z2,z3,z4,z1145,z6]),(0,[z72,z7,z2,z140,z3,z5]),(0,[z7,z2,z3,z4,z331,z6]),(0,[z7,z2,z3,z79,z10,z6]),(0,[z7,z2,z43,z938,z5,z6])],[(0,[z7,z2,z3,z27,z9,z6]),(0,[z148,z69,z3,z4,z70,z6]),(0,[z72,z2,z287,z3,z29,z6]),(0,[z221,z2,z365,z3,z5,z56]),(0,[z7,z2,z239,z4,z5,z76]),(0,[z7,z2,z40,z586,z3,z5])],[(0,[z7,z2,z3,z4,z5,z1146]),(0,[z7,z2,z1147,z4,z5,z6]),(0,[z7,z2,z140,z3,z4,z5]),(0,[z7,z2,z3,z4,z723,z6]),(0,[z7,z2,z3,z18,z236,z6]),(0,[z7,z2,z239,z4,z5,z6])]],
   [[],[(0,[z7,z2,z3,z4,z70,z6]),(0,[z7,z2,z1148,z4,z5,z6]),(0,[z7,z2,z3,z1149,z4,z6]),(0,[z7,z2,z3,z1150,z5,z6]),(0,[z7,z2,z311,z4,z441,z6]),(1,[z7,z2,z113,z24,z3]),(0,[z7,z2,z113,z3,z529,z68])],[(0,[z7,z2,z459,z84,z5,z6]),(0,[z7,z669,z3,z4,z10,z6])],[(0,[z7,z2,z3,z4,z1151,z6]),(0,[z7,z2,z321,z4,z67,z6]),(0,[z7,z1152,z3,z4,z5,z6])],[(0,[z7,z2,z459,z4,z9,z6]),(0,[z147,z7,z2,z775,z5,z6]),(0,[z7,z2,z3,z4,z5,z1153]),(0,[z7,z2,z3,z4,z513,z145]),(0,[z7,z2,z138,z3,z608,z6])],[(0,[z7,z38,z3,z4,z438,z6]),(0,[z7,z1154,z3,z4,z5,z6]),(0,[z97,z2,z3,z4,z326,z6]),(0,[z7,z2,z1155,z3,z4,z5]),(0,[z7,z2,z239,z19,z5,z6]),(0,[z7,z2,z113,z24,z3,z6])],[(0,[z7,z2,z3,z4,z1156,z6]),(0,[z7,z2,z3,z5,z1157,z6]),(0,[z7,z2,z3,z4,z5,z1158]),(0,[z7,z2,z3,z4,z85,z6])],[(0,[z7,z2,z3,z4,z5,z1159]),(0,[z7,z3,z4,z5,z6,z754]),(0,[z7,z2,z108,z43,z5,z243]),(0,[z7,z2,z3,z4,z1160,z6]),(0,[z7,z2,z3,z136,z5,z811])]],
   [[(0,[z7,z2,z1161,z4,z5,z6]),(0,[z7,z2,z3,z4,z1162,z6]),(0,[z687,z2,z112,z4,z5,z6]),(0,[z7,z2,z81,z4,z9,z6]),(0,[z7,z2,z4,z727,z67,z6])],[(0,[z7,z1163,z3,z4,z5,z6]),(0,[z42,z2,z3,z4,z242,z6]),(0,[z7,z428,z3,z4,z5,z76]),(0,[z7,z2,z876,z3,z4,z5]),(0,[z7,z256,z3,z4,z10,z6]),(0,[z7,z2,z113,z24,z3,z5])],[(0,[z7,z2,z3,z4,z1164,z6]),(0,[z148,z69,z3,z4,z123,z6]),(0,[z7,z1165,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1166]),(0,[z7,z2,z3,z4,z5,z1167]),(0,[z7,z98,z3,z746,z5,z6]),(0,[z7,z1168,z3,z4,z5,z6])],[],[(0,[z7,z2,z3,z4,z513,z418])],[(0,[z7,z2,z3,z4,z123,z6]),(0,[z7,z2,z3,z4,z1169,z6]),(0,[z7,z2,z3,z58,z5,z418]),(0,[z7,z2,z81,z4,z5,z6])],[(0,[z7,z2,z3,z1170,z5,z6]),(0,[z147,z26,z143,z4,z5,z6]),(0,[z2,z942,z3,z4,z5,z6]),(0,[z147,z7,z62,z4,z5,z6]),(0,[z7,z2,z3,z4,z1171,z6]),(0,[z7,z2,z474,z3,z4,z208]),(0,[z7,z2,z138,z3,z604,z6]),(0,[z7,z2,z24,z3,z136,z4])],[(0,[z147,z2,z129,z4,z5,z6]),(0,[z7,z2,z3,z1172,z5,z6]),(0,[z14,z7,z144,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1173]),(0,[z7,z2,z3,z4,z291,z418]),(0,[z7,z2,z3,z151,z10,z6]),(0,[z7,z2,z1174,z4,z9,z6])]],
   [[(0,[z7,z2,z3,z1175,z4,z5]),(0,[z7,z2,z3,z437,z9,z6]),(0,[z7,z2,z3,z4,z5,z1176]),(0,[z7,z2,z3,z4,z10,z288]),(0,[z7,z2,z3,z136,z9,z59]),(0,[z7,z2,z1177,z3,z4,z6]),(0,[z7,z2,z554,z18,z5,z6]),(0,[z7,z2,z3,z4,z6,z1178]),(0,[z7,z2,z3,z4,z284,z11]),(0,[z7,z2,z3,z4,z1179,z6]),(0,[z7,z2,z4,z5,z835,z74])],[(0,[z7,z2,z1180,z3,z4,z6]),(0,[z7,z2,z3,z4,z1181,z6]),(0,[z7,z3,z4,z695,z10,z6]),(0,[z7,z2,z3,z92,z220,z6]),(0,[z7,z2,z3,z4,z5,z1182]),(0,[z7,z3,z4,z10,z490,z6]),(0,[z7,z2,z3,z4,z1183,z6]),(0,[z7,z2,z108,z938,z5,z6])],[(0,[z182,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1184,z4,z6]),(0,[z7,z62,z3,z4,z438,z6]),(0,[z7,z3,z4,z1185,z5,z6]),(0,[z7,z2,z3,z4,z5,z1186])],[(0,[z7,z2,z3,z4,z5,z1187]),(0,[z7,z2,z3,z4,z1188,z6]),(0,[z7,z2,z108,z43,z10,z6]),(0,[z7,z367,z3,z4,z5,z75]),(0,[z7,z2,z3,z4,z6,z711])],[(0,[z7,z2,z1174,z4,z5,z6]),(1,[z7,z2,z938,z5,z6])],[(0,[z147,z7,z2,z4,z5,z1189]),(0,[z7,z2,z3,z437,z5,z6]),(0,[z7,z1190,z3,z4,z5,z6]),(0,[z7,z496,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z1191,z6]),(0,[z7,z2,z3,z4,z5,z20])],[(0,[z7,z2,z4,z5,z6,z1192]),(0,[z7,z2,z3,z4,z5,z1193]),(0,[z7,z2,z365,z3,z5,z137]),(0,[z7,z2,z3,z4,z5,z1194]),(0,[z7,z706,z3,z4,z10,z6]),(0,[z7,z2,z3,z4,z6,z1195]),(0,[z7,z2,z24,z3,z4,z6])],[(0,[z7,z2,z3,z4,z5,z1196]),(0,[z26,z143,z3,z4,z378,z6]),(0,[z7,z2,z3,z1197,z5,z6]),(0,[z7,z2,z293,z4,z154,z6]),(0,[z7,z2,z3,z1198,z5,z6]),(0,[z7,z2,z239,z4,z10,z6])]],
   [[(0,[z7,z2,z1199,z4,z5,z6]),(0,[z7,z2,z287,z3,z152,z4]),(0,[z7,z2,z3,z1200,z5,z6]),(0,[z7,z2,z3,z136,z5,z415]),(0,[z7,z2,z426,z4,z5,z74])],[(0,[z69,z942,z3,z4,z5,z6]),(0,[z0,z182,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1201]),(0,[z7,z2,z1202,z4,z5,z6]),(0,[z7,z2,z3,z4,z1203,z6]),(0,[z7,z2,z3,z4,z1204,z6]),(0,[z7,z2,z81,z4,z5,z243]),(0,[z7,z2,z3,z4,z6,z1205])],[(0,[z7,z2,z3,z4,z10,z1031]),(0,[z7,z2,z3,z194,z9,z6]),(0,[z7,z2,z3,z5,z921,z6]),(0,[z7,z2,z3,z1206,z5,z6])],[(0,[z7,z2,z3,z1207,z5,z6]),(0,[z7,z942,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1208,z6]),(0,[z7,z1209,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1210]),(0,[z7,z2,z40,z3,z4,z41])],[(0,[z7,z2,z1211,z4,z5,z6]),(0,[z7,z2,z3,z84,z378,z6]),(0,[z0,z62,z129,z4,z5,z6]),(0,[z0,z2,z713,z4,z5,z6]),(0,[z7,z2,z239,z17,z5,z6]),(0,[z7,z2,z153,z4,z5,z74])],[(0,[z7,z2,z3,z4,z1212,z6]),(0,[z147,z7,z2,z4,z1213,z6]),(0,[z7,z2,z3,z1214,z5,z6]),(0,[z7,z2,z3,z4,z1215,z6]),(0,[z97,z2,z3,z4,z176,z6]),(0,[z1216,z2,z3,z4,z5,z6]),(0,[z7,z2,z108,z79,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1189]),(0,[z516,z69,z3,z4,z5,z6]),(0,[z1217,z7,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z6,z1218]),(0,[z7,z2,z3,z4,z1219,z6]),(0,[z7,z2,z3,z4,z1220,z6]),(0,[z7,z3,z4,z719,z5,z6]),(0,[z7,z539,z3,z4,z9,z6])],[(0,[z7,z2,z3,z1221,z5,z6]),(0,[z7,z2,z3,z1222,z5,z6]),(0,[z7,z580,z3,z58,z5,z6]),(0,[z7,z2,z3,z4,z127,z229]),(0,[z1223,z2,z3,z4,z5,z6]),(0,[z7,z599,z3,z4,z10,z6])]],
   [[(0,[z7,z2,z459,z4,z378,z6]),(0,[z7,z2,z1224,z4,z5,z6]),(0,[z7,z2,z3,z1225,z4,z6]),(0,[z7,z2,z3,z4,z5,z1226]),(0,[z7,z2,z1227,z3,z5,z6]),(0,[z7,z2,z3,z4,z525,z6]),(0,[z7,z296,z3,z58,z5,z6]),(0,[z7,z2,z1228,z4,z9,z6]),(0,[z7,z2,z3,z4,z1229,z6])],[(0,[z7,z2,z804,z4,z5,z6]),(0,[z7,z2,z3,z4,z1230,z6]),(0,[z2,z3,z124,z767,z5,z6]),(0,[z221,z2,z87,z3,z4,z5]),(0,[z14,z308,z144,z4,z5,z6]),(0,[z7,z2,z3,z1231,z5,z6]),(0,[z7,z319,z3,z4,z9,z6]),(0,[z7,z2,z1232,z3,z4,z6])],[(0,[z308,z2,z3,z4,z127,z6]),(0,[z7,z2,z3,z93,z331,z6]),(0,[z7,z2,z3,z4,z1233,z6]),(0,[z7,z1234,z3,z4,z5,z6]),(0,[z7,z1235,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1079]),(0,[z42,z2,z3,z4,z723,z6]),(0,[z7,z2,z81,z18,z5,z6]),(0,[z7,z2,z3,z4,z67,z48])],[(0,[z7,z2,z1236,z4,z5,z6]),(0,[z7,z2,z3,z1237,z4,z6]),(0,[z7,z2,z3,z4,z1238,z6]),(0,[z7,z2,z78,z4,z355,z137])],[(0,[z182,z2,z144,z4,z5,z6]),(0,[z7,z2,z1228,z4,z5,z6]),(0,[z7,z2,z81,z4,z10,z6]),(0,[z7,z2,z138,z3,z168,z6])],[(0,[z26,z500,z143,z4,z5,z6]),(0,[z7,z2,z3,z4,z1213,z6]),(0,[z148,z942,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1239]),(0,[z7,z2,z3,z170,z155,z6]),(0,[z7,z1240,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1241,z6]),(0,[z7,z259,z3,z17,z513,z6]),(0,[z7,z299,z3,z4,z9,z76]),(0,[z7,z2,z3,z43,z236,z6])],[(0,[z7,z2,z3,z4,z5,z1242]),(0,[z7,z38,z3,z437,z5,z6]),(0,[z7,z2,z3,z4,z1243,z6]),(0,[z7,z259,z3,z746,z5,z6]),(0,[z7,z2,z3,z4,z1244,z6])]],
   [[(0,[z7,z2,z3,z325,z127,z6]),(0,[z7,z846,z144,z4,z5,z6]),(0,[z7,z2,z821,z4,z5,z6])],[(0,[z7,z2,z1245,z4,z5,z6]),(0,[z1246,z2,z3,z4,z5,z6])],[(0,[z7,z2,z139,z4,z5,z82]),(0,[z1,z2,z112,z4,z5,z6]),(0,[z182,z2,z3,z4,z10,z6]),(0,[z7,z2,z86,z3,z409,z6]),(0,[z7,z2,z3,z1247,z5,z6])],[(0,[z7,z2,z3,z5,z1248,z6]),(0,[z7,z2,z3,z4,z1249,z6]),(0,[z7,z2,z3,z1250,z5,z6]),(0,[z7,z98,z3,z58,z9,z6]),(0,[z7,z299,z3,z4,z5,z76])],[(0,[z7,z3,z4,z9,z375,z6]),(0,[z7,z2,z3,z1251,z5,z6]),(0,[z7,z2,z1252,z3,z5,z6])],[(0,[z147,z1,z2,z4,z5,z6]),(0,[z7,z38,z3,z4,z1208,z6]),(0,[z7,z2,z3,z437,z10,z6]),(0,[z7,z2,z3,z4,z10,z20]),(0,[z7,z2,z3,z136,z10,z59]),(0,[z7,z487,z3,z4,z9,z6]),(0,[z7,z3,z4,z5,z75,z754]),(0,[z7,z2,z3,z4,z1253,z6])],[(0,[z7,z2,z3,z4,z1254,z6]),(0,[z148,z188,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1255,z6]),(0,[z7,z2,z140,z3,z4,z10]),(0,[z7,z2,z253,z3,z4,z74]),(0,[z7,z3,z4,z679,z9,z6])],[(0,[z7,z2,z4,z753,z5,z6]),(0,[z7,z496,z3,z4,z5,z75])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1048).take 210) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1258)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 527, 210] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 92).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 190).take 66).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [92, 98, 66] = true :=
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

end PEqualNP.Outside.L_meta_39209

theorem PEqualNP.Outside.L_meta_39209 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4205373576) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4205373576) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39209.solve