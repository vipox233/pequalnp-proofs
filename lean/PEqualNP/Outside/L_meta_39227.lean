import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39227

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
  Nat.testBit (4277074600 * 2 ^ 32 + 4241291392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x88223033792618dd#64 ++ 0x110446066f24c31b#64 ++ 0x586670fff92619ff#64 ++ 0xeb0cce1fff24c33f#64 : BitVec 256),
   (0x00888c88a04ae16a#64 ++ 0xa011119114095c2d#64 ++ 0xe9998c88e1ffe1ff#64 ++ 0xdd3331911c3ffc3f#64 : BitVec 256),
   (0x021e050d0a382a30#64 ++ 0xc043c0a1a1470546#64 ++ 0xfe1e0f0f1e387e3e#64 ++ 0xbfc3c1e1e3c70fc7#64 : BitVec 256),
   (0x05e00ad015c05583#64 ++ 0x00bc015a02b80ab0#64 ++ 0xffe00ff01fc07fc6#64 ++ 0x7ffc01fe03f80ff8#64 : BitVec 256),
   (0x077750001fb50004#64 ++ 0x00eeea0003f6a000#64 ++ 0xe7fff0001fff8005#64 ++ 0xfcfffe0003fff000#64 : BitVec 256),
   (0x17ddefeec0000000#64 ++ 0x02fbbdfdd8000000#64 ++ 0xd7ffffffe0000003#64 ++ 0xfafffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000020020048 0x0000000004004009 0x48000088e12601ff 0xc90000111c24c03f

def z1 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe1e0f0f1e387e3e 0xbfc3c1e1e3c70fc7

def z2 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe00ff01fc07fc6 0x7ffc01fe03f80ff8

def z3 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x066670001e000000 0x20ccce0003c00000

def z4 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xe7fff0001fff8005 0xfcfffe0003fff000

def z5 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd7ffffffe0000003 0xfafffffffc000000

def z6 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x586670fff92619ff 0xeb0cce1fff24c33f

def z7 : W := mkw 0x00888c88a042c14a 0x2011119114085829 0xc1998c88e1c781c3 0xd83331911c38f038

def z8 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xe9998c88e1ffe1ff 0xdd3331911c3ffc3f

def z9 : W := mkw 0x0755400000000000 0x00eaa80000000000 0xc7fff00000000001 0xf8fffe0000000000

def z10 : W := mkw 0x00000000200aa068 0xa00000000401540d 0x00000000003f8038 0x000000000007f007

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0xe199800001ff8005 0xdc333000003ff000

def z12 : W := mkw 0x07ffdc88bfffe16e 0xa0fffb9117fffc2d 0xeffffc88ffffe1ff 0xfdffff911ffffc3f

def z13 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0x566673ffe0000003 0xeaccce7ffc000000

def z14 : W := mkw 0x8ffe3fff7ffe7fff 0xd1ffc7ffefffcfff 0xfffe7ffffffe7fff 0xffffcfffffffcfff

def z15 : W := mkw 0x0008050d00082a30 0xc00100a1a0010546 0x18000f0f00007e3a 0x030001e1e0000fc7

def z16 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x08000000192619fc 0x010000000324c33f

def z17 : W := mkw 0x0002000108200810 0x0000400021040102 0x5806000f1820183e 0xab00c001e3040307

def z18 : W := mkw 0x8a3e353f7b3e3afd 0xd147c6a7ef67c75f 0xfe7e7fffff3e7fff 0xffcfcfffffe7cfff

def z19 : W := mkw 0x05c00ac004c04502 0x00b80158009808a0 0xa7800f0006c06600 0x14f001e000d80cc0

def z20 : W := mkw 0x17ddefeec4c04502 0x02fbbdfdd89808a0 0xf7ffffffe6c06603 0xfefffffffcd80cc0

def z21 : W := mkw 0x0000202240000000 0x0000040448000000 0x506670ffe0000003 0xea0cce1ffc000000

def z22 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xaf800f001fc07fc4 0x15f001e003f80ff8

def z23 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xf7ffffffe1ff8007 0xfefffffffc3ff000

def z24 : W := mkw 0x021e050d0a300a10 0x4043c0a1a1460142 0xd61e0f0f1e001e02 0xbac3c1e1e3c003c0

def z25 : W := mkw 0x88aabcbbf96ef9ff 0xb11557977f2ddf3f 0xf9fffcfff9fff9ff 0xff3fff9fff3fff3f

def z26 : W := mkw 0x882210113b3e3afd 0xd10442022767c75f 0x280000001f3e7ffc 0x0500000003e7cfff

def z27 : W := mkw 0x075750000eb50004 0x00eaea0001d6a000 0xa79ff00006ff8001 0x94f3fe0000dff000

def z28 : W := mkw 0x002210003926004c 0x000442000724c009 0x48667088f92601ff 0xe90cce111f24c03f

def z29 : W := mkw 0x15c9eeeae04ae16a 0xa2b93ddd5c095c2d 0xe9f9fcf8e1ffe1ff 0xdd3f3f9f1c3ffc3f

def z30 : W := mkw 0x07d54ac000000000 0x00faa95800000000 0xd7fffff000000003 0xfafffffe00000000

def z31 : W := mkw 0x0000202240000000 0x0000040448000000 0x100000ffe0000002 0x0200001ffc000000

def z32 : W := mkw 0x0755602240000000 0x00eaac0448000000 0xd7fff0ffe0000003 0xfafffe1ffc000000

def z33 : W := mkw 0x00088408a00aa068 0xa00110811401540d 0x00198008e03f8039 0x800330011c07f007

def z34 : W := mkw 0x029e8d8daa7aeb7a 0xe053d1b1b54f5d6f 0xff9f8f8fffffffff 0xfff3f1f1ffffffff

def z35 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000001ff8004 0x04000000003ff000

def z36 : W := mkw 0x1088afeec0000000 0x021115fdd8000000 0x10000fffe0000002 0x020001fffc000000

def z37 : W := mkw 0x88002033600218d9 0x110004066c00431b 0x180000ffe00019fa 0x0300001ffc00033f

def z38 : W := mkw 0x8820303251041085 0x110406064a208210 0x0060707000000000 0x000c0e0e00000000

def z39 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0x01e1f00001c78001 0x403c3e000038f000

def z40 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x001e000f00380038 0x8003c001e0070007

def z41 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x01e000f001c001c0 0x403c001e00380038

def z42 : W := mkw 0x07f75ad01ff55587 0x00feeb5a03feaab0 0xfffffff01fffffc7 0xfffffffe03fffff8

def z43 : W := mkw 0x8f7770337fb718dd 0x11eeee066ff6e31b 0xfffff0ffffff99ff 0xfffffe1ffffff33f

def z44 : W := mkw 0x0008050d00082a30 0xc00100a1a0010546 0xfe000f0f1e007e3e 0x3fc001e1e3c00fc7

def z45 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x879fff0fe0000001 0x90f3ffe1fc000000

def z46 : W := mkw 0x00888c888048e122 0xa011119110091c24 0xe9998c8001d9e1c6 0x5d333190003b3c38

def z47 : W := mkw 0x8822303359241895 0x110446066b248312 0x1066707718001800 0x220cce0ee3000300

def z48 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xfffffffffe007e07 0xffffffffffc00fc0

def z49 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa1998c80e1dfe1c1 0x543331901c3bfc38

def z50 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xe7e670001fc00004 0x7cfcce0003f80000

def z51 : W := mkw 0x021601050a300a10 0x4042c020a1460142 0xf61e03071e381e04 0xbec3c060e3c703c0

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe000f001e007e06 0x3fc001e003c00fc0

def z53 : W := mkw 0x15e1eaf2d5c05583 0x02bc3d5e5ab80ab0 0x01e1f0f0e1c001c1 0x403c3e1e1c380038

def z54 : W := mkw 0x9ffffffffde65ddf 0x13ffffffffbccbbb 0xffffffffffe67fff 0xfffffffffffccfff

def z55 : W := mkw 0x8f7770335fb51895 0x11eeee066bf6a312 0x166670771e001800 0x22ccce0ee3c00300

def z56 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xae180f001e387e3c 0x15c301e003c70fc7

def z57 : W := mkw 0x021c050c02182220 0xc04380a180430444 0xf61e0f0f06186602 0xbec3c1e1e0c30cc0

def z58 : W := mkw 0x05e88ed8b5caf5eb 0xa0bd11db16b95ebd 0xfff98ff8ffffffff 0xffff31ff1fffffff

def z59 : W := mkw 0x8f7770337fb718dd 0x11eeee066ff6e31b 0x5e6670ffff2619ff 0xebccce1fffe4c33f

def z60 : W := mkw 0x0755400000000000 0x00eaa80000000000 0xe7fff00001ff8005 0xfcfffe00003ff000

def z61 : W := mkw 0x17ddefeee04ae16a 0xa2fbbdfddc095c2d 0xffffffffe1ffe1ff 0xfffffffffc3ffc3f

def z62 : W := mkw 0x00888c888048e122 0xa011119110091c24 0xa1998c0000d9e000 0x14333180001b3c00

def z63 : W := mkw 0x88203032710610cd 0x110406064e20c219 0x506670ffe10601c3 0xea0cce1ffc20c038

def z64 : W := mkw 0x021c050c02182220 0xc04380a180430444 0xa6180f0006186600 0x14c301e000c30cc0

def z65 : W := mkw 0x88203032710610cd 0x110406064e20c219 0x006070f0e10601c1 0x400c0e1e1c20c038

def z66 : W := mkw 0x021750000a350004 0x0042ea000146a000 0x001ff000003f8001 0x8003fe000007f000

def z67 : W := mkw 0x0755400006910000 0x00eaa80000d22000 0xa799800006d98000 0x14f3300000db3000

def z68 : W := mkw 0x8d6232735da41c95 0x11ac464e6bb48392 0x166673771e001e00 0x22ccce6ee3c003c0

def z69 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x08000c88e00061fa 0x010001911c000c3f

def z70 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x01998088e1ff81f9 0xc03330111c3ff03f

def z71 : W := mkw 0x077f550c1fb50004 0x00efeaa183f6a000 0xf7ffff0f1fff8007 0xfeffffe1e3fff000

def z72 : W := mkw 0x17ffffeedfb50004 0x02fffffddbf6a000 0xf7ffffffffff8007 0xfefffffffffff000

def z73 : W := mkw 0x88aa9c99b96ef9ff 0xb1155393372ddf3f 0xe9998c88f9fff9ff 0xdd3331911f3fff3f

def z74 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0x1666737700000000 0x22ccce6ee0000000

def z75 : W := mkw 0x15c1eae2c0000000 0x02b83d5c58000000 0x51e7f0ffe0000003 0xea3cfe1ffc000000

def z76 : W := mkw 0x0560025015801481 0x00ac004a02b00290 0x166003701e001e00 0x22cc006e03c003c0

def z77 : W := mkw 0x077752501fb51485 0x00eeea4a03f6a290 0xf7fff3701fff9e05 0xfefffe6e03fff3c0

def z78 : W := mkw 0x00888c8880000000 0x0011119110000000 0xc1998c88e0000003 0xd83331911c000000

def z79 : W := mkw 0x0560025015801481 0x00ac004a02b00290 0x5e6003f01f001fc6 0x6bcc007e03e003f8

def z80 : W := mkw 0x07fe0fdd1ff87fb3 0xc0ffc1fba3ff0ff6 0xfffe0fff1ff87ffe 0xffffc1ffe3ff0fff

def z81 : W := mkw 0x075750000a350004 0x00eaea000146a000 0xc7fff000003f8001 0xf8fffe000007f000

def z82 : W := mkw 0x9ffffffff92618dd 0x13ffffffff24c31b 0xdffffffff92619ff 0xfbffffffff24c33f

def z83 : W := mkw 0x021601050a300a10 0x4042c020a1460142 0x160603071e001e00 0x22c0c060e3c003c0

def z84 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xfe667fffff267fff 0xffcccfffffe4cfff

def z85 : W := mkw 0x0020001015c05583 0x0004000202b80ab0 0x0000000001c001c0 0x0000000000380038

def z86 : W := mkw 0x129cafeec0000000 0x025395fdd8000000 0xd61e0fffe0000002 0xbac3c1fffc000000

def z87 : W := mkw 0x077750101fb51085 0x00eeea0203f6a210 0xfffff0f01fff99c7 0xfffffe1e03fff338

def z88 : W := mkw 0x008088808040c102 0x2010111010081820 0x0181800000c18000 0x0030300000183000

def z89 : W := mkw 0x1088affec0405583 0x021115ffd8080ab0 0x18000fffe0007fc2 0x030001fffc000ff8

def z90 : W := mkw 0x029c8d8c80000000 0x005391b190000000 0xd79f8f8fe0000003 0xfaf3f1f1fc000000

def z91 : W := mkw 0x17dfefefca382a30 0xc2fbfdfdf9470546 0xfffffffffe387e3f 0xffffffffffc70fc7

def z92 : W := mkw 0x8abebdbffb7efbff 0xf157d7b7ff6fdf7f 0xffffffffffffffff 0xffffffffffffffff

def z93 : W := mkw 0x00800ad000405583 0x0010015a00080ab0 0x18000ff000007fc2 0x030001fe00000ff8

def z94 : W := mkw 0x121de52ec0000000 0x0243bca5d8000000 0x001ff00fe0000001 0x8003fe01fc000000

def z95 : W := mkw 0x17ddefeec6910000 0x02fbbdfdd8d22000 0xf7ffffffe6d98003 0xfefffffffcdb3000

def z96 : W := mkw 0x077f550d1fbd2a34 0xc0efeaa1a3f7a546 0xfe7e7f0f1e387e3e 0xbfcfcfe1e3c70fc7

def z97 : W := mkw 0x0560000015800000 0x00ac000002b00000 0x01e0000001c00000 0x403c000000380000

def z98 : W := mkw 0x882230337b3e3afd 0xd10446066f67c75f 0x786670ffff3e7fff 0xef0cce1fffe7cfff

def z99 : W := mkw 0x05e21ad01ff55587 0x00bc435a03feaab0 0xffe00ff01fffffc6 0x7ffc01fe03fffff8

def z100 : W := mkw 0x0560001015c05583 0x00ac000202b80ab0 0xefe000001fc07fc4 0x7dfc000003f80ff8

def z101 : W := mkw 0x0000000020020048 0x0000000004004009 0x08000000012601fc 0x010000000024c03f

def z102 : W := mkw 0x00800ad000405583 0x0010015a00080ab0 0x000000f0000001c0 0x0000001e00000038

def z103 : W := mkw 0x021c050c00000000 0x004380a180000000 0xd61e0f0f00000002 0xbac3c1e1e0000000

def z104 : W := mkw 0x00000000204ae16a 0xa000000004095c2d 0xe999800001ffe1fd 0xdd333000003ffc3f

def z105 : W := mkw 0x0000000020020048 0x0000000004004009 0xe9998088e1ff81ff 0xdd3330111c3ff03f

def z106 : W := mkw 0x0002000108200810 0x0000400021040102 0x1006000718001800 0x2200c000e3000300

def z107 : W := mkw 0x8de23af37de65ddf 0x11bc475e6fbccbbb 0xffe67fffffe67fff 0xfffccffffffccfff

def z108 : W := mkw 0x9fdfffefe826085c 0x13fbfffdfd04c10b 0xd7ffffffe026003b 0xfafffffffc04c007

def z109 : W := mkw 0x0080888080000000 0x0010111010000000 0x01818080e0000001 0x403030101c000000

def z110 : W := mkw 0x07ffdc889fb50004 0x00fffb9113f6a000 0xe7fffc88ffff8007 0xfcffff911ffff000

def z111 : W := mkw 0x00000000204ae16a 0xa000000004095c2d 0x2800000001ffe1fc 0x05000000003ffc3f

def z112 : W := mkw 0x88aabcbbf96ef9ff 0xb11557977f2ddf3f 0x58667cfff92679ff 0xeb0ccf9fff24cf3f

def z113 : W := mkw 0x8a1e352f6a3e2a7c 0xd143c6a5ed47c54f 0x001e700fe03e0039 0x8003ce01fc07c007

def z114 : W := mkw 0x0000001000405583 0x0000000200080ab0 0x0800000000007fc0 0x0100000000000ff8

def z115 : W := mkw 0x00808880a042c14a 0x2010111014085829 0x01818080e1c781c1 0x403030101c38f038

def z116 : W := mkw 0x05e08ad0b5c2d5cb 0x20bc115a16b85ab9 0x01e180f0e1c781c1 0x403c301e1c38f038

def z117 : W := mkw 0x0020001011001081 0x0004000202200210 0x1060007018001800 0x220c000e03000300

def z118 : W := mkw 0x17fdeffed5801481 0x02ffbdffdab00290 0xd7fffffffe001e03 0xfaffffffffc003c0

def z119 : W := mkw 0x021750000a350004 0x0042ea000146a000 0xe61ff0001e3f8005 0xbcc3fe0003c7f000

def z120 : W := mkw 0x00888ed8a04af5eb 0xa01111db14095ebd 0xf9998ff8e1ffffff 0xdf3331ff1c3fffff

def z121 : W := mkw 0x0022100019240004 0x0004420003248000 0x4066700019260005 0xe80cce000324c000

def z122 : W := mkw 0x0560025015801481 0x00ac004a02b00290 0xfe600f701e007e06 0x3fcc01ee03c00fc0

def z123 : W := mkw 0x07f7d880bff7c14e 0x20fefb1017fef829 0xe7fff080ffff81c5 0xfcfffe101ffff038

def z124 : W := mkw 0x17ddefeec048e122 0xa2fbbdfdd8091c24 0xf7ffffffe0d9e003 0xfefffffffc1b3c00

def z125 : W := mkw 0x0755400006910000 0x00eaa80000d22000 0xe7fff00006d98001 0xfcfffe0000db3000

def z126 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x01fff0ffe0000001 0xc03ffe1ffc000000

def z127 : W := mkw 0x17f7fae2dfb50004 0x02feff5c5bf6a000 0xe7fff0f0ffff8005 0xfcfffe1e1ffff000

def z128 : W := mkw 0x05e88c88b5cae16a 0xa0bd119116b95c2d 0xeff98c88ffffe1ff 0xfdff31911ffffc3f

def z129 : W := mkw 0x8888acbbe04af9fb 0xb11115977c095f3f 0xf9998cffe1fff9ff 0xdf33319ffc3fff3f

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0x5006000f00000002 0xaa00c001e0000000

def z131 : W := mkw 0x8888acbbe04af9fb 0xb11115977c095f3f 0x18000cffe00079fa 0x0300019ffc000f3f

def z132 : W := mkw 0x029e0fdd0a787fb3 0xc053c1fba14f0ff6 0xfe1e0fff1e387ffe 0xbfc3c1ffe3c70fff

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0x5800000018001806 0x2b00000003000300

def z134 : W := mkw 0x8822303359241895 0x110446066b248312 0x5866707f1820183e 0xab0cce0fe3040307

def z135 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x16667fffe0000002 0x22cccffffc000000

def z136 : W := mkw 0x0000000100000810 0x0000000020000102 0x1800000f0000183a 0x03000001e0000307

def z137 : W := mkw 0x000200010a382a30 0xc000400021470546 0x280000001e387e3c 0x0500000003c70fc7

def z138 : W := mkw 0x0020001011001081 0x0004000202200210 0xfe600ff01f007fc6 0x7fcc01fe03e00ff8

def z139 : W := mkw 0x8800202360020858 0x110004046c00410b 0x0000000fe0000038 0x00000001fc000007

def z140 : W := mkw 0x00088408a04ae16a 0xa001108114095c2d 0x28198008e1ffe1fd 0x850330011c3ffc3f

def z141 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xff998f88ffffffff 0xfff331f11fffffff

def z142 : W := mkw 0x00800ac000000000 0x0010015800000000 0x10000ff000000002 0x020001fe00000000

def z143 : W := mkw 0x88aabcbbf92618dd 0x111557977f24c31b 0xd9fffcfff92619ff 0xfb3fff9fff24c33f

def z144 : W := mkw 0x05c88ec880000000 0x00b911d910000000 0xd7f98ff8e0000003 0xfaff31ff1c000000

def z145 : W := mkw 0x0088acaac0000000 0x0011159558000000 0xd1fffcffe0000003 0xfa3fff9ffc000000

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z147 : W := mkw 0x0540024004800400 0x00a8004800900080 0x0600030006000600 0x00c0006000c000c0

def z148 : W := mkw 0x1088afeee04ae16a 0xa21115fddc095c2d 0x18000fffe00061fa 0x030001fffc000c3f

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000f0000007e02 0x030001e000000fc0

def z150 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x08198c88e03fe1fb 0x810331911c07fc3f

def z151 : W := mkw 0x008008802042414a 0x0010011004084829 0xe9800c88e1e661ff 0xdd3001911c3ccc3f

def z152 : W := mkw 0x00808880a042c14a 0x2010111014085829 0xe9818c80e1c7e1c7 0x5d3031901c38fc38

def z153 : W := mkw 0x05c00ac000000000 0x00b8015800000000 0x01e000f000000000 0x403c001e00000000

def z154 : W := mkw 0x15e8affed5c05583 0x02bd15ffdab80ab0 0xffe00fffffc07fc6 0x7ffc01fffff80ff8

def z155 : W := mkw 0x0080088000404102 0x0010011000080820 0xe9800c8001c061c6 0x5d30019000380c38

def z156 : W := mkw 0x056350001da50004 0x00ac6a0003b4a000 0x41e7f00019e78005 0xe83cfe00033cf000

def z157 : W := mkw 0x0020000011000000 0x0004000002200000 0x4060000019000004 0x680c000003200000

def z158 : W := mkw 0x88223033796ef9ff 0xb10446066f2ddf3f 0x786670fff9fff9ff 0xef0cce1fff3fff3f

def z159 : W := mkw 0x0775500015850004 0x00eeaa0002b0a000 0xc7fff00001c78001 0xf8fffe000038f000

def z160 : W := mkw 0x8a3e151d3b3e3afd 0xd147c2a3a767c75f 0xfe1e0f0f1f3e7ffe 0xbfc3c1e1e3e7cfff

def z161 : W := mkw 0x0214010400000000 0x0042802080000000 0x1606030700000000 0x22c0c060e0000000

def z162 : W := mkw 0x9ffffffffb3e3afd 0xd3ffffffff67c75f 0xffffffffff3e7fff 0xffffffffffe7cfff

def z163 : W := mkw 0x17ddcfcc82182220 0xc2fbb9f990430444 0xa7998f0006186600 0x14f331e000c30cc0

def z164 : W := mkw 0x8de03af275c655cf 0x11bc075e4eb8cab9 0x01e070f0e1c601c1 0x403c0e1e1c38c038

def z165 : W := mkw 0x0080088000404102 0x0010011000080820 0x0180008001c001c0 0x4030001000380038

def z166 : W := mkw 0x0022100019240004 0x0004420003248000 0x0066700018000000 0x200cce0003000000

def z167 : W := mkw 0x15c1eae2c0000000 0x02b83d5c58000000 0xd7e1fff0e0000003 0x7afc3ffe1c000000

def z168 : W := mkw 0x121fe52fca382a30 0xc243fca5f9470546 0x001ff00fe0380039 0x8003fe01fc070007

def z169 : W := mkw 0x077e050d1fb82a30 0xc0efc0a1a3f70546 0xfffe0f0f1ff87e3e 0xffffc1e1e3ff0fc7

def z170 : W := mkw 0x05c00ac000000000 0x00b8015800000000 0xd7e00ff000000002 0x7afc01fe00000000

def z171 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0xe1f9f00001ff8005 0xdc3f3e00003ff000

def z172 : W := mkw 0x0560025015c05583 0x00ac004a02b80ab0 0x3e6003701fc07fc4 0x27cc006e03f80ff8

def z173 : W := mkw 0x07dc0fcc06d86722 0xc0fb81f980db0ce4 0xa7980f0006d86600 0x14f301e000db0cc0

def z174 : W := mkw 0x05e15ad015c55587 0x00bc2b5a02b8aab0 0xffe1fff01fc7ffc7 0x7ffc3ffe03f8fff8

def z175 : W := mkw 0x17ddefeec2182220 0xc2fbbdfdd8430444 0xf7ffffffe6186603 0xfefffffffcc30cc0

def z176 : W := mkw 0x121de52ec0000000 0x0243bca5d8000000 0x507ff0ffe0000003 0xea0ffe1ffc000000

def z177 : W := mkw 0x002210001fb50004 0x0004420003f6a000 0x200000001fff8004 0x0400000003fff000

def z178 : W := mkw 0x17dfcfcd8a382a30 0xc2fbf9f9b1470546 0xff9f8f0f1e387e3e 0xbff3f1e1e3c70fc7

def z179 : W := mkw 0x88221011396ef9ff 0xb1044202272ddf3f 0x2800000019fff9fc 0x05000000033fff3f

def z180 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x006670ffe12601f9 0xc00cce1ffc24c03f

def z181 : W := mkw 0x0022001119201891 0x0004400223240312 0x586600ff192019fe 0xeb0cc01fe324033f

def z182 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xd61e0f0f0038003a 0xbac3c1e1e0070007

def z183 : W := mkw 0x17fdeffed1001081 0x02ffbdffda200210 0xdffffffff90019c7 0xfbffffffff200338

def z184 : W := mkw 0x00888c888048e122 0xa011119110091c24 0xe9998c0800f9e03e 0x9d333181001f3c07

def z185 : W := mkw 0x0020001011001081 0x0004000202200210 0x586000f0190019c6 0x6b0c001e03200338

def z186 : W := mkw 0x880230236826085c 0x110046046d04c10b 0x0006700fe0260039 0x8000ce01fc04c007

def z187 : W := mkw 0x121ff52eca350004 0x0243fea5d946a000 0x001ff00fe03f8001 0x8003fe01fc07f000

def z188 : W := mkw 0x1215612640000000 0x0242ac24c8000000 0x0006700700000000 0x0000ce00e0000000

def z189 : W := mkw 0x021f550d0a3d2a34 0xc043eaa1a147a546 0x001ff00f003f8039 0x8003fe01e007f007

def z190 : W := mkw 0x17ddefefc0082a30 0xc2fbbdfdf8010546 0xdfffffffe0007e3b 0xfbfffffffc000fc7

def z191 : W := mkw 0x021c050d00082a30 0xc04380a1a0010546 0xde1e0f0f00007e3a 0xbbc3c1e1e0000fc7

def z192 : W := mkw 0x021750000a350004 0x0042ea000146a000 0xe19ff00001ff8005 0xdc33fe00003ff000

def z193 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x01fff00001ff8001 0xc03ffe00003ff000

def z194 : W := mkw 0x077f550d1fbd2a34 0xc0efeaa1a3f7a546 0xffffff0f1ffffe3f 0xffffffe1e3ffffc7

def z195 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x086070f0f92619fd 0x410c0e1e1f24c33f

def z196 : W := mkw 0x05c00ac000000000 0x00b8015800000000 0x87800f0000000000 0x10f001e000000000

def z197 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xb7e00f701ec07e00 0x36fc01ee03d80fc0

def z198 : W := mkw 0x021601050a300a10 0x4042c020a1460142 0x5e06030f1e201e3e 0xabc0c061e3c403c7

def z199 : W := mkw 0x882a353f792e3afd 0xd10546a7ef25c75f 0x58667ffff9267fff 0xeb0ccfffff24cfff

def z200 : W := mkw 0x15c1eae2c0000000 0x02b83d5c58000000 0x01e1f0f0e0000001 0x403c3e1e1c000000

def z201 : W := mkw 0x0002000128220858 0x000040002504410b 0x5806008ff92619ff 0xeb00c011ff24c33f

def z202 : W := mkw 0x05e88ed895c8f5a3 0xa0bd11db12b91eb4 0xfff98ff01fd9ffc6 0x7fff31fe03fb3ff8

def z203 : W := mkw 0x077770225fb50004 0x00eeee044bf6a000 0xf7fff0ffffff8007 0xfefffe1ffffff000

def z204 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xfff98ff01fffffc7 0xffff31fe03fffff8

def z205 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x186670fff80019fa 0x230cce1fff00033f

def z206 : W := mkw 0x000a040908282830 0x8001408121050506 0xf81e0c0f1838783e 0xbf03c181e3070f07

def z207 : W := mkw 0x077750011fb50814 0x00eeea0023f6a102 0xfffff00f1fff983f 0xfffffe01e3fff307

def z208 : W := mkw 0x07f758801ff54106 0x00feeb1003fea820 0xeffffc801fffe1c7 0xfdffff9003fffc38

def z209 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa7fff0001ed98000 0x34fffe0003db3000

def z210 : W := mkw 0x0020001015c05583 0x0004000202b80ab0 0x280000001fc07fc4 0x0500000003f80ff8

def z211 : W := mkw 0x17fdeffed5c05583 0x02ffbdffdab80ab0 0xffffffffffc07fc7 0xfffffffffff80ff8

def z212 : W := mkw 0x00200010310210c9 0x0004000206204219 0x586000f8f92619ff 0xeb0c001f1f24c33f

def z213 : W := mkw 0x0755400000000000 0x00eaa80000000000 0x0666700000000000 0x20ccce0000000000

def z214 : W := mkw 0x023e150d1fbd2a34 0xc047c2a1a3f7a546 0xfe1e0f0f1ffffe3e 0xbfc3c1e1e3ffffc7

def z215 : W := mkw 0x880230236826085c 0x110046046d04c10b 0x506670ffe026003b 0xea0cce1ffc04c007

def z216 : W := mkw 0x0008040800082020 0x8001008100010404 0xe8180c080038603e 0x9d03018100070c07

def z217 : W := mkw 0x05c00ac004c04502 0x00b80158009808a0 0xef800f8007c067c6 0x5df001f000f80cf8

def z218 : W := mkw 0x121dc50c80000000 0x0243b8a190000000 0x0019800000000000 0x0003300000000000

def z219 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xff9f8f0f1ffffe3f 0xfff3f1e1e3ffffc7

def z220 : W := mkw 0x0020001015c05583 0x0004000202b80ab0 0xfe000f001fc07fc6 0x3fc001e003f80ff8

def z221 : W := mkw 0x8822101119241895 0x1104420223248312 0x0000000018001800 0x0000000003000300

def z222 : W := mkw 0x8802302348240814 0x1100460469048102 0x0006700700000000 0x0000ce00e0000000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0xa199800000d98000 0x14333000001b3000

def z224 : W := mkw 0x029c8d8ca04ae16a 0xa05391b194095c2d 0xff9f8f8fe1ffe1ff 0xfff3f1f1fc3ffc3f

def z225 : W := mkw 0x1088afeec0000000 0x021115fdd8000000 0x50667fffe0000003 0xea0ccffffc000000

def z226 : W := mkw 0x175de76ec0000000 0x02ebbcedd8000000 0x167ff37fe0000001 0xa2cffe6ffc000000

def z227 : W := mkw 0x002210101ff55587 0x0004420203feaab0 0x280000001fffffc4 0x0500000003fffff8

def z228 : W := mkw 0x00888c88a00aa068 0xa01111911401540d 0xc1998c88e03f803b 0xd83331911c07f007

def z229 : W := mkw 0x0020001011001081 0x0004000202200210 0x08000000190019c4 0x0100000003200338

def z230 : W := mkw 0x88002033600218d9 0x110004066c00431b 0x580000ffe12619ff 0xcb00001ffc24c33f

def z231 : W := mkw 0x9ffffffff96ef9ff 0xb3ffffffff2ddf3f 0xfffffffff9fff9ff 0xffffffffff3fff3f

def z232 : W := mkw 0x0000000100082a30 0xc000000020010546 0x0800000000007e38 0x0100000000000fc7

def z233 : W := mkw 0x0020100015850004 0x0004020002b0a000 0x0000000001c78000 0x000000000038f000

def z234 : W := mkw 0x021601050a300a10 0x4042c020a1460142 0x0006000700000000 0x0000c000e0000000

def z235 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x161e030f1e381e38 0xa2c3c061e3c703c7

def z236 : W := mkw 0x021e050d2a3a2a78 0xc043c0a1a547454f 0xfe1e0f8fff3e7fff 0xffc3c1f1ffe7cfff

def z237 : W := mkw 0x0560000015800000 0x00ac000002b00000 0xe7e000001fc00004 0x7cfc000003f80000

def z238 : W := mkw 0x05c02ae240000000 0x00b8055c48000000 0xd7e67fffe0000003 0xfafccffffc000000

def z239 : W := mkw 0x021e252f4a382a30 0xc043c4a5e9470546 0xfe7e7ffffe387e3f 0xffcfcfffffc70fc7

def z240 : W := mkw 0x00800ad000405583 0x0010015a00080ab0 0xfe000ff01e007fc6 0x3fc001fe03c00ff8

def z241 : W := mkw 0x00a00ad015c05583 0x0014015a02b80ab0 0x38000ff01fc07fc6 0x070001fe03f80ff8

def z242 : W := mkw 0x00888c8880000000 0x0011119110000000 0xe1998c88e1ff8007 0xdc3331911c3ff000

def z243 : W := mkw 0x8d617032758710cd 0x11ac2e064eb0e219 0x01e1f0f0e1c781c1 0x403c3e1e1c38f038

def z244 : W := mkw 0x00888c888048e122 0xa011119110091c24 0xe1998c0001ffe005 0xdc333180003ffc00

def z245 : W := mkw 0x17ddefeec0404102 0x02fbbdfdd8080820 0xffffffffe1c061c7 0xfffffffffc380c38

def z246 : W := mkw 0x0541400004810000 0x00a8280000902000 0x0181800000c18000 0x0030300000183000

def z247 : W := mkw 0x0080088000404102 0x0010011000080820 0x08000c80000061c2 0x0100019000000c38

def z248 : W := mkw 0x8800203340001891 0x1100040668000312 0x1000007700001800 0x0200000ee0000300

def z249 : W := mkw 0x07ff5fdd1ffd7fb7 0xc0ffebfba3ffaff6 0xffffffff1fffffff 0xffffffffe3ffffff

def z250 : W := mkw 0x10888fcc80000000 0x021111f990000000 0x00000f0000000000 0x000001e000000000

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0xe018000000380004 0x9c03000000070000

def z252 : W := mkw 0x0008040800082020 0x8001008100010404 0x08000c080000603a 0x0100018100000c07

def z253 : W := mkw 0x882230337fb718dd 0x110446066ff6e31b 0x786670ffffff99ff 0xef0cce1ffffff33f

def z254 : W := mkw 0x0000000006910000 0x0000000000d22000 0x2000000006d98000 0x0400000000db3000

def z255 : W := mkw 0x8deabefbfdeefdff 0xb1bd57df7fbddfbf 0xffffffffffffffff 0xffffffffffffffff

def z256 : W := mkw 0x05e80fdd15c87fb3 0xc0bd01fba2b90ff6 0xffe00fff1fc07ffe 0x7ffc01ffe3f80fff

def z257 : W := mkw 0x17ddcfcc80000000 0x02fbb9f990000000 0x87998f0000000000 0x10f331e000000000

def z258 : W := mkw 0x008a8c89a86ae97a 0xa0115191350d5d2f 0xf99f8c8ff9fff9ff 0xff33f191ff3fff3f

def z259 : W := mkw 0x000a050d08282a30 0xc00140a1a1050546 0x58060f0f18207e3e 0xab00c1e1e3040fc7

def z260 : W := mkw 0x0020100011040004 0x0004020002208000 0x0060700001060001 0x400c0e000020c000

def z261 : W := mkw 0x05e20ad11de05d93 0x00bc415a23bc0bb2 0xffe60fff1fe07ffe 0xfffcc1ffe3fc0fff

def z262 : W := mkw 0x05e00ac015c04502 0x00bc015802b808a0 0xe7e00f001fc06604 0x7cfc01e003f80cc0

def z263 : W := mkw 0x021750000a350004 0x0042ea000146a000 0x0006700000000000 0x0000ce0000000000

def z264 : W := mkw 0x0008840880000000 0x0001108110000000 0x00198008e0000001 0x800330011c000000

def z265 : W := mkw 0x0560000015800000 0x00ac000002b00000 0x066000001e000000 0x20cc000003c00000

def z266 : W := mkw 0x880ab42be82ea87c 0xb10156857d05d50f 0x001ff00fe03f8039 0x8003fe01fc07f007

def z267 : W := mkw 0x17fffffedff55587 0x02ffffffdbfeaab0 0xffffffffffffffc7 0xfffffffffffffff8

def z268 : W := mkw 0x882230237926085c 0x110446046f24c10b 0x4066700ff926003d 0xe80cce01ff24c007

def z269 : W := mkw 0x175de52ec0000000 0x02ebbca5d8000000 0xc7fff00fe0000001 0xf8fffe01fc000000

def z270 : W := mkw 0x0755400000000000 0x00eaa80000000000 0x8799800000000000 0x10f3300000000000

def z271 : W := mkw 0x0022100019240004 0x0004420003248000 0x0000000019260004 0x000000000324c000

def z272 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xc7fff0001e000001 0xf8fffe0003c00000

def z273 : W := mkw 0x00880c8800486122 0x8011019100090c24 0xe9980c8801f861fe 0xdd330191003f0c3f

def z274 : W := mkw 0x05e20ad11ff87fb3 0xc0bc415a23ff0ff6 0xffe00ff01ff87ffe 0x7ffc01fe03ff0fff

def z275 : W := mkw 0x077600001fb00000 0x00eec00003f60000 0xe7fe00001ff80004 0xfcffc00003ff0000

def z276 : W := mkw 0x0022101019241085 0x0004420203248210 0x586670f0192619c7 0xeb0cce1e0324c338

def z277 : W := mkw 0x0080088000404102 0x0010011000080820 0xa1800c0000c06000 0x1430018000180c00

def z278 : W := mkw 0x07ffdd8dbfffeb7e 0xe0fffbb1b7fffd6f 0xffffff8fffffffff 0xfffffff1ffffffff

def z279 : W := mkw 0x0002000108200810 0x0000400021040102 0xfe060f0f1e207e3e 0xbfc0c1e1e3c40fc7

def z280 : W := mkw 0x0560001015801081 0x00ac000202b00210 0xffe000f01fc019c6 0x7ffc001e03f80338

def z281 : W := mkw 0x029e8d8daa7aeb7a 0xe053d1b1b54f5d6f 0xfe1e0f8ffe387ffe 0xbfc3c1f1ffc70fff

def z282 : W := mkw 0x000200000a300000 0x0000400001460000 0x200000001e380004 0x0400000003c70000

def z283 : W := mkw 0x9de1faf2f10610cd 0x13bc3f5e5e20c219 0x01e1f0f0e10601c1 0x403c3e1e1c20c038

def z284 : W := mkw 0x000200010a382a30 0xc000400021470546 0x7806000f1e387e3e 0xaf00c001e3c70fc7

def z285 : W := mkw 0x8808253f600a3af9 0xd10104a7ec01475f 0x18000fffe0007ffa 0x030001fffc000fff

def z286 : W := mkw 0x9ffdfffef10610cd 0x13ffbfffde20c219 0xd7ffffffe10601c3 0xfafffffffc20c038

def z287 : W := mkw 0x05c88ec8a04ae16a 0xa0b911d914095c2d 0xfff98ff8e1ffe1ff 0xffff31ff1c3ffc3f

def z288 : W := mkw 0x023e051d1ff87fb3 0xc047c0a3a3ff0ff6 0xfe1e0f0f1ff87ffe 0xbfc3c1e1e3ff0fff

def z289 : W := mkw 0x1541626240000000 0x02a82c4c48000000 0x0060707000000000 0x000c0e0e00000000

def z290 : W := mkw 0x07ffded8bffff5ef 0xa0fffbdb17fffebd 0xfffffff8ffffffff 0xffffffff1fffffff

def z291 : W := mkw 0x17ddcfcc8048e122 0xa2fbb9f990091c24 0xa7998f0000d9e000 0x14f331e0001b3c00

def z292 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x19e00ff001c07fc2 0x433c01fe00380ff8

def z293 : W := mkw 0x9fffffffd9241895 0x13fffffffb248312 0xd7fffffff8001803 0xfaffffffff000300

def z294 : W := mkw 0x88802af360425ddb 0x1110055e6c084bbb 0x18000fffe0007ffa 0x030001fffc000fff

def z295 : W := mkw 0x88a238b3796659df 0x111447166f2ccb3b 0xf9e67cfff9e679ff 0xff3ccf9fff3ccf3f

def z296 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x181e0f0f00387e3a 0x8303c1e1e0070fc7

def z297 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xe9800c88e1c061fe 0x5d3001911c380c3f

def z298 : W := mkw 0x07f75ad01ff55587 0x00feeb5a03feaab0 0xe7fff0f01fff81c5 0xfcfffe1e03fff038

def z299 : W := mkw 0x029e8c88aa7ae16a 0xa053d191154f5c2d 0xef9f8c88ffffe1ff 0xfdf3f1911ffffc3f

def z300 : W := mkw 0x17fdffeed5850004 0x02ffbffddab0a000 0xd7ffffffe1c78003 0xfafffffffc38f000

def z301 : W := mkw 0x023e051d1b383ab1 0xc047c0a3a3670756 0xfe7e0fff1f387ffe 0xffcfc1ffe3e70fff

def z302 : W := mkw 0x15e1fae2d5850004 0x02bc3f5c5ab0a000 0x01e1f0f0e1c78001 0x403c3e1e1c38f000

def z303 : W := mkw 0x0214010402100200 0x4042802080420040 0x0600030006000600 0x00c0006000c000c0

def z304 : W := mkw 0x8d6230337da618dd 0x11ac46066fb4c31b 0xffe670ffffe619ff 0xfffcce1ffffcc33f

def z305 : W := mkw 0x17dfffeeca350004 0x02fbfffdd946a000 0xd7ffffffe03f8003 0xfafffffffc07f000

def z306 : W := mkw 0x056210001fb50004 0x00ac420003f6a000 0xe7e000001fff8004 0x7cfc000003fff000

def z307 : W := mkw 0x0002000108200810 0x0000400021040102 0x080000001820183c 0x0100000003040307

def z308 : W := mkw 0x0080088000404102 0x0010011000080820 0xff800f801fc07fc6 0x7ff001f003f80ff8

def z309 : W := mkw 0x07fc0fdc17d877a3 0xc0ff81fb82fb0ef4 0xfff80ff01fd87fc6 0x7fff01fe03fb0ff8

def z310 : W := mkw 0x021e050d08200810 0x0043c0a1a1040102 0xde1e0f0f1820183e 0xbbc3c1e1e3040307

def z311 : W := mkw 0x1088afefc0082a30 0xc21115fdf8010546 0x18000fffe0007e3a 0x030001fffc000fc7

def z312 : W := mkw 0x0755400006910000 0x00eaa80000d22000 0xe799800007ff8005 0xdcf3300000fff000

def z313 : W := mkw 0x00a88c98b14af1eb 0xa015119316295e3d 0xf9f98cf8f9fff9ff 0xff3f319f1f3fff3f

def z314 : W := mkw 0x9fffffffffb718dd 0x13fffffffff6e31b 0xffffffffffff99ff 0xfffffffffffff33f

def z315 : W := mkw 0x0000000000000000 0x0000000000000000 0x4066700000000001 0xe80cce0000000000

def z316 : W := mkw 0x029c8d8c8258e322 0xe05391b1904b1c64 0xa7998f0006d9e600 0x14f331e000db3cc0

def z317 : W := mkw 0x05e80ed815c875a3 0x80bd01db02b90eb4 0xfff80ff81ff87ffe 0xffff01ff03ff0fff

def z318 : W := mkw 0x021c050c02182220 0xc04380a180430444 0x0018000000180000 0x0003000000030000

def z319 : W := mkw 0x021600000a300000 0x0042c00001460000 0xe61e00001e380004 0xbcc3c00003c70000

def z320 : W := mkw 0x17dfefefc8200810 0x02fbfdfdf9040102 0xdffffffff820183f 0xfbffffffff040307

def z321 : W := mkw 0x05e1d880b5c7c14e 0x20bc3b1016b8f829 0x01e1f080e1c781c1 0x403c3e101c38f038

def z322 : W := mkw 0x05e0088015c04102 0x00bc011002b80820 0xefe00c801fc061c6 0x7dfc019003f80c38

def z323 : W := mkw 0x021c050c00000000 0x004380a180000000 0x001e000f00000000 0x8003c001e0000000

def z324 : W := mkw 0x00888c888048e122 0xa011119110091c24 0xe1998c88e0d9e003 0xdc3331911c1b3c00

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x506000f000000002 0x6a0c001e00000000

def z326 : W := mkw 0x05c00ac004c04502 0x00b80158009808a0 0xf7e00ff006c06602 0x7efc01fe00d80cc0

def z327 : W := mkw 0x1000236640000000 0x0200046cc8000000 0x1000037700000000 0x0200006ee0000000

def z328 : W := mkw 0x0088acaae04ae16a 0xa01115955c095c2d 0xf9fffcffe1ffe1ff 0xff3fff9ffc3ffc3f

def z329 : W := mkw 0x07ddcc8880000000 0x00fbb99110000000 0xc7fffc88e0000003 0xf8ffff911c000000

def z330 : W := mkw 0x00a0089011405183 0x0014011202280a30 0xf9e00cf019c079c6 0x7f3c019e03380f38

def z331 : W := mkw 0x17fdeffed5c05583 0x02ffbdffdab80ab0 0xd7ffffffe1c001c3 0xfafffffffc380038

def z332 : W := mkw 0x8a3631377b361add 0x5146c626ef66c35b 0x5e6673ffff261fff 0xebccce7fffe4c3ff

def z333 : W := mkw 0x021e04080a382020 0x8043c08101470404 0xee1e0c081e38603e 0xbdc3c18103c70c07

def z334 : W := mkw 0x002210001fb50004 0x0004420003f6a000 0xe19980001fff8005 0xdc33300003fff000

def z335 : W := mkw 0x023610001b340004 0x0046c20003668000 0xe67e70001f3e0005 0xfccfce0003e7c000

def z336 : W := mkw 0x000200010a382a30 0xc000400021470546 0x0000000000380038 0x0000000000070007

def z337 : W := mkw 0x002210011fbd2a34 0xc004420023f7a546 0x280000001ffffe3c 0x0500000003ffffc7

def z338 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xe67e70001e380004 0xbccfce0003c70000

def z339 : W := mkw 0x021f550d0a3d2a34 0xc043eaa1a147a546 0xfe1fff0f1e3ffe3f 0xbfc3ffe1e3c7ffc7

def z340 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x97998fffe0000002 0x12f331fffc000000

def z341 : W := mkw 0x17ddefeee0020048 0x02fbbdfddc004009 0xdfffffffe12601ff 0xfbfffffffc24c03f

def z342 : W := mkw 0x8d6370337da718dd 0x11ac6e066fb4e31b 0x59e7f0fff9e799ff 0xeb3cfe1fff3cf33f

def z343 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xe61e000f1e38003c 0xbcc3c001e3c70007

def z344 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x1e060f0f1e007e3a 0x23c0c1e1e3c00fc7

def z345 : W := mkw 0x0755400006910000 0x00eaa80000d22000 0x0600000006000000 0x00c0000000c00000

def z346 : W := mkw 0x8822303359241895 0x110446066b248312 0x5066707719261805 0xea0cce0ee324c300

def z347 : W := mkw 0x1080aae2c0000000 0x0210155c58000000 0x000000f0e0000000 0x0000001e1c000000

def z348 : W := mkw 0x882a343b792e38fd 0x910546876f25c71f 0xf87e7cfff93e79ff 0xff0fcf9fff27cf3f

def z349 : W := mkw 0x0000000000000000 0x0000000000000000 0x00198000003f8001 0x800330000007f000

def z350 : W := mkw 0x17d56be640000000 0x02faad7cc8000000 0xd7e67ff700000002 0x7afccffee0000000

def z351 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xffffff001ffffe07 0xffffffe003ffffc0

def z352 : W := mkw 0x17dfefefea7aeb7a 0xe2fbfdfdfd4f5d6f 0xffffffffffffffff 0xffffffffffffffff

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0xe60000001e000004 0x3cc0000003c00000

def z354 : W := mkw 0x88002033600218d9 0x110004066c00431b 0x586670ffe00019fb 0xeb0cce1ffc00033f

def z355 : W := mkw 0x07f60bd51ff05f93 0x40fec17aa3fe0bf2 0xffe60ff71fc07fc6 0x7ffcc1fee3f80ff8

def z356 : W := mkw 0x075f450d0a382a30 0xc0ebe8a1a1470546 0xffffff0f1e387e3f 0xffffffe1e3c70fc7

def z357 : W := mkw 0x00a88c98b5caf5eb 0xa015119316b95ebd 0xe9998c88ffffffff 0xdd3331911fffffff

def z358 : W := mkw 0x008a8c89aa7aeb7a 0xe0115191354f5d6f 0xe9998c88ffffffff 0xdd3331911fffffff

def z359 : W := mkw 0x00088408a00aa068 0xa00110811401540d 0x48198088e13f81ff 0xc90330111c27f03f

def z360 : W := mkw 0x07de0fcd0a382a30 0xc0fbc1f9a1470546 0xfffe0fff1e387e3e 0xffffc1ffe3c70fc7

def z361 : W := mkw 0x00008000a0028048 0x2000100014005009 0x00018000e0078001 0x000030001c00f000

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0xa6000f0006006600 0x14c001e000c00cc0

def z363 : W := mkw 0x17ddcfcc80000000 0x02fbb9f990000000 0xd7f98ff000000002 0x7aff31fe00000000

def z364 : W := mkw 0x1008a52ec0000000 0x020114a5d8000000 0x0000000fe0000000 0x00000001fc000000

def z365 : W := mkw 0x00888ed8a04af5eb 0xa01111db14095ebd 0x18000ff8e0007ffa 0x030001ff1c000fff

def z366 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x29e000f01fc07fc4 0x453c001e03f80ff8

def z367 : W := mkw 0x00800880204ae16a 0xa010011004095c2d 0xe9800c8001ffe1fe 0x5d300190003ffc3f

def z368 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa79980001fff8004 0x14f3300003fff000

def z369 : W := mkw 0x0020001015801481 0x0004000202b00290 0x000000001e001e00 0x0000000003c003c0

def z370 : W := mkw 0x05e88ed895c05583 0x00bd11db12b80ab0 0xfff98ff8ffc07fc7 0xffff31ff1ff80ff8

def z371 : W := mkw 0x00a0089015c05583 0x0014011202b80ab0 0xe9800c801fc07fc6 0x5d30019003f80ff8

def z372 : W := mkw 0x0000000004c04502 0x00000000009808a0 0x2000000006c06600 0x0400000000d80cc0

def z373 : W := mkw 0x0000202240000000 0x0000040448000000 0x006070f0e0000001 0x400c0e1e1c000000

def z374 : W := mkw 0x8de02af375c25ddb 0x11bc055e6eb84bbb 0xffe00fffffc07ffe 0x7ffc01fffff80fff

def z375 : W := mkw 0x0560025015801481 0x00ac004a02b00290 0x0060007000000000 0x000c000e00000000

def z376 : W := mkw 0x88a0b8b2f146d1cf 0x311417165e28da39 0x01e1f0f0e1c781c1 0x403c3e1e1c38f038

def z377 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x09818c88e1c7e1fb 0x413031911c38fc3f

def z378 : W := mkw 0x0214000000000000 0x0042800000000000 0xc61e000000000000 0xb8c3c00000000000

def z379 : W := mkw 0x00800ac000404502 0x00100158000808a0 0x00000f0000006600 0x000001e000000cc0

def z380 : W := mkw 0x17ffffeeffffe16e 0xa2fffffddffffc2d 0xffffffffffffe1ff 0xfffffffffffffc3f

def z381 : W := mkw 0x0775500017950004 0x00eeaa0002f2a000 0xa7f9f00007df8001 0x54ff3e0000fbf000

def z382 : W := mkw 0x00088408a00aa068 0xa00110811401540d 0xe1998008e1ff803d 0xdc3330011c3ff007

def z383 : W := mkw 0x0560025015801481 0x00ac004a02b00290 0xf7e003701fc01e04 0x7efc006e03f803c0

def z384 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x48000088f92619ff 0xc90000111f24c33f

def z385 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x106670f7f90619c1 0x620cce1eff20c338

def z386 : W := mkw 0x00000000204ae16a 0xa000000004095c2d 0x08000000000061f8 0x0100000000000c3f

def z387 : W := mkw 0x0000000020020048 0x0000000004004009 0x08000088e00001fa 0x010000111c00003f

def z388 : W := mkw 0x021e050c0a300000 0x0043c0a181460000 0xf61e0f0f1e380006 0xbec3c1e1e3c70000

def z389 : W := mkw 0x17ddcfcc86910000 0x02fbb9f990d22000 0xa7998f0006d98000 0x14f331e000db3000

def z390 : W := mkw 0x9fddefffe00218d9 0x13fbbdfffc00431b 0xdfffffffe00019fb 0xfbfffffffc00033f

def z391 : W := mkw 0x021c050c00000000 0x004380a180000000 0xfe1e0f0f1e007e06 0xbfc3c1e1e3c00fc0

def z392 : W := mkw 0x07f54ad015c05583 0x00fea95a02b80ab0 0xfffffff01fc07fc7 0xfffffffe03f80ff8

def z393 : W := mkw 0x0000000000404102 0x0000000000080820 0x2800000001c061c4 0x0500000000380c38

def z394 : W := mkw 0x05c88ec884c8e522 0xa0b911d910991ca4 0xa7998f0006d9e600 0x14f331e000db3cc0

def z395 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x48000c88e12661ff 0xc90001911c24cc3f

def z396 : W := mkw 0x056350001fb50004 0x00ac6a0003f6a000 0x21e1f0001fff8005 0x443c3e0003fff000

def z397 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x1e600ff01e007fc2 0x23cc01fe03c00ff8

def z398 : W := mkw 0x88223032792610cd 0x110446064f24c219 0x406670f0f92601c5 0xe80cce1e1f24c038

def z399 : W := mkw 0x0020203251001081 0x000404064a200210 0x586670fff90019c7 0xeb0cce1fff200338

def z400 : W := mkw 0x121fe52fca382a30 0xc243fca5f9470546 0xfe1fff0ffe387e3f 0xbfc3ffe1ffc70fc7

def z401 : W := mkw 0x0540000000000000 0x00a8000000000000 0xc7e0000000000000 0x78fc000000000000

def z402 : W := mkw 0x077751051fb50a14 0x40eeea20a3f6a142 0xf7fff3071fff9e05 0xfefffe60e3fff3c0

def z403 : W := mkw 0x002210001fb50004 0x0004420003f6a000 0x000000001e000000 0x0000000003c00000

def z404 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x59e000f019c019c6 0x6b3c001e03380338

def z405 : W := mkw 0x88023033682618dd 0x110046066d04c31b 0x180670ffe02619fb 0x8300ce1ffc04c33f

def z406 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x586000f0192619fe 0x6b0c001e0324c33f

def z407 : W := mkw 0x07f54ad017d15583 0x00fea95a02fa2ab0 0xfff98ff01fd9ffc6 0x7fff31fe03fb3ff8

def z408 : W := mkw 0x8f7770335fb51895 0x11eeee066bf6a312 0xf7fff0771fff9805 0xfefffe0ee3fff300

def z409 : W := mkw 0x021c252e40000000 0x004384a5c8000000 0xd67e7fffe0000003 0xfacfcffffc000000

def z410 : W := mkw 0x17ddcfcc80000000 0x02fbb9f990000000 0xc7998f88e0000003 0xd8f331f11c000000

def z411 : W := mkw 0x05e88ed8b5caf5eb 0xa0bd11db16b95ebd 0xe9f98cf8e1ffe1ff 0xdd3f319f1c3ffc3f

def z412 : W := mkw 0x17fdcfdc95c05583 0x02ffb9fb92b80ab0 0xfff98ff01fc07fc6 0x7fff31fe03f80ff8

def z413 : W := mkw 0x15c1eae2e042c14a 0x22b83d5c5c085829 0x01e1f0f0e1c781c1 0x403c3e1e1c38f038

def z414 : W := mkw 0x077f54081fbd2024 0x80efea8103f7a404 0xeffffc081fffe03f 0xfdffff8103fffc07

def z415 : W := mkw 0x07ddcc88a04ae16a 0xa0fbb99114095c2d 0xeffffc88e1ffe1ff 0xfdffff911c3ffc3f

def z416 : W := mkw 0x021e850daa3aaa78 0xe043d0a1b547554f 0xfe1f8f0ffe3ffe3f 0xbfc3f1e1ffc7ffc7

def z417 : W := mkw 0x9f777377792618dd 0x13eeee6eef24c31b 0x5e6673fff92619ff 0xebccce7fff24c33f

def z418 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x281e000f1e387e3c 0x8503c001e3c70fc7

def z419 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xe9e00cf001c061c6 0x5d3c019e00380c38

def z420 : W := mkw 0x029e8d8d8a78eb32 0xe053d1b1b14f1d66 0xff9f8f0f1ef9fe3e 0xbff3f1e1e3df3fc7

def z421 : W := mkw 0x075740000a300000 0x00eae80001460000 0xe7fff0001e380005 0xfcfffe0003c70000

def z422 : W := mkw 0x88201010310610cd 0x110402020620c219 0x00000000010601c0 0x000000000020c038

def z423 : W := mkw 0x05e15ad015c55587 0x00bc2b5a02b8aab0 0x01e1f0f001c781c1 0x403c3e1e0038f038

def z424 : W := mkw 0x0000000020020048 0x0000000004004009 0x00000080e10601c1 0x400000101c20c038

def z425 : W := mkw 0x077750003fffe16e 0xa0eeea0007fffc2d 0xeffff0001fffe1fd 0xfdfffe0003fffc3f

def z426 : W := mkw 0x0022100019240004 0x0004420003248000 0xe1fff00019ff8005 0xfc3ffe00033ff000

def z427 : W := mkw 0x056210001da40004 0x00ac420003b48000 0xe7e670001fe60005 0xfcfcce0003fcc000

def z428 : W := mkw 0x88a23af379665ddf 0x1114475e6f2ccbbb 0x58667ffff9267fff 0xeb0ccfffff24cfff

def z429 : W := mkw 0x0022302259240004 0x000446044b248000 0x506670fff9260007 0xea0cce1fff24c000

def z430 : W := mkw 0x15c9efeec0000000 0x02b93dfdd8000000 0x11e1ffffe0000003 0x423c3ffffc000000

def z431 : W := mkw 0x8d6232737da61cdd 0x11ac464e6fb4c39b 0x5e6673ffff261fff 0xebccce7fffe4c3ff

def z432 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0xe7e1f0001fc78005 0x7cfc3e0003f8f000

def z433 : W := mkw 0x00088408a00aa068 0xa00110811401540d 0xe8198c08e03fe03f 0x9d0331811c07fc07

def z434 : W := mkw 0x0020001035caf5eb 0xa004000206b95ebd 0x280000001ffffffc 0x0500000003ffffff

def z435 : W := mkw 0x021600010a300810 0x0042c00021460102 0xfe1e000f1e38183e 0xbfc3c001e3c70307

def z436 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x0806700ff92619fd 0x8100ce01ff24c33f

def z437 : W := mkw 0x0008040800082020 0x8001008100010404 0x0018000800380038 0x8003000100070007

def z438 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x87f9fff0e0000001 0x50ff3ffe1c000000

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0xe180000001c00004 0x5c30000000380000

def z440 : W := mkw 0x000884088008a020 0xa001108110011404 0x0019800000198000 0x0003300000033000

def z441 : W := mkw 0x8a3630337b3618dd 0x1146c6066f66c31b 0xfe7e70ffff3e19ff 0xffcfce1fffe7c33f

def z442 : W := mkw 0x0215400000000000 0x0042a80000000000 0x001ff00000000001 0x8003fe0000000000

def z443 : W := mkw 0x077603551fb01e91 0x40eec06aa3f603d2 0x166603771e001e00 0x22ccc06ee3c003c0

def z444 : W := mkw 0x07f60ad01ff05583 0x00fec15a03fe0ab0 0xfffe0ff01ff87fc6 0xffffc1fe03ff0ff8

def z445 : W := mkw 0x8a3631375b341a95 0x5146c626eb668352 0x166673771e001e00 0x22ccce6ee3c003c0

def z446 : W := mkw 0x121de52ec0000000 0x0243bca5d8000000 0xd61fff0fe0000003 0xbac3ffe1fc000000

def z447 : W := mkw 0x0777500019240004 0x00eeea0003248000 0xc7fff00019260005 0xf8fffe000324c000

def z448 : W := mkw 0x077752501fb51485 0x00eeea4a03f6a290 0x166673701e001e00 0x22ccce6e03c003c0

def z449 : W := mkw 0x0560000015800000 0x00ac000002b00000 0xe7f980001fff8005 0xfcff300003fff000

def z450 : W := mkw 0x0080088000000000 0x0010011000000000 0xc1800c8000000002 0x5830019000000000

def z451 : W := mkw 0x021601050a382a30 0xc042c020a1470546 0x3e0603071e387e3c 0x27c0c060e3c70fc7

def z452 : W := mkw 0x021600000a300000 0x0042c00001460000 0x001e000000380000 0x8003c00000070000

def z453 : W := mkw 0x07ddcc8886d9e122 0xa0fbb99110db3c24 0xa7998c0006d9e000 0x14f3318000db3c00

def z454 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x18667077192619fc 0x230cce0ee324c33f

def z455 : W := mkw 0x05e00ad035caf5eb 0xa0bc015a06b95ebd 0xffe00ff01ffffffe 0x7ffc01fe03ffffff

def z456 : W := mkw 0x88002032600210c9 0x110004064c004219 0x000000f0e00001c0 0x0000001e1c000038

def z457 : W := mkw 0x07d54ac006d14502 0x00faa95800da28a0 0xa7998f0006d9e600 0x14f331e000db3cc0

def z458 : W := mkw 0x88a2b8b3f966d9df 0x311457167f2cdb3b 0x59e7f0fff9e799ff 0xeb3cfe1fff3cf33f

def z459 : W := mkw 0x880210012826085c 0x110042002504c10b 0x0000000000260038 0x000000000004c007

def z460 : W := mkw 0x002210003fffe16e 0xa004420007fffc2d 0x280000001fffe1fc 0x0500000003fffc3f

def z461 : W := mkw 0x8de03af275c655cf 0x11bc075e4eb8cab9 0xffe07ff0ffc67fc7 0x7ffc0ffe1ff8cff8

def z462 : W := mkw 0x8a1770236a37085c 0x1142ee046d46e10b 0x001ff00fe03f8039 0x8003fe01fc07f007

def z463 : W := mkw 0x88203032710610cd 0x110406064e20c219 0x586070f0f90619c7 0x6b0c0e1e1f20c338

def z464 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x266670001fff8004 0x24ccce0003fff000

def z465 : W := mkw 0x8f7750113fb718dd 0x11eeea0227f6e31b 0xeffff0001fff99fd 0xfdfffe0003fff33f

def z466 : W := mkw 0x077f550d1fbd2a34 0xc0efeaa1a3f7a546 0xe7fff00f1fff803d 0xfcfffe01e3fff007

def z467 : W := mkw 0x00080408204ae16a 0xa001008104095c2d 0xe8180c0801ffe1fe 0x9d030181003ffc3f

def z468 : W := mkw 0x15e1eaf2d5c05583 0x02bc3d5e5ab80ab0 0xffe1fff0ffc07fc7 0x7ffc3ffe1ff80ff8

def z469 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x5806000f192619fe 0xab00c001e324c33f

def z470 : W := mkw 0x021601050a300a10 0x4042c020a1460142 0xfe060f071e007e06 0x3fc0c1e0e3c00fc0

def z471 : W := mkw 0x1088afeec0000000 0x021115fdd8000000 0xd1998fffe0000003 0xda3331fffc000000

def z472 : W := mkw 0x0775400015800000 0x00eea80002b00000 0xe7fff0001fc00005 0xfcfffe0003f80000

def z473 : W := mkw 0x021fd408aa3fa06c 0xa043fa811547f40d 0x001ff008e03f8039 0x8003fe011c07f007

def z474 : W := mkw 0x05e88ed8b5caf5eb 0xa0bd11db16b95ebd 0xffe00ff8ffc07ffe 0x7ffc01ff1ff80fff

def z475 : W := mkw 0x00888c8880000000 0x0011119110000000 0x00000c88e0000002 0x000001911c000000

def z476 : W := mkw 0x00888c888048e122 0xa011119110091c24 0x00000c0000006000 0x0000018000000c00

def z477 : W := mkw 0x0000202260020048 0x000004044c004009 0x586670ffe12601ff 0xeb0cce1ffc24c03f

def z478 : W := mkw 0x175763674a300a10 0x42eaec6ce9460142 0x166673771e001e00 0x22ccce6ee3c003c0

def z479 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xa7e00ff007c067c0 0x54fc01fe00f80cf8

def z480 : W := mkw 0x0540000004800000 0x00a8000000900000 0xa780000006c00000 0x14f0000000d80000

def z481 : W := mkw 0x023e150d1b3c2a34 0xc047c2a1a3678546 0xfe7e7f0f1f3e7e3f 0xffcfcfe1e3e7cfc7

def z482 : W := mkw 0x021c050c00082020 0x804380a180010404 0xfe1e0f0f0038603e 0xbfc3c1e1e0070c07

def z483 : W := mkw 0x8a3770337b3718dd 0x1146ee066f66e31b 0x587ff0fff93f99ff 0xeb0ffe1fff27f33f

def z484 : W := mkw 0x00aa9c88b96ee16e 0xa0155391172ddc2d 0xe9fffc88f9ffe1ff 0xfd3fff911f3ffc3f

def z485 : W := mkw 0x8de21ad13de65ddf 0x11bc435a27bccbbb 0xffe00ff01fe67ffe 0x7ffc01fe03fccfff

def z486 : W := mkw 0x0002000008200000 0x0000400001040000 0x4006000018200004 0xa800c00003040000

def z487 : W := mkw 0x0022100119240814 0x0004420023248102 0x5866700f1926183f 0xeb0cce01e324c307

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0xd6000f0000000002 0x3ac001e000000000

def z489 : W := mkw 0x17ddeffec0405583 0x02fbbdffd8080ab0 0xdfffffffe0007fc3 0xfbfffffffc000ff8

def z490 : W := mkw 0x0002000108200810 0x0000400021040102 0x0006000f00200038 0x8000c001e0040007

def z491 : W := mkw 0x00080408200a2068 0x800100810401440d 0xe8180c88e13e61ff 0xdd0301911c27cc3f

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8000c0000006006 0x1d00018000000c00

def z493 : W := mkw 0x17d5ebe6c0000000 0x02fabd7cd8000000 0x17e7f3f7e0000001 0x62fcfe7efc000000

def z494 : W := mkw 0x07ffdc889ffde126 0xa0fffb9113ffbc24 0xe7fffc001fffe005 0xfcffff8003fffc00

def z495 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0x0060700000000000 0x000c0e0000000000

def z496 : W := mkw 0x00800ad000405583 0x0010015a00080ab0 0xf9800ff001c07fc6 0x5f3001fe00380ff8

def z497 : W := mkw 0x023610001fb50004 0x0046c20003f6a000 0xe61e00001fff8004 0xbcc3c00003fff000

def z498 : W := mkw 0x000210000a350004 0x000042000146a000 0x00000000003f8000 0x000000000007f000

def z499 : W := mkw 0x15c8afeec0000000 0x02b915fdd8000000 0xd7e00fffe0000002 0x7afc01fffc000000

def z500 : W := mkw 0x07f75ac01ff54506 0x00feeb5803fea8a0 0xe7ffff001fffe605 0xfcffffe003fffcc0

def z501 : W := mkw 0x021c050d02182a30 0xc04380a1a0430546 0xbe180f0f06187e3a 0x17c301e1e0c30fc7

def z502 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x97ffff7700000000 0x32ffffeee0000000

def z503 : W := mkw 0x17dfefefca300a10 0x42fbfdfdf9460142 0xd7fffffffe001e03 0xfaffffffffc003c0

def z504 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xb61e0f071e187e00 0x36c3c1e0e3c30fc0

def z505 : W := mkw 0x00880fdd00487fb3 0xc01101fba0090ff6 0x18000fff00007ffa 0x030001ffe0000fff

def z506 : W := mkw 0x029c8d8ca25ae36a 0xe05391b1944b5c6d 0xef998f88e7ffe7ff 0xddf331f11cfffcff

def z507 : W := mkw 0x98aabffff92618dd 0x131557ffff24c31b 0x58667ffff92619ff 0xeb0ccfffff24c33f

def z508 : W := mkw 0x17ddcfcca04ae16a 0xa2fbb9f994095c2d 0xef998f88e1ffe1ff 0xddf331f11c3ffc3f

def z509 : W := mkw 0x077fd408bfbfa06c 0xa0effa8117f7f40d 0xe7fff008ffff803d 0xfcfffe011ffff007

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x480000080020003e 0x8900000100040007

def z511 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xf9fff0fff9ff99ff 0xff3ffe1fff3ff33f

def z512 : W := mkw 0x0000000020020048 0x0000000004004009 0x00000008e0260039 0x800000011c04c007

def z513 : W := mkw 0x8a3e353f792618dd 0x1147c6a7ef24c31b 0xde7e7ffff92619ff 0xfbcfcfffff24c33f

def z514 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xc9998c88e00061fb 0xd93331911c000c3f

def z515 : W := mkw 0x121de52ee00aa068 0xa243bca5dc01540d 0x001ff00fe03f8039 0x8003fe01fc07f007

def z516 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x466670001f260005 0xe8ccce0003e4c000

def z517 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xd7e00ff001c001c2 0x7afc01fe00380038

def z518 : W := mkw 0x9de3faf3f92618dd 0x13bc7f5e7f24c31b 0x59e7f0fff92619ff 0xeb3cfe1fff24c33f

def z519 : W := mkw 0x0215400002110000 0x0042a80000422000 0x0019800000198000 0x0003300000033000

def z520 : W := mkw 0x9888afffe00218d9 0x131115fffc00431b 0x18000fffe00019fa 0x030001fffc00033f

def z521 : W := mkw 0x88022033682218d9 0x110044066d04431b 0x580600fff82019fe 0xab00c01fff04033f

def z522 : W := mkw 0x075d450c06992220 0xc0eba8a180d32444 0xa7998f0006d9e600 0x14f331e000db3cc0

def z523 : W := mkw 0x00888d8da04aeb7a 0xe01111b1b4095d6f 0xf9998f8fe1ffffff 0xdf3331f1fc3fffff

def z524 : W := mkw 0x00888c8880404102 0x0011119110080820 0xe9998c88e1c061c7 0xdd3331911c380c38

def z525 : W := mkw 0x0000000000082020 0x8000000000010404 0x280000000038603c 0x0500000000070c07

def z526 : W := mkw 0x8a3e353f7b3e3afd 0xd147c6a7ef67c75f 0x587e70fff93e19ff 0xeb0fce1fff27c33f

def z527 : W := mkw 0x029fdc88aa7fe16e 0xa053fb91154ffc2d 0xe99ffc88e1ffe1ff 0xdd33ff911c3ffc3f

def z528 : W := mkw 0x8f777033792618dd 0x11eeee066f24c31b 0xdffff0fff92619ff 0xfbfffe1fff24c33f

def z529 : W := mkw 0x9a1ff52fe826085c 0x1343fea5fd04c10b 0x001ff00fe0260039 0x8003fe01fc04c007

def z530 : W := mkw 0x077e075d1fb83eb1 0xc0efc0eba3f707d6 0xfe7e0f7f1e387e3e 0xbfcfc1efe3c70fc7

def z531 : W := mkw 0x129dedaec0000000 0x0253bdb5d8000000 0xc19ffc8fe0000003 0xd833ff91fc000000

def z532 : W := mkw 0x88203033710618dd 0x110406066e20c31b 0x186070ffe10619fb 0x430c0e1ffc20c33f

def z533 : W := mkw 0x021c050c00000000 0x004380a180000000 0x86180f0000000000 0x10c301e000000000

def z534 : W := mkw 0x0775400017910000 0x00eea80002f22000 0xe7f980001fd98004 0x7cff300003fb3000

def z535 : W := mkw 0x00aa9c88bfffe16e 0xa015539117fffc2d 0xe9998c88ffffe1ff 0xdd3331911ffffc3f

def z536 : W := mkw 0x077750101ff55587 0x00eeea0203feaab0 0xeffff0001fffffc5 0xfdfffe0003fffff8

def z537 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xe81e0c0f0038603e 0x9d03c181e0070c07

def z538 : W := mkw 0x00808880a042c14a 0x2010111014085829 0xe1998080e1ff81c5 0xdc3330101c3ff038

def z539 : W := mkw 0x17fdefeed5800000 0x02ffbdfddab00000 0xf7ffffffffc00007 0xfefffffffff80000

def z540 : W := mkw 0x05e21ad01de45587 0x00bc435a03bc8ab0 0xffe67ff01fe67fc7 0xfffccffe03fccff8

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x0181800001c78001 0x403030000038f000

def z542 : W := mkw 0x17dfefeeca300000 0x02fbfdfdd9460000 0xf7fffffffe380007 0xfeffffffffc70000

def z543 : W := mkw 0x8ffffcbbfffff9ff 0xb1ffff977fffff3f 0xfffffcfffffff9ff 0xffffff9fffffff3f

def z544 : W := mkw 0x0008040800082020 0x8001008100010404 0xfe180f081e387e3e 0xbfc301e103c70fc7

def z545 : W := mkw 0x00888c8880000000 0x0011119110000000 0x81998c0000000000 0x1033318000000000

def z546 : W := mkw 0x0000202240000000 0x0000040448000000 0x1066707700000000 0x220cce0ee0000000

def z547 : W := mkw 0x0000010500000a10 0x40000020a0000142 0x1000030700001e00 0x02000060e00003c0

def z548 : W := mkw 0x88203032710610cd 0x110406064e20c219 0x486070f8e12601ff 0xc90c0e1f1c24c03f

def z549 : W := mkw 0x17ffffeedfb50004 0x02fffffddbf6a000 0xd7fffffffe000003 0xfaffffffffc00000

def z550 : W := mkw 0x021600000a300000 0x0042c00001460000 0xfe1e0f001e387e06 0xbfc3c1e003c70fc0

def z551 : W := mkw 0x9a3ff53ff92618dd 0x1347fea7ff24c31b 0x587ff0fff92619ff 0xeb0ffe1fff24c33f

def z552 : W := mkw 0x021c050c02182220 0xc04380a180430444 0xfe180f001e187e06 0x3fc301e003c30fc0

def z553 : W := mkw 0x0000001000001081 0x0000000200000210 0x180000f0000019c2 0x0300001e00000338

def z554 : W := mkw 0x05e00ac015800000 0x00bc015802b00000 0xf7e00ff01fc00006 0x7efc01fe03f80000

def z555 : W := mkw 0x17ddcfcc84c04502 0x02fbb9f9909808a0 0xa7998f0006c06600 0x14f331e000d80cc0

def z556 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x28000c88e1ffe1fe 0x050001911c3ffc3f

def z557 : W := mkw 0x9f77737759241895 0x13eeee6eeb248312 0x1666737718001800 0x22ccce6ee3000300

def z558 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xa61e0f0f06386638 0x94c3c1e1e0c70cc7

def z559 : W := mkw 0x8822303359241895 0x110446066b248312 0x586670f7190019c6 0x6b0cce1ee3200338

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000001260005 0xc80000000024c000

def z561 : W := mkw 0x05c00ac004c04502 0x00b80158009808a0 0xff800f001ec07e06 0x3ff001e003d80fc0

def z562 : W := mkw 0x0008050c00000000 0x000100a180000000 0x10000f0f00000002 0x020001e1e0000000

def z563 : W := mkw 0x17ffdfcc9fb50004 0x02fffbf993f6a000 0xe7ffff001fff8005 0xfcffffe003fff000

def z564 : W := mkw 0x882210113fb718dd 0x1104420227f6e31b 0x280000001fff99fc 0x0500000003fff33f

def z565 : W := mkw 0x17f56bf655c05583 0x02fead7ecab80ab0 0xffe67ff71fc07fc6 0x7ffccffee3f80ff8

def z566 : W := mkw 0x05e9dc88b5cfe16e 0xa0bd3b9116b9fc2d 0xe9f9fc88e1ffe1ff 0xdd3f3f911c3ffc3f

def z567 : W := mkw 0x8f7770237fb7085c 0x11eeee046ff6e10b 0xe7fff00fffff803d 0xfcfffe01fffff007

def z568 : W := mkw 0x07f75ad01ff55587 0x00feeb5a03feaab0 0xffe67ff01fc07fc6 0x7ffccffe03f80ff8

def z569 : W := mkw 0x029e8d8d8a382a30 0xc053d1b1b1470546 0xff9f8f8ffe387e3f 0xfff3f1f1ffc70fc7

def z570 : W := mkw 0x0002100008240004 0x0000420001048000 0x0006700000260001 0x8000ce000004c000

def z571 : W := mkw 0x000000002042c14a 0x2000000004085829 0x0000000001c781c0 0x000000000038f038

def z572 : W := mkw 0x05c00ac000000000 0x00b8015800000000 0xffe00ff01e007e06 0x7ffc01fe03c00fc0

def z573 : W := mkw 0x021600000a300000 0x0042c00001460000 0xe79f80001fff8005 0xfcf3f00003fff000

def z574 : W := mkw 0x07dc0fcc00000000 0x00fb81f980000000 0xd7fe0fff00000002 0xfaffc1ffe0000000

def z575 : W := mkw 0x0020001011001081 0x0004000202200210 0x006000f0010001c0 0x400c001e00200038

def z576 : W := mkw 0x0008040800000000 0x0001008100000000 0xc0180c0800000002 0x9803018100000000

def z577 : W := mkw 0x002210001fb50004 0x0004420003f6a000 0x606670001fff8005 0xec0cce0003fff000

def z578 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x07e7f0001fc78001 0x60fcfe0003f8f000

def z579 : W := mkw 0x17ffffefdfbd2a34 0xc2fffffdfbf7a546 0xfffffffffffffe3f 0xffffffffffffffc7

def z580 : W := mkw 0x000200010a382a30 0xc000400021470546 0xfe000f001e387e3e 0x3fc001e003c70fc7

def z581 : W := mkw 0x00888d8da04aeb7a 0xe01111b1b4095d6f 0x18000f8fe0007ffa 0x030001f1fc000fff

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x48000080010001c6 0x4900001000200038

def z583 : W := mkw 0x1088afeee04ae16a 0xa21115fddc095c2d 0xf9998fffe1ffe1ff 0xdf3331fffc3ffc3f

def z584 : W := mkw 0x0008040800082020 0x8001008100010404 0xa0180c0000186000 0x1403018000030c00

def z585 : W := mkw 0x000200010a300a10 0x4000400021460142 0x000000001e001e00 0x0000000003c003c0

def z586 : W := mkw 0x05e00ad015801481 0x00bc015a02b00290 0xd7e00ff01e001e02 0x7afc01fe03c003c0

def z587 : W := mkw 0x07de0fcd0ef86f32 0xc0fbc1f9a1df0de6 0xff9e0f0f1ef87e3e 0xbff3c1e1e3df0fc7

def z588 : W := mkw 0x021c050c02182220 0xc04380a180430444 0xee180f080638663e 0x9dc301e100c70cc7

def z589 : W := mkw 0x8de23af37de65ddf 0x11bc475e6fbccbbb 0x59e670fff9e619ff 0xeb3cce1fff3cc33f

def z590 : W := mkw 0x17ddcfcc80000000 0x02fbb9f990000000 0xc7ffff0000000001 0xf8ffffe000000000

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000088e0000003 0xc80000111c000000

def z592 : W := mkw 0x17fdeffef5caf5eb 0xa2ffbdffdeb95ebd 0xffffffffffffffff 0xffffffffffffffff

def z593 : W := mkw 0x880030226006004c 0x110006044c00c009 0x00007000e0060001 0x00000e001c00c000

def z594 : W := mkw 0x021e050c0a382220 0xc043c0a181470444 0xe61e0f001e386604 0xbcc3c1e003c70cc0

def z595 : W := mkw 0x888abcabe86ee97e 0xb11157957d0ddd2f 0xe99ffc8fe1ffe1ff 0xdd33ff91fc3ffc3f

def z596 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x48667000192619fd 0xe90cce000324c33f

def z597 : W := mkw 0x17ffefffdff87fb3 0xc2fffdfffbff0ff6 0xfffffffffff87fff 0xffffffffffff0fff

def z598 : W := mkw 0x05e00ad011001081 0x00bc015a02200210 0xdfe00ff0190019c6 0x7bfc01fe03200338

def z599 : W := mkw 0x88000011200218d9 0x110000022400431b 0x08000000000019f8 0x010000000000033f

def z600 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x1066707ff8261839 0xa20cce0fff04c307

def z601 : W := mkw 0x8f7f753f7fbf3afd 0xd1efeea7eff7e75f 0xffffffffffffffff 0xffffffffffffffff

def z602 : W := mkw 0x05c88ec8a4cae56a 0xa0b911d914995cad 0xef998f88e7ffe7ff 0xddf331f11cfffcff

def z603 : W := mkw 0x077751051fb50a14 0x40eeea20a3f6a142 0x166673071e001e00 0x22ccce60e3c003c0

def z604 : W := mkw 0x077f550c1fbd2224 0xc0efeaa183f7a444 0xe7ffff001fffe605 0xfcffffe003fffcc0

def z605 : W := mkw 0x15c9eeeac0000000 0x02b93ddd58000000 0xc1f9fcf8e0000003 0xd83f3f9f1c000000

def z606 : W := mkw 0x0080088000404102 0x0010011000080820 0xe9998c8001ffe1c7 0xdd333190003ffc38

def z607 : W := mkw 0x023750001fb50004 0x0046ea0003f6a000 0x201ff0001fff8005 0x8403fe0003fff000

def z608 : W := mkw 0x0008040800082020 0x8001008100010404 0xe9998c0801ffe03f 0xdd333181003ffc07

def z609 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xe7e000f01fc001c4 0x7cfc001e03f80038

def z610 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa9998c0001ffe1fc 0x15333180003ffc3f

def z611 : W := mkw 0x88a8bcbaf14ef1ef 0xb11517975e29de3d 0xe9f9fcf8e1ffe1ff 0xdd3f3f9f1c3ffc3f

def z612 : W := mkw 0x00888c88a0020048 0x0011119114004009 0xc9998c88e12601ff 0xd93331911c24c03f

def z613 : W := mkw 0x17ddefeee04ae16a 0xa2fbbdfddc095c2d 0xdfffffffe00061fb 0xfbfffffffc000c3f

def z614 : W := mkw 0x0008050d00082a30 0xc00100a1a0010546 0x0000000f00000038 0x00000001e0000007

def z615 : W := mkw 0x0020000015800000 0x0004000002b00000 0x200000001fc00004 0x0400000003f80000

def z616 : W := mkw 0x0540024000000000 0x00a8004800000000 0x1660037000000000 0x22cc006e00000000

def z617 : W := mkw 0x0008050d00082a30 0xc00100a1a0010546 0xf8180f0f00387e3e 0x9f0301e1e0070fc7

def z618 : W := mkw 0x05c00ac004c04502 0x00b80158009808a0 0x0180000000c00000 0x0030000000180000

def z619 : W := mkw 0x075f450d0eb92a30 0xc0ebe8a1a1d72546 0xff9f8f0f1ef9fe3e 0xbff3f1e1e3df3fc7

def z620 : W := mkw 0x000000000048e122 0xa000000000091c24 0x2000000000d9e000 0x04000000001b3c00

def z621 : W := mkw 0x00808880a042c14a 0x2010111014085829 0x00000080e00001c0 0x000000101c000038

def z622 : W := mkw 0x175f676f4a382a30 0xc2ebecede9470546 0xfe7e7f7f1e387e3e 0xbfcfcfefe3c70fc7

def z623 : W := mkw 0x05e00ad035c255cb 0x00bc015a06b84ab9 0xffe00ff8ffe67fff 0xfffc01ff1ffccfff

def z624 : W := mkw 0x021600000a300000 0x0042c00001460000 0x060600001e000000 0x20c0c00003c00000

def z625 : W := mkw 0x00088408a00aa068 0xa00110811401540d 0x00000008e0000038 0x000000011c000007

def z626 : W := mkw 0x17ddefeee00aa068 0xa2fbbdfddc01540d 0xd7ffffffe03f803b 0xfafffffffc07f007

def z627 : W := mkw 0x882210113de65ddf 0x1104420227bccbbb 0x280000001fe67ffc 0x0500000003fccfff

def z628 : W := mkw 0x05c00ad004c05583 0x00b8015a00980ab0 0xbf800ff006c07fc2 0x17f001fe00d80ff8

def z629 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x17e003f01fc01fc0 0x62fc007e03f803f8

def z630 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x067ff0001e3f8001 0xa0cffe0003c7f000

def z631 : W := mkw 0x0008050c00082220 0xc00100a180010444 0x00000f0000006600 0x000001e000000cc0

def z632 : W := mkw 0x00a00ad011405583 0x0014015a02280ab0 0x58600ff019007fc6 0x6b0c01fe03200ff8

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x160003001e001e00 0x22c0006003c003c0

def z634 : W := mkw 0x17dfefefca382a30 0xc2fbfdfdf9470546 0xd7ffffffe038003b 0xfafffffffc070007

def z635 : W := mkw 0x17ddcfcc80000000 0x02fbb9f990000000 0xd79f8f0f00000002 0xbaf3f1e1e0000000

def z636 : W := mkw 0x129dedaee04ae16a 0xa253bdb5dc095c2d 0xe99ffc8fe1ffe1ff 0xdd33ff91fc3ffc3f

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x280000001e007e04 0x0500000003c00fc0

def z638 : W := mkw 0x0002202348200810 0x0000440469040102 0x586670fff820183f 0xeb0cce1fff040307

def z639 : W := mkw 0x021e850daa3aaa78 0xe043d0a1b547554f 0x001f800fe03f8039 0x8003f001fc07f007

def z640 : W := mkw 0x8a1e352f6a3e2a7c 0xd143c6a5ed47c54f 0xfe1e7f0ffe3e7e3f 0xbfc3cfe1ffc7cfc7

def z641 : W := mkw 0x000a050d0a382a30 0xc00140a1a1470546 0x38000f0f1e387e3e 0x070001e1e3c70fc7

def z642 : W := mkw 0x0000000002182220 0xc000000000430444 0x2000000006186600 0x0400000000c30cc0

def z643 : W := mkw 0x00808880a042c14a 0x2010111014085829 0x49818088e1e781ff 0xc93030111c3cf03f

def z644 : W := mkw 0x177773665fb50004 0x02eeee6ccbf6a000 0xf7fff3771fff8005 0xfefffe6ee3fff000

def z645 : W := mkw 0x17ddefeec0082020 0x82fbbdfdd8010404 0xffffffffe038603f 0xfffffffffc070c07

def z646 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa1998c08e0ffe039 0x943331811c1ffc07

def z647 : W := mkw 0x021600010a382a30 0xc042c00021470546 0xee1e00001e387e3c 0xbdc3c00003c70fc7

def z648 : W := mkw 0x000200012a7aeb7a 0xe0004000254f5d6f 0x280000001ffffffc 0x0500000003ffffff

def z649 : W := mkw 0x880230236826085c 0x110046046d04c10b 0x5806700ff826183f 0xab00ce01ff04c307

def z650 : W := mkw 0x075d450c00000000 0x00eba8a180000000 0xd7ffff0f00000003 0xfaffffe1e0000000

def z651 : W := mkw 0x88202033710218d9 0x110404066e20431b 0x586000fff90019fe 0x6b0c001fff20033f

def z652 : W := mkw 0x8de23af3792618dd 0x11bc475e6f24c31b 0xdfe67ffff92619ff 0xfbfccfffff24c33f

def z653 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0xd7fff37700000001 0xfafffe6ee0000000

def z654 : W := mkw 0x000a04090a382a30 0xc001408121470546 0xe8180c081e387e3e 0x9d03018103c70fc7

def z655 : W := mkw 0x8de23af35de45d97 0x11bc475e6bbc8bb2 0xffe67ff71fc07fc6 0x7ffccffee3f80ff8

def z656 : W := mkw 0x002200111ff87fb3 0xc004400223ff0ff6 0x280000001ff87ffc 0x0500000003ff0fff

def z657 : W := mkw 0x00808880a04ae16a 0xa010111014095c2d 0x29818080e1ffe1fd 0x453030101c3ffc3f

def z658 : W := mkw 0x05c00ac000404102 0x00b8015800080820 0xffe00ff001c061c6 0x7ffc01fe00380c38

def z659 : W := mkw 0x1001e022c0000000 0x02003c0458000000 0x0001f000e0000001 0x00003e001c000000

def z660 : W := mkw 0x129defeec0000000 0x0253bdfdd8000000 0x101fffffe0000003 0x8203fffffc000000

def z661 : W := mkw 0x8ff77af37ff75ddf 0x11feef5e6ffeebbb 0xffffffffffffffff 0xffffffffffffffff

def z662 : W := mkw 0x17ddefeee042c14a 0x22fbbdfddc085829 0xd7ffffffe1c781c3 0xfafffffffc38f038

def z663 : W := mkw 0x00888c8880082020 0x8011119110010404 0xe9998c88e038603f 0xdd3331911c070c07

def z664 : W := mkw 0x17ffffeed9240004 0x02fffffddb248000 0xd7fffffff9260007 0xfaffffffff24c000

def z665 : W := mkw 0x07fe8fddbffafffb 0xe0ffd1fbb7ff5fff 0xffff8fffffffffff 0xfffff1ffffffffff

def z666 : W := mkw 0x880230236826085c 0x110046046d04c10b 0x4806708fe12601ff 0xc900ce11fc24c03f

def z667 : W := mkw 0x0541400000000000 0x00a8280000000000 0x01e1f00000000001 0x403c3e0000000000

def z668 : W := mkw 0x0000202240000000 0x0000040448000000 0x0006700fe0000001 0x8000ce01fc000000

def z669 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x581e000f1838183e 0xab03c001e3070307

def z670 : W := mkw 0x05e02af255c05583 0x00bc055e4ab80ab0 0xffe67fffffc07fc7 0xfffccffffff80ff8

def z671 : W := mkw 0x882230337de65ddf 0x110446066fbccbbb 0x786670ffffe67fff 0xef0cce1ffffccfff

def z672 : W := mkw 0x8a1e253f6a3a3af9 0xd143c4a7ed47475f 0xfe1e0ffffe387ffe 0xbfc3c1ffffc70fff

def z673 : W := mkw 0x175d676e40000000 0x02ebacedc8000000 0xd67e7f7f00000002 0xbacfcfefe0000000

def z674 : W := mkw 0x1775637655801481 0x02eeac6ecab00290 0x166673771e001e00 0x22ccce6ee3c003c0

def z675 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa9998c88e0d9e1fa 0x153331911c1b3c3f

def z676 : W := mkw 0x077750003fb7004c 0x00eeea0007f6e009 0xeffff088ffff81ff 0xfdfffe111ffff03f

def z677 : W := mkw 0x0214000002100000 0x0042800000420000 0xa618000006180000 0x14c3000000c30000

def z678 : W := mkw 0x0020001015c05583 0x0004000202b80ab0 0x786000f01fc07fc6 0x6f0c001e03f80ff8

def z679 : W := mkw 0x882ab43bf92eb8fd 0xb10556877f25d71f 0x587ff0fff93f99ff 0xeb0ffe1fff27f33f

def z680 : W := mkw 0x0000025000001481 0x0000004a00000290 0x1000037000001e00 0x0200006e000003c0

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0xc199800000000001 0xd833300000000000

def z682 : W := mkw 0x129eafefca382a30 0xc253d5fdf9470546 0xfe1e0ffffe387e3e 0xbfc3c1ffffc70fc7

def z683 : W := mkw 0x8a3e353f5b3c3ab5 0xd147c6a7eb678756 0xfe7e7f7f1e387e3e 0xbfcfcfefe3c70fc7

def z684 : W := mkw 0x029e8d8daa7aeb7a 0xe053d1b1b54f5d6f 0xe99f8c8fe1ffe1ff 0xdd33f191fc3ffc3f

def z685 : W := mkw 0x0560000015800000 0x00ac000002b00000 0xffe00f001fc07e06 0x7ffc01e003f80fc0

def z686 : W := mkw 0x17d5eae2c0000000 0x02fabd5c58000000 0xc7fff0f0e0000001 0xf8fffe1e1c000000

def z687 : W := mkw 0x15c1cac080000000 0x02b8395810000000 0x0181800000000000 0x0030300000000000

def z688 : W := mkw 0x023750001b350004 0x0046ea000366a000 0x407ff000193f8005 0xe80ffe000327f000

def z689 : W := mkw 0x1755434400000000 0x02eaa86880000000 0x0600030000000000 0x00c0006000000000

def z690 : W := mkw 0x075740000eb10000 0x00eae80001d62000 0xe79f80001ef98004 0xbcf3f00003df3000

def z691 : W := mkw 0x029e0d8d0a786b32 0xc053c1b1a14f0d66 0xff9e0f8f1ff87ffe 0xfff3c1f1e3ff0fff

def z692 : W := mkw 0x00000000204ae16a 0xa000000004095c2d 0x68000088e1ffe1ff 0xcd0000111c3ffc3f

def z693 : W := mkw 0x05e08ad0b5c2d5cb 0x20bc115a16b85ab9 0xffe18ff0ffc7ffc7 0x7ffc31fe1ff8fff8

def z694 : W := mkw 0x8f7770327fb710cd 0x11eeee064ff6e219 0xe7fff0f0ffff81c5 0xfcfffe1e1ffff038

def z695 : W := mkw 0x177773665fb50004 0x02eeee6ccbf6a000 0x166673771e000000 0x22ccce6ee3c00000

def z696 : W := mkw 0x07ddcc88a6dbe16a 0xa0fbb99114db7c2d 0xef998c88e7ffe1ff 0xddf331911cfffc3f

def z697 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xe8180c88e03861fe 0x9d0301911c070c3f

def z698 : W := mkw 0x8822303359241895 0x110446066b248312 0x506670fff8001803 0xea0cce1fff000300

def z699 : W := mkw 0x0001500000050004 0x00002a000000a000 0x0001f00000078001 0x00003e000000f000

def z700 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x180000fff92619fe 0x0300001fff24c33f

def z701 : W := mkw 0x07fc0fdc15c05583 0x00ff81fb82b80ab0 0xfffe0fff1fc07fc6 0xffffc1ffe3f80ff8

def z702 : W := mkw 0x021e050d2a7aeb7a 0xe043c0a1a54f5d6f 0xfe1e0f0f1ffffffe 0xbfc3c1e1e3ffffff

def z703 : W := mkw 0x077750011fbd2a34 0xc0eeea0023f7a546 0xeffff0001ffffe3d 0xfdfffe0003ffffc7

def z704 : W := mkw 0x07f75ac01fb50004 0x00feeb5803f6a000 0xf7fffff01fff8007 0xfefffffe03fff000

def z705 : W := mkw 0x177ff52edfb50004 0x02effea5dbf6a000 0xe7fff00fffff8005 0xfcfffe01fffff000

def z706 : W := mkw 0x05c00ad000405583 0x00b8015a00080ab0 0xdfe00ff000007fc2 0x7bfc01fe00000ff8

def z707 : W := mkw 0x021750000a350004 0x0042ea000146a000 0xe79ff0001fff8005 0xfcf3fe0003fff000

def z708 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x56667fffe0000003 0xeacccffffc000000

def z709 : W := mkw 0x07ffdc88bfffe16e 0xa0fffb9117fffc2d 0x0e667c88fe0061fa 0x21cccf911fc00c3f

def z710 : W := mkw 0x002210001fb50004 0x0004420003f6a000 0xe1fff0001fff8005 0xfc3ffe0003fff000

def z711 : W := mkw 0x121de52ec0000000 0x0243bca5d8000000 0x107ff07fe0000001 0xa20ffe0ffc000000

def z712 : W := mkw 0x023610001b340004 0x0046c20003668000 0xe7fff0001fff8005 0xfcfffe0003fff000

def z713 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xff9f8f0f1ef9fe3e 0xbff3f1e1e3df3fc7

def z714 : W := mkw 0x07dc2fee40000000 0x00fb85fdc8000000 0xd7fe7fffe0000003 0xfaffcffffc000000

def z715 : W := mkw 0x0569550d158d2a34 0xc0ad2aa1a2b1a546 0x19e1ff0f01c7fe3b 0x433c3fe1e038ffc7

def z716 : W := mkw 0x077750011fb50814 0x00eeea0023f6a102 0xffffff0f1ffffe3f 0xffffffe1e3ffffc7

def z717 : W := mkw 0x10aabfeedfb50004 0x021557fddbf6a000 0x30000fffffff8006 0x060001fffffff000

def z718 : W := mkw 0x88aa9c99b96ef9ff 0xb1155393372ddf3f 0xa9998c0019fff9fc 0x15333180033fff3f

def z719 : W := mkw 0x17ddefeec0082020 0x82fbbdfdd8010404 0xffffffffe1ffe03f 0xfffffffffc3ffc07

def z720 : W := mkw 0x17ddefeec4c8e522 0xa2fbbdfdd8991ca4 0xf7ffffffe6d9e603 0xfefffffffcdb3cc0

def z721 : W := mkw 0x0755500006950004 0x00eaaa0000d2a000 0xa799f00006df8001 0x14f33e0000dbf000

def z722 : W := mkw 0x0214202240000000 0x0042840448000000 0xd67e70ffe0000003 0xfacfce1ffc000000

def z723 : W := mkw 0x17ddefeec6d9e122 0xa2fbbdfdd8db3c24 0xf7ffffffe6d9e003 0xfefffffffcdb3c00

def z724 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xfff98ff01fd9ffc6 0x7fff31fe03fb3ff8

def z725 : W := mkw 0x88221011392e3afd 0xd10442022725c75f 0x0800000019267ffc 0x010000000324cfff

def z726 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xf7fff00f1fff8007 0xfefffe01e3fff000

def z727 : W := mkw 0x056210001da40004 0x00ac420003b48000 0xe7fff0001fff8005 0xfcfffe0003fff000

def z728 : W := mkw 0x0755602246910000 0x00eaac0448d22000 0xf7fff0ffe6d98003 0xfefffe1ffcdb3000

def z729 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xfe600ff01e007fc6 0x3fcc01fe03c00ff8

def z730 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xc1998c88e1ff81fb 0xd83331911c3ff03f

def z731 : W := mkw 0x0541602240000000 0x00a82c0448000000 0x51e7f0ffe0000003 0xea3cfe1ffc000000

def z732 : W := mkw 0x88023033682618dd 0x110046066d04c31b 0x586670ffe02619fb 0xeb0cce1ffc04c33f

def z733 : W := mkw 0x05688658b58ab4e9 0xa0ad10cb16b1569d 0x16798378fe3f9e39 0xa2cf306f1fc7f3c7

def z734 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x00000000012601f8 0x000000000024c03f

def z735 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xc7fff00001ff8001 0xf8fffe00003ff000

def z736 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x41fff00019ff8005 0xe83ffe00033ff000

def z737 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xf9f98cf8e1ffe1ff 0xff3f319f1c3ffc3f

def z738 : W := mkw 0x02968985aa72cb5a 0x6052d130b54e596b 0x17878387ffc79fc1 0x62f0f070fff8f3f8

def z739 : W := mkw 0x882210113b3e3afd 0xd10442022767c75f 0x08000000193e19fc 0x010000000327c33f

def z740 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xbfe00f701fc07fc4 0x37fc01ee03f80ff8

def z741 : W := mkw 0x0008242a40082020 0x8001048548010404 0xf87e7cffe038603f 0xff0fcf9ffc070c07

def z742 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x49998088e1ff81ff 0xc93330111c3ff03f

def z743 : W := mkw 0x8de17af275c755cf 0x11bc2f5e4eb8eab9 0x01e1f0f0e1c781c1 0x403c3e1e1c38f038

def z744 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xff9e0f0f1ff87e3e 0xfff3c1e1e3ff0fc7

def z745 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xdffffffff8001807 0xfbffffffff000300

def z746 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x586670fff80019fb 0xeb0cce1fff00033f

def z747 : W := mkw 0x075750000eb50004 0x00eaea0001d6a000 0xe7fff00006ff8001 0xfcfffe0000dff000

def z748 : W := mkw 0x17ddefeec0082020 0x82fbbdfdd8010404 0xfffffffffe387e3f 0xffffffffffc70fc7

def z749 : W := mkw 0x88221011392eb8fd 0xb10442022725d71f 0x08000000193f99fc 0x010000000327f33f

def z750 : W := mkw 0x17ddefeec4800400 0x02fbbdfdd8900080 0xd7ffffffe6000603 0xfafffffffcc000c0

def z751 : W := mkw 0x0000001000001081 0x0000000200000210 0xfe000ff01e007fc6 0x3fc001fe03c00ff8

def z752 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x97fffff7e0000001 0x72fffffefc000000

def z753 : W := mkw 0x07fe0fdd1ff87fb3 0xc0ffc1fba3ff0ff6 0x01fe00ff01f801f8 0xc03fc01fe03f003f

def z754 : W := mkw 0x15c1eae2c0000000 0x02b83d5c58000000 0xd7e7ffffe0000003 0xfafcfffffc000000

def z755 : W := mkw 0x00888d8ca04ae36a 0xe01111b194095c6d 0xe9998f88e1ffe7ff 0xdd3331f11c3ffcff

def z756 : W := mkw 0x17ddefeec6910000 0x02fbbdfdd8d22000 0xd7ffffffe6000003 0xfafffffffcc00000

def z757 : W := mkw 0x8f556033669318d9 0x11eaac066cd2631b 0xbf9980ffe6d999fa 0x17f3301ffcdb333f

def z758 : W := mkw 0x00800ad000405583 0x0010015a00080ab0 0xff800ff01fc07fc6 0x7ff001fe03f80ff8

def z759 : W := mkw 0x02975ad00a755587 0x0052eb5a014eaab0 0x181ffff0003fffc3 0x8303fffe0007fff8

def z760 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x5e060f0f1e207e3e 0xabc0c1e1e3c40fc7

def z761 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe60fff1fc07fc6 0xfffcc1ffe3f80ff8

def z762 : W := mkw 0x8a3c353e731e32ed 0xd14786a7ce63c65d 0xa6787ff0e71e67c1 0x54cf0ffe1ce3ccf8

def z763 : W := mkw 0x0000202240000000 0x0000040448000000 0xd6667fffe0000003 0xfacccffffc000000

def z764 : W := mkw 0x000a050d0a382a30 0xc00140a1a1470546 0xfe000f0f1e387e3e 0x3fc001e1e3c70fc7

def z765 : W := mkw 0x077750101fb51085 0x00eeea0203f6a210 0xeffff0001fff99c5 0xfdfffe0003fff338

def z766 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xf9e670fff9e619ff 0xff3cce1fff3cc33f

def z767 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x48000000192619fd 0xc90000000324c33f

def z768 : W := mkw 0x0000202240000000 0x0000040448000000 0xd1fff0ffe0000003 0xfa3ffe1ffc000000

def z769 : W := mkw 0x17ddefeec2182220 0xc2fbbdfdd8430444 0xffffffffe638663f 0xfffffffffcc70cc7

def z770 : W := mkw 0x077750011fb50814 0x00eeea0023f6a102 0xeffff0001fff983d 0xfdfffe0003fff307

def z771 : W := mkw 0x0000202240000000 0x0000040448000000 0x1066707fe0000001 0xa20cce0ffc000000

def z772 : W := mkw 0x021601050a300a10 0x4042c020a1460142 0xfe060f0f1e207e3e 0xbfc0c1e1e3c40fc7

def z773 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x506670ffe12601fb 0xea0cce1ffc24c03f

def z774 : W := mkw 0x17ddefeec4810000 0x02fbbdfdd8902000 0xd7ffffffe0c18003 0xfafffffffc183000

def z775 : W := mkw 0x17556366604ae16a 0xa2eaac6ccc095c2d 0x3e66737701ffe1fc 0x27ccce6ee03ffc3f

def z776 : W := mkw 0x05e08ad095c05583 0x00bc115a12b80ab0 0xffe18ff0ffc07fc7 0x7ffc31fe1ff80ff8

def z777 : W := mkw 0x075750000a350004 0x00eaea000146a000 0xe7fff00001ff8005 0xfcfffe00003ff000

def z778 : W := mkw 0x9fffdfddb92618dd 0x13fffbfbb724c31b 0x8f998f00192619fc 0x11f331e00324c33f

def z779 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xe1fff00001ff8005 0xdc3ffe00003ff000

def z780 : W := mkw 0x1001e022c0000000 0x02003c0458000000 0x5067f0ffe0000003 0xea0cfe1ffc000000

def z781 : W := mkw 0x0000202240000000 0x0000040448000000 0xf1fff0ffe1ff8007 0xfe3ffe1ffc3ff000

def z782 : W := mkw 0x029cadaec0000000 0x005395b5d8000000 0xd7ffffffe0000003 0xfafffffffc000000

def z783 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x167fffffe0000003 0xa2cffffffc000000

def z784 : W := mkw 0x0000202240000000 0x0000040448000000 0x586670fff8001807 0xeb0cce1fff000300

def z785 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x87ffffffe0000001 0xd0fffffffc000000

def z786 : W := mkw 0x1215612640000000 0x0242ac24c8000000 0x506670ffe0000003 0xea0cce1ffc000000

def z787 : W := mkw 0x021601050a382a30 0xc042c020a1470546 0xfe060f071e387e3e 0x3fc0c1e0e3c70fc7

def z788 : W := mkw 0x8888adbfe04afbfb 0xf11115b7fc095f7f 0x18000fffe0007ffa 0x030001fffc000fff

def z789 : W := mkw 0x002230227926004c 0x000446044f24c009 0x586670fff92601ff 0xeb0cce1fff24c03f

def z790 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe00ff8ffc07fc7 0xfffc01ff1ff80ff8

def z791 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0x166673ffe0000002 0x22ccce7ffc000000

def z792 : W := mkw 0x8de02af275c255cb 0x11bc055e4eb84ab9 0x01e000f0e1c001c0 0x403c001e1c380038

def z793 : W := mkw 0x17ddefeec0404102 0x02fbbdfdd8080820 0xdfffffffe00061c3 0xfbfffffffc000c38

def z794 : W := mkw 0x88002033600218d9 0x110004066c00431b 0x586670ffe12619ff 0xeb0cce1ffc24c33f

def z795 : W := mkw 0x021c252e42182220 0xc04384a5c8430444 0xf67e7fffe6186603 0xfecfcffffcc30cc0

def z796 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xb7e00ff01fc07fc0 0x76fc01fe03f80ff8

def z797 : W := mkw 0x05e15ad015c55587 0x00bc2b5a02b8aab0 0xffe07ff01fc07fc6 0x7ffc0ffe03f80ff8

def z798 : W := mkw 0x0777500019240004 0x00eeea0003248000 0xe7fff00019ff8005 0xfcfffe00033ff000

def z799 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xeffff0001ffffe05 0xfdfffe0003ffffc0

def z800 : W := mkw 0x882230337da61cdd 0x110446066fb4c39b 0x586670ffff261fff 0xeb0cce1fffe4c3ff

def z801 : W := mkw 0x123de53ed5c05583 0x0247bca7dab80ab0 0x281ff00fffc07fc5 0x8503fe01fff80ff8

def z802 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x17fff3ffe0000001 0xe2fffe7ffc000000

def z803 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x280000001f267ffc 0x0500000003e4cfff

def z804 : W := mkw 0x8dc23ae36ce64d5e 0x11b8475c6d9cc9ab 0xa7867f0fe6e66639 0x94f0cfe1fcdcccc7

def z805 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xe9fffc88e1ffe1ff 0xfd3fff911c3ffc3f

def z806 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd7ffffffe03f8003 0xfafffffffc07f000

def z807 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x3e600ff01fc07fc6 0x27cc01fe03f80ff8

def z808 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xef998f88e7ffe7ff 0xddf331f11cfffcff

def z809 : W := mkw 0x077752401fb50404 0x00eeea4803f6a080 0xe7fff3001fff8605 0xfcfffe6003fff0c0

def z810 : W := mkw 0x0775500017950004 0x00eeaa0002f2a000 0x01f9f00001df8001 0x403f3e00003bf000

def z811 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xf7ffff001fff8007 0xfeffffe003fff000

def z812 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xe7fff088ffff8007 0xfcfffe111ffff000

def z813 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xae1e0f0f1e387e3c 0x95c3c1e1e3c70fc7

def z814 : W := mkw 0x021f550d0a3d2a34 0xc043eaa1a147a546 0xff9fff0f1ffffe3f 0xfff3ffe1e3ffffc7

def z815 : W := mkw 0x00a00ad011405583 0x0014015a02280ab0 0xfe600ff01f007fc6 0x7fcc01fe03e00ff8

def z816 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xf7ffffffe0380007 0xfefffffffc070000

def z817 : W := mkw 0x0008050d00082a30 0xc00100a1a0010546 0x1e000f0f1e007e3a 0x23c001e1e3c00fc7

def z818 : W := mkw 0x88221011396ef9ff 0xb1044202272ddf3f 0x08000000192679fc 0x010000000324cf3f

def z819 : W := mkw 0x0000000100000810 0x0000000020000102 0xfe000f0f1e007e3e 0x3fc001e1e3c00fc7

def z820 : W := mkw 0x88202033710218d9 0x110404066e20431b 0x586670fff90019ff 0xeb0cce1fff20033f

def z821 : W := mkw 0x10888fcca04ae16a 0xa21111f994095c2d 0xe9998f88e1ffe1ff 0xdd3331f11c3ffc3f

def z822 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x186670fff90619fb 0x630cce1fff20c33f

def z823 : W := mkw 0x0000202240000000 0x0000040448000000 0x586670ffe020003f 0xeb0cce1ffc040007

def z824 : W := mkw 0x882210113b3618dd 0x110442022766c31b 0x280000001f3e19fc 0x0500000003e7c33f

def z825 : W := mkw 0x17ddefeec048e122 0xa2fbbdfdd8091c24 0xf7ffffffe1ffe007 0xfefffffffc3ffc00

def z826 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa1998c88e1ffe1f9 0xd43331911c3ffc3f

def z827 : W := mkw 0x15c3eae3ca382a30 0xc2b87d5c79470546 0x29e1f0f0fe387e3d 0x453c3e1e1fc70fc7

def z828 : W := mkw 0x0215400000000000 0x0042a80000000000 0xe19ff00001ff8005 0xdc33fe00003ff000

def z829 : W := mkw 0x8888acabe04ae97a 0xb11115957c095d2f 0x08000c8fe00061fa 0x01000191fc000c3f

def z830 : W := mkw 0x0000202240000000 0x0000040448000000 0x106670ffe0000002 0x220cce1ffc000000

def z831 : W := mkw 0x05e08ad095c0d583 0x20bc115a12b81ab0 0xffe18ff01fc1ffc6 0x7ffc31fe03f83ff8

def z832 : W := mkw 0x1088affee04af5eb 0xa21115ffdc095ebd 0x18000fffe0007ffa 0x030001fffc000fff

def z833 : W := mkw 0x021e850d8a38aa30 0xe043d0a1b1471546 0xfe1f8f0f1e39fe3e 0xbfc3f1e1e3c73fc7

def z834 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xfff98ff01fc07fc7 0xffff31fe03f80ff8

def z835 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xafe00ff01fc07fc4 0x55fc01fe03f80ff8

def z836 : W := mkw 0x121fc50d8a382a30 0xc243f8a1b1470546 0xfe1f8f0f1e387e3e 0xbfc3f1e1e3c70fc7

def z837 : W := mkw 0x175de76ec0000000 0x02ebbcedd8000000 0xd67fff7fe0000003 0xbacfffeffc000000

def z838 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x2800000019ff99fc 0x05000000033ff33f

def z839 : W := mkw 0x05c02ae240000000 0x00b8055c48000000 0x51e670ffe0000003 0xea3cce1ffc000000

def z840 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xf9998f88e1ffffff 0xdf3331f11c3fffff

def z841 : W := mkw 0x0008252e40000000 0x000104a5c8000000 0x50667fffe0000003 0xea0ccffffc000000

def z842 : W := mkw 0x0000202240000000 0x0000040448000000 0xfe667ffffe007e07 0xffcccfffffc00fc0

def z843 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x29998088e1ffe1fd 0xc53330111c3ffc3f

def z844 : W := mkw 0x075750000eb50004 0x00eaea0001d6a000 0x019ff00000ff8001 0x8033fe00001ff000

def z845 : W := mkw 0x00888c88a0020048 0x0011119114004009 0xe9998c88e1ff81ff 0xdd3331911c3ff03f

def z846 : W := mkw 0x0755400006910000 0x00eaa80000d22000 0xe7fff00007ff8005 0xfcfffe0000fff000

def z847 : W := mkw 0x17ddefeec4c04502 0x02fbbdfdd89808a0 0xd7ffffffe0c00003 0xfafffffffc180000

def z848 : W := mkw 0x021750000a350004 0x0042ea000146a000 0x019ff00001ff8001 0xc033fe00003ff000

def z849 : W := mkw 0x175de76ec0000000 0x02ebbcedd8000000 0xd7fff37fe0000001 0xfafffe6ffc000000

def z850 : W := mkw 0x8f7750111fb51895 0x11eeea0223f6a312 0xe7fff0001fff9805 0xfcfffe0003fff300

def z851 : W := mkw 0x077750011fb50814 0x00eeea0023f6a102 0xe7fff00f1fff803d 0xfcfffe01e3fff007

def z852 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xbe180f0f1e387e3e 0x17c301e1e3c70fc7

def z853 : W := mkw 0x882a1419392e38fd 0x910542832725c71f 0xe8180c08193e79fe 0x9d0301810327cf3f

def z854 : W := mkw 0x00800ad000405583 0x0010015a00080ab0 0x1e000ff01e007fc2 0x23c001fe03c00ff8

def z855 : W := mkw 0x023750001fb50004 0x0046ea0003f6a000 0xe19ff0001fff8005 0xdc33fe0003fff000

def z856 : W := mkw 0x0088acaac048e122 0xa011159558091c24 0xf1fffcffe0d9e003 0xfe3fff9ffc1b3c00

def z857 : W := mkw 0x021600010a300810 0x0042c00021460102 0xfe1e0f0f1e387e3e 0xbfc3c1e1e3c70fc7

def z858 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa7fff0001fff8004 0x34fffe0003fff000

def z859 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa9998c88e1ffe1fe 0x153331911c3ffc3f

def z860 : W := mkw 0x077750101fb51085 0x00eeea0203f6a210 0xf7fff0701fff9805 0xfefffe0e03fff300

def z861 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd7ffffffe1260007 0xfafffffffc24c000

def z862 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xeffff0081fff803f 0xfdfffe0103fff007

def z863 : W := mkw 0x0008242a40000000 0x0001048548000000 0xd07e7cffe0000003 0xfa0fcf9ffc000000

def z864 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x086670fff92619fd 0xc10cce1fff24c33f

def z865 : W := mkw 0x0775400015800000 0x00eea80002b00000 0xe7fff0001fff8005 0xfcfffe0003fff000

def z866 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe7e7f0f1e387e3f 0xffcfcfe1e3c70fc7

def z867 : W := mkw 0x0000000000000000 0x0000000000000000 0xe1fff00001ff8005 0xfc3ffe00003ff000

def z868 : W := mkw 0x07ddecaac0000000 0x00fbbd9558000000 0xd7fffcffe0000003 0xfaffff9ffc000000

def z869 : W := mkw 0x17d5ebe6c0000000 0x02fabd7cd8000000 0xd7fff3f7e0000001 0xfafffe7efc000000

def z870 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x586670fff82019fe 0xab0cce1fff04033f

def z871 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x5e600ff01f007fc6 0x6bcc01fe03e00ff8

def z872 : W := mkw 0x88002033600218d9 0x110004066c00431b 0x186670ffe00019fa 0x230cce1ffc00033f

def z873 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xde667ffff92619ff 0xfbcccfffff24c33f

def z874 : W := mkw 0x8f7750113fb718dd 0x11eeea0227f6e31b 0xaf9980001fff99fc 0x15f3300003fff33f

def z875 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe67ff01fc07fc7 0xfffccffe03f80ff8

def z876 : W := mkw 0x17d5ebe6c0000000 0x02fabd7cd8000000 0xd7e7fff7e0000003 0x7afcfffefc000000

def z877 : W := mkw 0x882230337fb718dd 0x110446066ff6e31b 0xf9fff0ffffff99ff 0xff3ffe1ffffff33f

def z878 : W := mkw 0x17ddefeec0082220 0xc2fbbdfdd8010444 0xd7ffffffe0006603 0xfafffffffc000cc0

def z879 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x786670ffff267fff 0xef0cce1fffe4cfff

def z880 : W := mkw 0x17ddefeec048e122 0xa2fbbdfdd8091c24 0xffffffffe0f9e03f 0xfffffffffc1f3c07

def z881 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xf7fff0f01fff8007 0xfefffe1e03fff000

def z882 : W := mkw 0x17ddcfcc8048e122 0xa2fbb9f990091c24 0x87998f0000006000 0x10f331e000000c00

def z883 : W := mkw 0x00888ec8a04ae16a 0xa01111d914095c2d 0xf9998ff8e1ffe1ff 0xdf3331ff1c3ffc3f

def z884 : W := mkw 0x077751041fb50204 0x40eeea2083f6a040 0xe7fff3001fff8605 0xfcfffe6003fff0c0

def z885 : W := mkw 0x882230337b3618dd 0x110446066f66c31b 0x786670ffff3e19ff 0xef0cce1fffe7c33f

def z886 : W := mkw 0x17ddefeec0082020 0x82fbbdfdd8010404 0xf7ffffffe0186003 0xfefffffffc030c00

def z887 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe18ff01fc7ffc7 0x7ffc31fe03f8fff8

def z888 : W := mkw 0x0560025015c05583 0x00ac004a02b80ab0 0xfe600f701fc07fc6 0x3fcc01ee03f80ff8

def z889 : W := mkw 0x17ddefeec0486122 0x82fbbdfdd8090c24 0xffffffffe1f861ff 0xfffffffffc3f0c3f

def z890 : W := mkw 0x88221011396659df 0x11044202272ccb3b 0x2800000019e679fc 0x05000000033ccf3f

def z891 : W := mkw 0x17ddefeec2110000 0x02fbbdfdd8422000 0xd7ffffffe0198003 0xfafffffffc033000

def z892 : W := mkw 0x17d56be640000000 0x02faad7cc8000000 0xd7e67fffe0000003 0xfafccffffc000000

def z893 : W := mkw 0x1088afeec0000000 0x021115fdd8000000 0xd1ffffffe0000003 0xfa3ffffffc000000

def z894 : W := mkw 0x88aabcbbd96cf9b7 0xb11557977b2d9f36 0xb1fffc7718d9f800 0x363fff8ee31b3f00

def z895 : W := mkw 0x1755e366c0000000 0x02eabc6cd8000000 0x1667f377e0000001 0x22ccfe6efc000000

def z896 : W := mkw 0x00088408a00aa068 0xa00110811401540d 0xe9998088e1ff81ff 0xdd3330111c3ff03f

def z897 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xbe1e0f071e387e3c 0x37c3c1e0e3c70fc7

def z898 : W := mkw 0x882210113b7efbff 0xf1044202276fdf7f 0x280000001ffffffc 0x0500000003ffffff

def z899 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xbe1e0f0f1e187e3a 0x37c3c1e1e3c30fc7

def z900 : W := mkw 0x021c252e40000000 0x004384a5c8000000 0x507e70ffe0000003 0xea0fce1ffc000000

def z901 : W := mkw 0x077751051fb50a14 0x40eeea20a3f6a142 0xfffff30f1fff9e3f 0xfffffe61e3fff3c7

def z902 : W := mkw 0x17ddefeec008a020 0xa2fbbdfdd8011404 0xd7ffffffe0198003 0xfafffffffc033000

def z903 : W := mkw 0x8a1f752f6a3f2a7c 0xd143eea5ed47e54f 0x001ff00fe03f8039 0x8003fe01fc07f007

def z904 : W := mkw 0x0088acaae04ae16a 0xa01115955c095c2d 0x18000cffe00061fa 0x0300019ffc000c3f

def z905 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe00ff81fe07ffe 0xfffc01ff03fc0fff

def z906 : W := mkw 0x880230236826085c 0x110046046d04c10b 0x586670ffe12601ff 0xeb0cce1ffc24c03f

def z907 : W := mkw 0x023750001b350004 0x0046ea000366a000 0xe1fff00019ff8005 0xfc3ffe00033ff000

def z908 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xdfe00ff01e007fc2 0x7bfc01fe03c00ff8

def z909 : W := mkw 0x88203033710618dd 0x110406066e20c31b 0x586670ffe10619fb 0xeb0cce1ffc20c33f

def z910 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x587ff0fff93f99ff 0xeb0ffe1fff27f33f

def z911 : W := mkw 0x05c8aeeac0000000 0x00b915dd58000000 0xd7ffffffe0000003 0xfafffffffc000000

def z912 : W := mkw 0x0020001015c05583 0x0004000202b80ab0 0xfe600ff01fc07fc6 0x7fcc01fe03f80ff8

def z913 : W := mkw 0x05c02ae244c04502 0x00b8055c489808a0 0xf7e67fffe6c06603 0xfefccffffcd80cc0

def z914 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xdfffffffe020003f 0xfbfffffffc040007

def z915 : W := mkw 0x15e1cad095c05583 0x02bc395a12b80ab0 0xffe18ff01fc07fc6 0x7ffc31fe03f80ff8

def z916 : W := mkw 0x1088adaee04ae16a 0xa21115b5dc095c2d 0x08000c8fe00061fa 0x01000191fc000c3f

def z917 : W := mkw 0x0008050d00082a30 0xc00100a1a0010546 0xfe180f0f1e387e3e 0xbfc301e1e3c70fc7

def z918 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe1e0f8ffe387e3f 0xffc3c1f1ffc70fc7

def z919 : W := mkw 0x882230337da618dd 0x110446066fb4c31b 0x786670ffffe619ff 0xef0cce1ffffcc33f

def z920 : W := mkw 0x17d5ebe6c0000000 0x02fabd7cd8000000 0x57e7f3ffe0000003 0xeafcfe7ffc000000

def z921 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0x1666737fe0000001 0xa2ccce6ffc000000

def z922 : W := mkw 0x17ddefeec0404102 0x02fbbdfdd8080820 0xffffffffffc07fc7 0xfffffffffff80ff8

def z923 : W := mkw 0x129cafeec0000000 0x025395fdd8000000 0xd67e7fffe0000003 0xfacfcffffc000000

def z924 : W := mkw 0x000a050d08282a30 0xc00140a1a1050546 0xfe060f0f1e207e3e 0xbfc0c1e1e3c40fc7

def z925 : W := mkw 0x021e050d08200810 0x0043c0a1a1040102 0xfe1e0f0f1e207e3e 0xbfc3c1e1e3c40fc7

def z926 : W := mkw 0x056350001da50004 0x00ac6a0003b4a000 0xe1fff00019ff8005 0xfc3ffe00033ff000

def z927 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xfff80ff01ff87fc6 0xffff01fe03ff0ff8

def z928 : W := mkw 0x077752401fb50004 0x00eeea4803f6a000 0xf7fff3701fff8005 0xfefffe6e03fff000

def z929 : W := mkw 0x077750101fb51085 0x00eeea0203f6a210 0xfffffff01fffffc7 0xfffffffe03fffff8

def z930 : W := mkw 0x1088afefe04aeb7a 0xe21115fdfc095d6f 0x18000fffe0007ffa 0x030001fffc000fff

def z931 : W := mkw 0x175d676e40000000 0x02ebacedc8000000 0xd67e7fffe0000003 0xfacfcffffc000000

def z932 : W := mkw 0x882210113ff75ddf 0x1104420227feebbb 0x280000001ffffffc 0x0500000003ffffff

def z933 : W := mkw 0x882230337b3718dd 0x110446066f66e31b 0x586670fff93f99ff 0xeb0cce1fff27f33f

def z934 : W := mkw 0x05c00ad004c05583 0x00b8015a00980ab0 0xff800ff01ec07fc6 0x3ff001fe03d80ff8

def z935 : W := mkw 0x075d652e40000000 0x00ebaca5c8000000 0xd7ffffffe0000003 0xfafffffffc000000

def z936 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa9998c08e1ffe1fd 0x953331811c3ffc3f

def z937 : W := mkw 0x882210113b361add 0x510442022766c35b 0x080000001f261ffc 0x0100000003e4c3ff

def z938 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xef998c88ffffe1ff 0xfdf331911ffffc3f

def z939 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0x09998c88e1ffe1fb 0xc13331911c3ffc3f

def z940 : W := mkw 0x00808880a04ae16a 0xa010111014095c2d 0xe9998080e1ffe1fd 0xdd3330101c3ffc3f

def z941 : W := mkw 0x9de1faf2f5c655cf 0x13bc3f5e5eb8cab9 0x01e1f0f0e1c601c1 0x403c3e1e1c38c038

def z942 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xbf800ff01fc07fc6 0x17f001fe03f80ff8

def z943 : W := mkw 0x882210113deefdff 0xb104420227bddfbf 0x280000001ffffffc 0x0500000003ffffff

def z944 : W := mkw 0x0775500017950004 0x00eeaa0002f2a000 0xe7fff00007df8001 0xfcfffe0000fbf000

def z945 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe1f8f0f1e3ffe3f 0xbfc3f1e1e3c7ffc7

def z946 : W := mkw 0x17ddefeec0404502 0x02fbbdfdd80808a0 0xd7ffffffe0006603 0xfafffffffc000cc0

def z947 : W := mkw 0x15c9eeeac0000000 0x02b93ddd58000000 0xd1fffcffe0000003 0xfa3fff9ffc000000

def z948 : W := mkw 0x021e150d0a3d2a34 0xc043c2a1a147a546 0xfe1e0f0f1e3ffe3e 0xbfc3c1e1e3c7ffc7

def z949 : W := mkw 0x8a1e252f6a3a2a78 0xd143c4a5ed47454f 0x001e000fe0380038 0x8003c001fc070007

def z950 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x186670ffe12619fb 0xc30cce1ffc24c33f

def z951 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xf7ffffffe6006603 0xfefffffffcc00cc0

def z952 : W := mkw 0x0560001015801081 0x00ac000202b00210 0xffe00ff01fc07fc6 0x7ffc01fe03f80ff8

def z953 : W := mkw 0x175de76ec0000000 0x02ebbcedd8000000 0x567ff3ffe0000003 0xeacffe7ffc000000

def z954 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xe7ffff001fffe605 0xfcffffe003fffcc0

def z955 : W := mkw 0x077751041fb50004 0x00eeea2083f6a000 0xf7fff3071fff8005 0xfefffe60e3fff000

def z956 : W := mkw 0x882230337b361add 0x510446066f66c35b 0x586670ffff261fff 0xeb0cce1fffe4c3ff

def z957 : W := mkw 0x1008a52ec0000000 0x020114a5d8000000 0x506670ffe0000003 0xea0cce1ffc000000

def z958 : W := mkw 0x175de52ec0000000 0x02ebbca5d8000000 0xd7fff0ffe0000003 0xfafffe1ffc000000

def z959 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xc1fffcffe0000003 0xd83fff9ffc000000

def z960 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa79ff0001fff8005 0x94f3fe0003fff000

def z961 : W := mkw 0x17ddcfcc8258e322 0xe2fbb9f9904b1c64 0xa7998f0006d9e600 0x14f331e000db3cc0

def z962 : W := mkw 0x17ddefeec2100000 0x02fbbdfdd8420000 0xf7ffffffe6180003 0xfefffffffcc30000

def z963 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xbfe00ff01ec07fc2 0x37fc01fe03d80ff8

def z964 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xf9998c88f9fff9ff 0xff3331911f3fff3f

def z965 : W := mkw 0x05e00ad011001081 0x00bc015a02200210 0xffe00ff01f007fc6 0x7ffc01fe03e00ff8

def z966 : W := mkw 0x008008802042414a 0x0010011004084829 0xe9998c88e1ffe1ff 0xdd3331911c3ffc3f

def z967 : W := mkw 0x0080a8a2c0000000 0x0010151458000000 0x51e7f0ffe0000003 0xea3cfe1ffc000000

def z968 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0x1fe00ff01fc07fc2 0x63fc01fe03f80ff8

def z969 : W := mkw 0x88203032710610cd 0x110406064e20c219 0x586670ffe12601ff 0xeb0cce1ffc24c03f

def z970 : W := mkw 0x882210113da61cdd 0x1104420227b4c39b 0x080000001f261ffc 0x0100000003e4c3ff

def z971 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x08000000180019f8 0x010000000300033f

def z972 : W := mkw 0x17ddefeec4c04502 0x02fbbdfdd89808a0 0xffffffffe7c067c7 0xfffffffffcf80cf8

def z973 : W := mkw 0x0022203359201891 0x000444066b240312 0x586670fff92019ff 0xeb0cce1fff24033f

def z974 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe00ff01fffffc6 0x7ffc01fe03fffff8

def z975 : W := mkw 0x000200010a382a30 0xc000400021470546 0xfe060f0f1e387e3e 0xbfc0c1e1e3c70fc7

def z976 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe1e0f0f1f3e7e3f 0xffc3c1e1e3e7cfc7

def z977 : W := mkw 0x17ddefeec4800000 0x02fbbdfdd8900000 0xf7ffffffe6c00003 0xfefffffffcd80000

def z978 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd7e67fffe0000002 0x7afccffffc000000

def z979 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xf7ffffffe0d98003 0xfefffffffc1b3000

def z980 : W := mkw 0x077751051fb50a14 0x40eeea20a3f6a142 0xffffff071ffffe07 0xffffffe0e3ffffc0

def z981 : W := mkw 0x00080408200a2068 0x800100810401440d 0xe9998c88e1ffe1ff 0xdd3331911c3ffc3f

def z982 : W := mkw 0x17ddefeec0082020 0x82fbbdfdd8010404 0xdfffffffe000603b 0xfbfffffffc000c07

def z983 : W := mkw 0x077752501fb51485 0x00eeea4a03f6a290 0xfffff3f01fff9fc7 0xfffffe7e03fff3f8

def z984 : W := mkw 0x882210113fbf3afd 0xd104420227f7e75f 0x280000001ffffffc 0x0500000003ffffff

def z985 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x1e1e0f0f1e387e3a 0xa3c3c1e1e3c70fc7

def z986 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0x3e060f0f1e387e3e 0x27c0c1e1e3c70fc7

def z987 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0x166673f7e0000001 0x62ccce7efc000000

def z988 : W := mkw 0x077752501fb51485 0x00eeea4a03f6a290 0xffffff701ffffe07 0xffffffee03ffffc0

def z989 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x59e7f0fff9e799ff 0xeb3cfe1fff3cf33f

def z990 : W := mkw 0x05e15ad015c55587 0x00bc2b5a02b8aab0 0xfff9fff01fffffc7 0xffff3ffe03fffff8

def z991 : W := mkw 0x021f450d0a392a30 0xc043e8a1a1472546 0xfe1f8f0f1e39fe3e 0xbfc3f1e1e3c73fc7

def z992 : W := mkw 0x077751051fb50a14 0x40eeea20a3f6a142 0xe7fff0071fff8005 0xfcfffe00e3fff000

def z993 : W := mkw 0x00888ec8a04ae56a 0xa01111d914095cad 0xe9998f88e1ffe7ff 0xdd3331f11c3ffcff

def z994 : W := mkw 0x05c00ad000405583 0x00b8015a00080ab0 0xffe00ff01e007fc6 0x7ffc01fe03c00ff8

def z995 : W := mkw 0x021e150d0a3c2a34 0xc043c2a1a1478546 0xfe1e7f0f1e3e7e3f 0xbfc3cfe1e3c7cfc7

def z996 : W := mkw 0x0002100008240004 0x0000420001048000 0xe19ff00001ff8005 0xdc33fe00003ff000

def z997 : W := mkw 0x077752501fb51485 0x00eeea4a03f6a290 0xe7fff0701fff8005 0xfcfffe0e03fff000

def z998 : W := mkw 0x0000202240000000 0x0000040448000000 0x506670ffe1260007 0xea0cce1ffc24c000

def z999 : W := mkw 0x0541400000000000 0x00a8280000000000 0xe1f9f00001ff8005 0xdc3f3e00003ff000

def z1000 : W := mkw 0x00888d8ca04ae16a 0xa01111b194095c2d 0xf9998f8fe1ffe1ff 0xdf3331f1fc3ffc3f

def z1001 : W := mkw 0x175de76ec0000000 0x02ebbcedd8000000 0x1666737fe0000000 0x22ccce6ffc000000

def z1002 : W := mkw 0x15c1eae2c0000000 0x02b83d5c58000000 0x11e7f0f7e0000001 0x623cfe1efc000000

def z1003 : W := mkw 0x88022033682218d9 0x110044066d04431b 0x586670fff82019ff 0xeb0cce1fff04033f

def z1004 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa7fff0001eff8001 0xb4fffe0003dff000

def z1005 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xd9fff0fff92619ff 0xfb3ffe1fff24c33f

def z1006 : W := mkw 0x00808880a042c14a 0x2010111014085829 0xe9998088e1ff81ff 0xdd3330111c3ff03f

def z1007 : W := mkw 0x1088aeeae04ae16a 0xa21115dd5c095c2d 0x08000cf8e00061fa 0x0100019f1c000c3f

def z1008 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x07fff0001fff8001 0xe0fffe0003fff000

def z1009 : W := mkw 0x88221011392618dd 0x110442022724c31b 0xfe000f001f267ffe 0x3fc001e003e4cfff

def z1010 : W := mkw 0x0214212640000000 0x00428424c8000000 0x566673ffe0000003 0xeaccce7ffc000000

def z1011 : W := mkw 0x121fe52fea3aaa78 0xe243fca5fd47554f 0x001ff00fe03f8039 0x8003fe01fc07f007

def z1012 : W := mkw 0x17ddefeec2182220 0xc2fbbdfdd8430444 0xd7ffffffe0180003 0xfafffffffc030000

def z1013 : W := mkw 0x17ddefeec0404102 0x02fbbdfdd8080820 0xffffffffe1ffe1c7 0xfffffffffc3ffc38

def z1014 : W := mkw 0x17d5ebe6c0000000 0x02fabd7cd8000000 0x01e7f0f7e0000001 0x403cfe1efc000000

def z1015 : W := mkw 0x0088acaac0000000 0x0011159558000000 0x50667cffe0000003 0xea0ccf9ffc000000

def z1016 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa7f9f0001fff8005 0x54ff3e0003fff000

def z1017 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd7ffffffe1c78003 0xfafffffffc38f000

def z1018 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xf7fff3001fff9e05 0xfefffe6003fff3c0

def z1019 : W := mkw 0x05e14ad015c15583 0x00bc295a02b82ab0 0xffe18ff01fc1ffc6 0x7ffc31fe03f83ff8

def z1020 : W := mkw 0x00a0089011405183 0x0014011202280a30 0xffe00ff01fc07fc6 0x7ffc01fe03f80ff8

def z1021 : W := mkw 0x121de52ec0000000 0x0243bca5d8000000 0xd67fffffe0000003 0xfacffffffc000000

def z1022 : W := mkw 0x0775500015850004 0x00eeaa0002b0a000 0xe7fff00001ff8005 0xfcfffe00003ff000

def z1023 : W := mkw 0x008028a240404102 0x0010051448080820 0xf9e67cffe1c061c7 0xff3ccf9ffc380c38

def z1024 : W := mkw 0x077750111fb51895 0x00eeea0223f6a312 0xfffff0ff1fff99ff 0xfffffe1fe3fff33f

def z1025 : W := mkw 0x8de0baf2f5c6d5cf 0x31bc175e5eb8dab9 0x01e1f0f0e1c781c1 0x403c3e1e1c38f038

def z1026 : W := mkw 0x9f7773775fb51895 0x13eeee6eebf6a312 0x166673771e001800 0x22ccce6ee3c00300

def z1027 : W := mkw 0x05c00ac000404102 0x00b8015800080820 0xffe00ff01fc07fc6 0x7ffc01fe03f80ff8

def z1028 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xf7ffffffe1c00007 0xfefffffffc380000

def z1029 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xfe6670ffff2619ff 0xffccce1fffe4c33f

def z1030 : W := mkw 0x07d56ae240000000 0x00faad5c48000000 0xd7ffffffe0000003 0xfafffffffc000000

def z1031 : W := mkw 0x15c1eae2c0000000 0x02b83d5c58000000 0x01e7f0ffe0000001 0xc03cfe1ffc000000

def z1032 : W := mkw 0x882210113966d9df 0x31044202272cdb3b 0x0800000019e799fc 0x01000000033cf33f

def z1033 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xdfffffffe0007e03 0xfbfffffffc000fc0

def z1034 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe060f0f1e007e3e 0x3fc0c1e1e3c00fc7

def z1035 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xff9f8f0f1e387e3f 0xfff3f1e1e3c70fc7

def z1036 : W := mkw 0x077753551fb51e95 0x40eeea6aa3f6a3d2 0xf7fff3771fff9e05 0xfefffe6ee3fff3c0

def z1037 : W := mkw 0x17d5eae2c0000000 0x02fabd5c58000000 0xd7fff0ffe0000003 0xfafffe1ffc000000

def z1038 : W := mkw 0x129defeec0000000 0x0253bdfdd8000000 0x507fffffe0000003 0xea0ffffffc000000

def z1039 : W := mkw 0x021f450d0a382a30 0xc043e8a1a1470546 0xfe1fff0f1e387e3f 0xbfc3ffe1e3c70fc7

def z1040 : W := mkw 0x17ddefeec258e322 0xe2fbbdfdd84b1c64 0xf7ffffffe6d9e603 0xfefffffffcdb3cc0

def z1041 : W := mkw 0x008028a240000000 0x0010051448000000 0xd1e67cffe0000003 0xfa3ccf9ffc000000

def z1042 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x00000000190619c0 0x000000000320c338

def z1043 : W := mkw 0x021f550d0a3d2a34 0xc043eaa1a147a546 0xfe1e7f0f1e387e3e 0xbfc3cfe1e3c70fc7

def z1044 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe1e0f8f1f387ffe 0xffc3c1f1e3e70fff

def z1045 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x586670fff90019fe 0x6b0cce1fff20033f

def z1046 : W := mkw 0x0755602240000000 0x00eaac0448000000 0x566670ffe0000003 0xeaccce1ffc000000

def z1047 : W := mkw 0x000a040908282830 0x8001408121050506 0xfe1e0f0f1e387e3e 0xbfc3c1e1e3c70fc7

def z1048 : W := mkw 0x129dedaec0000000 0x0253bdb5d8000000 0xd1fffcffe0000003 0xfa3fff9ffc000000

def z1049 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x486670ffe12601ff 0xc90cce1ffc24c03f

def z1050 : W := mkw 0x882210113ffe7fff 0xd104420227ffcfff 0x280000001ffe7ffc 0x0500000003ffcfff

def z1051 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x97ffffffe0000002 0x32fffffffc000000

def z1052 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa7fff0001fdf8001 0x74fffe0003fbf000

def z1053 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x186670fff92619fe 0x230cce1fff24c33f

def z1054 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0x21fff0001fff8005 0xc43ffe0003fff000

def z1055 : W := mkw 0x15c8afeec0000000 0x02b915fdd8000000 0xd7e67fffe0000003 0xfafccffffc000000

def z1056 : W := mkw 0x88a21891396659df 0x11144312272ccb3b 0xe9800c8019e679fe 0x5d300190033ccf3f

def z1057 : W := mkw 0x17ddefeec4c04502 0x02fbbdfdd89808a0 0xfffffffffec07e07 0xffffffffffd80fc0

def z1058 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd7fffffffe001e03 0xfaffffffffc003c0

def z1059 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xeffff0801fff81c7 0xfdfffe1003fff038

def z1060 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xeffffc001fffe007 0xfdffff8003fffc00

def z1061 : W := mkw 0x882210113ffff9ff 0xb104420227ffff3f 0x280000001ffff9fc 0x0500000003ffff3f

def z1062 : W := mkw 0x05e01ad015c55587 0x00bc035a02b8aab0 0xffe00ff01fc7ffc6 0x7ffc01fe03f8fff8

def z1063 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xf8667cfff92679ff 0xff0ccf9fff24cf3f

def z1064 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x48000008192619fe 0x890000010324c33f

def z1065 : W := mkw 0x15e1eaf2f5c2d5cb 0x22bc3d5e5eb85ab9 0x01e1f0f0e1c781c1 0x403c3e1e1c38f038

def z1066 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x106670fff92619f9 0xe20cce1fff24c33f

def z1067 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xc7fff0ffe0000001 0xf8fffe1ffc000000

def z1068 : W := mkw 0x0020100011040004 0x0004020002208000 0xe1f9f00001ff8005 0xdc3f3e00003ff000

def z1069 : W := mkw 0x00088408a04ae16a 0xa001108114095c2d 0xe9998008e1ffe1fd 0xdd3330011c3ffc3f

def z1070 : W := mkw 0x05e00ad015c05583 0x00bc015a02b80ab0 0xffe00ff01fe67fc7 0xfffc01fe03fccff8

def z1071 : W := mkw 0x17ddefeec2100200 0x42fbbdfdd8420040 0xd7ffffffe6000603 0xfafffffffcc000c0

def z1072 : W := mkw 0x882230337da718dd 0x110446066fb4e31b 0x586670fff9e799ff 0xeb0cce1fff3cf33f

def z1073 : W := mkw 0x17ddefeec048e122 0xa2fbbdfdd8091c24 0xd7ffffffe0006003 0xfafffffffc000c00

def z1074 : W := mkw 0x9a1ff52fea3e2a7c 0xd343fea5fd47c54f 0x001ff00fe03e0039 0x8003fe01fc07c007

def z1075 : W := mkw 0x8a3e151d3b3e3afd 0xd147c2a3a767c75f 0xae180f001f3e7ffc 0x15c301e003e7cfff

def z1076 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xd67e7fffe0000002 0xbacfcffffc000000

def z1077 : W := mkw 0x8888aefbe04afdfb 0xb11115df7c095fbf 0x18000fffe0007ffa 0x030001fffc000fff

def z1078 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xff998f88e1ffe1ff 0xfff331f11c3ffc3f

def z1079 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xf99f8c8fe1ffe1ff 0xff33f191fc3ffc3f

def z1080 : W := mkw 0x00202032710210c9 0x000404064e204219 0x586670fff92619ff 0xeb0cce1fff24c33f

def z1081 : W := mkw 0x077750101fb51485 0x00eeea0203f6a290 0xe7fff0001fff9e05 0xfcfffe0003fff3c0

def z1082 : W := mkw 0x88221011392e38fd 0x910442022725c71f 0x28000000193e79fc 0x050000000327cf3f

def z1083 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x51fff0ffe0000003 0xea3ffe1ffc000000

def z1084 : W := mkw 0x05e14ad015c05583 0x00bc295a02b80ab0 0xffe1fff01fc07fc7 0x7ffc3ffe03f80ff8

def z1085 : W := mkw 0x075740000a300000 0x00eae80001460000 0xe7fff0001fff8005 0xfcfffe0003fff000

def z1086 : W := mkw 0x882210113fb718dd 0x1104420227f6e31b 0x080000001f2619fc 0x0100000003e4c33f

def z1087 : W := mkw 0x17ddefeec2182220 0xc2fbbdfdd8430444 0xfffffffffe187e07 0xffffffffffc30fc0

def z1088 : W := mkw 0x882210113b3718dd 0x110442022766e31b 0x08000000193f99fc 0x010000000327f33f

def z1089 : W := mkw 0x0775500017950004 0x00eeaa0002f2a000 0xe7f9f00007ff8005 0xdcff3e0000fff000

def z1090 : W := mkw 0x0775500017950004 0x00eeaa0002f2a000 0xe7f9f0001fdf8005 0x7cff3e0003fbf000

def z1091 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xa9998c80e1ffe1fd 0x553331901c3ffc3f

def z1092 : W := mkw 0x175de76ec0000000 0x02ebbcedd8000000 0x007ff07fe0000001 0x800ffe0ffc000000

def z1093 : W := mkw 0x17ddefeec6910000 0x02fbbdfdd8d22000 0xf7ffffffe7ff8007 0xfefffffffcfff000

def z1094 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0xa1f9f00001df8001 0x543f3e00003bf000

def z1095 : W := mkw 0x0000202260020048 0x000004044c004009 0x586670ffe00001fb 0xeb0cce1ffc00003f

def z1096 : W := mkw 0x17ddcfcc86d86722 0xc2fbb9f990db0ce4 0xa7998f0006d86600 0x14f331e000db0cc0

def z1097 : W := mkw 0x021c050d02182a30 0xc04380a1a0430546 0xfe180f0f1e187e3e 0x3fc301e1e3c30fc7

def z1098 : W := mkw 0x0215602240000000 0x0042ac0448000000 0x507ff0ffe0000003 0xea0ffe1ffc000000

def z1099 : W := mkw 0x17ddefeec048e122 0xa2fbbdfdd8091c24 0xffffffffe1d9e1c7 0xfffffffffc3b3c38

def z1100 : W := mkw 0x021e850d8a382a30 0xc043d0a1b1470546 0xfe1f8f0ffe387e3f 0xbfc3f1e1ffc70fc7

def z1101 : W := mkw 0x882210113da718dd 0x1104420227b4e31b 0x0800000019e799fc 0x01000000033cf33f

def z1102 : W := mkw 0x1000236640000000 0x0200046cc8000000 0x506673ffe0000003 0xea0cce7ffc000000

def z1103 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xffffffffe0006007 0xfffffffffc000c00

def z1104 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x186670fff82619fb 0xa30cce1fff04c33f

def z1105 : W := mkw 0x9888afffe04af9fb 0xb31115fffc095f3f 0x18000fffe00079fa 0x030001fffc000f3f

def z1106 : W := mkw 0x0000202240000000 0x0000040448000000 0x106670f7e0000001 0x620cce1efc000000

def z1107 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xb61e0f0f1e387e38 0xb6c3c1e1e3c70fc7

def z1108 : W := mkw 0x1755636640000000 0x02eaac6cc8000000 0xd7fff3ffe0000003 0xfafffe7ffc000000

def z1109 : W := mkw 0x021750000a350004 0x0042ea000146a000 0xa19ff00000ff8001 0x9433fe00001ff000

def z1110 : W := mkw 0x17ddcfcc84c8e522 0xa2fbb9f990991ca4 0xa7998f0006d9e600 0x14f331e000db3cc0

def z1111 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xe1998088e1ff81fd 0xdc3330111c3ff03f

def z1112 : W := mkw 0x17ddefeec6992220 0xc2fbbdfdd8d32444 0xf7ffffffe6d9e603 0xfefffffffcdb3cc0

def z1113 : W := mkw 0x8f7772735fb51c95 0x11eeee4e6bf6a392 0x166673771e001e00 0x22ccce6ee3c003c0

def z1114 : W := mkw 0x0000202240000000 0x0000040448000000 0x006670ffe0000001 0xc00cce1ffc000000

def z1115 : W := mkw 0x077750011fb50814 0x00eeea0023f6a102 0xf7fff0071fff9805 0xfefffe00e3fff300

def z1116 : W := mkw 0x17ddcfcc86d9e122 0xa2fbb9f990db3c24 0xa7998f0006d9e000 0x14f331e000db3c00

def z1117 : W := mkw 0x056350001fb50004 0x00ac6a0003f6a000 0xe1f9f0001fff8005 0xdc3f3e0003fff000

def z1118 : W := mkw 0x8de21ad13de65ddf 0x11bc435a27bccbbb 0xaf800f001fe67ffc 0x15f001e003fccfff

def z1119 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0xe7f9f0001fff8005 0xfcff3e0003fff000

def z1120 : W := mkw 0x00a00ad015c05583 0x0014015a02b80ab0 0xfe000ff01fc07fc6 0x3fc001fe03f80ff8

def z1121 : W := mkw 0x077750101fb51085 0x00eeea0203f6a210 0xe7fff0f01fff81c5 0xfcfffe1e03fff038

def z1122 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe7e0fff1e387e3e 0xffcfc1ffe3c70fc7

def z1123 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x48000080192619fe 0x490000100324c33f

def z1124 : W := mkw 0x00802ae240000000 0x0010055c48000000 0x50667fffe0000003 0xea0ccffffc000000

def z1125 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xfffff0001fff9807 0xfffffe0003fff300

def z1126 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xfe1e0f0f1ffffe3e 0xbfc3c1e1e3ffffc7

def z1127 : W := mkw 0x0008a42ac0000000 0x0001148558000000 0x507ff0ffe0000003 0xea0ffe1ffc000000

def z1128 : W := mkw 0x075750000eb50004 0x00eaea0001d6a000 0xe79ff0001eff8005 0xbcf3fe0003dff000

def z1129 : W := mkw 0x05e01ad015c45587 0x00bc035a02b88ab0 0xffe07ff01fc67fc7 0x7ffc0ffe03f8cff8

def z1130 : W := mkw 0x17d5ebe6c0000000 0x02fabd7cd8000000 0x166673f7e0000000 0x22ccce7efc000000

def z1131 : W := mkw 0x0561500015850004 0x00ac2a0002b0a000 0x01f9f00001ff8001 0xc03f3e00003ff000

def z1132 : W := mkw 0x00000000204ae16a 0xa000000004095c2d 0xe9998088e1ffe1ff 0xdd3330111c3ffc3f

def z1133 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xf7fffffffe000007 0xfeffffffffc00000

def z1134 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0xdfffffffe10001c7 0xfbfffffffc200038

def z1135 : W := mkw 0x021c050c00082020 0x804380a180010404 0xfe1e0f0f1e387e3e 0xbfc3c1e1e3c70fc7

def z1136 : W := mkw 0x8822101139665ddf 0x11044202272ccbbb 0x0800000019267ffc 0x010000000324cfff

def z1137 : W := mkw 0x17ddefeec0082020 0x82fbbdfdd8010404 0xd7ffffffe038003b 0xfafffffffc070007

def z1138 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x5e6673ffff261fff 0xebccce7fffe4c3ff

def z1139 : W := mkw 0x177753441fb50004 0x02eeea6883f6a000 0xe7fff3001fff8005 0xfcfffe6003fff000

def z1140 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x786670fff9ff99ff 0xef0cce1fff3ff33f

def z1141 : W := mkw 0x0002202368220858 0x000044046d04410b 0x586670fff92619ff 0xeb0cce1fff24c33f

def z1142 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x0000000018261838 0x000000000304c307

def z1143 : W := mkw 0x17ddefeec0404102 0x02fbbdfdd8080820 0xf7ffffffe0c06003 0xfefffffffc180c00

def z1144 : W := mkw 0x1080aae2c0000000 0x0210155c58000000 0x506670ffe0000003 0xea0cce1ffc000000

def z1145 : W := mkw 0x021e050d0a382a30 0xc043c0a1a1470546 0xde1e0f0f1e007e3a 0xbbc3c1e1e3c00fc7

def z1146 : W := mkw 0x882230337fb718dd 0x110446066ff6e31b 0x586670ffff2619ff 0xeb0cce1fffe4c33f

def z1147 : W := mkw 0x00888c88a04ae16a 0xa011119114095c2d 0xe9998c88ffffffff 0xdd3331911fffffff

def z1148 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x17e7ffffe0000003 0x62fcfffffc000000

def z1149 : W := mkw 0x88221011392618dd 0x110442022724c31b 0xe999800019ff99fd 0xdd333000033ff33f

def z1150 : W := mkw 0x88221011392618dd 0x110442022724c31b 0x58000000192619fe 0x2b0000000324c33f

def z1151 : W := mkw 0x1541626240000000 0x02a82c4c48000000 0x506670ffe0000003 0xea0cce1ffc000000

def z1152 : W := mkw 0x121de52ec0000000 0x0243bca5d8000000 0x007ff0ffe0000001 0xc00ffe1ffc000000

def z1153 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x11ffffffe0000003 0xc23ffffffc000000

def z1154 : W := mkw 0x021c050d00082a30 0xc04380a1a0010546 0xfe1e0f0f1e007e3e 0xbfc3c1e1e3c00fc7

def z1155 : W := mkw 0x17ddefeec0000000 0x02fbbdfdd8000000 0x97ffff7fe0000001 0xb2ffffeffc000000

def z1156 : W := mkw 0x1088afeec0000000 0x021115fdd8000000 0x10667fffe0000002 0x220ccffffc000000

def z1157 : W := mkw 0x8888acbae04af1eb 0xb11115975c095e3d 0x08000cf8e00061fa 0x0100019f1c000c3f

def z1158 : W := mkw 0x0540202240000000 0x00a8040448000000 0xd7e670ffe0000003 0xfafcce1ffc000000

def z1159 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0xf87e70fff93e19ff 0xff0fce1fff27c33f

def z1160 : W := mkw 0x8a1eb52fea3eaa7c 0xf143d6a5fd47d54f 0x001ff00fe03f8039 0x8003fe01fc07f007

def z1161 : W := mkw 0x17ddefeec040c102 0x22fbbdfdd8081820 0xd7ffffffe0c18003 0xfafffffffc183000

def z1162 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x406670fff92601fd 0xe80cce1fff24c03f

def z1163 : W := mkw 0x15c9efeec0000000 0x02b93dfdd8000000 0x51e7ffffe0000003 0xea3cfffffc000000

def z1164 : W := mkw 0x0560025015801481 0x00ac004a02b00290 0xfe600ff01f007fc6 0x7fcc01fe03e00ff8

def z1165 : W := mkw 0x077750001fb50004 0x00eeea0003f6a000 0xa7fff00007ff8001 0xd4fffe0000fff000

def z1166 : W := mkw 0x0000202240000000 0x0000040448000000 0x586670ffe10001c7 0xeb0cce1ffc200038

def z1167 : W := mkw 0x0001500000050004 0x00002a000000a000 0xe199f00001ff8005 0xdc333e00003ff000

def z1168 : W := mkw 0x0540226240000000 0x00a8044c48000000 0x566673ffe0000003 0xeaccce7ffc000000

def z1169 : W := mkw 0x8f7771375fb51a95 0x51eeee26ebf6a352 0x166673771e001e00 0x22ccce6ee3c003c0

def z1170 : W := mkw 0x882210113de65ddf 0x1104420227bccbbb 0x0800000019e619fc 0x01000000033cc33f

def z1171 : W := mkw 0x17ddefeec0404102 0x02fbbdfdd8080820 0xd7ffffffe1c001c3 0xfafffffffc380038

def z1172 : W := mkw 0x077750011fb50a14 0x40eeea0023f6a142 0xe7fff0001fff9e05 0xfcfffe0003fff3c0

def z1173 : W := mkw 0x882210113da618dd 0x1104420227b4c31b 0x280000001fe619fc 0x0500000003fcc33f

def z1174 : W := mkw 0x075750000eb50004 0x00eaea0001d6a000 0xe79ff00007ff8005 0xdcf3fe0000fff000

def z1175 : W := mkw 0x88223033792618dd 0x110446066f24c31b 0x58667ffff9267fff 0xeb0ccfffff24cfff

def z1176 : W := mkw 0x17ddefeec6d86722 0xc2fbbdfdd8db0ce4 0xf7ffffffe6d86603 0xfefffffffcdb0cc0

def z1177 : W := mkw 0x17ddefeec6d14502 0x02fbbdfdd8da28a0 0xf7ffffffe6d9e603 0xfefffffffcdb3cc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z9,z4,z5,z6])],[(0,[z10,z8,z1,z2,z4,z5,z6]),(1,[z11,z1,z2,z12,z5,z6]),(1,[z8,z1,z2,z4,z13,z6]),(0,[z8,z1,z2,z4,z5,z6,z14]),(0,[z15,z8,z1,z2,z4,z16,z6]),(0,[z17,z8,z2,z4,z5,z6,z18]),(0,[z8,z1,z19,z2,z4,z20,z6]),(0,[z21,z8,z1,z22,z2,z4,z6])],[(0,[z11,z8,z1,z2,z4,z23,z6]),(0,[z8,z24,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z25]),(0,[z8,z1,z2,z4,z5,z26,z6]),(1,[z8,z1,z2,z27,z5,z6])],[(0,[z28,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z29,z5,z6]),(0,[z8,z1,z2,z4,z30,z5,z6]),(0,[z31,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z32,z4,z6])],[(0,[z33,z1,z34,z2,z4,z5,z6]),(0,[z35,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z36,z5,z6]),(0,[z21,z8,z1,z2,z4,z37,z6])],[(0,[z8,z1,z2,z4,z5,z38,z6]),(0,[z11,z8,z1,z39,z2,z5,z6]),(0,[z8,z40,z1,z41,z4,z5,z6]),(1,[z15,z8,z39,z2,z5,z6]),(0,[z8,z1,z2,z42,z5,z6,z43]),(0,[z44,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z45,z5,z6]),(0,[z46,z8,z1,z2,z4,z5,z6])],[(0,[z8,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z2,z4,z5,z6]),(0,[z33,z8,z1,z2,z4,z16,z6]),(0,[z0,z8,z1,z2,z4,z5,z47]),(0,[z8,z1,z2,z4,z5,z48,z6]),(0,[z49,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z32,z4,z5,z6])],[(0,[z8,z1,z2,z50,z4,z5,z6]),(0,[z8,z51,z1,z2,z4,z5,z6])]],
   [[(0,[z52,z8,z1,z2,z4,z48,z6]),(0,[z8,z1,z2,z4,z53,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z54]),(1,[z1,z2,z4,z5,z6,z55]),(0,[z21,z8,z56,z1,z2,z4,z6]),(0,[z8,z57,z1,z2,z4,z16,z6])],[(0,[z8,z1,z2,z58,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z59]),(0,[z8,z1,z2,z60,z5,z61,z6]),(1,[z21,z62,z8,z1,z2,z4]),(0,[z8,z1,z2,z4,z5,z63,z6]),(0,[z8,z64,z1,z2,z4,z5,z65]),(0,[z8,z66,z1,z2,z67,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z68])],[(0,[z69,z8,z1,z2,z42,z5,z6]),(0,[z52,z70,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z71,z5,z6]),(0,[z8,z1,z2,z9,z5,z72,z6]),(0,[z8,z1,z2,z4,z16,z6,z73])],[(0,[z8,z1,z2,z4,z74,z5,z6]),(1,[z8,z1,z2,z4,z75,z6])],[(0,[z8,z1,z76,z2,z77,z5,z6]),(0,[z21,z78,z8,z1,z2,z4,z6]),(0,[z8,z1,z79,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z80,z6]),(0,[z8,z1,z2,z81,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z5,z82])],[(0,[z8,z1,z1,z2,z4,z5,z6]),(0,[z21,z8,z83,z1,z2,z4,z6]),(0,[z70,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z84]),(0,[z85,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z86,z5,z6]),(0,[z8,z1,z2,z4,z87,z5,z6])],[(0,[z88,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z89,z5,z6])],[(0,[z8,z1,z90,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z91,z6]),(0,[z8,z66,z1,z2,z4,z16,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z6,z92]),(0,[z93,z8,z1,z76,z4,z5,z6]),(1,[z8,z1,z2,z4,z5,z84]),(0,[z8,z1,z2,z4,z94,z16,z6]),(1,[z8,z1,z2,z4,z95,z6])],[(0,[z8,z1,z2,z4,z96,z5,z6])],[(0,[z11,z8,z1,z2,z12,z5,z6]),(0,[z11,z1,z2,z4,z5,z47,z6]),(0,[z8,z1,z97,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z98]),(0,[z8,z1,z2,z99,z4,z5,z6]),(0,[z8,z1,z100,z2,z4,z5,z6]),(0,[z101,z8,z1,z2,z4,z16,z6])],[(0,[z102,z8,z1,z2,z4,z5,z6]),(0,[z8,z103,z1,z2,z4,z91,z6]),(0,[z104,z8,z1,z2,z4,z5,z6]),(0,[z105,z8,z1,z2,z4,z5,z6])],[(0,[z106,z8,z1,z2,z4,z5,z6]),(0,[z17,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z107]),(0,[z8,z1,z19,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z5,z6,z108])],[(0,[z109,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z110,z5,z6]),(0,[z111,z8,z1,z2,z4,z74,z6]),(0,[z15,z8,z39,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z112]),(0,[z8,z1,z2,z4,z94,z61,z6]),(0,[z8,z1,z4,z5,z6,z113,z18]),(0,[z114,z8,z1,z2,z4,z5,z6])],[(0,[z33,z115,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z116,z4,z5,z6]),(0,[z117,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z21,z33,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z118,z6]),(0,[z8,z119,z1,z2,z4,z5,z6]),(0,[z8,z1,z39,z2,z4,z5,z6]),(0,[z8,z120,z1,z2,z4,z5,z6]),(0,[z21,z121,z8,z1,z2,z4,z6])],[(0,[z8,z1,z122,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z123,z5,z6]),(0,[z62,z8,z1,z2,z4,z124,z6]),(0,[z8,z1,z2,z125,z4,z5,z6])],[(1,[z8,z1,z2,z4,z126,z6]),(0,[z8,z1,z2,z4,z5,z127,z6]),(0,[z8,z1,z2,z128,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z129]),(0,[z130,z21,z8,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z6,z131]),(0,[z8,z1,z132,z2,z4,z5,z6])],[(0,[z133,z8,z1,z2,z4,z5,z6]),(0,[z8,z66,z1,z2,z5,z6,z43]),(0,[z8,z1,z2,z67,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z95,z6])],[],[(0,[z8,z1,z2,z4,z5,z134,z6]),(1,[z8,z1,z2,z4,z135,z6]),(0,[z8,z1,z2,z4,z5,z37,z47]),(0,[z52,z8,z1,z2,z4,z5,z84]),(0,[z136,z8,z1,z2,z4,z5,z6]),(0,[z137,z8,z103,z2,z4,z5,z6]),(1,[z138,z8,z1,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z139,z6]),(0,[z140,z8,z1,z2,z4,z5,z6])],[(0,[z21,z8,z1,z39,z2,z4,z6])]],
   [[(0,[z21,z8,z1,z34,z2,z4,z6]),(0,[z33,z8,z1,z76,z4,z5,z6]),(1,[z141,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z5,z65,z6,z18]),(0,[z142,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z143]),(0,[z52,z8,z1,z4,z42,z5,z6]),(0,[z8,z1,z2,z67,z4,z5,z37])],[(0,[z8,z1,z144,z2,z4,z5,z6]),(0,[z8,z145,z1,z2,z4,z5,z6]),(0,[z93,z8,z1,z2,z42,z5,z6]),(0,[z146,z8,z1,z2,z4,z16,z6])],[(0,[z8,z1,z147,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z148,z5,z6]),(0,[z149,z8,z1,z2,z4,z5,z6]),(0,[z150,z8,z1,z2,z4,z5,z6]),(0,[z151,z8,z1,z2,z4,z5,z6]),(1,[z21,z8,z1,z2,z4,z43])],[(0,[z152,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z153,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z42,z6]),(0,[z8,z1,z2,z4,z154,z5,z6])],[(0,[z155,z1,z2,z58,z4,z5,z6]),(0,[z8,z1,z2,z60,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z6,z25]),(0,[z8,z1,z156,z2,z4,z5,z6]),(0,[z157,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z158]),(0,[z8,z1,z2,z159,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z6,z160])],[(0,[z8,z161,z1,z2,z4,z5,z6]),(1,[z0,z21,z8,z1,z2,z4]),(0,[z130,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z162]),(0,[z8,z1,z2,z4,z163,z5,z6])]],
   [[(1,[z8,z2,z4,z5,z6,z164]),(0,[z21,z8,z1,z2,z4,z36,z6])],[(0,[z8,z1,z34,z2,z4,z16,z6]),(0,[z165,z8,z1,z2,z4,z5,z6]),(0,[z166,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z167,z5,z6]),(0,[z8,z1,z2,z4,z168,z5,z6]),(0,[z8,z1,z2,z4,z169,z5,z6]),(0,[z8,z1,z170,z2,z4,z16,z6])],[(1,[z8,z1,z171,z2,z5,z6]),(0,[z8,z1,z172,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z173,z5,z6]),(0,[z8,z1,z2,z174,z4,z5,z6]),(0,[z8,z64,z1,z2,z4,z175,z6]),(0,[z8,z1,z19,z2,z4,z176,z6]),(0,[z177,z8,z1,z2,z36,z5,z6]),(0,[z8,z1,z2,z4,z5,z178,z6])],[(1,[z8,z1,z2,z4,z179,z6]),(0,[z52,z8,z1,z2,z4,z5,z180]),(0,[z181,z8,z1,z2,z4,z5,z6]),(0,[z93,z8,z40,z1,z4,z5,z6]),(0,[z8,z182,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z87,z5,z6]),(0,[z8,z1,z2,z4,z5,z183,z6]),(1,[z8,z1,z2,z4,z20,z6]),(1,[z21,z8,z1,z2,z4,z16]),(0,[z8,z56,z1,z2,z4,z5,z6])],[(0,[z62,z8,z1,z2,z4,z5,z6]),(0,[z184,z8,z1,z2,z4,z5,z6]),(0,[z185,z8,z1,z2,z4,z5,z186]),(0,[z8,z1,z2,z4,z187,z5,z6])],[(0,[z8,z1,z2,z4,z188,z5,z6]),(0,[z8,z1,z189,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z190,z6]),(0,[z8,z1,z2,z4,z26,z6,z18]),(0,[z8,z191,z1,z2,z4,z5,z6])],[(0,[z8,z192,z1,z2,z4,z5,z6]),(0,[z52,z141,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z193,z5,z6]),(1,[z93,z8,z66,z1,z5,z6]),(1,[z177,z8,z1,z2,z36,z6])],[(0,[z8,z83,z1,z171,z2,z5,z6]),(0,[z8,z1,z2,z3,z4,z16,z6]),(0,[z21,z8,z1,z2,z4,z47,z6]),(0,[z8,z1,z2,z194,z42,z5,z6]),(0,[z8,z1,z2,z4,z5,z195,z6]),(0,[z8,z1,z196,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z197,z2,z4,z5,z6]),(0,[z8,z198,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z199]),(1,[z137,z8,z2,z4,z200,z6]),(0,[z8,z1,z2,z4,z176,z5,z6])],[(0,[z201,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z202,z4,z5,z6]),(1,[z8,z64,z2,z4,z5,z65]),(0,[z8,z1,z2,z4,z203,z5,z6])],[(1,[z8,z1,z204,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z205,z6]),(0,[z78,z8,z1,z2,z4,z74,z6]),(0,[z206,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z207,z5,z6])],[(0,[z8,z1,z2,z4,z208,z5,z6]),(0,[z8,z1,z2,z209,z4,z5,z6]),(0,[z210,z8,z1,z2,z4,z211,z6]),(0,[z185,z8,z1,z2,z4,z5,z6])],[(0,[z212,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z12,z5,z6]),(0,[z8,z1,z2,z213,z4,z5,z6]),(0,[z78,z1,z2,z4,z5,z61,z6]),(0,[z8,z1,z2,z4,z91,z16,z6]),(1,[z8,z1,z4,z5,z6,z113]),(0,[z8,z1,z214,z2,z4,z5,z6])],[(0,[z69,z8,z1,z2,z12,z5,z6]),(0,[z8,z1,z2,z4,z5,z215,z6])],[(1,[z216,z34,z2,z4,z5,z6]),(0,[z8,z1,z217,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z218,z5,z6])],[(0,[z216,z8,z34,z2,z4,z5,z6]),(0,[z8,z1,z219,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z200,z74,z6]),(0,[z8,z1,z2,z4,z5,z179,z6]),(0,[z220,z8,z1,z2,z4,z5,z6]),(0,[z210,z8,z1,z170,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z20,z6]),(0,[z8,z1,z2,z4,z221,z16,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z222,z6]),(0,[z52,z8,z40,z2,z4,z5,z6])],[(0,[z8,z1,z76,z4,z42,z5,z6]),(0,[z223,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z5,z6,z131]),(0,[z8,z1,z224,z2,z4,z5,z6]),(0,[z93,z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z225,z5,z6])],[(0,[z8,z1,z2,z4,z226,z5,z6]),(0,[z8,z1,z2,z4,z61,z91,z6]),(0,[z52,z8,z1,z41,z4,z5,z6]),(0,[z227,z8,z1,z2,z4,z5,z6]),(0,[z228,z8,z1,z2,z4,z5,z6]),(0,[z229,z8,z1,z2,z4,z5,z6]),(0,[z121,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z230,z6]),(0,[z8,z1,z2,z4,z5,z6,z231]),(0,[z232,z8,z1,z2,z4,z5,z6]),(0,[z233,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z170,z4,z5,z211,z6]),(0,[z21,z210,z8,z1,z2,z4,z6])],[(0,[z8,z234,z1,z2,z4,z5,z6]),(0,[z8,z235,z1,z2,z4,z5,z6]),(0,[z8,z1,z236,z2,z4,z5,z6]),(0,[z52,z8,z2,z4,z5,z65,z6]),(0,[z8,z1,z39,z174,z4,z5,z6]),(0,[z8,z1,z237,z2,z4,z16,z6]),(0,[z8,z1,z238,z2,z4,z6,z107]),(0,[z21,z8,z1,z239,z2,z4,z6])],[(0,[z11,z21,z8,z1,z2,z4,z6]),(0,[z111,z78,z1,z2,z4,z5,z6]),(0,[z240,z8,z1,z2,z4,z5,z6]),(0,[z8,z241,z1,z2,z4,z5,z6]),(0,[z242,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z243]),(1,[z8,z1,z2,z67,z5,z37]),(0,[z244,z8,z1,z2,z4,z5,z6])],[(0,[z216,z1,z34,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z245,z6]),(0,[z111,z8,z1,z2,z4,z16,z6]),(0,[z0,z8,z1,z2,z4,z5,z25]),(0,[z21,z62,z8,z1,z2,z4,z5]),(0,[z8,z1,z246,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z16,z6])],[(0,[z247,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z248,z6]),(0,[z21,z8,z1,z2,z4,z74,z6]),(0,[z0,z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z249,z5,z6]),(0,[z8,z1,z2,z4,z250,z5,z6])]],
   [[(0,[z251,z8,z1,z2,z4,z5,z6]),(0,[z252,z8,z1,z2,z4,z5,z6]),(0,[z216,z8,z1,z2,z4,z16,z6]),(0,[z210,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z253]),(0,[z254,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z255]),(1,[z8,z1,z2,z148,z5,z6]),(0,[z8,z1,z2,z256,z4,z5,z6]),(0,[z185,z8,z1,z4,z5,z6,z107])],[(1,[z8,z192,z1,z2,z5,z6]),(1,[z8,z1,z2,z4,z23,z6]),(1,[z8,z1,z2,z4,z175,z6]),(0,[z8,z1,z2,z4,z257,z5,z43])],[(0,[z8,z83,z1,z2,z4,z16,z6]),(0,[z8,z258,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z5,z253]),(0,[z259,z8,z1,z2,z4,z5,z6])],[(0,[z111,z8,z1,z2,z4,z61,z6]),(0,[z260,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z261,z4,z5,z6]),(0,[z8,z1,z262,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z6,z82])],[(0,[z15,z8,z83,z2,z4,z5,z6]),(0,[z8,z263,z1,z2,z4,z5,z6]),(0,[z264,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z265,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z266,z6]),(0,[z8,z1,z2,z4,z5,z267,z6]),(0,[z8,z1,z2,z4,z5,z268,z6]),(0,[z21,z185,z8,z1,z2,z4,z6])],[(0,[z121,z69,z8,z1,z2,z5,z6]),(1,[z8,z40,z41,z4,z5,z6]),(0,[z137,z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z269,z5,z6]),(0,[z8,z1,z2,z270,z4,z5,z6]),(0,[z8,z1,z2,z4,z72,z16,z6]),(0,[z271,z8,z1,z2,z4,z5,z6])],[(1,[z115,z83,z2,z4,z5,z6]),(0,[z8,z1,z2,z272,z4,z5,z6]),(0,[z273,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z274,z4,z5,z6]),(0,[z8,z1,z2,z4,z65,z16,z6])]],
   [[(0,[z8,z1,z2,z275,z4,z5,z6]),(0,[z8,z39,z2,z4,z194,z5,z6]),(0,[z276,z8,z1,z2,z4,z5,z6])],[(0,[z277,z8,z1,z2,z4,z5,z6]),(0,[z177,z8,z1,z2,z4,z36,z6])],[(0,[z8,z1,z2,z4,z278,z5,z6]),(0,[z8,z1,z2,z4,z5,z245,z6]),(0,[z11,z8,z1,z2,z4,z5,z6]),(1,[z44,z8,z2,z4,z5,z6]),(0,[z8,z1,z170,z2,z4,z94,z6]),(1,[z279,z8,z2,z4,z5,z6]),(0,[z8,z1,z280,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z16,z6]),(0,[z8,z1,z2,z4,z257,z5,z16])],[(0,[z8,z1,z281,z2,z4,z5,z6]),(0,[z282,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z18,z107]),(1,[z8,z1,z238,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z283]),(0,[z284,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z36,z74,z6]),(0,[z8,z1,z2,z4,z5,z285,z6]),(0,[z8,z1,z2,z4,z5,z6,z286]),(0,[z8,z1,z2,z4,z42,z5,z6]),(0,[z8,z1,z287,z2,z4,z5,z6]),(0,[z8,z1,z288,z2,z4,z5,z6]),(0,[z8,z1,z4,z5,z186,z6,z107])],[(0,[z8,z1,z2,z4,z289,z5,z6]),(0,[z8,z1,z2,z4,z290,z5,z6]),(1,[z8,z1,z2,z4,z291,z5]),(0,[z15,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z292,z2,z4,z5,z6]),(0,[z8,z1,z2,z67,z194,z5,z6])],[(0,[z8,z1,z2,z4,z5,z23,z6]),(0,[z11,z8,z1,z2,z9,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z293]),(0,[z8,z103,z1,z2,z4,z16,z6]),(0,[z137,z8,z1,z2,z4,z91,z6]),(0,[z8,z1,z2,z4,z5,z175,z6]),(0,[z8,z1,z2,z4,z5,z6,z294])],[(0,[z8,z1,z2,z4,z291,z5,z61]),(0,[z8,z1,z2,z4,z291,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z6,z295]),(0,[z8,z1,z2,z4,z5,z61,z6]),(0,[z8,z296,z1,z2,z4,z5,z6]),(0,[z297,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z257,z16,z6])],[(0,[z216,z115,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z298,z5,z6]),(0,[z8,z1,z299,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z194,z16,z6]),(0,[z8,z1,z2,z4,z5,z300,z6]),(0,[z8,z1,z301,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z302,z5,z6]),(1,[z105,z1,z2,z4,z5,z6])],[(0,[z8,z303,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z304]),(0,[z8,z1,z2,z4,z5,z305,z6]),(0,[z8,z1,z306,z2,z4,z5,z6]),(0,[z307,z8,z1,z2,z4,z16,z6])],[(0,[z308,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z58,z4,z6]),(0,[z8,z1,z2,z194,z5,z6,z43]),(0,[z8,z1,z2,z4,z309,z5,z6]),(0,[z8,z1,z2,z67,z5,z37,z6]),(0,[z8,z310,z1,z2,z4,z5,z6])],[(0,[z52,z185,z8,z1,z4,z5,z6]),(0,[z8,z1,z2,z4,z311,z5,z6]),(0,[z185,z8,z1,z19,z4,z5,z6]),(0,[z8,z57,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z312,z4,z5,z6]),(0,[z8,z313,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z314]),(0,[z21,z8,z1,z2,z67,z4,z6]),(0,[z315,z21,z8,z1,z2,z4,z6])],[(0,[z8,z1,z316,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z37,z25])],[(0,[z8,z1,z2,z317,z4,z5,z6]),(0,[z21,z8,z1,z76,z2,z4,z6]),(0,[z8,z318,z1,z2,z4,z5,z6]),(0,[z8,z319,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z194,z6]),(0,[z8,z1,z2,z4,z5,z320,z6]),(0,[z8,z1,z19,z4,z5,z186,z6])]],
   [[(0,[z8,z1,z2,z321,z4,z5,z6]),(0,[z8,z1,z322,z2,z4,z5,z6]),(0,[z8,z323,z1,z2,z4,z5,z6])],[(0,[z8,z1,z19,z2,z4,z5,z186]),(0,[z324,z8,z1,z2,z4,z5,z6])],[(0,[z21,z216,z8,z1,z2,z4,z6]),(0,[z8,z40,z1,z2,z4,z16,z6]),(0,[z325,z21,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z203,z6]),(0,[z8,z1,z326,z2,z4,z16,z6])],[(0,[z8,z1,z2,z4,z327,z5,z6]),(0,[z21,z8,z1,z2,z4,z6,z18]),(0,[z8,z66,z1,z2,z4,z5,z6]),(0,[z21,z8,z328,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z329,z5,z6]),(0,[z8,z330,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z126,z5,z6]),(0,[z8,z1,z2,z4,z5,z331,z6]),(0,[z8,z1,z2,z4,z94,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z332]),(0,[z8,z333,z1,z2,z4,z5,z6]),(0,[z0,z62,z1,z2,z4,z5,z6]),(0,[z8,z41,z2,z4,z194,z5,z6]),(0,[z8,z1,z2,z67,z4,z225,z6])],[(0,[z101,z8,z1,z2,z4,z5,z6]),(0,[z334,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z335,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z186,z6])],[(0,[z336,z8,z1,z2,z4,z5,z6]),(0,[z337,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z338,z4,z5,z6]),(0,[z21,z155,z8,z1,z2,z4,z6]),(0,[z15,z8,z41,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z200,z16,z6]),(0,[z8,z1,z19,z2,z4,z5,z6])],[(0,[z0,z8,z1,z2,z4,z257,z5]),(0,[z8,z66,z339,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z340,z5,z6])],[(0,[z8,z83,z2,z4,z194,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z73])],[(0,[z8,z1,z2,z4,z5,z341,z6]),(0,[z8,z1,z41,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z342]),(0,[z8,z343,z1,z2,z4,z5,z6])],[(0,[z11,z8,z344,z2,z4,z5,z6]),(0,[z8,z1,z2,z345,z4,z5,z6]),(0,[z62,z8,z1,z2,z4,z5,z47])],[(0,[z155,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z346,z6]),(0,[z8,z1,z2,z4,z200,z61,z6]),(0,[z8,z1,z2,z4,z347,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z348]),(0,[z83,z1,z34,z2,z4,z5,z6]),(0,[z349,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z350,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z6]),(0,[z8,z1,z2,z4,z351,z5,z6]),(0,[z325,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z155,z8,z1,z58,z4,z5,z6]),(0,[z8,z1,z237,z2,z42,z5,z6]),(0,[z185,z8,z1,z2,z27,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z164]),(0,[z8,z2,z4,z5,z6,z164,z107]),(0,[z21,z8,z1,z2,z4,z16,z6])],[(0,[z8,z1,z2,z4,z5,z352,z6]),(0,[z353,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z5,z354])],[(0,[z8,z1,z2,z4,z355,z5,z6]),(0,[z17,z8,z41,z2,z4,z5,z6])],[(0,[z8,z1,z2,z204,z4,z5,z6]),(0,[z52,z8,z1,z2,z4,z126,z6]),(0,[z52,z8,z2,z4,z194,z5,z6]),(0,[z8,z40,z1,z4,z80,z5,z6])],[(0,[z8,z1,z2,z4,z4,z5,z6]),(0,[z8,z1,z2,z356,z4,z5,z6])],[(0,[z69,z8,z1,z2,z4,z5,z6]),(0,[z8,z357,z1,z2,z4,z5,z6])],[(0,[z8,z358,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z65,z6]),(0,[z359,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z9,z72,z6])],[(0,[z8,z1,z2,z4,z360,z5,z6]),(0,[z8,z328,z1,z2,z4,z5,z6])]],
   [[(0,[z361,z8,z1,z2,z4,z5,z6]),(0,[z21,z69,z8,z1,z2,z4,z6]),(0,[z362,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z91,z6]),(0,[z8,z1,z2,z4,z5,z186,z18]),(0,[z8,z1,z2,z4,z363,z5,z6]),(0,[z8,z1,z2,z4,z5,z354,z6]),(0,[z8,z1,z2,z4,z5,z6,z43])],[(0,[z155,z8,z1,z2,z4,z226,z6]),(0,[z69,z8,z1,z2,z9,z5,z6]),(0,[z8,z41,z2,z4,z5,z65,z6]),(0,[z8,z1,z2,z4,z364,z5,z6])],[(0,[z8,z365,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z47,z6,z25]),(0,[z21,z8,z40,z1,z2,z4,z6]),(0,[z8,z1,z366,z2,z4,z5,z6]),(0,[z8,z64,z1,z2,z4,z5,z6]),(0,[z367,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z368,z4,z6]),(0,[z8,z1,z2,z4,z16,z6,z6])],[(0,[z8,z1,z2,z193,z4,z5,z6]),(0,[z8,z1,z2,z4,z91,z211,z6])],[(0,[z369,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z370,z4,z5,z6]),(0,[z8,z371,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z25]),(0,[z8,z1,z2,z4,z5,z47,z43]),(0,[z137,z8,z2,z4,z200,z5,z6]),(0,[z372,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z9,z4,z36,z6]),(0,[z373,z21,z8,z1,z2,z4,z6])],[(0,[z8,z1,z34,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z61,z16,z6]),(1,[z8,z319,z2,z194,z5,z6]),(0,[z21,z8,z1,z2,z4,z6,z107]),(0,[z8,z1,z2,z4,z36,z16,z6]),(0,[z8,z1,z2,z4,z5,z6,z374])],[(0,[z8,z1,z375,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z47,z6]),(0,[z8,z1,z2,z4,z5,z72,z6])],[(0,[z8,z1,z2,z4,z5,z6,z376]),(1,[z8,z1,z2,z4,z124,z6]),(0,[z377,z8,z1,z2,z4,z5,z6]),(0,[z8,z378,z1,z2,z4,z5,z6]),(0,[z379,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z257,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z380,z6]),(0,[z17,z8,z1,z2,z381,z5,z6]),(0,[z382,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z383,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z384,z6])],[(0,[z8,z1,z2,z4,z5,z385,z6]),(0,[z386,z8,z1,z2,z4,z5,z6]),(0,[z387,z8,z1,z2,z4,z5,z6]),(0,[z8,z388,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z11,z8,z1,z2,z194,z5,z6]),(0,[z8,z1,z2,z4,z36,z61,z6]),(0,[z8,z1,z2,z4,z389,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z390])],[(0,[z8,z391,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z392,z5,z6])],[(0,[z393,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z394,z2,z4,z5,z6]),(0,[z1,z2,z4,z74,z5,z61,z6]),(0,[z8,z1,z2,z4,z5,z221,z6]),(0,[z111,z21,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z6,z25]),(0,[z185,z8,z1,z2,z4,z5,z107]),(0,[z105,z1,z2,z4,z5,z6,z43]),(1,[z21,z8,z1,z2,z4,z6]),(0,[z8,z1,z22,z2,z4,z5,z6])],[(0,[z0,z21,z8,z1,z2,z4,z6]),(0,[z15,z8,z1,z2,z194,z5,z6]),(0,[z395,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z160])],[(0,[z69,z8,z1,z2,z3,z5,z6]),(0,[z52,z8,z1,z2,z193,z5,z6]),(0,[z8,z1,z2,z4,z80,z16,z6]),(0,[z8,z1,z396,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z397,z2,z4,z5,z6]),(0,[z8,z1,z2,z148,z5,z61,z6]),(0,[z52,z17,z8,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z398,z6]),(0,[z8,z1,z2,z4,z211,z16,z6]),(0,[z399,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z400,z5,z6])],[(0,[z11,z0,z1,z2,z4,z5,z6]),(0,[z11,z8,z1,z2,z5,z37,z6]),(0,[z373,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z401,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z402,z5,z6]),(0,[z33,z1,z76,z2,z4,z5,z6]),(0,[z403,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z404,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z405,z6]),(0,[z8,z1,z2,z4,z5,z406,z6]),(0,[z1,z2,z4,z5,z6,z55,z43]),(0,[z8,z1,z2,z4,z407,z5,z6]),(1,[z21,z8,z1,z2,z4,z37])],[(0,[z8,z1,z2,z4,z5,z124,z6]),(0,[z8,z1,z2,z4,z5,z6,z408]),(0,[z8,z409,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z74,z91,z6]),(0,[z8,z1,z2,z4,z410,z5,z6]),(0,[z8,z1,z2,z411,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z55]),(0,[z8,z1,z2,z4,z5,z412,z6])],[(0,[z8,z1,z2,z4,z77,z5,z6]),(1,[z8,z1,z2,z351,z5,z6]),(0,[z8,z1,z2,z4,z94,z200,z6]),(0,[z93,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z413,z5,z6])],[(0,[z8,z1,z2,z4,z414,z5,z6]),(0,[z17,z8,z1,z2,z4,z5,z18]),(0,[z8,z1,z2,z4,z415,z5,z6])]],
   [[(0,[z93,z8,z1,z58,z4,z5,z6]),(0,[z8,z1,z416,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z417]),(0,[z8,z319,z1,z2,z194,z5,z6]),(0,[z8,z418,z1,z2,z4,z5,z6])],[(0,[z8,z1,z419,z2,z4,z5,z6]),(0,[z8,z1,z420,z2,z4,z5,z6]),(0,[z8,z1,z39,z2,z4,z16,z6]),(0,[z8,z1,z2,z421,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z422,z6]),(0,[z8,z1,z2,z423,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z211,z6]),(0,[z21,z8,z1,z2,z4,z94,z6]),(0,[z177,z8,z1,z2,z4,z16,z6])],[(1,[z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z125,z4,z16,z6])],[(0,[z424,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z425,z5,z6]),(0,[z0,z8,z1,z2,z4,z5,z6]),(1,[z426,z8,z1,z2,z5,z6]),(0,[z8,z41,z2,z4,z80,z5,z6]),(0,[z8,z1,z427,z2,z4,z5,z6])],[(0,[z21,z8,z319,z1,z2,z4,z6]),(0,[z8,z66,z1,z2,z194,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z428]),(0,[z429,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z430,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z431]),(0,[z8,z1,z432,z2,z4,z5,z6]),(0,[z433,z8,z1,z2,z4,z5,z6]),(0,[z177,z8,z1,z2,z4,z5,z253]),(0,[z21,z8,z1,z2,z4,z6,z43])],[(0,[z8,z83,z1,z2,z4,z5,z6]),(0,[z52,z8,z1,z2,z4,z16,z6]),(1,[z8,z103,z2,z4,z91,z6]),(0,[z8,z1,z239,z2,z4,z5,z6])]],
   [[(0,[z434,z8,z1,z2,z4,z5,z6]),(0,[z426,z8,z1,z2,z5,z6,z25]),(1,[z8,z339,z2,z4,z5,z6]),(1,[z185,z8,z1,z4,z5,z107])],[(0,[z185,z8,z1,z2,z87,z5,z6]),(0,[z8,z435,z1,z2,z4,z5,z6])],[(0,[z1,z34,z2,z58,z4,z5,z6]),(0,[z21,z137,z8,z1,z2,z4,z6]),(1,[z8,z1,z237,z42,z5,z6]),(0,[z8,z1,z2,z4,z5,z436,z6]),(1,[z21,z8,z1,z2,z4,z82])],[(0,[z437,z8,z1,z2,z4,z5,z6]),(0,[z115,z8,z34,z2,z4,z5,z6]),(1,[z8,z1,z2,z207,z5,z6]),(0,[z8,z1,z2,z4,z438,z5,z6]),(0,[z8,z1,z2,z4,z422,z16,z6])],[(0,[z439,z8,z1,z2,z4,z5,z6]),(1,[z155,z1,z58,z4,z5,z6]),(0,[z440,z8,z1,z2,z4,z5,z6]),(1,[z62,z1,z2,z4,z5,z47]),(0,[z8,z1,z2,z4,z5,z6,z441]),(0,[z8,z442,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z72,z6]),(0,[z21,z177,z8,z1,z2,z4,z6])],[(0,[z33,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z179,z6,z25]),(0,[z8,z1,z2,z443,z4,z5,z6]),(0,[z8,z1,z2,z4,z444,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z445])],[(0,[z8,z1,z2,z4,z5,z5,z6]),(0,[z8,z1,z2,z4,z446,z5,z6]),(0,[z210,z8,z1,z4,z94,z5,z6]),(0,[z8,z1,z2,z447,z4,z5,z6])],[(0,[z8,z1,z2,z4,z448,z5,z6]),(1,[z8,z1,z2,z4,z176,z6])]],
   [[(0,[z33,z8,z1,z58,z4,z5,z6]),(0,[z8,z1,z449,z2,z4,z5,z6])],[(0,[z450,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z180,z6]),(0,[z52,z8,z2,z4,z80,z5,z6])],[(0,[z8,z451,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z60,z5,z6]),(0,[z8,z452,z1,z2,z4,z5,z6]),(0,[z8,z103,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z37,z16,z6])],[(0,[z11,z8,z1,z2,z4,z135,z6]),(0,[z8,z1,z2,z4,z453,z5,z6]),(0,[z8,z1,z2,z4,z5,z454,z6]),(0,[z8,z1,z2,z455,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z6,z25]),(0,[z52,z15,z8,z2,z4,z5,z6])],[(0,[z8,z34,z2,z4,z194,z5,z6]),(0,[z115,z8,z1,z2,z4,z16,z6]),(0,[z33,z155,z1,z2,z4,z5,z6]),(0,[z8,z141,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z456,z6]),(0,[z8,z103,z2,z4,z5,z91,z6]),(0,[z8,z1,z2,z4,z457,z5,z6]),(0,[z8,z1,z2,z4,z257,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z458]),(0,[z62,z8,z1,z2,z4,z16,z6]),(0,[z8,z40,z1,z4,z5,z186,z6]),(0,[z8,z1,z2,z4,z194,z5,z6]),(0,[z21,z8,z1,z2,z4,z5,z43]),(0,[z8,z1,z2,z4,z459,z16,z6])],[(0,[z460,z8,z1,z2,z4,z5,z6]),(0,[z69,z8,z1,z2,z194,z5,z6]),(0,[z78,z8,z1,z2,z4,z16,z6]),(0,[z307,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z461]),(0,[z8,z1,z2,z4,z5,z6,z462])],[(0,[z11,z8,z1,z2,z3,z5,z6]),(0,[z69,z8,z66,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z5,z463,z6])]],
   [[(1,[z8,z1,z2,z402,z5,z6]),(0,[z8,z1,z2,z464,z4,z5,z6]),(0,[z52,z8,z1,z4,z80,z5,z6]),(1,[z240,z8,z1,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z6,z465])],[(0,[z8,z1,z2,z4,z61,z72,z6]),(0,[z21,z8,z103,z1,z2,z4,z6]),(0,[z8,z66,z1,z4,z42,z5,z6]),(1,[z121,z8,z1,z2,z5,z43]),(0,[z8,z1,z2,z4,z257,z5,z37])],[(0,[z8,z1,z2,z4,z466,z5,z6]),(0,[z467,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z468,z5,z6]),(0,[z8,z1,z2,z4,z5,z469,z6]),(1,[z17,z8,z2,z4,z5,z18]),(0,[z8,z64,z1,z2,z4,z5,z18]),(0,[z8,z1,z2,z4,z16,z6,z18]),(0,[z8,z1,z2,z67,z4,z95,z6])],[(0,[z8,z470,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z77,z5,z6]),(0,[z8,z1,z2,z4,z471,z5,z6]),(0,[z62,z8,z1,z2,z4,z13,z6]),(0,[z8,z1,z2,z472,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z37,z6])],[(0,[z11,z69,z1,z2,z4,z5,z6]),(1,[z8,z344,z2,z4,z5,z6]),(0,[z8,z1,z473,z2,z4,z5,z6]),(0,[z8,z1,z2,z474,z4,z5,z6]),(0,[z475,z8,z1,z2,z4,z5,z6]),(0,[z476,z8,z1,z2,z4,z5,z6]),(0,[z69,z8,z1,z2,z5,z37,z6]),(0,[z78,z8,z1,z2,z4,z61,z6]),(0,[z477,z8,z1,z2,z4,z5,z61]),(0,[z477,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z94,z74,z6]),(0,[z8,z1,z2,z4,z478,z5,z6]),(0,[z8,z1,z479,z2,z4,z5,z6]),(0,[z8,z1,z480,z2,z4,z5,z6]),(0,[z185,z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z481,z2,z4,z5,z6]),(0,[z146,z21,z8,z1,z2,z4,z6])],[(0,[z8,z83,z1,z2,z402,z5,z6]),(0,[z8,z482,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z483]),(0,[z315,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z5,z16])],[(0,[z8,z40,z1,z2,z4,z5,z6]),(0,[z8,z484,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z6,z485])],[(0,[z8,z1,z76,z2,z4,z16,z6]),(0,[z486,z8,z1,z2,z4,z5,z6]),(0,[z487,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z488,z8,z1,z2,z4,z5,z6]),(0,[z8,z66,z1,z237,z2,z5,z6]),(0,[z8,z1,z2,z4,z5,z489,z6])],[(0,[z8,z1,z58,z4,z42,z5,z6]),(0,[z490,z8,z1,z2,z4,z5,z6]),(0,[z491,z8,z1,z2,z4,z5,z6])],[(0,[z492,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z493,z6]),(0,[z8,z1,z2,z4,z494,z5,z6]),(0,[z8,z1,z19,z2,z4,z5,z107])],[(0,[z8,z1,z495,z2,z4,z5,z6]),(0,[z496,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z497,z2,z4,z5,z6]),(0,[z17,z8,z1,z2,z4,z5,z65]),(0,[z498,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z499,z5,z6]),(0,[z8,z1,z170,z2,z4,z211,z6]),(0,[z8,z1,z2,z4,z500,z5,z6]),(0,[z21,z8,z1,z2,z9,z4,z6])],[(0,[z216,z8,z1,z2,z4,z493,z6]),(0,[z8,z501,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z493,z5,z6])],[(0,[z8,z1,z2,z4,z502,z5,z6])],[(0,[z8,z1,z2,z4,z5,z503,z6]),(0,[z11,z8,z1,z204,z4,z5,z6]),(0,[z8,z504,z1,z2,z4,z5,z6]),(0,[z505,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z506,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z507]),(0,[z8,z1,z2,z4,z508,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z509,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z113])],[(0,[z146,z8,z1,z2,z4,z5,z6]),(0,[z510,z8,z1,z2,z4,z5,z6]),(0,[z11,z8,z1,z2,z4,z5,z511]),(0,[z21,z8,z1,z2,z4,z61,z6]),(0,[z210,z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z257,z5,z82])],[(0,[z512,z8,z1,z2,z4,z5,z6]),(0,[z11,z8,z1,z2,z4,z5,z205]),(0,[z21,z8,z1,z2,z4,z12,z6]),(0,[z8,z1,z2,z4,z5,z6,z513]),(0,[z8,z1,z2,z368,z4,z5,z6])],[(0,[z514,z8,z1,z2,z4,z5,z6])],[(0,[z115,z83,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z135,z5,z6]),(0,[z8,z1,z2,z4,z61,z211,z6]),(0,[z8,z1,z2,z4,z515,z5,z6]),(0,[z8,z1,z2,z516,z4,z5,z6]),(0,[z8,z1,z517,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z518]),(0,[z8,z519,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z9,z4,z16,z6]),(0,[z177,z8,z1,z2,z4,z5,z354]),(0,[z8,z1,z2,z4,z5,z6,z520])],[(0,[z15,z8,z34,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z521,z6]),(0,[z8,z1,z39,z2,z42,z5,z6]),(0,[z8,z1,z2,z4,z5,z459,z6]),(0,[z177,z8,z1,z2,z4,z72,z6])],[(0,[z8,z1,z2,z522,z4,z5,z6]),(0,[z8,z523,z1,z2,z4,z5,z6]),(1,[z8,z409,z1,z2,z4,z6]),(0,[z524,z8,z1,z2,z4,z5,z6])],[(0,[z525,z8,z1,z2,z4,z5,z6]),(0,[z11,z8,z219,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z526]),(0,[z93,z8,z66,z1,z2,z5,z6]),(0,[z8,z1,z527,z2,z4,z5,z6]),(1,[z8,z1,z170,z4,z211,z6]),(0,[z8,z1,z2,z4,z5,z6,z528]),(0,[z8,z1,z2,z4,z5,z6,z529])]],
   [[(0,[z8,z1,z2,z4,z530,z5,z6]),(0,[z8,z1,z2,z4,z531,z5,z6]),(0,[z8,z1,z2,z4,z5,z532,z6]),(0,[z8,z533,z1,z2,z4,z5,z6]),(0,[z8,z1,z170,z2,z4,z5,z6]),(0,[z8,z1,z2,z534,z4,z5,z6]),(0,[z8,z535,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z257,z16])],[(0,[z21,z8,z1,z2,z3,z4,z6]),(1,[z70,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z536,z5,z6]),(0,[z21,z8,z1,z2,z4,z5,z37])],[(0,[z8,z537,z1,z2,z4,z5,z6]),(0,[z538,z8,z1,z2,z4,z5,z6]),(0,[z21,z17,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z539,z6]),(0,[z8,z1,z2,z540,z4,z5,z6])],[(0,[z541,z8,z1,z2,z4,z5,z6]),(0,[z11,z1,z2,z4,z12,z5,z6]),(0,[z11,z121,z8,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z5,z542,z6]),(0,[z137,z8,z1,z2,z4,z200,z6])],[(0,[z1,z76,z2,z58,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z543]),(0,[z8,z1,z2,z4,z16,z6,z107])],[(0,[z544,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z58,z4,z16,z6]),(0,[z545,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z42,z16,z6]),(0,[z546,z21,z8,z1,z2,z4,z6])],[(0,[z547,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z548,z6]),(0,[z11,z8,z1,z397,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z549,z6]),(0,[z8,z550,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z551]),(0,[z8,z1,z238,z2,z4,z5,z6]),(0,[z8,z552,z1,z2,z4,z5,z6])],[(0,[z11,z8,z66,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z74,z16,z6]),(0,[z62,z8,z1,z2,z4,z257,z5]),(0,[z553,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z554,z2,z4,z5,z6])]],
   [[(1,[z52,z8,z4,z80,z5,z6]),(0,[z8,z1,z2,z4,z555,z5,z6]),(0,[z556,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z557])],[(0,[z8,z558,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z559,z6]),(0,[z560,z8,z1,z2,z4,z5,z6]),(0,[z69,z8,z1,z2,z36,z5,z6]),(0,[z426,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z561,z2,z4,z5,z6]),(0,[z8,z1,z2,z67,z4,z5,z43])],[(0,[z562,z8,z1,z2,z4,z5,z6]),(0,[z8,z103,z1,z2,z4,z200,z6]),(0,[z8,z2,z4,z200,z5,z91,z6]),(0,[z21,z8,z1,z170,z2,z4,z6]),(0,[z8,z1,z2,z4,z186,z16,z6]),(0,[z8,z1,z2,z4,z5,z563,z6])],[(1,[z8,z145,z1,z2,z4,z6]),(0,[z15,z8,z319,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z564,z6])],[(0,[z8,z1,z2,z4,z5,z565,z6]),(0,[z15,z8,z1,z39,z2,z5,z6]),(0,[z8,z1,z2,z566,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z567])],[(0,[z8,z1,z2,z4,z568,z5,z6]),(0,[z8,z1,z569,z2,z4,z5,z6]),(0,[z8,z145,z1,z2,z4,z6,z25]),(0,[z8,z1,z39,z2,z67,z5,z6]),(0,[z570,z8,z1,z2,z4,z5,z6])],[(0,[z216,z8,z83,z2,z4,z5,z6]),(0,[z571,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z572,z2,z4,z5,z6])]],
   [[(0,[z8,z573,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z574,z5,z6]),(0,[z575,z8,z1,z2,z4,z5,z6]),(0,[z8,z319,z1,z2,z4,z16,z6]),(0,[z17,z8,z1,z2,z4,z16,z6])],[(0,[z576,z8,z1,z2,z4,z5,z6]),(0,[z44,z8,z66,z2,z4,z5,z6]),(0,[z577,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z578,z4,z5,z6]),(0,[z546,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z6]),(0,[z8,z1,z2,z4,z5,z579,z6]),(0,[z8,z1,z2,z5,z37,z6,z43]),(0,[z324,z8,z1,z2,z4,z16,z6])],[(0,[z8,z1,z2,z4,z80,z5,z6]),(0,[z8,z1,z237,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z225,z6])],[(0,[z580,z8,z1,z2,z4,z5,z6])],[(0,[z8,z581,z1,z2,z4,z5,z6]),(0,[z582,z8,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z6]),(0,[z111,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z47,z6]),(0,[z52,z21,z8,z1,z2,z4,z6]),(0,[z8,z1,z237,z4,z42,z5,z6]),(1,[z210,z8,z1,z4,z94,z6]),(0,[z8,z1,z2,z4,z583,z5,z6])],[(0,[z216,z8,z1,z2,z4,z5,z6]),(0,[z584,z8,z1,z2,z4,z5,z6]),(0,[z585,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z586,z2,z4,z5,z6]),(0,[z8,z319,z1,z39,z2,z5,z6]),(0,[z21,z8,z1,z2,z4,z65,z6]),(0,[z8,z1,z2,z4,z587,z5,z6])]],
   [[(0,[z8,z588,z1,z2,z4,z5,z6]),(0,[z8,z1,z339,z2,z4,z5,z6]),(0,[z8,z1,z2,z27,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z564,z6]),(0,[z8,z1,z2,z67,z4,z16,z6])],[(0,[z8,z1,z2,z4,z5,z6,z589]),(0,[z8,z1,z2,z4,z590,z5,z6]),(0,[z591,z21,z8,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z592,z6]),(0,[z111,z1,z2,z4,z74,z5,z6]),(0,[z52,z8,z1,z4,z5,z186,z6]),(0,[z8,z1,z2,z4,z5,z593,z6]),(0,[z8,z1,z2,z381,z4,z5,z6]),(0,[z210,z8,z1,z2,z4,z94,z6])],[(0,[z240,z8,z1,z39,z4,z5,z6]),(0,[z8,z66,z1,z39,z2,z5,z6]),(0,[z8,z64,z2,z4,z5,z65,z6]),(0,[z279,z8,z1,z2,z4,z5,z6]),(0,[z8,z594,z1,z2,z4,z5,z6])],[(1,[z33,z1,z76,z4,z5,z6]),(0,[z0,z21,z8,z1,z2,z4,z5]),(0,[z8,z1,z41,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z5,z6,z595]),(0,[z8,z1,z2,z4,z5,z596,z6])],[(0,[z8,z1,z2,z4,z5,z597,z6]),(0,[z21,z15,z8,z1,z2,z4,z6]),(0,[z137,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z94,z91,z6]),(0,[z93,z8,z66,z1,z4,z5,z6]),(0,[z177,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z6,z43]),(0,[z8,z1,z598,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z599,z16,z6])],[(0,[z155,z8,z1,z2,z4,z245,z6]),(0,[z8,z1,z2,z4,z5,z600,z6]),(0,[z155,z8,z1,z2,z4,z16,z6]),(0,[z52,z8,z1,z2,z351,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z601]),(0,[z8,z1,z602,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z603,z5,z6]),(0,[z8,z1,z2,z4,z604,z5,z6]),(0,[z8,z1,z2,z4,z5,z186,z65])]],
   [[(0,[z8,z1,z2,z4,z605,z5,z6]),(0,[z8,z344,z1,z2,z4,z5,z6]),(0,[z606,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z607,z2,z4,z5,z6])],[(1,[z8,z1,z2,z4,z226,z6]),(0,[z185,z8,z40,z1,z4,z5,z6]),(0,[z608,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z609,z2,z4,z5,z6]),(0,[z8,z1,z39,z2,z5,z6,z43]),(0,[z21,z8,z66,z1,z2,z4,z6]),(0,[z177,z8,z1,z2,z9,z5,z6]),(0,[z8,z1,z2,z36,z5,z72,z6]),(0,[z610,z8,z1,z2,z4,z5,z6])],[(1,[z8,z1,z2,z4,z5,z180]),(0,[z17,z8,z1,z2,z207,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z611]),(0,[z279,z8,z2,z4,z5,z6,z107]),(0,[z612,z8,z1,z2,z4,z5,z6])],[(0,[z21,z115,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z613,z6]),(0,[z52,z8,z1,z2,z4,z5,z6]),(0,[z614,z8,z1,z2,z4,z5,z6]),(0,[z615,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z616,z2,z4,z5,z6]),(0,[z617,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z618,z2,z4,z5,z6]),(0,[z8,z1,z2,z619,z4,z5,z6])],[(0,[z620,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z200,z6])],[(0,[z621,z8,z1,z2,z4,z5,z6]),(0,[z8,z192,z1,z76,z2,z5,z6]),(0,[z69,z8,z1,z2,z4,z16,z6]),(0,[z591,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z622,z5,z6]),(0,[z8,z1,z2,z623,z4,z5,z6])],[(0,[z8,z624,z1,z2,z4,z5,z6]),(0,[z625,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z626,z6]),(0,[z62,z8,z1,z2,z4,z5,z25]),(1,[z8,z1,z2,z4,z627,z6]),(0,[z8,z1,z628,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z82])]],
   [[(0,[z8,z1,z629,z2,z4,z5,z6]),(0,[z115,z8,z83,z2,z4,z5,z6]),(0,[z8,z1,z2,z630,z4,z5,z6]),(0,[z631,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z627,z6,z107]),(0,[z8,z1,z2,z9,z4,z72,z6]),(0,[z121,z8,z1,z2,z4,z5,z43]),(0,[z8,z1,z2,z32,z4,z6,z43])],[(0,[z17,z8,z64,z2,z4,z5,z6]),(0,[z8,z632,z1,z2,z4,z5,z6])],[(0,[z633,z8,z1,z2,z4,z5,z6]),(0,[z11,z8,z1,z2,z36,z5,z6]),(0,[z69,z1,z2,z3,z4,z5,z6]),(1,[z477,z8,z1,z2,z4,z5]),(0,[z8,z1,z2,z4,z5,z634,z6]),(0,[z8,z1,z2,z4,z200,z211,z6]),(0,[z21,z8,z64,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z635,z5,z6]),(0,[z21,z93,z8,z1,z2,z4,z6])],[(0,[z8,z64,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z636,z5,z6])],[(0,[z637,z8,z1,z2,z4,z5,z6]),(0,[z638,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z639,z2,z4,z5,z6]),(0,[z69,z8,z1,z39,z2,z5,z6]),(1,[z111,z1,z2,z4,z74,z6])],[(0,[z8,z1,z2,z4,z5,z25,z43]),(0,[z138,z8,z1,z4,z5,z6,z18]),(0,[z8,z1,z2,z4,z5,z6,z640])],[(0,[z11,z8,z1,z2,z42,z5,z6]),(0,[z8,z319,z2,z4,z194,z5,z6]),(0,[z8,z409,z1,z2,z4,z6,z18]),(0,[z8,z1,z4,z94,z5,z211,z6]),(1,[z8,z1,z19,z4,z5,z186]),(0,[z641,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z115,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z12,z16,z6]),(0,[z21,z62,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z41,z2,z4,z6]),(0,[z642,z8,z1,z2,z4,z5,z6]),(0,[z643,z8,z1,z2,z4,z5,z6]),(0,[z121,z8,z1,z2,z67,z5,z6]),(0,[z21,z8,z1,z2,z4,z6,z6])],[(0,[z8,z1,z2,z4,z644,z5,z6]),(0,[z8,z1,z326,z2,z4,z5,z6])],[(1,[z8,z1,z2,z4,z645,z6]),(0,[z78,z8,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z211,z6]),(0,[z646,z8,z1,z2,z4,z5,z6]),(0,[z8,z647,z1,z2,z4,z5,z6]),(0,[z21,z21,z8,z1,z2,z4,z6])],[(0,[z648,z8,z1,z2,z4,z5,z6]),(0,[z115,z1,z2,z58,z4,z5,z6]),(0,[z8,z1,z2,z4,z74,z72,z6]),(0,[z8,z1,z2,z4,z5,z649,z6]),(0,[z8,z1,z2,z650,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z651,z6]),(0,[z8,z1,z2,z4,z5,z6,z652]),(0,[z8,z1,z2,z4,z5,z627,z6])],[(0,[z216,z8,z1,z2,z4,z645,z6]),(0,[z8,z1,z2,z5,z6,z131,z25]),(0,[z8,z40,z1,z4,z42,z5,z6])],[(0,[z8,z1,z2,z4,z653,z5,z6]),(0,[z654,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z655]),(0,[z21,z8,z1,z19,z2,z4,z6])],[(0,[z8,z1,z2,z4,z5,z6,z511]),(0,[z656,z8,z1,z2,z4,z5,z6]),(0,[z657,z8,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z381,z5,z6]),(0,[z121,z8,z1,z2,z4,z16,z6]),(0,[z229,z8,z1,z2,z4,z16,z6])],[(0,[z8,z1,z658,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z659,z5,z6]),(0,[z8,z1,z2,z4,z200,z5,z6]),(0,[z8,z1,z2,z4,z660,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z661])]],
   [[(0,[z8,z1,z2,z4,z5,z662,z6]),(0,[z155,z8,z1,z76,z4,z5,z6]),(0,[z663,z8,z1,z2,z4,z5,z6]),(0,[z93,z8,z1,z237,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z599,z6]),(0,[z8,z1,z2,z4,z5,z664,z6])],[(0,[z8,z1,z2,z4,z665,z5,z6]),(0,[z8,z1,z2,z4,z5,z666,z6]),(1,[z8,z1,z2,z4,z5,z511]),(0,[z52,z93,z8,z1,z4,z5,z6]),(1,[z8,z1,z174,z4,z5,z6]),(0,[z8,z1,z667,z2,z4,z5,z6]),(0,[z668,z21,z8,z1,z2,z4,z6])],[(1,[z8,z1,z2,z4,z5,z205]),(0,[z138,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z75,z5,z6]),(0,[z8,z669,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z670,z4,z6]),(0,[z8,z1,z2,z4,z16,z16,z6])],[(0,[z8,z1,z76,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z13,z5,z6]),(0,[z8,z64,z1,z2,z4,z75,z6]),(0,[z8,z1,z2,z4,z5,z6,z671]),(0,[z8,z1,z2,z4,z5,z6,z672])],[(0,[z8,z1,z2,z4,z673,z5,z6]),(0,[z62,z1,z2,z4,z5,z47,z6]),(0,[z21,z8,z1,z237,z2,z4,z6]),(0,[z8,z1,z2,z4,z674,z5,z6])],[(0,[z675,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z645,z6]),(1,[z69,z1,z2,z3,z5,z6]),(0,[z8,z1,z2,z4,z676,z5,z6]),(0,[z8,z677,z1,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z26,z6]),(0,[z31,z21,z8,z1,z2,z4,z6]),(0,[z678,z8,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z6,z679]),(0,[z680,z8,z1,z2,z4,z5,z6]),(1,[z8,z219,z2,z4,z5,z6]),(0,[z681,z8,z1,z2,z4,z5,z6]),(1,[z78,z1,z2,z4,z61,z6]),(0,[z8,z1,z2,z4,z682,z5,z6]),(0,[z8,z1,z2,z4,z564,z6,z43]),(0,[z21,z610,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z6,z683]),(0,[z8,z1,z684,z2,z4,z5,z6]),(0,[z8,z1,z685,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z686,z5,z6]),(0,[z8,z1,z2,z4,z687,z5,z6]),(0,[z8,z1,z688,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z465])],[(0,[z8,z1,z2,z4,z689,z5,z6]),(0,[z8,z1,z2,z690,z4,z5,z6])],[(0,[z8,z1,z691,z2,z4,z5,z6]),(1,[z8,z1,z2,z4,z48,z6]),(0,[z8,z1,z2,z4,z5,z6,z18]),(0,[z692,z8,z1,z2,z4,z5,z6]),(0,[z271,z8,z1,z2,z4,z16,z6])],[(0,[z8,z1,z2,z693,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z65,z107]),(0,[z8,z1,z2,z4,z5,z6,z694]),(0,[z8,z1,z2,z4,z695,z5,z6]),(0,[z121,z8,z1,z2,z5,z6,z43]),(0,[z8,z1,z2,z4,z696,z5,z6]),(0,[z8,z1,z2,z670,z4,z5,z6])],[(0,[z8,z40,z41,z2,z4,z5,z6]),(0,[z697,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z67,z42,z5,z6]),(0,[z121,z8,z1,z2,z4,z5,z37])],[(0,[z8,z1,z2,z4,z5,z698,z6]),(0,[z699,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z186,z6]),(0,[z8,z1,z2,z4,z5,z700,z6]),(0,[z21,z8,z1,z2,z4,z6,z82])],[(0,[z8,z1,z171,z2,z4,z5,z6]),(1,[z8,z1,z397,z4,z5,z6]),(0,[z11,z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z74,z211,z6]),(0,[z8,z1,z2,z4,z701,z5,z6]),(0,[z668,z8,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z485])],[(0,[z8,z1,z702,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z703,z5,z6]),(0,[z8,z1,z2,z4,z704,z5,z6]),(0,[z8,z1,z2,z4,z705,z5,z6]),(0,[z8,z1,z706,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z8,z707,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z708,z6]),(0,[z1,z2,z3,z709,z5,z6]),(0,[z710,z8,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z711,z6]),(0,[z177,z8,z1,z2,z6,z465])],[(0,[z8,z1,z712,z2,z5,z6]),(0,[z21,z8,z1,z2,z4,z548]),(0,[z8,z192,z1,z397,z5,z6]),(0,[z8,z713,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z180]),(0,[z8,z1,z2,z4,z714,z6])],[(0,[z8,z1,z2,z4,z135,z6]),(0,[z8,z715,z2,z4,z5,z6]),(0,[z487,z8,z1,z2,z5,z43]),(0,[z279,z8,z2,z716,z5,z6]),(0,[z8,z1,z2,z717,z5,z6])],[(0,[z8,z1,z2,z4,z6,z718]),(0,[z8,z1,z2,z4,z719,z6]),(0,[z8,z1,z4,z16,z6,z113])],[(0,[z21,z216,z34,z2,z4,z6]),(0,[z141,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z720,z6]),(0,[z8,z1,z2,z721,z5,z6]),(0,[z8,z722,z1,z2,z4,z6]),(0,[z8,z57,z2,z4,z91,z6]),(0,[z105,z121,z1,z2,z5,z43])],[(0,[z17,z8,z4,z5,z113,z18]),(0,[z21,z8,z1,z2,z4,z405])],[(0,[z8,z1,z2,z194,z5,z511]),(0,[z8,z1,z2,z4,z723,z6])],[(0,[z21,z476,z8,z1,z2,z4]),(0,[z44,z93,z8,z4,z5,z6])]],
   [[(0,[z8,z1,z724,z4,z5,z6]),(0,[z477,z8,z1,z2,z4,z200]),(0,[z52,z8,z194,z42,z5,z6]),(0,[z8,z1,z2,z4,z725,z6]),(0,[z8,z1,z2,z726,z5,z6]),(0,[z279,z8,z2,z4,z5,z65])],[(0,[z8,z1,z727,z2,z5,z6]),(0,[z8,z1,z2,z728,z4,z6])],[],[(0,[z8,z1,z729,z4,z5,z6]),(0,[z730,z1,z2,z4,z5,z6]),(0,[z638,z8,z1,z2,z4,z16]),(0,[z17,z138,z8,z4,z5,z18])],[(0,[z8,z1,z2,z5,z37,z511]),(0,[z0,z1,z2,z4,z5,z511]),(0,[z111,z1,z2,z4,z74,z6]),(0,[z0,z1,z2,z4,z16,z25]),(0,[z8,z2,z4,z5,z6,z164]),(0,[z8,z1,z715,z2,z5,z6]),(0,[z8,z1,z731,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z732]),(0,[z105,z21,z1,z2,z4,z5])],[(1,[z1,z733,z4,z5,z6]),(0,[z70,z1,z2,z4,z48,z6]),(0,[z8,z319,z2,z194,z16,z6])],[(0,[z8,z1,z171,z2,z5,z6]),(0,[z308,z1,z58,z4,z5,z6]),(0,[z8,z1,z2,z4,z734,z180])],[(0,[z8,z1,z2,z4,z179,z6]),(0,[z8,z1,z2,z735,z5,z6]),(0,[z8,z1,z2,z736,z5,z6]),(0,[z8,z1,z2,z87,z5,z6]),(0,[z101,z1,z2,z4,z6,z73])]],
   [[(0,[z426,z8,z1,z2,z179,z6]),(0,[z21,z737,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z645,z6]),(0,[z8,z738,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z739,z6])],[(0,[z8,z1,z740,z4,z5,z6]),(0,[z240,z8,z66,z1,z5,z6]),(0,[z93,z8,z66,z1,z5,z6]),(0,[z177,z8,z1,z2,z36,z6])],[],[(0,[z741,z8,z1,z2,z4,z6]),(0,[z33,z1,z76,z77,z5,z6]),(0,[z52,z8,z4,z80,z48,z6]),(0,[z742,z1,z2,z4,z5,z6]),(0,[z52,z505,z8,z4,z5,z6]),(0,[z137,z8,z2,z4,z200,z6]),(0,[z8,z2,z4,z5,z6,z743])],[(0,[z8,z744,z2,z4,z5,z6]),(0,[z15,z8,z2,z193,z5,z6]),(0,[z8,z1,z2,z4,z745,z6]),(0,[z8,z64,z2,z4,z5,z65]),(0,[z21,z8,z64,z2,z4,z65]),(0,[z105,z1,z2,z42,z5,z6]),(0,[z185,z8,z1,z87,z5,z107]),(0,[z21,z8,z2,z4,z6,z164])],[(0,[z8,z1,z204,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z746]),(0,[z8,z1,z2,z747,z5,z6])],[(0,[z8,z1,z2,z4,z748,z6]),(0,[z8,z1,z2,z4,z749,z6]),(0,[z8,z1,z2,z4,z750,z6]),(0,[z8,z39,z715,z2,z5,z6]),(0,[z8,z1,z2,z36,z717,z6]),(0,[z751,z8,z1,z4,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z752,z6]),(0,[z1,z738,z2,z4,z5,z6]),(0,[z8,z2,z4,z753,z5,z6]),(0,[z8,z1,z2,z4,z754,z6]),(0,[z755,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z174,z4,z6]),(0,[z8,z1,z2,z9,z203,z6])],[(0,[z8,z1,z2,z4,z756,z6]),(0,[z8,z2,z4,z5,z65,z589]),(0,[z21,z17,z8,z2,z4,z18]),(0,[z8,z1,z2,z4,z5,z757]),(0,[z21,z8,z1,z2,z203,z37]),(0,[z307,z8,z2,z4,z6,z160])],[(0,[z758,z8,z1,z4,z5,z6]),(0,[z52,z8,z256,z4,z5,z6]),(0,[z8,z1,z759,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z253])],[(0,[z8,z760,z2,z4,z5,z6]),(0,[z11,z0,z21,z1,z2,z4]),(0,[z620,z21,z8,z1,z2,z4]),(0,[z8,z1,z761,z4,z5,z6])],[(0,[z8,z344,z2,z4,z135,z6]),(0,[z8,z2,z4,z5,z65,z762])],[(0,[z69,z1,z2,z3,z5,z6]),(0,[z8,z1,z2,z5,z6,z131]),(0,[z763,z8,z1,z2,z4,z6]),(0,[z15,z240,z8,z39,z5,z6]),(0,[z8,z1,z2,z4,z26,z6])],[(0,[z8,z1,z449,z42,z5,z6]),(0,[z78,z1,z2,z4,z61,z6]),(0,[z477,z8,z1,z2,z4,z16])],[(0,[z426,z1,z2,z5,z47,z6]),(0,[z8,z1,z4,z753,z5,z6]),(0,[z764,z8,z2,z4,z5,z6]),(0,[z8,z1,z2,z765,z16,z6])]],
   [[(0,[z8,z1,z2,z4,z5,z766]),(0,[z8,z1,z2,z4,z767,z6]),(0,[z768,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z769,z6]),(0,[z8,z1,z2,z770,z5,z6])],[(0,[z771,z8,z1,z2,z4,z6]),(0,[z8,z772,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z676]),(0,[z21,z141,z1,z2,z4,z6]),(0,[z52,z21,z8,z4,z80,z6])],[(0,[z8,z1,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z245,z6]),(0,[z8,z1,z2,z4,z5,z773]),(0,[z8,z1,z2,z4,z774,z6]),(0,[z8,z409,z1,z4,z6,z113]),(0,[z8,z1,z2,z4,z389,z16])],[(0,[z78,z1,z2,z4,z775,z6]),(0,[z426,z8,z1,z2,z16,z6]),(0,[z70,z1,z2,z4,z5,z84])],[(0,[z8,z1,z776,z4,z5,z6]),(0,[z8,z1,z2,z777,z5,z6]),(0,[z21,z8,z1,z2,z4,z778])],[(0,[z8,z1,z2,z779,z5,z6]),(0,[z8,z1,z397,z4,z5,z6]),(0,[z8,z1,z2,z148,z5,z6]),(0,[z8,z1,z2,z4,z780,z6]),(0,[z279,z8,z2,z4,z16,z6])],[(0,[z8,z1,z2,z4,z23,z6]),(0,[z781,z8,z1,z2,z4,z6])],[(0,[z8,z1,z782,z2,z4,z6]),(0,[z8,z1,z2,z4,z783,z6]),(0,[z784,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z785,z6])]],
   [[(0,[z8,z344,z171,z2,z5,z6]),(0,[z8,z1,z2,z4,z786,z6]),(0,[z8,z787,z2,z4,z5,z6]),(0,[z11,z1,z2,z12,z5,z6]),(0,[z8,z1,z2,z4,z13,z6]),(0,[z0,z8,z145,z1,z2,z4]),(0,[z240,z8,z1,z193,z5,z6]),(0,[z8,z339,z2,z4,z16,z6]),(0,[z185,z8,z1,z4,z16,z107]),(0,[z21,z8,z1,z761,z4,z6])],[(0,[z21,z8,z1,z2,z87,z6])],[(0,[z8,z1,z2,z5,z6,z788]),(0,[z21,z8,z1,z204,z4,z6]),(0,[z8,z1,z2,z9,z23,z6]),(0,[z789,z8,z1,z2,z4,z5]),(0,[z69,z1,z2,z583,z5,z6]),(0,[z8,z1,z790,z4,z5,z6]),(0,[z8,z40,z41,z4,z5,z6]),(0,[z52,z8,z4,z80,z5,z84]),(0,[z8,z1,z237,z42,z16,z6]),(0,[z21,z279,z8,z2,z4,z6]),(0,[z8,z1,z2,z32,z4,z6]),(0,[z8,z1,z2,z4,z791,z6]),(0,[z8,z2,z4,z5,z6,z792])],[(0,[z115,z83,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z793,z6]),(0,[z8,z1,z2,z4,z5,z794]),(0,[z105,z1,z2,z4,z5,z25]),(0,[z8,z1,z2,z207,z16,z6]),(0,[z8,z795,z1,z2,z4,z6])],[(0,[z8,z1,z796,z4,z5,z6]),(0,[z8,z1,z797,z4,z5,z6]),(0,[z155,z1,z58,z4,z245,z6]),(0,[z1,z76,z733,z4,z5,z6]),(0,[z8,z219,z2,z4,z135,z6]),(0,[z8,z1,z2,z798,z5,z6]),(0,[z62,z1,z2,z4,z16,z47]),(0,[z8,z1,z2,z799,z5,z6]),(0,[z21,z8,z1,z2,z4,z304]),(0,[z21,z8,z1,z2,z4,z596])],[(0,[z8,z1,z2,z4,z5,z800]),(0,[z21,z69,z1,z2,z3,z6]),(0,[z70,z1,z2,z4,z126,z6]),(0,[z8,z1,z170,z4,z801,z6]),(0,[z8,z1,z2,z4,z72,z354])],[(0,[z8,z1,z2,z4,z802,z6]),(0,[z78,z1,z2,z60,z61,z6]),(0,[z44,z8,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z48,z180]),(0,[z8,z1,z2,z4,z803,z6]),(0,[z8,z1,z4,z5,z186,z804]),(0,[z21,z805,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z806,z6]),(0,[z8,z1,z807,z4,z5,z6]),(0,[z21,z28,z8,z1,z2,z4]),(0,[z808,z1,z2,z4,z5,z6]),(0,[z8,z4,z753,z80,z5,z6]),(0,[z21,z8,z1,z2,z4,z314]),(0,[z315,z8,z1,z2,z203,z6])]],
   [[(0,[z8,z1,z2,z809,z5,z6]),(0,[z8,z344,z204,z4,z5,z6]),(0,[z21,z62,z8,z1,z2,z4]),(0,[z8,z1,z2,z810,z5,z6])],[(0,[z69,z8,z1,z174,z5,z6]),(0,[z8,z1,z2,z811,z5,z6]),(1,[z8,z4,z753,z5,z6])],[(0,[z8,z66,z219,z2,z5,z6]),(0,[z1,z2,z709,z12,z5,z6]),(0,[z8,z1,z2,z812,z5,z6]),(0,[z62,z1,z2,z4,z13,z47]),(0,[z8,z41,z4,z753,z5,z6]),(0,[z8,z1,z2,z4,z75,z6]),(0,[z279,z8,z238,z2,z4,z6]),(0,[z21,z8,z813,z2,z4,z6])],[(0,[z21,z8,z1,z171,z2,z6]),(0,[z8,z192,z814,z2,z5,z6]),(0,[z8,z715,z2,z194,z5,z6]),(0,[z8,z815,z1,z4,z5,z6])],[(0,[z8,z1,z2,z4,z816,z6]),(0,[z817,z8,z2,z4,z5,z6]),(0,[z1,z2,z4,z709,z5,z6]),(0,[z8,z1,z2,z5,z37,z112]),(0,[z8,z1,z2,z4,z818,z6]),(0,[z52,z8,z4,z80,z126,z6]),(0,[z8,z1,z2,z5,z6,z757]),(0,[z819,z8,z2,z4,z5,z6]),(0,[z31,z8,z1,z2,z368,z6])],[(0,[z8,z1,z2,z60,z36,z6]),(0,[z8,z2,z4,z5,z6,z762]),(0,[z8,z339,z2,z5,z6,z43]),(0,[z8,z1,z2,z4,z5,z820]),(0,[z1,z2,z4,z821,z5,z6])],[(0,[z8,z1,z2,z60,z23,z6]),(0,[z11,z8,z339,z2,z5,z6]),(0,[z0,z21,z610,z1,z2,z4]),(0,[z21,z8,z1,z2,z6,z131]),(0,[z8,z1,z2,z4,z801,z6])],[(0,[z8,z1,z2,z4,z5,z822]),(0,[z823,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z332]),(0,[z8,z1,z2,z4,z824,z6]),(0,[z220,z8,z1,z4,z94,z6]),(0,[z8,z1,z2,z4,z95,z6])]],
   [[(0,[z21,z201,z8,z1,z2,z4]),(0,[z8,z1,z2,z402,z16,z6]),(0,[z11,z1,z2,z415,z5,z6]),(0,[z240,z8,z1,z4,z16,z6]),(0,[z8,z1,z2,z4,z825,z6])],[(0,[z21,z8,z1,z2,z60,z6]),(0,[z8,z40,z4,z753,z5,z6]),(0,[z185,z8,z1,z238,z4,z107]),(0,[z121,z8,z1,z2,z16,z43])],[(0,[z11,z1,z2,z709,z5,z6]),(0,[z8,z1,z2,z312,z5,z37]),(0,[z826,z1,z2,z4,z5,z6]),(0,[z8,z2,z4,z827,z5,z6]),(0,[z17,z8,z2,z4,z16,z18]),(0,[z8,z828,z1,z2,z5,z6]),(0,[z8,z1,z2,z5,z6,z829])],[(0,[z8,z1,z2,z77,z16,z6])],[(0,[z8,z344,z2,z4,z16,z6]),(0,[z21,z8,z1,z397,z4,z6]),(0,[z8,z435,z2,z194,z5,z6])],[(0,[z21,z8,z1,z2,z77,z6]),(0,[z830,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z342]),(0,[z8,z1,z4,z801,z5,z6]),(0,[z8,z1,z2,z4,z555,z16]),(0,[z591,z328,z1,z2,z4,z6])],[(0,[z8,z1,z831,z4,z5,z6]),(0,[z8,z1,z2,z832,z5,z6]),(0,[z8,z833,z2,z4,z5,z6]),(0,[z8,z1,z834,z4,z5,z6]),(0,[z138,z8,z1,z4,z5,z186]),(0,[z8,z1,z2,z368,z5,z37])],[(0,[z8,z1,z733,z4,z5,z6]),(0,[z8,z1,z835,z4,z5,z6]),(0,[z8,z1,z759,z2,z5,z6]),(0,[z8,z2,z4,z836,z5,z6]),(0,[z21,z8,z1,z2,z67,z37])]],
   [[(0,[z8,z1,z2,z4,z837,z6]),(0,[z8,z219,z204,z4,z5,z6]),(0,[z8,z344,z2,z4,z23,z6]),(0,[z8,z1,z2,z4,z838,z6]),(0,[z8,z1,z839,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z354])],[(0,[z115,z83,z2,z402,z5,z6]),(0,[z21,z8,z1,z2,z4,z230]),(0,[z70,z1,z2,z193,z5,z6]),(0,[z840,z1,z2,z4,z5,z6]),(0,[z841,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z237,z42,z6])],[(0,[z21,z212,z8,z1,z2,z4]),(0,[z8,z219,z2,z4,z5,z511]),(0,[z842,z8,z1,z2,z4,z6]),(0,[z8,z1,z2,z716,z5,z6]),(1,[z8,z1,z2,z717,z6])],[(0,[z8,z219,z2,z4,z5,z205]),(0,[z8,z344,z39,z2,z5,z6]),(0,[z843,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z844,z5,z6]),(0,[z845,z1,z2,z4,z5,z6])],[(0,[z21,z8,z1,z394,z2,z4]),(0,[z138,z8,z1,z4,z5,z6]),(0,[z668,z8,z1,z22,z4,z6])],[(0,[z155,z1,z733,z4,z5,z6]),(0,[z121,z8,z1,z2,z5,z511]),(0,[z8,z1,z2,z846,z5,z6]),(0,[z8,z1,z2,z4,z847,z6])],[(0,[z8,z848,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z849,z6]),(0,[z8,z1,z204,z194,z5,z6]),(0,[z8,z1,z2,z5,z6,z850]),(0,[z141,z1,z2,z4,z5,z84]),(0,[z8,z1,z2,z851,z5,z6]),(0,[z8,z852,z2,z4,z5,z6])]],
   [[(0,[z21,z8,z1,z2,z4,z341]),(0,[z8,z2,z193,z194,z5,z6])],[(0,[z8,z1,z2,z4,z6,z853]),(0,[z854,z8,z1,z171,z5,z6]),(0,[z8,z1,z855,z2,z5,z6]),(0,[z8,z1,z397,z4,z5,z511]),(0,[z8,z856,z1,z2,z4,z6]),(0,[z8,z857,z2,z4,z5,z6])],[(0,[z8,z1,z397,z4,z5,z205]),(0,[z8,z66,z1,z2,z5,z511]),(0,[z8,z1,z2,z858,z5,z6]),(0,[z141,z1,z4,z42,z5,z6]),(0,[z259,z8,z39,z2,z5,z6]),(0,[z859,z1,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z43])],[(0,[z21,z8,z192,z1,z2,z6]),(0,[z8,z1,z2,z860,z5,z6]),(0,[z8,z1,z2,z4,z861,z6]),(0,[z8,z1,z2,z36,z613,z6]),(0,[z8,z1,z4,z26,z6,z113]),(0,[z21,z8,z1,z2,z4,z406]),(0,[z121,z8,z1,z2,z32,z43])],[(0,[z8,z1,z2,z862,z5,z6]),(0,[z863,z8,z1,z2,z4,z6]),(0,[z11,z1,z2,z12,z5,z511])],[(0,[z11,z1,z2,z12,z5,z205]),(0,[z111,z1,z2,z4,z6,z73]),(0,[z8,z1,z2,z4,z5,z864]),(0,[z52,z8,z4,z753,z5,z6])],[(0,[z8,z1,z2,z865,z5,z6]),(0,[z0,z21,z8,z1,z2,z4]),(0,[z8,z1,z2,z4,z126,z180]),(0,[z8,z40,z423,z4,z5,z6]),(0,[z105,z1,z2,z4,z257,z5]),(0,[z21,z8,z866,z2,z4,z6]),(0,[z867,z8,z1,z2,z5,z6])],[(0,[z8,z219,z397,z4,z5,z6]),(0,[z8,z1,z2,z4,z868,z6])]],
   [[(0,[z8,z1,z2,z4,z869,z6]),(0,[z8,z1,z2,z4,z5,z870]),(0,[z8,z1,z871,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z872]),(0,[z8,z1,z2,z4,z5,z873]),(0,[z8,z1,z2,z4,z874,z43]),(0,[z8,z1,z2,z5,z37,z757])],[(0,[z115,z470,z2,z4,z5,z6]),(0,[z70,z1,z2,z4,z16,z6]),(0,[z8,z1,z875,z4,z5,z6])],[(0,[z11,z219,z2,z12,z5,z6]),(0,[z8,z1,z2,z4,z20,z6]),(0,[z21,z8,z1,z2,z4,z16])],[(0,[z0,z21,z62,z1,z2,z4]),(0,[z8,z1,z2,z4,z827,z6])],[(0,[z8,z1,z2,z4,z876,z6]),(0,[z8,z1,z2,z4,z5,z877]),(0,[z141,z1,z2,z4,z5,z180]),(0,[z8,z1,z2,z4,z878,z6])],[(0,[z216,z738,z2,z4,z5,z6]),(0,[z8,z1,z2,z193,z5,z6]),(0,[z8,z1,z2,z4,z5,z879]),(0,[z8,z1,z2,z4,z880,z6]),(0,[z8,z1,z2,z881,z5,z6]),(0,[z8,z1,z2,z4,z225,z43]),(0,[z8,z1,z2,z4,z257,z564]),(0,[z21,z8,z1,z2,z4,z390])],[(0,[z8,z1,z2,z4,z882,z5]),(0,[z21,z426,z8,z1,z2,z6]),(0,[z21,z8,z1,z2,z4,z124]),(0,[z883,z1,z2,z4,z5,z6])],[]],
   [[(0,[z426,z8,z1,z2,z5,z43]),(0,[z52,z8,z4,z80,z16,z6]),(0,[z52,z8,z132,z4,z5,z6]),(0,[z8,z1,z2,z67,z5,z521]),(0,[z8,z1,z19,z4,z5,z804])],[(0,[z21,z8,z1,z2,z402,z6]),(0,[z8,z1,z2,z884,z5,z6]),(0,[z11,z1,z397,z12,z5,z6]),(0,[z8,z319,z2,z194,z5,z6]),(0,[z8,z1,z2,z4,z5,z885]),(0,[z276,z8,z1,z2,z5,z43])],[(0,[z8,z1,z2,z4,z886,z6]),(0,[z33,z1,z122,z4,z5,z6]),(0,[z8,z1,z887,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z521]),(0,[z21,z244,z8,z1,z2,z4])],[(0,[z8,z1,z888,z4,z5,z6]),(0,[z52,z8,z4,z249,z5,z6]),(0,[z8,z1,z2,z4,z889,z6]),(0,[z8,z1,z4,z5,z6,z113])],[(0,[z324,z1,z2,z4,z61,z6]),(0,[z8,z41,z4,z5,z6,z461]),(0,[z21,z8,z1,z2,z27,z6]),(0,[z105,z21,z1,z2,z4,z43]),(0,[z1,z2,z32,z4,z6,z55])],[(0,[z216,z34,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z890,z6]),(0,[z8,z1,z2,z4,z891,z6])],[(0,[z8,z1,z2,z4,z892,z6]),(0,[z105,z121,z1,z2,z5,z6])],[(0,[z0,z328,z1,z2,z4,z5]),(0,[z8,z119,z2,z194,z5,z6]),(0,[z44,z8,z2,z194,z5,z6]),(0,[z8,z1,z759,z237,z5,z6])]],
   [[(0,[z8,z1,z2,z4,z893,z6]),(0,[z1,z2,z4,z5,z6,z894]),(0,[z8,z1,z2,z351,z16,z6]),(0,[z52,z8,z261,z4,z5,z6]),(0,[z8,z1,z2,z4,z895,z6]),(0,[z17,z8,z2,z4,z5,z762]),(0,[z896,z1,z2,z4,z5,z6]),(0,[z21,z8,z897,z2,z4,z6])],[(0,[z8,z1,z2,z4,z898,z6]),(0,[z8,z899,z2,z4,z5,z6]),(0,[z8,z900,z1,z2,z4,z6]),(1,[z8,z715,z2,z5,z6]),(0,[z8,z1,z685,z42,z5,z6]),(0,[z8,z1,z2,z4,z564,z253])],[(0,[z21,z8,z1,z2,z4,z417]),(0,[z8,z1,z2,z901,z5,z6]),(0,[z8,z1,z2,z193,z5,z180]),(0,[z52,z8,z301,z4,z5,z6]),(0,[z8,z1,z2,z67,z225,z37])],[(0,[z8,z1,z2,z4,z902,z6]),(0,[z8,z1,z4,z5,z6,z903]),(1,[z105,z21,z1,z2,z4]),(0,[z21,z8,z904,z1,z2,z6])],[(0,[z8,z1,z905,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z906]),(0,[z8,z1,z907,z2,z5,z6]),(0,[z8,z1,z908,z4,z5,z6]),(0,[z8,z1,z2,z4,z838,z511]),(0,[z52,z141,z4,z80,z5,z6]),(0,[z8,z1,z2,z4,z48,z84]),(0,[z240,z8,z1,z42,z5,z6]),(0,[z138,z8,z4,z5,z65,z6]),(0,[z8,z1,z2,z67,z5,z37]),(0,[z21,z8,z1,z2,z37,z43])],[(0,[z8,z1,z2,z4,z5,z909]),(1,[z8,z2,z4,z827,z6]),(0,[z8,z339,z2,z67,z5,z6]),(0,[z21,z8,z66,z1,z2,z43]),(0,[z429,z8,z1,z2,z4,z16]),(0,[z8,z1,z2,z4,z6,z778])],[(0,[z8,z1,z2,z4,z5,z910]),(0,[z21,z8,z1,z2,z4,z37])],[(0,[z8,z1,z911,z2,z4,z6]),(0,[z8,z1,z204,z4,z135,z6]),(0,[z912,z8,z1,z4,z5,z6]),(0,[z8,z1,z913,z2,z4,z6])]],
   [[(0,[z8,z1,z2,z4,z914,z6]),(0,[z21,z8,z1,z2,z4,z431]),(0,[z8,z1,z4,z915,z5,z6]),(0,[z21,z8,z1,z2,z4,z436]),(0,[z8,z1,z2,z916,z5,z6]),(0,[z279,z8,z4,z5,z186,z6])],[(0,[z8,z192,z1,z2,z5,z6]),(0,[z917,z8,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z135,z511]),(0,[z8,z918,z2,z4,z5,z6]),(0,[z477,z8,z1,z2,z4,z94]),(0,[z21,z8,z40,z41,z4,z6]),(0,[z8,z1,z2,z4,z175,z6]),(0,[z8,z1,z2,z4,z5,z919])],[(0,[z8,z1,z2,z4,z920,z6]),(0,[z8,z1,z2,z4,z135,z205]),(0,[z21,z8,z1,z2,z148,z6]),(0,[z8,z1,z2,z4,z16,z98]),(0,[z8,z1,z2,z4,z921,z6]),(0,[z8,z1,z2,z4,z5,z253])],[(0,[z8,z1,z2,z4,z922,z6]),(0,[z93,z8,z1,z193,z5,z6]),(0,[z8,z1,z2,z4,z923,z6]),(0,[z924,z8,z2,z4,z5,z6]),(0,[z8,z925,z2,z4,z5,z6]),(0,[z8,z1,z2,z765,z5,z6])],[(0,[z8,z1,z926,z2,z5,z6]),(0,[z21,z15,z8,z39,z2,z6]),(0,[z8,z1,z19,z4,z20,z186])],[(0,[z8,z1,z927,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z454]),(0,[z185,z8,z1,z4,z5,z84]),(0,[z185,z8,z1,z4,z5,z804])],[(0,[z8,z1,z2,z928,z5,z6]),(0,[z477,z78,z8,z1,z2,z4]),(0,[z62,z1,z2,z4,z5,z894]),(0,[z21,z8,z1,z2,z4,z441]),(0,[z138,z8,z1,z929,z5,z6]),(0,[z21,z612,z8,z1,z2,z4])],[(0,[z8,z1,z2,z930,z5,z6]),(0,[z8,z1,z2,z4,z931,z6]),(0,[z155,z1,z58,z4,z16,z6]),(0,[z8,z1,z2,z4,z932,z6]),(0,[z8,z1,z2,z4,z5,z933]),(0,[z105,z1,z2,z4,z564,z6])]],
   [[(0,[z8,z1,z934,z4,z5,z6])],[(0,[z8,z1,z2,z4,z803,z84]),(0,[z279,z8,z2,z4,z5,z6]),(0,[z21,z8,z319,z2,z194,z6]),(0,[z8,z1,z2,z935,z4,z6]),(0,[z936,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z16,z180]),(0,[z8,z1,z238,z2,z4,z6]),(0,[z279,z185,z8,z4,z5,z6]),(0,[z867,z21,z8,z1,z2,z6]),(0,[z546,z610,z1,z2,z4,z6])],[(0,[z8,z103,z2,z4,z91,z6]),(0,[z8,z1,z4,z801,z211,z6]),(0,[z1,z2,z4,z564,z6,z55]),(0,[z8,z1,z2,z4,z778,z82])],[(0,[z8,z1,z2,z4,z937,z6]),(0,[z8,z1,z2,z4,z291,z5]),(0,[z21,z477,z8,z1,z2,z4]),(0,[z426,z8,z1,z2,z5,z37]),(0,[z141,z1,z2,z4,z48,z6]),(0,[z938,z1,z2,z4,z5,z6]),(0,[z939,z1,z2,z4,z5,z6]),(0,[z8,z339,z2,z4,z5,z6]),(0,[z940,z1,z2,z4,z5,z6]),(0,[z44,z8,z4,z42,z5,z6]),(0,[z8,z2,z4,z5,z6,z941]),(0,[z185,z8,z1,z4,z5,z107]),(0,[z21,z8,z1,z19,z4,z186]),(0,[z8,z1,z2,z125,z72,z6]),(0,[z21,z8,z1,z942,z4,z6]),(0,[z8,z1,z2,z4,z5,z778])],[(0,[z8,z1,z2,z4,z943,z6]),(0,[z11,z28,z1,z2,z5,z6]),(0,[z8,z1,z2,z60,z16,z6]),(0,[z8,z1,z2,z944,z16,z6])],[(0,[z817,z8,z192,z2,z5,z6]),(0,[z8,z1,z397,z4,z135,z6]),(0,[z69,z1,z2,z5,z6,z129])],[(0,[z8,z945,z2,z4,z5,z6]),(0,[z8,z1,z2,z207,z5,z6]),(0,[z21,z8,z1,z39,z2,z43]),(0,[z8,z552,z2,z4,z5,z65])]],
   [[(0,[z8,z219,z2,z42,z5,z6]),(0,[z105,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z179,z6,z131]),(0,[z8,z1,z2,z4,z946,z6]),(0,[z8,z1,z22,z4,z94,z6]),(0,[z185,z8,z4,z5,z164,z107]),(0,[z21,z8,z918,z2,z4,z6])],[(0,[z8,z1,z2,z4,z947,z6]),(0,[z11,z1,z2,z12,z135,z6]),(0,[z0,z1,z2,z5,z131,z25]),(0,[z8,z948,z2,z4,z5,z6]),(0,[z8,z1,z4,z5,z6,z949])],[(0,[z8,z1,z2,z4,z5,z950]),(0,[z8,z1,z2,z4,z951,z6]),(0,[z8,z1,z952,z4,z5,z6])],[(0,[z8,z1,z2,z4,z953,z6]),(0,[z8,z66,z1,z397,z5,z6]),(0,[z8,z632,z66,z1,z5,z6]),(0,[z8,z1,z2,z4,z176,z6])],[(0,[z8,z1,z2,z954,z5,z6])],[(0,[z216,z34,z2,z4,z493,z6]),(0,[z8,z1,z2,z955,z5,z6]),(0,[z8,z1,z2,z4,z5,z956]),(0,[z8,z1,z204,z4,z5,z511]),(0,[z8,z145,z1,z2,z6,z131])],[(0,[z8,z1,z204,z4,z5,z205]),(0,[z21,z70,z1,z2,z4,z6]),(0,[z8,z1,z2,z4,z957,z6]),(0,[z8,z57,z2,z4,z422,z6])],[(0,[z467,z1,z2,z4,z74,z6]),(0,[z21,z8,z1,z2,z4,z483])]],
   [[(0,[z21,z8,z1,z2,z4,z494]),(0,[z8,z1,z2,z4,z958,z6])],[(0,[z8,z1,z2,z4,z959,z6]),(1,[z1,z2,z4,z775,z6]),(0,[z8,z1,z2,z960,z5,z6])],[(0,[z8,z1,z2,z193,z48,z6]),(0,[z8,z103,z239,z2,z4,z6])],[(0,[z8,z573,z2,z194,z5,z6]),(0,[z8,z1,z2,z4,z961,z5]),(0,[z111,z1,z2,z4,z775,z6]),(0,[z21,z62,z1,z2,z4,z47]),(0,[z8,z1,z2,z4,z962,z6]),(0,[z279,z8,z2,z4,z627,z6])],[(0,[z8,z1,z2,z60,z291,z5]),(0,[z240,z8,z1,z4,z5,z6]),(0,[z8,z1,z2,z4,z126,z84]),(0,[z21,z8,z1,z2,z42,z43]),(0,[z21,z185,z8,z1,z4,z107])],[(0,[z21,z8,z1,z2,z4,z453]),(0,[z121,z8,z1,z2,z5,z43])],[(0,[z8,z1,z963,z4,z5,z6]),(0,[z11,z8,z1,z174,z5,z6]),(0,[z964,z1,z2,z4,z5,z6]),(0,[z8,z550,z2,z194,z5,z6]),(0,[z8,z1,z965,z4,z5,z6]),(0,[z17,z8,z2,z4,z5,z18]),(0,[z8,z1,z2,z381,z16,z6]),(0,[z966,z1,z2,z4,z5,z6])],[(0,[z967,z8,z1,z2,z4,z6]),(0,[z768,z8,z1,z2,z4,z511]),(0,[z654,z8,z2,z4,z200,z6]),(0,[z93,z141,z1,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z700]),(0,[z21,z936,z1,z2,z4,z6])]],
   [[(0,[z8,z1,z968,z4,z5,z6]),(0,[z115,z83,z171,z2,z5,z6]),(0,[z8,z1,z2,z4,z5,z969]),(0,[z8,z1,z2,z4,z970,z6]),(0,[z8,z1,z2,z4,z971,z6]),(0,[z8,z1,z2,z4,z972,z6]),(0,[z138,z8,z1,z4,z5,z84]),(0,[z973,z8,z1,z2,z4,z5]),(0,[z21,z240,z8,z1,z4,z6]),(0,[z8,z64,z2,z4,z5,z762]),(0,[z8,z66,z1,z759,z5,z6]),(0,[z210,z8,z1,z4,z6,z485]),(0,[z8,z904,z1,z2,z5,z6])],[(0,[z8,z1,z974,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z511]),(0,[z477,z78,z1,z2,z4,z61]),(0,[z21,z8,z1,z2,z4,z384]),(0,[z8,z1,z174,z4,z16,z6]),(0,[z975,z8,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z507]),(0,[z324,z1,z2,z4,z221,z6])],[(0,[z854,z8,z1,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z205]),(0,[z8,z371,z1,z4,z94,z6]),(0,[z8,z56,z2,z4,z200,z6]),(0,[z121,z8,z1,z2,z5,z757])],[(0,[z8,z1,z204,z4,z23,z6]),(0,[z8,z976,z2,z4,z5,z6]),(0,[z8,z1,z2,z709,z5,z6]),(0,[z8,z1,z2,z4,z977,z6])],[(0,[z8,z1,z2,z4,z978,z6]),(0,[z8,z1,z2,z4,z979,z6]),(0,[z477,z8,z1,z2,z148,z5]),(0,[z21,z8,z1,z2,z4,z513]),(0,[z8,z1,z4,z94,z801,z6])],[(0,[z8,z1,z2,z980,z5,z6]),(0,[z11,z1,z204,z12,z5,z6]),(0,[z8,z1,z2,z4,z23,z511]),(0,[z981,z1,z2,z4,z5,z6]),(0,[z137,z8,z2,z4,z827,z6]),(0,[z17,z8,z409,z2,z4,z18])],[(0,[z8,z1,z2,z4,z982,z6]),(0,[z8,z1,z2,z4,z23,z205]),(0,[z69,z1,z2,z3,z16,z6]),(0,[z8,z1,z2,z983,z5,z6]),(0,[z8,z1,z2,z4,z984,z6]),(0,[z21,z8,z1,z2,z4,z518]),(0,[z8,z1,z2,z4,z16,z671]),(0,[z21,z8,z1,z2,z4,z520])],[(0,[z8,z985,z2,z4,z5,z6]),(0,[z8,z219,z2,z4,z16,z6]),(0,[z8,z986,z2,z4,z5,z6]),(0,[z62,z8,z856,z1,z2,z4]),(0,[z52,z8,z351,z80,z5,z6]),(0,[z8,z1,z2,z4,z63,z16]),(0,[z17,z8,z2,z207,z5,z18]),(0,[z138,z8,z1,z4,z5,z107]),(0,[z8,z1,z2,z4,z987,z6])]],
   [[(0,[z8,z1,z2,z988,z5,z6]),(0,[z8,z1,z39,z2,z5,z511]),(0,[z21,z8,z1,z2,z351,z6]),(0,[z21,z181,z8,z1,z2,z4]),(0,[z8,z1,z326,z4,z211,z6]),(0,[z8,z1,z2,z4,z5,z354])],[(0,[z8,z1,z2,z4,z5,z989]),(0,[z8,z1,z990,z4,z5,z6]),(0,[z8,z145,z1,z2,z4,z43]),(0,[z21,z8,z856,z1,z2,z4]),(0,[z93,z8,z1,z759,z5,z6]),(0,[z8,z991,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z528])],[(0,[z8,z1,z2,z992,z5,z6]),(0,[z0,z21,z1,z2,z3,z4]),(0,[z78,z1,z2,z148,z61,z6]),(0,[z21,z8,z1,z2,z381,z6]),(0,[z993,z1,z2,z4,z5,z6]),(1,[z8,z1,z4,z5,z804])],[(0,[z8,z219,z2,z4,z23,z6])],[(0,[z141,z2,z4,z194,z5,z6]),(0,[z141,z1,z2,z4,z126,z6]),(0,[z8,z1,z994,z4,z5,z6]),(0,[z8,z995,z2,z4,z5,z6]),(0,[z996,z8,z1,z2,z5,z6]),(0,[z1,z2,z4,z16,z6,z55]),(0,[z21,z8,z852,z2,z4,z6])],[(0,[z8,z1,z2,z997,z5,z6]),(0,[z8,z1,z4,z5,z186,z526]),(0,[z8,z2,z4,z627,z6,z164]),(0,[z8,z1,z2,z9,z72,z6])],[(0,[z8,z1,z397,z4,z16,z6]),(0,[z998,z8,z1,z2,z4,z6]),(0,[z8,z1,z999,z2,z5,z6]),(0,[z8,z64,z2,z4,z75,z65]),(0,[z21,z1,z2,z4,z55,z43])],[(0,[z610,z1,z2,z4,z74,z6]),(0,[z1000,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z163,z16]),(0,[z8,z1,z942,z4,z5,z6])]],
   [[(0,[z367,z1,z2,z4,z74,z6]),(0,[z70,z1,z2,z351,z5,z6]),(0,[z8,z1,z2,z193,z5,z84]),(0,[z8,z2,z4,z5,z65,z84]),(0,[z8,z1,z2,z4,z1001,z6]),(0,[z21,z8,z1,z2,z4,z551])],[(0,[z11,z1,z2,z12,z16,z6]),(0,[z8,z1,z2,z4,z1002,z6]),(0,[z17,z8,z2,z4,z5,z84]),(0,[z8,z1,z2,z4,z5,z1003]),(0,[z580,z8,z2,z4,z200,z6]),(0,[z8,z813,z2,z4,z5,z6]),(1,[z8,z1,z2,z5,z757]),(0,[z21,z8,z1,z2,z368,z37])],[(0,[z8,z1,z2,z1004,z5,z6]),(0,[z8,z1,z397,z4,z23,z6]),(0,[z8,z409,z1,z2,z4,z6]),(0,[z8,z1,z2,z27,z16,z6])],[(0,[z8,z1,z2,z4,z5,z1005]),(0,[z1,z2,z4,z775,z61,z6]),(0,[z0,z1,z2,z4,z5,z25]),(0,[z8,z1,z170,z4,z211,z6])],[(0,[z105,z1,z2,z4,z5,z511]),(1,[z1,z2,z709,z5,z6]),(0,[z1006,z1,z2,z4,z5,z6]),(0,[z8,z103,z2,z4,z827,z6]),(0,[z8,z1,z2,z1007,z5,z6])],[(0,[z70,z1,z2,z4,z5,z6]),(0,[z11,z1,z2,z12,z23,z6]),(0,[z1,z2,z4,z5,z47,z511]),(0,[z15,z8,z39,z2,z16,z6])],[(0,[z8,z1,z2,z1008,z5,z6]),(0,[z93,z8,z192,z1,z5,z6]),(0,[z477,z8,z1,z2,z60,z5]),(0,[z8,z1,z2,z4,z124,z6]),(0,[z8,z1,z2,z4,z1009,z6]),(0,[z138,z8,z409,z1,z4,z6]),(0,[z271,z8,z1,z2,z6,z465])],[(0,[z8,z1010,z1,z2,z4,z6])]],
   [[(0,[z8,z1,z4,z1011,z5,z6]),(0,[z477,z8,z1,z2,z4,z72]),(0,[z8,z1,z2,z4,z1012,z6]),(0,[z15,z8,z39,z174,z5,z6]),(0,[z8,z1,z2,z4,z1013,z6])],[(0,[z738,z34,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1014,z6]),(0,[z8,z1015,z1,z2,z4,z6]),(0,[z477,z8,z1,z2,z4,z91]),(0,[z8,z1,z2,z60,z72,z6]),(0,[z279,z8,z2,z4,z5,z18])],[(0,[z1,z2,z4,z5,z894,z25]),(0,[z8,z1,z2,z193,z126,z6]),(0,[z8,z866,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z1016,z6])],[(0,[z8,z1,z2,z4,z1017,z6]),(0,[z8,z1,z2,z1018,z5,z6]),(0,[z538,z83,z2,z4,z5,z6]),(0,[z763,z8,z1,z2,z4,z84]),(0,[z8,z1,z1019,z4,z5,z6]),(0,[z8,z1,z170,z670,z4,z6])],[(0,[z21,z8,z1,z2,z4,z6]),(0,[z8,z1020,z1,z4,z5,z6]),(0,[z11,z1,z2,z566,z5,z6]),(0,[z8,z1,z2,z4,z1021,z6]),(1,[z8,z1,z2,z4,z778])],[(0,[z8,z1,z2,z1022,z5,z6]),(0,[z1023,z8,z1,z2,z4,z6]),(0,[z21,z33,z1,z76,z4,z6]),(0,[z830,z8,z1,z2,z4,z205]),(0,[z8,z1,z2,z1024,z5,z6]),(0,[z210,z8,z1,z4,z801,z6])],[(0,[z8,z2,z4,z5,z6,z1025]),(0,[z44,z8,z39,z2,z5,z6]),(0,[z21,z8,z1,z2,z858,z6]),(0,[z21,z8,z1,z2,z960,z6])],[(0,[z1,z2,z4,z5,z47,z894]),(0,[z1,z2,z4,z5,z6,z1026]),(0,[z8,z1,z2,z4,z599,z354]),(0,[z8,z1,z2,z67,z95,z37])]],
   [[(0,[z8,z1,z1027,z4,z5,z6]),(0,[z8,z1,z2,z4,z1028,z6]),(0,[z8,z1,z383,z42,z5,z6]),(0,[z62,z1,z2,z4,z124,z47]),(0,[z141,z1,z2,z193,z5,z6]),(0,[z8,z1,z2,z4,z5,z1029]),(0,[z8,z1,z2,z4,z16,z84]),(0,[z8,z1,z2,z4,z1030,z6]),(0,[z8,z1,z2,z4,z1031,z6]),(0,[z8,z1,z2,z4,z564,z6])],[(0,[z8,z1,z2,z4,z1032,z6]),(0,[z8,z1,z2,z4,z1033,z6]),(0,[z105,z1,z2,z194,z5,z6]),(0,[z21,z8,z1,z875,z4,z6])],[(0,[z8,z1034,z2,z4,z5,z6]),(0,[z8,z1035,z2,z4,z5,z6]),(0,[z0,z426,z1,z2,z5,z25]),(0,[z105,z66,z1,z2,z5,z6]),(0,[z399,z8,z1,z2,z4,z16])],[(0,[z21,z69,z8,z1,z2,z37]),(0,[z52,z8,z193,z80,z5,z6]),(0,[z8,z1,z2,z1036,z5,z6]),(0,[z8,z40,z4,z5,z6,z640]),(0,[z8,z1,z2,z4,z1037,z6]),(0,[z21,z8,z1,z2,z207,z6])],[(0,[z8,z1,z2,z351,z5,z6]),(0,[z8,z1,z2,z4,z1038,z6]),(0,[z8,z1039,z2,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1040,z6]),(0,[z1041,z8,z1,z2,z4,z6]),(1,[z1,z2,z4,z5,z894]),(0,[z8,z145,z1,z2,z4,z37]),(0,[z8,z1,z2,z368,z36,z6])],[(0,[z8,z1,z2,z4,z1042,z6]),(0,[z8,z1043,z2,z4,z5,z6]),(0,[z21,z8,z1,z790,z4,z6])],[(0,[z8,z1044,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z1045]),(0,[z33,z1,z76,z4,z16,z6]),(0,[z8,z1,z39,z204,z5,z6]),(0,[z8,z1,z2,z1046,z4,z6]),(0,[z8,z1,z2,z4,z225,z6]),(0,[z105,z1,z2,z5,z37,z6])]],
   [[(0,[z544,z34,z2,z4,z5,z6]),(0,[z21,z8,z219,z2,z4,z6]),(0,[z426,z8,z145,z1,z2,z6]),(0,[z105,z1,z2,z4,z5,z47]),(0,[z21,z8,z1,z2,z193,z6]),(0,[z52,z8,z4,z5,z186,z65]),(0,[z21,z8,z1,z2,z4,z532])],[(0,[z8,z1,z2,z4,z5,z6]),(0,[z1047,z8,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1048,z6]),(0,[z21,z8,z1,z2,z4,z180]),(0,[z138,z8,z1,z4,z26,z6])],[(0,[z8,z1,z2,z4,z5,z1049]),(0,[z426,z8,z1,z2,z5,z6]),(0,[z8,z1,z2,z4,z1050,z6]),(0,[z210,z8,z1,z4,z94,z6])],[(0,[z8,z1,z2,z4,z1051,z6]),(0,[z8,z1,z2,z4,z775,z6]),(0,[z8,z2,z4,z827,z91,z6]),(0,[z8,z1,z561,z4,z5,z186])],[(0,[z8,z1,z2,z1052,z5,z6]),(0,[z8,z1,z2,z4,z5,z1053]),(0,[z8,z1,z2,z1054,z5,z6]),(0,[z279,z8,z2,z4,z5,z84]),(0,[z8,z1,z2,z4,z1055,z6]),(0,[z8,z2,z4,z16,z6,z164]),(0,[z8,z1,z2,z4,z225,z37])],[(0,[z8,z1,z2,z42,z5,z511]),(0,[z8,z40,z1,z87,z5,z6]),(0,[z21,z44,z8,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z874])],[(0,[z8,z1,z2,z4,z6,z1056]),(0,[z138,z8,z1,z4,z16,z6]),(0,[z8,z1,z2,z4,z1057,z6]),(0,[z105,z21,z1,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1058,z6]),(0,[z8,z1,z759,z42,z5,z6]),(0,[z8,z1,z2,z846,z16,z6])]],
   [[(0,[z8,z1,z2,z1059,z5,z6]),(0,[z1,z2,z4,z5,z47,z59]),(0,[z101,z477,z8,z1,z2,z4]),(0,[z1,z2,z4,z74,z775,z6]),(0,[z141,z1,z2,z4,z16,z6]),(0,[z8,z1,z4,z5,z6,z804])],[(0,[z8,z344,z2,z194,z5,z6]),(0,[z8,z1,z237,z42,z5,z6]),(0,[z8,z1,z280,z42,z5,z6]),(0,[z21,z8,z1,z2,z4,z82])],[(0,[z8,z1,z2,z1060,z5,z6]),(0,[z8,z1,z2,z4,z1061,z6]),(0,[z477,z8,z1,z2,z4,z211]),(0,[z8,z1,z1062,z4,z5,z6])],[(0,[z8,z1,z2,z4,z5,z1063]),(0,[z8,z1,z2,z4,z1064,z6]),(0,[z155,z1,z58,z4,z5,z6]),(0,[z8,z2,z4,z1065,z5,z6]),(0,[z62,z1,z2,z4,z5,z47]),(0,[z8,z1,z193,z42,z5,z6]),(0,[z8,z1,z2,z4,z5,z762])],[(0,[z62,z1,z2,z4,z508,z5]),(0,[z8,z2,z4,z5,z762,z18]),(0,[z8,z1,z326,z4,z459,z6])],[(0,[z8,z1,z2,z4,z5,z1066]),(0,[z216,z34,z2,z4,z645,z6]),(0,[z8,z1,z2,z4,z226,z6]),(0,[z8,z1,z2,z4,z1067,z6]),(0,[z21,z324,z8,z1,z2,z4])],[(0,[z8,z1,z2,z36,z23,z6]),(0,[z8,z1,z2,z4,z734,z6]),(0,[z21,z138,z8,z1,z4,z6]),(0,[z1068,z8,z1,z2,z5,z6]),(0,[z1069,z1,z2,z4,z5,z6])],[(0,[z21,z8,z344,z2,z4,z6]),(0,[z8,z1,z1070,z4,z5,z6]),(0,[z121,z8,z1,z2,z564,z43])]],
   [[(0,[z8,z1,z2,z4,z1071,z6]),(0,[z8,z51,z2,z194,z5,z6]),(0,[z15,z240,z8,z4,z5,z6]),(0,[z8,z1,z2,z67,z5,z651])],[(0,[z8,z1,z2,z60,z5,z6]),(0,[z21,z8,z1,z2,z4,z291]),(0,[z8,z1,z2,z4,z16,z158]),(0,[z52,z70,z4,z80,z5,z6]),(0,[z8,z1,z2,z944,z5,z6]),(0,[z8,z1,z2,z4,z36,z354])],[(0,[z8,z1,z171,z2,z16,z6]),(0,[z8,z1,z397,z42,z5,z6]),(0,[z8,z1,z2,z4,z5,z1072]),(0,[z8,z1,z2,z1016,z5,z6]),(0,[z21,z8,z1,z2,z4,z651]),(0,[z8,z1,z2,z4,z717,z6])],[(0,[z8,z1,z2,z4,z1073,z6]),(0,[z62,z8,z145,z1,z2,z4]),(0,[z8,z1,z4,z5,z6,z1074]),(0,[z8,z1,z2,z4,z6,z1075]),(0,[z8,z1,z2,z4,z627,z6]),(0,[z8,z1,z2,z87,z16,z6])],[(0,[z8,z1,z2,z4,z1076,z6]),(0,[z229,z8,z1,z4,z6,z485])],[(0,[z8,z1,z2,z16,z6,z131]),(0,[z8,z391,z2,z4,z91,z6]),(0,[z21,z8,z1,z2,z4,z652])],[(0,[z477,z8,z1,z2,z4,z5]),(0,[z8,z1,z2,z193,z16,z6]),(0,[z8,z319,z715,z2,z5,z6]),(0,[z8,z1,z174,z67,z5,z6]),(0,[z93,z8,z66,z1,z16,z6]),(0,[z8,z1,z2,z9,z717,z6]),(0,[z21,z8,z1,z740,z4,z6])],[(0,[z8,z1,z2,z402,z5,z6]),(0,[z155,z1,z58,z4,z226,z6]),(0,[z8,z1,z2,z67,z5,z757])]],
   [[(0,[z8,z1,z2,z5,z6,z1077]),(0,[z21,z8,z1,z2,z4,z511]),(0,[z78,z328,z1,z2,z4,z6]),(0,[z1078,z1,z2,z4,z5,z6]),(0,[z1079,z1,z2,z4,z5,z6]),(0,[z21,z8,z339,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z564])],[(0,[z21,z8,z1,z2,z4,z205]),(0,[z52,z8,z1,z87,z5,z6]),(0,[z93,z8,z66,z339,z5,z6]),(0,[z8,z1,z4,z5,z804,z107]),(0,[z185,z8,z1,z4,z627,z107])],[(0,[z8,z1,z2,z77,z5,z6]),(0,[z1080,z8,z1,z2,z4,z5]),(0,[z8,z1,z2,z1081,z5,z6]),(0,[z8,z1,z204,z4,z16,z6]),(0,[z21,z8,z1,z2,z4,z173]),(0,[z8,z1,z2,z747,z16,z6])],[(0,[z8,z344,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1082,z6]),(0,[z8,z1,z2,z4,z1083,z6]),(0,[z8,z1,z19,z4,z5,z186]),(0,[z177,z8,z1,z2,z36,z253])],[(0,[z8,z1,z2,z4,z291,z16]),(0,[z15,z8,z715,z2,z5,z6]),(0,[z8,z1,z1084,z4,z5,z6])],[(0,[z8,z1,z2,z1085,z5,z6]),(0,[z8,z1,z2,z4,z1086,z6]),(0,[z8,z41,z2,z207,z5,z6]),(1,[z8,z2,z4,z5,z762]),(0,[z8,z64,z2,z4,z175,z65]),(0,[z8,z1,z2,z4,z1087,z6]),(0,[z325,z8,z1,z670,z4,z6])],[(0,[z216,z34,z2,z4,z16,z6]),(0,[z608,z34,z2,z4,z5,z6]),(0,[z15,z8,z171,z2,z5,z6]),(0,[z21,z155,z1,z58,z4,z6]),(0,[z382,z1,z76,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z195]),(0,[z8,z1,z2,z4,z1088,z6])],[(0,[z8,z1,z2,z1089,z5,z6]),(0,[z11,z1,z2,z5,z37,z47]),(0,[z11,z484,z1,z2,z5,z6]),(0,[z8,z1,z2,z1090,z5,z6]),(0,[z21,z1091,z1,z2,z4,z6])]],
   [[(0,[z8,z1,z2,z4,z1092,z6]),(0,[z8,z1,z2,z4,z291,z124])],[(0,[z8,z1,z2,z4,z493,z6]),(0,[z8,z1,z171,z990,z5,z6]),(0,[z606,z1,z58,z4,z5,z6]),(0,[z78,z1,z2,z4,z291,z61]),(0,[z8,z1,z2,z4,z1093,z6]),(0,[z244,z1,z2,z4,z5,z47])],[(0,[z8,z1,z1094,z2,z5,z6]),(0,[z44,z8,z2,z193,z5,z6]),(0,[z8,z1,z2,z381,z5,z6]),(0,[z240,z8,z4,z194,z5,z6]),(0,[z21,z8,z1,z2,z4,z465])],[(0,[z21,z8,z1,z316,z2,z4]),(0,[z8,z171,z2,z194,z5,z6]),(0,[z524,z1,z2,z4,z61,z6]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z137,z8,z2,z4,z6,z160]),(0,[z8,z1,z2,z5,z757,z43]),(0,[z21,z121,z8,z1,z2,z43]),(0,[z21,z859,z1,z2,z4,z6])],[(0,[z1095,z8,z1,z2,z4,z5]),(0,[z8,z1,z2,z4,z16,z698]),(0,[z8,z1,z2,z4,z1096,z5]),(0,[z8,z1097,z2,z4,z5,z6]),(0,[z8,z1098,z1,z2,z4,z6]),(1,[z8,z1,z4,z801,z6]),(0,[z8,z1,z2,z4,z1099,z6]),(0,[z8,z1,z2,z770,z16,z6])],[(0,[z8,z1100,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z511]),(0,[z0,z145,z1,z2,z4,z25]),(0,[z8,z1,z174,z4,z5,z6]),(0,[z21,z8,z1,z2,z812,z6])],[(0,[z115,z738,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z205]),(0,[z426,z8,z1,z2,z5,z511]),(0,[z8,z1,z2,z4,z1101,z6]),(1,[z8,z1,z759,z5,z6])],[(0,[z8,z1,z2,z4,z1102,z6])]],
   [[(0,[z8,z1,z2,z4,z1103,z6]),(0,[z8,z1,z2,z4,z5,z1104]),(0,[z8,z814,z2,z4,z5,z6]),(0,[z8,z1,z2,z5,z6,z1105]),(0,[z138,z8,z1,z844,z5,z6]),(0,[z8,z1,z19,z4,z176,z186])],[(0,[z1106,z8,z1,z2,z4,z6]),(0,[z8,z1107,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1108,z6]),(0,[z8,z1,z2,z148,z16,z6]),(0,[z0,z21,z1,z2,z4,z25]),(0,[z8,z1109,z1,z2,z5,z6]),(0,[z8,z1,z2,z351,z48,z6]),(0,[z8,z1,z174,z5,z6,z43])],[(0,[z8,z1,z2,z4,z1110,z5]),(0,[z8,z192,z1,z2,z16,z6]),(0,[z1111,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z1112,z6]),(0,[z8,z1,z2,z929,z5,z6]),(0,[z1,z2,z4,z5,z6,z1113])],[(0,[z8,z219,z2,z4,z5,z6]),(0,[z1114,z8,z1,z2,z4,z6]),(0,[z8,z1,z572,z4,z211,z6]),(0,[z17,z138,z8,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z253])],[(0,[z8,z1,z2,z1115,z5,z6]),(0,[z8,z1,z2,z4,z1116,z5]),(0,[z8,z897,z2,z4,z5,z6]),(0,[z21,z1079,z1,z2,z4,z6])],[(0,[z83,z738,z2,z4,z5,z6]),(0,[z8,z1,z1117,z2,z5,z6]),(0,[z8,z1,z432,z42,z5,z6]),(0,[z21,z93,z8,z66,z1,z6]),(0,[z8,z1,z2,z4,z6,z1118])],[(0,[z8,z1,z1119,z2,z5,z6]),(0,[z8,z1,z2,z4,z48,z6]),(0,[z8,z40,z41,z4,z16,z6]),(0,[z8,z1120,z1,z4,z5,z6]),(0,[z105,z21,z8,z1,z2,z4]),(0,[z21,z8,z1,z2,z881,z6])],[(1,[z738,z2,z4,z5,z6]),(0,[z115,z83,z2,z4,z16,z6]),(0,[z8,z1,z2,z4,z5,z894]),(0,[z8,z1,z2,z1121,z5,z6]),(0,[z8,z1122,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z257,z16])]],
   [[(0,[z8,z1,z2,z4,z1123,z6]),(0,[z1124,z8,z1,z2,z4,z6])],[(0,[z8,z192,z1,z42,z5,z6]),(0,[z69,z8,z339,z2,z5,z6]),(0,[z1,z2,z4,z775,z5,z6]),(0,[z242,z1,z2,z4,z61,z6]),(0,[z8,z1,z2,z1125,z5,z6])],[(0,[z8,z1126,z2,z4,z5,z6]),(0,[z44,z8,z2,z4,z16,z6]),(0,[z8,z1,z2,z717,z72,z6]),(0,[z21,z8,z1,z835,z4,z6]),(0,[z130,z8,z239,z2,z4,z6])],[(0,[z1127,z8,z1,z2,z4,z6]),(0,[z21,z8,z1,z2,z4,z59]),(0,[z8,z1,z2,z4,z257,z124]),(0,[z8,z1,z2,z1128,z5,z6]),(0,[z8,z1,z1129,z4,z5,z6])],[(0,[z8,z1,z2,z4,z1130,z6])],[(0,[z8,z1,z1131,z2,z5,z6]),(0,[z69,z1,z2,z709,z5,z6]),(0,[z21,z8,z1,z2,z4,z469]),(0,[z1132,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z16,z778])],[(0,[z11,z1,z527,z2,z5,z6]),(0,[z663,z1,z2,z4,z61,z6]),(0,[z8,z1,z2,z4,z1133,z6]),(0,[z1091,z1,z2,z4,z5,z6]),(0,[z8,z1,z2,z27,z5,z6]),(0,[z373,z8,z56,z2,z4,z6])],[(0,[z8,z1,z2,z4,z1134,z6]),(0,[z52,z8,z4,z80,z5,z6]),(0,[z21,z8,z1,z2,z4,z84]),(0,[z8,z1,z19,z4,z186,z16]),(0,[z577,z8,z1,z2,z5,z43])]],
   [[(0,[z8,z1135,z2,z4,z5,z6]),(0,[z8,z1,z2,z148,z291,z5]),(0,[z1114,z8,z1,z2,z4,z180]),(0,[z52,z8,z2,z207,z5,z6])],[(0,[z15,z8,z39,z2,z5,z6]),(0,[z21,z8,z1,z4,z6,z113]),(0,[z8,z1,z2,z4,z1136,z6]),(0,[z105,z1,z2,z4,z16,z6])],[(0,[z8,z1,z2,z4,z1137,z6]),(0,[z8,z1,z2,z4,z5,z1138]),(0,[z11,z1,z2,z676,z5,z6]),(0,[z8,z1,z2,z1139,z5,z6]),(0,[z17,z8,z2,z381,z5,z18])],[(0,[z8,z1,z2,z4,z5,z1140]),(0,[z8,z145,z1,z2,z4,z6]),(0,[z8,z1,z4,z5,z186,z84])],[(0,[z1141,z8,z1,z2,z4,z5]),(0,[z21,z115,z83,z2,z4,z6]),(0,[z8,z1,z2,z4,z1142,z6]),(0,[z8,z1,z2,z4,z1143,z6]),(0,[z11,z21,z1,z2,z12,z6]),(0,[z1,z2,z4,z5,z6,z55]),(0,[z101,z21,z8,z1,z2,z4]),(0,[z8,z1,z2,z4,z1144,z6]),(0,[z185,z8,z1,z27,z5,z107])],[(0,[z8,z1145,z2,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z1146]),(0,[z70,z1,z2,z4,z5,z180]),(0,[z1147,z1,z2,z4,z5,z6]),(0,[z8,z189,z41,z4,z5,z6]),(0,[z805,z1,z2,z4,z5,z6]),(0,[z21,z1,z2,z4,z6,z55])],[(0,[z8,z482,z2,z4,z91,z6]),(0,[z15,z141,z2,z4,z5,z6]),(0,[z52,z8,z4,z5,z593,z6]),(0,[z21,z8,z1,z2,z4,z599]),(0,[z121,z1,z2,z5,z55,z43]),(0,[z8,z1,z2,z125,z599,z6])],[(0,[z8,z1,z2,z4,z1148,z6]),(0,[z8,z344,z2,z4,z5,z511]),(0,[z8,z1,z2,z4,z1149,z6]),(0,[z104,z1,z2,z4,z74,z6]),(0,[z8,z1,z2,z351,z5,z84]),(0,[z8,z1,z2,z4,z1150,z6]),(0,[z8,z1,z2,z16,z6,z850])]],
   [[(0,[z8,z1,z2,z4,z1151,z6]),(0,[z8,z344,z2,z4,z5,z205]),(0,[z8,z1,z2,z4,z971,z205]),(0,[z11,z1,z2,z5,z248,z6]),(0,[z69,z1,z2,z603,z5,z6]),(0,[z105,z1,z39,z2,z5,z6]),(0,[z279,z8,z2,z810,z5,z6])],[(0,[z8,z1,z2,z4,z1152,z6]),(0,[z44,z93,z8,z66,z5,z6]),(0,[z8,z238,z2,z4,z6,z164]),(0,[z177,z8,z1,z2,z36,z354]),(0,[z105,z1,z2,z32,z4,z6])],[(0,[z8,z1,z2,z4,z1153,z6]),(0,[z8,z2,z4,z200,z827,z6]),(0,[z17,z8,z2,z4,z26,z18]),(0,[z8,z1154,z2,z4,z5,z6]),(0,[z177,z8,z1,z2,z717,z6])],[(0,[z8,z1,z2,z4,z1155,z6]),(0,[z69,z1,z2,z448,z5,z6])],[(0,[z8,z1,z2,z4,z1156,z6]),(0,[z8,z1,z2,z4,z5,z84]),(0,[z52,z8,z4,z80,z5,z180]),(0,[z52,z181,z8,z4,z5,z6]),(0,[z8,z1,z2,z5,z6,z1157]),(0,[z8,z1,z1158,z2,z4,z6]),(0,[z8,z1,z2,z4,z5,z804]),(0,[z8,z1,z2,z4,z257,z778])],[(0,[z8,z1,z2,z4,z5,z1159]),(0,[z8,z1,z4,z5,z6,z1160]),(0,[z8,z1,z2,z4,z1161,z6]),(0,[z387,z21,z8,z1,z2,z4]),(0,[z334,z8,z1,z2,z36,z6]),(0,[z8,z1,z2,z4,z5,z1162]),(0,[z8,z1,z2,z4,z1163,z6])],[(0,[z8,z1,z1164,z4,z5,z6]),(0,[z111,z477,z8,z1,z2,z4]),(0,[z0,z21,z328,z1,z2,z4]),(0,[z8,z1,z2,z4,z354,z16]),(0,[z8,z1,z2,z4,z6,z874])],[(0,[z0,z426,z1,z2,z5,z6]),(0,[z8,z1,z2,z1165,z5,z6])]],
   [[(0,[z1166,z8,z1,z2,z4,z6]),(0,[z11,z21,z8,z1,z2,z37]),(0,[z8,z1,z658,z4,z211,z6]),(0,[z1167,z8,z1,z2,z5,z6])],[(0,[z33,z192,z1,z76,z5,z6]),(0,[z8,z1,z1168,z2,z4,z6]),(0,[z0,z1,z2,z4,z179,z25]),(0,[z8,z1,z2,z351,z126,z6]),(0,[z1,z2,z4,z5,z6,z1169])],[(0,[z1,z2,z3,z5,z6,z408]),(0,[z8,z1,z2,z4,z1170,z6]),(0,[z21,z8,z1,z2,z194,z43]),(0,[z21,z8,z1,z2,z726,z6])],[(0,[z8,z1,z2,z4,z1171,z6]),(0,[z8,z1,z2,z1172,z5,z6]),(0,[z33,z1,z76,z4,z5,z6]),(0,[z1,z733,z2,z4,z5,z6]),(0,[z21,z8,z1,z2,z4,z666]),(0,[z21,z8,z1,z2,z4,z143])],[(0,[z8,z344,z397,z4,z5,z6]),(0,[z8,z1,z2,z351,z5,z180]),(0,[z8,z1,z2,z4,z1173,z6]),(0,[z737,z1,z2,z4,z5,z6])],[(0,[z8,z1,z2,z1174,z5,z6]),(0,[z8,z1,z2,z4,z5,z1175]),(0,[z21,z8,z1122,z2,z4,z6])],[(0,[z1,z733,z58,z4,z5,z6]),(0,[z33,z1,z733,z4,z5,z6]),(0,[z8,z1,z2,z4,z126,z6]),(0,[z8,z1,z2,z4,z1176,z6]),(0,[z8,z1,z2,z4,z1177,z6]),(0,[z8,z1,z2,z4,z215,z16])],[(0,[z11,z344,z2,z12,z5,z6]),(0,[z477,z8,z1,z2,z4,z36]),(0,[z141,z1,z2,z351,z5,z6]),(0,[z279,z185,z8,z4,z5,z107])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1046).take 186) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1232)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 523, 186] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 103).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 205).take 51).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [103, 102, 51] = true :=
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

end PEqualNP.Outside.L_meta_39227

theorem PEqualNP.Outside.L_meta_39227 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4241291392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4241291392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39227.solve