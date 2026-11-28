import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40433

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4242590912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1021646378c8eccc#64 ++ 0x41021646378c8ecc#64 ++ 0x5067ece7f8c9eccf#64 ++ 0xb5067ece7f8c9ecc#64 : BitVec 256),
   (0x008b0108a05a0550#64 ++ 0x8008b0108a05a055#64 ++ 0xe19b1318e0fe3fff#64 ++ 0x7e19b1318e0fe3ff#64 : BitVec 256),
   (0x06141c150b0570a9#64 ++ 0x006141c150b0570a#64 ++ 0xfe1c1c1f1f0ff0fe#64 ++ 0xefe1c1c1f1f0ff0f#64 : BitVec 256),
   (0x2b601ea01da03a0e#64 ++ 0x02b601ea01da03a0#64 ++ 0x3fe01fe01ff03f0d#64 ++ 0xf3fe01fe01ff03f0#64 : BitVec 256),
   (0x8dffa00016ff8000#64 ++ 0x08dffa00016ff800#64 ++ 0xbfffe0001fffc00b#64 ++ 0xebfffe0001fffc00#64 : BitVec 256),
   (0x4fdedbdec0000000#64 ++ 0x04fdedbdec000000#64 ++ 0xcfffffffe0000007#64 ++ 0xfcfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [9, 6]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000404240000000 0x0000040424000000 0x4067ece7e0000007 0xb4067ece7e000000

def z1 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe19b1318e0fe3fff 0x7e19b1318e0fe3ff

def z2 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c1c1f1f0ff0fe 0xefe1c1c1f1f0ff0f

def z3 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x1064ece71801c000 0x81064ece71801c00

def z4 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe01fe01ff03f0d 0xf3fe01fe01ff03f0

def z5 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe0000007 0xfcfffffffe000000

def z6 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe0001fffc00b 0xebfffe0001fffc00

def z7 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f8c9eccf 0xb5067ece7f8c9ecc

def z8 : W := mkw 0x2f741ea01fa53a0e 0x02f741ea01fa53a0 0xbffc1fe01fffff0f 0xfbffc1fe01fffff0

def z9 : W := mkw 0x4fdedfdfc90070a9 0x04fdedfdfc90070a 0xcfffffffe00030f7 0xfcfffffffe00030f

def z10 : W := mkw 0xafffbea01fffba0e 0x0afffbea01fffba0 0xbfffffe01fffff0f 0xfbfffffe01fffff0

def z11 : W := mkw 0x0021200010c88000 0x00021200010c8800 0x1000000018c9c008 0x01000000018c9c00

def z12 : W := mkw 0x849fa108a25f8550 0x8849fa108a25f855 0xe19ff318e0ffffff 0x7e19ff318e0fffff

def z13 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x21e013e000f03f0d 0x721e013e000f03f0

def z14 : W := mkw 0x00000108a0000550 0x800000108a000055 0x40001318e0003ff4 0x140001318e0003ff

def z15 : W := mkw 0x008b0000005a0000 0x0008b0000005a000 0xa19b000000fe000b 0x6a19b000000fe000

def z16 : W := mkw 0x100160436048c4c0 0x4100160436048c4c 0x4007e007e009c0c2 0x04007e007e009c0c

def z17 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xfffff318ffffffff 0xffffff318fffffff

def z18 : W := mkw 0x89eba00016ff8000 0x089eba00016ff800 0x31e3e0001fffc009 0x031e3e0001fffc00

def z19 : W := mkw 0x8ddfa000067f8000 0x08ddfa000067f800 0xaf9fe000073fc002 0x4af9fe000073fc00

def z20 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x1000000018c9ecc8 0x01000000018c9ecc

def z21 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x8fffe00000000003 0xe8fffe0000000000

def z22 : W := mkw 0xcffffbded6ff8000 0x0cffffbded6ff800 0xffffffffffffc00f 0xfffffffffffffc00

def z23 : W := mkw 0x069f1d1dab5f75f9 0x8069f1d1dab5f75f 0xff9f1f1fffffffff 0xfff9f1f1ffffffff

def z24 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x1e64e0001f01c000 0x81e64e0001f01c00

def z25 : W := mkw 0xcfffffdfdffff0a9 0x0cfffffdfdffff0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z26 : W := mkw 0x02001c0009003008 0x002001c000900300 0x3e001c001f00300c 0xe3e001c001f00300

def z27 : W := mkw 0x2f741eb51fa57aaf 0x02f741eb51fa57aa 0xfffc1fff1fffffff 0xffffc1fff1ffffff

def z28 : W := mkw 0x29eb03a8b4fa0f56 0x829eb03a8b4fa0f5 0xe1fb13f8e0fe3fff 0x7e1fb13f8e0fe3ff

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z30 : W := mkw 0x0414000002050000 0x0041400000205000 0xbe1c00001f0fc00a 0xebe1c00001f0fc00

def z31 : W := mkw 0x00000401090070a9 0x000000401090070a 0x00000000000030f0 0x000000000000030f

def z32 : W := mkw 0x89eba00014fa8000 0x089eba00014fa800 0x01e3e00000f00001 0x001e3e00000f0000

def z33 : W := mkw 0x008b414ae05a0550 0x8008b414ae05a055 0xe1ffffffe0fe3fff 0xfe1ffffffe0fe3ff

def z34 : W := mkw 0x0414000002050000 0x0041400000205000 0x1e0400001f01c000 0x81e0400001f01c00

def z35 : W := mkw 0x008b0000005a0000 0x0008b0000005a000 0xe19b101800fe30ff 0x6e19b101800fe30f

def z36 : W := mkw 0x0021240118c8e088 0x00021240118c8e08 0x5067ec0718c9e0cf 0xa5067ec0718c9e0c

def z37 : W := mkw 0x296004201da03a0e 0x0296004201da03a0 0x3fe000001ff03f09 0xe3fe000001ff03f0

def z38 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc01b0018e00e00f2 0x0c01b0018e00e00f

def z39 : W := mkw 0x04140015020540a1 0x004140015020540a 0xc01c001f000fc0f2 0x0c01c001f000fc0f

def z40 : W := mkw 0x0960000014a00000 0x00960000014a0000 0x01e0000000f00001 0x001e0000000f0000

def z41 : W := mkw 0x4ddec3cac0000000 0x04ddec3cac000000 0x8fffe3e0e0000003 0xf8fffe3e0e000000

def z42 : W := mkw 0x0960000014a00000 0x00960000014a0000 0x3fe000001ff00009 0xe3fe000001ff0000

def z43 : W := mkw 0x0ddec04240000000 0x00ddec0424000000 0xcfffece7e0000007 0xfcfffece7e000000

def z44 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xe0fe000000000000

def z45 : W := mkw 0x02001c15090070a9 0x002001c15090070a 0x40001c1f000030f4 0x040001c1f000030f

def z46 : W := mkw 0x0001000020480440 0x0000100002048044 0xe01b1018e0ce3cff 0x7e01b1018e0ce3cf

def z47 : W := mkw 0x22201c201da03a0e 0x022201c201da03a0 0x3e001c001ff03f0c 0xe3e001c001ff03f0

def z48 : W := mkw 0x4bcadbdec0000000 0x04bcadbdec000000 0x41e3ffffe0000005 0x141e3ffffe000000

def z49 : W := mkw 0x6ffedffedda03a0e 0x06ffedffedda03a0 0xfffffffffff03f0f 0xffffffffffff03f0

def z50 : W := mkw 0x26141eb50b057aaf 0x026141eb50b057aa 0xfe1c1fff1f0ffffe 0xffe1c1fff1f0ffff

def z51 : W := mkw 0x22001ea009003a0e 0x022001ea009003a0 0x00001fe000003f04 0x100001fe000003f0

def z52 : W := mkw 0x849fa000025f8000 0x0849fa000025f800 0x801fe000000fc002 0x0801fe000000fc00

def z53 : W := mkw 0x8fffbd1dbffff5f9 0x88fffbd1dbffff5f 0xffffff1fffffffff 0xfffffff1ffffffff

def z54 : W := mkw 0x0614181403051021 0x0061418140305102 0xee181018070e30fe 0x6ee181018070e30f

def z55 : W := mkw 0x428a5bdec0000000 0x0428a5bdec000000 0xc19b1fffe0000007 0x7c19b1fffe000000

def z56 : W := mkw 0x028b1d08a95a3558 0x8028b1d08a95a355 0xff9b1f18fffe3fff 0xfff9b1f18fffe3ff

def z57 : W := mkw 0x0021200010c88000 0x00021200010c8800 0x1067e00018c9c00b 0xa1067e00018c9c00

def z58 : W := mkw 0x9dffe4637effeccc 0x49dffe4637effecc 0xffffece7ffffeccf 0xfffffece7ffffecc

def z59 : W := mkw 0x302164637de8fece 0x4302164637de8fec 0x7067ece7fff9ffcf 0xb7067ece7fff9ffc

def z60 : W := mkw 0x100164636848eccc 0x4100164636848ecc 0x4007ece7e009ecc6 0x14007ece7e009ecc

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0xc018101800000006 0x6c01810180000000

def z62 : W := mkw 0x1000446368006ccc 0x41000446368006cc 0x40000ce7e0002cc4 0x140000ce7e0002cc

def z63 : W := mkw 0x49ca838880000000 0x049ca83888000000 0x0180030000000000 0x0018003000000000

def z64 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x50000ce7f8c9eccc 0x150000ce7f8c9ecc

def z65 : W := mkw 0x1021606270c88c44 0x41021606270c88c4 0x0063e0e0e0c00c01 0x10063e0e0e0c00c0

def z66 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0xf07ffcfff8cffcff 0xff07ffcfff8cffcf

def z67 : W := mkw 0x049f011da25f45f1 0x8049f011da25f45f 0xc01f001fe00fc0f2 0x0c01f001fe00fc0f

def z68 : W := mkw 0x008a414ac0000000 0x0008a414ac000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z69 : W := mkw 0x849fa000025f8000 0x0849fa000025f800 0xbe1fe0001f0fc00a 0xebe1fe0001f0fc00

def z70 : W := mkw 0x4fdedbdec2050000 0x04fdedbdec205000 0xffffffffff0fc00f 0xfffffffffff0fc00

def z71 : W := mkw 0x002004201880280c 0x0002004201880280 0x10600ce018c02c0d 0xb10600ce018c02c0

def z72 : W := mkw 0x0200180001001000 0x0020018000100100 0x2e00100007001000 0x42e0010000700100

def z73 : W := mkw 0x0614181403051021 0x0061418140305102 0xae18101807061030 0x4ae1810180706103

def z74 : W := mkw 0x4fdedfdec9003008 0x04fdedfdec900300 0xffffffffff00300f 0xfffffffffff00300

def z75 : W := mkw 0x0000444348006088 0x0000044434800608 0x5067ece7f809e0cf 0xb5067ece7f809e0c

def z76 : W := mkw 0x4fdedfdfcb0570a9 0x04fdedfdfcb0570a 0xffffffffff0ff0ff 0xfffffffffff0ff0f

def z77 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbf9800001fffc008 0x4bf9800001fffc00

def z78 : W := mkw 0x8dde800006370000 0x08dde80000637000 0xafffe00007360003 0xeafffe0000736000

def z79 : W := mkw 0x008b0108805a0000 0x0008b0108805a000 0xe19b1318e0fe000f 0x7e19b1318e0fe000

def z80 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe00e30ff 0xfefffffffe00e30f

def z81 : W := mkw 0x1000456be8006ddc 0xc1000456be8006dd 0x40001fffe0003ff4 0x140001fffe0003ff

def z82 : W := mkw 0x008a010880000000 0x0008a01088000000 0xc19b1318e0000007 0x7c19b1318e000000

def z83 : W := mkw 0x4fdfdbdee05a0550 0x84fdfdbdee05a055 0xefffffffe0fe3fff 0xfefffffffe0fe3ff

def z84 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1fe01fe01f000005 0xf1fe01fe01f00000

def z85 : W := mkw 0x89ca800004320000 0x089ca80000432000 0x0180000000300000 0x0018000000030000

def z86 : W := mkw 0x8fffbc151ffff0a9 0x08fffbc151ffff0a 0xfffffc1f1ffff0ff 0xefffffc1f1ffff0f

def z87 : W := mkw 0x102164637bcdfced 0x4102164637bcdfce 0x7067ece7ffcffcff 0xb7067ece7ffcffcf

def z88 : W := mkw 0x2f541e950f2572ab 0x02f541e950f2572a 0xff9c1f1f1f3ff3fe 0xeff9c1f1f1f3ff3f

def z89 : W := mkw 0x4000415ec0000000 0x04000415ec000000 0x4000001fe0000000 0x04000001fe000000

def z90 : W := mkw 0x42005bdec0000000 0x042005bdec000000 0x40001fffe0000004 0x140001fffe000000

def z91 : W := mkw 0x0d54800000000000 0x00d5480000000000 0x0e64e00000000000 0x80e64e0000000000

def z92 : W := mkw 0x0000040108006088 0x0000004010800608 0x40000c07000020c4 0x040000c07000020c

def z93 : W := mkw 0x4fde9b9c83051021 0x04fde9b9c8305102 0xaf98131807061030 0x4af9813180706103

def z94 : W := mkw 0x46145bdec0000000 0x046145bdec000000 0xce1c1fffe0000006 0xfce1c1fffe000000

def z95 : W := mkw 0x4ffffbded0c88000 0x04ffffbded0c8800 0xdffffffff8c9c00f 0xfdffffffff8c9c00

def z96 : W := mkw 0x4fdfdbdee05a0550 0x84fdfdbdee05a055 0xcfffffffe00e00f7 0xfcfffffffe00e00f

def z97 : W := mkw 0x3b617ee37de8fece 0x43b617ee37de8fec 0x7fe7ffe7fff9ffcf 0xf7fe7ffe7fff9ffc

def z98 : W := mkw 0x0001000020480440 0x0000100002048044 0x40030000e0c82ccf 0x340030000e0c82cc

def z99 : W := mkw 0x2beb1fa8bdfa3f5e 0x82beb1fa8bdfa3f5 0xfffb1ff8fffe3fff 0xffffb1ff8fffe3ff

def z100 : W := mkw 0x200002a000000a06 0x0200002a000000a0 0x000003e000000f00 0x1000003e000000f0

def z101 : W := mkw 0x12005c7769007ced 0x412005c7769007ce 0x40001cffe0003cf4 0x140001cffe0003cf

def z102 : W := mkw 0x16357c777bcdfced 0x416357c777bcdfce 0xfe7ffcffffcffcff 0xffe7ffcffffcffcf

def z103 : W := mkw 0x0940028000000000 0x0094002800000000 0x01e003e000000001 0x101e003e00000000

def z104 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc01b0018e0ce2cff 0x3c01b0018e0ce2cf

def z105 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x0fe7efe7e0000001 0x90fe7efe7e000000

def z106 : W := mkw 0x0414001400000000 0x0041400140000000 0xc01c001f00000002 0x0c01c001f0000000

def z107 : W := mkw 0x0414000000000000 0x0041400000000000 0x8e1c000000000002 0xe8e1c00000000000

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0180000000e000a 0x6a0180000000e000

def z109 : W := mkw 0x902124213effeccc 0x4902124213effecc 0x300000001fffecc8 0x0300000001fffecc

def z110 : W := mkw 0x02001c0009003008 0x002001c000900300 0xfe181c181f0e30fe 0xefe181c181f0e30f

def z111 : W := mkw 0x0000040108006088 0x0000004010800608 0x50040c071809e0ce 0xa50040c071809e0c

def z112 : W := mkw 0x069f191ca35f1571 0x8069f191ca35f157 0xef9b1318e7fe3fff 0x7ef9b1318e7fe3ff

def z113 : W := mkw 0x5ffffffff8c8eccc 0x45ffffffff8c8ecc 0xdffffffff8c9eccf 0xfdffffffff8c9ecc

def z114 : W := mkw 0xaffe9ea01fb73a0e 0x0affe9ea01fb73a0 0xbff81fe01ff63f0d 0xfbff81fe01ff63f0

def z115 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xbe1c1c1f1f07d030 0xcbe1c1c1f1f07d03

def z116 : W := mkw 0x449ec15ec0000000 0x0449ec15ec000000 0xc01fe01fe0000002 0x0c01fe01fe000000

def z117 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x01e003e000f00f01 0x101e003e000f00f0

def z118 : W := mkw 0x42005bdec0000000 0x042005bdec000000 0x4067ffffe0000007 0xb4067ffffe000000

def z119 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0x1e040c071f01c000 0x81e040c071f01c00

def z120 : W := mkw 0x0614585640000000 0x0061458564000000 0xce7ffcffe0000007 0xfce7ffcffe000000

def z121 : W := mkw 0x4fdedbdec3051021 0x04fdedbdec305102 0xefffffffe7061037 0xfefffffffe706103

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180130000f03f0d 0x72180130000f03f0

def z123 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xde1c0c1f1f0fc0f2 0x8de1c0c1f1f0fc0f

def z124 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0x0e64ece700000000 0x80e64ece70000000

def z125 : W := mkw 0x2b401e800d20320a 0x02b401e800d20320 0x3f801f001f30330c 0xe3f801f001f30330

def z126 : W := mkw 0x46145fdfcb0570a9 0x046145fdfcb0570a 0xfe1c1fffff0ff0fe 0xffe1c1fffff0ff0f

def z127 : W := mkw 0x02001c010b0570a9 0x002001c010b0570a 0x3e001c001f0ff0fc 0xe3e001c001f0ff0f

def z128 : W := mkw 0x02001c150b0570a9 0x002001c150b0570a 0x70001c1f1f0ff0fc 0x070001c1f1f0ff0f

def z129 : W := mkw 0x8dffa10896ff8000 0x08dffa10896ff800 0xfffff318ffffc00f 0xffffff318ffffc00

def z130 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x5067ece7f801c007 0xb5067ece7f801c00

def z131 : W := mkw 0x5f75fef778c8eccc 0x45f75fef778c8ecc 0x5e67ece7f8c9eccf 0xb5e67ece7f8c9ecc

def z132 : W := mkw 0xadffa2a016ff8a06 0x0adffa2a016ff8a0 0xbfffe3e01fffcf0b 0xfbfffe3e01fffcf0

def z133 : W := mkw 0x6ffe9fbc9da03a0e 0x06ffe9fbc9da03a0 0xbff81ff81ff03f0d 0xfbff81ff81ff03f0

def z134 : W := mkw 0xcfde9b9c86370000 0x0cfde9b9c8637000 0xaf98131807360000 0x4af9813180736000

def z135 : W := mkw 0x8021200016ff8000 0x08021200016ff800 0x300000001fffc008 0x0300000001fffc00

def z136 : W := mkw 0x1021646278c8ac4c 0x41021646278c8ac4 0x1063ece0f8c02c0d 0xb1063ece0f8c02c0

def z137 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0xfff81ff81ffe3fff 0xffff81ff81ffe3ff

def z138 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x8ffcffff00000000 0xc8ffcffff0000000

def z139 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0x21831300e0f03f0d 0x721831300e0f03f0

def z140 : W := mkw 0x8dffa01516ffc0a1 0x08dffa01516ffc0a 0xffffe01f1fffc0fb 0xeffffe01f1fffc0f

def z141 : W := mkw 0x06141c1508006088 0x006141c150800608 0xde1c1c1f1809e0ce 0xede1c1c1f1809e0c

def z142 : W := mkw 0x2bea1fa89db23b1e 0x82bea1fa89db23b1 0xbff81ff81ff63f3d 0xfbff81ff81ff63f3

def z143 : W := mkw 0x4940c2c240000000 0x04940c2c24000000 0x0060e0e000000000 0x00060e0e00000000

def z144 : W := mkw 0x008a010880000000 0x0008a01088000000 0x01830300e0000001 0x101830300e000000

def z145 : W := mkw 0x9dffe56bfeffeddc 0xc9dffe56bfeffedd 0xffffffffffffffff 0xffffffffffffffff

def z146 : W := mkw 0x0960000014a00000 0x00960000014a0000 0x3fe013001ff03f0d 0xf3fe013001ff03f0

def z147 : W := mkw 0x1021656bf8c8eddc 0xc1021656bf8c8edd 0x5067fffff8c9ffff 0xb5067fffff8c9fff

def z148 : W := mkw 0x14156057624dc4e1 0x414156057624dc4e 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z149 : W := mkw 0x0020000014a00000 0x00020000014a0000 0x300000001ff00008 0x0300000001ff0000

def z150 : W := mkw 0x4fde9b9c80000000 0x04fde9b9c8000000 0x8f98131800000000 0x48f9813180000000

def z151 : W := mkw 0x0b405ac240000000 0x00b405ac24000000 0x4fe7ffe7e0000007 0xf4fe7ffe7e000000

def z152 : W := mkw 0x80012000025f8000 0x080012000025f800 0x00000000000fc000 0x000000000000fc00

def z153 : W := mkw 0x041404010b0570a9 0x0041404010b0570a 0xbe1c00001f0ff0fa 0xebe1c00001f0ff0f

def z154 : W := mkw 0x000004010b0570a9 0x0000004010b0570a 0x100000001f01c000 0x0100000001f01c00

def z155 : W := mkw 0x49cbc3cae05a0550 0x849cbc3cae05a055 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z156 : W := mkw 0x49cac3cac0000000 0x049cac3cac000000 0x01e3e3e0e0000001 0x101e3e3e0e000000

def z157 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xbe1c0c071f0fc00a 0xebe1c0c071f0fc00

def z158 : W := mkw 0x041404150a0560a9 0x0041404150a0560a 0xd01c0c1f180fe0fe 0xad01c0c1f180fe0f

def z159 : W := mkw 0x8fffba8016ff8000 0x08fffba8016ff800 0xbfffffe01fffc00f 0xfbfffffe01fffc00

def z160 : W := mkw 0x0b401a8000000000 0x00b401a800000000 0x0f80130000000000 0x40f8013000000000

def z161 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1fe00fe01ff00f01 0x91fe00fe01ff00f0

def z162 : W := mkw 0x008a010880120110 0x8008a01088012011 0xa198131800361330 0x4a19813180036133

def z163 : W := mkw 0x4fdedbdec0120110 0x84fdedbdec012011 0xefffffffe0361337 0xfefffffffe036133

def z164 : W := mkw 0x4fdfdbdec05a0000 0x04fdfdbdec05a000 0xefffffffe0fe000f 0xfefffffffe0fe000

def z165 : W := mkw 0x0000040108006088 0x0000004010800608 0x100000001809e0c8 0x0100000001809e0c

def z166 : W := mkw 0x32005ee369007ece 0x432005ee369007ec 0x40001fe7e0003fc4 0x140001fe7e0003fc

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0181018000e30fe 0x6e0181018000e30f

def z168 : W := mkw 0x102064637880eccc 0x4102064637880ecc 0x5064ece7f801ecc4 0x95064ece7f801ecc

def z169 : W := mkw 0x100044634800688c 0x4100044634800688 0x00000ce700000000 0x000000ce70000000

def z170 : W := mkw 0x16347c775b85f8ad 0x416347c775b85f8a 0x1e64ece71f01c000 0x81e64ece71f01c00

def z171 : W := mkw 0x1021606270c88c44 0x41021606270c88c4 0x4063e0e0e0c82ccf 0x34063e0e0e0c82cc

def z172 : W := mkw 0x100060434000c080 0x4100060434000c08 0x0004e0070001c000 0x00004e0070001c00

def z173 : W := mkw 0x0021200030c88440 0x00021200030c8844 0x5067e000f8c9eccf 0xb5067e000f8c9ecc

def z174 : W := mkw 0x449ec15ec0000000 0x0449ec15ec000000 0xc07fecffe0000007 0xbc07fecffe000000

def z175 : W := mkw 0x469edd5fcb0570a9 0x0469edd5fcb0570a 0xfe1ffc1fff0ff0fe 0xefe1ffc1fff0ff0f

def z176 : W := mkw 0xafffbfa8bfffbf5e 0x8afffbfa8bfffbf5 0xfffffff8ffffffff 0xffffffff8fffffff

def z177 : W := mkw 0x000004010b0570a9 0x0000004010b0570a 0x300000001f0ff0f8 0x0300000001f0ff0f

def z178 : W := mkw 0x5f74fef75880e88c 0x45f74fef75880e88 0x1e64ece71801c000 0x81e64ece71801c00

def z179 : W := mkw 0x16353c353bcdfced 0x416353c353bcdfce 0xfe1c1c1f1fcffcfe 0xefe1c1c1f1fcffcf

def z180 : W := mkw 0x1000042128006ccc 0x41000042128006cc 0x0000000000002cc0 0x00000000000002cc

def z181 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x8f98000000000000 0x48f9800000000000

def z182 : W := mkw 0x8dde800006370000 0x08dde80000637000 0xaf98000007360000 0x4af9800000736000

def z183 : W := mkw 0x3b607ee35da0fa8e 0x43b607ee35da0fa8 0x1e64ece71f01c000 0x81e64ece71f01c00

def z184 : W := mkw 0x0dde810880000000 0x00dde81088000000 0xcffff318e0000007 0xfcffff318e000000

def z185 : W := mkw 0x06141c140b053029 0x006141c140b05302 0xbe181c181f06303c 0xebe181c181f06303

def z186 : W := mkw 0x86353c151ffff0a9 0x086353c151ffff0a 0xfe1c1c1f1ffff0fe 0xefe1c1c1f1ffff0f

def z187 : W := mkw 0x8020200016a58000 0x08020200016a5800 0x100000001f01c000 0x0100000001f01c00

def z188 : W := mkw 0x49cbc3cae05a0550 0x849cbc3cae05a055 0xe1fbf3f8e0fe3fff 0x7e1fbf3f8e0fe3ff

def z189 : W := mkw 0x469edbdec0000000 0x0469edbdec000000 0xc01fffffe0000006 0x1c01fffffe000000

def z190 : W := mkw 0x449ec15ec0000000 0x0449ec15ec000000 0xc19ff31fe0000007 0x7c19ff31fe000000

def z191 : W := mkw 0x42005fdfc90070a9 0x042005fdfc90070a 0x40001fffe00030f4 0x140001fffe00030f

def z192 : W := mkw 0x8fde981407371021 0x08fde98140737102 0xaf98101807361030 0x4af9810180736103

def z193 : W := mkw 0x0fde981400000000 0x00fde98140000000 0xcffffc1f00000007 0xecffffc1f0000000

def z194 : W := mkw 0x00010000205a0550 0x800010000205a055 0x2000000000fe3ff8 0x02000000000fe3ff

def z195 : W := mkw 0x2f741eb41da03a0e 0x02f741eb41da03a0 0xfffc1fff1ff03f0f 0xffffc1fff1ff03f0

def z196 : W := mkw 0x10004043600044c0 0x410004043600044c 0x40000007e00000c0 0x040000007e00000c

def z197 : W := mkw 0x10ab656bf8daeddc 0xc10ab656bf8daedd 0xf1fffffff8ffffff 0xff1fffffff8fffff

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000130000003f04 0x10000130000003f0

def z199 : W := mkw 0x008b0108a0480440 0x0008b0108a048044 0xc19b1318e0c82ccf 0x7c19b1318e0c82cc

def z200 : W := mkw 0x0000000020000440 0x0000000002000044 0x40000000e0002cc4 0x140000000e0002cc

def z201 : W := mkw 0x3b607ee35da0fa8e 0x43b607ee35da0fa8 0x3fe4ffe71ff1ff0d 0xf3fe4ffe71ff1ff0

def z202 : W := mkw 0x7ffffffffde8fece 0x47ffffffffde8fec 0xfffffffffff9ffcf 0xffffffffffff9ffc

def z203 : W := mkw 0x0dffa00010c88000 0x00dffa00010c8800 0x9fffe00018c9c00b 0xe9fffe00018c9c00

def z204 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x1067e00018c9eccb 0xa1067e00018c9ecc

def z205 : W := mkw 0x16357c777bcdfced 0x416357c777bcdfce 0x5e67ece7ffc9eccf 0xb5e67ece7ffc9ecc

def z206 : W := mkw 0x008a010880000000 0x0008a01088000000 0x8198131800000000 0x4819813180000000

def z207 : W := mkw 0x008a000000000000 0x0008a00000000000 0x819b000000000003 0x6819b00000000000

def z208 : W := mkw 0x1021646378daeddc 0xc1021646378daedd 0x7067ece7f8ffffff 0xb7067ece7f8fffff

def z209 : W := mkw 0x00000015000040a1 0x000000015000040a 0x4000001f000000f0 0x04000001f000000f

def z210 : W := mkw 0x06341c351b8578ad 0x006341c351b8578a 0xfe7c1cff1fcffcff 0xffe7c1cff1fcffcf

def z211 : W := mkw 0x2b601a8015a01202 0x02b601a8015a0120 0x3fe013001ff01309 0xe3fe013001ff0130

def z212 : W := mkw 0x6fde9b9c85201202 0x06fde9b9c8520120 0xaf98131807301300 0x4af9813180730130

def z213 : W := mkw 0x069e191c80000000 0x0069e191c8000000 0xcf9f1f1fe0000007 0xfcf9f1f1fe000000

def z214 : W := mkw 0x2b601ea11da07a8e 0x02b601ea11da07a8 0x7fe41fe71ff9ffcf 0xf7fe41fe71ff9ffc

def z215 : W := mkw 0x49cac3cac0000000 0x049cac3cac000000 0x41e7efe7e0000007 0xb41e7efe7e000000

def z216 : W := mkw 0x2b605ee25da03a0e 0x02b605ee25da03a0 0x7fe7ffe7fff03f0f 0xf7fe7ffe7fff03f0

def z217 : W := mkw 0x1021242138daeddc 0xc1021242138daedd 0x3000000018fffff8 0x03000000018fffff

def z218 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1e600ce01fc02c0d 0xb1e600ce01fc02c0

def z219 : W := mkw 0xcdffe3cad6ff8000 0x0cdffe3cad6ff800 0xbfffe3e0ffffc00b 0xfbfffe3e0ffffc00

def z220 : W := mkw 0x00010000205a0550 0x800010000205a055 0x2180130000fe3ffd 0x72180130000fe3ff

def z221 : W := mkw 0x02001c15090070a9 0x002001c15090070a 0x7e001c1f1f0030fc 0xe7e001c1f1f0030f

def z222 : W := mkw 0x3beb7febfdfaffde 0xc3beb7febfdfaffd 0xffffffffffffffff 0xffffffffffffffff

def z223 : W := mkw 0x0ddf8000005a0000 0x00ddf8000005a000 0xafffe00000fe000b 0xeafffe00000fe000

def z224 : W := mkw 0x102124213bcdfced 0x4102124213bcdfce 0x300000001fcffcf8 0x0300000001fcffcf

def z225 : W := mkw 0x2b401a8005201202 0x02b401a800520120 0x2f80130007301300 0x42f8013000730130

def z226 : W := mkw 0x100160436048c4c0 0x4100160436048c4c 0x4067ece7e009c0c7 0xb4067ece7e009c0c

def z227 : W := mkw 0x202004201da03a0e 0x0202004201da03a0 0x300000001ff03f08 0x0300000001ff03f0

def z228 : W := mkw 0x8dffa00036ff8440 0x08dffa00036ff844 0xffffe000ffffeccf 0xfffffe000ffffecc

def z229 : W := mkw 0x2b601aa015a01a06 0x02b601aa015a01a0 0x2fe013e007f01f01 0x52fe013e007f01f0

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x100400001809c00a 0xa100400001809c00

def z231 : W := mkw 0x102024211880e88c 0x4102024211880e88 0x100000001801c000 0x0100000001801c00

def z232 : W := mkw 0x1021604370c8c4c0 0x41021604370c8c4c 0x5067e007f8c9c0cb 0xa5067e007f8c9c0c

def z233 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x3fe4e0001ff1c009 0xe3fe4e0001ff1c00

def z234 : W := mkw 0x9ffffc777ffffced 0x49ffffc777ffffce 0xfffffcfffffffcff 0xffffffcfffffffcf

def z235 : W := mkw 0x1000406260000c44 0x41000406260000c4 0x000000e0e0000c00 0x1000000e0e0000c0

def z236 : W := mkw 0x06141c000b053008 0x006141c000b05300 0xbe1c1c001f0ff00e 0xebe1c1c001f0ff00

def z237 : W := mkw 0x22001ea009003a0e 0x022001ea009003a0 0x3e001fe01f003f0c 0xf3e001fe01f003f0

def z238 : W := mkw 0x0b401a8000000000 0x00b401a800000000 0x0fe01fe000000005 0xf0fe01fe00000000

def z239 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xbfffe300ffffcf0b 0xfbfffe300ffffcf0

def z240 : W := mkw 0x002004201880280c 0x0002004201880280 0x1000000018c02c08 0x01000000018c02c0

def z241 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x006000e000000000 0x0006000e00000000

def z242 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0x00030000e0000000 0x000030000e000000

def z243 : W := mkw 0x069e191c83171131 0x8069e191c8317113 0xaf98131807361330 0x4af9813180736133

def z244 : W := mkw 0x2bca1b8885321312 0x82bca1b888532131 0xaf98131807361330 0x4af9813180736133

def z245 : W := mkw 0xcffefbded6a58000 0x0cffefbded6a5800 0xdfffffffff01c007 0xfdfffffffff01c00

def z246 : W := mkw 0x89eba00014fa8000 0x089eba00014fa800 0x3fe3e0001ff00009 0xe3fe3e0001ff0000

def z247 : W := mkw 0x008a010880120110 0x8008a01088012011 0xa198131800f63f3d 0x7a198131800f63f3

def z248 : W := mkw 0x2b401a8005201202 0x02b401a800520120 0x0e00000007000000 0x00e0000000700000

def z249 : W := mkw 0x8dffa10896ff8110 0x88dffa10896ff811 0xbffff3181fffd33b 0xebffff3181fffd33

def z250 : W := mkw 0x202004211fa57aaf 0x0202004211fa57aa 0x300000001ffffff8 0x0300000001ffffff

def z251 : W := mkw 0x22001ea009003a0e 0x022001ea009003a0 0x00000ce000000000 0x000000ce00000000

def z252 : W := mkw 0x4fde9b9c80000000 0x04fde9b9c8000000 0x8ff81ff800000005 0xf8ff81ff80000000

def z253 : W := mkw 0x8d54800006250000 0x08d5480000625000 0x0e00000007000000 0x00e0000000700000

def z254 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f809c0c2 0x85067ece7f809c0c

def z255 : W := mkw 0x10ab656bf8daeddc 0xc10ab656bf8daedd 0xd07fecfff8cfecff 0xbd07fecfff8cfecf

def z256 : W := mkw 0x008a010880000000 0x0008a01088000000 0xe19b1318e00e30ff 0x7e19b1318e00e30f

def z257 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcf981fffe0000004 0x5cf981fffe000000

def z258 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x8ffbf3f8e0000001 0x58ffbf3f8e000000

def z259 : W := mkw 0x1021606270c88c44 0x41021606270c88c4 0x1067e0e0f8c9cc0b 0xb1067e0e0f8c9cc0

def z260 : W := mkw 0x000004010b0570a9 0x0000004010b0570a 0xf01810181f0ff0fe 0x6f01810181f0ff0f

def z261 : W := mkw 0x143564637acdeccc 0x4143564637acdecc 0xfe7fece7ffcfeccf 0xffe7fece7ffcfecc

def z262 : W := mkw 0x1b617ee378c8eccc 0x41b617ee378c8ecc 0x5fe7ffe7f8c9eccf 0xf5fe7ffe7f8c9ecc

def z263 : W := mkw 0x069e1d1d8b1771b9 0x8069e1d1d8b1771b 0xff9c1f1f1f3ff3fe 0xeff9c1f1f1f3ff3f

def z264 : W := mkw 0x4bcadbcac0000000 0x04bcadbcac000000 0x0fe3ffe0e0000005 0xf0fe3ffe0e000000

def z265 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x3fe003e01ff00f09 0xf3fe003e01ff00f0

def z266 : W := mkw 0x008b0000005a0000 0x0008b0000005a000 0xa19b130000fe3f0f 0x7a19b130000fe3f0

def z267 : W := mkw 0x8435200016ff8000 0x08435200016ff800 0xbe1c00001fffc00a 0xebe1c00001fffc00

def z268 : W := mkw 0x008b0000205a0440 0x0008b0000205a044 0xe19b0000e0fe2ccf 0x7e19b0000e0fe2cc

def z269 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x50030000f8c9eccf 0x350030000f8c9ecc

def z270 : W := mkw 0x0dde800002050000 0x00dde80000205000 0xbfffe0001f0fc00b 0xebfffe0001f0fc00

def z271 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc01b1318e00e3ff6 0x1c01b1318e00e3ff

def z272 : W := mkw 0x80ab2108b6ff8550 0x880ab2108b6ff855 0xf19b1318ffffffff 0x7f19b1318fffffff

def z273 : W := mkw 0x00010401284864c8 0x000010401284864c 0x50070c07f8c9eccf 0xb50070c07f8c9ecc

def z274 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180030000f00f01 0x10180030000f00f0

def z275 : W := mkw 0x0614181400000000 0x0061418140000000 0x0e040c0700000000 0x80e040c070000000

def z276 : W := mkw 0x108b614be05ac5d0 0xc108b614be05ac5d 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z277 : W := mkw 0x8fffb81416ff8000 0x08fffb81416ff800 0xfffffc1f1fffc00f 0xefffffc1f1fffc00

def z278 : W := mkw 0x22001a8001001202 0x022001a800100120 0x0000130000001300 0x0000013000000130

def z279 : W := mkw 0xa02124201fffba0e 0x0a02124201fffba0 0x300000001fffff08 0x0300000001fffff0

def z280 : W := mkw 0x0b601a8014a00000 0x00b601a8014a0000 0x3fe01fe01ff0000d 0xf3fe01fe01ff0000

def z281 : W := mkw 0x0000040108006088 0x0000004010800608 0x10040c071801c000 0x810040c071801c00

def z282 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xde1c1c1f1f01c006 0xede1c1c1f1f01c00

def z283 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xce7fecffe0000002 0x8ce7fecffe000000

def z284 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1e600ce01f000000 0x81e600ce01f00000

def z285 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xaffbe00007f60001 0x4affbe00007f6000

def z286 : W := mkw 0x02201c201980380c 0x002201c201980380 0x3e601ce01fc03c0d 0xf3e601ce01fc03c0

def z287 : W := mkw 0x16145c776b057ced 0x416145c776b057ce 0xfe1c1cffff0ffcfe 0xffe1c1cffff0ffcf

def z288 : W := mkw 0x1020606250808804 0x4102060625080880 0x0060e0e000000000 0x00060e0e00000000

def z289 : W := mkw 0x4ddec15ec0000000 0x04ddec15ec000000 0xcfffe01fe0000003 0xecfffe01fe000000

def z290 : W := mkw 0x6fdedbdec5201202 0x06fdedbdec520120 0xefffffffe7301307 0xfefffffffe730130

def z291 : W := mkw 0x4f549a9400000000 0x04f549a940000000 0x0e00000000000000 0x00e0000000000000

def z292 : W := mkw 0x069f1c150b5f70a9 0x0069f1c150b5f70a 0xff9f1c1f1ffff0ff 0xeff9f1c1f1ffff0f

def z293 : W := mkw 0x849fa108a25f8550 0x8849fa108a25f855 0xc01fe018e00fc0f2 0x0c01fe018e00fc0f

def z294 : W := mkw 0x8021200036ff8550 0x88021200036ff855 0x300000001ffffff8 0x0300000001ffffff

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0xa018101800061030 0x4a01810180006103

def z296 : W := mkw 0x02001c15090070a9 0x002001c15090070a 0x50041c1f1809f0fe 0xa50041c1f1809f0f

def z297 : W := mkw 0x6f74def65da03a0e 0x06f74def65da03a0 0x1e64ece71f000000 0x81e64ece71f00000

def z298 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0x01830300e0f00f01 0x101830300e0f00f0

def z299 : W := mkw 0x0614181403051021 0x0061418140305102 0x0e00000007000000 0x00e0000000700000

def z300 : W := mkw 0xafffbeb51ffffaaf 0x0afffbeb51ffffaa 0xffffffff1fffffff 0xfffffffff1ffffff

def z301 : W := mkw 0xab613ea01fffba0e 0x0ab613ea01fffba0 0x3fe01fe01fffff0d 0xf3fe01fe01fffff0

def z302 : W := mkw 0x00010000205a0550 0x800010000205a055 0x00000000000e00f0 0x000000000000e00f

def z303 : W := mkw 0x8d75a00016ff8000 0x08d75a00016ff800 0x3e64e0001fffc008 0x83e64e0001fffc00

def z304 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x5064ece71809e0ce 0xa5064ece71809e0c

def z305 : W := mkw 0x8ddf8000067f0000 0x08ddf8000067f000 0xaf9b000007fe000b 0x6af9b000007fe000

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000000f03f08 0x02000000000f03f0

def z307 : W := mkw 0x6f74def65da03a0e 0x06f74def65da03a0 0x3fe4ffe71ff03f0d 0xf3fe4ffe71ff03f0

def z308 : W := mkw 0x0414000002050000 0x0041400000205000 0xfe1c10181f0ff0fe 0xefe1c10181f0ff0f

def z309 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0x4e67ece7e0000007 0xb4e67ece7e000000

def z310 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0x3e040c071f0ff0f8 0x83e040c071f0ff0f

def z311 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe00ce01ff00009 0xe3fe00ce01ff0000

def z312 : W := mkw 0x5ffffbfef0c88c44 0x45ffffbfef0c88c4 0xcfffffffe0c00c07 0xfcfffffffe0c00c0

def z313 : W := mkw 0x29eb03a8b4fa0f56 0x829eb03a8b4fa0f5 0x01e303e0e0f00f01 0x101e303e0e0f00f0

def z314 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0x3e041c071f01f00c 0xe3e041c071f01f00

def z315 : W := mkw 0x8dffa00036ff8550 0x88dffa00036ff855 0xbfffe0001ffffffb 0xebfffe0001ffffff

def z316 : W := mkw 0x8fffb81417ff9021 0x08fffb81417ff902 0xbffff0181fffd03b 0xebffff0181fffd03

def z317 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x4063ece7e0c02cc5 0x14063ece7e0c02cc

def z318 : W := mkw 0x2bcb1b88a57a1752 0x82bcb1b88a57a175 0xef9b1318e7fe3fff 0x7ef9b1318e7fe3ff

def z319 : W := mkw 0x42005bdee0000550 0x842005bdee000055 0x40001fffe0003ff4 0x140001fffe0003ff

def z320 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xfffff0181ffff0ff 0xefffff0181ffff0f

def z321 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x71e7ffe7f8f9ffcf 0xf71e7ffe7f8f9ffc

def z322 : W := mkw 0x42001b9c80000000 0x042001b9c8000000 0x0000131800000000 0x0000013180000000

def z323 : W := mkw 0x041404010a056088 0x0041404010a05608 0xfe1c0c071f0fe0ce 0xefe1c0c071f0fe0c

def z324 : W := mkw 0x008a010880120110 0x8008a01088012011 0x8018001800060030 0x0801800180006003

def z325 : W := mkw 0x8fffbc001fffb008 0x08fffbc001fffb00 0xbffffc001ffff00f 0xebffffc001ffff00

def z326 : W := mkw 0x0614181400000000 0x0061418140000000 0xce1c1c1f00000006 0xece1c1c1f0000000

def z327 : W := mkw 0x302124213de8fece 0x4302124213de8fec 0x300000001ff9ffc8 0x0300000001ff9ffc

def z328 : W := mkw 0x000004010b0570a9 0x0000004010b0570a 0x70040c071f0ff0fe 0xa70040c071f0ff0f

def z329 : W := mkw 0x4fdedbdee0000550 0x84fdedbdee000055 0xcfffffffe0003ff7 0xfcfffffffe0003ff

def z330 : W := mkw 0x143564777acdeced 0x4143564777acdece 0xd07fecfff8cfecff 0xbd07fecfff8cfecf

def z331 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe01b1018e00e30fe 0x6e01b1018e00e30f

def z332 : W := mkw 0x0020000010800000 0x0002000001080000 0x1060000018c00009 0xa1060000018c0000

def z333 : W := mkw 0x10ab2529b8daeddc 0xc10ab2529b8daedd 0xf19b1318f8ffffff 0x7f19b1318f8fffff

def z334 : W := mkw 0x00010108a0480550 0x800010108a048055 0x40031318e0c83fff 0x340031318e0c83ff

def z335 : W := mkw 0x6fdedffec9003a0e 0x06fdedffec9003a0 0xcfffffffe0003f07 0xfcfffffffe0003f0

def z336 : W := mkw 0x049f0000025f0000 0x0049f0000025f000 0xbf9f00001fffc00b 0xebf9f00001fffc00

def z337 : W := mkw 0x100120012048c4c0 0x4100120012048c4c 0x000000000009c0c0 0x0000000000009c0c

def z338 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1067ece7f8c1cc01 0x91067ece7f8c1cc0

def z339 : W := mkw 0x0000010880000110 0x8000001088000011 0x0000131800001330 0x0000013180000133

def z340 : W := mkw 0x0000000002050000 0x0000000000205000 0x300000001f0fc008 0x0300000001f0fc00

def z341 : W := mkw 0x8960a00014a08000 0x08960a00014a0800 0x0060e00000000000 0x00060e0000000000

def z342 : W := mkw 0x4fdedfdfcb0570a9 0x04fdedfdfcb0570a 0xdfffffffff01c007 0xfdfffffffff01c00

def z343 : W := mkw 0x00000108a0000550 0x800000108a000055 0x40000018e00000f0 0x040000018e00000f

def z344 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc19b0318e0fe0ff3 0x1c19b0318e0fe0ff

def z345 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1063e0e0f8c9ecc9 0x11063e0e0f8c9ecc

def z346 : W := mkw 0x1021202030c88c44 0x41021202030c88c4 0x0000000000c00c00 0x00000000000c00c0

def z347 : W := mkw 0xabebbea01dfaba0e 0x0abebbea01dfaba0 0x3fe3ffe01ff03f0d 0xf3fe3ffe01ff03f0

def z348 : W := mkw 0x06145c574b0570a9 0x006145c574b0570a 0xfe7ffcffff0ff0ff 0xffe7ffcffff0ff0f

def z349 : W := mkw 0x52005fffe8006ccc 0x452005fffe8006cc 0x40001fffe0002cc4 0x140001fffe0002cc

def z350 : W := mkw 0x8414a00002058000 0x08414a0000205800 0x0004e0000001c000 0x00004e0000001c00

def z351 : W := mkw 0x008b0000005a0000 0x0008b0000005a000 0x801b0000000e0002 0x0801b0000000e000

def z352 : W := mkw 0xcffffad656ff8000 0x0cffffad656ff800 0xbfffece71fffc00b 0xebfffece71fffc00

def z353 : W := mkw 0x42005ad640000000 0x042005ad64000000 0x00000ce700000000 0x000000ce70000000

def z354 : W := mkw 0x2000042009003a0e 0x02000042009003a0 0x0000000000003f00 0x00000000000003f0

def z355 : W := mkw 0x94bfe4637adfeccc 0x494bfe4637adfecc 0xd07fece7f8cfeccf 0xbd07fece7f8cfecc

def z356 : W := mkw 0x00010000205a0550 0x800010000205a055 0x0000000000f00f00 0x00000000000f00f0

def z357 : W := mkw 0x8dfea00016b78000 0x08dfea00016b7800 0xbffce0001f37c000 0xcbffce0001f37c00

def z358 : W := mkw 0x069f1d1dab5f75f9 0x8069f1d1dab5f75f 0xfe1f1c1fff0ff0fe 0xefe1f1c1fff0ff0f

def z359 : W := mkw 0x12217c6379c8fccc 0x412217c6379c8fcc 0x7e67fce7ffc9fccf 0xf7e67fce7ffc9fcc

def z360 : W := mkw 0x0b601c001da03008 0x00b601c001da0300 0x3fe01c001ff0300d 0xe3fe01c001ff0300

def z361 : W := mkw 0x2b613ea01de8ba0e 0x02b613ea01de8ba0 0x3fe7ffe01ff9ff0f 0xf3fe7ffe01ff9ff0

def z362 : W := mkw 0x041404150b0570a9 0x0041404150b0570a 0xf01c001f1f0ff0fa 0x0f01c001f1f0ff0f

def z363 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0xbe7ce0001f0fc00a 0xebe7ce0001f0fc00

def z364 : W := mkw 0x0001000020480440 0x0000100002048044 0x40030000e00800c2 0x040030000e00800c

def z365 : W := mkw 0x2b601ea11fa57aaf 0x02b601ea11fa57aa 0x3fe01fe01ffffffd 0xf3fe01fe01ffffff

def z366 : W := mkw 0x0020002010800804 0x0002000201080080 0x006000e000c00c01 0x1006000e000c00c0

def z367 : W := mkw 0x9dffe06276ff8c44 0x49dffe06276ff8c4 0xbfffe0e0ffffcc0b 0xfbfffe0e0ffffcc0

def z368 : W := mkw 0x89eba108b4fa8550 0x889eba108b4fa855 0x01e3e300e0f00f01 0x101e3e300e0f00f0

def z369 : W := mkw 0x9dffe04376ffc4c0 0x49dffe04376ffc4c 0xffffe007ffffc0cb 0xeffffe007ffffc0c

def z370 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe01b0018e0fe3ffa 0x0e01b0018e0fe3ff

def z371 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x1fe7e0001ff1c001 0x81fe7e0001ff1c00

def z372 : W := mkw 0x849e800002170000 0x0849e80000217000 0x8018000000060000 0x0801800000006000

def z373 : W := mkw 0x0020200010808000 0x0002020001080800 0x1064e0001801c000 0x81064e0001801c00

def z374 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe0f03f0f 0xfefffffffe0f03f0

def z375 : W := mkw 0x1dffe46378c8eccc 0x41dffe46378c8ecc 0xdfffece7f8c9eccf 0xfdfffece7f8c9ecc

def z376 : W := mkw 0x428b5bdee05a0550 0x8428b5bdee05a055 0xe19b1fffe0fe3fff 0x7e19b1fffe0fe3ff

def z377 : W := mkw 0x0021604250c88000 0x00021604250c8800 0x5067ece7f8c9c00f 0xb5067ece7f8c9c00

def z378 : W := mkw 0x02001c15090070a9 0x002001c15090070a 0xe0181c1f000e30fe 0x6e0181c1f000e30f

def z379 : W := mkw 0x02001c15090070a9 0x002001c15090070a 0x00000c0700000000 0x000000c070000000

def z380 : W := mkw 0x1001446368486ccc 0x41001446368486cc 0x40030ce7e0c82ccf 0x340030ce7e0c82cc

def z381 : W := mkw 0x396162e274e88e46 0x4396162e274e88e4 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z382 : W := mkw 0x008a0108a0120550 0x8008a0108a012055 0xe1981318e0363ff4 0x5e1981318e0363ff

def z383 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xc01c1c1f000ff0f6 0x0c01c1c1f000ff0f

def z384 : W := mkw 0x0b401e8009003008 0x00b401e800900300 0x3fe01fe01f00300d 0xf3fe01fe01f00300

def z385 : W := mkw 0x00010000205a0550 0x800010000205a055 0x60030000e0fe3fff 0x360030000e0fe3ff

def z386 : W := mkw 0x89eba00014fa8000 0x089eba00014fa800 0xa1fbe00000fe000b 0x6a1fbe00000fe000

def z387 : W := mkw 0x3b605ee37da07ece 0x43b605ee37da07ec 0x7fe01fe7fff03fcd 0xf7fe01fe7fff03fc

def z388 : W := mkw 0x69eac3ead4a00a06 0x069eac3ead4a00a0 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z389 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0x0fe4ffe700000005 0xf0fe4ffe70000000

def z390 : W := mkw 0x06151c152b5f75f9 0x806151c152b5f75f 0xfe1c1c1f1ffffffe 0xefe1c1c1f1ffffff

def z391 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe19b0018e0fe00fb 0x6e19b0018e0fe00f

def z392 : W := mkw 0x849fa000025f8000 0x0849fa000025f800 0xa19fe00000ffc00b 0x6a19fe00000ffc00

def z393 : W := mkw 0x0fde9c150b0570a9 0x00fde9c150b0570a 0xfffffc1f1f0ff0ff 0xefffffc1f1f0ff0f

def z394 : W := mkw 0x00000001020540a1 0x000000001020540a 0x00000000000fc0f0 0x000000000000fc0f

def z395 : W := mkw 0xadffa4201fffba0e 0x0adffa4201fffba0 0xbfffe0001fffff0b 0xebfffe0001fffff0

def z396 : W := mkw 0x902164637effeccc 0x4902164637effecc 0x7067ece7ffffeccf 0xb7067ece7ffffecc

def z397 : W := mkw 0x0001000000480000 0x0000100000048000 0x0003000000c8000b 0x20003000000c8000

def z398 : W := mkw 0x22001ea009003a0e 0x022001ea009003a0 0x21801fe000f03f0d 0x721801fe000f03f0

def z399 : W := mkw 0x22001eb509007aaf 0x022001eb509007aa 0x40001fff00003ff4 0x140001fff00003ff

def z400 : W := mkw 0x4fdfdfdfeb5f75f9 0x84fdfdfdfeb5f75f 0xffffffffffffffff 0xffffffffffffffff

def z401 : W := mkw 0x0435200012cd8000 0x00435200012cd800 0xbe7fe0001fcfc00b 0xebe7fe0001fcfc00

def z402 : W := mkw 0x0001000020480440 0x0000100002048044 0x0000000000c82cc8 0x00000000000c82cc

def z403 : W := mkw 0x0000040008002008 0x0000004000800200 0x10000c001800200c 0xa10000c001800200

def z404 : W := mkw 0x228b1fa8a95a3f5e 0x8228b1fa8a95a3f5 0xe19b1ff8e0fe3fff 0x7e19b1ff8e0fe3ff

def z405 : W := mkw 0x069e1d1d8b0570a9 0x0069e1d1d8b0570a 0xff9f1f1fff0ff0ff 0xfff9f1f1fff0ff0f

def z406 : W := mkw 0x1021606370c8ccc4 0x41021606370c8ccc 0x4067e0e7e0c9ccc3 0x14067e0e7e0c9ccc

def z407 : W := mkw 0x8fffbc151ffff0a9 0x08fffbc151ffff0a 0xbfffec071fffc00b 0xebfffec071fffc00

def z408 : W := mkw 0x396166e37ce8eece 0x4396166e37ce8eec 0x51e7efe7f8f9efcf 0xb51e7efe7f8f9efc

def z409 : W := mkw 0x096004201ca0280c 0x0096004201ca0280 0x3fe00ce01ff02c0d 0xf3fe00ce01ff02c0

def z410 : W := mkw 0x0021242018c8a80c 0x00021242018c8a80 0x1067ece018c9ec0f 0xb1067ece018c9ec0

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180130000000005 0x7018013000000000

def z412 : W := mkw 0x296006a01da03a0e 0x0296006a01da03a0 0x31e003e01ff03f09 0x131e003e01ff03f0

def z413 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x9e7fe0001f0fc002 0x89e7fe0001f0fc00

def z414 : W := mkw 0x4fdf9b9ca05a0550 0x84fdf9b9ca05a055 0xef9b1318e0fe3fff 0x7ef9b1318e0fe3ff

def z415 : W := mkw 0x8021200016ff8000 0x08021200016ff800 0x3067e0001fffc00b 0xa3067e0001fffc00

def z416 : W := mkw 0x5fdedfffe8006ccc 0x45fdedfffe8006cc 0xcfffffffe0002cc7 0xfcfffffffe0002cc

def z417 : W := mkw 0xaf74bea01fa5ba0e 0x0af74bea01fa5ba0 0x3fe4ffe01ff1ff0d 0xf3fe4ffe01ff1ff0

def z418 : W := mkw 0x12217c7779c8fced 0x412217c7779c8fce 0x5067fcfff8c9fcff 0xb5067fcfff8c9fcf

def z419 : W := mkw 0x22201ea01da03a0e 0x022201ea01da03a0 0x30001fe01ff03f0c 0x130001fe01ff03f0

def z420 : W := mkw 0x8dde810886370110 0x88dde81088637011 0xaf98131807361330 0x4af9813180736133

def z421 : W := mkw 0x0b601ea01880280c 0x00b601ea01880280 0x1fe01fe018c02c0d 0xf1fe01fe018c02c0

def z422 : W := mkw 0x0614181402050000 0x0061418140205000 0xfe1c1c1f1f0fc00e 0xefe1c1c1f1f0fc00

def z423 : W := mkw 0xcffffbdef6ff8550 0x8cffffbdef6ff855 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0x0000404240000000 0x0000040424000000 0x0063e0e0e0000001 0x10063e0e0e000000

def z425 : W := mkw 0x62005ffec9003a0e 0x062005ffec9003a0 0x40001fffe0003f04 0x140001fffe0003f0

def z426 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x1064ece718c1ec0d 0xb1064ece718c1ec0

def z427 : W := mkw 0x1000446368006ccc 0x41000446368006cc 0x50040ce7f809ecce 0xb50040ce7f809ecc

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x00600ce000000005 0xb00600ce00000000

def z429 : W := mkw 0x22201ea019803a0e 0x022201ea019803a0 0x10601fe018c03f0d 0xb10601fe018c03f0

def z430 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0180018000e00f2 0x0c0180018000e00f

def z431 : W := mkw 0x049f011da25f45f1 0x8049f011da25f45f 0xe19f131fe0ffffff 0x7e19f131fe0fffff

def z432 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5007e007f8c9ecca 0x05007e007f8c9ecc

def z433 : W := mkw 0x02001d1da90075f9 0x802001d1da90075f 0x40001f1fe0003ff4 0x140001f1fe0003ff

def z434 : W := mkw 0x000004200800280c 0x0000004200800280 0x00000ce000002c04 0x100000ce000002c0

def z435 : W := mkw 0x00000108a0000550 0x800000108a000055 0x61801318e0f03ffd 0x761801318e0f03ff

def z436 : W := mkw 0x3b617ee37de8fece 0x43b617ee37de8fec 0x5e67ece7ffc9eccf 0xb5e67ece7ffc9ecc

def z437 : W := mkw 0x02001c0009003008 0x002001c000900300 0x00001c0000003004 0x000001c000000300

def z438 : W := mkw 0x02001c0109007088 0x002001c010900708 0x7e041c071f09f0ce 0xe7e041c071f09f0c

def z439 : W := mkw 0x0001200000488000 0x0000120000048800 0x0007e0000009c002 0x00007e0000009c00

def z440 : W := mkw 0x0000000000000000 0x0000000000000000 0x200010000000300c 0x6200010000000300

def z441 : W := mkw 0x0960000014a00000 0x00960000014a0000 0x1e6000001f000000 0x81e6000001f00000

def z442 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xff9c1f1f1fffffff 0xfff9c1f1f1ffffff

def z443 : W := mkw 0x0001404260480440 0x0000140426048044 0x4067ece7e0c82ccf 0xb4067ece7e0c82cc

def z444 : W := mkw 0x06141c15090070a9 0x006141c15090070a 0xce1c1c1f000030f6 0xece1c1c1f000030f

def z445 : W := mkw 0x008a000000120000 0x0008a00000012000 0xa198000000360000 0x4a19800000036000

def z446 : W := mkw 0x16157c576b4df4e9 0x416157c576b4df4e 0xfe1ffc1fff0ff0fe 0xefe1ffc1fff0ff0f

def z447 : W := mkw 0x1000446368006ccc 0x41000446368006cc 0x4067ece7e0002cc7 0xb4067ece7e0002cc

def z448 : W := mkw 0x4fdfdbdee05a0550 0x84fdfdbdee05a055 0xcfffffffe0f00f07 0xfcfffffffe0f00f0

def z449 : W := mkw 0x0b401a8000000000 0x00b401a800000000 0x0e600ce000000000 0x80e600ce00000000

def z450 : W := mkw 0x400043cac0000000 0x0400043cac000000 0x000003e0e0000000 0x1000003e0e000000

def z451 : W := mkw 0x196164637ce8eccc 0x4196164637ce8ecc 0x7fe7ece7fff9eccf 0xf7fe7ece7fff9ecc

def z452 : W := mkw 0x1020446378806ccc 0x41020446378806cc 0x50600ce7f8c02ccd 0xb50600ce7f8c02cc

def z453 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0x41831318e0f03ff5 0x141831318e0f03ff

def z454 : W := mkw 0x0001000020480440 0x0000100002048044 0x61831300e0f83fcf 0x761831300e0f83fc

def z455 : W := mkw 0x0614181403051021 0x0061418140305102 0xbe1c10181f0fd03a 0xebe1c10181f0fd03

def z456 : W := mkw 0x0f541a9400000000 0x00f541a940000000 0xcffc1fff00000007 0xfcffc1fff0000000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180130000301300 0x4218013000030130

def z458 : W := mkw 0x0000000100004080 0x0000000010000408 0x400400070009c0c2 0x0400400070009c0c

def z459 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xa198131800fe3ff8 0x4a198131800fe3ff

def z460 : W := mkw 0x9dffe4635effe88c 0x49dffe4635effe88 0xbfffece71fffc00b 0xebfffece71fffc00

def z461 : W := mkw 0x2b401a8005201202 0x02b401a800520120 0x2fe01fe007301305 0xf2fe01fe00730130

def z462 : W := mkw 0x9dffa4213effeccc 0x49dffa4213effecc 0xbfffe0001fffeccb 0xebfffe0001fffecc

def z463 : W := mkw 0x449fc15ee05a0550 0x8449fc15ee05a055 0xe19ff31fe0fe3fff 0x7e19ff31fe0fe3ff

def z464 : W := mkw 0x04140015020540a1 0x004140015020540a 0xe01c101f000ff0fe 0x6e01c101f000ff0f

def z465 : W := mkw 0x008b0509a85a65d8 0x8008b0509a85a65d 0xf19f1f1ff8ffffff 0xff19f1f1ff8fffff

def z466 : W := mkw 0x2000000005201202 0x0200000000520120 0x2000000007301300 0x0200000000730130

def z467 : W := mkw 0xafde9a8007371202 0x0afde9a800737120 0xaf98130007361300 0x4af9813000736130

def z468 : W := mkw 0x89eba00014fa8000 0x089eba00014fa800 0x11e7e00018f9c00b 0xa11e7e00018f9c00

def z469 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xffffe018ffffc0fb 0xeffffe018ffffc0f

def z470 : W := mkw 0x4fde9b9c80000000 0x04fde9b9c8000000 0xcf9c1f1f00000006 0xecf9c1f1f0000000

def z471 : W := mkw 0x449e811c80000000 0x0449e811c8000000 0x8018001800000000 0x0801800180000000

def z472 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc19b1318e00e00f7 0x7c19b1318e00e00f

def z473 : W := mkw 0x0000000020000550 0x8000000002000055 0x0000000000003ff0 0x00000000000003ff

def z474 : W := mkw 0x8dffe04256ff8000 0x08dffe04256ff800 0xffffece7ffffc00f 0xfffffece7ffffc00

def z475 : W := mkw 0x4fde9b9c80000000 0x04fde9b9c8000000 0x8ffff31800000003 0xe8ffff3180000000

def z476 : W := mkw 0x008a010880000000 0x0008a01088000000 0xe19b1318e0f03f0f 0x7e19b1318e0f03f0

def z477 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcf9ff31fe0000002 0x4cf9ff31fe000000

def z478 : W := mkw 0x5fdffbdfe048c4c0 0x45fdffbdfe048c4c 0xcfffffffe009c0c7 0xfcfffffffe009c0c

def z479 : W := mkw 0x06141c1409003008 0x006141c140900300 0xfe1c1c1f1f00300e 0xefe1c1c1f1f00300

def z480 : W := mkw 0x0fde9a8000000000 0x00fde9a800000000 0x8fffffe000000007 0xf8fffffe00000000

def z481 : W := mkw 0x9d75e4637eedeccc 0x49d75e4637eedecc 0x5e67ece7ffc9eccf 0xb5e67ece7ffc9ecc

def z482 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0x41830300e0f82fcf 0x341830300e0f82fc

def z483 : W := mkw 0x26341c351fa57aaf 0x026341c351fa57aa 0xfe1c1c1f1ffffffe 0xefe1c1c1f1ffffff

def z484 : W := mkw 0x8961200016ff8000 0x08961200016ff800 0x3fe000001fffc009 0xe3fe000001fffc00

def z485 : W := mkw 0xafffbea01fffba0e 0x0afffbea01fffba0 0xbfffece01fffc00b 0xebfffece01fffc00

def z486 : W := mkw 0x408ac14ac0000000 0x0408ac14ac000000 0x0003e000e0000000 0x00003e000e000000

def z487 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xee181c1f070630f4 0x4ee181c1f070630f

def z488 : W := mkw 0x2b401ea00d203a0e 0x02b401ea00d203a0 0x2f801fe007303f04 0x52f801fe007303f0

def z489 : W := mkw 0x4fdfdbdee0480440 0x04fdfdbdee048044 0xcfffffffe0c82ccf 0xfcfffffffe0c82cc

def z490 : W := mkw 0x8dde800006370000 0x08dde80000637000 0xbf9c00001f3fc00a 0xebf9c00001f3fc00

def z491 : W := mkw 0x0d74000016a50000 0x00d74000016a5000 0xbffc00001fffc00b 0xebffc00001fffc00

def z492 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x50040c0718c9ecce 0xa50040c0718c9ecc

def z493 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffff3001fffff0f 0xfbffff3001fffff0

def z494 : W := mkw 0xbffffee37ffffece 0x4bffffee37ffffec 0xffffffe7ffffffcf 0xfffffffe7ffffffc

def z495 : W := mkw 0x202004201da03a0e 0x0202004201da03a0 0x318013001ff03f0d 0x7318013001ff03f0

def z496 : W := mkw 0x1021646358c8e88c 0x41021646358c8e88 0x1067ece718c9c00b 0xa1067ece718c9c00

def z497 : W := mkw 0x4ddec3dec0000000 0x04ddec3dec000000 0xc1ffe3ffe0000003 0x1c1ffe3ffe000000

def z498 : W := mkw 0x2b401ea009003a0e 0x02b401ea009003a0 0x0fe01fe000003f05 0xf0fe01fe000003f0

def z499 : W := mkw 0x0021042038c82c4c 0x00021042038c82c4 0x50630ce0f8c82ccf 0xb50630ce0f8c82cc

def z500 : W := mkw 0x06141d1dab0575f9 0x806141d1dab0575f 0xfe1c1f1fff0ffffe 0xffe1c1f1fff0ffff

def z501 : W := mkw 0x6ffedfffdfa57aaf 0x06ffedfffdfa57aa 0xffffffffffffffff 0xffffffffffffffff

def z502 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x01e01fe000f03f05 0x101e01fe000f03f0

def z503 : W := mkw 0xcdffe15ed6ff8000 0x0cdffe15ed6ff800 0xffffe01fffffc00b 0xeffffe01fffffc00

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180000000f00009 0x62180000000f0000

def z505 : W := mkw 0x20ab0528bdfa3f5e 0x820ab0528bdfa3f5 0xf19b1318fffe3fff 0x7f19b1318fffe3ff

def z506 : W := mkw 0x002004201880280c 0x0002004201880280 0x10600ce018000000 0x810600ce01800000

def z507 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x81ffe00000ffc003 0x081ffe00000ffc00

def z508 : W := mkw 0x02001c0009003008 0x002001c000900300 0x1e000c001f000000 0x81e000c001f00000

def z509 : W := mkw 0x2020002014a00a06 0x02020002014a00a0 0x0000000000f00f00 0x00000000000f00f0

def z510 : W := mkw 0x22001fa8a9003f5e 0x822001fa8a9003f5 0x40001ff8e0003ff4 0x140001ff8e0003ff

def z511 : W := mkw 0x0961200014e88000 0x00961200014e8800 0x3fe7e0001ff9c00b 0xe3fe7e0001ff9c00

def z512 : W := mkw 0x3b613ea13de8fece 0x43b613ea13de8fec 0x3fe01fe01ff9ffcd 0xf3fe01fe01ff9ffc

def z513 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc19b1318e0f00f07 0x7c19b1318e0f00f0

def z514 : W := mkw 0x2b601eb51da07aaf 0x02b601eb51da07aa 0x7fe01fff1ff03ffd 0xf7fe01fff1ff03ff

def z515 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3e601ce01f00300c 0xe3e601ce01f00300

def z516 : W := mkw 0x00ab200010da8000 0x000ab200010da800 0xb1ffe00018ffc00b 0xeb1ffe00018ffc00

def z517 : W := mkw 0x8d75a00016ed8000 0x08d75a00016ed800 0x1e67e0001fc9c00b 0xa1e67e0001fc9c00

def z518 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1e601fe01f003f04 0x91e601fe01f003f0

def z519 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe19b1318e03e13f2 0x4e19b1318e03e13f

def z520 : W := mkw 0x6beadfeadda03a0e 0x06beadfeadda03a0 0x3fe3ffe0fff03f0d 0xf3fe3ffe0fff03f0

def z521 : W := mkw 0xcf74fad656a58000 0x0cf74fad656a5800 0x1e64ece71f01c000 0x81e64ece71f01c00

def z522 : W := mkw 0x2beb1fa8bdfa3f5e 0x82beb1fa8bdfa3f5 0x3fe31fe0fff03f0d 0xf3fe31fe0fff03f0

def z523 : W := mkw 0x202104203dfa3f5e 0x8202104203dfa3f5 0x300000001ffe3ff8 0x0300000001ffe3ff

def z524 : W := mkw 0x2f741eb41fa53a2f 0x02f741eb41fa53a2 0xbff81ff81ff63f3d 0xfbff81ff81ff63f3

def z525 : W := mkw 0x4f54ded74b0570a9 0x04f54ded74b0570a 0x1e64ece71f01c000 0x81e64ece71f01c00

def z526 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0xce7cfcff00000006 0xece7cfcff0000000

def z527 : W := mkw 0x06151c152b4d74e9 0x006151c152b4d74e 0xfe1f1c1fffcffcff 0xffe1f1c1fffcffcf

def z528 : W := mkw 0x0614181400000000 0x0061418140000000 0x8e18101800000000 0x48e1810180000000

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e0000001f000008 0xe3e0000001f00000

def z530 : W := mkw 0x802124011ffff0a9 0x0802124011ffff0a 0x300000001ffff0f8 0x0300000001ffff0f

def z531 : W := mkw 0xdffffffffeffeccc 0x4dffffffffeffecc 0xffffffffffffeccf 0xfffffffffffffecc

def z532 : W := mkw 0x02001a8000000000 0x002001a800000000 0x00001fe000000004 0x100001fe00000000

def z533 : W := mkw 0x10ab656bf8c8eccc 0x410ab656bf8c8ecc 0xd1fffffff8c9eccf 0xfd1fffffff8c9ecc

def z534 : W := mkw 0x10ab616af0da8d54 0xc10ab616af0da8d5 0xe1fbf3f8e0fe3fff 0x7e1fbf3f8e0fe3ff

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0xe198131800fe3fff 0x7e198131800fe3ff

def z536 : W := mkw 0x00ab0528b8da2d5c 0x800ab0528b8da2d5 0xf1fb1ff8f8fe3fff 0xff1fb1ff8f8fe3ff

def z537 : W := mkw 0x0000404240000000 0x0000040424000000 0x0064ece700000000 0x80064ece70000000

def z538 : W := mkw 0x0021200010c88000 0x00021200010c8800 0x0063e00000c00001 0x00063e00000c0000

def z539 : W := mkw 0x0000040108006088 0x0000004010800608 0xf01c1c1f180ff0fe 0xef01c1c1f180ff0f

def z540 : W := mkw 0x0414001402050021 0x0041400140205002 0x8018001800060030 0x0801800180006003

def z541 : W := mkw 0x04140015020540a1 0x004140015020540a 0xfe1c001f1f0fc0fa 0xefe1c001f1f0fc0f

def z542 : W := mkw 0x16bf7d7ffbdffdfd 0xc16bf7d7ffbdffdf 0xffffffffffffffff 0xffffffffffffffff

def z543 : W := mkw 0x0000040009003008 0x0000004000900300 0x300000001f003008 0x0300000001f00300

def z544 : W := mkw 0xcfdedbdec6370000 0x0cfdedbdec637000 0xefffffffe7360007 0xfefffffffe736000

def z545 : W := mkw 0x09eb0108b4fa0550 0x809eb0108b4fa055 0xfffb1318fffe3fff 0xffffb1318fffe3ff

def z546 : W := mkw 0x16357c7778c8eccc 0x416357c7778c8ecc 0xde7ffcfff8c9eccf 0xfde7ffcfff8c9ecc

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x40001018000030f4 0x040001018000030f

def z548 : W := mkw 0x008a010880000000 0x0008a01088000000 0xc01b0018e0000002 0x0c01b0018e000000

def z549 : W := mkw 0x4f54ded74b0570a9 0x04f54ded74b0570a 0xfe7cfcff1f0ff0fe 0xefe7cfcff1f0ff0f

def z550 : W := mkw 0x449ec15fc20540a1 0x0449ec15fc20540a 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z551 : W := mkw 0x2940028004200202 0x0294002800420020 0x0180030000300300 0x0018003000030030

def z552 : W := mkw 0x0bcb1b88a05a0550 0x80bcb1b88a05a055 0xeffb1ff8e0fe3fff 0xfeffb1ff8e0fe3ff

def z553 : W := mkw 0x84bfa00016ff8000 0x084bfa00016ff800 0xb01fe0001fffc00a 0x0b01fe0001fffc00

def z554 : W := mkw 0x5ffeffffd880e88c 0x45ffeffffd880e88 0xdffffffff801c007 0xfdffffffff801c00

def z555 : W := mkw 0x8dfea00016a58000 0x08dfea00016a5800 0x9fffe0001f01c003 0xe9fffe0001f01c00

def z556 : W := mkw 0x00010108a05a0550 0x800010108a05a055 0x60001318e0fe3ffc 0x160001318e0fe3ff

def z557 : W := mkw 0x049f0108a25f0550 0x8049f0108a25f055 0xff9f1318ffffffff 0xfff9f1318fffffff

def z558 : W := mkw 0x0614181403051021 0x0061418140305102 0xee1c1c1f07061036 0xeee1c1c1f0706103

def z559 : W := mkw 0x108b456be85a6ddc 0xc108b456be85a6dd 0xe19b1fffe0fe3fff 0x7e19b1fffe0fe3ff

def z560 : W := mkw 0x008b0108805a0110 0x8008b0108805a011 0xa19b131800fe133b 0x6a19b131800fe133

def z561 : W := mkw 0x0000000000120110 0x8000000000012011 0x2000000000361330 0x0200000000036133

def z562 : W := mkw 0x09ca800000000000 0x009ca80000000000 0x01e3e00000000001 0x001e3e0000000000

def z563 : W := mkw 0x2ffe9ea01da03a0e 0x02ffe9ea01da03a0 0xbfffffe01ff03f0f 0xfbfffffe01ff03f0

def z564 : W := mkw 0x4ffedffed880280c 0x04ffedffed880280 0xdffffffff8c02c0f 0xfdffffffff8c02c0

def z565 : W := mkw 0x99ebe06274fa8c44 0x499ebe06274fa8c4 0x01e3e0e0e0f00c01 0x101e3e0e0e0f00c0

def z566 : W := mkw 0x06141815020540a1 0x006141815020540a 0xce1c1c1f000fc0f6 0xece1c1c1f000fc0f

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x40030000e0000007 0x340030000e000000

def z568 : W := mkw 0xafffba8017ff9202 0x0afffba8017ff920 0xbffff3001fffd30b 0xebffff3001fffd30

def z569 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x10600ce018c9eccd 0xb10600ce018c9ecc

def z570 : W := mkw 0x00ab2108b0da8550 0x800ab2108b0da855 0xf1fff318f8ffffff 0xff1fff318f8fffff

def z571 : W := mkw 0x2f741eb51fa57aaf 0x02f741eb51fa57aa 0x3fe41fe71ff1ff0d 0xf3fe41fe71ff1ff0

def z572 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3f8013001ff03f08 0x43f8013001ff03f0

def z573 : W := mkw 0x06353c151bcdf0a9 0x006353c151bcdf0a 0xfe7ffc1f1fcff0ff 0xefe7ffc1f1fcff0f

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000820ce 0x240000000000820c

def z575 : W := mkw 0x0000404240000000 0x0000040424000000 0x4007e007e0000002 0x04007e007e000000

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067e00000000003 0xa0067e0000000000

def z577 : W := mkw 0x4b405bdec0000000 0x04b405bdec000000 0x4fe01fffe0000005 0xf4fe01fffe000000

def z578 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0x5e041c1f1f01f0f4 0x85e041c1f1f01f0f

def z579 : W := mkw 0x89eba108b4fa8550 0x889eba108b4fa855 0xe1fbf318e0fe3fff 0x7e1fbf318e0fe3ff

def z580 : W := mkw 0x0614181400000000 0x0061418140000000 0xee1c1c1f000e30fe 0xeee1c1c1f000e30f

def z581 : W := mkw 0x2fff1fbdbfff7fff 0x82fff1fbdbfff7ff 0xffff1fffffffffff 0xfffff1ffffffffff

def z582 : W := mkw 0x849fa015025fc0a1 0x0849fa015025fc0a 0xc01fe01f000fc0f2 0x0c01fe01f000fc0f

def z583 : W := mkw 0x99ebe4637cfaeccc 0x499ebe4637cfaecc 0x51e7ece7f8f9eccf 0xb51e7ece7f8f9ecc

def z584 : W := mkw 0x1001604260488440 0x4100160426048844 0x0003e000e0000000 0x00003e000e000000

def z585 : W := mkw 0x008a010880120110 0x8008a01088012011 0xe19b1318e0361337 0x7e19b1318e036133

def z586 : W := mkw 0x2b401a8005201202 0x02b401a800520120 0x2f80130007f03f0d 0x72f80130007f03f0

def z587 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe01fe01f301300 0xc3fe01fe01f30130

def z588 : W := mkw 0x2f541a9407251223 0x02f541a940725122 0xaf98131807361330 0x4af9813180736133

def z589 : W := mkw 0x54bfe57ff8c8eccc 0x454bfe57ff8c8ecc 0xd07fecfff8c9eccf 0xbd07fecfff8c9ecc

def z590 : W := mkw 0x00010000205a0550 0x800010000205a055 0xe018101800fe3ffe 0x6e018101800fe3ff

def z591 : W := mkw 0xcfffbb9c96ff8000 0x0cfffbb9c96ff800 0xbffff3181fffc00b 0xebffff3181fffc00

def z592 : W := mkw 0x002004201880280c 0x0002004201880280 0x31e01fe018f03f0d 0xf31e01fe018f03f0

def z593 : W := mkw 0x2b611ea03dfa3f5e 0x82b611ea03dfa3f5 0x3fe01fe01ffe3ffd 0xf3fe01fe01ffe3ff

def z594 : W := mkw 0x002004211880688c 0x0002004211880688 0x50640ce718c9eccf 0xb50640ce718c9ecc

def z595 : W := mkw 0x0000404240000000 0x0000040424000000 0x40000ce7e0000004 0x140000ce7e000000

def z596 : W := mkw 0x0dfe800014a00000 0x00dfe800014a0000 0xbfffe0001ff0000b 0xebfffe0001ff0000

def z597 : W := mkw 0xc9ebe3cad4fa8000 0x0c9ebe3cad4fa800 0x01e3e3e0e0f00001 0x101e3e3e0e0f0000

def z598 : W := mkw 0x4414c05640000000 0x04414c0564000000 0x0004e00700000000 0x00004e0070000000

def z599 : W := mkw 0x0f741c151fa570a9 0x00f741c151fa570a 0xfffc1c1f1ffff0ff 0xefffc1c1f1ffff0f

def z600 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0x5e040c071f09e0ce 0xa5e040c071f09e0c

def z601 : W := mkw 0x8f74bc151fa5f0a9 0x08f74bc151fa5f0a 0xfe7cfc1f1f0ff0fe 0xefe7cfc1f1f0ff0f

def z602 : W := mkw 0x808ba000005a8000 0x0808ba000005a800 0x0003e00000000000 0x00003e0000000000

def z603 : W := mkw 0x100164436848e4c8 0x4100164436848e4c 0x5007ec07f809e0ce 0xa5007ec07f809e0c

def z604 : W := mkw 0x49cac3cac0000000 0x049cac3cac000000 0xc1fbf3f8e0000007 0x7c1fbf3f8e000000

def z605 : W := mkw 0x5ffffffff8daeddc 0xc5ffffffff8daedd 0xfffffffff8ffffff 0xffffffffff8fffff

def z606 : W := mkw 0x202004201da03a0e 0x0202004201da03a0 0x30600ce01ff03f0d 0xb30600ce01ff03f0

def z607 : W := mkw 0x449fc15ee05a0550 0x8449fc15ee05a055 0xc01fe01fe00e00f2 0x0c01fe01fe00e00f

def z608 : W := mkw 0xc49fe15ec25f8000 0x0c49fe15ec25f800 0xc01fe01fe00fc002 0x0c01fe01fe00fc00

def z609 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e001c0000000004 0xe0e001c000000000

def z610 : W := mkw 0x0200181400000000 0x0020018140000000 0x40001c1f00000004 0x040001c1f0000000

def z611 : W := mkw 0x10ab656bf8daeddc 0xc10ab656bf8daedd 0x51e7efe7f8f9efcf 0xb51e7efe7f8f9efc

def z612 : W := mkw 0x00010000005a0000 0x000010000005a000 0x2000000000fe0008 0x02000000000fe000

def z613 : W := mkw 0x108b614be05ac5d0 0xc108b614be05ac5d 0xe19ff31fe0ffffff 0x7e19ff31fe0fffff

def z614 : W := mkw 0xa9eba2a014fa8a06 0x0a9eba2a014fa8a0 0x01e3e3e000f00f01 0x101e3e3e000f00f0

def z615 : W := mkw 0xeffffffedfffba0e 0x0effffffedfffba0 0xffffffffffffff0f 0xfffffffffffffff0

def z616 : W := mkw 0x59ebe3eaf0c88c44 0x459ebe3eaf0c88c4 0x01e3e3e0e0c00c01 0x101e3e3e0e0c00c0

def z617 : W := mkw 0x0f541e950b0570a9 0x00f541e950b0570a 0xfffc1fff1f0ff0ff 0xffffc1fff1f0ff0f

def z618 : W := mkw 0x02001c0009003008 0x002001c000900300 0x3f801f001ff03f0d 0xf3f801f001ff03f0

def z619 : W := mkw 0x002044625880280c 0x0002044625880280 0x5067ece7f8c02c0f 0xb5067ece7f8c02c0

def z620 : W := mkw 0xcfdffbdec25f8000 0x0cfdffbdec25f800 0xcfffffffe00fc007 0xfcfffffffe00fc00

def z621 : W := mkw 0x202004201da03a0e 0x0202004201da03a0 0x100000001f000000 0x0100000001f00000

def z622 : W := mkw 0x9d74e4635ea5e88c 0x49d74e4635ea5e88 0x1e64ece71f01c000 0x81e64ece71f01c00

def z623 : W := mkw 0x32217ee379c8fece 0x432217ee379c8fec 0x5067ffe7f8c9ffcf 0xb5067ffe7f8c9ffc

def z624 : W := mkw 0x008a0108a0000550 0x8008a0108a000055 0xc19b1318e0003ff7 0x7c19b1318e0003ff

def z625 : W := mkw 0x16347c775b85f8ad 0x416347c775b85f8a 0xfe7cfcff1f0ff0fe 0xefe7cfcff1f0ff0f

def z626 : W := mkw 0x04140015020540a1 0x004140015020540a 0x000400070001c000 0x0000400070001c00

def z627 : W := mkw 0x0200181401001021 0x0020018140100102 0x0000101800001030 0x0000010180000103

def z628 : W := mkw 0x8dffa00014fa8000 0x08dffa00014fa800 0x8fffe00000f00003 0xe8fffe00000f0000

def z629 : W := mkw 0x549fe15fe048c4c0 0x4549fe15fe048c4c 0xc01fe01fe009c0c2 0x0c01fe01fe009c0c

def z630 : W := mkw 0x6ffedffedda03a0e 0x06ffedffedda03a0 0xdfffffffff000007 0xfdfffffffff00000

def z631 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0x21830300e0fe3ff9 0x121830300e0fe3ff

def z632 : W := mkw 0x028b1d1da95a75f9 0x8028b1d1da95a75f 0xe19b1f1fe0fe3fff 0x7e19b1f1fe0fe3ff

def z633 : W := mkw 0x949fe043625fc4c0 0x4949fe043625fc4c 0xc01fe007e00fc0c2 0x0c01fe007e00fc0c

def z634 : W := mkw 0x000104012b5f75f9 0x8000104012b5f75f 0x300000001ffffff8 0x0300000001ffffff

def z635 : W := mkw 0x008a010880120110 0x8008a01088012011 0x0180030000300300 0x0018003000030030

def z636 : W := mkw 0x2b601fa8bda03f5e 0x82b601fa8bda03f5 0x7fe01ff8fff03ffd 0xf7fe01ff8fff03ff

def z637 : W := mkw 0x469ed95ec0000000 0x0469ed95ec000000 0xce1ffc1fe0000006 0xece1ffc1fe000000

def z638 : W := mkw 0x2b601aa014a00a06 0x02b601aa014a00a0 0x0fe01fe000f00f05 0xf0fe01fe000f00f0

def z639 : W := mkw 0x0940000004200000 0x0094000000420000 0x2f80000007300000 0x42f8000000730000

def z640 : W := mkw 0x008b0509ab5f75f9 0x8008b0509ab5f75f 0xf19b1318ffffffff 0x7f19b1318fffffff

def z641 : W := mkw 0xaf74bea01fa5ba0e 0x0af74bea01fa5ba0 0x1e64ece01f01c000 0x81e64ece01f01c00

def z642 : W := mkw 0x00000108a0000550 0x800000108a000055 0x00000300e0000f00 0x100000300e0000f0

def z643 : W := mkw 0x049e800000000000 0x0049e80000000000 0x801fe00000000002 0x0801fe0000000000

def z644 : W := mkw 0x4f54dbdec0000000 0x04f54dbdec000000 0x4e64ffffe0000004 0x94e64ffffe000000

def z645 : W := mkw 0x4fdedad640000000 0x04fdedad64000000 0x8fffece700000003 0xe8fffece70000000

def z646 : W := mkw 0x8dffa4201effa80c 0x08dffa4201effa80 0xbfffece01fffec0f 0xfbfffece01fffec0

def z647 : W := mkw 0x4fde9f9d8b0570a9 0x04fde9f9d8b0570a 0xff9c1f1f1f0ff0fe 0xeff9c1f1f1f0ff0f

def z648 : W := mkw 0x8dffa4011effe088 0x08dffa4011effe08 0xffffec071fffe0cf 0xeffffec071fffe0c

def z649 : W := mkw 0x8dfe800016b70000 0x08dfe800016b7000 0xbff800001ff60009 0xebff800001ff6000

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x40040c0700000006 0xa40040c070000000

def z651 : W := mkw 0x0b401a8000000000 0x00b401a800000000 0x2fe01fe000f03f0d 0xf2fe01fe000f03f0

def z652 : W := mkw 0x0414000002050000 0x0041400000205000 0xae18000007060000 0x4ae1800000706000

def z653 : W := mkw 0x8ddf8108a67f0550 0x88ddf8108a67f055 0xef9b1318e7fe3fff 0x7ef9b1318e7fe3ff

def z654 : W := mkw 0x52217ffff8c8eccc 0x452217ffff8c8ecc 0x5067fffff8c9eccf 0xb5067fffff8c9ecc

def z655 : W := mkw 0xcffffbded4fa8000 0x0cffffbded4fa800 0xcfffffffe0f00007 0xfcfffffffe0f0000

def z656 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xa19b1318e0f61f31 0x5a19b1318e0f61f3

def z657 : W := mkw 0x3b617ee27de8be4e 0x43b617ee27de8be4 0x3fe3ffe0fff03f0d 0xf3fe3ffe0fff03f0

def z658 : W := mkw 0x008b0000005a0000 0x0008b0000005a000 0x0183000000f00001 0x00183000000f0000

def z659 : W := mkw 0x2b611ea03de83e4e 0x02b611ea03de83e4 0x7fe31fe0fff83fcf 0xf7fe31fe0fff83fc

def z660 : W := mkw 0x0bca1b8880000000 0x00bca1b888000000 0xcffb1ff8e0000007 0xfcffb1ff8e000000

def z661 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3e600ce01ff03f08 0x83e600ce01ff03f0

def z662 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xbe1810181f0ff0f8 0x4be1810181f0ff0f

def z663 : W := mkw 0x2beb1ea01dfa3a0e 0x02beb1ea01dfa3a0 0xbffb1fe01ffe3f0f 0xfbffb1fe01ffe3f0

def z664 : W := mkw 0x0001000020480440 0x0000100002048044 0x00030000e0c00c01 0x100030000e0c00c0

def z665 : W := mkw 0x4ffedbded4a00000 0x04ffedbded4a0000 0xfffffffffff0000f 0xffffffffffff0000

def z666 : W := mkw 0x008b0000205a0550 0x8008b0000205a055 0xa19b000000fe3ffb 0x6a19b000000fe3ff

def z667 : W := mkw 0x296006a01ca02a0e 0x0296006a01ca02a0 0x11e00fe018f02f0d 0xb11e00fe018f02f0

def z668 : W := mkw 0x8dffa4011ffff0a9 0x08dffa4011ffff0a 0xbfffe0001ffff0fb 0xebfffe0001ffff0f

def z669 : W := mkw 0x84bfa00012df8000 0x084bfa00012df800 0x907fe00018cfc00b 0xa907fe00018cfc00

def z670 : W := mkw 0x09eb000014fa0000 0x009eb000014fa000 0xbffb00001ffe000b 0xebffb00001ffe000

def z671 : W := mkw 0x6fffdffefdfa3f5e 0x86fffdffefdfa3f5 0xfffffffffffe3fff 0xffffffffffffe3ff

def z672 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xa19b0300e0fe0f0b 0x7a19b0300e0fe0f0

def z673 : W := mkw 0x8fde9c150f3770a9 0x08fde9c150f3770a 0xff9c1c1f1f3ff0fe 0xeff9c1c1f1f3ff0f

def z674 : W := mkw 0x869fbc150b5ff0a9 0x0869fbc150b5ff0a 0xfe1ffc1f1f0ff0fe 0xefe1ffc1f1f0ff0f

def z675 : W := mkw 0x0ddf8108a05a0550 0x80ddf8108a05a055 0xeffff318e0fe3fff 0xfeffff318e0fe3ff

def z676 : W := mkw 0x6ffedbfed4a00a06 0x06ffedbfed4a00a0 0xcfffffffe0f00f07 0xfcfffffffe0f00f0

def z677 : W := mkw 0x1021606270c88c44 0x41021606270c88c4 0x4067ece7e0c00c07 0xb4067ece7e0c00c0

def z678 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1064ece718c9ecc8 0x81064ece718c9ecc

def z679 : W := mkw 0x4fdedfdfc8006088 0x04fdedfdfc800608 0xdffffffff809e0cf 0xfdffffffff809e0c

def z680 : W := mkw 0x2f741eb51fa57aaf 0x02f741eb51fa57aa 0x1e640ce71f01c000 0x81e640ce71f01c00

def z681 : W := mkw 0x6b605ffedda03a0e 0x06b605ffedda03a0 0x7fe01ffffff03f0d 0xf7fe01ffffff03f0

def z682 : W := mkw 0x4fde9b9c80000000 0x04fde9b9c8000000 0xcf9b1318e0000007 0x7cf9b1318e000000

def z683 : W := mkw 0x10ab646378daeccc 0x410ab646378daecc 0xf1ffece7f8ffeccf 0xff1ffece7f8ffecc

def z684 : W := mkw 0x06141815030550a1 0x006141815030550a 0xee1c101f070fd0f2 0x4ee1c101f070fd0f

def z685 : W := mkw 0x10ab616af0da8d54 0xc10ab616af0da8d5 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z686 : W := mkw 0x0000010880000000 0x0000001088000000 0x40001318e0000004 0x140001318e000000

def z687 : W := mkw 0x80ab200016ff8000 0x080ab200016ff800 0xb19b00001fffc00b 0x6b19b00001fffc00

def z688 : W := mkw 0x008a010880120110 0x8008a01088012011 0xe1981318003e33fe 0x6e1981318003e33f

def z689 : W := mkw 0x8000000006370000 0x0800000000637000 0x2000000007360000 0x0200000000736000

def z690 : W := mkw 0x069f191ca05a0550 0x8069f191ca05a055 0xef9f1f1fe0fe3fff 0xfef9f1f1fe0fe3ff

def z691 : W := mkw 0x59ebe7ebf8c8eccc 0x459ebe7ebf8c8ecc 0x51e7efe7f8c9eccf 0xb51e7efe7f8c9ecc

def z692 : W := mkw 0x8ddfa000025f8000 0x08ddfa000025f800 0x8fffe000000fc003 0xe8fffe000000fc00

def z693 : W := mkw 0x0000000003051021 0x0000000000305102 0x2000000007061030 0x0200000000706103

def z694 : W := mkw 0x0414000002050000 0x0041400000205000 0x801c0000000fc002 0x0801c0000000fc00

def z695 : W := mkw 0x00000108a0000550 0x800000108a000055 0xe0181318e00e3ffe 0x7e0181318e00e3ff

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000c02c0d 0x30000000000c02c0

def z697 : W := mkw 0x4fde9b9c80120110 0x84fde9b9c8012011 0xaf98131800361330 0x4af9813180036133

def z698 : W := mkw 0x5ffffffffbcdfced 0x45ffffffffbcdfce 0xffffffffffcffcff 0xfffffffffffcffcf

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000000e30f8 0x020000000000e30f

def z700 : W := mkw 0x8021200014fa8000 0x08021200014fa800 0x0000000000f00000 0x00000000000f0000

def z701 : W := mkw 0x2bea1fa89da03a0e 0x02bea1fa89da03a0 0xfffb1ff8fff03f0f 0xffffb1ff8fff03f0

def z702 : W := mkw 0x3f757ef77fedfeef 0x43f757ef77fedfee 0xffffffffffffffff 0xffffffffffffffff

def z703 : W := mkw 0x2f741eb51fa57aaf 0x02f741eb51fa57aa 0xfe7c1cff1f0ff0fe 0xefe7c1cff1f0ff0f

def z704 : W := mkw 0x100160436048c4c0 0x4100160436048c4c 0x4007e007e0c9eccf 0x34007e007e0c9ecc

def z705 : W := mkw 0x4fdedbdfc20540a1 0x04fdedbdfc20540a 0xcfffffffe00fc0f7 0xfcfffffffe00fc0f

def z706 : W := mkw 0x8f74bc151fa5f0a9 0x08f74bc151fa5f0a 0x1e64ec071f01c000 0x81e64ec071f01c00

def z707 : W := mkw 0x12005d7fe9007dfd 0xc12005d7fe9007df 0x40001fffe0003ff4 0x140001fffe0003ff

def z708 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe0c02c0f 0xfcfffffffe0c02c0

def z709 : W := mkw 0xcfdedbdec6370000 0x0cfdedbdec637000 0xffffffffff3fc00f 0xfffffffffff3fc00

def z710 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe00820cf 0xfcfffffffe00820c

def z711 : W := mkw 0x4fdedbdec2050000 0x04fdedbdec205000 0xffffffffff0ff0ff 0xfffffffffff0ff0f

def z712 : W := mkw 0x069e595ec0000000 0x0069e595ec000000 0xcfffffffe0000007 0xfcfffffffe000000

def z713 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3f801fe01ff03f0c 0x53f801fe01ff03f0

def z714 : W := mkw 0xc2217bded6ff8000 0x0c2217bded6ff800 0x70001fffffffc00c 0x170001fffffffc00

def z715 : W := mkw 0x12005c7769007ced 0x412005c7769007ce 0x40000ce7e0002cc4 0x140000ce7e0002cc

def z716 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xbfffe000ffffc00b 0xebfffe000ffffc00

def z717 : W := mkw 0x808ba108a05a8550 0x8808ba108a05a855 0xe19bf318e0fe3fff 0x7e19bf318e0fe3ff

def z718 : W := mkw 0x0000404240000000 0x0000040424000000 0x4067ece7e0000002 0x84067ece7e000000

def z719 : W := mkw 0x42005ed7490070a9 0x042005ed7490070a 0x00000ce700000000 0x000000ce70000000

def z720 : W := mkw 0xa69fbea00b5fba0e 0x0a69fbea00b5fba0 0x801fffe0000fff06 0x1801fffe0000fff0

def z721 : W := mkw 0x041404010a056088 0x0041404010a05608 0xfe1c1c1f1f0ff0fe 0xefe1c1c1f1f0ff0f

def z722 : W := mkw 0x42005ad640000000 0x042005ad64000000 0x4067ece7e0000007 0xb4067ece7e000000

def z723 : W := mkw 0x469edbdec0000000 0x0469edbdec000000 0xc07fffffe0000007 0xbc07fffffe000000

def z724 : W := mkw 0x0614585643051021 0x0061458564305102 0xee7ffcffe7061037 0xfee7ffcffe706103

def z725 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x9e7ce0001f0fc002 0x89e7ce0001f0fc00

def z726 : W := mkw 0x0ddec14ac0000000 0x00ddec14ac000000 0xcfffffffe0000007 0xfcfffffffe000000

def z727 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xfffff018fffff0ff 0xefffff018fffff0f

def z728 : W := mkw 0x04bf200012df8000 0x004bf200012df800 0xbfffe0001fffc00b 0xebfffe0001fffc00

def z729 : W := mkw 0x49cac7cbcb0570a9 0x049cac7cbcb0570a 0x31e3e3e0ff0ff0f9 0x131e3e3e0ff0ff0f

def z730 : W := mkw 0x0414405640000000 0x0041440564000000 0xc07fecffe0000007 0xbc07fecffe000000

def z731 : W := mkw 0x8dfea00016a58000 0x08dfea00016a5800 0x1fe7e0001f01c001 0x81fe7e0001f01c00

def z732 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe1fff318e0fe3fff 0xfe1fff318e0fe3ff

def z733 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe0001f3fc002 0xcbfffe0001f3fc00

def z734 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffece01fffc00f 0xfbfffece01fffc00

def z735 : W := mkw 0x2d7402b516a54aa7 0x02d7402b516a54aa 0xc1fc03ff00ffcff3 0x1c1fc03ff00ffcff

def z736 : W := mkw 0x128b5d7fe95a7dfd 0xc128b5d7fe95a7df 0xe19b1fffe0fe3fff 0x7e19b1fffe0fe3ff

def z737 : W := mkw 0x1021646378daeddc 0xc1021646378daedd 0xf07ffcfff8ffffff 0xff07ffcfff8fffff

def z738 : W := mkw 0x04140015020540a1 0x004140015020540a 0xde1c001f1f0fc0f2 0x8de1c001f1f0fc0f

def z739 : W := mkw 0x296006a01da03a0e 0x0296006a01da03a0 0x3fe003e01ff03f09 0xf3fe003e01ff03f0

def z740 : W := mkw 0x09cac04240000000 0x009cac0424000000 0x41e7ece7e0000007 0xb41e7ece7e000000

def z741 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x1e64e0001fc1c009 0xa1e64e0001fc1c00

def z742 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xffffe000ffffc00f 0xfffffe000ffffc00

def z743 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xfffff0181fffc00f 0xefffff0181fffc00

def z744 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffff3001fffc00f 0xfbffff3001fffc00

def z745 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe19f1f1fe0fe3fff 0xfe19f1f1fe0fe3ff

def z746 : W := mkw 0x8d75a00016ff8000 0x08d75a00016ff800 0xbe7ce0001fffc00a 0xebe7ce0001fffc00

def z747 : W := mkw 0x26141eb50b057aaf 0x026141eb50b057aa 0xff9c1fff1fffffff 0xfff9c1fff1ffffff

def z748 : W := mkw 0x1635787673cd9c65 0x41635787673cd9c6 0xae7bf0f8e7c61c31 0x5ae7bf0f8e7c61c3

def z749 : W := mkw 0xc9ebe3caf4fa8550 0x8c9ebe3caf4fa855 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z750 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xbfffe300fffffffb 0xfbfffe300fffffff

def z751 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x3fe7e0001ff1c009 0xe3fe7e0001ff1c00

def z752 : W := mkw 0x3b417ac36568d6c2 0x43b417ac36568d6c 0x6f87f307e739d3c2 0x46f87f307e739d3c

def z753 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1067ece7f8c9cc0b 0xb1067ece7f8c9cc0

def z754 : W := mkw 0x1021242138daeccc 0x41021242138daecc 0x3000000018ffecc8 0x03000000018ffecc

def z755 : W := mkw 0xcfdedbdec6370110 0x8cfdedbdec637011 0xefffffffe7361337 0xfefffffffe736133

def z756 : W := mkw 0x06141e950b0570a9 0x006141e950b0570a 0xfe1c1fff1f0ff0fe 0xffe1c1fff1f0ff0f

def z757 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xffffe0001fffe0cf 0xeffffe0001fffe0c

def z758 : W := mkw 0x0021604270c88440 0x00021604270c8844 0x5067ece7f8c9eccf 0xb5067ece7f8c9ecc

def z759 : W := mkw 0x3b613ea13de8fece 0x43b613ea13de8fec 0x3f8013001ff9ffc8 0x43f8013001ff9ffc

def z760 : W := mkw 0x6fdedbdec5201202 0x06fdedbdec520120 0xcfffffffe7000007 0xfcfffffffe700000

def z761 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x5067ece7f8c1ec0f 0xb5067ece7f8c1ec0

def z762 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xffffe0181fffc0fb 0xeffffe0181fffc0f

def z763 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067fcfff8c9fcff 0xb5067fcfff8c9fcf

def z764 : W := mkw 0x100160436048c4c0 0x4100160436048c4c 0x4067ece7e009c0c2 0x84067ece7e009c0c

def z765 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe3001fffcf0b 0xfbfffe3001fffcf0

def z766 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xc1ffffffe0000007 0x1c1ffffffe000000

def z767 : W := mkw 0x4fdedbdec3051021 0x04fdedbdec305102 0xcfffffffe7000007 0xfcfffffffe700000

def z768 : W := mkw 0x9dffa02036ff8c44 0x49dffa02036ff8c4 0xbfffe0001fffcc0b 0xebfffe0001fffcc0

def z769 : W := mkw 0x06141815030550a1 0x006141815030550a 0xfe1c101f1f0fd0fa 0xefe1c101f1f0fd0f

def z770 : W := mkw 0x0614585640000000 0x0061458564000000 0x4e67ece7e0000007 0xb4e67ece7e000000

def z771 : W := mkw 0x008b2108a05a8550 0x8008b2108a05a855 0xe19ff318e0ffffff 0x7e19ff318e0fffff

def z772 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c101f1f0ff0fa 0x4fe1c101f1f0ff0f

def z773 : W := mkw 0x4fde9b9c83051021 0x04fde9b9c8305102 0x8f98131807000000 0x48f9813180700000

def z774 : W := mkw 0x6fdedbdec1001202 0x06fdedbdec100120 0xcfffffffe0001307 0xfcfffffffe000130

def z775 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x0fe7ffe7e0000005 0xf0fe7ffe7e000000

def z776 : W := mkw 0x0d75200016ed8000 0x00d75200016ed800 0xbfffe0001fffc00b 0xebfffe0001fffc00

def z777 : W := mkw 0x4bcadbcac0000000 0x04bcadbcac000000 0x4fe7ffe7e0000007 0xf4fe7ffe7e000000

def z778 : W := mkw 0x8d74a00016b78000 0x08d74a00016b7800 0x3e64e0001f37c000 0x83e64e0001f37c00

def z779 : W := mkw 0xad74a2a016a58a06 0x0ad74a2a016a58a0 0x1fe4e3e01ff1cf01 0x91fe4e3e01ff1cf0

def z780 : W := mkw 0x296006a01ca02a0e 0x0296006a01ca02a0 0x3fe00fe01ff02f0d 0xf3fe00fe01ff02f0

def z781 : W := mkw 0x094042c240000000 0x0094042c24000000 0x41e7efe7e0000007 0xb41e7efe7e000000

def z782 : W := mkw 0x069f1d1dab5f75f9 0x8069f1d1dab5f75f 0x1f870f07fff1cf01 0x91f870f07fff1cf0

def z783 : W := mkw 0x1021646378c8eddc 0xc1021646378c8edd 0x5067ece7f8c9ffff 0xb5067ece7f8c9fff

def z784 : W := mkw 0x5fffbfbdb8c8eccc 0x45fffbfbdb8c8ecc 0x9f98131818c9ecc8 0x49f98131818c9ecc

def z785 : W := mkw 0x8d74a108b6a58550 0x88d74a108b6a5855 0x5e64f318ff01fff4 0x95e64f318ff01fff

def z786 : W := mkw 0x3f747ef75fa5faaf 0x43f747ef75fa5faa 0x1e64ece71f01c000 0x81e64ece71f01c00

def z787 : W := mkw 0x8dffa00036ff8550 0x88dffa00036ff855 0xbfffe0001fffcf0b 0xebfffe0001fffcf0

def z788 : W := mkw 0x302164637dfaffde 0xc302164637dfaffd 0x7067ece7ffffffff 0xb7067ece7fffffff

def z789 : W := mkw 0x8dffa10896ff8000 0x08dffa10896ff800 0xffffe018ffffc00b 0xeffffe018ffffc00

def z790 : W := mkw 0x52005fffe9007ced 0x452005fffe9007ce 0x40001fffe0003cf4 0x140001fffe0003cf

def z791 : W := mkw 0x64bec57edda03a0e 0x064bec57edda03a0 0xf01fe01ffff03f0a 0x0f01fe01ffff03f0

def z792 : W := mkw 0x2b401a8005201202 0x02b401a800520120 0x2fe01fe007f03f0d 0xf2fe01fe007f03f0

def z793 : W := mkw 0x16353c353bcdfced 0x416353c353bcdfce 0xbe1810181fcffcf8 0x4be1810181fcffcf

def z794 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0xf07fece7f8cfeccf 0xff07fece7f8cfecc

def z795 : W := mkw 0x2beb1fa8bdfa3f5e 0x82beb1fa8bdfa3f5 0xde7b0cf8ff0e00f2 0x8de7b0cf8ff0e00f

def z796 : W := mkw 0x8dffa00036ff8550 0x88dffa00036ff855 0xfffff0181fffffff 0xefffff0181ffffff

def z797 : W := mkw 0x8d75a00016ff8000 0x08d75a00016ff800 0x3e67e0001fffc00b 0xa3e67e0001fffc00

def z798 : W := mkw 0xab60bea01da0ba0e 0x0ab60bea01da0ba0 0x3fe0ffe01ff03f0d 0xf3fe0ffe01ff03f0

def z799 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0xf018101818cffcfe 0x6f018101818cffcf

def z800 : W := mkw 0x10aa656bd892e99c 0xc10aa656bd892e99 0xb1fcffff1837d330 0xcb1fcffff1837d33

def z801 : W := mkw 0x0960200014a08000 0x00960200014a0800 0x3fe4e0001ff1c009 0xe3fe4e0001ff1c00

def z802 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c0c1f1f0ff0fa 0x8fe1c0c1f1f0ff0f

def z803 : W := mkw 0x8dffa10896ff8000 0x08dffa10896ff800 0xfffff318fffff0ff 0xffffff318fffff0f

def z804 : W := mkw 0x0000404240000000 0x0000040424000000 0x41e7ffe7e0000007 0xf41e7ffe7e000000

def z805 : W := mkw 0x0ddf8108a25f0550 0x80ddf8108a25f055 0xfffff318ffffffff 0xffffff318fffffff

def z806 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x9fffe0001ff1c003 0xe9fffe0001ff1c00

def z807 : W := mkw 0x2b405ac245201202 0x02b405ac24520120 0x6fe7ffe7e7301307 0xf6fe7ffe7e730130

def z808 : W := mkw 0x49cac3cac0000000 0x049cac3cac000000 0x41e3efe7e0000005 0x141e3efe7e000000

def z809 : W := mkw 0x2b603ea01da0ba0e 0x02b603ea01da0ba0 0x3fe4ffe01ff1ff0d 0xf3fe4ffe01ff1ff0

def z810 : W := mkw 0x8d75a00016ff8000 0x08d75a00016ff800 0x1e64e0001ff1c000 0x81e64e0001ff1c00

def z811 : W := mkw 0xadffa2a016ff8a06 0x0adffa2a016ff8a0 0xbfffe0e01fffc00b 0xebfffe0e01fffc00

def z812 : W := mkw 0x9ddec4636e376ccc 0x49ddec4636e376cc 0xef980ce7e7362cc4 0x5ef980ce7e7362cc

def z813 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x1fe003e01ff00f01 0x91fe003e01ff00f0

def z814 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c1f1f1f0ffffe 0xffe1c1f1f1f0ffff

def z815 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe0001ff7c001 0xcbfffe0001ff7c00

def z816 : W := mkw 0x0000404240000000 0x0000040424000000 0xe07ffcffe00e30ff 0xfe07ffcffe00e30f

def z817 : W := mkw 0x449ec15ec0000000 0x0449ec15ec000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z818 : W := mkw 0x0961200014e88000 0x00961200014e8800 0x1e67e0001fc9c00b 0xa1e67e0001fc9c00

def z819 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xbffff300ffffff0f 0xfbffff300ffffff0

def z820 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c1c1f1f0fd0f2 0xcfe1c1c1f1f0fd0f

def z821 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xde1c0c1f1f0fe0fe 0xade1c0c1f1f0fe0f

def z822 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xbffff318ffffdf3b 0xfbffff318ffffdf3

def z823 : W := mkw 0x32005ef769007eef 0x432005ef769007ee 0x40001fffe0003ff4 0x140001fffe0003ff

def z824 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe013e01ff03f09 0x53fe013e01ff03f0

def z825 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe1fb1ff8e0fe3fff 0xfe1fb1ff8e0fe3ff

def z826 : W := mkw 0x8d75a00036ff8550 0x88d75a00036ff855 0x3e64e0001ffffff8 0x83e64e0001ffffff

def z827 : W := mkw 0x1021604370c8c4c0 0x41021604370c8c4c 0x5067ece7f8c9c0cf 0xb5067ece7f8c9c0c

def z828 : W := mkw 0x6fdedbdec5201202 0x06fdedbdec520120 0xefffffffe7f03f0f 0xfefffffffe7f03f0

def z829 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x100000001809c0c0 0x0100000001809c0c

def z830 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xbffff3181ffffffb 0xebffff3181ffffff

def z831 : W := mkw 0x0414000002050000 0x0041400000205000 0xbe7fe0001f0fc00b 0xebe7fe0001f0fc00

def z832 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xffffe018fffffffb 0xeffffe018fffffff

def z833 : W := mkw 0x4b405bdec0000000 0x04b405bdec000000 0x4fe7ffffe0000007 0xf4fe7ffffe000000

def z834 : W := mkw 0x102124213bdffdfd 0xc102124213bdffdf 0x300000001ffffff8 0x0300000001ffffff

def z835 : W := mkw 0x0960200014a08000 0x00960200014a0800 0x1e64e0001f01c000 0x81e64e0001f01c00

def z836 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffce0001fffc008 0xcbffce0001fffc00

def z837 : W := mkw 0x22001ea009003a0e 0x022001ea009003a0 0x3f801fe01ff03f0d 0xf3f801fe01ff03f0

def z838 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xde1c1c1f1f0fc0f6 0xede1c1c1f1f0fc0f

def z839 : W := mkw 0x4f55dad6605a0550 0x84f55dad6605a055 0x2e64ece700fe3ff8 0x82e64ece700fe3ff

def z840 : W := mkw 0x096004201ca0280c 0x0096004201ca0280 0x3fe01fe01ff03f0d 0xf3fe01fe01ff03f0

def z841 : W := mkw 0x2b601aa015a01a06 0x02b601aa015a01a0 0x3fe013e01ff01f09 0xf3fe013e01ff01f0

def z842 : W := mkw 0x0d54800002050000 0x00d5480000205000 0xbe7ce0001f0fc00a 0xebe7ce0001f0fc00

def z843 : W := mkw 0x12015c7769487ced 0x412015c7769487ce 0xe01b1cffe0ce3cff 0x7e01b1cffe0ce3cf

def z844 : W := mkw 0x8dde800006370000 0x08dde80000637000 0xbfffe0001f3fc00b 0xebfffe0001f3fc00

def z845 : W := mkw 0x849fa108a25f8550 0x8849fa108a25f855 0xfe1ff018ff0ff0fe 0xefe1ff018ff0ff0f

def z846 : W := mkw 0x8bebbc151dfaf0a9 0x08bebbc151dfaf0a 0x41e3fc1f00f030f5 0x041e3fc1f00f030f

def z847 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x9e7fe0001fcfc00b 0xa9e7fe0001fcfc00

def z848 : W := mkw 0x10ab2529b8daeddc 0xc10ab2529b8daedd 0xb198131818fffff8 0x4b198131818fffff

def z849 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x3fe4f3001ff1ff0d 0xf3fe4f3001ff1ff0

def z850 : W := mkw 0x2b601ea11da07a8e 0x02b601ea11da07a8 0x7fe01fe71ff03fcd 0xf7fe01fe71ff03fc

def z851 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1067ece7f8c1ec0d 0xb1067ece7f8c1ec0

def z852 : W := mkw 0x4fdedbdec0000110 0x84fdedbdec000011 0xcfffffffe0001337 0xfcfffffffe000133

def z853 : W := mkw 0x8dfea00016b78000 0x08dfea00016b7800 0xbfffe0001f37c003 0xebfffe0001f37c00

def z854 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xfffff3181fffffff 0xffffff3181ffffff

def z855 : W := mkw 0x0435200032cd8440 0x00435200032cd844 0xfe7ff018ffcffcff 0xffe7ff018ffcffcf

def z856 : W := mkw 0xcfde9b9c86250000 0x0cfde9b9c8625000 0x8f98131807000000 0x48f9813180700000

def z857 : W := mkw 0x002044635880688c 0x0002044635880688 0x5067ece7f8c9eccf 0xb5067ece7f8c9ecc

def z858 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0xbffce0001fffc00b 0xebffce0001fffc00

def z859 : W := mkw 0xcfdedbdec6250000 0x0cfdedbdec625000 0xcfffffffe7000007 0xfcfffffffe700000

def z860 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe7c1cff1f0ff0ff 0xffe7c1cff1f0ff0f

def z861 : W := mkw 0x2b601aa015a01a06 0x02b601aa015a01a0 0x0fe003e007f00f01 0x10fe003e007f00f0

def z862 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xffffec071fffc00f 0xeffffec071fffc00

def z863 : W := mkw 0x041404150b0570a9 0x0041404150b0570a 0xfe1c001f1f0ff0fa 0xefe1c001f1f0ff0f

def z864 : W := mkw 0x102164637ce8eccc 0x4102164637ce8ecc 0x7067ece7fff9eccf 0xb7067ece7fff9ecc

def z865 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xf19f1318f8ffffff 0xff19f1318f8fffff

def z866 : W := mkw 0x8dffa00036ff8440 0x08dffa00036ff844 0xbfffe0001fffeccb 0xebfffe0001fffecc

def z867 : W := mkw 0x2b401ea00d203a0e 0x02b401ea00d203a0 0x2f801fe007f03f0d 0x72f801fe007f03f0

def z868 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x7e67ece7ffc9eccf 0xf7e67ece7ffc9ecc

def z869 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe0f00f07 0xfcfffffffe0f00f0

def z870 : W := mkw 0x008a0108a0120550 0x8008a0108a012055 0xe1981318e0f63ffd 0x7e1981318e0f63ff

def z871 : W := mkw 0x008a414ac0000000 0x0008a414ac000000 0xc07fecffe0000007 0xbc07fecffe000000

def z872 : W := mkw 0x2b601eb51da07aaf 0x02b601eb51da07aa 0x7fe41fff1ff9ffff 0xf7fe41fff1ff9fff

def z873 : W := mkw 0x0021644358c8e088 0x00021644358c8e08 0x5067ece7f8c9e0cf 0xb5067ece7f8c9e0c

def z874 : W := mkw 0x2b601aa014a00a06 0x02b601aa014a00a0 0x3fe01fe01ff00f0d 0xf3fe01fe01ff00f0

def z875 : W := mkw 0x8dffa10896ff8110 0x88dffa10896ff811 0xfffff318ffffd33f 0xffffff318ffffd33

def z876 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x1fe7e0001ff9c00b 0xa1fe7e0001ff9c00

def z877 : W := mkw 0x1021646378daeddc 0xc1021646378daedd 0x5067ece7f8cfecff 0xb5067ece7f8cfecf

def z878 : W := mkw 0x8dfea00016b78000 0x08dfea00016b7800 0xbffce0001f3fc00a 0xebffce0001f3fc00

def z879 : W := mkw 0x2b601ea11da07a8e 0x02b601ea11da07a8 0xfffc1fff1fffffff 0xffffc1fff1ffffff

def z880 : W := mkw 0x302124213dfaffde 0xc302124213dfaffd 0x300000001ffffff8 0x0300000001ffffff

def z881 : W := mkw 0x8dffa10896ff8000 0x08dffa10896ff800 0xfffff318ffffff0f 0xffffff318ffffff0

def z882 : W := mkw 0x8dffa10896ff8110 0x88dffa10896ff811 0xbfffe0181fffc03b 0xebfffe0181fffc03

def z883 : W := mkw 0x8d75a00016ed8000 0x08d75a00016ed800 0x1e64e0001fc9c008 0x81e64e0001fc9c00

def z884 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xce7ffcffe0000006 0xece7ffcffe000000

def z885 : W := mkw 0x4bcadbdec0000000 0x04bcadbdec000000 0xc1fbffffe0000007 0x7c1fbffffe000000

def z886 : W := mkw 0x04bf2108b2df8550 0x804bf2108b2df855 0xfffff318ffffffff 0xffffff318fffffff

def z887 : W := mkw 0x0021200010c88000 0x00021200010c8800 0x3e67e0001fc9c00b 0xe3e67e0001fc9c00

def z888 : W := mkw 0x8ddec04246370000 0x08ddec0424637000 0xefffece7e7360007 0xfefffece7e736000

def z889 : W := mkw 0x02005c57490070a9 0x002005c57490070a 0x40001cffe00030f4 0x140001cffe00030f

def z890 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x8fffffffe0000001 0xd8fffffffe000000

def z891 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x3fe7e0001fffc009 0x83fe7e0001fffc00

def z892 : W := mkw 0x6f74def75fa57aaf 0x06f74def75fa57aa 0x1e64ece71f01c000 0x81e64ece71f01c00

def z893 : W := mkw 0x1021646378daeddc 0xc1021646378daedd 0x71e7ffe7f8ffffff 0xf71e7ffe7f8fffff

def z894 : W := mkw 0x1021606370c8ccc4 0x41021606370c8ccc 0x4067ece7e0c9ccc7 0xb4067ece7e0c9ccc

def z895 : W := mkw 0x0ddf8000025f0000 0x00ddf8000025f000 0xbfffe0001fffc00b 0xebfffe0001fffc00

def z896 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x1fe4e0001f01c001 0xe1fe4e0001f01c00

def z897 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe0001ffff0fb 0xebfffe0001ffff0f

def z898 : W := mkw 0x49cac3cac0000000 0x049cac3cac000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z899 : W := mkw 0x26141c350b057aaf 0x026141c350b057aa 0xfe1c1c1f1f0ffffe 0xefe1c1c1f1f0ffff

def z900 : W := mkw 0x0dfe800016a50000 0x00dfe800016a5000 0xbfffe0001fffc00b 0xebfffe0001fffc00

def z901 : W := mkw 0x0000404240000000 0x0000040424000000 0x5067ece7f809c00f 0xb5067ece7f809c00

def z902 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f8c9ecca 0x85067ece7f8c9ecc

def z903 : W := mkw 0x0dde810882050000 0x00dde81088205000 0xfffff318ff0ff0ff 0xffffff318ff0ff0f

def z904 : W := mkw 0x42005fdfe90075f9 0x842005fdfe90075f 0x40001fffe0003ff4 0x140001fffe0003ff

def z905 : W := mkw 0xadffa2a016ff8a06 0x0adffa2a016ff8a0 0xbffff3e01fffff0f 0xfbffff3e01fffff0

def z906 : W := mkw 0x302164637ce8eece 0x4302164637ce8eec 0x5067ece7f8f9efcf 0xb5067ece7f8f9efc

def z907 : W := mkw 0x1021646378daeddc 0xc1021646378daedd 0x5067ece7f8f9efcf 0xb5067ece7f8f9efc

def z908 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x4067ece7e0c9ecc7 0x14067ece7e0c9ecc

def z909 : W := mkw 0x102064637880eccc 0x4102064637880ecc 0x5067ece7f801ecc7 0xb5067ece7f801ecc

def z910 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1fe01fe01ff03f05 0x91fe01fe01ff03f0

def z911 : W := mkw 0x3b603ea11da0fa8e 0x43b603ea11da0fa8 0x3fe01fe01ff1ff0d 0xf3fe01fe01ff1ff0

def z912 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x3000000018f9ffc8 0x03000000018f9ffc

def z913 : W := mkw 0x8dfea00016b78000 0x08dfea00016b7800 0x9e7ce0001f07c000 0x89e7ce0001f07c00

def z914 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0xbff81fe01ffe3f0f 0xfbff81fe01ffe3f0

def z915 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x7fe31fe0fff03f0f 0xf7fe31fe0fff03f0

def z916 : W := mkw 0x100160436048c4c0 0x4100160436048c4c 0x4067ece7e0c9eccf 0xb4067ece7e0c9ecc

def z917 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe000300f 0xfefffffffe000300

def z918 : W := mkw 0x4fde9b9c82050021 0x04fde9b9c8205002 0x8f98131800060030 0x48f9813180006003

def z919 : W := mkw 0x04140015020540a1 0x004140015020540a 0xfe1c101f1f0ff0fe 0xefe1c101f1f0ff0f

def z920 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x1e67e0001f01c003 0xa1e67e0001f01c00

def z921 : W := mkw 0x0d54c04240000000 0x00d54c0424000000 0x4e67ece7e0000007 0xb4e67ece7e000000

def z922 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1f1c1fff0ff0ff 0xffe1f1c1fff0ff0f

def z923 : W := mkw 0x449fc15fe25f45f1 0x8449fc15fe25f45f 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z924 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x9fffe0001f0fc003 0xe9fffe0001f0fc00

def z925 : W := mkw 0x2b601eb51da07aaf 0x02b601eb51da07aa 0x3fe01fe71ff03f0d 0xf3fe01fe71ff03f0

def z926 : W := mkw 0x149f615fe25fc5f1 0xc149f615fe25fc5f 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z927 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x1fe4e0001ff1c001 0x81fe4e0001ff1c00

def z928 : W := mkw 0x302124213ce8eece 0x4302124213ce8eec 0x1000000018f9efc8 0x01000000018f9efc

def z929 : W := mkw 0x8d75a00016ff8000 0x08d75a00016ff800 0x1e64e0001f0fc000 0x81e64e0001f0fc00

def z930 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xa19b1318e0fe3ff9 0x5a19b1318e0fe3ff

def z931 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0x4fe7ffe7e0000007 0xf4fe7ffe7e000000

def z932 : W := mkw 0x12005c57690074e9 0x412005c57690074e 0x40001c1fe00030f4 0x040001c1fe00030f

def z933 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x5067ece7f809e0cf 0xb5067ece7f809e0c

def z934 : W := mkw 0x0434200012858000 0x0043420001285800 0xbe7ce0001f0fc00a 0xebe7ce0001f0fc00

def z935 : W := mkw 0x0dffa00014e88000 0x00dffa00014e8800 0xbfffe0001ff9c00b 0xebfffe0001ff9c00

def z936 : W := mkw 0x4fdedad640000000 0x04fdedad64000000 0xcfffece7e0000007 0xfcfffece7e000000

def z937 : W := mkw 0x4fdedbdec2050000 0x04fdedbdec205000 0xefffffffe7060007 0xfefffffffe706000

def z938 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe01fe01ffe3ffd 0xf3fe01fe01ffe3ff

def z939 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0xce7ffcffe0000007 0xfce7ffcffe000000

def z940 : W := mkw 0x8dfea00016b78000 0x08dfea00016b7800 0x1fe4e0001f31c000 0x81fe4e0001f31c00

def z941 : W := mkw 0x2b601ea11da07aaf 0x02b601ea11da07aa 0x3fe01fe01ff03ffd 0xf3fe01fe01ff03ff

def z942 : W := mkw 0x143524213acdeccc 0x4143524213acdecc 0xbe1c00001fcfecca 0xebe1c00001fcfecc

def z943 : W := mkw 0x428a5bdec0000000 0x0428a5bdec000000 0xc1ffffffe0000007 0xfc1ffffffe000000

def z944 : W := mkw 0xefde9b9c87371202 0x0efde9b9c8737120 0xaf98131807361300 0x4af9813180736130

def z945 : W := mkw 0x0961200034e88440 0x00961200034e8844 0x7fe7f300fff9ffcf 0xf7fe7f300fff9ffc

def z946 : W := mkw 0x8414a00002058000 0x08414a0000205800 0x1e04e0001f01c000 0x81e04e0001f01c00

def z947 : W := mkw 0x102124213acdeced 0x4102124213acdece 0x1000000018cfecf8 0x01000000018cfecf

def z948 : W := mkw 0x1021606270c88c44 0x41021606270c88c4 0x5067ece7f8c9cc0f 0xb5067ece7f8c9cc0

def z949 : W := mkw 0x328b5febe95a7fde 0xc328b5febe95a7fd 0xe19b1fffe0fe3fff 0x7e19b1fffe0fe3ff

def z950 : W := mkw 0x1021242139c8fccc 0x41021242139c8fcc 0x300000001fc9fcc8 0x0300000001fc9fcc

def z951 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe181c1f1f0ff0fc 0x4fe181c1f1f0ff0f

def z952 : W := mkw 0x06141c350b0578ad 0x006141c350b0578a 0xfe1c1cff1f0ffcfe 0xffe1c1cff1f0ffcf

def z953 : W := mkw 0x8dfea00016b78000 0x08dfea00016b7800 0xbffce0001ff7c009 0xebffce0001ff7c00

def z954 : W := mkw 0x0614181402050000 0x0061418140205000 0xfe1c1c1f1f0ff0fe 0xefe1c1c1f1f0ff0f

def z955 : W := mkw 0x0001604240488000 0x0000160424048800 0x4067ece7e009c007 0xb4067ece7e009c00

def z956 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xc19b1318e0fe3ff7 0x1c19b1318e0fe3ff

def z957 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe00e00f7 0xfcfffffffe00e00f

def z958 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x5000000018c9ecce 0x25000000018c9ecc

def z959 : W := mkw 0x4fdedbdec2050021 0x04fdedbdec205002 0xcfffffffe0060037 0xfcfffffffe006003

def z960 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f8c1cc07 0xb5067ece7f8c1cc0

def z961 : W := mkw 0x4fdedbdec2050000 0x04fdedbdec205000 0xdfffffffff01c007 0xfdfffffffff01c00

def z962 : W := mkw 0x8dffa00036ff8440 0x08dffa00036ff844 0xbfffe000ffffcc0b 0xfbfffe000ffffcc0

def z963 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffff0001ffff00f 0xebffff0001ffff00

def z964 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xdffffffff809c00f 0xfdffffffff809c00

def z965 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffff0181fffd03b 0xebffff0181fffd03

def z966 : W := mkw 0x26141eb50b057aaf 0x026141eb50b057aa 0xfe1c1cff1f0ff0fe 0xefe1c1cff1f0ff0f

def z967 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0xfff81ff81ff03f0f 0xffff81ff81ff03f0

def z968 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xce7fffffe0000006 0x9ce7fffffe000000

def z969 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xffffe018ffffecff 0xfffffe018ffffecf

def z970 : W := mkw 0x8414a00002058000 0x08414a0000205800 0xbe1ce0001f0fc00a 0xebe1ce0001f0fc00

def z971 : W := mkw 0x302124213de8fece 0x4302124213de8fec 0x100000001fc9ecc8 0x0100000001fc9ecc

def z972 : W := mkw 0x4fdedbdec4200000 0x04fdedbdec420000 0xefffffffe7300007 0xfefffffffe730000

def z973 : W := mkw 0x8dffa00036ff8440 0x08dffa00036ff844 0xfffff018fffffcff 0xffffff018fffffcf

def z974 : W := mkw 0x8dffa10896ff8110 0x88dffa10896ff811 0xbffff3181fffff3f 0xfbffff3181fffff3

def z975 : W := mkw 0x1021646358c8e88c 0x41021646358c8e88 0x5067ece7f8c9c00f 0xb5067ece7f8c9c00

def z976 : W := mkw 0x902124213eedeccc 0x4902124213eedecc 0x100000001fc9ecc8 0x0100000001fc9ecc

def z977 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x1000000018c9eccd 0x31000000018c9ecc

def z978 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x2fe003e007f00f01 0x52fe003e007f00f0

def z979 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe0000002 0xccfffffffe000000

def z980 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c1c1f1ffffffe 0xefe1c1c1f1ffffff

def z981 : W := mkw 0x408ac14ac0000000 0x0408ac14ac000000 0x4067ece7e0000007 0xb4067ece7e000000

def z982 : W := mkw 0x8dffa28016ff8000 0x08dffa28016ff800 0xbfffe3e01fffc00b 0xfbfffe3e01fffc00

def z983 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe0301307 0xfefffffffe030130

def z984 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f8c9c0cb 0xa5067ece7f8c9c0c

def z985 : W := mkw 0x3021242139c8fece 0x43021242139c8fec 0x1000000018c9ffc8 0x01000000018c9ffc

def z986 : W := mkw 0x46145bdec0000000 0x046145bdec000000 0xce7fffffe0000007 0xfce7fffffe000000

def z987 : W := mkw 0x6fdedbdec7251223 0x06fdedbdec725122 0xefffffffe7361337 0xfefffffffe736133

def z988 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x3180130018f9ffcd 0x73180130018f9ffc

def z989 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x2fe01fe007f03f05 0x52fe01fe007f03f0

def z990 : W := mkw 0x04152000024d8000 0x004152000024d800 0xbe1fe0001f0fc00a 0xebe1fe0001f0fc00

def z991 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f809e0ce 0xa5067ece7f809e0c

def z992 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c1c1f1fcffcff 0xffe1c1c1f1fcffcf

def z993 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x71e7ece7f8f9eccf 0xf71e7ece7f8f9ecc

def z994 : W := mkw 0xcfde9b9c86370110 0x8cfde9b9c8637011 0xaf98131807361330 0x4af9813180736133

def z995 : W := mkw 0x2b601aa015a01a06 0x02b601aa015a01a0 0x2fe01fe007f01f05 0xf2fe01fe007f01f0

def z996 : W := mkw 0x4fdedbdec3051021 0x04fdedbdec305102 0xefffffffe70e30ff 0xfefffffffe70e30f

def z997 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe19b1318e0f63ff5 0x5e19b1318e0f63ff

def z998 : W := mkw 0x4fde9b9c82050000 0x04fde9b9c8205000 0xaf98131807060000 0x4af9813180706000

def z999 : W := mkw 0x0fdedac240000000 0x00fdedac24000000 0xcfffffe7e0000007 0xfcfffffe7e000000

def z1000 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1067ece7f8c9ecc9 0x91067ece7f8c9ecc

def z1001 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x7067ece7f8cffcff 0xb7067ece7f8cffcf

def z1002 : W := mkw 0x99ebe16af4fa8d54 0xc99ebe16af4fa8d5 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z1003 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xfffff318ffffd3fb 0xefffff318ffffd3f

def z1004 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffbe0001fffc009 0x4bffbe0001fffc00

def z1005 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbf9fe0001fffc00a 0x4bf9fe0001fffc00

def z1006 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x4fe7efe7e0000007 0xb4fe7efe7e000000

def z1007 : W := mkw 0x4fdedbdec0120110 0x84fdedbdec012011 0xcfffffffe0300307 0xfcfffffffe030030

def z1008 : W := mkw 0xadffa28016ff8202 0x0adffa28016ff820 0xbfffe3001fffc30b 0xebfffe3001fffc30

def z1009 : W := mkw 0x4f54dbdec0000000 0x04f54dbdec000000 0x4e67ffffe0000007 0xb4e67ffffe000000

def z1010 : W := mkw 0x0fded85640000000 0x00fded8564000000 0xcffffcffe0000007 0xfcffffcffe000000

def z1011 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe7ffe01ff03f0f 0xf3fe7ffe01ff03f0

def z1012 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x9fffe0001fffc003 0x89fffe0001fffc00

def z1013 : W := mkw 0x1021242138c8eddc 0xc1021242138c8edd 0x1000000018c9fff8 0x01000000018c9fff

def z1014 : W := mkw 0x1000446368006ccc 0x41000446368006cc 0x5067ece7f809eccf 0xb5067ece7f809ecc

def z1015 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe0fe3fff 0xfefffffffe0fe3ff

def z1016 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xce7fecffe0000007 0xbce7fecffe000000

def z1017 : W := mkw 0x902164637cfaeccc 0x4902164637cfaecc 0x5067ece7f8f9eccf 0xb5067ece7f8f9ecc

def z1018 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x7067ece7f8f9ffcf 0xb7067ece7f8f9ffc

def z1019 : W := mkw 0x3021646379c8fece 0x43021646379c8fec 0x5067ece7f8c9ffcf 0xb5067ece7f8c9ffc

def z1020 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe0f0000f 0xfefffffffe0f0000

def z1021 : W := mkw 0x0dffa00012cd8000 0x00dffa00012cd800 0xbfffe0001fcfc00b 0xebfffe0001fcfc00

def z1022 : W := mkw 0x4fdedbdec1001000 0x04fdedbdec100100 0xefffffffe7001007 0xfefffffffe700100

def z1023 : W := mkw 0x00000108a0000550 0x800000108a000055 0xe1981318e0fe3fff 0x7e1981318e0fe3ff

def z1024 : W := mkw 0x296002a014a00a06 0x0296002a014a00a0 0x3fe013e01ff03f0d 0xf3fe013e01ff03f0

def z1025 : W := mkw 0x849fa108a25f8550 0x8849fa108a25f855 0xff9ff318ffffffff 0xfff9ff318fffffff

def z1026 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffecffe0000003 0xecfffecffe000000

def z1027 : W := mkw 0x12005c77490078ad 0x412005c77490078a 0x00000ce700000000 0x000000ce70000000

def z1028 : W := mkw 0x0435200012cd8000 0x00435200012cd800 0x1e67e0001fc9c00b 0xa1e67e0001fc9c00

def z1029 : W := mkw 0x4000415ec0000000 0x04000415ec000000 0x4067ecffe0000007 0xb4067ecffe000000

def z1030 : W := mkw 0x8d75a00016ff8000 0x08d75a00016ff800 0x3fe4e0001fffc009 0xe3fe4e0001fffc00

def z1031 : W := mkw 0x0f545ad640000000 0x00f545ad64000000 0xcfffffffe0000007 0xfcfffffffe000000

def z1032 : W := mkw 0x8435200016ff8000 0x08435200016ff800 0xbe7fe0001fffc00b 0xebe7fe0001fffc00

def z1033 : W := mkw 0x849fa000025f8000 0x0849fa000025f800 0x9e1fe0001f0fc002 0x89e1fe0001f0fc00

def z1034 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe1c0c1f1f0fc0fa 0xefe1c0c1f1f0fc0f

def z1035 : W := mkw 0x12005c77490078ad 0x412005c77490078a 0x40001cff000030f4 0x040001cff000030f

def z1036 : W := mkw 0x4bcadbdec0000000 0x04bcadbdec000000 0x4fe3ffffe0000005 0xf4fe3ffffe000000

def z1037 : W := mkw 0x1021646379c8fced 0x41021646379c8fce 0x5067ece7f8c9fcff 0xb5067ece7f8c9fcf

def z1038 : W := mkw 0x0020604250808000 0x0002060425080800 0x5067ece7f801c007 0xb5067ece7f801c00

def z1039 : W := mkw 0x8dffa00016ff8110 0x88dffa00016ff811 0xbfffe0001fffd33b 0xebfffe0001fffd33

def z1040 : W := mkw 0x02001c0109007088 0x002001c010900708 0xfe1c1c1f1f0ff0fe 0xefe1c1c1f1f0ff0f

def z1041 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe0001fffff0b 0xebfffe0001fffff0

def z1042 : W := mkw 0x32005ee349007a8e 0x432005ee349007a8 0x00000ce700000000 0x000000ce70000000

def z1043 : W := mkw 0x4fdedbdec1001021 0x04fdedbdec100102 0xcfffffffe0001037 0xfcfffffffe000103

def z1044 : W := mkw 0x302164637de8fece 0x4302164637de8fec 0x5067ece7ffc9eccf 0xb5067ece7ffc9ecc

def z1045 : W := mkw 0xb02124213ffffece 0x4b02124213ffffec 0x300000001fffffc8 0x0300000001fffffc

def z1046 : W := mkw 0x8dfea00016a58000 0x08dfea00016a5800 0x9e7fe0001f01c002 0x89e7fe0001f01c00

def z1047 : W := mkw 0x8dffa00036ff8550 0x88dffa00036ff855 0xffffe000ffffffff 0xfffffe000fffffff

def z1048 : W := mkw 0x12005c6369007ccc 0x412005c6369007cc 0x40001ce7e0003cc4 0x140001ce7e0003cc

def z1049 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe00fe01ff00f09 0xf3fe00fe01ff00f0

def z1050 : W := mkw 0x0000444348006088 0x0000044434800608 0x5067ece7f801c007 0xb5067ece7f801c00

def z1051 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x0e67ece7e0000000 0x80e67ece7e000000

def z1052 : W := mkw 0x949fe14be25fc5d0 0xc949fe14be25fc5d 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z1053 : W := mkw 0xcfde9b9c82170000 0x0cfde9b9c8217000 0x8f98131800060000 0x48f9813180006000

def z1054 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xff9c1f1f1f0ff0ff 0xfff9c1f1f1f0ff0f

def z1055 : W := mkw 0x8d75a00016ed8000 0x08d75a00016ed800 0x1e67e0001f09c002 0x81e67e0001f09c00

def z1056 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x7fe01ff81ff03ffd 0xf7fe01ff81ff03ff

def z1057 : W := mkw 0x6fde9b9c87251223 0x06fde9b9c8725122 0xaf98131807361330 0x4af9813180736133

def z1058 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe41fe01ff9ff0f 0xf3fe41fe01ff9ff0

def z1059 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe19b1318e0fe3ffa 0x4e19b1318e0fe3ff

def z1060 : W := mkw 0x42005bdec0000000 0x042005bdec000000 0x4063ffffe0000005 0x14063ffffe000000

def z1061 : W := mkw 0x09eb2108b4fa8550 0x809eb2108b4fa855 0xfffff318ffffffff 0xffffff318fffffff

def z1062 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x7067fce7f8c9fccf 0xf7067fce7f8c9fcc

def z1063 : W := mkw 0x008a404240000000 0x0008a40424000000 0xc1ffece7e0000007 0xfc1ffece7e000000

def z1064 : W := mkw 0x0200584240000000 0x0020058424000000 0x4e67fce7e0000007 0xf4e67fce7e000000

def z1065 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0xd07fecfff8cfecff 0xbd07fecfff8cfecf

def z1066 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x3e64e0001f01c008 0xe3e64e0001f01c00

def z1067 : W := mkw 0x2b601eb51da07aaf 0x02b601eb51da07aa 0xfff81fff1ffe3fff 0xffff81fff1ffe3ff

def z1068 : W := mkw 0xc49fe15ee25f8550 0x8c49fe15ee25f855 0xc01fe01fe00fc0f2 0x0c01fe01fe00fc0f

def z1069 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0xf1fffffff8ffffff 0xff1fffffff8fffff

def z1070 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xfe7ffc1f1f0ff0ff 0xefe7ffc1f1f0ff0f

def z1071 : W := mkw 0x2b601eb41da03a0e 0x02b601eb41da03a0 0x7fe01fff1ff03f0d 0xf7fe01fff1ff03f0

def z1072 : W := mkw 0x84bfa00012df8000 0x084bfa00012df800 0xbe7fe0001fcfc00b 0xebe7fe0001fcfc00

def z1073 : W := mkw 0x4ddec15ec0000000 0x04ddec15ec000000 0xcfffecffe0000007 0xfcfffecffe000000

def z1074 : W := mkw 0x102124213ce8eccc 0x4102124213ce8ecc 0x300000001ff9ecc8 0x0300000001ff9ecc

def z1075 : W := mkw 0x8dffa01416ff8000 0x08dffa01416ff800 0xffffe01f1fffc00b 0xeffffe01f1fffc00

def z1076 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x3e64e0001ff1c008 0x83e64e0001ff1c00

def z1077 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f8c9ccc3 0x95067ece7f8c9ccc

def z1078 : W := mkw 0x0940404240000000 0x0094040424000000 0x4fe7ece7e0000007 0xf4fe7ece7e000000

def z1079 : W := mkw 0x902124213effeddc 0xc902124213effedd 0x300000001ffffff8 0x0300000001ffffff

def z1080 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f809ecc6 0x95067ece7f809ecc

def z1081 : W := mkw 0x1021242138daeddc 0xc1021242138daedd 0x1000000018cfecf8 0x01000000018cfecf

def z1082 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xde7fe018ff0fc0f2 0x8de7fe018ff0fc0f

def z1083 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xe1981318e0fe3ffc 0x5e1981318e0fe3ff

def z1084 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffefffe0000003 0x9cfffefffe000000

def z1085 : W := mkw 0xcfde9b9c87371021 0x0cfde9b9c8737102 0xaf98131807361030 0x4af9813180736103

def z1086 : W := mkw 0x008a414ac0000000 0x0008a414ac000000 0x41e7efe7e0000007 0xb41e7efe7e000000

def z1087 : W := mkw 0x4414c05640000000 0x04414c0564000000 0x4067ece7e0000007 0xb4067ece7e000000

def z1088 : W := mkw 0x1021646378daeccc 0x41021646378daecc 0x7067ece7f8ffeccf 0xb7067ece7f8ffecc

def z1089 : W := mkw 0x428a5fdfc90070a9 0x0428a5fdfc90070a 0xe19b1fffe00e30ff 0x7e19b1fffe00e30f

def z1090 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x0000000000c02cc0 0x00000000000c02cc

def z1091 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x7fe41fe71ff03f0f 0xf7fe41fe71ff03f0

def z1092 : W := mkw 0x4ddec3dec0000000 0x04ddec3dec000000 0xc1ffefffe0000007 0xbc1ffefffe000000

def z1093 : W := mkw 0x8dffa10896ff8000 0x08dffa10896ff800 0xbffff3181fffc00b 0xebffff3181fffc00

def z1094 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xfffff318ffffc0ff 0xffffff318ffffc0f

def z1095 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xff9c1f1f1f3ff3fe 0xeff9c1f1f1f3ff3f

def z1096 : W := mkw 0x8dffa108b6ff8440 0x08dffa108b6ff844 0xfffff318ffffeccf 0xffffff318ffffecc

def z1097 : W := mkw 0x0b601a8014a00000 0x00b601a8014a0000 0x3fe01fe01ff03f0d 0xf3fe01fe01ff03f0

def z1098 : W := mkw 0x8dffa10896ff8110 0x88dffa10896ff811 0xbfffe3001fffc30b 0xebfffe3001fffc30

def z1099 : W := mkw 0x8dffa00036ff8440 0x08dffa00036ff844 0xffffe000ffffc0cb 0xeffffe000ffffc0c

def z1100 : W := mkw 0x0200585640000000 0x0020058564000000 0x4067fcffe0000007 0xb4067fcffe000000

def z1101 : W := mkw 0x8dfea10896a58000 0x08dfea10896a5800 0xdffff318ff01c007 0xfdffff318ff01c00

def z1102 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe0061037 0xfefffffffe006103

def z1103 : W := mkw 0x0bca5bcac0000000 0x00bca5bcac000000 0xcfffffffe0000007 0xfcfffffffe000000

def z1104 : W := mkw 0x0434200012858000 0x0043420001285800 0x1e64e0001f01c000 0x81e64e0001f01c00

def z1105 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcffbffffe0000005 0x5cffbffffe000000

def z1106 : W := mkw 0x1021242138daeddc 0xc1021242138daedd 0x1000000018f9efc8 0x01000000018f9efc

def z1107 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x5067ece7f801c002 0x85067ece7f801c00

def z1108 : W := mkw 0x06141815020540a1 0x006141815020540a 0xfe1c1c1f1f0fc0fe 0xefe1c1c1f1f0fc0f

def z1109 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xffffe300ffffefcf 0xfffffe300ffffefc

def z1110 : W := mkw 0xefdedbdec7371202 0x0efdedbdec737120 0xefffffffe7361307 0xfefffffffe736130

def z1111 : W := mkw 0x8961200016ff8000 0x08961200016ff800 0x3fe7e0001fffc00b 0xe3fe7e0001fffc00

def z1112 : W := mkw 0x8dffa10896ff8110 0x88dffa10896ff811 0xfffff3181ffff3ff 0xefffff3181ffff3f

def z1113 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe00030f7 0xfcfffffffe00030f

def z1114 : W := mkw 0x100060434000c080 0x4100060434000c08 0x4067ece7e001c007 0xb4067ece7e001c00

def z1115 : W := mkw 0x4bcadbdec0000000 0x04bcadbdec000000 0x01e3efe7e0000001 0x101e3efe7e000000

def z1116 : W := mkw 0x84bfa00016ff8000 0x084bfa00016ff800 0xbe1fe0001fffc00a 0xebe1fe0001fffc00

def z1117 : W := mkw 0x49cac3cac0000000 0x049cac3cac000000 0x01e7efe7e0000001 0x901e7efe7e000000

def z1118 : W := mkw 0x0000404240000000 0x0000040424000000 0xc07ffcffe0000007 0xfc07ffcffe000000

def z1119 : W := mkw 0x00014443684864c8 0x000014443684864c 0x5067ece7f8c9eccf 0xb5067ece7f8c9ecc

def z1120 : W := mkw 0x4fdedbdec0120110 0x84fdedbdec012011 0xefffffffe03e33ff 0xfefffffffe03e33f

def z1121 : W := mkw 0x42005fdfc90070a9 0x042005fdfc90070a 0x40001fffe0000004 0x140001fffe000000

def z1122 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0xd07ffcfff8c9eccf 0xfd07ffcfff8c9ecc

def z1123 : W := mkw 0x8d75a00016ed8000 0x08d75a00016ed800 0xbe7fe0001fcfc00b 0xebe7fe0001fcfc00

def z1124 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x1004000018c9ecca 0xa1004000018c9ecc

def z1125 : W := mkw 0x42005d5fc90070a9 0x042005d5fc90070a 0x40001c1fe00030f4 0x040001c1fe00030f

def z1126 : W := mkw 0x849fa000025f8000 0x0849fa000025f800 0xbf9fe0001fffc00b 0xebf9fe0001fffc00

def z1127 : W := mkw 0x008a414ac0120110 0x8008a414ac012011 0xe1ffffffe0361337 0xfe1ffffffe036133

def z1128 : W := mkw 0x4fdedbdec0120110 0x84fdedbdec012011 0xcfffffffe0060037 0xfcfffffffe006003

def z1129 : W := mkw 0x0d54800002050000 0x00d5480000205000 0x1e64e0001f01c000 0x81e64e0001f01c00

def z1130 : W := mkw 0x09eb200014fa8000 0x009eb200014fa800 0xbfffe0001fffc00b 0xebfffe0001fffc00

def z1131 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x51e7efe7f8f9efcf 0xb51e7efe7f8f9efc

def z1132 : W := mkw 0x8dffa02016ff8804 0x08dffa02016ff880 0xbfffe0e01fffcc0b 0xfbfffe0e01fffcc0

def z1133 : W := mkw 0x0000404240000000 0x0000040424000000 0x61e7ffe7e0f03f0f 0xf61e7ffe7e0f03f0

def z1134 : W := mkw 0x008b0108a05a0550 0x8008b0108a05a055 0xff9b1318fffe3fff 0xfff9b1318fffe3ff

def z1135 : W := mkw 0x89eba00016ff8000 0x089eba00016ff800 0x3fe3e0001fffc009 0xe3fe3e0001fffc00

def z1136 : W := mkw 0x8dfea00016a58000 0x08dfea00016a5800 0xbfffe0001ff1c00b 0xebfffe0001ff1c00

def z1137 : W := mkw 0x902124213adfeccc 0x4902124213adfecc 0x1000000018cfecc8 0x01000000018cfecc

def z1138 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbe7fe0001f0fc00a 0xebe7fe0001f0fc00

def z1139 : W := mkw 0x449ec15ec0000000 0x0449ec15ec000000 0xc07fecffe0000002 0x8c07fecffe000000

def z1140 : W := mkw 0x4fdedbdec2050000 0x04fdedbdec205000 0xcfffffffe00fc007 0xfcfffffffe00fc00

def z1141 : W := mkw 0x0b405ac240000000 0x00b405ac24000000 0x4e67ece7e0000007 0xb4e67ece7e000000

def z1142 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x1000000018c1cc00 0x01000000018c1cc0

def z1143 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe01fe01ff03f08 0xc3fe01fe01ff03f0

def z1144 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x8fffefe7e0000003 0xf8fffefe7e000000

def z1145 : W := mkw 0x4fde9b9c83171131 0x84fde9b9c8317113 0xaf98131807361330 0x4af9813180736133

def z1146 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbfffe0001fffec0f 0xfbfffe0001fffec0

def z1147 : W := mkw 0x902124213cfaeccc 0x4902124213cfaecc 0x1000000018f9ecc8 0x01000000018f9ecc

def z1148 : W := mkw 0x302124213fedfeef 0x4302124213fedfee 0x300000001ffffff8 0x0300000001ffffff

def z1149 : W := mkw 0x8d75a00016ed8000 0x08d75a00016ed800 0x3fe7e0001ff9c00b 0xe3fe7e0001ff9c00

def z1150 : W := mkw 0x4bcadbdec0000000 0x04bcadbdec000000 0x41e7ffffe0000007 0xb41e7ffffe000000

def z1151 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0xfe7cf0181f0ff0fe 0xefe7cf0181f0ff0f

def z1152 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f809c0c7 0xb5067ece7f809c0c

def z1153 : W := mkw 0xadffa3a8b6ff8f56 0x8adffa3a8b6ff8f5 0xbfffe3e0ffffcf0b 0xfbfffe3e0ffffcf0

def z1154 : W := mkw 0x8dffa01416ff8021 0x08dffa01416ff802 0xbfffe0181fffc03b 0xebfffe0181fffc03

def z1155 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0x0e67ece7e0000001 0x90e67ece7e000000

def z1156 : W := mkw 0xad74a2a016a58a06 0x0ad74a2a016a58a0 0x1e64e0e01f01c000 0x81e64e0e01f01c00

def z1157 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ece7f8c1ecc5 0x95067ece7f8c1ecc

def z1158 : W := mkw 0xadffa02016ff8a06 0x0adffa02016ff8a0 0xbfffe0001fffcf0b 0xebfffe0001fffcf0

def z1159 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xde1c1c1f1f0ff0f6 0x8de1c1c1f1f0ff0f

def z1160 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbe7fe0001fffc00a 0x8be7fe0001fffc00

def z1161 : W := mkw 0x4940c2c240000000 0x04940c2c24000000 0x4067ece7e0000007 0xb4067ece7e000000

def z1162 : W := mkw 0x102124213acdeccc 0x4102124213acdecc 0x300000001fcfecc8 0x0300000001fcfecc

def z1163 : W := mkw 0x1021242139c8fced 0x41021242139c8fce 0x1000000018c9fcf8 0x01000000018c9fcf

def z1164 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x9e7ce0001f01c002 0xe9e7ce0001f01c00

def z1165 : W := mkw 0x0414404240000000 0x0041440424000000 0xce7fece7e0000007 0xfce7fece7e000000

def z1166 : W := mkw 0x049e800002050000 0x0049e80000205000 0xbe1fe0001f0fc00a 0xebe1fe0001f0fc00

def z1167 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xfffff318ffffcf0f 0xffffff318ffffcf0

def z1168 : W := mkw 0x72005fffe9007ece 0x472005fffe9007ec 0x40001fffe0003fc4 0x140001fffe0003fc

def z1169 : W := mkw 0x89eba00014fa8000 0x089eba00014fa800 0x3fe7e0001ff9c00b 0xe3fe7e0001ff9c00

def z1170 : W := mkw 0x2b601aa015a01a06 0x02b601aa015a01a0 0x2fe013e007f03f0d 0x72fe013e007f03f0

def z1171 : W := mkw 0x02201c201980380c 0x002201c201980380 0x3fe01fe01ff03f0d 0xf3fe01fe01ff03f0

def z1172 : W := mkw 0x0b401e8009003008 0x00b401e800900300 0x3fe01fe01ff03f0d 0xf3fe01fe01ff03f0

def z1173 : W := mkw 0x2b601ea11da07a8e 0x02b601ea11da07a8 0x3fe41fe71ff1ff0d 0xf3fe41fe71ff1ff0

def z1174 : W := mkw 0x8d75a00016ed8000 0x08d75a00016ed800 0x1e67e0001fc1c001 0x81e67e0001fc1c00

def z1175 : W := mkw 0x62005fffc9007aaf 0x062005fffc9007aa 0x40001fffe0003ff4 0x140001fffe0003ff

def z1176 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe01fe01ff01f01 0xd3fe01fe01ff01f0

def z1177 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0xbffff3001fffd30b 0xebffff3001fffd30

def z1178 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0xbe7ce0001f07c000 0xcbe7ce0001f07c00

def z1179 : W := mkw 0x0000404340004080 0x0000040434000408 0x4067ece7e009c0c7 0xb4067ece7e009c0c

def z1180 : W := mkw 0x32005febe9007fde 0xc32005febe9007fd 0x40001fffe0003ff4 0x140001fffe0003ff

def z1181 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0xffffe318ffffcffb 0xfffffe318ffffcff

def z1182 : W := mkw 0x428b5fdfe95a75f9 0x8428b5fdfe95a75f 0xe19b1fffe0fe3fff 0x7e19b1fffe0fe3ff

def z1183 : W := mkw 0x8dffa00036ff8440 0x08dffa00036ff844 0xfffff300ffffffcf 0xffffff300ffffffc

def z1184 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x7fe01fe01ff83fcf 0xf7fe01fe01ff83fc

def z1185 : W := mkw 0x8dffa00036ff8550 0x88dffa00036ff855 0xbfffe0001fffc0fb 0xebfffe0001fffc0f

def z1186 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x1067ece7f801c000 0x81067ece7f801c00

def z1187 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x3fe00fe01ff03f09 0x93fe00fe01ff03f0

def z1188 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xff9c1c1f1ffff0ff 0xeff9c1c1f1ffff0f

def z1189 : W := mkw 0x39eb63eaf4fa8f56 0xc39eb63eaf4fa8f5 0x01e3e3e0e0f00f01 0x101e3e3e0e0f00f0

def z1190 : W := mkw 0x4fdedbdec3051021 0x04fdedbdec305102 0xffffffffff0fd03f 0xfffffffffff0fd03

def z1191 : W := mkw 0x4fdedbdec0120110 0x84fdedbdec012011 0xefffffffe0f63f3f 0xfefffffffe0f63f3

def z1192 : W := mkw 0x902124213ffffced 0x4902124213ffffce 0x300000001ffffcf8 0x0300000001ffffcf

def z1193 : W := mkw 0x8dffa00016ff8000 0x08dffa00016ff800 0x1e67e0001f01c000 0x81e67e0001f01c00

def z1194 : W := mkw 0x02005ac240000000 0x002005ac24000000 0x4067ffe7e0000007 0xb4067ffe7e000000

def z1195 : W := mkw 0x1021242138c8eccc 0x41021242138c8ecc 0x3000000018cffcf8 0x03000000018cffcf

def z1196 : W := mkw 0x102064635880e88c 0x4102064635880e88 0x1067ece7f801c001 0x91067ece7f801c00

def z1197 : W := mkw 0x2b601ea11da07a8e 0x02b601ea11da07a8 0x3fe01fe01ff9ffcd 0xf3fe01fe01ff9ffc

def z1198 : W := mkw 0x8ddfa000067f8000 0x08ddfa000067f800 0xbf9fe0001f3fc00a 0xebf9fe0001f3fc00

def z1199 : W := mkw 0x049ec04240000000 0x0049ec0424000000 0xc07fece7e0000007 0xbc07fece7e000000

def z1200 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x3fe4e0001f31c000 0xc3fe4e0001f31c00

def z1201 : W := mkw 0x400043cac0000000 0x0400043cac000000 0x4067efe7e0000007 0xb4067efe7e000000

def z1202 : W := mkw 0x102124213bcdfced 0x4102124213bcdfce 0x100000001fc9ecc8 0x0100000001fc9ecc

def z1203 : W := mkw 0x9dffa4213effeccc 0x49dffa4213effecc 0xbf9800001fffecc8 0x4bf9800001fffecc

def z1204 : W := mkw 0x0000404240000000 0x0000040424000000 0x4067ece7e0c02c0f 0xb4067ece7e0c02c0

def z1205 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x5067ffe7f8c9ffcf 0xb5067ffe7f8c9ffc

def z1206 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1fe01fe01ff00f05 0xf1fe01fe01ff00f0

def z1207 : W := mkw 0x0001000020480440 0x0000100002048044 0xe19b1318e0fe3fff 0x7e19b1318e0fe3ff

def z1208 : W := mkw 0x06141c150b0570a9 0x006141c150b0570a 0xbe1c1c1f1f0ff0f8 0xcbe1c1c1f1f0ff0f

def z1209 : W := mkw 0x0000404240000000 0x0000040424000000 0x4063ece7e0000005 0x14063ece7e000000

def z1210 : W := mkw 0x8d75a00036ed8440 0x08d75a00036ed844 0x5e67e000ffc9eccf 0xb5e67e000ffc9ecc

def z1211 : W := mkw 0x2b601eb41da03a2f 0x02b601eb41da03a2 0x3fe01ff81ff03f3d 0xf3fe01ff81ff03f3

def z1212 : W := mkw 0xcfdedbdec2170000 0x0cfdedbdec217000 0xcfffffffe0060007 0xfcfffffffe006000

def z1213 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0x1fe00fe01ff02f0d 0xb1fe00fe01ff02f0

def z1214 : W := mkw 0x0021646258c8a80c 0x00021646258c8a80 0x5067ece7f8c9ec0f 0xb5067ece7f8c9ec0

def z1215 : W := mkw 0x0000404240000000 0x0000040424000000 0x0067ece7e0000001 0x90067ece7e000000

def z1216 : W := mkw 0x8ddfa000025f8000 0x08ddfa000025f800 0xbfffe0001f0fc00b 0xebfffe0001f0fc00

def z1217 : W := mkw 0x2b601ea01da03a0e 0x02b601ea01da03a0 0xbff81ff81ff63f3d 0xfbff81ff81ff63f3

def z1218 : W := mkw 0x0000414ac0000000 0x00000414ac000000 0x4067ffffe0000007 0xb4067ffffe000000

def z1219 : W := mkw 0xcfdedbdec4320000 0x0cfdedbdec432000 0xcfffffffe0300007 0xfcfffffffe030000

def z1220 : W := mkw 0x6fdedbdec5321312 0x86fdedbdec532131 0xefffffffe7361337 0xfefffffffe736133

def z1221 : W := mkw 0x100164636848eccc 0x4100164636848ecc 0x4067ece7e009ecc7 0xb4067ece7e009ecc

def z1222 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xcfffffffe0003f07 0xfcfffffffe0003f0

def z1223 : W := mkw 0x0dde800002050000 0x00dde80000205000 0x9fffe0001f01c003 0xe9fffe0001f01c00

def z1224 : W := mkw 0x4fdedbdec3171131 0x84fdedbdec317113 0xefffffffe7361337 0xfefffffffe736133

def z1225 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x1e64e0001f09c00a 0xa1e64e0001f09c00

def z1226 : W := mkw 0xadffa3a8b6ff8f56 0x8adffa3a8b6ff8f5 0xfffff3f8ffffffff 0xffffff3f8fffffff

def z1227 : W := mkw 0x4f54dad640000000 0x04f54dad64000000 0x4e67ece7e0000002 0x84e67ece7e000000

def z1228 : W := mkw 0x8dfea00016a58000 0x08dfea00016a5800 0xbfffe0001f0fc00b 0xebfffe0001f0fc00

def z1229 : W := mkw 0x100164436848e4c8 0x4100164436848e4c 0x5067ece7f809e0cf 0xb5067ece7f809e0c

def z1230 : W := mkw 0x8d74a00016a58000 0x08d74a00016a5800 0x3e64e0001f0fc008 0x83e64e0001f0fc00

def z1231 : W := mkw 0x8dffa108b6ff8550 0x88dffa108b6ff855 0x1fe7e300fff1cf01 0x91fe7e300fff1cf0

def z1232 : W := mkw 0x4fdedbdec0120000 0x04fdedbdec012000 0xefffffffe0360007 0xfefffffffe036000

def z1233 : W := mkw 0x32005ee349007a8e 0x432005ee349007a8 0x00001fe700003f04 0x100001fe700003f0

def z1234 : W := mkw 0x42005ed7490070a9 0x042005ed7490070a 0x40001cff000030f4 0x040001cff000030f

def z1235 : W := mkw 0x008a010880000000 0x0008a01088000000 0xe19b1318e0fe3fff 0x7e19b1318e0fe3ff

def z1236 : W := mkw 0x8dfea00016a58000 0x08dfea00016a5800 0x9ffce0001f01c000 0xc9ffce0001f01c00

def z1237 : W := mkw 0x0000404240000000 0x0000040424000000 0x4067ece7e00820cf 0xb4067ece7e00820c

def z1238 : W := mkw 0x302164637de8fece 0x4302164637de8fec 0x71e7ffe7fff9ffcf 0xf71e7ffe7fff9ffc

def z1239 : W := mkw 0x32015ee369487ece 0x432015ee369487ec 0x61831fe7e0f83fcf 0x761831fe7e0f83fc

def z1240 : W := mkw 0x8dfea10896b78110 0x88dfea10896b7811 0xbffcf3181f37d330 0xcbffcf3181f37d33

def z1241 : W := mkw 0x1021646378c8eccc 0x41021646378c8ecc 0x51e7ffe7f8c9eccf 0xf51e7ffe7f8c9ecc

def z1242 : W := mkw 0x32005ee369007ece 0x432005ee369007ec 0x40000ce7e0002cc4 0x140000ce7e0002cc

def z1243 : W := mkw 0x1021646379c8fccc 0x41021646379c8fcc 0x7067ece7ffc9fccf 0xb7067ece7ffc9fcc

def z1244 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0x4fe7ffffe0000005 0x94fe7ffffe000000

def z1245 : W := mkw 0xcdffa38896ff8000 0x0cdffa38896ff800 0xbfffe3001fffc00b 0xebfffe3001fffc00

def z1246 : W := mkw 0x8dffa10896ff8000 0x08dffa10896ff800 0xbfffe300ffffc00b 0xfbfffe300ffffc00

def z1247 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xffffffffff00000f 0xfffffffffff00000

def z1248 : W := mkw 0x469ed95ec0000000 0x0469ed95ec000000 0xce7ffcffe0000007 0xfce7ffcffe000000

def z1249 : W := mkw 0x4ddec3cac0000000 0x04ddec3cac000000 0xcfffefe7e0000007 0xfcfffefe7e000000

def z1250 : W := mkw 0x6fdedbdec4200202 0x06fdedbdec420020 0xcfffffffe0300307 0xfcfffffffe030030

def z1251 : W := mkw 0x4fdedbdec0000000 0x04fdedbdec000000 0xefffffffe00e000f 0xfefffffffe00e000

def z1252 : W := mkw 0x0414404242050000 0x0041440424205000 0xfe7fece7ff0fc00f 0xffe7fece7ff0fc00

def z1253 : W := mkw 0xcdffa11c96ff8000 0x0cdffa11c96ff800 0xbfffe0181fffc00b 0xebfffe0181fffc00

def z1254 : W := mkw 0x041404150a0560a9 0x0041404150a0560a 0xfe1c0c1f1f0fe0fe 0xefe1c0c1f1f0fe0f

def z1255 : W := mkw 0x26141e950b0572ab 0x026141e950b0572a 0xfe1c1f1f1f0ff3fe 0xefe1c1f1f1f0ff3f

def z1256 : W := mkw 0x8dffa00016ed8000 0x08dffa00016ed800 0x9fffe0001fc9c00b 0xe9fffe0001fc9c00

def z1257 : W := mkw 0x8dffa00036ff8550 0x88dffa00036ff855 0xbffff3001fffffff 0xfbffff3001ffffff

def z1258 : W := mkw 0xcfdedbdec7371021 0x0cfdedbdec737102 0xefffffffe7361037 0xfefffffffe736103

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z8,z5,z6]),(0,[z1,z2,z7,z4,z5,z9,z6]),(0,[z0,z1,z2,z7,z4,z6,z10]),(0,[z11,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z12,z6])],[(0,[z1,z2,z7,z13,z4,z5,z6]),(0,[z14,z15,z2,z7,z4,z5,z6]),(0,[z1,z2,z16,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z18,z6]),(0,[z1,z2,z7,z4,z5,z19,z6]),(0,[z0,z1,z2,z20,z4,z5,z6]),(0,[z1,z2,z21,z7,z4,z5,z22])],[(0,[z1,z2,z23,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z6,z25]),(0,[z1,z2,z20,z7,z4,z6,z22])],[(1,[z1,z26,z7,z27,z5,z6]),(0,[z1,z2,z7,z28,z4,z5,z6])],[(0,[z29,z1,z2,z7,z4,z5,z17]),(0,[z1,z30,z2,z7,z4,z5,z17]),(0,[z31,z1,z2,z7,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z32]),(0,[z0,z1,z33,z2,z7,z4,z6])],[(0,[z1,z34,z2,z7,z4,z5,z6]),(0,[z35,z1,z2,z7,z4,z5,z6]),(0,[z36,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z37,z4,z5,z6])],[(0,[z0,z38,z1,z2,z7,z4,z6]),(0,[z1,z39,z2,z7,z27,z5,z6]),(0,[z1,z2,z40,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z41,z5,z6]),(0,[z0,z1,z2,z42,z7,z4,z6]),(1,[z1,z2,z43,z7,z4,z6]),(0,[z1,z2,z44,z7,z4,z5,z6])],[(0,[z1,z45,z2,z7,z4,z5,z17]),(0,[z46,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z47,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z48,z6]),(0,[z1,z45,z2,z7,z4,z5,z32]),(0,[z1,z2,z20,z7,z4,z49,z6]),(0,[z1,z2,z7,z50,z4,z5,z6]),(0,[z1,z2,z7,z51,z4,z5,z52])]],
   [[(0,[z1,z2,z7,z4,z5,z6,z53]),(0,[z1,z54,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z55,z5,z6]),(0,[z1,z56,z2,z7,z4,z5,z6]),(1,[z57,z1,z2,z4,z5,z58]),(0,[z57,z1,z2,z7,z51,z4,z5]),(1,[z1,z2,z4,z59,z5,z6]),(0,[z1,z2,z60,z7,z4,z5,z6])],[(0,[z61,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z62,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z63,z5,z6]),(0,[z1,z2,z64,z7,z4,z5,z6])],[(0,[z1,z2,z65,z7,z4,z5,z24]),(0,[z1,z26,z2,z20,z7,z4,z6])],[(1,[z1,z2,z66,z4,z5,z6]),(0,[z1,z67,z2,z7,z4,z5,z6]),(0,[z68,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z69,z6]),(0,[z1,z2,z7,z4,z5,z70,z6]),(0,[z0,z71,z1,z2,z7,z4,z6])],[(0,[z1,z72,z2,z7,z4,z5,z6]),(0,[z0,z1,z73,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z74,z6]),(0,[z75,z1,z2,z4,z5,z76,z6]),(0,[z1,z2,z7,z4,z5,z77,z6]),(0,[z1,z2,z20,z7,z4,z78,z6]),(0,[z79,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z80,z6]),(0,[z1,z2,z81,z7,z4,z5,z6]),(1,[z82,z2,z7,z4,z83,z6]),(0,[z1,z2,z7,z84,z4,z5,z6]),(1,[z2,z7,z4,z5,z24,z17]),(0,[z1,z2,z7,z4,z5,z85,z6]),(0,[z1,z30,z7,z4,z5,z6,z86])],[(0,[z0,z1,z2,z65,z7,z4,z6]),(0,[z1,z2,z7,z87,z4,z5,z6]),(0,[z1,z2,z7,z4,z88,z5,z6]),(0,[z1,z2,z7,z4,z89,z5,z6]),(0,[z1,z2,z42,z7,z4,z5,z52]),(0,[z1,z2,z7,z4,z90,z5,z22])],[(0,[z1,z2,z7,z4,z5,z17,z86]),(0,[z1,z2,z91,z7,z4,z5,z24]),(0,[z92,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z4,z93,z5,z6]),(0,[z1,z2,z7,z4,z94,z5,z6]),(0,[z1,z2,z7,z4,z5,z95,z6]),(0,[z1,z2,z21,z7,z4,z90,z6])]],
   [[(1,[z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z7,z4,z5,z96,z6]),(1,[z0,z1,z2,z4,z97,z6]),(0,[z1,z2,z7,z4,z5,z49,z6])],[(0,[z0,z98,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z99,z6]),(0,[z1,z2,z7,z100,z4,z5,z6])],[(0,[z38,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z7,z101,z102,z4,z5]),(0,[z1,z2,z103,z7,z4,z5,z6]),(0,[z104,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z42,z7,z5,z10]),(0,[z1,z2,z42,z7,z4,z5,z10])],[(0,[z1,z2,z7,z4,z105,z5,z6]),(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z1,z106,z2,z7,z4,z5,z6]),(0,[z1,z107,z2,z7,z4,z5,z6])],[(0,[z108,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z4,z76,z6]),(0,[z1,z2,z7,z4,z6,z109,z58])],[(0,[z1,z2,z7,z4,z99,z5,z17]),(0,[z1,z110,z2,z7,z4,z5,z6]),(0,[z111,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z112,z7,z4,z5,z6]),(0,[z0,z1,z2,z16,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z113,z6]),(0,[z1,z2,z7,z4,z5,z6,z114])],[(0,[z1,z115,z2,z7,z4,z5,z6]),(0,[z14,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z116,z5,z17]),(0,[z1,z2,z7,z117,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z52,z6]),(1,[z1,z2,z7,z4,z118,z6])],[(0,[z1,z39,z119,z7,z4,z5,z6]),(0,[z1,z2,z120,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z121,z6]),(0,[z1,z30,z39,z7,z4,z5,z6]),(1,[z1,z2,z20,z7,z4,z6])]],
   [[(0,[z122,z1,z123,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z124,z5,z17]),(0,[z15,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z125,z4,z5,z6]),(0,[z1,z2,z7,z4,z126,z5,z6])],[(0,[z1,z127,z2,z7,z4,z5,z6]),(0,[z1,z128,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z129]),(1,[z1,z2,z130,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z131,z6]),(1,[z1,z2,z7,z4,z5,z132]),(0,[z1,z2,z7,z4,z5,z133,z6]),(1,[z1,z2,z4,z5,z6,z134])],[(0,[z1,z2,z7,z117,z99,z5,z6]),(0,[z1,z2,z7,z4,z5,z135,z24]),(0,[z1,z2,z136,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z137,z5,z6]),(0,[z1,z2,z7,z4,z138,z5,z6]),(0,[z139,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z140]),(0,[z1,z141,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z4,z6,z10])],[(0,[z1,z2,z7,z4,z142,z5,z6]),(0,[z1,z2,z3,z65,z4,z5,z6])],[(0,[z1,z2,z7,z4,z143,z5,z6]),(0,[z144,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z145]),(0,[z82,z1,z2,z7,z4,z5,z129]),(0,[z1,z2,z146,z7,z4,z5,z6]),(0,[z1,z2,z7,z147,z4,z5,z6]),(0,[z1,z2,z7,z148,z4,z5,z6]),(0,[z149,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z76,z24]),(0,[z1,z2,z4,z97,z150,z5,z6]),(1,[z1,z2,z151,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z152,z6]),(0,[z1,z153,z2,z7,z4,z5,z6])]],
   [[(0,[z154,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z155,z5,z6]),(0,[z1,z2,z7,z4,z156,z124,z6]),(0,[z1,z157,z2,z7,z4,z5,z6]),(0,[z1,z158,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z159])],[(0,[z1,z2,z16,z3,z4,z5,z6]),(0,[z122,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z160,z7,z4,z5,z6])],[(1,[z1,z2,z7,z161,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z162,z1,z2,z7,z4,z163,z6]),(0,[z1,z2,z7,z4,z5,z164,z6]),(0,[z1,z2,z7,z4,z5,z17,z58]),(0,[z165,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z27,z97,z5,z6]),(0,[z1,z2,z7,z4,z166,z97,z5]),(0,[z57,z1,z2,z42,z7,z4,z5])],[(0,[z167,z1,z2,z7,z4,z5,z17]),(0,[z122,z38,z2,z7,z4,z5,z6]),(0,[z1,z2,z168,z7,z4,z5,z6]),(0,[z1,z2,z169,z7,z4,z5,z17]),(0,[z1,z2,z7,z170,z4,z5,z6]),(0,[z0,z1,z2,z21,z7,z4,z6])],[(0,[z1,z2,z171,z7,z4,z5,z6]),(0,[z1,z2,z172,z7,z4,z5,z6]),(0,[z0,z15,z1,z2,z7,z4,z6]),(0,[z173,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z174,z5,z6])],[(0,[z1,z2,z7,z4,z150,z5,z24]),(0,[z1,z2,z42,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z175,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z176]),(0,[z1,z2,z7,z4,z97,z5,z17]),(0,[z1,z2,z42,z7,z117,z5,z6]),(0,[z177,z1,z2,z7,z4,z156,z6]),(1,[z1,z2,z7,z4,z70,z6]),(0,[z1,z2,z7,z4,z5,z178,z6]),(0,[z1,z2,z20,z7,z179,z4,z6]),(0,[z1,z2,z180,z7,z4,z5,z6]),(1,[z1,z2,z20,z4,z150,z6]),(0,[z1,z2,z181,z7,z4,z5,z6]),(0,[z1,z2,z62,z4,z5,z182,z6])],[(0,[z1,z2,z7,z51,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z32,z6]),(0,[z1,z2,z7,z4,z183,z5,z6])]],
   [[(1,[z1,z2,z7,z4,z105,z6]),(0,[z1,z2,z184,z7,z4,z5,z6]),(0,[z1,z185,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z186,z6])],[(0,[z1,z2,z2,z7,z4,z5,z6])],[(0,[z82,z1,z2,z7,z4,z124,z6]),(0,[z1,z2,z7,z4,z5,z187,z24]),(0,[z1,z2,z20,z65,z7,z4,z6]),(0,[z177,z1,z7,z4,z156,z5,z6]),(0,[z1,z2,z7,z4,z188,z5,z6]),(0,[z1,z2,z7,z4,z189,z5,z6]),(1,[z1,z7,z50,z4,z5,z6])],[(0,[z167,z1,z2,z7,z4,z105,z6]),(0,[z1,z2,z7,z4,z190,z5,z6]),(1,[z111,z0,z1,z2,z4,z6]),(0,[z1,z2,z7,z4,z191,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z192]),(0,[z1,z2,z193,z7,z4,z5,z6])],[(1,[z1,z2,z7,z137,z5,z6]),(0,[z194,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z117,z97,z5,z6]),(0,[z1,z2,z7,z4,z195,z5,z6]),(0,[z1,z2,z196,z7,z4,z5,z6]),(0,[z0,z0,z1,z2,z7,z4,z6])],[(0,[z0,z1,z2,z23,z7,z4,z6]),(0,[z162,z1,z2,z197,z4,z5,z6]),(0,[z198,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z4,z99,z6]),(0,[z199,z1,z2,z7,z4,z5,z6])],[(0,[z98,z1,z2,z7,z4,z5,z6]),(0,[z200,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z201,z5,z6]),(0,[z1,z2,z7,z4,z5,z24,z17]),(0,[z1,z2,z7,z4,z150,z5,z17]),(0,[z1,z2,z42,z7,z4,z5,z17]),(0,[z1,z2,z21,z7,z4,z5,z24]),(0,[z1,z2,z7,z117,z4,z5,z69]),(0,[z71,z1,z2,z16,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z202,z6]),(0,[z1,z2,z203,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z182,z6]),(0,[z1,z2,z204,z7,z4,z5,z6])],[(0,[z1,z2,z7,z205,z4,z5,z6]),(0,[z206,z1,z2,z7,z4,z5,z6]),(0,[z207,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z83,z49,z6]),(1,[z1,z2,z208,z4,z5,z6]),(0,[z209,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z210,z7,z4,z5,z6]),(0,[z1,z2,z7,z211,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z212,z6])]],
   [[(0,[z1,z2,z213,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z214,z5,z6]),(0,[z1,z2,z120,z7,z102,z4,z6]),(1,[z1,z2,z7,z4,z215,z6]),(0,[z1,z2,z7,z4,z90,z156,z6]),(0,[z57,z1,z2,z4,z5,z6,z58])],[(0,[z1,z2,z7,z4,z5,z5,z6]),(0,[z177,z1,z2,z7,z4,z5,z24]),(0,[z71,z1,z2,z4,z97,z5,z6]),(0,[z1,z2,z7,z4,z216,z5,z6])],[(0,[z1,z2,z217,z7,z4,z5,z6]),(0,[z1,z2,z7,z218,z4,z5,z6]),(0,[z1,z39,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z24,z182]),(0,[z1,z2,z7,z4,z5,z6,z219]),(1,[z1,z30,z7,z4,z5,z86]),(0,[z0,z1,z2,z7,z4,z90,z6]),(0,[z1,z2,z20,z7,z4,z52,z6]),(0,[z220,z1,z2,z7,z4,z5,z6]),(0,[z1,z221,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z222,z5,z6]),(0,[z122,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z223,z7,z4,z5,z6]),(0,[z1,z2,z7,z102,z4,z5,z24]),(0,[z1,z2,z224,z7,z102,z4,z6]),(0,[z1,z2,z7,z117,z225,z5,z6]),(0,[z71,z1,z2,z20,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z113,z6]),(0,[z1,z2,z226,z227,z4,z5,z6])],[(0,[z98,z1,z2,z7,z4,z5,z228]),(0,[z111,z1,z2,z7,z229,z5,z6]),(0,[z230,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z231,z20,z7,z4,z6]),(0,[z57,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z232,z7,z4,z5,z6])],[],[(0,[z162,z2,z3,z7,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z5,z24]),(0,[z38,z1,z2,z7,z4,z5,z233]),(0,[z14,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z234]),(0,[z0,z1,z73,z2,z4,z5,z6]),(0,[z1,z2,z235,z7,z4,z5,z6]),(0,[z1,z236,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z237,z4,z5,z6]),(0,[z1,z2,z238,z20,z7,z4,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z6,z239]),(0,[z240,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z241,z4,z5,z6]),(0,[z242,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z243,z7,z4,z5,z6]),(0,[z1,z119,z2,z20,z7,z4,z6]),(0,[z0,z162,z1,z2,z7,z4,z6]),(0,[z162,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z7,z4,z244,z5,z6]),(0,[z1,z73,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z24,z245]),(0,[z1,z2,z7,z4,z5,z246,z6]),(0,[z247,z1,z2,z7,z4,z5,z6]),(0,[z57,z1,z2,z4,z150,z5,z6])],[(0,[z1,z2,z7,z248,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z249]),(0,[z1,z2,z7,z4,z156,z5,z17]),(0,[z1,z2,z7,z4,z90,z5,z24]),(0,[z1,z2,z7,z250,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z132]),(0,[z1,z2,z7,z4,z5,z52,z6])],[(0,[z1,z2,z7,z4,z4,z5,z6]),(0,[z82,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z7,z251,z4,z5,z17]),(0,[z1,z2,z7,z4,z252,z5,z6]),(0,[z1,z2,z20,z4,z150,z5,z6])],[(0,[z1,z2,z7,z4,z5,z253,z6]),(0,[z1,z2,z254,z7,z4,z5,z6]),(0,[z1,z2,z7,z255,z4,z5,z6]),(0,[z256,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z257,z5,z6])],[(0,[z1,z39,z23,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z258,z5,z6]),(0,[z1,z30,z2,z20,z7,z4,z6]),(0,[z1,z2,z259,z7,z4,z5,z6])],[(0,[z260,z1,z2,z7,z4,z5,z6]),(0,[z1,z26,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z261,z4,z5,z6]),(0,[z1,z2,z151,z7,z4,z97,z6])]],
   [[(0,[z1,z2,z65,z197,z4,z5,z6]),(0,[z1,z2,z7,z262,z4,z5,z6])],[(0,[z1,z2,z263,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z17]),(0,[z1,z2,z7,z4,z264,z5,z6]),(0,[z1,z2,z7,z4,z156,z6,z22]),(1,[z1,z2,z7,z265,z5,z6]),(0,[z1,z45,z2,z20,z7,z4,z6]),(0,[z1,z2,z16,z4,z150,z5,z6]),(0,[z1,z2,z20,z7,z7,z4,z6]),(0,[z266,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z267,z6]),(0,[z268,z1,z2,z7,z4,z5,z6])],[(0,[z1,z119,z2,z7,z4,z5,z17]),(0,[z162,z1,z2,z7,z4,z5,z17]),(0,[z1,z73,z2,z7,z4,z5,z17]),(1,[z1,z2,z7,z4,z191,z5]),(0,[z1,z2,z42,z7,z5,z6,z10])],[(0,[z194,z1,z2,z7,z4,z83,z6]),(0,[z1,z2,z269,z7,z4,z5,z6]),(0,[z1,z2,z270,z7,z4,z5,z6]),(0,[z1,z2,z7,z227,z4,z5,z6]),(0,[z271,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z272,z6])],[(0,[z273,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z23,z20,z7,z4,z6]),(0,[z274,z1,z2,z7,z4,z5,z6]),(0,[z1,z275,z2,z7,z4,z5,z6]),(0,[z82,z1,z2,z7,z4,z5,z17]),(0,[z57,z1,z30,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z32,z6]),(0,[z1,z2,z7,z225,z4,z5,z6]),(0,[z1,z2,z7,z4,z59,z5,z6])],[(0,[z1,z2,z7,z276,z4,z5,z6]),(0,[z194,z2,z7,z4,z124,z5,z6]),(0,[z14,z2,z7,z4,z5,z24,z6]),(0,[z1,z2,z7,z4,z5,z6,z277]),(0,[z1,z2,z7,z278,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z279]),(0,[z1,z2,z280,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z90,z135])],[(0,[z281,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z197,z4,z5,z6]),(0,[z38,z1,z2,z7,z4,z5,z6]),(0,[z1,z282,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z23,z7,z4,z27,z5,z6]),(0,[z1,z2,z7,z4,z283,z5,z6]),(0,[z1,z2,z7,z284,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z285,z6]),(0,[z1,z286,z2,z7,z4,z5,z6]),(1,[z1,z2,z120,z7,z4,z6]),(0,[z1,z2,z7,z287,z4,z5,z6])],[(0,[z1,z2,z288,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z83,z6]),(0,[z1,z45,z30,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z289,z5,z6])],[(0,[z1,z34,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z290,z6]),(0,[z1,z2,z7,z227,z116,z5,z6])],[(0,[z98,z2,z7,z197,z4,z5,z6]),(0,[z1,z2,z7,z4,z291,z5,z6]),(0,[z1,z2,z292,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z293,z17]),(0,[z1,z2,z7,z4,z5,z294,z17]),(0,[z1,z2,z238,z7,z4,z49,z6])],[(1,[z1,z2,z7,z4,z5,z6]),(0,[z295,z1,z2,z7,z4,z5,z6]),(1,[z1,z45,z7,z4,z5,z32]),(0,[z1,z45,z2,z21,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z182,z6]),(0,[z57,z1,z2,z7,z4,z5,z58])],[(0,[z1,z2,z7,z4,z55,z5,z24]),(0,[z1,z2,z7,z4,z5,z6,z245]),(0,[z1,z30,z2,z7,z4,z70,z6]),(0,[z1,z296,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z297,z6])],[(0,[z298,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z23,z7,z4,z5,z17]),(0,[z1,z299,z2,z7,z4,z5,z6]),(0,[z1,z73,z65,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z300]),(0,[z1,z2,z20,z7,z4,z90,z6]),(0,[z1,z2,z7,z4,z5,z6,z301])],[(0,[z302,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z303]),(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z4,z113,z6])]],
   [[(0,[z1,z2,z304,z7,z4,z5,z6]),(0,[z298,z119,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z305,z6]),(0,[z306,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z307,z6]),(0,[z1,z308,z2,z7,z4,z5,z17]),(0,[z29,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z20,z7,z4,z150,z6])],[(0,[z167,z1,z2,z66,z4,z5,z6]),(0,[z1,z2,z7,z161,z4,z5,z6]),(1,[z1,z2,z7,z4,z309,z6]),(1,[z1,z123,z7,z4,z5,z6]),(0,[z1,z310,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z311,z4,z5,z6])],[(0,[z1,z2,z7,z117,z284,z5,z6]),(0,[z1,z2,z7,z4,z76,z83,z6]),(0,[z15,z1,z2,z20,z7,z4,z6]),(0,[z111,z1,z7,z102,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z312,z6]),(0,[z1,z2,z7,z51,z5,z52,z6])],[(0,[z167,z1,z2,z7,z4,z80,z6]),(0,[z1,z2,z7,z313,z4,z5,z6]),(0,[z1,z314,z2,z7,z4,z5,z6]),(0,[z194,z1,z2,z7,z4,z5,z315]),(0,[z1,z2,z7,z4,z5,z6,z316]),(0,[z1,z2,z317,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z318,z5,z6])],[(0,[z1,z2,z7,z4,z319,z5,z6]),(1,[z1,z2,z7,z101,z4,z5])],[(1,[z1,z2,z7,z4,z5,z320]),(1,[z38,z2,z7,z284,z5,z6]),(0,[z1,z2,z62,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z49,z24]),(0,[z1,z2,z7,z4,z27,z5,z6])],[(0,[z122,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z321,z4,z5,z6]),(0,[z1,z2,z65,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z322,z5,z6]),(0,[z1,z323,z2,z7,z4,z5,z6])],[(0,[z324,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z17,z22]),(0,[z1,z2,z7,z4,z5,z6,z325]),(0,[z1,z326,z2,z7,z4,z156,z6]),(1,[z1,z2,z7,z4,z327,z6]),(0,[z328,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z329,z6]),(0,[z111,z1,z2,z20,z7,z4,z6]),(0,[z1,z26,z2,z7,z27,z5,z6]),(0,[z1,z2,z7,z330,z4,z5,z6]),(0,[z331,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z238,z7,z4,z6]),(0,[z1,z2,z7,z4,z90,z135,z6])],[(1,[z1,z2,z224,z7,z4,z6]),(0,[z332,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z333,z4,z5,z6]),(0,[z334,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z335,z6])],[(0,[z1,z336,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z116,z83,z6]),(0,[z1,z2,z7,z4,z5,z113,z24]),(0,[z1,z2,z20,z7,z117,z4,z6]),(0,[z1,z2,z337,z7,z4,z5,z6])],[(1,[z1,z2,z338,z4,z5,z6]),(0,[z2,z3,z7,z197,z4,z5,z6]),(0,[z339,z1,z2,z7,z4,z5,z6]),(0,[z15,z2,z7,z4,z5,z6,z17]),(0,[z1,z2,z7,z117,z4,z5,z24]),(0,[z340,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z341,z6]),(0,[z1,z2,z7,z4,z5,z342,z6]),(0,[z343,z1,z2,z7,z4,z5,z6]),(0,[z2,z7,z4,z124,z5,z83,z6]),(1,[z1,z2,z20,z7,z4,z24]),(0,[z344,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z345,z7,z4,z5,z6]),(0,[z1,z2,z346,z20,z7,z4,z6]),(0,[z1,z2,z7,z179,z4,z5,z6])],[(0,[z167,z1,z2,z20,z7,z4,z6]),(1,[z122,z2,z7,z99,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z347]),(0,[z1,z2,z348,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z349,z6])],[(0,[z1,z2,z7,z4,z5,z350,z6]),(0,[z351,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z352]),(0,[z1,z2,z7,z4,z353,z5,z6]),(0,[z1,z2,z7,z225,z27,z5,z6]),(0,[z1,z2,z7,z225,z4,z290,z6]),(0,[z0,z1,z2,z62,z7,z4,z6])],[(0,[z0,z1,z2,z7,z4,z6,z17]),(0,[z1,z65,z7,z102,z4,z5,z6]),(0,[z1,z2,z7,z354,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z355])]],
   [[(0,[z356,z1,z2,z7,z4,z5,z6]),(0,[z98,z1,z2,z7,z4,z5,z357]),(0,[z122,z1,z2,z321,z4,z5,z6])],[(0,[z1,z2,z358,z7,z4,z5,z6]),(0,[z111,z1,z2,z7,z4,z5,z17]),(0,[z1,z7,z4,z156,z5,z76,z6]),(0,[z1,z2,z20,z7,z4,z32,z6]),(0,[z1,z2,z7,z4,z5,z6,z109])],[(0,[z1,z326,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z359,z4,z5,z6]),(0,[z1,z2,z360,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z361,z5,z6]),(0,[z1,z362,z2,z7,z4,z5,z6])],[(0,[z298,z1,z2,z7,z4,z5,z363]),(0,[z364,z1,z2,z7,z4,z5,z6]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z177,z1,z326,z7,z4,z5,z6]),(0,[z1,z2,z62,z7,z51,z4,z5])],[],[(0,[z1,z2,z7,z4,z365,z5,z6]),(1,[z1,z2,z7,z4,z290,z6])],[(0,[z1,z2,z7,z4,z124,z49,z6]),(0,[z366,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z367])],[(0,[z0,z1,z2,z7,z4,z83,z6]),(0,[z1,z2,z7,z4,z5,z368,z17]),(0,[z1,z2,z7,z4,z5,z135,z17]),(1,[z1,z2,z270,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z369]),(0,[z370,z1,z2,z7,z4,z5,z6])]],
   [[(0,[z167,z1,z2,z7,z161,z5,z6]),(0,[z1,z2,z7,z4,z5,z371,z6]),(0,[z0,z1,z2,z7,z102,z4,z6]),(0,[z71,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z372,z6]),(0,[z0,z1,z2,z7,z4,z216,z6]),(0,[z1,z2,z20,z7,z4,z182,z6]),(0,[z1,z2,z42,z20,z7,z4,z6])],[(0,[z1,z2,z231,z7,z4,z5,z6]),(0,[z373,z1,z2,z7,z4,z5,z6]),(0,[z0,z194,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z229,z4,z5,z6]),(0,[z57,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z374,z6]),(0,[z1,z2,z7,z4,z5,z17,z145]),(0,[z1,z2,z7,z375,z4,z5,z6]),(0,[z1,z2,z7,z4,z376,z5,z6])],[(0,[z1,z326,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z76,z17]),(0,[z1,z26,z7,z4,z27,z5,z6]),(0,[z1,z45,z2,z7,z265,z5,z6]),(0,[z1,z2,z20,z7,z4,z5,z6]),(1,[z377,z1,z2,z4,z5,z6])],[(0,[z1,z2,z7,z208,z4,z5,z6]),(0,[z1,z378,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z32,z24]),(1,[z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z238,z7,z4,z5,z6])],[(0,[z1,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z338,z7,z4,z5,z6]),(0,[z1,z379,z2,z7,z4,z5,z6]),(0,[z122,z2,z7,z4,z99,z5,z6]),(0,[z1,z2,z7,z4,z5,z24,z86]),(0,[z1,z2,z380,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z381,z5,z6]),(0,[z382,z1,z2,z7,z4,z5,z6]),(0,[z1,z383,z2,z7,z4,z5,z6])],[(0,[z1,z2,z384,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z327,z97,z6]),(0,[z385,z1,z2,z7,z4,z5,z6])],[(0,[z167,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z386,z6]),(0,[z1,z2,z7,z4,z387,z5,z6]),(0,[z1,z2,z7,z4,z5,z388,z6]),(0,[z1,z2,z7,z5,z52,z6,z10])]],
   [[(0,[z1,z2,z7,z4,z389,z5,z6]),(0,[z1,z2,z390,z7,z4,z5,z6]),(0,[z1,z2,z16,z7,z4,z5,z6]),(0,[z391,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z392,z6]),(0,[z194,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z17,z10]),(1,[z1,z73,z65,z4,z5,z6]),(0,[z1,z2,z4,z5,z182,z6,z58]),(0,[z1,z7,z51,z50,z4,z5,z6]),(0,[z1,z2,z393,z7,z4,z5,z6])],[(0,[z167,z1,z2,z7,z137,z5,z6]),(0,[z394,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z16,z225,z5,z6]),(0,[z1,z2,z20,z7,z333,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z395]),(0,[z1,z2,z7,z4,z5,z6,z396])],[(0,[z29,z1,z2,z7,z4,z5,z6]),(0,[z397,z1,z2,z7,z4,z5,z6]),(0,[z98,z1,z2,z7,z4,z5,z24]),(1,[z1,z2,z7,z4,z5,z315]),(0,[z1,z2,z7,z4,z124,z76,z6]),(0,[z1,z2,z7,z398,z4,z5,z6]),(0,[z1,z2,z7,z399,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z400,z6]),(0,[z162,z1,z2,z7,z4,z309,z6]),(0,[z82,z1,z2,z7,z4,z5,z303]),(1,[z1,z401,z2,z7,z4,z5]),(0,[z177,z1,z2,z20,z7,z4,z6]),(0,[z1,z45,z7,z4,z5,z32,z6]),(0,[z402,z1,z2,z20,z7,z4,z6])],[(0,[z403,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z121,z6]),(0,[z1,z39,z2,z20,z7,z4,z6]),(1,[z0,z57,z1,z2,z4,z6]),(0,[z1,z2,z7,z404,z4,z5,z6])],[(0,[z1,z2,z405,z7,z4,z5,z6]),(0,[z1,z2,z406,z7,z4,z5,z6]),(0,[z1,z39,z2,z7,z117,z5,z6]),(0,[z1,z45,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z407]),(0,[z1,z2,z7,z4,z408,z5,z6]),(0,[z1,z2,z4,z5,z6,z134,z22])]],
   [[(0,[z298,z1,z119,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z24,z6]),(0,[z1,z2,z409,z7,z4,z5,z6]),(0,[z410,z1,z2,z7,z4,z5,z6])],[(0,[z411,z1,z2,z7,z4,z5,z6]),(1,[z1,z39,z7,z117,z5,z6]),(0,[z1,z2,z7,z412,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z413,z6]),(0,[z1,z2,z21,z7,z4,z5,z17]),(1,[z0,z1,z2,z4,z113,z6]),(0,[z1,z2,z7,z4,z5,z414,z6]),(0,[z1,z2,z7,z4,z5,z415,z6]),(0,[z1,z2,z7,z4,z5,z416,z6])],[(0,[z1,z2,z20,z7,z4,z6,z17]),(0,[z1,z2,z7,z4,z5,z24,z417]),(0,[z1,z2,z7,z418,z4,z5,z6]),(0,[z1,z2,z7,z419,z4,z5,z6]),(1,[z1,z2,z21,z7,z4,z22])],[(1,[z1,z2,z7,z4,z5,z371]),(0,[z1,z2,z7,z4,z5,z420,z17]),(1,[z1,z2,z7,z4,z6,z109])],[(0,[z177,z1,z2,z7,z4,z5,z17]),(0,[z1,z73,z2,z20,z7,z4,z6]),(0,[z1,z2,z421,z7,z4,z5,z6]),(0,[z1,z422,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z357]),(0,[z1,z39,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z17,z423]),(0,[z71,z1,z2,z7,z97,z5,z6]),(0,[z424,z0,z1,z2,z7,z4,z6])],[(0,[z1,z2,z7,z102,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z425,z6])]],
   [[(0,[z0,z1,z119,z2,z7,z4,z6]),(0,[z1,z2,z426,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z24,z58]),(0,[z1,z2,z7,z4,z5,z52,z24]),(0,[z1,z2,z7,z4,z5,z6,z86]),(0,[z1,z2,z427,z7,z4,z5,z6]),(0,[z428,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z429,z4,z5,z6]),(0,[z1,z2,z21,z7,z4,z6,z22])],[(0,[z430,z1,z2,z7,z4,z5,z6]),(0,[z111,z1,z2,z7,z214,z5,z6]),(0,[z1,z431,z2,z7,z4,z5,z6]),(0,[z1,z2,z432,z7,z4,z5,z6])],[(0,[z1,z433,z2,z7,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z5,z17]),(1,[z1,z2,z7,z4,z283,z6]),(0,[z1,z2,z7,z4,z5,z253,z24]),(0,[z0,z1,z45,z2,z7,z4,z6]),(0,[z434,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z151,z7,z4,z5,z6]),(0,[z435,z1,z2,z7,z4,z5,z6])],[(0,[z38,z1,z2,z7,z284,z5,z6]),(0,[z1,z2,z7,z4,z436,z5,z6]),(0,[z1,z2,z20,z7,z4,z83,z6]),(0,[z1,z437,z2,z7,z4,z5,z6]),(0,[z1,z438,z2,z7,z4,z5,z6]),(0,[z439,z1,z2,z7,z4,z5,z6])],[(0,[z440,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z99,z5,z6]),(0,[z1,z2,z441,z7,z4,z5,z6]),(0,[z1,z26,z2,z7,z4,z5,z24]),(0,[z1,z2,z20,z7,z102,z4,z6])],[(0,[z1,z2,z442,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z374,z6]),(0,[z443,z1,z2,z7,z4,z5,z6]),(0,[z71,z1,z2,z7,z225,z5,z6]),(0,[z1,z2,z7,z4,z116,z5,z6])],[(0,[z119,z2,z23,z7,z4,z5,z6]),(0,[z111,z1,z73,z7,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z86]),(0,[z1,z2,z16,z7,z97,z5,z6]),(0,[z1,z444,z2,z7,z4,z5,z6])],[(0,[z445,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z124,z5,z6]),(0,[z15,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z90,z5,z17]),(0,[z1,z2,z7,z446,z4,z5,z6]),(0,[z1,z2,z43,z7,z4,z5,z6]),(0,[z1,z2,z447,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z448,z6]),(0,[z1,z123,z2,z7,z4,z5,z6]),(0,[z1,z2,z449,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z450,z5,z6]),(0,[z1,z2,z7,z227,z4,z116,z6]),(0,[z1,z2,z7,z451,z4,z5,z6]),(0,[z1,z2,z452,z7,z4,z5,z6])],[(0,[z1,z2,z7,z227,z4,z5,z24]),(0,[z0,z1,z2,z7,z4,z156,z6]),(0,[z453,z1,z2,z7,z4,z5,z6]),(0,[z1,z45,z2,z7,z4,z5,z86]),(0,[z454,z1,z2,z7,z4,z5,z6]),(1,[z0,z1,z2,z16,z4,z6]),(0,[z1,z455,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z225,z4,z5,z24]),(0,[z1,z2,z456,z7,z4,z5,z6])],[(0,[z1,z2,z7,z66,z4,z5,z6]),(0,[z457,z1,z2,z7,z4,z5,z6]),(0,[z2,z7,z4,z5,z24,z6,z17]),(0,[z458,z1,z2,z7,z4,z5,z6]),(0,[z1,z326,z7,z4,z5,z76,z6]),(1,[z71,z1,z2,z97,z5,z6]),(0,[z0,z459,z1,z2,z7,z4,z6])],[(0,[z122,z1,z2,z7,z4,z283,z6]),(0,[z1,z30,z2,z21,z7,z4,z5])],[(0,[z1,z2,z7,z4,z5,z6,z460]),(0,[z1,z2,z16,z7,z225,z5,z6]),(0,[z1,z2,z20,z7,z461,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z462]),(0,[z1,z2,z7,z4,z463,z5,z6])],[(0,[z1,z2,z7,z4,z5,z357,z6]),(1,[z68,z1,z2,z7,z4,z6]),(0,[z1,z464,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z303,z6]),(0,[z1,z2,z7,z4,z5,z83,z24]),(0,[z1,z2,z7,z4,z5,z6,z417]),(0,[z1,z465,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z466,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z467])],[(0,[z122,z1,z2,z7,z4,z374,z6]),(0,[z38,z1,z2,z7,z99,z5,z6]),(0,[z1,z2,z7,z4,z5,z468,z6]),(0,[z1,z2,z7,z4,z93,z5,z6]),(0,[z1,z2,z62,z20,z7,z4,z6])]],
   [[(1,[z1,z2,z7,z4,z5,z469]),(0,[z82,z2,z7,z4,z5,z83,z6]),(0,[z1,z2,z7,z4,z470,z5,z6]),(0,[z1,z2,z7,z4,z471,z5,z6]),(0,[z472,z1,z2,z7,z4,z5,z6])],[(0,[z68,z1,z2,z7,z197,z4,z6]),(0,[z38,z2,z7,z284,z4,z5,z6]),(0,[z473,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z346,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z6,z474]),(0,[z1,z2,z7,z4,z475,z5,z6]),(0,[z476,z1,z2,z7,z4,z5,z6])],[(0,[z167,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z197,z4,z6]),(0,[z1,z2,z169,z7,z4,z5,z6]),(0,[z122,z1,z2,z7,z284,z5,z6]),(0,[z194,z82,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z191,z5,z76]),(0,[z1,z2,z7,z4,z477,z5,z6]),(0,[z1,z2,z7,z4,z5,z478,z6]),(0,[z1,z479,z2,z7,z4,z5,z6]),(0,[z1,z2,z480,z7,z4,z5,z6])],[(0,[z298,z1,z2,z7,z4,z5,z239]),(0,[z298,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z24,z481]),(0,[z1,z7,z4,z27,z5,z32,z6]),(1,[z0,z1,z2,z4,z182,z6]),(0,[z0,z1,z2,z7,z4,z116,z6]),(0,[z1,z2,z7,z4,z5,z6,z58])],[(0,[z0,z1,z2,z7,z4,z5,z24]),(0,[z482,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z483,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z484,z6])],[(1,[z1,z2,z7,z4,z5,z228]),(0,[z1,z2,z7,z4,z5,z6,z485]),(0,[z1,z2,z7,z4,z486,z5,z6]),(0,[z177,z1,z2,z7,z4,z76,z6]),(0,[z1,z2,z7,z4,z97,z5,z6]),(0,[z1,z487,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z488,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z489,z6]),(0,[z1,z73,z2,z7,z4,z215,z6]),(0,[z1,z2,z7,z4,z5,z490,z6]),(0,[z1,z2,z7,z51,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z17,z53]),(0,[z1,z2,z491,z7,z4,z5,z6]),(0,[z1,z39,z7,z117,z4,z5,z6])]],
   [[(0,[z1,z2,z492,z7,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z113,z6])],[(1,[z1,z2,z7,z4,z5,z493]),(0,[z1,z2,z7,z4,z5,z6,z494])],[(0,[z1,z2,z7,z99,z27,z5,z6]),(0,[z1,z2,z7,z495,z4,z5,z6]),(0,[z1,z2,z496,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z497,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z134]),(0,[z1,z2,z7,z498,z4,z5,z6])],[(0,[z167,z1,z2,z7,z4,z5,z320]),(0,[z122,z1,z2,z7,z4,z5,z24]),(0,[z499,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z500,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z501,z6]),(0,[z1,z2,z7,z502,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z90,z5]),(0,[z1,z2,z7,z4,z5,z6,z503])],[(0,[z1,z2,z7,z4,z309,z5,z6]),(0,[z504,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z62,z7,z4,z5,z182]),(0,[z1,z2,z7,z505,z4,z5,z6])],[(0,[z506,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z24,z6]),(0,[z1,z2,z7,z4,z215,z5,z6]),(0,[z1,z2,z7,z4,z5,z507,z6]),(0,[z1,z2,z7,z4,z150,z5,z6]),(0,[z1,z2,z42,z7,z4,z5,z6])],[(0,[z1,z508,z2,z7,z4,z5,z6]),(0,[z122,z1,z2,z7,z99,z5,z6]),(0,[z14,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z509,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z6,z86]),(0,[z57,z1,z45,z2,z7,z4,z5]),(0,[z1,z45,z2,z7,z4,z90,z5])],[(0,[z298,z1,z23,z7,z4,z5,z6]),(1,[z98,z2,z197,z4,z5,z6]),(0,[z1,z2,z7,z4,z90,z76,z6])]],
   [[(0,[z1,z2,z7,z510,z4,z5,z6]),(0,[z1,z2,z511,z7,z4,z97,z5]),(0,[z1,z2,z7,z4,z512,z5,z6]),(1,[z1,z2,z62,z4,z5,z182])],[(0,[z167,z1,z2,z338,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z49,z17]),(0,[z1,z2,z7,z4,z5,z341,z24]),(1,[z111,z1,z102,z4,z5,z6]),(0,[z111,z1,z2,z4,z150,z5,z6]),(0,[z424,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z117,z4,z5,z132]),(0,[z513,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z514,z5,z6])],[(0,[z1,z2,z7,z515,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z363,z6]),(0,[z1,z516,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z517]),(0,[z1,z2,z7,z4,z5,z187,z6]),(0,[z194,z1,z2,z7,z4,z124,z6]),(0,[z1,z2,z7,z518,z4,z5,z6]),(0,[z519,z1,z2,z7,z4,z5,z6])],[(0,[z122,z1,z2,z7,z4,z5,z493]),(0,[z1,z2,z7,z4,z5,z350,z24]),(0,[z1,z2,z7,z4,z5,z520,z6]),(0,[z428,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z521])],[(0,[z1,z2,z7,z4,z522,z5,z6]),(1,[z1,z2,z7,z4,z5,z363]),(0,[z1,z2,z7,z523,z4,z5,z6]),(0,[z1,z2,z7,z4,z524,z5,z6]),(0,[z1,z2,z7,z4,z525,z5,z6]),(0,[z1,z2,z7,z4,z118,z182,z6])],[(0,[z1,z2,z7,z4,z526,z5,z6]),(0,[z1,z2,z527,z7,z4,z5,z6]),(0,[z1,z528,z2,z7,z4,z5,z6]),(0,[z529,z1,z2,z7,z4,z5,z6]),(0,[z1,z326,z2,z20,z7,z4,z6]),(0,[z1,z2,z20,z7,z4,z156,z6]),(0,[z1,z2,z7,z4,z5,z530,z6]),(0,[z0,z1,z2,z348,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z531]),(0,[z1,z532,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z113,z17]),(0,[z1,z2,z7,z4,z166,z5,z6])],[(0,[z1,z2,z7,z533,z4,z5,z6]),(0,[z1,z2,z7,z117,z4,z5,z17]),(0,[z14,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z534,z4,z5,z6]),(0,[z535,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z69]),(0,[z1,z536,z2,z7,z4,z5,z6]),(0,[z537,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z62,z7,z4,z5,z58]),(0,[z1,z2,z7,z4,z118,z5,z6])]],
   [[(1,[z1,z442,z7,z4,z5,z6]),(1,[z1,z2,z20,z7,z4,z17]),(0,[z538,z1,z2,z7,z4,z5,z6])],[(0,[z98,z1,z2,z197,z4,z5,z6]),(0,[z539,z1,z2,z7,z4,z5,z6]),(0,[z1,z540,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z51,z4,z6]),(0,[z1,z541,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z542,z4,z5,z6]),(0,[z543,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z156,z5,z6])],[(0,[z1,z2,z7,z251,z4,z5,z6]),(0,[z1,z2,z270,z7,z4,z5,z76]),(0,[z1,z2,z7,z4,z5,z6,z544]),(0,[z1,z2,z545,z7,z4,z5,z6])],[(0,[z1,z2,z7,z546,z4,z5,z6])],[(0,[z71,z1,z2,z7,z4,z5,z24]),(0,[z111,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z27,z6])],[(0,[z547,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z197,z4,z6]),(0,[z548,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z284,z4,z6]),(0,[z1,z2,z7,z4,z549,z5,z6]),(0,[z373,z1,z2,z7,z4,z5,z24]),(0,[z57,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z550,z5,z6]),(0,[z1,z2,z7,z225,z4,z174,z6]),(0,[z1,z2,z180,z20,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z80,z6]),(0,[z1,z2,z146,z7,z4,z5,z17]),(0,[z111,z1,z2,z102,z4,z5,z6]),(0,[z1,z2,z7,z551,z4,z5,z6]),(1,[z1,z326,z7,z4,z76,z6]),(0,[z1,z2,z20,z7,z4,z116,z6]),(0,[z1,z2,z552,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z553,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z554,z6]),(0,[z1,z2,z7,z4,z5,z6,z6]),(0,[z1,z2,z20,z7,z4,z5,z24])],[(0,[z194,z1,z2,z7,z4,z5,z555]),(1,[z0,z1,z2,z7,z4,z24]),(0,[z0,z1,z26,z2,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z6,z58]),(0,[z0,z1,z2,z4,z5,z182,z6]),(0,[z0,z1,z2,z7,z4,z135,z6]),(0,[z556,z1,z2,z7,z4,z5,z6])],[(0,[z1,z119,z2,z7,z4,z5,z6]),(0,[z162,z1,z2,z7,z4,z5,z6]),(0,[z122,z1,z442,z7,z4,z5,z6]),(0,[z1,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z380,z7,z4,z5,z24]),(0,[z1,z73,z2,z7,z4,z5,z6]),(0,[z1,z557,z2,z7,z4,z5,z6]),(0,[z1,z558,z2,z20,z7,z4,z6]),(0,[z1,z2,z7,z559,z4,z5,z6]),(0,[z560,z1,z2,z7,z4,z5,z6])],[(0,[z561,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z562,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z563,z5,z6])],[(0,[z82,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z564,z6]),(0,[z1,z2,z21,z20,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z565]),(0,[z1,z566,z2,z7,z4,z5,z6])],[(0,[z567,z1,z2,z7,z4,z5,z6]),(0,[z173,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z17,z176]),(0,[z1,z2,z16,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z24,z22])],[(0,[z1,z2,z7,z4,z5,z6,z228]),(1,[z1,z2,z7,z4,z5,z129]),(0,[z1,z2,z7,z4,z5,z6,z568]),(0,[z1,z2,z7,z4,z5,z6,z474]),(0,[z1,z2,z569,z7,z4,z5,z6])],[(1,[z1,z2,z217,z7,z4,z6]),(0,[z1,z2,z7,z284,z4,z5,z6]),(0,[z0,z1,z39,z2,z7,z4,z6]),(0,[z1,z2,z7,z265,z4,z5,z6]),(0,[z1,z570,z2,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z571,z5,z6]),(0,[z1,z2,z217,z7,z197,z4,z6]),(0,[z1,z2,z7,z4,z5,z32,z17]),(0,[z29,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z398,z4,z5,z24]),(0,[z1,z2,z7,z572,z4,z5,z6]),(0,[z1,z2,z573,z7,z4,z5,z6])],[(0,[z574,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z320]),(0,[z1,z2,z184,z7,z4,z5,z17]),(0,[z111,z1,z2,z65,z4,z5,z6]),(0,[z575,z0,z1,z2,z7,z4,z6]),(0,[z576,z0,z1,z2,z7,z4,z6])],[(0,[z1,z2,z3,z4,z97,z5,z6]),(0,[z1,z2,z7,z4,z5,z293,z6]),(0,[z1,z2,z7,z4,z5,z294,z6]),(0,[z1,z2,z20,z7,z4,z6,z86]),(0,[z1,z2,z7,z4,z577,z5,z6])],[(0,[z1,z578,z2,z7,z4,z5,z6]),(0,[z1,z45,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z579,z6]),(0,[z0,z57,z1,z2,z7,z4,z6]),(0,[z1,z2,z226,z7,z4,z5,z6])],[(0,[z1,z2,z3,z20,z7,z4,z6]),(0,[z1,z580,z2,z7,z4,z5,z6])],[(0,[z1,z2,z23,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z581,z5,z6]),(0,[z194,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z582,z6]),(0,[z1,z2,z7,z4,z5,z6,z583]),(0,[z1,z2,z21,z7,z4,z5,z135])],[],[(0,[z98,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z517,z6]),(0,[z1,z2,z7,z4,z5,z555,z6]),(0,[z1,z308,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z182,z17]),(0,[z1,z2,z584,z7,z4,z5,z6]),(0,[z1,z2,z4,z150,z5,z113,z6]),(0,[z585,z1,z2,z20,z7,z4,z6])]],
   [[(0,[z1,z2,z7,z586,z4,z5,z6]),(0,[z240,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z238,z7,z227,z5,z6])],[(0,[z1,z2,z7,z587,z4,z5,z6]),(0,[z1,z2,z7,z4,z588,z5,z6]),(0,[z1,z2,z7,z4,z5,z589,z6])],[(0,[z167,z1,z2,z7,z4,z5,z371]),(0,[z0,z298,z1,z2,z7,z4,z6]),(0,[z1,z2,z3,z4,z150,z5,z6]),(0,[z1,z2,z7,z4,z156,z83,z6]),(0,[z590,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z591])],[(0,[z592,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z593,z5,z6]),(0,[z594,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z166,z5]),(0,[z595,z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z596,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z597])],[(0,[z1,z2,z7,z4,z598,z5,z6]),(0,[z1,z2,z62,z7,z4,z5,z6]),(0,[z1,z2,z599,z7,z4,z5,z6])],[(0,[z1,z600,z2,z7,z4,z5,z6]),(0,[z162,z1,z2,z7,z4,z5,z517]),(0,[z0,z1,z2,z7,z4,z124,z6]),(0,[z1,z2,z7,z4,z5,z24,z601]),(0,[z1,z2,z65,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z602,z6]),(0,[z1,z2,z20,z7,z51,z4,z6])],[(0,[z1,z73,z2,z4,z150,z5,z6]),(0,[z1,z2,z603,z7,z4,z5,z6]),(0,[z1,z326,z2,z7,z4,z76,z6]),(0,[z1,z2,z4,z93,z5,z76,z6]),(0,[z0,z1,z2,z7,z227,z4,z6]),(1,[z1,z2,z7,z4,z6,z544])],[(0,[z1,z30,z2,z62,z7,z4,z5]),(0,[z1,z2,z20,z7,z4,z6,z462])]],
   [[(0,[z1,z2,z7,z4,z604,z5,z6]),(0,[z1,z2,z7,z4,z5,z605,z6]),(1,[z15,z2,z7,z4,z5,z17]),(0,[z1,z26,z2,z7,z117,z5,z6]),(0,[z1,z2,z7,z27,z5,z52,z6]),(0,[z1,z7,z4,z5,z32,z6,z86]),(0,[z1,z2,z7,z606,z4,z5,z6]),(0,[z1,z2,z7,z51,z4,z5,z10]),(0,[z1,z2,z7,z4,z5,z6,z22])],[(0,[z1,z2,z7,z4,z99,z5,z24]),(0,[z1,z2,z7,z4,z607,z5,z6]),(0,[z1,z2,z441,z7,z4,z5,z24]),(0,[z1,z2,z20,z7,z4,z27,z6]),(0,[z177,z0,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z97,z6]),(0,[z1,z2,z7,z461,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z608])],[(0,[z0,z1,z2,z197,z4,z5,z6]),(0,[z537,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z284,z4,z6]),(0,[z1,z2,z130,z7,z4,z5,z6]),(0,[z1,z2,z91,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z116,z5,z24]),(0,[z1,z609,z2,z7,z4,z5,z6]),(0,[z1,z610,z2,z7,z4,z5,z6]),(0,[z1,z45,z2,z62,z7,z4,z5]),(1,[z1,z541,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z90,z5,z135])],[(0,[z1,z2,z7,z611,z4,z5,z6]),(0,[z612,z1,z2,z7,z4,z5,z6]),(0,[z1,z401,z2,z7,z4,z5,z6]),(0,[z1,z45,z2,z7,z514,z5,z6]),(0,[z1,z2,z7,z613,z4,z5,z6]),(0,[z11,z1,z2,z20,z7,z4,z6])],[(0,[z1,z2,z7,z7,z4,z5,z6]),(0,[z82,z1,z2,z7,z4,z83,z6]),(0,[z194,z1,z2,z208,z4,z5,z6]),(0,[z1,z2,z7,z4,z124,z5,z24]),(0,[z15,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z52,z17]),(0,[z1,z2,z7,z4,z5,z6,z614])],[(0,[z0,z1,z326,z2,z7,z4,z6]),(0,[z1,z2,z20,z7,z4,z6,z58]),(0,[z1,z2,z20,z7,z4,z135,z6]),(0,[z1,z2,z7,z4,z5,z6,z615])],[(0,[z38,z1,z2,z7,z4,z5,z469]),(1,[z1,z2,z238,z7,z49,z6])],[(0,[z1,z2,z7,z197,z4,z5,z24]),(0,[z38,z1,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z24,z10]),(0,[z1,z2,z7,z4,z5,z616,z6])]],
   [[(0,[z1,z2,z7,z284,z27,z5,z6]),(0,[z1,z2,z7,z4,z5,z17,z17]),(0,[z1,z26,z2,z7,z4,z5,z17]),(0,[z111,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z617,z7,z4,z5,z6])],[(0,[z1,z618,z2,z7,z4,z5,z6]),(1,[z1,z2,z254,z4,z5,z6]),(1,[z1,z2,z7,z4,z5,z555]),(0,[z1,z2,z7,z4,z76,z6,z22]),(0,[z619,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z620])],[(0,[z1,z2,z7,z621,z4,z5,z6]),(0,[z1,z2,z7,z117,z5,z52,z6]),(0,[z0,z1,z2,z7,z225,z4,z6]),(0,[z1,z2,z7,z4,z5,z78,z6]),(0,[z1,z2,z7,z4,z5,z6,z622]),(0,[z1,z2,z7,z4,z623,z5,z6]),(0,[z624,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z625,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z233,z6]),(0,[z0,z1,z2,z7,z572,z4,z6]),(0,[z1,z541,z7,z51,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z239]),(0,[z1,z626,z2,z7,z4,z5,z6]),(0,[z1,z73,z2,z102,z4,z5,z6]),(1,[z177,z1,z7,z4,z156,z6]),(0,[z1,z2,z7,z4,z514,z5,z6]),(0,[z1,z2,z7,z4,z182,z6,z544]),(0,[z1,z2,z42,z7,z51,z5,z6])],[(0,[z1,z2,z7,z227,z4,z5,z17]),(0,[z1,z2,z7,z4,z48,z5,z6]),(0,[z0,z1,z2,z4,z97,z5,z6]),(0,[z567,z0,z1,z2,z7,z4,z6])],[(0,[z298,z1,z2,z20,z7,z4,z6]),(0,[z0,z1,z2,z3,z7,z4,z6]),(0,[z1,z2,z7,z321,z4,z5,z6]),(0,[z1,z2,z7,z225,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z368,z6]),(0,[z1,z627,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z628,z6]),(0,[z1,z2,z7,z4,z5,z629,z6]),(0,[z1,z2,z7,z116,z5,z49,z6]),(0,[z1,z2,z7,z4,z5,z135,z6])],[(0,[z167,z1,z2,z7,z4,z5,z24]),(1,[z1,z2,z7,z4,z5,z249]),(0,[z1,z2,z7,z4,z5,z630,z6]),(0,[z1,z2,z7,z4,z5,z6,z315]),(0,[z1,z2,z20,z7,z4,z24,z6]),(0,[z111,z0,z1,z2,z4,z5,z6]),(0,[z1,z2,z224,z7,z4,z5,z6]),(0,[z631,z1,z2,z7,z4,z5,z6]),(0,[z1,z632,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z20,z7,z4,z6])]],
   [[(0,[z167,z298,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z197,z4,z5,z17]),(0,[z38,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z6,z601]),(0,[z1,z7,z117,z4,z27,z5,z6]),(1,[z75,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z20,z4,z6]),(0,[z1,z2,z4,z150,z5,z182,z6]),(0,[z1,z2,z7,z4,z5,z6,z633]),(0,[z377,z1,z2,z4,z5,z6,z22])],[(0,[z634,z1,z2,z7,z4,z5,z6]),(0,[z635,z1,z2,z7,z4,z5,z6]),(1,[z0,z1,z2,z197,z4,z6]),(0,[z1,z2,z7,z4,z636,z5,z6]),(0,[z1,z2,z7,z4,z637,z5,z6]),(0,[z1,z2,z7,z638,z4,z5,z6]),(0,[z1,z2,z639,z7,z4,z5,z6]),(0,[z1,z33,z2,z7,z4,z5,z6]),(1,[z1,z2,z226,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z83,z17]),(0,[z1,z2,z7,z4,z97,z5,z24]),(0,[z1,z326,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z76,z6]),(0,[z1,z640,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z641])],[(0,[z642,z1,z2,z7,z4,z5,z6]),(0,[z122,z1,z2,z254,z4,z5,z6]),(0,[z1,z2,z7,z51,z4,z5,z24]),(0,[z1,z73,z2,z7,z4,z121,z6]),(0,[z1,z643,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z644,z5,z6]),(0,[z1,z2,z7,z4,z645,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z646]),(0,[z575,z1,z2,z7,z4,z5,z6]),(0,[z576,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z647,z5,z6]),(0,[z377,z1,z2,z7,z4,z5,z6])],[(1,[z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z27,z5,z24]),(0,[z1,z2,z7,z4,z5,z6,z648]),(0,[z1,z2,z7,z4,z5,z649,z6])],[(0,[z1,z119,z7,z4,z27,z5,z6]),(0,[z650,z1,z2,z7,z4,z5,z6]),(0,[z1,z73,z2,z65,z4,z5,z6])],[(0,[z298,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z651,z7,z4,z5,z6]),(0,[z1,z652,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z653,z6]),(0,[z1,z2,z7,z4,z5,z654,z6])]],
   [[(0,[z0,z1,z2,z7,z4,z5,z17]),(1,[z1,z2,z7,z4,z48,z6]),(0,[z1,z2,z7,z4,z5,z6,z655]),(0,[z1,z2,z7,z227,z4,z49,z6])],[(0,[z1,z2,z197,z4,z97,z5,z6]),(0,[z1,z2,z20,z7,z4,z124,z6]),(0,[z14,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z511,z7,z4,z5,z6])],[(0,[z167,z2,z23,z7,z4,z5,z6]),(0,[z0,z82,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z24,z24]),(0,[z1,z30,z7,z4,z27,z5,z6]),(1,[z1,z2,z511,z7,z4,z5]),(0,[z0,z1,z2,z7,z7,z4,z6]),(0,[z1,z2,z337,z20,z7,z4,z6]),(0,[z1,z2,z20,z7,z227,z4,z6]),(0,[z1,z2,z7,z4,z5,z6,z10]),(0,[z1,z2,z7,z4,z135,z6,z22])],[(0,[z167,z1,z23,z7,z4,z5,z6]),(0,[z1,z26,z39,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z163,z6]),(0,[z1,z378,z2,z7,z4,z5,z6]),(0,[z656,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z657,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z52]),(1,[z1,z2,z7,z227,z116,z6])],[(1,[z1,z2,z7,z4,z5,z413]),(0,[z1,z2,z20,z7,z4,z97,z6]),(0,[z0,z57,z1,z2,z4,z5,z6]),(0,[z57,z1,z2,z62,z4,z5,z6])],[(0,[z658,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z659,z5,z6]),(0,[z1,z2,z660,z7,z4,z5,z6]),(0,[z1,z2,z7,z661,z4,z5,z6]),(0,[z1,z2,z7,z4,z27,z5,z17]),(0,[z1,z401,z2,z7,z102,z4,z5]),(0,[z0,z1,z30,z2,z7,z4,z6]),(0,[z0,z1,z662,z2,z7,z4,z6]),(0,[z595,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z6,z22])],[(0,[z122,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z663,z5,z6]),(0,[z1,z45,z2,z7,z4,z5,z52]),(0,[z0,z1,z2,z7,z4,z77,z6]),(0,[z1,z558,z2,z7,z4,z5,z6])]],
   [[(0,[z664,z1,z2,z7,z4,z5,z6]),(0,[z1,z30,z2,z7,z4,z5,z10]),(0,[z459,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z665,z6]),(0,[z666,z1,z2,z7,z4,z5,z6])],[(0,[z1,z2,z197,z4,z150,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z481]),(0,[z1,z2,z7,z667,z4,z5,z6]),(0,[z1,z2,z16,z225,z4,z5,z6]),(0,[z1,z2,z43,z7,z4,z6,z58]),(0,[z1,z2,z21,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z6,z668]),(0,[z1,z2,z7,z4,z5,z669,z6])],[(0,[z1,z2,z16,z197,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z420,z6]),(0,[z1,z39,z7,z4,z5,z32,z6]),(0,[z1,z45,z2,z7,z4,z5,z10]),(0,[z0,z1,z2,z16,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z49,z6])],[(0,[z98,z162,z2,z7,z4,z5,z6]),(0,[z402,z1,z2,z7,z4,z5,z6]),(1,[z0,z1,z73,z2,z4,z6]),(0,[z177,z1,z2,z7,z4,z5,z6])],[(1,[z167,z23,z7,z4,z5,z6]),(0,[z1,z2,z670,z7,z4,z5,z6]),(0,[z1,z39,z2,z7,z4,z5,z6]),(0,[z1,z2,z225,z4,z97,z5,z6]),(0,[z165,z1,z2,z20,z7,z4,z6])],[(0,[z1,z2,z7,z102,z4,z5,z6]),(0,[z1,z2,z20,z7,z225,z4,z6])],[(0,[z122,z1,z2,z7,z4,z5,z413]),(0,[z1,z2,z7,z4,z5,z671,z6]),(0,[z1,z2,z7,z4,z5,z6,z423]),(0,[z1,z2,z7,z4,z353,z5,z17]),(0,[z1,z2,z7,z4,z156,z5,z24]),(0,[z672,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z20,z7,z4,z512,z6])]],
   [[],[(0,[z1,z2,z3,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z150,z6]),(0,[z1,z2,z42,z62,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z6,z673]),(0,[z1,z2,z7,z4,z5,z674,z6]),(0,[z1,z2,z675,z7,z4,z5,z6])],[(1,[z194,z2,z7,z4,z124,z6]),(0,[z1,z2,z7,z4,z5,z676,z6]),(0,[z1,z2,z677,z7,z4,z5,z6])],[(0,[z1,z2,z678,z7,z4,z5,z6]),(1,[z1,z2,z7,z229,z5,z6]),(0,[z1,z2,z20,z20,z7,z4,z6]),(0,[z1,z2,z238,z7,z4,z116,z6])],[(0,[z2,z7,z284,z4,z99,z5,z6]),(0,[z1,z2,z7,z4,z5,z6,z469]),(0,[z1,z2,z238,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z679,z6]),(0,[z1,z2,z7,z4,z680,z5,z6]),(0,[z1,z2,z7,z4,z327,z5,z6]),(0,[z1,z662,z2,z7,z4,z5,z6]),(0,[z585,z1,z2,z7,z4,z5,z6]),(1,[z1,z2,z7,z51,z5,z52]),(0,[z1,z2,z7,z4,z5,z681,z6])],[(0,[z1,z2,z7,z4,z682,z5,z6]),(0,[z1,z2,z7,z683,z4,z5,z6])],[(0,[z1,z684,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z90,z5,z6])],[(0,[z1,z119,z2,z7,z4,z5,z24]),(0,[z1,z2,z197,z102,z4,z5,z6]),(0,[z1,z2,z7,z685,z4,z5,z6]),(0,[z162,z1,z2,z7,z4,z5,z24]),(0,[z194,z1,z2,z20,z7,z4,z6]),(0,[z1,z2,z7,z101,z4,z5,z6])]],
   [[(1,[z1,z2,z7,z4,z5,z233]),(0,[z686,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z687,z6]),(0,[z688,z1,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z76,z6]),(0,[z1,z2,z16,z20,z7,z4,z6]),(1,[z1,z2,z7,z4,z174,z6]),(0,[z1,z2,z7,z4,z5,z689,z6]),(0,[z1,z2,z227,z4,z59,z5,z6])],[(0,[z98,z1,z2,z20,z7,z4,z6]),(0,[z82,z1,z2,z7,z4,z5,z24]),(0,[z71,z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z42,z7,z27,z5,z6]),(0,[z1,z2,z690,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z691,z6]),(0,[z1,z2,z7,z4,z5,z692,z6])],[(0,[z162,z1,z2,z7,z4,z5,z249]),(0,[z194,z1,z2,z130,z4,z5,z6]),(0,[z57,z1,z2,z7,z4,z5,z17]),(0,[z693,z1,z2,z7,z4,z5,z6]),(0,[z1,z694,z2,z7,z4,z5,z6]),(0,[z695,z1,z2,z7,z4,z5,z6])],[(0,[z696,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z697,z5,z6]),(0,[z1,z2,z7,z4,z116,z124,z6]),(0,[z1,z30,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z698,z6]),(0,[z0,z1,z2,z7,z117,z4,z6]),(0,[z29,z1,z2,z20,z7,z4,z6])],[(0,[z699,z1,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z284,z4,z5,z24]),(0,[z1,z2,z20,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z700,z6])],[(0,[z1,z2,z7,z4,z5,z6,z493]),(0,[z1,z2,z7,z4,z701,z5,z6]),(1,[z0,z1,z2,z7,z4,z17]),(0,[z1,z2,z238,z7,z4,z5,z17]),(1,[z1,z2,z7,z214,z5,z6]),(0,[z1,z2,z7,z4,z702,z5,z6]),(0,[z1,z2,z238,z7,z5,z49,z6])],[(1,[z162,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z4,z703,z5,z6]),(0,[z1,z1,z2,z7,z4,z5,z17]),(0,[z1,z379,z2,z7,z4,z5,z17]),(0,[z75,z1,z2,z7,z4,z5,z6]),(0,[z650,z0,z1,z2,z7,z4,z6]),(0,[z57,z1,z2,z7,z4,z5,z182])],[(0,[z167,z1,z119,z7,z4,z5,z6]),(1,[z298,z119,z7,z4,z5,z6]),(1,[z1,z2,z7,z4,z163,z6]),(0,[z1,z2,z704,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z705,z6]),(0,[z1,z2,z7,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z338,z4,z80,z6]),(0,[z1,z2,z7,z707,z4,z5]),(0,[z1,z2,z7,z4,z708,z6]),(0,[z1,z2,z7,z4,z6,z709])],[(0,[z1,z2,z7,z4,z710,z6]),(0,[z0,z1,z2,z7,z161,z6]),(0,[z167,z23,z7,z4,z5,z371]),(0,[z2,z7,z4,z376,z5,z17]),(0,[z1,z2,z511,z7,z27,z5])],[(0,[z1,z2,z254,z4,z5,z493]),(0,[z1,z2,z7,z4,z711,z6]),(0,[z570,z2,z7,z4,z5,z24]),(0,[z0,z57,z1,z45,z2,z4])],[],[(0,[z1,z2,z7,z4,z5,z17]),(0,[z1,z2,z712,z7,z4,z6]),(0,[z0,z1,z54,z2,z4,z6]),(0,[z1,z2,z7,z713,z5,z6]),(0,[z1,z2,z7,z4,z135,z714])],[(0,[z1,z2,z7,z715,z4,z5]),(0,[z334,z2,z7,z4,z5,z24]),(0,[z1,z2,z224,z7,z101,z4]),(0,[z1,z2,z337,z7,z461,z6])],[(0,[z1,z2,z7,z4,z5,z716]),(0,[z0,z1,z2,z172,z4,z6]),(0,[z2,z7,z559,z4,z5,z17]),(0,[z2,z7,z4,z5,z717,z6])],[],[(0,[z718,z1,z2,z7,z4,z6]),(0,[z0,z459,z2,z7,z4,z17])],[(0,[z1,z2,z7,z4,z48,z24]),(0,[z0,z1,z2,z7,z51,z52]),(0,[z1,z558,z346,z7,z4,z6])],[(0,[z1,z2,z7,z4,z719,z5]),(0,[z1,z2,z7,z51,z5,z720])],[(0,[z98,z2,z197,z4,z5,z24]),(0,[z0,z1,z2,z276,z4,z6]),(0,[z1,z721,z7,z4,z5,z17])],[(0,[z1,z2,z7,z4,z5,z413]),(0,[z1,z2,z7,z4,z722,z17]),(0,[z2,z7,z404,z4,z5,z17]),(0,[z0,z1,z2,z226,z4,z6]),(0,[z1,z2,z7,z4,z723,z6])],[(0,[z1,z2,z20,z321,z4,z6])],[(0,[z1,z2,z321,z4,z5,z17]),(0,[z0,z1,z2,z7,z229,z6]),(0,[z1,z73,z2,z724,z4,z6]),(0,[z1,z7,z50,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z725])],[(0,[z1,z2,z726,z7,z4,z17]),(0,[z1,z2,z62,z4,z5,z420]),(0,[z1,z2,z7,z4,z5,z727]),(0,[z57,z1,z2,z4,z5,z474])]],
   [[(0,[z1,z728,z2,z7,z4,z5]),(0,[z220,z2,z7,z4,z124,z6]),(0,[z1,z326,z7,z4,z729,z6])],[(0,[z0,z1,z2,z4,z605,z6])],[(0,[z1,z730,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z731])],[(0,[z1,z2,z120,z3,z4,z6]),(0,[z718,z1,z2,z254,z4,z6]),(0,[z459,z2,z7,z4,z5,z17]),(0,[z1,z56,z7,z27,z5,z6]),(0,[z0,z732,z2,z7,z4,z6]),(0,[z0,z1,z2,z451,z4,z6]),(0,[z1,z541,z7,z51,z5,z52])],[(0,[z1,z2,z7,z4,z5,z733]),(0,[z0,z1,z2,z269,z4,z6]),(0,[z1,z2,z7,z4,z5,z734]),(0,[z1,z2,z511,z7,z4,z327])],[(0,[z1,z2,z338,z161,z5,z6]),(0,[z1,z2,z7,z735,z5,z6]),(0,[z0,z1,z2,z7,z514,z6])],[(0,[z1,z2,z321,z4,z5,z413]),(0,[z1,z2,z7,z736,z4,z5]),(0,[z1,z2,z737,z4,z5,z6]),(0,[z1,z30,z7,z4,z5,z86]),(0,[z428,z1,z2,z7,z216,z6])],[(0,[z0,z1,z2,z4,z436,z6]),(0,[z173,z1,z2,z4,z5,z145]),(0,[z1,z738,z7,z4,z5,z24]),(0,[z1,z2,z7,z739,z5,z6]),(0,[z1,z2,z740,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z741]),(0,[z0,z1,z2,z7,z4,z742])],[(0,[z1,z2,z7,z4,z5,z743]),(0,[z1,z2,z7,z4,z5,z744]),(0,[z0,z745,z2,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z746]),(0,[z1,z7,z747,z4,z5,z6])],[(0,[z0,z1,z2,z217,z4,z6]),(0,[z1,z65,z748,z4,z5,z6])],[(0,[z1,z2,z338,z4,z105,z6]),(0,[z1,z326,z7,z4,z76,z24])],[(0,[z1,z442,z7,z4,z5,z493]),(0,[z1,z7,z4,z5,z17,z749]),(0,[z1,z2,z7,z51,z5,z293]),(0,[z111,z0,z1,z662,z4,z6]),(0,[z1,z73,z2,z120,z4,z6]),(0,[z1,z2,z7,z4,z5,z750])],[(0,[z1,z2,z7,z4,z5,z751]),(0,[z1,z2,z7,z4,z290,z17])],[],[(0,[z1,z2,z66,z4,z5,z371]),(0,[z1,z2,z338,z137,z5,z6]),(0,[z1,z2,z7,z4,z5,z233]),(0,[z1,z45,z7,z4,z126,z5]),(0,[z1,z2,z225,z752,z5,z6])]],
   [[(0,[z1,z2,z753,z4,z5,z6]),(0,[z1,z2,z754,z7,z4,z6]),(0,[z0,z2,z7,z4,z24,z17]),(0,[z1,z2,z184,z7,z4,z423])],[(0,[z1,z2,z7,z4,z17,z755]),(0,[z1,z756,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z757]),(0,[z758,z1,z2,z4,z5,z6]),(0,[z1,z383,z7,z117,z5,z6]),(0,[z1,z2,z4,z759,z97,z6])],[(0,[z1,z2,z7,z4,z760,z6]),(0,[z1,z2,z761,z4,z5,z6]),(0,[z377,z1,z2,z4,z5,z17])],[(0,[z1,z2,z7,z4,z5,z762]),(0,[z1,z2,z763,z4,z5,z6]),(0,[z1,z2,z764,z4,z5,z6]),(0,[z2,z7,z4,z5,z17,z622])],[(0,[z1,z2,z7,z4,z5,z765]),(0,[z465,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z766,z6]),(0,[z1,z2,z7,z265,z5,z6]),(0,[z1,z45,z7,z265,z5,z32])],[(0,[z298,z119,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z767,z6]),(0,[z1,z2,z7,z4,z163,z6])],[(0,[z1,z34,z7,z4,z5,z601])],[(0,[z1,z2,z7,z4,z5,z768]),(0,[z1,z769,z7,z4,z5,z6]),(0,[z0,z1,z2,z4,z653,z6]),(0,[z0,z1,z2,z4,z654,z6])],[(0,[z0,z1,z2,z7,z137,z6]),(0,[z1,z2,z770,z7,z4,z6]),(0,[z771,z2,z7,z4,z5,z6])],[(0,[z0,z36,z1,z2,z4,z6]),(0,[z1,z2,z7,z4,z90,z135]),(1,[z1,z2,z7,z4,z714])],[(0,[z0,z1,z2,z214,z5,z6])],[(0,[z111,z1,z102,z229,z5,z6]),(0,[z1,z772,z7,z4,z5,z6]),(0,[z165,z1,z7,z179,z4,z6])],[(0,[z1,z2,z4,z773,z5,z6]),(0,[z0,z1,z442,z7,z4,z6]),(0,[z476,z2,z7,z4,z83,z6]),(0,[z0,z57,z1,z2,z4,z17]),(0,[z1,z2,z7,z399,z5,z52]),(0,[z1,z2,z7,z4,z774,z6])],[(0,[z1,z2,z7,z4,z775,z6]),(0,[z1,z2,z776,z7,z4,z5])],[(0,[z1,z2,z43,z7,z4,z24]),(0,[z1,z2,z7,z4,z777,z6]),(0,[z0,z1,z2,z7,z265,z6]),(0,[z1,z2,z7,z4,z5,z778])]],
   [[(0,[z1,z2,z7,z4,z5,z779]),(0,[z1,z2,z380,z4,z5,z182]),(0,[z1,z2,z7,z780,z5,z6]),(0,[z1,z2,z781,z7,z4,z6]),(0,[z1,z45,z7,z4,z5,z32])],[(0,[z1,z782,z7,z4,z5,z6]),(0,[z1,z2,z783,z4,z5,z6]),(0,[z0,z57,z1,z2,z4,z182]),(1,[z1,z2,z4,z784,z6]),(0,[z1,z2,z20,z4,z784,z6])],[],[(0,[z1,z2,z7,z4,z5,z303]),(0,[z1,z2,z20,z4,z93,z6])],[(0,[z15,z2,z7,z4,z5,z785]),(0,[z2,z7,z4,z786,z5,z6])],[(0,[z1,z123,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z80,z24]),(0,[z1,z2,z7,z4,z5,z787]),(0,[z82,z2,z7,z4,z83,z24]),(0,[z111,z1,z102,z214,z5,z6]),(0,[z1,z2,z4,z93,z5,z6])],[(0,[z0,z1,z2,z4,z97,z6])],[(0,[z688,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z788,z5,z6]),(0,[z1,z2,z7,z4,z5,z789]),(0,[z2,z7,z4,z5,z17,z521]),(0,[z0,z373,z1,z2,z4,z24]),(0,[z0,z1,z2,z7,z214,z6]),(0,[z1,z2,z7,z4,z5,z790])],[(0,[z38,z2,z7,z284,z5,z6]),(0,[z1,z73,z65,z4,z215,z6]),(0,[z1,z2,z238,z7,z791,z6])],[(0,[z454,z2,z197,z4,z5,z6]),(0,[z1,z2,z238,z7,z49,z24])],[(0,[z1,z2,z7,z792,z5,z6]),(0,[z0,z1,z2,z678,z4,z6]),(0,[z1,z2,z7,z793,z4,z6]),(0,[z1,z73,z65,z4,z121,z6]),(0,[z377,z1,z2,z4,z76,z6])],[],[(0,[z1,z2,z7,z4,z374,z17]),(0,[z0,z1,z2,z4,z679,z6]),(0,[z1,z2,z224,z7,z4,z6]),(0,[z1,z2,z7,z4,z118,z6])],[(0,[z1,z2,z794,z4,z5,z6]),(0,[z167,z782,z7,z4,z5,z6]),(0,[z0,z1,z2,z304,z4,z6]),(0,[z38,z2,z7,z795,z5,z6])],[(0,[z1,z123,z321,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z796]),(0,[z71,z1,z2,z166,z97,z5])]],
   [[(0,[z1,z2,z7,z4,z5,z797]),(0,[z1,z2,z7,z5,z24,z798])],[(0,[z1,z2,z799,z7,z4,z6]),(0,[z2,z7,z800,z4,z5,z6]),(0,[z1,z2,z801,z7,z4,z5]),(0,[z1,z802,z7,z4,z5,z6]),(0,[z79,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z803]),(0,[z1,z2,z4,z5,z6,z134])],[(0,[z804,z1,z2,z7,z4,z6]),(0,[z122,z0,z2,z7,z99,z6]),(1,[z1,z748,z4,z5,z6]),(0,[z1,z558,z7,z4,z76,z6])],[(0,[z1,z2,z7,z398,z5,z52]),(0,[z0,z1,z2,z4,z784,z6])],[(0,[z0,z1,z2,z20,z4,z24]),(0,[z1,z2,z805,z7,z4,z5]),(0,[z1,z2,z7,z5,z720,z10])],[(0,[z0,z1,z2,z197,z4,z24]),(0,[z1,z2,z7,z4,z374,z413]),(0,[z0,z1,z2,z4,z408,z6]),(0,[z0,z1,z2,z4,z93,z6])],[(0,[z1,z2,z7,z4,z5,z806])],[(0,[z1,z2,z7,z807,z4,z6])],[(0,[z1,z2,z151,z7,z4,z24]),(0,[z0,z1,z2,z511,z4,z5]),(0,[z0,z1,z2,z16,z572,z6]),(0,[z1,z2,z20,z7,z792,z6]),(0,[z1,z2,z7,z4,z808,z6]),(0,[z1,z2,z7,z5,z791,z6]),(0,[z1,z2,z7,z4,z714,z22])],[(0,[z2,z7,z4,z5,z579,z24]),(0,[z1,z2,z7,z809,z5,z24]),(0,[z1,z2,z7,z4,z5,z810]),(0,[z0,z1,z2,z511,z4,z97])],[],[(0,[z1,z2,z16,z586,z5,z6]),(0,[z2,z7,z4,z5,z12,z24])],[(0,[z1,z2,z7,z4,z5,z811])],[(0,[z0,z1,z2,z20,z4,z17]),(0,[z0,z1,z45,z7,z4,z32]),(0,[z1,z2,z21,z7,z4,z474]),(0,[z1,z2,z4,z5,z182,z812])],[(0,[z1,z2,z7,z813,z5,z6]),(0,[z1,z7,z514,z5,z32,z6]),(0,[z1,z2,z62,z4,z118,z182])],[(0,[z1,z814,z7,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z5,z815]),(0,[z816,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z817,z6]),(0,[z1,z2,z7,z227,z116,z24])],[(0,[z1,z2,z7,z4,z105,z24]),(0,[z1,z2,z20,z7,z4,z517]),(0,[z1,z2,z7,z4,z90,z294]),(0,[z1,z20,z7,z50,z4,z6])],[(1,[z2,z7,z795,z5,z6])],[(0,[z1,z2,z20,z7,z4,z363]),(0,[z1,z2,z818,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z819]),(0,[z1,z2,z7,z51,z387,z5])],[(0,[z1,z820,z7,z4,z5,z6]),(0,[z1,z821,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z48,z17]),(0,[z1,z2,z7,z4,z5,z822]),(0,[z1,z2,z7,z4,z823,z5]),(0,[z0,z1,z2,z7,z824,z6]),(0,[z1,z2,z226,z227,z116,z6])],[(0,[z1,z2,z16,z225,z5,z6]),(0,[z1,z2,z511,z20,z7,z4])],[(0,[z98,z2,z197,z4,z5,z17]),(0,[z1,z442,z20,z7,z4,z6])],[(0,[z1,z2,z208,z4,z5,z24]),(0,[z0,z1,z73,z2,z4,z24]),(0,[z825,z2,z7,z4,z5,z6]),(0,[z0,z1,z2,z4,z95,z6])],[(0,[z68,z1,z2,z4,z97,z6]),(0,[z1,z2,z130,z4,z83,z6]),(0,[z1,z2,z20,z208,z4,z6]),(0,[z1,z2,z7,z4,z215,z24]),(0,[z1,z2,z4,z752,z5,z6])],[(0,[z0,z2,z3,z197,z4,z6]),(0,[z1,z2,z7,z4,z5,z826]),(0,[z1,z2,z827,z4,z5,z6])],[(0,[z82,z2,z7,z4,z83,z129])],[(0,[z1,z2,z7,z4,z828,z6]),(0,[z1,z2,z829,z7,z4,z6]),(0,[z0,z1,z2,z64,z4,z6])],[(0,[z0,z1,z2,z345,z4,z6]),(0,[z0,z1,z2,z7,z4,z830]),(0,[z1,z831,z2,z7,z4,z5])],[(0,[z0,z1,z2,z4,z6,z114]),(0,[z0,z1,z2,z4,z113,z6])],[(0,[z1,z2,z7,z229,z5,z24]),(0,[z1,z2,z7,z4,z5,z832])]],
   [[(0,[z0,z1,z2,z4,z121,z6]),(0,[z0,z1,z772,z7,z4,z6])],[(0,[z0,z1,z73,z2,z4,z17]),(0,[z1,z2,z7,z4,z833,z6]),(0,[z402,z2,z7,z333,z4,z6])],[(0,[z1,z2,z7,z4,z5,z357]),(0,[z0,z1,z2,z321,z4,z6]),(0,[z2,z7,z613,z4,z5,z17])],[(0,[z122,z2,z20,z7,z99,z6]),(0,[z1,z2,z62,z7,z265,z5]),(0,[z0,z1,z2,z16,z216,z6])],[(0,[z1,z2,z834,z7,z4,z6]),(0,[z1,z2,z835,z7,z4,z5]),(0,[z1,z2,z7,z4,z174,z24]),(0,[z1,z2,z7,z824,z5,z6]),(0,[z0,z1,z652,z2,z4,z6])],[(0,[z0,z1,z2,z7,z4,z363])],[(0,[z1,z2,z7,z4,z5,z836]),(0,[z0,z15,z2,z7,z4,z17]),(0,[z732,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z837,z5,z6]),(0,[z1,z2,z829,z254,z4,z6]),(0,[z1,z838,z7,z4,z5,z6]),(0,[z82,z2,z7,z4,z839,z6]),(0,[z1,z2,z651,z7,z49,z6]),(0,[z194,z2,z7,z333,z4,z6]),(0,[z1,z326,z7,z4,z76,z17]),(0,[z1,z2,z62,z4,z5,z812]),(0,[z1,z2,z42,z7,z5,z720])],[(0,[z1,z2,z840,z7,z5,z6]),(0,[z1,z2,z7,z841,z5,z6])],[(0,[z0,z1,z2,z4,z201,z6]),(0,[z1,z2,z842,z7,z4,z5]),(0,[z1,z2,z7,z214,z5,z24]),(0,[z1,z2,z7,z843,z4,z5]),(0,[z1,z2,z7,z4,z5,z844])],[(0,[z1,z2,z7,z4,z5,z845]),(0,[z1,z2,z7,z4,z191,z5]),(0,[z1,z7,z4,z5,z846,z86])],[(0,[z1,z2,z7,z4,z5,z847]),(0,[z0,z1,z2,z208,z4,z6]),(0,[z1,z39,z20,z7,z117,z6])],[(0,[z0,z1,z2,z848,z4,z6]),(0,[z1,z2,z7,z4,z5,z849]),(0,[z1,z2,z7,z850,z5,z6]),(0,[z0,z1,z2,z511,z7,z4]),(0,[z567,z33,z2,z7,z4,z6])],[(0,[z1,z2,z851,z4,z5,z6]),(0,[z1,z2,z7,z4,z174,z17])],[(0,[z1,z2,z7,z4,z852,z6]),(0,[z1,z123,z7,z4,z374,z6]),(0,[z1,z2,z724,z7,z4,z6])],[(0,[z1,z2,z7,z4,z5,z853]),(0,[z666,z2,z7,z4,z5,z17]),(0,[z1,z26,z7,z27,z5,z24]),(0,[z230,z0,z1,z2,z4,z6]),(0,[z1,z2,z16,z225,z290,z6]),(0,[z0,z1,z2,z4,z178,z6])]],
   [[],[(0,[z1,z2,z7,z4,z5,z854]),(0,[z1,z30,z7,z4,z5,z674])],[(0,[z1,z2,z238,z7,z216,z6])],[(0,[z1,z2,z7,z4,z5,z6]),(0,[z1,z855,z2,z7,z4,z5])],[(0,[z1,z2,z4,z5,z24,z856]),(0,[z1,z7,z27,z5,z507,z6]),(0,[z857,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z192])],[(0,[z1,z2,z7,z4,z5,z858])],[(0,[z119,z782,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z6,z859]),(0,[z459,z2,z3,z4,z5,z6]),(0,[z194,z2,z208,z4,z124,z6])],[(0,[z98,z2,z800,z4,z5,z6]),(0,[z122,z2,z7,z99,z283,z6]),(0,[z1,z860,z7,z4,z5,z6])],[(0,[z1,z2,z7,z861,z5,z6]),(0,[z1,z2,z7,z4,z5,z862]),(0,[z1,z2,z7,z502,z5,z52]),(0,[z1,z863,z7,z4,z5,z6]),(0,[z1,z2,z864,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z228]),(0,[z1,z541,z20,z7,z4,z6])],[(0,[z1,z721,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z309,z24])],[(0,[z1,z2,z43,z7,z4,z17]),(0,[z1,z2,z7,z4,z722,z6]),(0,[z1,z2,z7,z101,z4,z5]),(1,[z1,z2,z7,z5,z720])],[(0,[z1,z2,z7,z4,z5,z320]),(0,[z0,z33,z2,z3,z4,z6]),(0,[z865,z2,z7,z4,z5,z6])],[(0,[z1,z2,z321,z4,z5,z6]),(0,[z122,z2,z7,z795,z5,z6]),(0,[z0,z1,z540,z2,z4,z6]),(0,[z1,z2,z20,z7,z4,z866])],[(0,[z1,z2,z726,z7,z4,z6]),(0,[z1,z2,z7,z867,z5,z24]),(0,[z1,z2,z748,z4,z5,z6]),(0,[z1,z2,z868,z4,z5,z6]),(0,[z71,z1,z2,z511,z97,z5]),(0,[z1,z2,z4,z327,z59,z6])],[(0,[z1,z2,z7,z4,z869,z6]),(0,[z870,z2,z7,z4,z5,z6]),(0,[z0,z57,z1,z2,z4,z58])]],
   [[(0,[z871,z1,z2,z7,z4,z6]),(0,[z1,z2,z20,z7,z4,z555]),(0,[z1,z662,z7,z4,z156,z6]),(0,[z1,z2,z7,z872,z5,z6])],[(0,[z873,z1,z2,z4,z5,z6]),(0,[z1,z2,z7,z874,z5,z6])],[(0,[z1,z2,z7,z4,z80,z17]),(0,[z1,z123,z7,z4,z5,z493]),(0,[z1,z2,z20,z7,z4,z469]),(0,[z38,z2,z20,z7,z284,z6]),(0,[z82,z2,z7,z4,z83,z17]),(0,[z1,z2,z7,z4,z5,z875])],[(0,[z1,z2,z7,z4,z5,z876]),(0,[z1,z2,z20,z7,z4,z239]),(0,[z98,z2,z20,z197,z4,z6]),(0,[z1,z2,z877,z4,z5,z6]),(0,[z1,z2,z130,z20,z4,z6]),(0,[z1,z2,z20,z7,z4,z24]),(0,[z1,z326,z348,z7,z4,z6]),(0,[z1,z2,z270,z4,z93,z5])],[(0,[z1,z2,z338,z4,z5,z24]),(0,[z1,z2,z62,z4,z5,z182])],[(0,[z1,z2,z7,z4,z5,z878]),(0,[z1,z2,z7,z879,z5,z6]),(0,[z1,z2,z7,z4,z880,z6]),(0,[z0,z1,z2,z4,z327,z6]),(0,[z1,z2,z7,z4,z5,z881])],[(0,[z1,z618,z7,z27,z5,z6]),(0,[z0,z1,z2,z4,z253,z6]),(0,[z1,z2,z7,z4,z5,z882]),(0,[z1,z2,z20,z7,z4,z249]),(0,[z1,z2,z130,z4,z5,z24]),(0,[z1,z2,z238,z7,z49,z17]),(0,[z1,z2,z91,z7,z4,z245]),(0,[z537,z459,z2,z7,z4,z6])],[(0,[z1,z2,z20,z7,z4,z883])],[(0,[z1,z2,z7,z4,z884,z6]),(0,[z1,z2,z7,z4,z885,z24])],[(0,[z1,z326,z7,z4,z191,z76])],[(0,[z0,z1,z2,z243,z4,z6])],[(0,[z1,z2,z7,z4,z309,z517]),(0,[z1,z886,z2,z7,z4,z5]),(0,[z887,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z69]),(0,[z1,z2,z7,z4,z888,z6]),(0,[z1,z889,z2,z7,z4,z5])],[(0,[z1,z2,z7,z4,z890,z6]),(0,[z1,z2,z20,z7,z4,z17]),(0,[z75,z1,z326,z2,z4,z6]),(0,[z1,z2,z7,z4,z290,z6])],[(0,[z1,z2,z7,z4,z5,z891]),(0,[z1,z2,z4,z5,z17,z134]),(0,[z2,z7,z4,z5,z892,z6]),(0,[z1,z2,z893,z4,z5,z6])],[(0,[z1,z2,z7,z161,z5,z24]),(0,[z82,z33,z2,z7,z4,z6]),(0,[z435,z2,z7,z4,z5,z24]),(0,[z1,z2,z20,z4,z59,z6])],[]],
   [[(0,[z1,z2,z894,z4,z5,z6])],[(0,[z0,z1,z2,z197,z4,z17]),(0,[z0,z1,z2,z4,z285,z6])],[(0,[z167,z23,z7,z4,z80,z6]),(0,[z1,z2,z895,z7,z4,z5]),(0,[z1,z2,z20,z4,z150,z24]),(0,[z1,z2,z7,z4,z70,z24]),(0,[z1,z2,z511,z151,z7,z4]),(0,[z377,z1,z2,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z896])],[(0,[z1,z2,z7,z4,z5,z897]),(0,[z1,z2,z7,z4,z898,z6]),(0,[z0,z1,z2,z7,z4,z469]),(0,[z1,z2,z151,z7,z4,z17]),(0,[z1,z7,z899,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z24]),(0,[z1,z2,z900,z7,z4,z5]),(0,[z901,z1,z30,z2,z4,z6])],[(0,[z1,z2,z7,z4,z791,z6])],[(0,[z1,z2,z902,z4,z5,z6]),(0,[z111,z0,z1,z2,z4,z24])],[(0,[z1,z2,z7,z137,z5,z24]),(0,[z1,z2,z208,z4,z5,z555]),(0,[z1,z2,z903,z7,z4,z5]),(0,[z0,z1,z2,z496,z4,z6])],[(0,[z1,z2,z7,z4,z904,z5]),(0,[z1,z2,z7,z4,z5,z905]),(0,[z111,z1,z2,z120,z4,z6]),(0,[z1,z2,z4,z906,z5,z6]),(0,[z1,z326,z4,z93,z76,z6]),(0,[z1,z2,z447,z20,z4,z6])],[(0,[z1,z2,z907,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z315]),(0,[z1,z73,z65,z4,z5,z24]),(0,[z1,z2,z908,z4,z5,z6]),(0,[z1,z7,z237,z27,z5,z6])],[(0,[z1,z2,z909,z4,z5,z6]),(0,[z1,z2,z20,z4,z150,z17]),(0,[z1,z30,z7,z514,z5,z6]),(1,[z1,z2,z752,z5,z6])],[(0,[z1,z2,z7,z910,z5,z6]),(0,[z167,z23,z20,z7,z4,z6]),(0,[z1,z2,z7,z911,z5,z6]),(0,[z1,z2,z7,z227,z116,z17]),(0,[z0,z57,z1,z2,z4,z6]),(0,[z1,z2,z226,z4,z49,z6])],[(0,[z1,z2,z7,z4,z105,z17]),(0,[z122,z442,z7,z99,z5,z6]),(0,[z1,z2,z912,z321,z4,z6]),(0,[z1,z2,z7,z4,z5,z913])],[(0,[z1,z2,z7,z914,z5,z6]),(0,[z1,z2,z7,z4,z121,z24]),(0,[z0,z1,z465,z2,z4,z6])],[(0,[z1,z2,z7,z915,z5,z6]),(0,[z1,z2,z916,z4,z5,z6])]],
   [[(0,[z1,z2,z7,z4,z917,z6]),(0,[z162,z2,z800,z4,z5,z6]),(0,[z111,z0,z1,z2,z4,z17]),(0,[z1,z2,z4,z918,z5,z6]),(0,[z0,z1,z2,z4,z59,z6])],[(0,[z1,z2,z7,z137,z5,z17]),(0,[z1,z919,z7,z4,z5,z17]),(0,[z0,z594,z1,z2,z4,z6])],[(0,[z1,z2,z42,z7,z5,z417]),(0,[z1,z2,z20,z7,z4,z166]),(0,[z0,z1,z2,z7,z4,z920]),(0,[z424,z1,z662,z7,z4,z6]),(0,[z0,z57,z1,z2,z4,z474])],[(0,[z1,z2,z7,z4,z5,z371]),(0,[z535,z2,z7,z4,z5,z17]),(0,[z1,z2,z921,z7,z4,z6]),(0,[z0,z1,z922,z7,z4,z6]),(0,[z1,z2,z7,z4,z6,z109])],[(0,[z1,z23,z7,z137,z5,z6]),(0,[z1,z2,z7,z923,z5,z6]),(0,[z1,z2,z7,z4,z5,z924]),(0,[z1,z2,z208,z4,z5,z17]),(0,[z194,z2,z130,z4,z124,z6]),(0,[z1,z2,z7,z925,z5,z17])],[(0,[z1,z2,z7,z926,z5,z6]),(0,[z1,z2,z7,z4,z215,z17]),(0,[z1,z308,z7,z4,z5,z86]),(0,[z1,z748,z102,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z927]),(0,[z1,z2,z4,z97,z174,z6])],[(0,[z535,z23,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z517]),(0,[z1,z7,z4,z729,z76,z6])],[(0,[z167,z23,z7,z161,z5,z6]),(0,[z1,z2,z7,z4,z928,z6]),(0,[z901,z1,z2,z4,z70,z6]),(0,[z1,z30,z7,z4,z5,z846]),(0,[z1,z2,z7,z4,z166,z5]),(0,[z1,z2,z7,z4,z5,z929])],[(0,[z1,z2,z20,z7,z4,z129]),(0,[z0,z930,z2,z7,z4,z6])],[(0,[z1,z2,z7,z4,z931,z6]),(0,[z1,z2,z7,z932,z4,z5]),(0,[z1,z2,z20,z4,z6,z396])],[(0,[z1,z30,z7,z4,z48,z86]),(0,[z1,z2,z151,z7,z4,z166]),(0,[z377,z1,z2,z21,z4,z6])],[(0,[z1,z2,z933,z4,z5,z6]),(0,[z1,z934,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z283,z24]),(0,[z1,z2,z7,z229,z5,z17])],[(0,[z1,z2,z7,z4,z374,z6]),(0,[z15,z2,z7,z4,z5,z17])],[(0,[z167,z23,z7,z4,z105,z6]),(0,[z1,z2,z935,z7,z4,z5])],[],[]],
   [[(0,[z1,z2,z66,z4,z80,z6]),(0,[z111,z0,z1,z348,z4,z6]),(0,[z1,z2,z20,z7,z4,z768])],[(0,[z167,z23,z7,z137,z5,z6]),(0,[z1,z2,z7,z4,z936,z6]),(0,[z1,z2,z7,z4,z937,z6]),(0,[z0,z1,z2,z4,z372,z6]),(0,[z0,z1,z2,z432,z4,z6])],[(0,[z0,z1,z2,z16,z4,z24]),(0,[z1,z30,z7,z4,z5,z140]),(0,[z1,z30,z573,z7,z4,z5]),(0,[z1,z2,z7,z4,z135,z462])],[(0,[z1,z2,z151,z197,z4,z6]),(0,[z0,z38,z2,z7,z284,z6]),(0,[z594,z1,z2,z97,z5,z6])],[(0,[z0,z98,z2,z197,z4,z6]),(0,[z1,z54,z65,z4,z5,z6]),(0,[z1,z2,z120,z7,z4,z24]),(0,[z111,z1,z20,z102,z4,z6]),(0,[z165,z75,z1,z2,z4,z6])],[(0,[z1,z2,z7,z938,z5,z6]),(0,[z1,z2,z7,z4,z939,z6]),(0,[z98,z2,z197,z4,z5,z357]),(0,[z1,z2,z7,z214,z5,z17]),(0,[z1,z2,z7,z4,z5,z940])],[(0,[z1,z2,z321,z4,z374,z6]),(0,[z1,z2,z7,z941,z5,z6])],[(0,[z1,z2,z130,z4,z124,z6]),(0,[z1,z2,z7,z942,z4,z6])],[(0,[z0,z1,z2,z231,z4,z6]),(0,[z672,z2,z7,z4,z5,z17])],[(0,[z391,z2,z7,z4,z5,z17]),(0,[z1,z39,z7,z735,z5,z6]),(0,[z0,z1,z2,z62,z4,z182])],[(0,[z0,z1,z2,z7,z4,z129]),(0,[z0,z1,z2,z4,z202,z6])],[(0,[z1,z26,z7,z27,z5,z17]),(0,[z1,z2,z7,z4,z943,z24]),(0,[z1,z2,z4,z5,z6,z944])],[(0,[z0,z1,z2,z20,z4,z6]),(0,[z1,z2,z42,z7,z361,z5])],[(0,[z1,z2,z20,z4,z697,z6]),(0,[z1,z2,z120,z7,z4,z17]),(0,[z1,z2,z945,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z946]),(0,[z1,z2,z947,z7,z4,z6]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z1,z2,z7,z4,z949,z5])],[(0,[z0,z1,z2,z4,z24,z182]),(0,[z1,z2,z950,z7,z4,z6]),(0,[z1,z951,z7,z4,z5,z6]),(0,[z1,z2,z4,z150,z6,z544])],[]],
   [[(0,[z1,z2,z7,z4,z309,z249]),(0,[z1,z2,z7,z4,z5,z493]),(0,[z0,z1,z2,z117,z97,z6]),(0,[z1,z952,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z5,z953]),(0,[z1,z954,z7,z4,z5,z17])],[(0,[z1,z442,z7,z4,z283,z6]),(0,[z1,z110,z7,z27,z5,z6]),(0,[z0,z1,z2,z683,z4,z6]),(0,[z1,z2,z180,z7,z4,z78]),(0,[z955,z1,z2,z4,z5,z6])],[(0,[z1,z2,z7,z251,z5,z293]),(0,[z1,z2,z7,z4,z327,z24]),(0,[z956,z2,z7,z4,z5,z6]),(0,[z1,z30,z393,z7,z4,z5])],[(0,[z1,z2,z7,z4,z957,z6]),(0,[z1,z2,z7,z4,z48,z6]),(0,[z0,z1,z2,z16,z97,z6])],[(0,[z1,z2,z66,z161,z5,z6]),(0,[z1,z2,z958,z7,z4,z6]),(0,[z1,z2,z7,z4,z959,z6])],[(0,[z1,z2,z960,z4,z5,z6]),(0,[z98,z2,z197,z4,z5,z6]),(0,[z1,z2,z7,z4,z309,z17]),(0,[z122,z2,z254,z99,z5,z6]),(0,[z1,z2,z130,z4,z5,z555]),(0,[z0,z1,z2,z603,z4,z6]),(0,[z1,z2,z511,z7,z4,z5]),(0,[z0,z1,z487,z2,z4,z6])],[(0,[z139,z119,z7,z4,z5,z6])],[(0,[z1,z442,z7,z284,z5,z6]),(0,[z75,z1,z326,z4,z76,z6])],[(0,[z122,z2,z7,z99,z5,z24]),(0,[z1,z2,z7,z4,z961,z24]),(0,[z1,z2,z20,z7,z4,z132])],[(0,[z1,z2,z7,z4,z5,z962]),(0,[z1,z39,z7,z13,z5,z6]),(0,[z1,z2,z321,z4,z5,z493]),(0,[z111,z1,z102,z4,z5,z24]),(0,[z1,z7,z51,z50,z5,z52])],[(0,[z1,z2,z66,z4,z105,z6]),(0,[z1,z2,z7,z4,z5,z963]),(1,[z0,z1,z2,z214,z6])],[(0,[z98,z2,z197,z4,z5,z228]),(0,[z385,z2,z197,z4,z5,z6]),(0,[z1,z2,z7,z4,z964,z6])],[(0,[z1,z2,z7,z4,z5,z965]),(0,[z1,z7,z966,z4,z5,z17]),(0,[z576,z1,z2,z7,z4,z474])],[(0,[z1,z2,z7,z967,z5,z6])],[(0,[z1,z2,z66,z137,z5,z6]),(1,[z782,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z968,z6]),(0,[z173,z1,z2,z4,z5,z58]),(0,[z1,z378,z7,z4,z5,z341]),(0,[z0,z1,z2,z613,z4,z6]),(0,[z1,z2,z7,z4,z5,z969]),(0,[z1,z2,z4,z5,z6,z812])]],
   [[(0,[z1,z2,z338,z4,z5,z17]),(0,[z1,z2,z7,z4,z5,z970]),(0,[z0,z1,z73,z2,z4,z6]),(0,[z1,z2,z752,z97,z5,z6])],[(0,[z1,z2,z7,z4,z55,z187]),(0,[z1,z2,z20,z4,z6,z134])],[(0,[z122,z2,z7,z99,z5,z17]),(0,[z1,z2,z7,z4,z971,z6]),(0,[z1,z2,z130,z4,z5,z17]),(0,[z1,z738,z7,z4,z5,z6]),(0,[z1,z7,z4,z5,z32,z846]),(0,[z1,z2,z7,z4,z759,z6]),(0,[z1,z2,z7,z4,z972,z6]),(0,[z1,z2,z7,z5,z52,z720])],[(0,[z1,z2,z7,z4,z5,z973]),(0,[z1,z2,z7,z4,z5,z974])],[(0,[z75,z1,z2,z4,z83,z6]),(0,[z0,z1,z951,z7,z4,z6])],[(0,[z0,z1,z2,z7,z4,z555]),(0,[z1,z2,z7,z4,z90,z9]),(0,[z1,z2,z511,z4,z150,z5])],[(0,[z1,z2,z975,z4,z5,z6]),(0,[z1,z2,z7,z4,z24,z976]),(0,[z1,z326,z7,z4,z76,z6])],[(0,[z1,z2,z977,z7,z4,z6]),(0,[z1,z2,z20,z7,z4,z413]),(0,[z1,z7,z4,z156,z729,z6]),(0,[z1,z45,z7,z287,z4,z5]),(0,[z1,z2,z7,z978,z5,z6])],[(0,[z0,z1,z2,z7,z4,z239]),(0,[z0,z1,z2,z4,z468,z6]),(0,[z1,z2,z7,z51,z5,z52])],[],[(0,[z1,z2,z7,z161,z5,z17]),(0,[z1,z2,z7,z4,z979,z6]),(0,[z1,z980,z7,z4,z5,z6]),(0,[z122,z2,z7,z99,z5,z413]),(0,[z331,z2,z7,z284,z5,z6]),(0,[z2,z7,z4,z5,z24,z653]),(0,[z165,z0,z1,z2,z4,z6]),(0,[z57,z1,z2,z4,z109,z58])],[(0,[z0,z1,z2,z7,z4,z249]),(0,[z1,z2,z7,z4,z981,z6]),(0,[z1,z2,z7,z4,z5,z982])],[(0,[z1,z2,z120,z197,z4,z6]),(0,[z1,z2,z7,z4,z983,z6]),(0,[z1,z2,z984,z4,z5,z6]),(0,[z1,z2,z7,z4,z174,z6]),(0,[z1,z2,z7,z4,z985,z6])],[(0,[z1,z2,z7,z4,z986,z6])],[(0,[z1,z2,z7,z4,z70,z17]),(0,[z1,z2,z7,z4,z987,z6])],[]],
   [[(0,[z167,z23,z338,z4,z5,z6]),(0,[z1,z541,z7,z4,z5,z10])],[(0,[z1,z2,z988,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z17]),(0,[z1,z30,z20,z7,z4,z86])],[(0,[z1,z2,z800,z4,z5,z6]),(0,[z1,z2,z7,z989,z5,z6]),(0,[z1,z990,z2,z7,z4,z5])],[(0,[z1,z2,z991,z4,z5,z6]),(0,[z1,z992,z7,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z134])],[(0,[z1,z2,z21,z7,z4,z245])],[(0,[z1,z39,z7,z117,z5,z24]),(0,[z111,z1,z120,z102,z4,z6]),(0,[z1,z2,z16,z4,z174,z6])],[(0,[z1,z2,z993,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z994]),(0,[z1,z73,z65,z4,z5,z17]),(0,[z1,z2,z7,z995,z5,z6])],[(0,[z1,z922,z7,z4,z5,z6]),(0,[z162,z2,z3,z4,z309,z6]),(0,[z1,z2,z7,z4,z996,z6]),(0,[z1,z2,z62,z4,z182,z544])],[(0,[z997,z2,z7,z4,z5,z6]),(0,[z11,z1,z2,z7,z4,z462])],[(0,[z0,z1,z2,z7,z4,z413]),(0,[z1,z2,z7,z4,z353,z294])],[(0,[z1,z2,z20,z7,z4,z233]),(0,[z1,z2,z7,z4,z121,z17]),(0,[z1,z2,z4,z998,z5,z6]),(0,[z1,z2,z999,z7,z4,z6]),(0,[z1,z2,z43,z7,z4,z6])],[(0,[z1,z2,z254,z4,z283,z6]),(0,[z71,z1,z2,z151,z97,z6])],[(0,[z1,z2,z1000,z4,z5,z6]),(0,[z1,z2,z1001,z4,z5,z6]),(0,[z1,z508,z7,z27,z5,z6]),(0,[z1,z7,z4,z5,z6,z1002]),(0,[z1,z2,z7,z4,z5,z1003])],[(0,[z2,z782,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1004]),(0,[z1,z2,z20,z87,z4,z6]),(0,[z1,z2,z7,z4,z6,z544])],[(0,[z194,z2,z7,z4,z839,z6])],[(0,[z0,z1,z2,z168,z4,z6]),(0,[z1,z2,z7,z4,z17,z109]),(0,[z0,z1,z2,z418,z4,z6])]],
   [[(0,[z1,z30,z7,z4,z70,z86])],[(0,[z1,z2,z7,z4,z80,z6]),(0,[z82,z2,z7,z4,z83,z6]),(0,[z1,z2,z7,z4,z5,z1005]),(0,[z0,z1,z2,z7,z4,z734]),(0,[z1,z2,z20,z7,z4,z844])],[(0,[z71,z1,z2,z20,z97,z6])],[(0,[z1,z2,z7,z4,z1006,z6]),(0,[z1,z2,z7,z4,z1007,z6]),(0,[z0,z373,z1,z2,z4,z6]),(0,[z1,z541,z7,z4,z5,z24]),(0,[z111,z1,z401,z102,z4,z5])],[(0,[z1,z2,z20,z338,z4,z6]),(0,[z82,z2,z7,z4,z83,z303]),(0,[z1,z2,z7,z4,z5,z1008])],[(0,[z1,z2,z238,z7,z49,z6]),(0,[z11,z377,z1,z2,z4,z6])],[(0,[z2,z545,z7,z4,z5,z24]),(0,[z0,z1,z39,z7,z117,z6]),(0,[z1,z2,z42,z7,z5,z10])],[(0,[z1,z2,z7,z4,z5,z742]),(0,[z1,z2,z7,z4,z1009,z6]),(0,[z1,z2,z7,z4,z283,z17]),(0,[z585,z2,z7,z4,z83,z6]),(0,[z71,z1,z2,z97,z5,z24]),(0,[z1,z2,z1010,z7,z4,z6]),(0,[z0,z1,z2,z7,z4,z166]),(0,[z1,z2,z20,z7,z4,z853]),(0,[z1,z2,z20,z7,z995,z6])],[(0,[z1,z2,z7,z1011,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1012]),(0,[z1,z2,z217,z208,z4,z6]),(0,[z0,z1,z2,z4,z554,z6]),(0,[z1,z2,z7,z4,z374,z493])],[(0,[z1,z2,z7,z4,z80,z320]),(0,[z68,z1,z2,z7,z4,z24]),(0,[z1,z7,z4,z27,z5,z69])],[(0,[z1,z2,z20,z7,z4,z6]),(0,[z1,z45,z20,z7,z4,z32])],[(0,[z281,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z7,z4,z233]),(0,[z1,z2,z1013,z7,z4,z6]),(0,[z930,z2,z7,z4,z5,z6]),(0,[z1,z2,z1014,z4,z5,z6])],[(0,[z0,z1,z2,z611,z4,z6]),(0,[z177,z1,z7,z4,z156,z24]),(0,[z557,z2,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z1015,z6]),(0,[z1,z7,z4,z729,z5,z6]),(0,[z650,z1,z348,z7,z4,z6])],[(0,[z1,z2,z20,z66,z4,z6]),(0,[z2,z7,z284,z795,z5,z6]),(0,[z1,z2,z20,z7,z4,z303]),(0,[z0,z1,z2,z16,z4,z17]),(0,[z75,z1,z2,z20,z4,z6]),(0,[z575,z1,z2,z7,z572,z6])],[(0,[z1,z2,z7,z4,z1016,z6]),(0,[z1,z2,z7,z4,z283,z413])]],
   [[(0,[z0,z1,z2,z197,z4,z6]),(0,[z1,z123,z20,z7,z4,z6])],[(0,[z167,z0,z23,z7,z4,z6]),(0,[z1,z2,z7,z4,z839,z6]),(0,[z75,z1,z2,z4,z5,z24]),(0,[z1,z2,z4,z5,z6,z1017])],[(0,[z1,z2,z16,z225,z174,z6]),(0,[z1,z541,z62,z7,z4,z5])],[(0,[z68,z1,z2,z7,z4,z17]),(0,[z1,z2,z1018,z4,z5,z6]),(0,[z1,z2,z151,z7,z4,z6])],[(0,[z1,z2,z7,z809,z5,z6]),(0,[z529,z1,z7,z27,z5,z6]),(0,[z1,z2,z4,z1019,z5,z6])],[(0,[z1,z2,z7,z4,z1020,z6]),(0,[z111,z0,z1,z73,z4,z6]),(0,[z1,z2,z1021,z7,z4,z5])],[(0,[z1,z2,z20,z7,z101,z4]),(0,[z0,z1,z2,z4,z6,z583])],[(0,[z2,z7,z4,z839,z83,z6]),(0,[z1,z2,z7,z4,z1022,z6]),(0,[z1023,z2,z7,z4,z5,z6])],[(0,[z0,z1,z2,z4,z222,z6]),(0,[z0,z1,z2,z4,z420,z17]),(0,[z0,z1,z2,z4,z182,z17]),(0,[z1,z2,z441,z7,z5,z417])],[(0,[z0,z1,z2,z130,z4,z6]),(0,[z1,z2,z7,z1024,z5,z17]),(0,[z1,z2,z7,z4,z5,z1025]),(0,[z1,z2,z4,z6,z134,z544])],[(0,[z1,z2,z7,z4,z1026,z6]),(0,[z1,z2,z7,z1027,z4,z5]),(0,[z1,z2,z20,z4,z150,z6]),(0,[z0,z1,z2,z4,z589,z6])],[(0,[z1,z7,z399,z4,z5,z32]),(0,[z1,z2,z7,z227,z116,z6])],[(0,[z1,z2,z7,z4,z105,z6])],[(0,[z1,z1028,z2,z7,z4,z5]),(0,[z1,z2,z7,z514,z5,z24]),(0,[z0,z1,z2,z203,z4,z6]),(0,[z1,z2,z4,z150,z784,z6]),(0,[z1,z2,z7,z4,z1029,z6])],[(0,[z1,z2,z7,z4,z5,z1030]),(0,[z0,z1,z401,z2,z7,z4])],[(0,[z1,z2,z7,z4,z327,z17]),(0,[z111,z0,z1,z2,z4,z6])]],
   [[(0,[z1,z2,z7,z137,z5,z6]),(0,[z1,z919,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z303]),(0,[z1,z2,z1031,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1032])],[(0,[z1,z2,z7,z4,z5,z1033]),(0,[z1,z442,z254,z4,z5,z6]),(0,[z1,z1034,z7,z4,z5,z6]),(0,[z1,z2,z43,z4,z182,z6])],[(0,[z1,z2,z7,z1035,z4,z5]),(0,[z1,z2,z7,z4,z1036,z6])],[(0,[z1,z2,z7,z925,z5,z6]),(0,[z1,z2,z208,z4,z5,z6])],[(0,[z1,z442,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z215,z6])],[(0,[z1,z2,z7,z4,z105,z320]),(0,[z1,z2,z1037,z4,z5,z6])],[(0,[z111,z1,z102,z4,z5,z17]),(0,[z1038,z1,z2,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z720])],[(0,[z0,z273,z1,z2,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1039]),(0,[z0,z1,z2,z7,z101,z4]),(0,[z1,z2,z7,z572,z116,z6])],[(0,[z0,z162,z2,z3,z4,z6]),(0,[z1,z2,z4,z182,z888,z6])],[(0,[z1,z1040,z7,z4,z5,z6]),(0,[z1,z2,z7,z229,z5,z6])],[(0,[z0,z459,z2,z3,z4,z6]),(0,[z1,z2,z7,z4,z5,z1041]),(0,[z2,z7,z4,z124,z839,z6]),(0,[z194,z2,z7,z4,z124,z24]),(0,[z1,z2,z7,z4,z1042,z5]),(0,[z1,z2,z7,z4,z1043,z6])],[(0,[z1,z2,z4,z93,z121,z6])],[(0,[z1,z2,z4,z1044,z5,z6]),(0,[z1,z401,z2,z224,z7,z4]),(0,[z1,z2,z7,z4,z6,z1045]),(0,[z1,z2,z7,z4,z5,z1046])],[(0,[z0,z1,z2,z7,z4,z132]),(0,[z1,z2,z270,z20,z7,z4]),(0,[z1,z2,z7,z4,z5,z1047])],[(0,[z1,z2,z7,z1048,z4,z5]),(0,[z0,z1,z889,z2,z7,z4]),(0,[z0,z1,z2,z4,z629,z6]),(0,[z1,z541,z7,z4,z5,z52])]],
   [[(0,[z1,z2,z7,z1049,z5,z6]),(0,[z1050,z1,z2,z4,z5,z6])],[(0,[z1,z2,z7,z4,z80,z371]),(0,[z560,z2,z7,z4,z5,z17]),(0,[z1,z7,z748,z4,z5,z6]),(0,[z1,z2,z7,z4,z1051,z6])],[(0,[z1,z2,z7,z5,z6,z1052]),(0,[z1,z2,z20,z7,z4,z315])],[(0,[z98,z2,z217,z197,z4,z6]),(0,[z1,z2,z217,z7,z4,z24]),(0,[z1,z2,z62,z418,z4,z5]),(1,[z1,z2,z4,z5,z812]),(0,[z1,z2,z4,z5,z6,z1053])],[(0,[z1,z2,z7,z214,z5,z6])],[(0,[z1,z1054,z7,z4,z5,z6]),(0,[z1,z2,z146,z7,z5,z176]),(0,[z1,z2,z7,z4,z327,z166])],[(0,[z592,z1,z2,z97,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1055])],[(0,[z1,z2,z7,z1056,z5,z6]),(0,[z1,z7,z4,z735,z5,z6]),(0,[z1,z2,z4,z5,z1057,z6])],[(0,[z1,z2,z3,z4,z309,z6]),(0,[z1,z2,z603,z225,z5,z6])],[(0,[z46,z2,z197,z4,z5,z6]),(0,[z1,z2,z4,z150,z121,z6]),(0,[z1,z26,z7,z27,z5,z6]),(0,[z0,z1,z2,z427,z4,z6])],[(0,[z1,z2,z20,z7,z4,z371]),(0,[z2,z20,z7,z4,z24,z17]),(0,[z1,z2,z7,z1058,z5,z6]),(0,[z1,z401,z2,z20,z7,z4]),(0,[z1,z39,z7,z117,z5,z132]),(0,[z1059,z2,z7,z4,z5,z6])],[(0,[z1,z2,z120,z7,z4,z6])],[(0,[z1,z2,z20,z7,z4,z357])],[(0,[z1,z2,z4,z5,z24,z134]),(0,[z0,z1,z2,z724,z4,z6]),(0,[z1,z2,z7,z4,z1060,z6]),(0,[z1,z2,z1061,z7,z4,z5]),(0,[z0,z1,z2,z4,z623,z6])],[(0,[z0,z1,z73,z65,z4,z6]),(0,[z1,z39,z7,z4,z5,z69])]],
   [[(0,[z1,z2,z1062,z4,z5,z6]),(0,[z1,z954,z7,z4,z5,z6]),(0,[z1063,z1,z2,z7,z4,z6]),(0,[z1,z1064,z2,z7,z4,z6])],[(0,[z1,z39,z7,z117,z5,z17]),(0,[z1,z2,z4,z59,z5,z24]),(0,[z745,z2,z7,z4,z5,z6]),(0,[z1,z422,z7,z4,z76,z6])],[(0,[z1,z2,z1065,z4,z5,z6]),(0,[z75,z1,z2,z4,z124,z6]),(0,[z1,z2,z4,z5,z17,z994]),(0,[z1,z2,z7,z4,z5,z1066])],[(0,[z0,z1,z2,z4,z524,z6]),(0,[z1,z2,z21,z7,z4,z714])],[(0,[z1,z2,z66,z4,z5,z24]),(0,[z2,z7,z4,z5,z24,z17]),(0,[z0,z410,z1,z2,z4,z6])],[(0,[z1,z2,z7,z4,z309,z6]),(0,[z1,z2,z4,z5,z812,z58])],[(0,[z1,z2,z7,z161,z5,z371])],[(0,[z1,z2,z120,z7,z101,z4]),(0,[z377,z1,z2,z4,z135,z6])],[(0,[z162,z2,z3,z4,z5,z517]),(0,[z1,z2,z7,z1067,z5,z24]),(0,[z0,z57,z1,z2,z42,z4]),(0,[z1,z2,z227,z59,z116,z6])],[(0,[z1,z2,z7,z4,z163,z517]),(0,[z0,z1,z2,z3,z4,z24]),(0,[z1,z2,z7,z867,z5,z6]),(0,[z1,z73,z4,z647,z5,z6]),(0,[z177,z1,z7,z179,z4,z6])],[(0,[z1,z2,z208,z4,z5,z315]),(0,[z556,z2,z7,z4,z5,z24]),(0,[z0,z377,z1,z2,z4,z6])],[(0,[z298,z119,z7,z4,z5,z363])],[(0,[z1,z2,z7,z4,z105,z371]),(0,[z1,z7,z966,z4,z5,z6]),(0,[z1,z2,z7,z5,z6,z1068]),(0,[z2,z675,z7,z4,z5,z24]),(0,[z1,z2,z1069,z4,z5,z6]),(0,[z0,z1,z1070,z7,z4,z6]),(0,[z1,z2,z7,z4,z784,z6])],[(0,[z1,z2,z254,z4,z5,z24]),(0,[z1,z2,z4,z327,z150,z6]),(0,[z1,z2,z7,z4,z5,z830])],[],[(0,[z1,z2,z338,z4,z5,z6]),(0,[z1,z541,z7,z4,z5,z17])]],
   [[(0,[z1,z2,z7,z137,z5,z371])],[(0,[z1,z2,z130,z4,z5,z6]),(0,[z122,z2,z7,z99,z5,z6]),(0,[z0,z1,z2,z4,z512,z6]),(0,[z0,z1,z2,z4,z689,z6])],[(0,[z57,z1,z2,z4,z5,z481]),(0,[z1,z2,z7,z1071,z5,z6]),(0,[z0,z1,z2,z4,z691,z6]),(0,[z1,z2,z226,z20,z4,z6])],[(0,[z1,z2,z7,z4,z885,z6]),(0,[z71,z1,z2,z97,z5,z17]),(0,[z1,z2,z7,z4,z5,z1072]),(0,[z1,z45,z7,z4,z5,z846]),(0,[z1,z2,z7,z4,z1073,z6]),(0,[z1,z2,z1074,z7,z4,z6])],[(0,[z1,z2,z20,z7,z4,z228]),(0,[z1,z2,z7,z4,z5,z1075]),(0,[z1,z2,z7,z4,z5,z1076]),(0,[z1,z2,z337,z226,z4,z6]),(0,[z1,z2,z226,z4,z116,z6])],[(0,[z1,z2,z1077,z4,z5,z6]),(0,[z1,z2,z226,z4,z5,z24]),(0,[z1,z2,z214,z150,z5,z6])],[(0,[z122,z123,z7,z99,z5,z6]),(0,[z1,z2,z254,z4,z5,z17]),(0,[z0,z1,z2,z511,z4,z6]),(0,[z0,z1,z2,z7,z915,z6]),(0,[z1,z2,z1078,z7,z4,z6])],[(0,[z1,z2,z20,z7,z4,z320]),(0,[z0,z71,z1,z2,z97,z6]),(0,[z1,z2,z7,z5,z6,z720])],[(0,[z1,z2,z338,z4,z5,z320]),(0,[z1,z2,z7,z4,z6,z1079]),(0,[z1,z2,z20,z7,z4,z493])],[(0,[z1,z2,z7,z161,z5,z6]),(0,[z0,z1,z2,z338,z4,z6]),(0,[z1,z2,z20,z254,z4,z6]),(0,[z1,z2,z7,z4,z5,z785]),(0,[z177,z1,z7,z4,z156,z17])],[(0,[z0,z1,z2,z60,z4,z6])],[(0,[z1,z2,z7,z4,z90,z77]),(0,[z1,z2,z7,z227,z512,z6])],[(0,[z1,z2,z1080,z4,z5,z6]),(0,[z1,z2,z7,z4,z55,z135]),(0,[z0,z57,z1,z30,z2,z4]),(0,[z0,z1,z2,z259,z4,z6])],[(0,[z75,z1,z2,z4,z5,z17]),(0,[z1,z2,z7,z4,z70,z6]),(0,[z1,z2,z20,z7,z4,z875])],[(0,[z1,z2,z254,z4,z5,z413]),(0,[z1,z2,z1081,z7,z4,z6]),(0,[z1,z2,z226,z4,z5,z17]),(0,[z1,z2,z20,z7,z4,z191])],[(0,[z1,z2,z42,z7,z5,z132])]],
   [[(0,[z0,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1082]),(0,[z443,z1,z2,z20,z4,z6]),(0,[z0,z1,z2,z27,z97,z6]),(0,[z0,z1083,z2,z7,z4,z6])],[(0,[z1,z2,z7,z4,z1084,z6]),(0,[z2,z7,z4,z5,z17,z706])],[(0,[z1,z2,z7,z161,z5,z320]),(1,[z0,z1,z2,z511,z4])],[(0,[z0,z1,z2,z66,z4,z6]),(0,[z1,z2,z7,z5,z6,z798]),(0,[z1,z7,z50,z4,z5,z24]),(0,[z75,z1,z2,z4,z6,z22]),(0,[z1,z2,z4,z5,z6,z1085])],[(0,[z1086,z1,z2,z7,z4,z6]),(0,[z0,z1,z299,z2,z4,z6]),(0,[z804,z1,z2,z321,z4,z6])],[(0,[z1,z2,z7,z4,z1087,z6]),(0,[z1,z2,z1088,z4,z5,z6]),(0,[z1,z2,z7,z4,z1089,z5]),(0,[z1,z73,z65,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z862])],[(0,[z0,z1,z2,z7,z4,z228]),(0,[z1,z2,z20,z7,z4,z69]),(0,[z1,z2,z1090,z7,z4,z6])],[(0,[z1,z2,z7,z1091,z5,z6]),(0,[z1,z7,z4,z5,z846,z6]),(0,[z1,z2,z7,z265,z5,z10])],[(0,[z1,z580,z7,z4,z76,z6]),(0,[z1,z2,z7,z4,z1092,z6])],[(0,[z0,z1,z2,z7,z4,z320]),(0,[z167,z23,z7,z4,z5,z24]),(0,[z1,z2,z7,z4,z5,z1093]),(0,[z1,z2,z7,z514,z5,z17]),(0,[z1,z2,z7,z4,z121,z6])],[(0,[z535,z2,z7,z99,z5,z6]),(0,[z0,z1,z2,z7,z1011,z6])],[(0,[z194,z2,z7,z4,z124,z555]),(0,[z0,z1,z438,z2,z4,z6]),(0,[z0,z1,z2,z569,z4,z6])],[(0,[z1,z2,z7,z137,z5,z320]),(0,[z57,z1,z541,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z1094])],[(1,[z1,z7,z4,z729,z6]),(0,[z0,z1,z2,z262,z4,z6])],[(0,[z1,z7,z747,z4,z5,z24]),(0,[z0,z1,z2,z4,z78,z6])],[(0,[z1,z1095,z7,z4,z5,z6]),(0,[z0,z173,z1,z2,z4,z17]),(0,[z1,z2,z7,z4,z5,z1096]),(0,[z1,z2,z21,z7,z4,z22]),(0,[z1,z2,z7,z4,z5,z714])]],
   [[(0,[z1,z442,z7,z4,z5,z17]),(0,[z1,z2,z1097,z7,z5,z17]),(0,[z0,z1,z2,z7,z4,z191]),(0,[z1,z42,z7,z50,z5,z6])],[(0,[z1,z2,z7,z4,z5,z1098]),(0,[z1,z2,z7,z4,z5,z1099]),(0,[z177,z1,z7,z4,z729,z6]),(0,[z1,z1100,z2,z7,z4,z6])],[(0,[z167,z23,z7,z4,z5,z17]),(0,[z0,z1,z2,z704,z4,z6]),(0,[z1,z2,z7,z4,z5,z1101]),(0,[z1,z2,z270,z7,z4,z90])],[(0,[z1,z2,z7,z4,z1102,z6]),(0,[z0,z1,z2,z4,z131,z6]),(0,[z344,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z24,z859]),(0,[z0,z57,z1,z2,z51,z4]),(0,[z240,z1,z2,z7,z512,z6])],[(0,[z1,z2,z1103,z7,z4,z6]),(0,[z1,z1104,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z1105,z6])],[(0,[z1,z2,z1106,z7,z4,z6]),(0,[z1,z2,z7,z848,z4,z6]),(0,[z0,z1,z123,z7,z4,z6]),(0,[z1,z2,z1107,z4,z5,z6])],[(0,[z2,z3,z800,z4,z5,z6]),(0,[z1,z2,z7,z4,z283,z6]),(0,[z0,z1,z2,z4,z183,z6]),(0,[z1,z2,z20,z4,z212,z6]),(0,[z1,z1108,z7,z4,z5,z6])],[(0,[z162,z2,z3,z20,z4,z6]),(0,[z194,z2,z7,z4,z124,z17]),(0,[z1,z2,z7,z4,z5,z1109]),(0,[z1,z2,z7,z4,z6,z1110])],[(0,[z1,z442,z7,z4,z5,z413]),(0,[z1,z2,z130,z4,z5,z315]),(0,[z1,z2,z7,z4,z5,z1111])],[(0,[z1,z2,z848,z197,z4,z6]),(0,[z0,z33,z2,z7,z4,z17]),(0,[z111,z1,z348,z4,z5,z6]),(0,[z0,z1,z2,z4,z649,z6])],[(0,[z162,z2,z3,z4,z5,z24]),(0,[z1,z2,z7,z265,z5,z24]),(0,[z1,z2,z7,z4,z5,z1112]),(0,[z1,z2,z21,z4,z134,z22])],[(0,[z1,z2,z7,z4,z1113,z6]),(0,[z1,z2,z7,z4,z163,z24]),(0,[z1,z123,z7,z4,z283,z6]),(0,[z1,z153,z7,z4,z156,z6]),(0,[z0,z1,z7,z50,z4,z6])],[(0,[z1,z379,z7,z4,z5,z368])],[(0,[z162,z2,z3,z4,z5,z249]),(0,[z1,z2,z1114,z4,z5,z6]),(0,[z1,z2,z7,z4,z1115,z17]),(0,[z0,z1,z2,z16,z4,z6])],[(0,[z1,z2,z7,z4,z163,z249]),(0,[z632,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z5,z17,z1052]),(0,[z1,z30,z7,z4,z5,z601]),(0,[z0,z1,z2,z359,z4,z6]),(0,[z1,z2,z7,z4,z5,z1116])],[(0,[z1,z2,z338,z4,z5,z371]),(0,[z1,z2,z217,z7,z4,z17]),(0,[z2,z7,z4,z5,z17,z641]),(0,[z1,z2,z42,z20,z7,z10]),(0,[z1,z2,z7,z4,z78,z22])]],
   [[(0,[z1,z2,z7,z4,z1117,z6]),(0,[z1,z2,z321,z4,z283,z6]),(0,[z33,z2,z7,z4,z5,z17])],[(0,[z1118,z1,z2,z66,z4,z6]),(0,[z1119,z1,z2,z4,z5,z6]),(0,[z1,z2,z7,z4,z1120,z6]),(0,[z595,z1,z2,z7,z4,z77]),(0,[z57,z1,z2,z20,z4,z58])],[(0,[z1,z2,z7,z4,z1121,z5]),(0,[z68,z1,z2,z7,z4,z6])],[(0,[z539,z0,z1,z2,z4,z6]),(0,[z162,z2,z3,z4,z5,z17])],[(0,[z1,z2,z21,z7,z4,z70]),(0,[z0,z1,z296,z2,z4,z6])],[],[(0,[z1,z2,z1122,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1123]),(0,[z1,z2,z7,z4,z943,z6])],[(0,[z298,z782,z7,z4,z5,z6]),(0,[z0,z1,z2,z7,z4,z315]),(0,[z15,z2,z20,z7,z4,z17]),(0,[z0,z1,z2,z4,z420,z6]),(0,[z1,z378,z7,z4,z5,z32]),(0,[z1,z73,z748,z4,z5,z6]),(0,[z1,z2,z1124,z7,z4,z6]),(0,[z0,z1,z2,z4,z182,z6]),(0,[z1,z2,z7,z4,z1125,z5])],[(0,[z1,z2,z7,z4,z5,z1126]),(0,[z1,z2,z7,z1024,z5,z6]),(0,[z1127,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z337,z4,z6]),(0,[z585,z2,z231,z7,z4,z6])],[],[(0,[z1,z2,z7,z4,z1128,z6]),(0,[z1,z123,z7,z4,z5,z24]),(0,[z122,z2,z7,z99,z374,z6]),(0,[z1,z2,z1129,z7,z4,z5])],[(0,[z1,z7,z4,z5,z17,z1002]),(0,[z1,z2,z4,z93,z5,z24])],[(0,[z1,z2,z1130,z7,z4,z5]),(0,[z1,z2,z7,z4,z17,z544]),(0,[z0,z1,z2,z4,z97,z24])],[(0,[z1,z119,z7,z137,z5,z6]),(0,[z1,z2,z1131,z4,z5,z6]),(0,[z38,z2,z7,z284,z5,z469]),(0,[z1,z2,z4,z59,z5,z17]),(0,[z1,z2,z7,z4,z5,z1132])],[(0,[z1133,z1,z2,z7,z4,z6]),(0,[z38,z2,z7,z284,z5,z24]),(0,[z1,z2,z7,z4,z327,z6])],[(0,[z1134,z2,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1135])]],
   [[(0,[z1,z2,z66,z4,z5,z17]),(0,[z0,z1,z2,z7,z4,z371]),(1,[z2,z800,z4,z5,z6]),(0,[z2,z7,z4,z5,z785,z17])],[(0,[z247,z2,z7,z4,z5,z17]),(0,[z0,z1,z2,z333,z4,z6]),(0,[z0,z1059,z2,z7,z4,z6]),(0,[z1,z1070,z7,z4,z5,z6])],[(0,[z0,z1,z2,z7,z4,z357]),(0,[z1,z2,z7,z4,z118,z24]),(0,[z0,z1,z2,z16,z225,z6])],[(0,[z1,z2,z7,z4,z90,z70])],[(0,[z1,z2,z7,z4,z961,z6]),(0,[z1,z2,z7,z4,z5,z1136])],[(0,[z0,z1,z2,z3,z4,z17]),(0,[z111,z1,z102,z4,z5,z6]),(0,[z1,z45,z7,z514,z5,z32]),(0,[z1,z2,z606,z97,z5,z6]),(0,[z1,z2,z7,z4,z6,z1137]),(0,[z1,z2,z7,z4,z90,z714])],[(0,[z1,z2,z7,z4,z5,z1138]),(0,[z1,z2,z7,z4,z5,z517]),(0,[z1,z2,z7,z4,z1139,z6]),(0,[z1,z2,z380,z4,z5,z253]),(0,[z0,z1,z2,z7,z4,z836])],[],[(0,[z1,z2,z7,z4,z5,z363]),(0,[z1,z2,z7,z4,z1140,z6])],[(0,[z1,z2,z1141,z7,z4,z6])],[(0,[z1,z2,z1142,z338,z4,z6]),(0,[z1,z2,z7,z1143,z5,z6])],[(0,[z1,z2,z7,z4,z1144,z6]),(0,[z1,z2,z4,z1145,z5,z6]),(0,[z1,z2,z7,z4,z5,z1146]),(0,[z2,z7,z4,z680,z5,z17]),(0,[z0,z1,z2,z4,z588,z6]),(0,[z1,z2,z7,z4,z6,z1147]),(0,[z71,z1,z2,z327,z97,z6])],[(0,[z0,z1,z2,z270,z7,z4]),(0,[z0,z1,z558,z2,z4,z6])],[(0,[z1,z7,z4,z5,z6,z749]),(0,[z1,z2,z7,z4,z1148,z6]),(0,[z1,z30,z7,z27,z5,z52])],[(0,[z1,z2,z7,z4,z5,z1149]),(0,[z122,z2,z321,z99,z5,z6]),(0,[z122,z2,z7,z99,z5,z493]),(0,[z0,z1,z2,z147,z4,z6]),(0,[z1,z2,z270,z7,z4,z5])],[(0,[z68,z1,z2,z16,z4,z6]),(0,[z268,z2,z7,z4,z5,z17]),(0,[z2,z7,z4,z5,z272,z24])]],
   [[(0,[z167,z23,z66,z4,z5,z6]),(0,[z260,z1,z7,z4,z156,z6]),(0,[z1,z2,z7,z4,z24,z109]),(0,[z1,z2,z7,z4,z1150,z6])],[(0,[z1,z2,z1142,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1151]),(0,[z1,z2,z1152,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1153]),(0,[z1,z2,z7,z4,z5,z1154]),(0,[z1,z2,z7,z4,z1155,z6]),(0,[z1,z2,z7,z4,z5,z1156]),(0,[z0,z57,z1,z2,z4,z77])],[(0,[z1,z2,z1157,z4,z5,z6]),(0,[z1,z2,z7,z4,z6,z755]),(0,[z1,z221,z7,z27,z5,z6]),(0,[z1,z2,z511,z7,z117,z5]),(0,[z0,z1,z2,z4,z888,z6]),(0,[z1083,z2,z7,z4,z5,z6])],[(0,[z1,z2,z7,z4,z711,z17]),(0,[z1,z2,z7,z813,z5,z24]),(0,[z0,z1,z570,z2,z4,z6])],[(0,[z1,z2,z7,z4,z17,z1079])],[(0,[z162,z2,z3,z4,z163,z6])],[(0,[z1,z2,z7,z4,z5,z1158]),(0,[z1,z2,z7,z265,z5,z52])],[(0,[z1,z1159,z7,z4,z5,z6]),(0,[z0,z1,z831,z2,z7,z4])],[(0,[z1,z2,z7,z4,z5,z1160])],[(0,[z1,z2,z7,z4,z1161,z6]),(0,[z0,z1,z2,z4,z305,z6]),(0,[z1,z2,z7,z4,z729,z6])],[(0,[z1,z2,z16,z572,z5,z6])],[(0,[z1,z464,z7,z117,z5,z6]),(0,[z1,z2,z16,z225,z5,z24]),(0,[z1,z401,z2,z7,z4,z5]),(0,[z1,z2,z1162,z7,z4,z6])],[(0,[z1,z2,z7,z116,z791,z6])],[(0,[z0,z1,z2,z7,z4,z493]),(0,[z1,z2,z1163,z7,z4,z6])],[(0,[z0,z1,z516,z2,z4,z6]),(0,[z0,z1,z2,z254,z4,z6]),(0,[z1,z2,z7,z4,z5,z1164]),(0,[z1,z1165,z2,z7,z4,z6]),(0,[z1,z1166,z2,z7,z4,z5])],[(1,[z2,z7,z4,z839,z6]),(0,[z56,z2,z7,z4,z5,z17]),(0,[z1,z7,z50,z4,z5,z17]),(0,[z1,z2,z4,z191,z93,z5])]],
   [[(0,[z373,z1,z2,z4,z5,z481]),(0,[z1,z39,z7,z117,z5,z6]),(0,[z1,z2,z7,z4,z5,z1167]),(0,[z1,z2,z7,z4,z5,z1168])],[(0,[z1,z2,z7,z4,z5,z1169]),(0,[z1,z2,z4,z5,z784,z6])],[(0,[z1,z2,z7,z1170,z5,z6])],[(0,[z0,z1,z2,z112,z4,z6]),(0,[z901,z1,z2,z7,z4,z6])],[(0,[z1,z1171,z2,z7,z5,z6]),(0,[z1,z2,z1172,z7,z5,z6]),(0,[z98,z68,z2,z197,z4,z6]),(0,[z1,z2,z270,z7,z4,z22]),(0,[z57,z1,z2,z43,z4,z58]),(0,[z57,z1,z2,z451,z4,z5])],[(0,[z1,z2,z7,z1173,z5,z6]),(0,[z0,z1,z141,z2,z4,z6]),(0,[z1,z2,z62,z4,z623,z5])],[(0,[z1,z2,z7,z4,z5,z1174]),(0,[z1,z2,z7,z4,z5,z1175]),(0,[z1,z2,z7,z752,z5,z6])],[(0,[z1,z2,z151,z3,z4,z6]),(0,[z1,z2,z7,z227,z791,z6])],[(0,[z1,z2,z7,z1176,z5,z6]),(0,[z1,z2,z7,z4,z5,z1177]),(0,[z1,z2,z7,z4,z5,z1178]),(0,[z1179,z1,z2,z4,z5,z6])],[],[(0,[z1,z2,z7,z4,z1180,z5]),(0,[z75,z1,z2,z270,z4,z5])],[(0,[z1,z401,z2,z120,z7,z4]),(0,[z1,z39,z7,z502,z5,z6]),(0,[z0,z1,z2,z7,z4,z69])],[(0,[z1,z2,z7,z837,z5,z24]),(0,[z1,z2,z7,z4,z5,z1181]),(0,[z1,z2,z7,z4,z1182,z5])],[(0,[z1,z326,z270,z7,z4,z76])],[(0,[z298,z119,z7,z4,z5,z239]),(0,[z590,z2,z7,z4,z124,z6]),(0,[z656,z2,z7,z4,z5,z17]),(0,[z1,z541,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1183])],[(0,[z1,z2,z7,z1184,z5,z6]),(0,[z1,z2,z7,z4,z5,z1185]),(0,[z1,z2,z169,z4,z5,z420]),(0,[z1,z2,z1186,z4,z5,z6]),(0,[z1,z2,z16,z752,z5,z6])]],
   [[(0,[z1,z2,z7,z1187,z5,z6]),(0,[z1,z1188,z7,z4,z5,z6]),(0,[z0,z1,z2,z204,z4,z6])],[(0,[z1118,z1,z2,z7,z4,z6]),(0,[z1,z7,z4,z1189,z5,z6]),(0,[z1,z2,z7,z495,z116,z6]),(0,[z111,z1,z748,z4,z5,z6]),(0,[z1,z2,z7,z4,z90,z267])],[(0,[z71,z1,z2,z97,z5,z6]),(0,[z1,z2,z7,z4,z1190,z6])],[(0,[z1,z2,z7,z4,z283,z493]),(0,[z758,z1,z2,z4,z5,z17]),(0,[z1,z26,z7,z735,z5,z6]),(0,[z75,z1,z2,z4,z191,z5]),(0,[z1,z2,z7,z4,z1191,z6]),(0,[z0,z1,z2,z4,z361,z6])],[(0,[z1,z2,z7,z795,z5,z6])],[(0,[z1,z2,z254,z4,z5,z6]),(0,[z1,z2,z7,z4,z6,z1192])],[(0,[z1,z2,z7,z265,z5,z17]),(0,[z1,z2,z7,z4,z5,z1193]),(0,[z0,z1,z2,z7,z713,z6]),(0,[z0,z1,z2,z232,z4,z6]),(0,[z1,z1194,z2,z7,z4,z6])],[(0,[z1,z2,z1195,z7,z4,z6]),(0,[z298,z119,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z163,z17]),(0,[z1,z2,z7,z4,z5,z469]),(0,[z0,z1,z2,z7,z1143,z6])],[(0,[z1,z2,z7,z4,z5,z24]),(0,[z1,z45,z7,z4,z5,z368]),(0,[z1,z39,z7,z117,z5,z69]),(0,[z177,z1,z7,z4,z156,z6])],[(0,[z1,z2,z20,z7,z229,z6]),(0,[z1,z2,z270,z7,z4,z70])],[(0,[z1,z2,z1195,z66,z4,z6]),(0,[z1,z123,z254,z4,z5,z6]),(0,[z1,z2,z7,z5,z52,z132]),(0,[z1,z2,z1196,z4,z5,z6]),(0,[z1,z2,z20,z7,z1197,z6])],[(0,[z1,z2,z7,z4,z5,z1198]),(0,[z1,z1199,z2,z7,z4,z6])],[(0,[z75,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z7,z1091,z6]),(0,[z1,z2,z7,z4,z5,z883])],[(0,[z1,z2,z226,z4,z5,z6])],[(0,[z2,z800,z197,z4,z5,z6]),(0,[z0,z1,z30,z7,z4,z86])],[(0,[z1,z7,z117,z735,z5,z6])]],
   [[(0,[z1,z2,z20,z7,z514,z6]),(0,[z57,z1,z2,z7,z265,z5]),(0,[z1,z2,z7,z4,z5,z1200])],[(0,[z177,z75,z1,z2,z4,z6]),(0,[z1,z2,z7,z4,z1201,z6]),(0,[z57,z1,z2,z43,z4,z6])],[(0,[z1,z2,z321,z4,z5,z24]),(0,[z377,z1,z2,z21,z4,z22])],[(0,[z1,z7,z735,z27,z5,z6])],[(0,[z1,z2,z1202,z7,z4,z6]),(0,[z2,z7,z795,z99,z5,z6]),(0,[z1,z2,z4,z998,z70,z6]),(0,[z1,z2,z7,z4,z6,z1203]),(0,[z57,z1,z2,z4,z5,z812])],[(0,[z1,z442,z7,z4,z374,z6]),(0,[z1,z2,z231,z130,z4,z6]),(0,[z1,z2,z224,z7,z4,z24]),(0,[z1,z2,z7,z4,z5,z920])],[(0,[z1,z123,z7,z4,z5,z17]),(0,[z2,z7,z4,z795,z5,z6]),(0,[z1,z2,z62,z20,z4,z182])],[(0,[z1,z2,z7,z161,z80,z6]),(0,[z1204,z1,z2,z7,z4,z6]),(0,[z1,z2,z1205,z4,z5,z6]),(0,[z1,z2,z4,z93,z5,z17]),(0,[z1,z2,z20,z7,z911,z6])],[(0,[z0,z1,z2,z4,z97,z17]),(0,[z0,z1,z2,z4,z214,z6]),(0,[z1,z2,z7,z514,z5,z6]),(0,[z57,z1,z2,z261,z4,z5])],[(0,[z1,z2,z7,z1206,z5,z6]),(0,[z1207,z2,z7,z4,z5,z6]),(0,[z0,z1,z1208,z7,z4,z6])],[(0,[z38,z2,z7,z284,z5,z17]),(0,[z1,z2,z4,z5,z6,z856]),(0,[z0,z1,z2,z7,z4,z1004]),(0,[z1,z7,z50,z5,z52,z6])],[(0,[z1,z1208,z7,z4,z5,z6]),(0,[z1,z2,z7,z5,z17,z1068]),(0,[z0,z1,z2,z4,z253,z24]),(0,[z0,z1,z541,z7,z4,z6]),(0,[z619,z1,z2,z20,z4,z6]),(0,[z1,z2,z7,z461,z49,z6])],[(0,[z377,z1,z2,z4,z156,z6]),(0,[z1209,z1,z2,z7,z4,z6]),(0,[z0,z825,z2,z7,z4,z6])],[(0,[z111,z0,z1,z2,z229,z6]),(0,[z901,z1,z2,z4,z5,z6])],[(0,[z1,z123,z7,z4,z5,z413]),(0,[z1,z2,z912,z7,z4,z6]),(0,[z1,z2,z224,z7,z4,z17]),(0,[z0,z173,z1,z2,z4,z6]),(0,[z1,z2,z7,z4,z118,z17]),(0,[z0,z1,z2,z7,z4,z1005])],[(0,[z1,z442,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1210]),(0,[z1,z2,z1097,z7,z5,z6]),(0,[z0,z75,z1,z2,z4,z6]),(0,[z1,z2,z7,z1211,z5,z6]),(0,[z71,z1,z2,z752,z5,z6]),(0,[z1,z2,z7,z4,z6,z1212])]],
   [[(0,[z1,z2,z4,z784,z113,z6])],[(0,[z167,z23,z7,z4,z5,z6]),(0,[z1,z2,z7,z1213,z5,z6]),(0,[z1,z2,z7,z137,z80,z6]),(0,[z1,z2,z7,z4,z290,z24]),(0,[z695,z2,z7,z4,z5,z24]),(0,[z1038,z1,z2,z4,z5,z6]),(0,[z1214,z1,z2,z4,z5,z6])],[(0,[z1215,z1,z2,z338,z4,z6])],[(0,[z256,z2,z7,z4,z83,z6]),(0,[z1,z2,z7,z4,z5,z1216]),(0,[z1,z2,z16,z20,z225,z6])],[(0,[z1,z2,z7,z1217,z5,z6]),(0,[z1,z2,z20,z7,z137,z6]),(0,[z1,z442,z7,z99,z5,z6]),(0,[z1,z26,z20,z7,z27,z6]),(0,[z1,z2,z7,z4,z5,z846]),(0,[z377,z1,z2,z20,z4,z6])],[(0,[z1218,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z6,z1219])],[(0,[z1,z2,z7,z4,z1220,z6]),(0,[z194,z2,z7,z4,z124,z6]),(0,[z1,z2,z1221,z4,z5,z6])],[(0,[z1,z2,z7,z4,z1222,z6]),(0,[z377,z1,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z6,z467])],[(0,[z1,z2,z1223,z7,z4,z5]),(0,[z0,z439,z1,z2,z4,z6])],[(0,[z1215,z1,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z1224,z6]),(0,[z1,z442,z321,z4,z5,z6]),(1,[z1,z7,z735,z5,z6]),(0,[z0,z1,z2,z4,z759,z6]),(0,[z0,z11,z1,z2,z4,z6])],[(0,[z167,z23,z7,z4,z5,z320]),(0,[z1,z2,z7,z4,z24,z544]),(0,[z1,z2,z20,z7,z265,z6]),(0,[z0,z1,z2,z375,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1225]),(0,[z1,z438,z7,z27,z5,z6]),(1,[z1,z7,z4,z5,z846]),(0,[z0,z1,z2,z4,z478,z6])],[(0,[z1,z2,z7,z4,z1115,z6]),(0,[z458,z0,z1,z2,z4,z6])],[(0,[z1,z2,z7,z4,z5,z129]),(0,[z1,z2,z7,z4,z5,z1226])],[(0,[z1,z2,z217,z7,z4,z6]),(0,[z1,z2,z7,z4,z6,z714])],[(0,[z1,z2,z7,z4,z1227,z6])]],
   [[(0,[z1,z30,z7,z4,z5,z582])],[(0,[z1,z2,z146,z7,z5,z10]),(0,[z0,z57,z1,z2,z4,z24])],[(0,[z1,z2,z7,z161,z105,z6]),(0,[z1,z2,z7,z4,z5,z1228]),(0,[z162,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z4,z90,z6])],[(0,[z1,z2,z20,z7,z214,z6]),(0,[z1,z2,z1229,z4,z5,z6])],[(0,[z247,z2,z3,z4,z5,z6]),(0,[z1,z30,z7,z4,z5,z300]),(0,[z0,z1,z2,z546,z4,z6]),(0,[z1,z2,z20,z677,z4,z6]),(0,[z0,z1,z860,z7,z4,z6])],[(0,[z38,z2,z7,z284,z5,z233]),(0,[z0,z1,z2,z533,z4,z6]),(0,[z1,z2,z7,z4,z5,z1230])],[(0,[z0,z1,z2,z4,z113,z24]),(0,[z0,z1,z185,z2,z4,z6])],[(0,[z1,z2,z16,z225,z5,z17]),(0,[z1,z2,z4,z5,z182,z591])],[(0,[z1,z2,z7,z4,z5,z1231]),(0,[z1,z2,z7,z4,z1232,z6]),(0,[z1,z2,z7,z4,z1233,z5]),(0,[z1,z2,z921,z7,z4,z24]),(0,[z693,z0,z1,z2,z4,z6])],[(0,[z539,z1,z102,z4,z5,z6]),(0,[z0,z1,z2,z426,z4,z6]),(0,[z1,z2,z7,z4,z6,z976])],[(0,[z1,z2,z7,z4,z1234,z5]),(0,[z1,z308,z7,z4,z5,z53]),(0,[z1,z73,z20,z65,z4,z6]),(0,[z1235,z2,z7,z4,z5,z6]),(1,[z901,z1,z2,z4,z6])],[(0,[z1,z2,z7,z4,z5,z1236]),(0,[z1,z2,z7,z4,z5,z812])],[(0,[z1,z2,z7,z137,z105,z6]),(0,[z1237,z1,z2,z7,z4,z6]),(0,[z1,z2,z4,z1238,z5,z6]),(0,[z1,z2,z7,z4,z1239,z5]),(0,[z111,z1,z101,z102,z4,z5]),(0,[z1,z2,z4,z59,z5,z6]),(0,[z57,z1,z2,z4,z5,z58])],[(0,[z1,z2,z7,z4,z5,z1240]),(0,[z1,z2,z217,z4,z150,z6]),(0,[z1,z2,z1241,z4,z5,z6]),(0,[z1,z2,z7,z4,z1242,z5])],[(0,[z1,z2,z254,z4,z374,z6]),(0,[z0,z1,z2,z255,z4,z6])],[(0,[z1,z2,z66,z4,z5,z6]),(0,[z1,z2,z20,z7,z161,z6]),(0,[z2,z7,z4,z839,z5,z6]),(0,[z2,z7,z4,z5,z785,z6]),(0,[z0,z1,z2,z4,z113,z17]),(0,[z1,z2,z7,z398,z5,z350])]],
   [[],[(0,[z1,z2,z7,z4,z374,z24])],[(0,[z0,z1,z2,z492,z4,z6]),(0,[z0,z1,z2,z4,z166,z97]),(0,[z1,z2,z7,z791,z49,z6])],[(0,[z1,z2,z197,z4,z309,z6]),(0,[z1,z2,z7,z1067,z5,z6]),(0,[z1,z2,z1243,z4,z5,z6]),(0,[z1,z2,z7,z265,z5,z132])],[(0,[z1,z2,z7,z4,z1244,z6]),(0,[z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z7,z4,z5,z1245]),(0,[z0,z1,z2,z4,z6,z544])],[(0,[z1,z2,z7,z4,z5,z1246]),(0,[z1,z2,z7,z4,z5,z866]),(0,[z1,z2,z7,z4,z1247,z6])],[(0,[z111,z1,z224,z102,z4,z6]),(0,[z1,z158,z7,z117,z5,z6])],[(0,[z266,z2,z7,z4,z5,z17]),(0,[z111,z0,z1,z2,z214,z6]),(0,[z1,z2,z7,z4,z1248,z6]),(0,[z1,z2,z7,z4,z1249,z6]),(0,[z0,z1,z2,z406,z4,z6]),(0,[z1,z2,z20,z7,z51,z52])],[(0,[z1,z2,z66,z4,z5,z320]),(0,[z1,z2,z7,z4,z5,z555]),(0,[z459,z2,z7,z4,z124,z6]),(0,[z35,z2,z7,z4,z5,z17]),(0,[z1,z2,z7,z4,z1250,z6])],[(0,[z1,z2,z7,z4,z1251,z6]),(0,[z1,z2,z840,z7,z5,z17]),(0,[z1,z2,z184,z7,z4,z22]),(0,[z1,z1252,z2,z7,z4,z6]),(0,[z1,z2,z7,z4,z5,z1253]),(0,[z1,z1254,z7,z4,z5,z6]),(0,[z0,z1,z2,z42,z7,z10])],[],[(0,[z1,z2,z7,z4,z5,z239]),(0,[z1,z7,z1255,z4,z5,z6]),(1,[z1,z2,z7,z791,z6])],[(0,[z782,z23,z7,z4,z5,z6]),(0,[z1,z2,z7,z4,z5,z1256]),(0,[z1,z2,z7,z4,z5,z1257])],[(0,[z194,z2,z7,z4,z124,z315]),(0,[z1,z2,z7,z1197,z5,z6])],[(0,[z1,z2,z7,z4,z5,z249]),(0,[z111,z0,z1,z102,z4,z6]),(0,[z1,z2,z7,z4,z5,z132]),(0,[z0,z1,z26,z7,z27,z6]),(0,[z1,z45,z7,z4,z5,z614])],[(0,[z1,z2,z7,z4,z6,z1258])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 510).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1010).take 375) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1385)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [510, 500, 375] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 157).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 157).take 160).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 317).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 475).take 37).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [157, 160, 158, 37] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_40433

theorem PEqualNP.Outside.L_meta_40433 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4242590912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4242590912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40433.solve