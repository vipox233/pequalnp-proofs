import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38681

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4205505160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x500004898401212a#64 ++ 0x28000244c2009095#64 ++ 0xed008f9f8c1fe3ff#64 ++ 0xf68047cfc60ff1ff#64 : BitVec 256),
   (0x200732243b148c94#64 ++ 0x900399121d8a464a#64 ++ 0xde0f7264ff149c9f#64 ++ 0xef07b9327f8a4e4f#64 : BitVec 256),
   (0x40b05c58d1671719#64 ++ 0x20582e2c68b38b8c#64 ++ 0xbff07c78f3e71f19#64 ++ 0xdff83e3c79f38f8c#64 : BitVec 256),
   (0x805b807602b81ac1#64 ++ 0xc02dc03b015c0d60#64 ++ 0x7fff807f03f81fe1#64 ++ 0xbfffc03f81fc0ff0#64 : BitVec 256),
   (0x016dfb0003dec000#64 ++ 0x00b6fd8001ef6000#64 ++ 0xf9ffff8003ffe001#64 ++ 0x7cffffc001fff000#64 : BitVec 256),
   (0x027eefffec000000#64 ++ 0x013f77fff6000000#64 ++ 0xfa7ffffffc000000#64 ++ 0xfd3ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [10, 3]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 6]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x127f706070000000 0x093fb83038000000

def z2 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xde0f7264ff149c9f 0xef07b9327f8a4e4f

def z3 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07c78f3e71f19 0xdff83e3c79f38f8c

def z4 : W := mkw 0x41fdff58d3ffd719 0x20feffac69ffeb8c 0xfffffff8f3ffff19 0xfffffffc79ffff8c

def z5 : W := mkw 0x500004898401212a 0x28000244c2009095 0xed008f9f8c1fe3ff 0xf68047cfc60ff1ff

def z6 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff807f03f81fe1 0xbfffc03f81fc0ff0

def z7 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x10ff700003e00000 0x087fb80001f00000

def z8 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0400000003149c9f 0x02000000018a4e4f

def z9 : W := mkw 0x0006222428000000 0x0003111214000000 0xda0f7264fc000000 0xed07b9327e000000

def z10 : W := mkw 0x8012007600201ac1 0xc009003b00100d60 0x0600007f00001fe0 0x8300003f80000ff0

def z11 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z12 : W := mkw 0xf05fb6ffbfbdbfff 0xf82fdb7fdfdedfff 0xffffffffffffffff 0xffffffffffffffff

def z13 : W := mkw 0x60b25c7cf9671f9d 0xb0592e3e7cb38fce 0xbff07c7cffe71f9f 0xdff83e3e7ff38fcf

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0xe9008f80001fe001 0x748047c0000ff000

def z15 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0ffffffffffff 0xfff87fffffffffff

def z16 : W := mkw 0x026cef89ec000000 0x013677c4f6000000 0xf87fff80fc000000 0x7c3fffc07e000000

def z17 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc1fe3ff 0xffbffffffe0ff1ff

def z18 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x12ff006003e01c00 0x097f803001f00e00

def z19 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x120f706073001c00 0x0907b83039800e00

def z20 : W := mkw 0x700736adbf15adbe 0xb8039b56df8ad6df 0xff0fffffff1fffff 0xff87ffffff8fffff

def z21 : W := mkw 0x60a47e08f947851c 0x30523f047ca3c28e 0x80007e00fc07801e 0x40003f007e03c00f

def z22 : W := mkw 0x216ffb243bdecc94 0x90b7fd921def664a 0xffffffe4fffffc9f 0xfffffff27ffffe4f

def z23 : W := mkw 0x0000048984000000 0x00000244c2000000 0x0000001f8c000000 0x8000000fc6000000

def z24 : W := mkw 0x40b67e7cf9671719 0x205b3f3e7cb38b8c 0xffff7e7cffe71f19 0xffffbf3e7ff38f8c

def z25 : W := mkw 0x005a807600000000 0x002d403b00000000 0x7a7f807f00000000 0xbd3fc03f80000000

def z26 : W := mkw 0x5101100003dfe12a 0x2880880001eff095 0x0580000003ffe3ff 0x02c0000001fff1ff

def z27 : W := mkw 0x4080000000631309 0x2040000000318984 0x0180000000e30300 0x00c0000000718180

def z28 : W := mkw 0x024ea3a72c000000 0x012751d396000000 0xda0ff3e7fc000000 0xed07f9f3fe000000

def z29 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xbff07c78f3ffffff 0xdff83e3c79ffffff

def z30 : W := mkw 0x2004320039048414 0x100219001c82420a 0x80007200fc04801e 0x400039007e02400f

def z31 : W := mkw 0x01247b000146c000 0x00923d8000a36000 0x80007f800007e000 0x40003fc00003f000

def z32 : W := mkw 0x42f8dddbd5671719 0x217c6eedeab38b8c 0xbff0fdfbf3e71f19 0xdff87efdf9f38f8c

def z33 : W := mkw 0x4080100011671719 0x2040080008b38b8c 0x0580000003e71f19 0x02c0000001f38f8c

def z34 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfe7ffffffc14809f 0xff3ffffffe0a404f

def z35 : W := mkw 0x40a05c08d1470518 0x20502e0468a3828c 0x80007c00f0070018 0x40003e007803800c

def z36 : W := mkw 0x500004898401212a 0x28000244c2009095 0x21008d9b000b6360 0x108046cd8005b1b0

def z37 : W := mkw 0x020423812c000000 0x010211c096000000 0x000003800c000000 0x000001c006000000

def z38 : W := mkw 0x0148810000884000 0x00a4408000442000 0x0000818000086000 0x000040c000043000

def z39 : W := mkw 0x8058805200a81241 0x402c402900540920 0x21f0801b00e80360 0x10f8400d807401b0

def z40 : W := mkw 0x827eefffeca81241 0x413f77fff6540920 0xfbfffffffce80360 0xfdfffffffe7401b0

def z41 : W := mkw 0x0006222428000000 0x0003111214000000 0x120f706070000000 0x0907b83038000000

def z42 : W := mkw 0x0010005000201201 0x0008002800100900 0x3ff0007803e01f01 0x9ff8003c01f00f80

def z43 : W := mkw 0x0003002402100880 0x8001801201080440 0x120f006003001c00 0x0907803001800e00

def z44 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xbbf07c6073e71c01 0x5df83e3039f38e00

def z45 : W := mkw 0x0278c95240000000 0x013c64a920000000 0x0070000000000000 0x0038000000000000

def z46 : W := mkw 0x500000000001212a 0x2800000000009095 0x05000000001fe3ff 0x02800000000ff1ff

def z47 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff848fffe09f 0xfeffffc247fff04f

def z48 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc0002048c14809f 0xe6000102460a404f

def z49 : W := mkw 0x0278cddbc4000000 0x013c66ede2000000 0xe8708f9f8c000000 0xf43847cfc6000000

def z50 : W := mkw 0x014da3000298c000 0x00a6d180014c6000 0x400f83800018e000 0x2007c1c0000c7000

def z51 : W := mkw 0x0168c90000ca4000 0x00b4648000652000 0x21f08d8000eb6000 0x10f846c00075b000

def z52 : W := mkw 0x005a807600000000 0x002d403b00000000 0x7f7f807f001803e1 0xbfbfc03f800c01f0

def z53 : W := mkw 0x825b84ffeeb81ac1 0xc12dc27ff75c0d60 0x7fff807ffff81fe1 0xbfffc03ffffc0ff0

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x21008d80000b6000 0x108046c00005b000

def z55 : W := mkw 0x516dff8987dfe12a 0x28b6ffc4c3eff095 0xfdffff9f8fffe3ff 0xfeffffcfc7fff1ff

def z56 : W := mkw 0xa00732243bbc9ed5 0xd00399121dde4f6a 0xdf8f7264fffc9fff 0xefc7b9327ffe4fff

def z57 : W := mkw 0x817ffb7603fedac1 0xc0bffdbb01ff6d60 0xffffffff03ffffe1 0xffffffff81fffff0

def z58 : W := mkw 0x60b15c58d3779f9d 0xb058ae2c69bbcfce 0xbff07c78f3f79f9f 0xdff83e3c79fbcfcf

def z59 : W := mkw 0x805b8076029808c0 0xc02dc03b014c0460 0x7a7f807f001800e0 0xbd3fc03f800c0070

def z60 : W := mkw 0x0049800002980000 0x0024c000014c0000 0x79ff800003f80001 0x3cffc00001fc0000

def z61 : W := mkw 0x52fefffffd67373b 0x297f7ffffeb39b9d 0xffffffffffffffff 0xffffffffffffffff

def z62 : W := mkw 0x2101100013decc94 0x9080880009ef664a 0x0580000003fffc9f 0x02c0000001fffe4f

def z63 : W := mkw 0x40900458c0211309 0x2048022c60108984 0x0000001800000300 0x0000000c00000180

def z64 : W := mkw 0x1000008104002022 0x0800004082001011 0x6d00839f0c18e3e7 0xb68041cf860c71f3

def z65 : W := mkw 0x0101100003dec000 0x0080880001ef6000 0x0180000003ffe001 0x00c0000001fff000

def z66 : W := mkw 0x8000000000a81241 0x4000000000540920 0x0180000000e80360 0x00c00000007401b0

def z67 : W := mkw 0x017dff58c3dec000 0x00beffac61ef6000 0xfbfffff8f3ffe001 0xfdfffffc79fff000

def z68 : W := mkw 0x00304c58c0201201 0x0018262c60100900 0xbff07c78f3e01f01 0xdff83e3c79f00f80

def z69 : W := mkw 0x70043689bd05a53e 0x38021b44de82d29f 0xed00ff9ffc1fe3ff 0xf6807fcffe0ff1ff

def z70 : W := mkw 0x027eefffec201201 0x013f77fff6100900 0xffffffffffe01f01 0xfffffffffff00f80

def z71 : W := mkw 0x41b15c58d3ffd719 0x20d8ae2c69ffeb8c 0xbff07c78f3ffff19 0xdff83e3c79ffff8c

def z72 : W := mkw 0x2002002438000c94 0x900100121c00064a 0x06000064fc001c9e 0x830000327e000e4f

def z73 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x16f07078f3e01f18 0x8b78383c79f00f8c

def z74 : W := mkw 0x0006222428000000 0x0003111214000000 0xde0f7264fc14809f 0xef07b9327e0a404f

def z75 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07ff8ffe7ff1f 0xdff83ffc7ff3ff8f

def z76 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x33ff807b03e81f60 0x19ffc03d81f40fb0

def z77 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x92f07c60f3e71c18 0x49783e3079f38e0c

def z78 : W := mkw 0x40b04c58d0631719 0x2058262c68318b8c 0x27f00c78f0e31f18 0x93f8063c78718f8c

def z79 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fff8f3ffff19 0xfff87ffc79ffff8c

def z80 : W := mkw 0x1000008104002022 0x0800004082001011 0x000003800c00e006 0x000001c006007003

def z81 : W := mkw 0x0020580001460000 0x00102c0000a30000 0xb9f07c0003e70001 0x5cf83e0001f38000

def z82 : W := mkw 0x216dfb0013decc94 0x90b6fd8009ef664a 0xfdffff8003fffc9f 0x7effffc001fffe4f

def z83 : W := mkw 0x5278cddbc401212a 0x293c66ede2009095 0x21708d9b000b6360 0x10b846cd8005b1b0

def z84 : W := mkw 0x004b802402980880 0x8025c012014c0440 0x7fff806403f81c81 0xbfffc03201fc0e40

def z85 : W := mkw 0x42a47f89fd470518 0x21523fc4fea3828c 0x80007f80fc070018 0x40003fc07e03800c

def z86 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x79fff00003f80001 0x3cfff80001fc0000

def z87 : W := mkw 0x210732243bdecc94 0x908399121def664a 0xdf8f7264fffffc9f 0xefc7b9327ffffe4f

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a007060f0000000 0xcd00383078000000

def z89 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xb9ff7c0003e70001 0x5cffbe0001f38000

def z90 : W := mkw 0x037eefffecca4000 0x01bf77fff6652000 0xfbfffffffceb6000 0xfdfffffffe75b000

def z91 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x607f8f9f0c000000 0x303fc7cf86000000

def z92 : W := mkw 0xa05fb2763bbc9ed5 0xd02fd93b1dde4f6a 0xfffff27ffffc9fff 0xfffff93ffffe4fff

def z93 : W := mkw 0x016dff8987dec000 0x00b6ffc4c3ef6000 0xf9ffff9f8fffe001 0xfcffffcfc7fff000

def z94 : W := mkw 0x006cef8984000000 0x003677c4c2000000 0xf87fff9f8c000000 0xfc3fffcfc6000000

def z95 : W := mkw 0x00304c58c0000000 0x0018262c60000000 0xba707c78f0000000 0xdd383e3c78000000

def z96 : W := mkw 0x42fefffffd671719 0x217f7ffffeb38b8c 0xffffffffffe71f19 0xfffffffffff38f8c

def z97 : W := mkw 0x0000100011040410 0x0000080008820208 0x1200706073001c00 0x0900383039800e00

def z98 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x12f0706073e01c00 0x0978383039f00e00

def z99 : W := mkw 0x021004dbc4000000 0x0108026de2000000 0x0000001b00000000 0x0000000d80000000

def z100 : W := mkw 0x40fadc7ed1671719 0x207d6e3f68b38b8c 0xfffffc7ff3e71f19 0xfffffe3ff9f38f8c

def z101 : W := mkw 0x2004320039048414 0x100219001c82420a 0xcc007204fc14809f 0xe60039027e0a404f

def z102 : W := mkw 0x027cefdbc4000000 0x013e77ede2000000 0xf87fff9b00000000 0x7c3fffcd80000000

def z103 : W := mkw 0x227ffb767b148c94 0x913ffdbb3d8a464a 0x127f706073001c00 0x093fb83039800e00

def z104 : W := mkw 0x016ceb0000ca4000 0x00b6758000652000 0xf9ffff8000eb6000 0x7cffffc00075b000

def z105 : W := mkw 0x700114899715adbe 0xb8008a44cb8ad6df 0xed008f9f8f1fffff 0xf68047cfc78fffff

def z106 : W := mkw 0x0003002402100880 0x8001801201080440 0x5e0f006403101c81 0xaf07803201880e40

def z107 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff07e7cfff79f9f 0xfff83f3e7ffbcfcf

def z108 : W := mkw 0x804b8026029808c0 0xc025c013014c0460 0x400f8007001800e0 0x2007c003800c0070

def z109 : W := mkw 0xa05b907613bc9ed5 0xd02dc83b09de4f6a 0x7fff807f03fc9fff 0xbfffc03f81fe4fff

def z110 : W := mkw 0x40b04c58c0631309 0x2058262c60318984 0xadf00c1880e70319 0xd6f8060c4073818c

def z111 : W := mkw 0x0048800000880000 0x0024400000440000 0x21f0800000e80000 0x10f8400000740000

def z112 : W := mkw 0x516dfb0003dfe12a 0x28b6fd8001eff095 0xfdffff8003ffe3ff 0x7effffc001fff1ff

def z113 : W := mkw 0x827fefffeeb81ac1 0xc13ff7fff75c0d60 0xfffffffffff81fe1 0xfffffffffffc0ff0

def z114 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf8ffff8003e00000 0x7c7fffc001f00000

def z115 : W := mkw 0x027acdffc4000000 0x013d66ffe2000000 0x7a7f8dff00000000 0xbd3fc6ff80000000

def z116 : W := mkw 0xc092047ed0211fd9 0xe049023f68108fec 0x0600007ff0001ff8 0x8300003ff8000ffc

def z117 : W := mkw 0x016deb0002dac000 0x00b6f580016d6000 0x61ff8f8000fbe000 0x30ffc7c0007df000

def z118 : W := mkw 0x0000100011040410 0x0000080008820208 0x9e007060f3041c19 0xcf00383079820e0c

def z119 : W := mkw 0x516dff8987dfe12a 0x28b6ffc4c3eff095 0xf9ffff808fffe01f 0x7cffffc047fff00f

def z120 : W := mkw 0x827feb766ab81ac1 0xc13ff5bb355c0d60 0x12ff706073e01c00 0x097fb83039f00e00

def z121 : W := mkw 0x500004898401212a 0x28000244c2009095 0x0400001f8c0003fe 0x8200000fc60001ff

def z122 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x160f7064ff001c9e 0x8b07b8327f800e4f

def z123 : W := mkw 0x02246f89ec000000 0x011237c4f6000000 0x80007f80fc000000 0x40003fc07e000000

def z124 : W := mkw 0x0005320003148000 0x00029900018a4000 0xd80f720003148001 0x6c07b900018a4000

def z125 : W := mkw 0x024ea3a72c000000 0x012751d396000000 0x400f83870c000000 0x2007c1c386000000

def z126 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0xba7f7c78f0000000 0xdd3fbe3c78000000

def z127 : W := mkw 0xa04fb2263b9c8cd4 0xd027d9131dce466a 0xde0ff267ff1c9cff 0xef07f933ff8e4e7f

def z128 : W := mkw 0x2001000002108884 0x9000800001084442 0x0000000000108086 0x0000000000084043

def z129 : W := mkw 0x40b04c58c0631309 0x2058262c60318984 0xbbf07c78f0e30300 0xddf83e3c78718180

def z130 : W := mkw 0x700726adae11a9ae 0xb8039356d708d4d7 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z131 : W := mkw 0x8010005200201241 0x4008002900100920 0x0000001b00000360 0x0000000d800001b0

def z132 : W := mkw 0x80020026000008c0 0xc001001300000460 0x00000007000000e0 0x0000000380000070

def z133 : W := mkw 0x00246b0000000000 0x0012358000000000 0x80007f8000000000 0x40003fc000000000

def z134 : W := mkw 0x010010000146c000 0x0080080000a36000 0x000000000007e000 0x000000000003f000

def z135 : W := mkw 0x8049800002b81ac1 0xc024c000015c0d60 0x7dff800003f81fe1 0x3effc00001fc0ff0

def z136 : W := mkw 0x0002002428000000 0x0001001214000000 0x02000064fc000000 0x810000327e000000

def z137 : W := mkw 0x00a0580051460410 0x00502c0028a30208 0x0000700070000000 0x0000380038000000

def z138 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x31fffd8003eb6000 0x18fffec001f5b000

def z139 : W := mkw 0x500004898401212a 0x28000244c2009095 0x4400839f8c18e3fe 0xa20041cfc60c71ff

def z140 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfb7ffffffc1fe001 0xfdbffffffe0ff000

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z142 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xff7ffffffc070319 0xffbffffffe03818c

def z143 : W := mkw 0x4181100013ffd719 0x20c0880009ffeb8c 0x0580000003ffff19 0x02c0000001ffff8c

def z144 : W := mkw 0x004a802600000000 0x0025401300000000 0x400f800700000000 0x2007c00380000000

def z145 : W := mkw 0x005b807602100880 0x802dc03b01080440 0x7e7f807f03101c81 0xbf3fc03f81880e40

def z146 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xfa7fffe070000000 0x7d3ffff038000000

def z147 : W := mkw 0x0278cddbc4000000 0x013c66ede2000000 0x20708d9b00000000 0x103846cd80000000

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x6d00801f001803e1 0xb680400f800c01f0

def z149 : W := mkw 0x827fefffeeb81ac1 0xc13ff7fff75c0d60 0xfaffffffffe01c00 0xfd7ffffffff00e00

def z150 : W := mkw 0x0002002400000000 0x0001001200000000 0x5a0f006400000000 0xad07803200000000

def z151 : W := mkw 0x500004898401212a 0x28000244c2009095 0xe8008f9f8c07e01e 0xf40047cfc603f00f

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0xed00821f8c1c83ff 0xf680410fc60e41ff

def z153 : W := mkw 0x021204ffec000000 0x0109027ff6000000 0x0200007ffc000000 0x8100003ffe000000

def z154 : W := mkw 0x037fffffefdec000 0x01bffffff7ef6000 0xfbffffffffffe001 0xfdfffffffffff000

def z155 : W := mkw 0x815fa37602b8dac1 0xc0afd1bb015c6d60 0x7fff83ff03f8ffe1 0xbfffc1ff81fc7ff0

def z156 : W := mkw 0x0000048984000000 0x00000244c2000000 0xe8008f9f8c000000 0xf40047cfc6000000

def z157 : W := mkw 0x60b77e7cfb779f9d 0xb05bbf3e7dbbcfce 0xffff7e7cfff79f9f 0xffffbf3e7ffbcfcf

def z158 : W := mkw 0x216dfb003bdec414 0x10b6fd801def620a 0xf9ffff80ffffe01f 0x7cffffc07ffff00f

def z159 : W := mkw 0x007cef58c0000000 0x003e77ac60000000 0xfa7ffff8f0000000 0xfd3ffffc78000000

def z160 : W := mkw 0x500004898401212a 0x28000244c2009095 0xec008f9f8c0003fe 0xf60047cfc60001ff

def z161 : W := mkw 0x817ffb7603fedac1 0xc0bffdbb01ff6d60 0x7ffff07f03f81fe1 0xbffff83f81fc0ff0

def z162 : W := mkw 0xd05b807602b93beb 0xe82dc03b015c9df5 0x7fff807f03ffffff 0xbfffc03f81ffffff

def z163 : W := mkw 0x50a05c89d547253a 0x28502e44eaa3929d 0x80007f80fc07e01e 0x40003fc07e03f00f

def z164 : W := mkw 0xc0fbdc7ed3ff1fd9 0xe07dee3f69ff8fec 0xfffffc7ff3ff1ff9 0xfffffe3ff9ff8ffc

def z165 : W := mkw 0xa17ffb763bfeded5 0xd0bffdbb1dff6f6a 0xffffffffffffffff 0xffffffffffffffff

def z166 : W := mkw 0x227eeffffc000c94 0x913f77fffe00064a 0xfe7ffffffc001c9e 0xff3ffffffe000e4f

def z167 : W := mkw 0x0058805200000000 0x002c402900000000 0x2070801b00000000 0x1038400d80000000

def z168 : W := mkw 0x500004898401212a 0x28000244c2009095 0x80000f808c07e01e 0x400007c04603f00f

def z169 : W := mkw 0x0020580001460000 0x00102c0000a30000 0x10f0700003e00000 0x0878380001f00000

def z170 : W := mkw 0x40a05c08d1470518 0x20502e0468a3828c 0x9e007c60f3071c19 0xcf003e3079838e0c

def z171 : W := mkw 0x0000000000000000 0x0000000000000000 0x40008007001800e0 0x20004003800c0070

def z172 : W := mkw 0x8001000002b81ac1 0xc0008000015c0d60 0x0080000003e01c00 0x0040000001f00e00

def z173 : W := mkw 0x40b04c58c0631309 0x2058262c60318984 0x21f00c1800e30300 0x10f8060c00718180

def z174 : W := mkw 0x1000008104002022 0x0800004082001011 0x400083870c18e0e6 0x200041c3860c7073

def z175 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xff7ffffffc1803e1 0xffbffffffe0c01f0

def z176 : W := mkw 0xa05fb2763bbc9ed5 0xd02fd93b1dde4f6a 0xdeff7264fff49c9f 0xef7fb9327ffa4e4f

def z177 : W := mkw 0x037effffed46c000 0x01bf7ffff6a36000 0xfa7ffffffc07e000 0xfd3ffffffe03f000

def z178 : W := mkw 0x200722242a108884 0x9003911215084442 0x400f02040c108086 0x2007810206084043

def z179 : W := mkw 0x024ea7afac000000 0x012753d7d6000000 0xe80f8f9f8c000000 0xf407c7cfc6000000

def z180 : W := mkw 0x0010005000000000 0x0008002800000000 0x3a70007800000000 0x9d38003c00000000

def z181 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x61ff801f00f803e0 0x30ffc00f807c01f0

def z182 : W := mkw 0x016cfb000146c000 0x00b67d8000a36000 0xf87fff800007e000 0x7c3fffc00003f000

def z183 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x3ff0707873e01f01 0x9ff8383c39f00f80

def z184 : W := mkw 0x20277a243b568c94 0x9013bd121dab464a 0xffff7e64fff79c9f 0xffffbf327ffbce4f

def z185 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x927f7fe0fc000000 0x493fbff07e000000

def z186 : W := mkw 0x700736adbf15adbe 0xb8039b56df8ad6df 0xde0f7fe4ff17fc9f 0xef07bff27f8bfe4f

def z187 : W := mkw 0x200310243b148c94 0x900188121d8a464a 0x06000064ff149c9f 0x830000327f8a4e4f

def z188 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfb7ffffffc0b6360 0xfdbffffffe05b1b0

def z189 : W := mkw 0x006ceb0000000000 0x0036758000000000 0xf87fff8000000000 0x7c3fffc000000000

def z190 : W := mkw 0x8058805200a81241 0x402c402900540920 0x3ff0807b03e81f61 0x9ff8403d81f40fb0

def z191 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xda0f7264ff001c00 0xed07b9327f800e00

def z192 : W := mkw 0xc081100013ff1fd9 0xe040880009ff8fec 0x0580000003ff1ff9 0x02c0000001ff8ffc

def z193 : W := mkw 0x034fa3a72e98c000 0x01a7d1d3974c6000 0x400f83870c18e000 0x2007c1c3860c7000

def z194 : W := mkw 0x827bcdffc6b81ac1 0xc13de6ffe35c0d60 0x7fff8dff03f81fe1 0xbfffc6ff81fc0ff0

def z195 : W := mkw 0x0001000002100880 0x8000800001080440 0x0400000003101c81 0x0200000001880e40

def z196 : W := mkw 0x500004898401212a 0x28000244c2009095 0x25008d9f8c0b63fe 0x928046cfc605b1ff

def z197 : W := mkw 0x0000000000000000 0x0000000000000000 0xed008f9f001fe3e1 0xf68047cf800ff1f0

def z198 : W := mkw 0x4000040880010108 0x2000020440008084 0x80000c0080070018 0x400006004003800c

def z199 : W := mkw 0x4000040880010108 0x2000020440008084 0xed008c1f801f03f9 0xf680460fc00f81fc

def z200 : W := mkw 0x20377e7cfb148c94 0x901bbf3e7d8a464a 0xfe7f7e7cff149c9f 0xff3fbf3e7f8a4e4f

def z201 : W := mkw 0x825fa3f72eb81ac1 0xc12fd1fb975c0d60 0x7fff83ff0ff81fe1 0xbfffc1ff87fc0ff0

def z202 : W := mkw 0x0168c90000ca4000 0x00b4648000652000 0xe9f08f8000ffe001 0x74f847c0007ff000

def z203 : W := mkw 0x805b84ff86b81ac1 0xc02dc27fc35c0d60 0xffff8fff8ff81fe1 0xffffc7ffc7fc0ff0

def z204 : W := mkw 0x2004320039048414 0x100219001c82420a 0x0000700070000000 0x0000380038000000

def z205 : W := mkw 0x4000040880010108 0x2000020440008084 0xad000c1880070319 0xd680060c4003818c

def z206 : W := mkw 0x02204d89c4000000 0x011026c4e2000000 0x00000d8000000000 0x000006c000000000

def z207 : W := mkw 0x804b8026029808c0 0xc025c013014c0460 0x5e0f806703181ce1 0xaf07c033818c0e70

def z208 : W := mkw 0x0001000002980000 0x00008000014c0000 0x0180000003f80001 0x00c0000001fc0000

def z209 : W := mkw 0x40900458d0211719 0x2048022c68108b8c 0x06000078f0001f18 0x8300003c78000f8c

def z210 : W := mkw 0xd05b84ff86b93beb 0xe82dc27fc35c9df5 0xffff8fff8fffffff 0xffffc7ffc7ffffff

def z211 : W := mkw 0x227fffffff148c94 0x913fffffff8a464a 0xfe7fffffff149c9f 0xff3fffffff8a4e4f

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x05000000001803e1 0x02800000000c01f0

def z213 : W := mkw 0x8001000002b81ac1 0xc0008000015c0d60 0x0580000003f81fe1 0x02c0000001fc0ff0

def z214 : W := mkw 0x204fb2243b9c8c94 0x9027d9121dce464a 0xfffff264fffc9c9f 0xfffff9327ffe4e4f

def z215 : W := mkw 0x4080100011470518 0x2040080008a3828c 0x0000000000070018 0x000000000003800c

def z216 : W := mkw 0x2006322439048414 0x100319121c82420a 0xda0f7264fc04801e 0xed07b9327e02400f

def z217 : W := mkw 0xd01204ff84213beb 0xe809027fc2109df5 0x0600007f8c001ffe 0x8300003fc6000fff

def z218 : W := mkw 0x2000000010000c94 0x900000000800064a 0x0400000000001c9e 0x0200000000000e4f

def z219 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0x17f0706073e71f19 0x0bf8383039f38f8c

def z220 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0xbaf07c78f3e01c00 0xdd783e3c79f00e00

def z221 : W := mkw 0x0030485040000000 0x0018242820000000 0x1270706070000000 0x0938383038000000

def z222 : W := mkw 0x0049800002980000 0x0024c000014c0000 0xf9ff8f8003ffe001 0x7cffc7c001fff000

def z223 : W := mkw 0x0080100011661611 0x0040080008b30b08 0x0080000003e01c00 0x0040000001f00e00

def z224 : W := mkw 0x200722242a108884 0x9003911215084442 0xda0f7264fc108086 0xed07b9327e084043

def z225 : W := mkw 0x00b0485040621201 0x0058242820310900 0x00f0000000e00000 0x0078000000700000

def z226 : W := mkw 0x814fa3260298c8c0 0xc0a7d193014c6460 0x400f83870018e0e0 0x2007c1c3800c7070

def z227 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x25f00c1803e71f19 0x12f8060c01f38f8c

def z228 : W := mkw 0x0020580011460410 0x00102c0008a30208 0xbff07c60f3e71c19 0xdff83e3079f38e0c

def z229 : W := mkw 0x0168d90001ce4000 0x00b46c8000e72000 0xb9f0fd8003ef6001 0x5cf87ec001f7b000

def z230 : W := mkw 0x80fbd87653fe1ed1 0xc07dec3b29ff0f68 0x12ff706073e01c00 0x097fb83039f00e00

def z231 : W := mkw 0x227fefffee108884 0x913ff7fff7084442 0xfa7ffffffc108086 0xfd3ffffffe084043

def z232 : W := mkw 0x500004898401212a 0x28000244c2009095 0xe9008f9f8c0b6360 0xf48047cfc605b1b0

def z233 : W := mkw 0x700110001315adbe 0xb8008800098ad6df 0x05000000031fffff 0x02800000018fffff

def z234 : W := mkw 0xd001000002b93beb 0xe8008000015c9df5 0x0580000003ffffff 0x02c0000001ffffff

def z235 : W := mkw 0x0105320003dec000 0x0082990001ef6000 0xd98f720003ffe001 0x6cc7b90001fff000

def z236 : W := mkw 0x816dfb0003fedac1 0xc0b6fd8001ff6d60 0xfdffff8003ffffe1 0x7effffc001fffff0

def z237 : W := mkw 0x2006222438000c94 0x900311121c00064a 0xde0f7264fc001c9e 0xef07b9327e000e4f

def z238 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xfff0ffffffe71f19 0xfff87ffffff38f8c

def z239 : W := mkw 0x0049800002980000 0x0024c000014c0000 0x10ff000003e00000 0x087f800001f00000

def z240 : W := mkw 0x52246f89ec01212a 0x291237c4f6009095 0xed00ff9ffc1fe3ff 0xf6807fcffe0ff1ff

def z241 : W := mkw 0x608732243b779f9d 0xb04399121dbbcfce 0xdf8f7264fff79f9f 0xefc7b9327ffbcfcf

def z242 : W := mkw 0xa001100013bc9ed5 0xd000880009de4f6a 0x0580000003fc9fff 0x02c0000001fe4fff

def z243 : W := mkw 0x51fdffd9d7fff73b 0x28feffecebfffb9d 0xffffffffffffffff 0xffffffffffffffff

def z244 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x33f07c7873e31f00 0x19f83e3c39f18f80

def z245 : W := mkw 0x50b04cd9c463332b 0x2858266ce2319995 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z246 : W := mkw 0x40b57e58d3779719 0x205abf2c69bbcb8c 0xffff7e78f3f79f19 0xffffbf3c79fbcf8c

def z247 : W := mkw 0x037dffdbc7dec000 0x01beffede3ef6000 0xf9ffff9b03ffe001 0x7cffffcd81fff000

def z248 : W := mkw 0x4080100011671719 0x2040080008b38b8c 0x9f807060f3e71f19 0xcfc0383079f38f8c

def z249 : W := mkw 0x42feefffec631309 0x217f77fff6318984 0xfbfffffffce30300 0xfdfffffffe718180

def z250 : W := mkw 0x5168cd8984cb612a 0x28b466c4c265b095 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z251 : W := mkw 0x51247f898547e12a 0x28923fc4c2a3f095 0xed00ff9f8c1fe3ff 0xf6807fcfc60ff1ff

def z252 : W := mkw 0x0005320013148410 0x00029900098a4208 0xde0f7260f3149c19 0xef07b930798a4e0c

def z253 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfe7ffffffc0003fe 0xff3ffffffe0001ff

def z254 : W := mkw 0xa01732763b349ed5 0xd00b993b1d9a4f6a 0xde0f727fff149fff 0xef07b93fff8a4fff

def z255 : W := mkw 0x0000100011040410 0x0000080008820208 0x0400000003041c19 0x0200000001820e0c

def z256 : W := mkw 0x227ffb767b148c94 0x913ffdbb3d8a464a 0xde7f7264ff149c9f 0xef3fb9327f8a4e4f

def z257 : W := mkw 0xc0f8cc5ac0eb1349 0x607c662d607589a4 0x21f08c1b00eb0360 0x10f8460d807581b0

def z258 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfa7ffffffc07e01e 0xfd3ffffffe03f00f

def z259 : W := mkw 0x21247b003946c414 0x10923d801ca3620a 0x80007f80fc07e01e 0x40003fc07e03f00f

def z260 : W := mkw 0x500014899505253a 0x28000a44ca82929d 0xff00ffffff1fffff 0xff807fffff8fffff

def z261 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xc00f7204fc14809e 0x6007b9027e0a404f

def z262 : W := mkw 0x01247b000146c000 0x00923d8000a36000 0xe900ff80001fe001 0x74807fc0000ff000

def z263 : W := mkw 0xd001048986b93beb 0xe8008244c35c9df5 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z264 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xda7f7264fc000000 0xed3fb9327e000000

def z265 : W := mkw 0x007acc7ec0000000 0x003d663f60000000 0xfa7ffc7ff0000000 0xfd3ffe3ff8000000

def z266 : W := mkw 0x0068c90000000000 0x0034648000000000 0x20708d8000000000 0x103846c000000000

def z267 : W := mkw 0xc1ffff7ed3ffdfd9 0xe0ffffbf69ffefec 0xfffffffff3fffff9 0xfffffffff9fffffc

def z268 : W := mkw 0x41b47f58d167d719 0x20da3fac68b3eb8c 0xbff07ff8f3e7ff19 0xdff83ffc79f3ff8c

def z269 : W := mkw 0xa04fa2262a9888c4 0xd027d113154c4462 0x400f82070c1880e6 0x2007c103860c4073

def z270 : W := mkw 0x40901458d1251719 0x20480a2c68928b8c 0x9e007078f3041f19 0xcf00383c79820f8c

def z271 : W := mkw 0x40b05c58c1671309 0x20582e2c60b38984 0xb9f07c1803e70301 0x5cf83e0c01f38180

def z272 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x160f706073149c9f 0x0b07b830398a4e4f

def z273 : W := mkw 0x824fa3a72e9808c0 0xc127d1d3974c0460 0x400f83870c1800e0 0x2007c1c3860c0070

def z274 : W := mkw 0x516dff8987dfe12a 0x28b6ffc4c3eff095 0xf9ffff9b03ffe361 0x7cffffcd81fff1b0

def z275 : W := mkw 0x0005220002108000 0x0002910001084000 0x400f020000108000 0x2007810000084000

def z276 : W := mkw 0x0101100003dec000 0x0080880001ef6000 0x0080000003e00000 0x0040000001f00000

def z277 : W := mkw 0x01257b000356c000 0x0092bd8001ab6000 0xd80f7f800317e001 0x6c07bfc0018bf000

def z278 : W := mkw 0x0000048984000000 0x00000244c2000000 0xed008f9f8c1803e1 0xf68047cfc60c01f0

def z279 : W := mkw 0x0010005000201201 0x0008002800100900 0x7ff0807f03f81fe1 0xbff8403f81fc0ff0

def z280 : W := mkw 0x500000810401212a 0x2800004082009095 0x450083870c1fe3ff 0x228041c3860ff1ff

def z281 : W := mkw 0x8058805200a81241 0x402c402900540920 0x6df0801f00f803e1 0xb6f8400f807c01f0

def z282 : W := mkw 0x201732743b349e95 0x900b993a1d9a4f4a 0xffff727cfff49f9f 0xffffb93e7ffa4fcf

def z283 : W := mkw 0x4080140891671719 0x20400a0448b38b8c 0xad800c1883e71f19 0xd6c0060c41f38f8c

def z284 : W := mkw 0xd05884db84a9336b 0x682c426dc25499b5 0xedf08f9f8cffe3ff 0xf6f847cfc67ff1ff

def z285 : W := mkw 0x509004d9d421373b 0x2848026cea109b9d 0x0600007ffc001ffe 0x8300003ffe000fff

def z286 : W := mkw 0x4000040880010108 0x2000020440008084 0x0400001880000318 0x8200000c4000018c

def z287 : W := mkw 0x200532003b148414 0x100299001d8a420a 0xd80f7200ff14801f 0x6c07b9007f8a400f

def z288 : W := mkw 0x804b8026029808c0 0xc025c013014c0460 0x6d0f801f001803e1 0xb687c00f800c01f0

def z289 : W := mkw 0x026eefafec000000 0x013777d7f6000000 0xc00fff87fc000000 0x6007ffc3fe000000

def z290 : W := mkw 0x237fffffffdecc94 0x91bfffffffef664a 0xfffffffffffffc9f 0xfffffffffffffe4f

def z291 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x16ff007f03e01fe0 0x8b7f803f81f00ff0

def z292 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x440f02040f149c9f 0x22078102078a4e4f

def z293 : W := mkw 0x500004088001212a 0x2800020440009095 0xad000c18801fe3ff 0xd680060c400ff1ff

def z294 : W := mkw 0x40b05c58d1470518 0x20582e2c68a3828c 0xba707c78f0070018 0xdd383e3c7803800c

def z295 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x7a7ff07f70000000 0xbd3ff83fb8000000

def z296 : W := mkw 0x817ffb7603fedac1 0xc0bffdbb01ff6d60 0xfbffffe003fffc01 0x7dfffff001fffe00

def z297 : W := mkw 0x006eeb2428000000 0x0037759214000000 0xfa7fffe4fc000000 0xfd3ffff27e000000

def z298 : W := mkw 0x40900458d0211719 0x2048022c68108b8c 0xaf000c78f0071f19 0xd780063c78038f8c

def z299 : W := mkw 0x0005320003148000 0x00029900018a4000 0x100f700003000000 0x0807b80001800000

def z300 : W := mkw 0x216ffb243bdecc94 0x90b7fd921def664a 0x12ff706073e01c00 0x097fb83039f00e00

def z301 : W := mkw 0x5278cddbc401212a 0x293c66ede2009095 0xed708f9f8c1fe3ff 0xf6b847cfc60ff1ff

def z302 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x9e007060f3149c9f 0xcf003830798a4e4f

def z303 : W := mkw 0x200736adbf148c94 0x90039b56df8a464a 0xfe0fffffff149c9f 0xff07ffffff8a4e4f

def z304 : W := mkw 0x0010005000201201 0x0008002800100900 0x12f0006003e01c00 0x0978003001f00e00

def z305 : W := mkw 0x80fbd87653fe1ed1 0xc07dec3b29ff0f68 0x7ffff07f73f81fe1 0xbffff83fb9fc0ff0

def z306 : W := mkw 0x42b25cfffd671719 0x21592e7ffeb38b8c 0xbff07c7fffe71f19 0xdff83e3ffff38f8c

def z307 : W := mkw 0xc0b15c58d3ff1fd9 0xe058ae2c69ff8fec 0xbff07c78f3ff1ff9 0xdff83e3c79ff8ffc

def z308 : W := mkw 0x500000000001212a 0x2800000000009095 0x01000000000b6360 0x008000000005b1b0

def z309 : W := mkw 0x2002002438000c94 0x900100121c00064a 0xce000264fc149c9f 0xe70001327e0a4e4f

def z310 : W := mkw 0x506cef898401212a 0x283677c4c2009095 0xfd7fff9f8c1fe3ff 0xfebfffcfc60ff1ff

def z311 : W := mkw 0x804b802602b81ac1 0xc025c013015c0d60 0x458f800703f81fe1 0x22c7c00381fc0ff0

def z312 : W := mkw 0x500304ad861129aa 0xa8018256c30894d5 0xff0f8fff8f1fffff 0xff87c7ffc78fffff

def z313 : W := mkw 0x005ea27628000000 0x002f513b14000000 0xfa7ff27ffc000000 0xfd3ff93ffe000000

def z314 : W := mkw 0xc2ffffffffff1fd9 0xe17fffffffff8fec 0xffffffffffff1ff9 0xffffffffffff8ffc

def z315 : W := mkw 0x62ffffffff779f9d 0xb17fffffffbbcfce 0xfffffffffff79f9f 0xfffffffffffbcfcf

def z316 : W := mkw 0x2001100013148c94 0x90008800098a464a 0xcc0002048f149c9f 0xe6000102478a4e4f

def z317 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xfa7ffffffc18e0e6 0xfd3ffffffe0c7073

def z318 : W := mkw 0x41a47f08d147c518 0x20d23f8468a3e28c 0x80007f80f007e018 0x40003fc07803f00c

def z319 : W := mkw 0x0001100003148000 0x00008800018a4000 0x0000000003148001 0x00000000018a4000

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000000014809f 0x02000000000a404f

def z321 : W := mkw 0x509004d9d421373b 0x2848026cea109b9d 0xef008ffffc1fffff 0xf78047fffe0fffff

def z322 : W := mkw 0x017dfb5003fed201 0x00befda801ff6900 0xfffffff803ffff01 0xfffffffc01ffff80

def z323 : W := mkw 0x0378cddbc4ca4000 0x01bc66ede2652000 0x21f08d9b00eb6000 0x10f846cd8075b000

def z324 : W := mkw 0xa05fb2763bbc9ed5 0xd02fd93b1dde4f6a 0x12ff706073e01c00 0x097fb83039f00e00

def z325 : W := mkw 0x02fefffffd661611 0x017f7ffffeb30b08 0xfaffffffffe01c00 0xfd7ffffffff00e00

def z326 : W := mkw 0x4000000000010108 0x2000000000008084 0x0500000000070319 0x028000000003818c

def z327 : W := mkw 0x024ea32628000000 0x0127519314000000 0x000f000000000000 0x0007800000000000

def z328 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xff0ff27fff1c9fff 0xff87f93fff8e4fff

def z329 : W := mkw 0x1000000000002022 0x0800000000001011 0x000000000018e0e6 0x00000000000c7073

def z330 : W := mkw 0x014da3000298c000 0x00a6d180014c6000 0xe90f8f80001fe001 0x7487c7c0000ff000

def z331 : W := mkw 0x821204ffec201ac1 0xc109027ff6100d60 0x0600007ffc001fe0 0x8300003ffe000ff0

def z332 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fc7ff3ff1ff9 0xfff87e3ff9ff8ffc

def z333 : W := mkw 0x216ffb243bdecc94 0x90b7fd921def664a 0xdeff7264fff49c9f 0xef7fb9327ffa4e4f

def z334 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xda0f726073149c01 0x6d07b930398a4e00

def z335 : W := mkw 0x214fa3242a98c884 0x90a7d192154c6442 0x400f83840c18e086 0x2007c1c2060c7043

def z336 : W := mkw 0x224fb3a73f148c94 0x9127d9d39f8a464a 0xde0ff3e7ff149c9f 0xef07f9f3ff8a4e4f

def z337 : W := mkw 0x114da3810698e022 0x08a6d1c0834c7011 0x400f83870c18e0e6 0x2007c1c3860c7073

def z338 : W := mkw 0x0020480000000000 0x0010240000000000 0xb8707c0000000000 0x5c383e0000000000

def z339 : W := mkw 0x0003002402100880 0x8001801201080440 0xde0f02648f149c9f 0xef078132478a4e4f

def z340 : W := mkw 0x02246b0068000000 0x0112358034000000 0x0000700070000000 0x0000380038000000

def z341 : W := mkw 0x016dfb0013dec410 0x00b6fd8009ef6208 0xffffffe0f3fffc19 0xfffffff079fffe0c

def z342 : W := mkw 0x02246f89ec000000 0x011237c4f6000000 0xe800ff9ffc000000 0xf4007fcffe000000

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0xed008f848c1fe09f 0xf68047c2460ff04f

def z344 : W := mkw 0x1000048984002022 0x08000244c2001011 0xe8008f9f8c18e0e6 0xf40047cfc60c7073

def z345 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0x527ff3e77c000000 0x293ff9f3be000000

def z346 : W := mkw 0x22247f89fd048414 0x11123fc4fe82420a 0x80007f80fc04801e 0x40003fc07e02400f

def z347 : W := mkw 0x4000040880010108 0x2000020440008084 0x21000c1800030300 0x1080060c00018180

def z348 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800020000148001 0x64000100000a4000

def z349 : W := mkw 0x02324cffec000000 0x0119267ff6000000 0xba707c7ffc000000 0xdd383e3ffe000000

def z350 : W := mkw 0x0000008104000000 0x0000004082000000 0x400083870c000000 0x200041c386000000

def z351 : W := mkw 0x70043689bd05a53e 0x38021b44de82d29f 0x80007f80fc07e01e 0x40003fc07e03f00f

def z352 : W := mkw 0x2000000038000414 0x100000001c00020a 0x00000000fc00001e 0x000000007e00000f

def z353 : W := mkw 0x805a807600a81241 0x402d403b00540920 0x7bff807f00e80360 0xbdffc03f807401b0

def z354 : W := mkw 0x006deb0002980000 0x0036f580014c0000 0xf9ffff8003f80001 0x7cffffc001fc0000

def z355 : W := mkw 0x0149900003dec000 0x00a4c80001ef6000 0x79ff800003ffe001 0x3cffc00001fff000

def z356 : W := mkw 0x005a807600201201 0x002d403b00100900 0x7fff807f03e01f01 0xbfffc03f81f00f80

def z357 : W := mkw 0x200722242a108884 0x9003911215084442 0x5e0f02640f109c87 0xaf07813207884e43

def z358 : W := mkw 0x01fdfb5053fed611 0x00fefda829ff6b08 0xfbffffe073fffc01 0x7dfffff039fffe00

def z359 : W := mkw 0x021626ffec000000 0x010b137ff6000000 0xda0f727ffc000000 0xed07b93ffe000000

def z360 : W := mkw 0x0000000000000000 0x0000000000000000 0x800002008c04801e 0x400001004602400f

def z361 : W := mkw 0x50304cd9c401212a 0x2818266ce2009095 0xff70fffffc1fe3ff 0xffb87ffffe0ff1ff

def z362 : W := mkw 0x036ffba72fdec000 0x01b7fdd397ef6000 0xf9ffff870fffe001 0x7cffffc387fff000

def z363 : W := mkw 0x0012007600000000 0x0009003b00000000 0x0200007f00000000 0x8100003f80000000

def z364 : W := mkw 0x0000100001040000 0x0000080000820000 0x9800700003040001 0x4c00380001820000

def z365 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x5eff006403f01c81 0xaf7f803201f80e40

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x01000000001fe001 0x00800000000ff000

def z367 : W := mkw 0x8048800200880040 0x4024400100440020 0x0000800300080060 0x0000400180040030

def z368 : W := mkw 0x1000008104002022 0x0800004082001011 0xe9008f870c1fe0e7 0x748047c3860ff073

def z369 : W := mkw 0x0000048984000000 0x00000244c2000000 0xec008f9f8c14809f 0xf60047cfc60a404f

def z370 : W := mkw 0x805fa2762ab81ac1 0xc02fd13b155c0d60 0xfffff27ffff81fe1 0xfffff93ffffc0ff0

def z371 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x327ffdfb70000000 0x193ffefdb8000000

def z372 : W := mkw 0x40b35c7cd3771f99 0xa059ae3e69bb8fcc 0xffff7c7cf3f71f99 0xffffbe3e79fb8fcc

def z373 : W := mkw 0x4080000010211719 0x2040000008108b8c 0x0400000000001f18 0x0200000000000f8c

def z374 : W := mkw 0x0003102413140c90 0x80018812098a0648 0xde0f7064f3141c99 0xef07b832798a0e4c

def z375 : W := mkw 0xa27fffffffbc9ed5 0xd13fffffffde4f6a 0xfffffffffffc9fff 0xfffffffffffe4fff

def z376 : W := mkw 0x2005320013148c94 0x90029900098a464a 0xdc0f720003149c9f 0x6e07b900018a4e4f

def z377 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xff0fffe4ff1ffc9f 0xff87fff27f8ffe4f

def z378 : W := mkw 0x40304c58c0010108 0x2018262c60008084 0xbf707c78f0070319 0xdfb83e3c7803818c

def z379 : W := mkw 0x0010105011241611 0x0008082808920b08 0xbff07078f3e41f19 0xdff8383c79f20f8c

def z380 : W := mkw 0x827feb766ab81ac1 0xc13ff5bb355c0d60 0x7ffff07f73f81fe1 0xbffff83fb9fc0ff0

def z381 : W := mkw 0x4000040880010108 0x2000020440008084 0xed008f98801fe319 0xf68047cc400ff18c

def z382 : W := mkw 0x037fefffee98c000 0x01bff7fff74c6000 0xfa7ffffffc18e000 0xfd3ffffffe0c7000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x400083800018e000 0x200041c0000c7000

def z384 : W := mkw 0x807bcc7ec2b81ac1 0xc03de63f615c0d60 0xfffffc7ff3f81fe1 0xfffffe3ff9fc0ff0

def z385 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff0fdfbf3ef7f79 0xdff87efdf9f7bfbc

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000f800007e000 0x400007c00003f000

def z387 : W := mkw 0x805b907613bc1ed1 0xc02dc83b09de0f68 0xfffff07ff3fc1ff9 0xfffff83ff9fe0ffc

def z388 : W := mkw 0x2002002438000c94 0x900100121c00064a 0x0200006070001c00 0x0100003038000e00

def z389 : W := mkw 0x216ffb243bdecc94 0x90b7fd921def664a 0xfbffffe073fffc01 0x7dfffff039fffe00

def z390 : W := mkw 0x0000100011040410 0x0000080008820208 0x80007000f0040018 0x400038007802000c

def z391 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff827f8ffc9fff 0xffffc13fc7fe4fff

def z392 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0000000003001c00 0x0000000001800e00

def z393 : W := mkw 0x43ffffffffffd719 0x21ffffffffffeb8c 0xffffffffffffff19 0xffffffffffffff8c

def z394 : W := mkw 0x02fefb7679661611 0x017f7dbb3cb30b08 0x12ff706073e01c00 0x097fb83039f00e00

def z395 : W := mkw 0x0003002402100880 0x8001801201080440 0x400f000400100080 0x2007800200080040

def z396 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x9ef07060f3e41c19 0xcf78383079f20e0c

def z397 : W := mkw 0x500004898401212a 0x28000244c2009095 0xc0008f878c1fe0fe 0x600047c3c60ff07f

def z398 : W := mkw 0x0004220000000000 0x0002110000000000 0xd80f720000000000 0x6c07b90000000000

def z399 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff8fff03ffffe1 0xffffc7ff81fffff0

def z400 : W := mkw 0x006ceb0000000000 0x0036758000000000 0xf97fff80001fe001 0x7cbfffc0000ff000

def z401 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xd8ff720003f48001 0x6c7fb90001fa4000

def z402 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7bff806003f81c01 0x3dffc03001fc0e00

def z403 : W := mkw 0x500004898401212a 0x28000244c2009095 0x0000001b00000360 0x0000000d800001b0

def z404 : W := mkw 0x027effffed460000 0x013f7ffff6a30000 0xfbffffffffe70001 0xfdfffffffff38000

def z405 : W := mkw 0x40900458d0211719 0x2048022c68108b8c 0x3ff00078f3e01f19 0x9ff8003c79f00f8c

def z406 : W := mkw 0x500004898401212a 0x28000244c2009095 0x6d00801f8c1803ff 0xb680400fc60c01ff

def z407 : W := mkw 0x00257a0003568000 0x0012bd0001ab4000 0xf9ff7e0003f78001 0x7cffbf0001fbc000

def z408 : W := mkw 0x42fefffffd470518 0x217f7ffffea3828c 0xfa7ffffffc070018 0xfd3ffffffe03800c

def z409 : W := mkw 0xd05884db84a9336b 0x682c426dc25499b5 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z410 : W := mkw 0x807bd87603fe1ac1 0xc03dec3b01ff0d60 0xfffffc7f03ff1fe1 0xfffffe3f81ff8ff0

def z411 : W := mkw 0x41f8cd58c0eb5309 0x20fc66ac6075a984 0x21f08d9800eb6300 0x10f846cc0075b180

def z412 : W := mkw 0x0020580001460000 0x00102c0000a30000 0x80007c0000070000 0x40003e0000038000

def z413 : W := mkw 0x0101100003dec000 0x0080880001ef6000 0xe9808f8003ffe001 0x74c047c001fff000

def z414 : W := mkw 0x01257b0003dec000 0x0092bd8001ef6000 0x81807f8003ffe001 0x40c03fc001fff000

def z415 : W := mkw 0xc0f8dc5ad1ef1759 0x607c6e2d68f78bac 0xbff0fc7bf3ef1f79 0xdff87e3df9f78fbc

def z416 : W := mkw 0x500004898401212a 0x28000244c2009095 0x84000f9f8c07e3fe 0xc20007cfc603f1ff

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e00006003001c01 0x8f00003001800e00

def z418 : W := mkw 0x0000048984000000 0x00000244c2000000 0xe9008f9f8c1fe001 0xf48047cfc60ff000

def z419 : W := mkw 0x016ffb242bdec000 0x00b7fd9215ef6000 0xfbffffe4ffffe001 0xfdfffff27ffff000

def z420 : W := mkw 0x8011005002b81ac1 0xc0088028015c0d60 0x3ff0007803f81fe1 0x9ff8003c01fc0ff0

def z421 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x11ff700003ffe001 0x08ffb80001fff000

def z422 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7aff807f03e01c00 0xbd7fc03f81f00e00

def z423 : W := mkw 0x5168cd8984cb612a 0x28b466c4c265b095 0xedf08f9f8cffe3ff 0xf6f847cfc67ff1ff

def z424 : W := mkw 0x524ea7afac01212a 0x292753d7d6009095 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z425 : W := mkw 0x0090005050201611 0x0048002828100b08 0x0200006070001c00 0x0100003038000e00

def z426 : W := mkw 0x016cfb0001cec000 0x00b67d8000e76000 0xa1f0ff8000efe000 0x50f87fc00077f000

def z427 : W := mkw 0x41edff08d3dfc518 0x20f6ff8469efe28c 0xf9ffff80f3ffe019 0x7cffffc079fff00c

def z428 : W := mkw 0x42feff7ef9671719 0x217f7fbf7cb38b8c 0xbfff7c78f3e71f19 0xdfffbe3c79f38f8c

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00000080040019 0xc60000004002000c

def z430 : W := mkw 0x508014899567373b 0x28400a44cab39b9d 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z431 : W := mkw 0x1000008104002022 0x0800004082001011 0xcc0083878c1ce0ff 0xe60041c3c60e707f

def z432 : W := mkw 0xd17fffff87fffbeb 0xe8bfffffc3fffdf5 0xffffffff8fffffff 0xffffffffc7ffffff

def z433 : W := mkw 0xd04b84af869929ea 0xe825c257c34c94f5 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z434 : W := mkw 0x40b04c58d0211719 0x2058262c68108b8c 0xbe707c78f0001f18 0xdf383e3c78000f8c

def z435 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800801f00000000 0xb400400f80000000

def z436 : W := mkw 0x0100000000ca4000 0x0080000000652000 0x0180000000eb6000 0x00c000000075b000

def z437 : W := mkw 0x500004898401212a 0x28000244c2009095 0x000000008c00001e 0x000000004600000f

def z438 : W := mkw 0x500004898401212a 0x28000244c2009095 0xe9008f808c1fe01f 0x748047c0460ff00f

def z439 : W := mkw 0x020200a72c000000 0x0101005396000000 0x000000070c000000 0x0000000386000000

def z440 : W := mkw 0x026eeba72c000000 0x013775d396000000 0xf87fff870c000000 0x7c3fffc386000000

def z441 : W := mkw 0x02266fadec000000 0x011337d6f6000000 0xda0f7fe4fc000000 0xed07bff27e000000

def z442 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x50fff38003f8e000 0x287ff9c001fc7000

def z443 : W := mkw 0x40205c0881470108 0x20102e0440a38084 0xbdf07c1883e70319 0xdef83e0c41f3818c

def z444 : W := mkw 0x00304cd9c4000000 0x0018266ce2000000 0xfa70fffffc000000 0xfd387ffffe000000

def z445 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x90ff7f8003e7e000 0x487fbfc001f3f000

def z446 : W := mkw 0x837fffffeffedac1 0xc1bffffff7ff6d60 0xffffffffffffffe1 0xfffffffffffffff0

def z447 : W := mkw 0x521204ffec01212a 0x2909027ff6009095 0x0600007ffc0003fe 0x8300003ffe0001ff

def z448 : W := mkw 0x0000040880000000 0x0000020440000000 0xa8000c1880000000 0xd400060c40000000

def z449 : W := mkw 0x500000000001212a 0x2800000000009095 0x04000000000003fe 0x02000000000001ff

def z450 : W := mkw 0x0000000010000410 0x0000000008000208 0x06000060f0001c18 0x8300003078000e0c

def z451 : W := mkw 0x6092047cf8211f9d 0xb049023e7c108fce 0x0600007cfc001f9e 0x8300003e7e000fcf

def z452 : W := mkw 0x0000048984000000 0x00000244c2000000 0x80000f808c000000 0x400007c046000000

def z453 : W := mkw 0x500004898401212a 0x28000244c2009095 0xad000f988c07e31f 0xd68007cc4603f18f

def z454 : W := mkw 0x200732242b148884 0x90039912158a4442 0xd80f72040f148087 0x6c07b902078a4043

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x39f0000003e00001 0x1cf8000001f00000

def z456 : W := mkw 0x0010005000201201 0x0008002800100900 0x0600007800001f00 0x8300003c00000f80

def z457 : W := mkw 0x500626adac01212a 0x28031356d6009095 0xff0ffffffc1fe3ff 0xff87fffffe0ff1ff

def z458 : W := mkw 0x6097367cfb359f9d 0xb04b9b3e7d9acfce 0xde0f727cff149f9f 0xef07b93e7f8a4fcf

def z459 : W := mkw 0x4000040880010108 0x2000020440008084 0xed000e1c8c17839f 0xf680070e460bc1cf

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x2d00001800000301 0x9680000c00000180

def z461 : W := mkw 0x0049800002980000 0x0024c000014c0000 0x400f800000180000 0x2007c000000c0000

def z462 : W := mkw 0x0120490000424000 0x0090248000212000 0x00000d8000036000 0x000006c00001b000

def z463 : W := mkw 0x50205c898547212a 0x28102e44c2a39095 0xfdf0ff9f8fffe3ff 0xfef87fcfc7fff1ff

def z464 : W := mkw 0x40f9dc58d3ff1719 0x207cee2c69ff8b8c 0xfffffc78f3ff1f19 0xfffffe3c79ff8f8c

def z465 : W := mkw 0x521204ffec01212a 0x2909027ff6009095 0xef008ffffc1fe3ff 0xf78047fffe0ff1ff

def z466 : W := mkw 0x0004220028000000 0x0002110014000000 0x80007200fc000000 0x400039007e000000

def z467 : W := mkw 0x805fb27603bc9ac1 0xc02fd93b01de4d60 0xfffff27f03fc9fe1 0xfffff93f81fe4ff0

def z468 : W := mkw 0x52246f89ec01212a 0x291237c4f6009095 0x80007f80fc07e01e 0x40003fc07e03f00f

def z469 : W := mkw 0x508010001167373b 0x2840080008b39b9d 0x0580000003ffffff 0x02c0000001ffffff

def z470 : W := mkw 0x0278cddbc4000000 0x013c66ede2000000 0xba70fdfbf0000000 0xdd387efdf8000000

def z471 : W := mkw 0x40a05c08d1671719 0x20502e0468b38b8c 0x85807c00f3e71f19 0x42c03e0079f38f8c

def z472 : W := mkw 0x0013007402301a81 0x8009803a01180d40 0x7fff007c03f01f81 0xbfff803e01f80fc0

def z473 : W := mkw 0x700204adbc012dbe 0xb8010256de0096df 0x0600007ffc001ffe 0x8300003ffe000fff

def z474 : W := mkw 0x116dfb8107dee022 0x08b6fdc083ef7011 0xf9ffff870fffe0e7 0x7cffffc387fff073

def z475 : W := mkw 0x805a807600a81ac1 0xc02d403b00540d60 0x27f0807f00e81fe0 0x93f8403f80740ff0

def z476 : W := mkw 0x2002102439040c94 0x900108121c82064a 0x9e007064ff041c9f 0xcf0038327f820e4f

def z477 : W := mkw 0x51247f898547e12a 0x28923fc4c2a3f095 0x80007f808c07e01e 0x40003fc04603f00f

def z478 : W := mkw 0xc05b847e82b91bc9 0xe02dc23f415c8de4 0xffff8c7f83ff1ff9 0xffffc63fc1ff8ffc

def z479 : W := mkw 0x41f8dd58d1ef5719 0x20fc6eac68f7ab8c 0xbff0fdf8f3ef7f19 0xdff87efc79f7bf8c

def z480 : W := mkw 0x02366fffec000000 0x011b37fff6000000 0x82007ffffc000000 0xc1003ffffe000000

def z481 : W := mkw 0x6007362cbb158d9c 0xb0039b165d8ac6ce 0xff0f7e7cff179f9f 0xff87bf3e7f8bcfcf

def z482 : W := mkw 0x007eeb7600000000 0x003f75bb00000000 0xfa7fffff00000000 0xfd3fffff80000000

def z483 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff9f03ffe3e1 0xfeffffcf81fff1f0

def z484 : W := mkw 0x037ffb766bdec000 0x01bffdbb35ef6000 0xfbffffe073ffe001 0x7dfffff039fff000

def z485 : W := mkw 0x124ea3a72c002022 0x092751d396001011 0x400f83870c18e0e6 0x2007c1c3860c7073

def z486 : W := mkw 0x021204ffec000000 0x0109027ff6000000 0xea008ffffc000000 0xf50047fffe000000

def z487 : W := mkw 0x0212007668000000 0x0109003b34000000 0x0200006070000000 0x0100003038000000

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400001f000003e0 0x8200000f800001f0

def z489 : W := mkw 0x00100458c0000000 0x0008022c60000000 0x02000078f0000000 0x8100003c78000000

def z490 : W := mkw 0x200532003b148c94 0x900299001d8a464a 0x84007200ff149c9f 0x420039007f8a4e4f

def z491 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x9e0f7060f3041c19 0xcf07b83079820e0c

def z492 : W := mkw 0x8000000000201ac1 0xc000000000100d60 0x0400000000001fe0 0x0200000000000ff0

def z493 : W := mkw 0x500004898401212a 0x28000244c2009095 0xe9008f9b001fe361 0x748047cd800ff1b0

def z494 : W := mkw 0x700736adbf15adbe 0xb8039b56df8ad6df 0xde0f727fff149fff 0xef07b93fff8a4fff

def z495 : W := mkw 0x727fffffff15adbe 0xb93fffffff8ad6df 0xff7fffffff1fffff 0xffbfffffff8fffff

def z496 : W := mkw 0x0010005000201201 0x0008002800100900 0x21f0001800e00300 0x10f8000c00700180

def z497 : W := mkw 0x4000140891050518 0x20000a044882828c 0xbf007c78f3071f19 0xdf803e3c79838f8c

def z498 : W := mkw 0x036dff89efdec000 0x01b6ffc4f7ef6000 0xf9ffff80ffffe001 0x7cffffc07ffff000

def z499 : W := mkw 0x0168c90000ca4000 0x00b4648000652000 0x00f0000000e00000 0x0078000000700000

def z500 : W := mkw 0x500000000001212a 0x2800000000009095 0x6d00801f001fe3ff 0xb680400f800ff1ff

def z501 : W := mkw 0x8178c95200ea5241 0x40bc64a900752920 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z502 : W := mkw 0x827eefffec201ac1 0xc13f77fff6100d60 0xfe7ffffffc001fe0 0xff3ffffffe000ff0

def z503 : W := mkw 0x2000100011048414 0x100008000882420a 0x000000000004801e 0x000000000002400f

def z504 : W := mkw 0x200722242a108884 0x9003911215084442 0xcc0f02048c14809f 0xe6078102460a404f

def z505 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07c7fffe71fff 0xdff83e3ffff38fff

def z506 : W := mkw 0x0020480000420000 0x0010240000210000 0x21f00c0000e30000 0x10f8060000718000

def z507 : W := mkw 0x8012007600201ac1 0xc009003b00100d60 0x6f00807f00181fe1 0xb780403f800c0ff0

def z508 : W := mkw 0x429204fffc211719 0x2149027ffe108b8c 0x0600007ffc001f18 0x8300003ffe000f8c

def z509 : W := mkw 0x8058805200a81241 0x402c402900540920 0x00f0000000e00000 0x0078000000700000

def z510 : W := mkw 0xc0b25c7ed1671fd9 0xe0592e3f68b38fec 0xbff07c7ff3e71ff9 0xdff83e3ff9f38ffc

def z511 : W := mkw 0x6081100013779f9d 0xb040880009bbcfce 0x0580000003f79f9f 0x02c0000001fbcfcf

def z512 : W := mkw 0x40b04c58c0631309 0x2058262c60318984 0x3ff00c7803e31f01 0x9ff8063c01f18f80

def z513 : W := mkw 0x500536898715a12a 0x28029b44c38ad095 0xfd0fff9f8f1fe3ff 0xfe87ffcfc78ff1ff

def z514 : W := mkw 0x700204adbc012dbe 0xb8010256de0096df 0xef008ffffc1fffff 0xf78047fffe0fffff

def z515 : W := mkw 0x1000008104002022 0x0800004082001011 0x0000818300086060 0x000040c180043030

def z516 : W := mkw 0x0020580001460000 0x00102c0000a30000 0xf9f0ff8003ffe001 0x7cf87fc001fff000

def z517 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x127f707ffc000000 0x893fb83ffe000000

def z518 : W := mkw 0x00366e7ce8000000 0x001b373e74000000 0xfa7f7e7cfc000000 0xfd3fbf3e7e000000

def z519 : W := mkw 0x010423000000c000 0x0082118000006000 0x000003800000e000 0x000001c000007000

def z520 : W := mkw 0x0169d90003dec000 0x00b4ec8001ef6000 0x21f08d8003ffe001 0x10f846c001fff000

def z521 : W := mkw 0x025a84ffec000000 0x012d427ff6000000 0x7a7f807ffc000000 0xbd3fc03ffe000000

def z522 : W := mkw 0x50b04cd9c463332b 0x2858266ce2319995 0xedf08f9f8cffe3ff 0xf6f847cfc67ff1ff

def z523 : W := mkw 0x0005320003148000 0x00029900018a4000 0xdc0f72048f14809f 0xee07b902478a404f

def z524 : W := mkw 0x8059805202b81241 0x402cc029015c0920 0x79ff801b03f80361 0x3cffc00d81fc01b0

def z525 : W := mkw 0x804b8026029808c0 0xc025c013014c0460 0x79ff800703f800e1 0x3cffc00381fc0070

def z526 : W := mkw 0x0006222428000000 0x0003111214000000 0x400f02040c000000 0x2007810206000000

def z527 : W := mkw 0x227fffffff148c94 0x913fffffff8a464a 0xfa7fffffff001c00 0xfd3fffffff800e00

def z528 : W := mkw 0x300722a52e10a8a6 0x9803915297085453 0x400f83870c18e0e6 0x2007c1c3860c7073

def z529 : W := mkw 0x004ca30000000000 0x0026518000000000 0x400f838000000000 0x2007c1c000000000

def z530 : W := mkw 0x2006322439048c94 0x900319121c82464a 0x86007264fc049c9e 0xc30039327e024e4f

def z531 : W := mkw 0xd0fbdcffd7ff3ffb 0xe87dee7febff9ffd 0xffffffffffffffff 0xffffffffffffffff

def z532 : W := mkw 0x500000000001212a 0x2800000000009095 0x000000000007e01e 0x000000000003f00f

def z533 : W := mkw 0x505a84ff8401212a 0x282d427fc2009095 0xff7f8fff8c1fe3ff 0xffbfc7ffc60ff1ff

def z534 : W := mkw 0x0000100001460000 0x0000080000a30000 0x0180000003e70001 0x00c0000001f38000

def z535 : W := mkw 0x700732243b15adbe 0xb80399121d8ad6df 0xdf0f7264ff1fffff 0xef87b9327f8fffff

def z536 : W := mkw 0x0007322403148880 0x80039912018a4440 0xde0f726403149c81 0xef07b932018a4e40

def z537 : W := mkw 0x500000000001212a 0x2800000000009095 0xed008f80001fe3ff 0x768047c0000ff1ff

def z538 : W := mkw 0x016ffb2403dec880 0x80b7fd9201ef6440 0xffffffe403fffc81 0xfffffff201fffe40

def z539 : W := mkw 0x221204fffc000c94 0x9109027ffe00064a 0x0600007ffc001c9e 0x8300003ffe000e4f

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0xc80002048c000000 0xe400010246000000

def z541 : W := mkw 0x20b77a747b769e95 0x905bbd3a3dbb4f4a 0x12ff706073e01c00 0x097fb83039f00e00

def z542 : W := mkw 0x70b77efdff77bfbf 0xb85bbf7effbbdfdf 0xffffffffffffffff 0xffffffffffffffff

def z543 : W := mkw 0x005b807602980000 0x002dc03b014c0000 0x7bff807f03f80001 0xbdffc03f81fc0000

def z544 : W := mkw 0x010100000298c000 0x00808000014c6000 0x000000000018e000 0x00000000000c7000

def z545 : W := mkw 0x2004320039048414 0x100219001c82420a 0x9e007260ff049c1f 0xcf0039307f824e0f

def z546 : W := mkw 0x0004320001048000 0x0002190000824000 0x8000720000048000 0x4000390000024000

def z547 : W := mkw 0xa05b80763ab81ed5 0xd02dc03b1d5c0f6a 0x7fff807ffff81fff 0xbfffc03ffffc0fff

def z548 : W := mkw 0x027cefdbec000000 0x013e77edf6000000 0xa070ff9bfc000000 0x50387fcdfe000000

def z549 : W := mkw 0x22277fadff148c94 0x9113bfd6ff8a464a 0xde0f7fe4ff149c9f 0xef07bff27f8a4e4f

def z550 : W := mkw 0x8013007602b81ac1 0xc009803b015c0d60 0x0780007f03f81fe1 0x83c0003f81fc0ff0

def z551 : W := mkw 0x514da7898699e12a 0x28a6d3c4c34cf095 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z552 : W := mkw 0x027acdffec000000 0x013d66fff6000000 0x22708dfffc000000 0x913846fffe000000

def z553 : W := mkw 0xc0fbcc7ec2fb1bc9 0xe07de63f617d8de4 0x7fff8c7f03fb1fe1 0xbfffc63f81fd8ff0

def z554 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x52ff806703f81ce0 0x297fc03381fc0e70

def z555 : W := mkw 0x1000008104002022 0x0800004082001011 0x000000070c0000e6 0x0000000386000073

def z556 : W := mkw 0xc0db907613ff1fd9 0xe06dc83b09ff8fec 0x7fff807f03ff1ff9 0xbfffc03f81ff8ffc

def z557 : W := mkw 0x21277b243b56cc94 0x9093bd921dab664a 0xde0f7fe4ff17fc9f 0xef07bff27f8bfe4f

def z558 : W := mkw 0x006cfb0001460000 0x00367d8000a30000 0xf9ffff8003e70001 0x7cffffc001f38000

def z559 : W := mkw 0x42feeffffc211719 0x217f77fffe108b8c 0xfe7ffffffc001f18 0xff3ffffffe000f8c

def z560 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x920f7260ff049c1e 0x4907b9307f824e0f

def z561 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xa1f07c18f0e70318 0x50f83e0c7873818c

def z562 : W := mkw 0x80010000029808c0 0xc0008000014c0460 0x00000000001800e0 0x00000000000c0070

def z563 : W := mkw 0x807feb7602b81ac1 0xc03ff5bb015c0d60 0xffffffff03f81fe1 0xffffffff81fc0ff0

def z564 : W := mkw 0x221736ffff148c94 0x910b9b7fff8a464a 0xde0f727fff149c9f 0xef07b93fff8a4e4f

def z565 : W := mkw 0x500004898401212a 0x28000244c2009095 0x00000d8000036000 0x000006c00001b000

def z566 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x5e0f706473101c81 0xaf07b83239880e40

def z567 : W := mkw 0x537fffffefdfe12a 0x29bffffff7eff095 0xffffffffffffe3ff 0xfffffffffffff1ff

def z568 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x460f807f00181fe0 0xa307c03f800c0ff0

def z569 : W := mkw 0x0030585001661201 0x00182c2800b30900 0xbff07c7803e71f01 0xdff83e3c01f38f80

def z570 : W := mkw 0x214fb3243b9ccc94 0x90a7d9921dce664a 0xde0ff3e4ff1cfc9f 0xef07f9f27f8e7e4f

def z571 : W := mkw 0x216ffb242bdec884 0x90b7fd9215ef6442 0xf9ffff840fffe087 0x7cffffc207fff043

def z572 : W := mkw 0x02000489ec000000 0x01000244f6000000 0x00000000fc000000 0x000000007e000000

def z573 : W := mkw 0x61ffff7cfbffdf9d 0xb0ffffbe7dffefce 0xfffffffcffffff9f 0xfffffffe7fffffcf

def z574 : W := mkw 0x500000000001212a 0x2800000000009095 0xcd0002048c1fe3ff 0xe6800102460ff1ff

def z575 : W := mkw 0x804b8026029808c0 0xc025c013014c0460 0x000f000000000000 0x0007800000000000

def z576 : W := mkw 0x0069d80003de0000 0x0034ec0001ef0000 0xf9fffc0003ff0001 0x7cfffe0001ff8000

def z577 : W := mkw 0x816ffb2603dec8c0 0xc0b7fd9301ef6460 0xf9ffff8703ffe0e1 0x7cffffc381fff070

def z578 : W := mkw 0x500004898401212a 0x28000244c2009095 0xcc00021f8c1483ff 0xe600010fc60a41ff

def z579 : W := mkw 0x2002002428000884 0x9001001214000442 0x000000040c000086 0x0000000206000043

def z580 : W := mkw 0x014db300039cc000 0x00a6d98001ce6000 0xd80ff380031ce001 0x6c07f9c0018e7000

def z581 : W := mkw 0x0169c90002da4000 0x00b4e480016d2000 0x79ff8d8003fb6001 0x3cffc6c001fdb000

def z582 : W := mkw 0x0000100011040410 0x0000080008820208 0xde007264ff149c9f 0xef0039327f8a4e4f

def z583 : W := mkw 0x41fdff58d3ffd719 0x20feffac69ffeb8c 0xbfff7c78f3e71f19 0xdfffbe3c79f38f8c

def z584 : W := mkw 0x0005320003148000 0x00029900018a4000 0xf90fff80031fe001 0x7c87ffc0018ff000

def z585 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x3fff007803e01f01 0x9fff803c01f00f80

def z586 : W := mkw 0x02346fd9ec000000 0x011a37ecf6000000 0xba707ff8fc000000 0xdd383ffc7e000000

def z587 : W := mkw 0x40a0580011671719 0x20502c0008b38b8c 0xbdf07c0003e71f19 0x5ef83e0001f38f8c

def z588 : W := mkw 0x40fcff58d1671719 0x207e7fac68b38b8c 0xfffffff8f3e71f19 0xfffffffc79f38f8c

def z589 : W := mkw 0x905b80f706b83ae3 0xc82dc07b835c1d71 0x7fff83ff0ff8ffe7 0xbfffc1ff87fc7ff3

def z590 : W := mkw 0x200722242a108884 0x9003911215084442 0x000f000000000000 0x0007800000000000

def z591 : W := mkw 0x000626adac000000 0x00031356d6000000 0xfa0ffffffc000000 0xfd07fffffe000000

def z592 : W := mkw 0xd27fefffeeb93beb 0xe93ff7fff75c9df5 0xffffffffffffffff 0xffffffffffffffff

def z593 : W := mkw 0x00305c58c1460000 0x00182e2c60a30000 0xbbf07c78f3e70001 0xddf83e3c79f38000

def z594 : W := mkw 0x40800408d0010518 0x204002046800828c 0x00000000f0000018 0x000000007800000c

def z595 : W := mkw 0x716fffadbfdfedbe 0xb8b7ffd6dfeff6df 0xffffffffffffffff 0xffffffffffffffff

def z596 : W := mkw 0x0003002402100880 0x8001801201080440 0x7f0f807f03181fe1 0xbf87c03f818c0ff0

def z597 : W := mkw 0x60b47e58f967971d 0x305a3f2c7cb3cb8e 0xbff07e78ffe79f1f 0xdff83f3c7ff3cf8f

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x400002040c108086 0x2000010206084043

def z599 : W := mkw 0x500004898401212a 0x28000244c2009095 0x0500001f8c1fe3ff 0x8280000fc60ff1ff

def z600 : W := mkw 0xc0db847ed2b91fd9 0xe06dc23f695c8fec 0x7fff807ff3f81ff9 0xbfffc03ff9fc0ffc

def z601 : W := mkw 0x00204c08c0000000 0x0010260460000000 0x80007c00f0000000 0x40003e0078000000

def z602 : W := mkw 0x0002002400000880 0x8001001200000440 0x0600006400001c80 0x8300003200000e40

def z603 : W := mkw 0x01247b000146c000 0x00923d8000a36000 0x0000700000000000 0x0000380000000000

def z604 : W := mkw 0x500004898401212a 0x28000244c2009095 0xad008d9b800f6379 0xd68046cdc007b1bc

def z605 : W := mkw 0xa05fb2763bbc9ed5 0xd02fd93b1dde4f6a 0x7ffff07f73f81fe1 0xbffff83fb9fc0ff0

def z606 : W := mkw 0xd01204ff84213beb 0xe809027fc2109df5 0xef008fff8c1fffff 0xf78047ffc60fffff

def z607 : W := mkw 0x41fdff58c3ffd309 0x20feffac61ffe984 0xf9ffff9803ffe301 0x7cffffcc01fff180

def z608 : W := mkw 0x0059805002b81201 0x002cc028015c0900 0x7fff807803f81f01 0xbfffc03c01fc0f80

def z609 : W := mkw 0x500004898401212a 0x28000244c2009095 0x25008d9b001fe3ff 0x128046cd800ff1ff

def z610 : W := mkw 0xa05fa2762ab89ac5 0xd02fd13b155c4d62 0x7fff827f0ff89fe7 0xbfffc13f87fc4ff3

def z611 : W := mkw 0x500004898401212a 0x28000244c2009095 0x6d008d9f001b63e1 0xb68046cf800db1f0

def z612 : W := mkw 0x60a77e2cfb578d9c 0xb053bf167dabc6ce 0xde0f7e64ff179c9f 0xef07bf327f8bce4f

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x2100801b00080360 0x1080400d800401b0

def z614 : W := mkw 0x827fefffee9808c0 0xc13ff7fff74c0460 0xfa7ffffffc1800e0 0xfd3ffffffe0c0070

def z615 : W := mkw 0x40a05c08d1470518 0x20502e0468a3828c 0xad007c18f0070319 0xd6803e0c7803818c

def z616 : W := mkw 0x01247b000146c000 0x00923d8000a36000 0xb9f07f8003e7e001 0x5cf83fc001f3f000

def z617 : W := mkw 0x500004898401212a 0x28000244c2009095 0xad000c1f8c0703ff 0xd680060fc60381ff

def z618 : W := mkw 0x817ffb7603fedac1 0xc0bffdbb01ff6d60 0x12ff706003e01c00 0x097fb83001f00e00

def z619 : W := mkw 0x40901458d1671719 0x20480a2c68b38b8c 0x07800078f3e71f19 0x83c0003c79f38f8c

def z620 : W := mkw 0x000722242a100880 0x8003911215080440 0xde0f7264ff101c81 0xef07b9327f880e40

def z621 : W := mkw 0x8001000002b81ac1 0xc0008000015c0d60 0x6d80801f03f81fe1 0xb6c0400f81fc0ff0

def z622 : W := mkw 0x60b77e7cfb779f9d 0xb05bbf3e7dbbcfce 0xbfff7c78f3e71f19 0xdfffbe3c79f38f8c

def z623 : W := mkw 0x01fdfb5053fed611 0x00fefda829ff6b08 0x12ff706073e01c00 0x097fb83039f00e00

def z624 : W := mkw 0x025ea7ffec000000 0x012f53fff6000000 0x420f83fffc000000 0xa107c1fffe000000

def z625 : W := mkw 0x0248818304000000 0x012440c182000000 0x0000818300000000 0x000040c180000000

def z626 : W := mkw 0x206ffb243b148c94 0x9037fd921d8a464a 0xfe7fffe4ff149c9f 0xff3ffff27f8a4e4f

def z627 : W := mkw 0x8003002402b81ac1 0xc0018012015c0d60 0x5f8f006403f81fe1 0xafc7803201fc0ff0

def z628 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x17ff006003f81fe1 0x0bff803001fc0ff0

def z629 : W := mkw 0x20b77a747b769e95 0x905bbd3a3dbb4f4a 0xdeff7264fff49c9f 0xef7fb9327ffa4e4f

def z630 : W := mkw 0x500004898401212a 0x28000244c2009095 0x85000f808c1fe3ff 0x428007c0460ff1ff

def z631 : W := mkw 0x904b80a7069828e2 0xc825c053834c1471 0x400f83870c18e0e6 0x2007c1c3860c7073

def z632 : W := mkw 0x016deb000298c000 0x00b6f580014c6000 0xf87fff800018e000 0x7c3fffc0000c7000

def z633 : W := mkw 0x500004898401212a 0x28000244c2009095 0x61008f9f0c1be3e6 0x308047cf860df1f3

def z634 : W := mkw 0x2004220028008004 0x1002110014004002 0x000002000c008006 0x0000010006004003

def z635 : W := mkw 0x0121580003dec000 0x0090ac0001ef6000 0xb9f07c0003ffe001 0x5cf83e0001fff000

def z636 : W := mkw 0x0049800002980000 0x0024c000014c0000 0x7dff801f03f803e1 0xbeffc00f81fc01f0

def z637 : W := mkw 0x027fefffee980000 0x013ff7fff74c0000 0xfbfffffffff80001 0xfdfffffffffc0000

def z638 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x86007c78f0071f18 0xc3003e3c78038f8c

def z639 : W := mkw 0x00305c58d1040410 0x00182e2c68820208 0xbe707c78f3041c19 0xdf383e3c79820e0c

def z640 : W := mkw 0x41edfb0013ffd719 0x20f6fd8009ffeb8c 0xfdffff8003ffff19 0x7effffc001ffff8c

def z641 : W := mkw 0x027fefffee100880 0x813ff7fff7080440 0xfe7fffffff101c81 0xff3fffffff880e40

def z642 : W := mkw 0x037ffb766bdec000 0x01bffdbb35ef6000 0x12ff706073e00000 0x097fb83039f00000

def z643 : W := mkw 0x227efffffd048414 0x113f7ffffe82420a 0xfa7ffffffc04801e 0xfd3ffffffe02400f

def z644 : W := mkw 0x205fb2763b148c94 0x902fd93b1d8a464a 0xfe7ff27fff149c9f 0xff3ff93fff8a4e4f

def z645 : W := mkw 0xc0fbdc7ed3ff1fd9 0xe07dee3f69ff8fec 0xbfff7c78f3e71f19 0xdfffbe3c79f38f8c

def z646 : W := mkw 0x8278cddbc4a81241 0x413c66ede2540920 0x21f08d9b00e80360 0x10f846cd807401b0

def z647 : W := mkw 0x817dfb5203fed241 0x40befda901ff6920 0xf9ffff9b03ffe361 0x7cffffcd81fff1b0

def z648 : W := mkw 0x014da3000298c000 0x00a6d180014c6000 0x000f000000000000 0x0007800000000000

def z649 : W := mkw 0x8012007600201ac1 0xc009003b00100d60 0x3ff0007f03e01fe1 0x9ff8003f81f00ff0

def z650 : W := mkw 0x005a807600000000 0x002d403b00000000 0x127f006000000000 0x093f803000000000

def z651 : W := mkw 0x0048800000000000 0x0024400000000000 0x787f800000000000 0x3c3fc00000000000

def z652 : W := mkw 0x4090105011671719 0x2048082808b38b8c 0x3ff0007803e71f19 0x9ff8003c01f38f8c

def z653 : W := mkw 0x815b907603fedac1 0xc0adc83b01ff6d60 0x7fff807f03ffffe1 0xbfffc03f81fffff0

def z654 : W := mkw 0xd05b84ff86b93beb 0xe82dc27fc35c9df5 0x7fff807f8ff81fff 0xbfffc03fc7fc0fff

def z655 : W := mkw 0x00304c58c0000000 0x0018262c60000000 0x20700c1800000000 0x1038060c00000000

def z656 : W := mkw 0x0006322439040410 0x000319121c820208 0xde0f7264ff041c19 0xef07b9327f820e0c

def z657 : W := mkw 0x014da3000298c000 0x00a6d180014c6000 0x79ff838003f8e001 0x3cffc1c001fc7000

def z658 : W := mkw 0x4000048984010108 0x20000244c2008084 0xed008f9f8c070319 0xf68047cfc603818c

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c00000400100081 0xa600000200080040

def z660 : W := mkw 0x037fffffefdec000 0x01bffffff7ef6000 0xfaffffffffe00000 0xfd7ffffffff00000

def z661 : W := mkw 0x8013007602301ac1 0xc009803b01180d60 0x5e0f007f03101fe1 0xaf07803f81880ff0

def z662 : W := mkw 0xd05b84ff86b93beb 0xe82dc27fc35c9df5 0x7fff8dff03fb7fe1 0xbfffc6ff81fdbff0

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000048c00009e 0x820000024600004f

def z664 : W := mkw 0x200300243a100c94 0x900180121d08064a 0x5e0f0064ff101c9f 0xaf0780327f880e4f

def z665 : W := mkw 0x817bc97602fa5ac1 0xc0bde4bb017d2d60 0x7fff8dff03fb7fe1 0xbfffc6ff81fdbff0

def z666 : W := mkw 0x0000000000201201 0x0000000000100900 0x0580000003e01f01 0x02c0000001f00f80

def z667 : W := mkw 0x42f8cddbc4631309 0x217c66ede2318984 0x21f08d9b00e30300 0x10f846cd80718180

def z668 : W := mkw 0x5101148987dfe12a 0x28808a44c3eff095 0xed808f9f8fffe3ff 0xf6c047cfc7fff1ff

def z669 : W := mkw 0x805a807600201ac1 0xc02d403b00100d60 0x7e7f807f00001fe0 0xbf3fc03f80000ff0

def z670 : W := mkw 0x025ea3f72c000000 0x012f51fb96000000 0x7a7f83ff0c000000 0xbd3fc1ff86000000

def z671 : W := mkw 0x8059805202b81ac1 0xc02cc029015c0d60 0x25f0801b03f81fe1 0x12f8400d81fc0ff0

def z672 : W := mkw 0xe0fffe7efbff9fdd 0xf07fff3f7dffcfee 0xfffffe7fffff9fff 0xffffff3fffffcfff

def z673 : W := mkw 0x40a04c08c0430108 0x2050260460218084 0x00000c0000030000 0x0000060000018000

def z674 : W := mkw 0x501004d98421332b 0x2808026cc2109995 0xfff08fff8fffffff 0xfff847ffc7ffffff

def z675 : W := mkw 0x8012007600201ac1 0xc009003b00100d60 0x0200006000001c00 0x0100003000000e00

def z676 : W := mkw 0x004db200039c8000 0x0026d90001ce4000 0xf9fff20003fc8001 0x7cfff90001fe4000

def z677 : W := mkw 0x0000048984000000 0x00000244c2000000 0x20008d9b00000000 0x100046cd80000000

def z678 : W := mkw 0x03247f89ed46c000 0x01923fc4f6a36000 0x80007f80fc07e000 0x40003fc07e03f000

def z679 : W := mkw 0x017ffb7603dec000 0x00bffdbb01ef6000 0xfbffffff03ffe001 0xfdffffff81fff000

def z680 : W := mkw 0x50a05c89d547253a 0x28502e44eaa3929d 0xed00ff9ffc1fe3ff 0xf6807fcffe0ff1ff

def z681 : W := mkw 0x027fffffef148000 0x013ffffff78a4000 0xfa7fffffff148001 0xfd3fffffff8a4000

def z682 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xc00fff80001fe000 0x6007ffc0000ff000

def z683 : W := mkw 0x006ceb0000000000 0x0036758000000000 0x107f700000000000 0x083fb80000000000

def z684 : W := mkw 0x8101100003fedac1 0xc080880001ff6d60 0x0580000003ffffe1 0x02c0000001fffff0

def z685 : W := mkw 0x500004898401212a 0x28000244c2009095 0xa1008f9b8c0fe37e 0x508047cdc607f1bf

def z686 : W := mkw 0x000732242b148000 0x00039912158a4000 0xda0f7264ff148001 0xed07b9327f8a4000

def z687 : W := mkw 0x200722243a108c94 0x900391121d08464a 0x460f0264fc109c9e 0xa30781327e084e4f

def z688 : W := mkw 0xa012007638201ed5 0xd009003b1c100f6a 0x0600007ffc001ffe 0x8300003ffe000fff

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x6900800000180001 0x34804000000c0000

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0xa9000c0000070001 0x5480060000038000

def z691 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x520f72647f109c86 0x2907b9323f884e43

def z692 : W := mkw 0x027efffffd040410 0x013f7ffffe820208 0xfe7fffffff041c19 0xff3fffffff820e0c

def z693 : W := mkw 0x504984898699212a 0x2824c244c34c9095 0xfdff8f9f8fffe3ff 0xfeffc7cfc7fff1ff

def z694 : W := mkw 0x006dfb0003148000 0x0036fd80018a4000 0xf87fff8003148001 0x7c3fffc0018a4000

def z695 : W := mkw 0x300732a53f14acb6 0x980399529f8a565b 0xde0ff3e7ff1cfcff 0xef07f9f3ff8e7e7f

def z696 : W := mkw 0x416dff0883dfc108 0x20b6ff8441efe084 0xfdffff9883ffe319 0xfeffffcc41fff18c

def z697 : W := mkw 0x005a84ff84000000 0x002d427fc2000000 0xfa7f8fff8c000000 0xfd3fc7ffc6000000

def z698 : W := mkw 0x014db30003dec000 0x00a6d98001ef6000 0x418f838003ffe001 0x20c7c1c001fff000

def z699 : W := mkw 0x4010045880211309 0x2008022c40108984 0xbff00c7883e71f19 0xdff8063c41f38f8c

def z700 : W := mkw 0x0001000002100000 0x0000800001080000 0x580f000003100001 0x2c07800001880000

def z701 : W := mkw 0x40a05c08d1470518 0x20502e0468a3828c 0xb9f07c00f3e70019 0x5cf83e0079f3800c

def z702 : W := mkw 0x2003102413148c94 0x90018812098a464a 0x5e0f006403149c9f 0xaf078032018a4e4f

def z703 : W := mkw 0x42b47fd9fd671719 0x215a3fecfeb38b8c 0xbff07ff8ffe71f19 0xdff83ffc7ff38f8c

def z704 : W := mkw 0x224fa3a72e108884 0x9127d1d397084442 0x400f83870c108086 0x2007c1c386084043

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8008f8000000000 0x740047c000000000

def z706 : W := mkw 0x500004898401212a 0x28000244c2009095 0xcc000f848c17e09f 0xe60007c2460bf04f

def z707 : W := mkw 0x210732243b9ccc94 0x908399121dce664a 0xde0f7264ff1cfc9f 0xef07b9327f8e7e4f

def z708 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07c7cffe71f9f 0xdff83e3e7ff38fcf

def z709 : W := mkw 0x827eeb7668201ac1 0xc13f75bb34100d60 0x167f707f70001fe0 0x8b3fb83fb8000ff0

def z710 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xffffffe003fffc01 0xfffffff001fffe00

def z711 : W := mkw 0xd05b84ff86b93beb 0xe82dc27fc35c9df5 0x92ff0fe08fe7fc1e 0x497f87f047f3fe0f

def z712 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xe1ffff8000ffe000 0x70ffffc0007ff000

def z713 : W := mkw 0x216dfb003bdec414 0x10b6fd801def620a 0xffffffe0fffffc1f 0xfffffff07ffffe0f

def z714 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff07c7cf3f71f99 0xfff83e3e79fb8fcc

def z715 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x327ffdfffc000000 0x993ffefffe000000

def z716 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xda0f7264ff049c1e 0xed07b9327f824e0f

def z717 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x37ff807f03e81fe0 0x9bffc03f81f40ff0

def z718 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff8703ffe0e1 0x7cffffc381fff070

def z719 : W := mkw 0x00266a2428000000 0x0013351214000000 0xfa7f7e64fc000000 0xfd3fbf327e000000

def z720 : W := mkw 0x027eefffec201201 0x013f77fff6100900 0xfbfffffffce00300 0xfdfffffffe700180

def z721 : W := mkw 0x005ea27628000000 0x002f513b14000000 0x127f706070000000 0x093fb83038000000

def z722 : W := mkw 0x0049800002980000 0x0024c000014c0000 0x79ff8d8003fb6001 0x3cffc6c001fdb000

def z723 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbbf07c60f3e71c19 0x5df83e3079f38e0c

def z724 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xfa7ff27ffc000000 0xfd3ff93ffe000000

def z725 : W := mkw 0x00366a7468000000 0x001b353a34000000 0xda7f7264fc000000 0xed3fb9327e000000

def z726 : W := mkw 0x000626adac000000 0x00031356d6000000 0xda0f7fe4fc000000 0xed07bff27e000000

def z727 : W := mkw 0x037eefffec00c000 0x01bf77fff6006000 0xfa7ffffffc00e000 0xfd3ffffffe007000

def z728 : W := mkw 0x834fa3a72e98c8c0 0xc1a7d1d3974c6460 0x400f83870c18e0e0 0x2007c1c3860c7070

def z729 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x05000000031ffc9f 0x02800000018ffe4f

def z730 : W := mkw 0x60b05c58d167971d 0x30582e2c68b3cb8e 0xbff07c78f3e79f1f 0xdff83e3c79f3cf8f

def z731 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0xfa7fffe77c000000 0x7d3ffff3be000000

def z732 : W := mkw 0x005a807600201201 0x002d403b00100900 0x7fff807f03f81fe1 0xbfffc03f81fc0ff0

def z733 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbaf07c78f3e71c18 0xdd783e3c79f38e0c

def z734 : W := mkw 0xa001100013bc9ed5 0xd000880009de4f6a 0xed80821f8ffc9fff 0xf6c0410fc7fe4fff

def z735 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07e78ffe79f1f 0xdff83f3c7ff3cf8f

def z736 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0fffbf3ffff79 0xfff87ffdf9ffffbc

def z737 : W := mkw 0x42feef7ee8631309 0x217f77bf74318984 0x33ff7c7870e30300 0x19ffbe3c38718180

def z738 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xfe0fffe4ff149c9f 0xff07fff27f8a4e4f

def z739 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x7a7ff07ffc000000 0xbd3ff83ffe000000

def z740 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xff0fffffff1fffff 0xff87ffffff8fffff

def z741 : W := mkw 0x6081100013359f9d 0xb0408800099acfce 0x0400000003149f9f 0x02000000018a4fcf

def z742 : W := mkw 0xa05cb25239ac9655 0x502e59291cd64b2a 0xa1f0f21bfcec837e 0x50f8790dfe7641bf

def z743 : W := mkw 0x42b05cdbd5671719 0x21582e6deab38b8c 0xbff07c7bf3e71f19 0xdff83e3df9f38f8c

def z744 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfe7ffffffc18e3fe 0xff3ffffffe0c71ff

def z745 : W := mkw 0x500626adac01212a 0x28031356d6009095 0xda0f7fe4fc07e01e 0xed07bff27e03f00f

def z746 : W := mkw 0x0006222428000000 0x0003111214000000 0xfa0ff27ffc000000 0xfd07f93ffe000000

def z747 : W := mkw 0x700110001315adbe 0xb8008800098ad6df 0x040000000317fc9f 0x02000000018bfe4f

def z748 : W := mkw 0x2279dddbd7148c94 0x913ceeedeb8a464a 0x24708d9b03149c9f 0x123846cd818a4e4f

def z749 : W := mkw 0x537eefffeccb612a 0x29bf77fff665b095 0xfffffffffcffe3ff 0xfffffffffe7ff1ff

def z750 : W := mkw 0x036dfb006bdec000 0x01b6fd8035ef6000 0xf9ffff8073ffe001 0x7cffffc039fff000

def z751 : W := mkw 0x007cef58c0000000 0x003e77ac60000000 0xba7f7c78f0000000 0xdd3fbe3c78000000

def z752 : W := mkw 0x0006222428000000 0x0003111214000000 0xfa0fffe4fc000000 0xfd07fff27e000000

def z753 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff8003ffe09f 0x7effffc001fff04f

def z754 : W := mkw 0x500004898401212a 0x28000244c2009095 0xff00fffffc1fe3ff 0xff807ffffe0ff1ff

def z755 : W := mkw 0x40366e7ce8010108 0x201b373e74008084 0xff7f7e7cfc17839f 0xffbfbf3e7e0bc1cf

def z756 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xbff07c78f3e71fff 0xdff83e3c79f38fff

def z757 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0xda7ff3e7fc000000 0xed3ff9f3fe000000

def z758 : W := mkw 0x200722243a108c94 0x900391121d08464a 0xde0f7264fc109c9e 0xef07b9327e084e4f

def z759 : W := mkw 0x031314ffefdec000 0x01898a7ff7ef6000 0x0380007fffffe001 0x81c0003ffffff000

def z760 : W := mkw 0x0001100013148410 0x00008800098a4208 0x0400000003149c19 0x02000000018a4e0c

def z761 : W := mkw 0x216ac92438ca4c94 0x90b564921c65264a 0x27f08de4fceb7c9e 0x93f846f27e75be4f

def z762 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x56ff807f03f81fe0 0xab7fc03f81fc0ff0

def z763 : W := mkw 0x0006222428000000 0x0003111214000000 0x520f72647c000000 0x2907b9323e000000

def z764 : W := mkw 0x700736adbf15adbe 0xb8039b56df8ad6df 0x330ffdfb730b7f60 0x1987fefdb985bfb0

def z765 : W := mkw 0x824fa3a72e9808c0 0xc127d1d3974c0460 0x400f83870c000000 0x2007c1c386000000

def z766 : W := mkw 0x0006222428000000 0x0003111214000000 0x120f7064fc000000 0x8907b8327e000000

def z767 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0xfa7ffff8f0000000 0xfd3ffffc78000000

def z768 : W := mkw 0x0030485040201201 0x0018242820100900 0x3ff0707873e01f01 0x9ff8383c39f00f80

def z769 : W := mkw 0x007eeb7628000000 0x003f75bb14000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z770 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x16f07060f3e01c18 0x8b78383079f00e0c

def z771 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfbffffe0f3ffe001 0xfdfffff079fff000

def z772 : W := mkw 0x006ceb0028000000 0x0036758014000000 0xf87fff80fc000000 0x7c3fffc07e000000

def z773 : W := mkw 0x314fa3a52e98e8a6 0x98a7d1d2974c7453 0x400f83870c18e0e6 0x2007c1c3860c7073

def z774 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff827f8ff81fe1 0xffffc13fc7fc0ff0

def z775 : W := mkw 0x00305c58d1460410 0x00182e2c68a30208 0xbff07c78f3e71c19 0xdff83e3c79f38e0c

def z776 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x37f07c7873e71f19 0x1bf83e3c39f38f8c

def z777 : W := mkw 0xc0facc7ec0eb1349 0x607d663f607589a4 0xfbfffc7ff0eb0360 0xfdfffe3ff87581b0

def z778 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xfb7fffe0701fe001 0x7dbffff0380ff000

def z779 : W := mkw 0xa05b80762ab81ac5 0xd02dc03b155c0d62 0x7fff807f0ff81fe7 0xbfffc03f87fc0ff3

def z780 : W := mkw 0x006cfb0001460000 0x00367d8000a30000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z781 : W := mkw 0x7101100013dfedbe 0xb880880009eff6df 0x0580000003ffffff 0x02c0000001ffffff

def z782 : W := mkw 0x016ceb0000ca4000 0x00b6758000652000 0xf9ffff8000ffe001 0x7cffffc0007ff000

def z783 : W := mkw 0xd27eefffec213beb 0xe93f77fff6109df5 0xfe7ffffffc001ffe 0xff3ffffffe000fff

def z784 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x61ff8f8003ffe001 0x30ffc7c001fff000

def z785 : W := mkw 0x100622a52c002022 0x0803115296001011 0xda0ff3e7fc18e0e6 0xed07f9f3fe0c7073

def z786 : W := mkw 0x02366effec000000 0x011b377ff6000000 0xfa7f7e7ffc000000 0xfd3fbf3ffe000000

def z787 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0x927f7fe0fc07e01e 0x493fbff07e03f00f

def z788 : W := mkw 0x026eefadec000000 0x013777d6f6000000 0xfa7fffe4fc000000 0xfd3ffff27e000000

def z789 : W := mkw 0xd081100013ff3ffb 0xe840880009ff9ffd 0x0580000003ffffff 0x02c0000001ffffff

def z790 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x13f0706073e71c01 0x09f8383039f38e00

def z791 : W := mkw 0x2101100013decc94 0x9080880009ef664a 0x0080000003e01c00 0x0040000001f00e00

def z792 : W := mkw 0x40a05c08d1470518 0x20502e0468a3828c 0xbff07c60f3e71c19 0xdff83e3079f38e0c

def z793 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x37ff807b03f81fe1 0x1bffc03d81fc0ff0

def z794 : W := mkw 0x037eefffecca4000 0x01bf77fff6652000 0xfbfffffffcffe001 0xfdfffffffe7ff000

def z795 : W := mkw 0x2101100013decc94 0x9080880009ef664a 0xed808f848ffffc9f 0xf6c047c247fffe4f

def z796 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7bff807b03f81f61 0x3dffc03d81fc0fb0

def z797 : W := mkw 0x016dfb0013dec410 0x00b6fd8009ef6208 0xfdffff8003fffc19 0x7effffc001fffe0c

def z798 : W := mkw 0x6181100013ffdf9d 0xb0c0880009ffefce 0x0580000003ffff9f 0x02c0000001ffffcf

def z799 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfe7ffffffc1483ff 0xff3ffffffe0a41ff

def z800 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xd0ffff8003ffe000 0x687fffc001fff000

def z801 : W := mkw 0x214fa3242a98c884 0x90a7d192154c6442 0x000f000000000000 0x0007800000000000

def z802 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x12f07060f3e01c18 0x0978383079f00e0c

def z803 : W := mkw 0xa0011000139c8cd4 0xd000880009ce466a 0x04000000031c9cff 0x02000000018e4e7f

def z804 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x440002040f149c9f 0x22000102078a4e4f

def z805 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xbff0fdfbf3e71f19 0xdff87efdf9f38f8c

def z806 : W := mkw 0x216dfb003bdecc94 0x90b6fd801def664a 0xfdffff80fffffc9f 0x7effffc07ffffe4f

def z807 : W := mkw 0x805a807600201ac1 0xc02d403b00100d60 0x7fff807f03e01fe1 0xbfffc03f81f00ff0

def z808 : W := mkw 0x000722242a100880 0x8003911215080440 0xde0f7264ff149c9f 0xef07b9327f8a4e4f

def z809 : W := mkw 0x2101100013dec414 0x1080880009ef620a 0x0180000003ffe01f 0x00c0000001fff00f

def z810 : W := mkw 0x8016227628201ac1 0xc00b113b14100d60 0xde0f727ffc001fe0 0xef07b93ffe000ff0

def z811 : W := mkw 0x00366efdec000000 0x001b377ef6000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z812 : W := mkw 0x005ea6ffac000000 0x002f537fd6000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z813 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7bff807f03e81f60 0xbdffc03f81f40fb0

def z814 : W := mkw 0x026eefafec000000 0x013777d7f6000000 0xda0fffe7fc000000 0xed07fff3fe000000

def z815 : W := mkw 0xd09204ffd4213ffb 0xe849027fea109ffd 0x0600007ffc001ffe 0x8300003ffe000fff

def z816 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x33f07c6073e31c00 0x19f83e3039f18e00

def z817 : W := mkw 0xa001100013349ed5 0xd0008800099a4f6a 0x0400000003149fff 0x02000000018a4fff

def z818 : W := mkw 0x016ceb0000ca4000 0x00b6758000652000 0x31fffd8000eb6000 0x18fffec00075b000

def z819 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xfff0fff8f3ffffff 0xfff87ffc79ffffff

def z820 : W := mkw 0x714fa7adae99e9ae 0xb8a7d3d6d74cf4d7 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z821 : W := mkw 0x4090105011671719 0x2048082808b38b8c 0xbff07078f3e71f19 0xdff8383c79f38f8c

def z822 : W := mkw 0x0216227668000000 0x010b113b34000000 0xda0f7264fc000000 0xed07b9327e000000

def z823 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xff7ffffffc17839f 0xffbffffffe0bc1cf

def z824 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x16f0706073e41c19 0x0b78383039f20e0c

def z825 : W := mkw 0x007eee7ee8000000 0x003f773f74000000 0xfa7ffe7ffc000000 0xfd3fff3ffe000000

def z826 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfe7ffffffc040019 0xff3ffffffe02000c

def z827 : W := mkw 0x216dfb0013decc94 0x90b6fd8009ef664a 0xf9ffff8003fffc01 0x7cffffc001fffe00

def z828 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07ff8f3e7ff19 0xdff83ffc79f3ff8c

def z829 : W := mkw 0x924fa3a72e9828e2 0xc927d1d3974c1471 0x400f83870c18e0e6 0x2007c1c3860c7073

def z830 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xfffff07ff3f81fe1 0xfffff83ff9fc0ff0

def z831 : W := mkw 0x00b05cd9d5661611 0x00582e6ceab30b08 0xfaf0ffffffe01c00 0xfd787ffffff00e00

def z832 : W := mkw 0x82256f89eeb81ac1 0xc112b7c4f75c0d60 0x85807f80fff81fe1 0x42c03fc07ffc0ff0

def z833 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xfff0fc7ff3ffffff 0xfff87e3ff9ffffff

def z834 : W := mkw 0x200722243a100c94 0x900391121d08064a 0xde0f7264ff101c9f 0xef07b9327f880e4f

def z835 : W := mkw 0xa00732243b9c8cd4 0xd00399121dce466a 0xde0f7264ff1c9cff 0xef07b9327f8e4e7f

def z836 : W := mkw 0x00366a7468000000 0x001b353a34000000 0x127f706070000000 0x093fb83038000000

def z837 : W := mkw 0x4010145891251719 0x20080a2c48928b8c 0xbff07c78f3e71f19 0xdff83e3c79f38f8c

def z838 : W := mkw 0x700110001315adbe 0xb8008800098ad6df 0x0400000003149fff 0x02000000018a4fff

def z839 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff83ff03f8ffe1 0xbfffc1ff81fc7ff0

def z840 : W := mkw 0x827eefffec201241 0x413f77fff6100920 0xfa7ffffffc000360 0xfd3ffffffe0001b0

def z841 : W := mkw 0x0101100013dec410 0x0080880009ef6208 0x0580000003fffc19 0x02c0000001fffe0c

def z842 : W := mkw 0x0006222428000000 0x0003111214000000 0xde0f7264fc100081 0xef07b9327e080040

def z843 : W := mkw 0x00266e2ce8000000 0x0013371674000000 0xda0f7e64fc000000 0xed07bf327e000000

def z844 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff0fdfbf3ffffff 0xdff87efdf9ffffff

def z845 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xbff07ff8ffe71f19 0xdff83ffc7ff38f8c

def z846 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0x33f0fdfb73eb7f60 0x19f87efdb9f5bfb0

def z847 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x33f0707873e01f00 0x19f8383c39f00f80

def z848 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff07e78f3f79f19 0xfff83f3c79fbcf8c

def z849 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc0b63fe 0xffbffffffe05b1ff

def z850 : W := mkw 0x500626adac01212a 0x28031356d6009095 0xde0f727ffc0003fe 0xef07b93ffe0001ff

def z851 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff9b03ffe361 0x7cffffcd81fff1b0

def z852 : W := mkw 0x300110811714acb6 0x980088408b8a565b 0x440083870f1cfcff 0x220041c3878e7e7f

def z853 : W := mkw 0x2001100013568c94 0x9000880009ab464a 0x0580000003f79c9f 0x02c0000001fbce4f

def z854 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0xfa7f7e7cfc000000 0xfd3fbf3e7e000000

def z855 : W := mkw 0x8001100013bc1ed1 0xc000880009de0f68 0x0580000003fc1ff9 0x02c0000001fe0ffc

def z856 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x327ffde070000000 0x193ffef038000000

def z857 : W := mkw 0xa04fa2262a9888c4 0xd027d113154c4462 0xed0f821f8c1c83ff 0xf687c10fc60e41ff

def z858 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x7ff0f07f73f81fe1 0xbff8783fb9fc0ff0

def z859 : W := mkw 0xc081140893ff1fd9 0xe0408a0449ff8fec 0xed808c1f83ff1ff9 0xf6c0460fc1ff8ffc

def z860 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff848fffe001 0xfcffffc247fff000

def z861 : W := mkw 0x4006262ca8010108 0x2003131654008084 0xff0f7e7cfc070319 0xff87bf3e7e03818c

def z862 : W := mkw 0x60b76e7cea739b8d 0xb05bb73e7539cdc6 0x61ff0e1c0cf38386 0x30ff870e0679c1c3

def z863 : W := mkw 0x027eefffec880000 0x013f77fff6440000 0xfbfffffffce80000 0xfdfffffffe740000

def z864 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0000000003109c86 0x0000000001884e43

def z865 : W := mkw 0x827eeb7668a81241 0x413f75bb34540920 0x33fff07b70e80360 0x19fff83db87401b0

def z866 : W := mkw 0x8049800002b81ac1 0xc024c000015c0d60 0x7dff801f03f81fe1 0xbeffc00f81fc0ff0

def z867 : W := mkw 0x52a47f89fd47253a 0x29523fc4fea3929d 0x80007f80fc07e01e 0x40003fc07e03f00f

def z868 : W := mkw 0x016deb0002dac000 0x00b6f580016d6000 0x79ff8f8003fbe001 0x3cffc7c001fdf000

def z869 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xd27fffe7fc000000 0x693ffff3fe000000

def z870 : W := mkw 0x025ea7ffec000000 0x012f53fff6000000 0xda0ff3fffc000000 0xed07f9fffe000000

def z871 : W := mkw 0x40a0580011671719 0x20502c0008b38b8c 0xbff07c60f3e71f19 0xdff83e3079f38f8c

def z872 : W := mkw 0x2006322439040c94 0x900319121c82064a 0xde0f7264ff041c9f 0xef07b9327f820e4f

def z873 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x7a7ff06070000000 0x3d3ff83038000000

def z874 : W := mkw 0x70a47e89fd47a53e 0x38523f44fea3d29f 0x80007f80fc07e01e 0x40003fc07e03f00f

def z875 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07df8f3e77f19 0xdff83efc79f3bf8c

def z876 : W := mkw 0x0006222428000000 0x0003111214000000 0xde0f7264fc040019 0xef07b9327e02000c

def z877 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0fc7fffff1fff 0xfff87e3fffff8fff

def z878 : W := mkw 0x827eefffeca81ac1 0xc13f77fff6540d60 0xfffffffffce81fe0 0xfffffffffe740ff0

def z879 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x5eff007f03f01fe1 0xaf7f803f81f80ff0

def z880 : W := mkw 0x037eefffec424000 0x01bf77fff6212000 0xfa7ffffffc036000 0xfd3ffffffe01b000

def z881 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfb7ffffffc1fe361 0xfdbffffffe0ff1b0

def z882 : W := mkw 0x210733243b14cc94 0x908399921d8a664a 0xde0f73e4ff14fc9f 0xef07b9f27f8a7e4f

def z883 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xda7f7fe4fc000000 0xed3fbff27e000000

def z884 : W := mkw 0x0059805002b81201 0x002cc028015c0900 0x7fff807f03f81fe1 0xbfffc03f81fc0ff0

def z885 : W := mkw 0x2081100013769e95 0x9040880009bb4f4a 0x0480000003f49c9f 0x0240000001fa4e4f

def z886 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbef07c78f3e01f18 0xdf783e3c79f00f8c

def z887 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc07e000 0xfd3ffffffe03f000

def z888 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xde0f727fff149fff 0xef07b93fff8a4fff

def z889 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xff0f727cff149f9f 0xff87b93e7f8a4fcf

def z890 : W := mkw 0xd278cddbc4a9336b 0x693c66ede25499b5 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z891 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xba7ffdfbf0000000 0xdd3ffefdf8000000

def z892 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x12f07c6073e31c00 0x09783e3039f18e00

def z893 : W := mkw 0x0000100011040410 0x0000080008820208 0xbff07060f3e41c19 0xdff8383079f20e0c

def z894 : W := mkw 0x805ea27628a81241 0x402f513b14540920 0xfbfff27ffce80360 0xfdfff93ffe7401b0

def z895 : W := mkw 0xd0f8ccdbc4eb336b 0x687c666de27599b5 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z896 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fffcffffff9f 0xfff87ffe7fffffcf

def z897 : W := mkw 0xd27eefffeca9336b 0x693f77fff65499b5 0xfffffffffcffe3ff 0xfffffffffe7ff1ff

def z898 : W := mkw 0x816dfb0203dec040 0x40b6fd8101ef6020 0xf9ffff8303ffe061 0x7cffffc181fff030

def z899 : W := mkw 0x0013007402301a81 0x8009803a01180d40 0x7fff807f03f81fe1 0xbfffc03f81fc0ff0

def z900 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07c78f3ffff19 0xdff83e3c79ffff8c

def z901 : W := mkw 0x516dff8987dfe12a 0x28b6ffc4c3eff095 0x14ff701f8fe003fe 0x8a7fb80fc7f001ff

def z902 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x9af07060f3e01c00 0xcd78383079f00e00

def z903 : W := mkw 0x004db200039c8000 0x0026d90001ce4000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z904 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x927f7260fc000000 0x493fb9307e000000

def z905 : W := mkw 0x014da3000298c000 0x00a6d180014c6000 0xf9ff8f8003ffe001 0x7cffc7c001fff000

def z906 : W := mkw 0x0002002400000000 0x0001001200000000 0xda0f7064f0000000 0xed07b83278000000

def z907 : W := mkw 0x500004898401212a 0x28000244c2009095 0xff008fff8f1fffff 0xff8047ffc78fffff

def z908 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x960f7264ff049c9e 0xcb07b9327f824e4f

def z909 : W := mkw 0x024ea32628000000 0x0127519314000000 0xda0f7264fc000000 0xed07b9327e000000

def z910 : W := mkw 0x027acdffc4000000 0x013d66ffe2000000 0xfa7ffdfff0000000 0xfd3ffefff8000000

def z911 : W := mkw 0x02feefffec621201 0x017f77fff6310900 0xfafffffffce00000 0xfd7ffffffe700000

def z912 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc0703ff 0xffbffffffe0381ff

def z913 : W := mkw 0x216dfb0003dec884 0x90b6fd8001ef6442 0xf9ffff8003ffe087 0x7cffffc001fff043

def z914 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfb7ffffffc180001 0xfdbffffffe0c0000

def z915 : W := mkw 0x52feefffec63332b 0x297f77fff6319995 0xfbfffffffceb6360 0xfdfffffffe75b1b0

def z916 : W := mkw 0x00304c58c0201201 0x0018262c60100900 0xbaf07c78f3e01c00 0xdd783e3c79f00e00

def z917 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xde7f7264fc14809f 0xef3fb9327e0a404f

def z918 : W := mkw 0x300110001314acb6 0x98008800098a565b 0x04000000031cfcff 0x02000000018e7e7f

def z919 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x9e0f7260ff049c1f 0xcf07b9307f824e0f

def z920 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0x7a7ff3ff7c000000 0xbd3ff9ffbe000000

def z921 : W := mkw 0x824fa3262a9808c0 0xc127d193154c0460 0x400f8007001800e0 0x2007c003800c0070

def z922 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff9f8fffe3ff 0xfeffffcfc7fff1ff

def z923 : W := mkw 0x827eeb7668201ac1 0xc13f75bb34100d60 0x127f706070001c00 0x093fb83038000e00

def z924 : W := mkw 0x0004220000000000 0x0002110000000000 0xda0f7260f0000000 0xed07b93078000000

def z925 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x5e0f7064ff101c9f 0xaf07b8327f880e4f

def z926 : W := mkw 0x51f8cdd9c4eb732b 0x28fc66ece275b995 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z927 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0000000003049c1e 0x0000000001824e0f

def z928 : W := mkw 0x0005320013148410 0x00029900098a4208 0xde0f7264ff149c9f 0xef07b9327f8a4e4f

def z929 : W := mkw 0x81367b760166dac1 0xc09b3dbb00b36d60 0x86007fff0007ffe0 0xc3003fff8003fff0

def z930 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x127f707b70000000 0x093fb83db8000000

def z931 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff9f03ffe001 0xfcffffcf81fff000

def z932 : W := mkw 0x200732243b568c94 0x900399121dab464a 0xdf8f7264fff79c9f 0xefc7b9327ffbce4f

def z933 : W := mkw 0x42ceb3a73d671719 0x216759d39eb38b8c 0x458f83870fe71f19 0x22c7c1c387f38f8c

def z934 : W := mkw 0x52f8cddbc463332b 0x297c66ede2319995 0x21f08d9b00eb6360 0x10f846cd8075b1b0

def z935 : W := mkw 0xd01204ff84213beb 0xe809027fc2109df5 0x0600007f00001fe0 0x8300003f80000ff0

def z936 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff8fff03f81fe1 0xffffc7ff81fc0ff0

def z937 : W := mkw 0x700114899715adbe 0xb8008a44cb8ad6df 0x0400001f8f149fff 0x8200000fc78a4fff

def z938 : W := mkw 0x2006222438000c94 0x900311121c00064a 0xde0f7264fc149c9f 0xef07b9327e0a4e4f

def z939 : W := mkw 0x500004898401212a 0x28000244c2009095 0x65008f9f0c1fe3ff 0x328047cf860ff1ff

def z940 : W := mkw 0x127eebf76c002022 0x093f75fbb6001011 0x527ff3e77c18e0e6 0x293ff9f3be0c7073

def z941 : W := mkw 0xd24fa7afae9929ea 0xe927d3d7d74c94f5 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z942 : W := mkw 0x827eefffec880040 0x413f77fff6440020 0xfa7ffffffc080060 0xfd3ffffffe040030

def z943 : W := mkw 0x0181100013fed611 0x00c0880009ff6b08 0x0180000003fffc01 0x00c0000001fffe00

def z944 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff07e7cffe71f19 0xfff83f3e7ff38f8c

def z945 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0x12f0706073e71c18 0x0978383039f38e0c

def z946 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x9af0706073e41c01 0x4d78383039f20e00

def z947 : W := mkw 0x020622a72c000000 0x0103115396000000 0xda0f7267fc000000 0xed07b933fe000000

def z948 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff8003eb6000 0x7cffffc001f5b000

def z949 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff8003ffe3e1 0x7effffc001fff1f0

def z950 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x3fff007f03e01fe1 0x9fff803f81f00ff0

def z951 : W := mkw 0x827eefffec201ac1 0xc13f77fff6100d60 0xfa7ffffffc001c00 0xfd3ffffffe000e00

def z952 : W := mkw 0x0010105011241611 0x0008082808920b08 0x3ff0707873e01f01 0x9ff8383c39f00f80

def z953 : W := mkw 0x006eeb2428000000 0x0037759214000000 0xff7fffe4fc1fe09f 0xffbffff27e0ff04f

def z954 : W := mkw 0x0006222428000000 0x0003111214000000 0xda0f726070000000 0x6d07b93038000000

def z955 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x71ffff8003fbe000 0x38ffffc001fdf000

def z956 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff0fc7bf3ef1f79 0xdff87e3df9f78fbc

def z957 : W := mkw 0x004ea32428000000 0x0027519214000000 0xda0ff3e4fc000000 0xed07f9f27e000000

def z958 : W := mkw 0x227eefffec008004 0x113f77fff6004002 0xfa7ffffffc008006 0xfd3ffffffe004003

def z959 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xfb7ffffffc1fe0e7 0xfdbffffffe0ff073

def z960 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff07e7ffff79fff 0xfff83f3ffffbcfff

def z961 : W := mkw 0x0169d90003dec000 0x00b4ec8001ef6000 0x79ff8d8003ffe001 0x3cffc6c001fff000

def z962 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xbaf07c6073e01c00 0x5d783e3039f00e00

def z963 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x16f0707873e01f00 0x8b78383c39f00f80

def z964 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0ffffffe7ff1f 0xfff87ffffff3ff8f

def z965 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xbff07078f3e41f19 0xdff8383c79f20f8c

def z966 : W := mkw 0x016deb0002dac000 0x00b6f580016d6000 0xe9ff8f8000ffe001 0x74ffc7c0007ff000

def z967 : W := mkw 0x2003102413148c94 0x90018812098a464a 0x0600006403149c9f 0x83000032018a4e4f

def z968 : W := mkw 0x016deb0002da4000 0x00b6f580016d2000 0xf9ffff8003fb6001 0x7cffffc001fdb000

def z969 : W := mkw 0x427eef7ee8010108 0x213f77bf74008084 0xbf7f7c78f0070319 0xdfbfbe3c7803818c

def z970 : W := mkw 0x2169d90013decc94 0x90b4ec8009ef664a 0x25f08d8003fffc9f 0x12f846c001fffe4f

def z971 : W := mkw 0x2001100013148c94 0x90008800098a464a 0xcc00020003149c9f 0x66000100018a4e4f

def z972 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xff0f7e64ff179c9f 0xff87bf327f8bce4f

def z973 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x97f07c60f3e71f19 0x4bf83e3079f38f8c

def z974 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xc20ffffffc000000 0xe107fffffe000000

def z975 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x37f07c78f3e31f18 0x9bf83e3c79f18f8c

def z976 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xba7f7c7ffc000000 0xdd3fbe3ffe000000

def z977 : W := mkw 0x8059805202b81ac1 0xc02cc029015c0d60 0x7dff801b03f81fe1 0x3effc00d81fc0ff0

def z978 : W := mkw 0x016cfb0001ce4000 0x00b67d8000e72000 0xf9ffff8003ef6001 0x7cffffc001f7b000

def z979 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff827f0ff89fe7 0xbfffc13f87fc4ff3

def z980 : W := mkw 0x026eefafec000000 0x013777d7f6000000 0xe80fff9ffc000000 0xf407ffcffe000000

def z981 : W := mkw 0x0001100013140c90 0x80008800098a0648 0x0400000003141c99 0x02000000018a0e4c

def z982 : W := mkw 0x407acc7ec0010108 0x203d663f60008084 0xff7ffc7ff01f03f9 0xffbffe3ff80f81fc

def z983 : W := mkw 0x02266fadec000000 0x011337d6f6000000 0xc00f7f84fc000000 0x6007bfc27e000000

def z984 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfb7ffffffc080360 0xfdbffffffe0401b0

def z985 : W := mkw 0x027eefffec000880 0x813f77fff6000440 0xfe7ffffffc001c80 0xff3ffffffe000e40

def z986 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x96f07c78f3e71f18 0xcb783e3c79f38f8c

def z987 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x000000000014809e 0x00000000000a404f

def z988 : W := mkw 0x005a807600000000 0x002d403b00000000 0xfa7ff07ff0000000 0xfd3ff83ff8000000

def z989 : W := mkw 0x214fa3242a98c884 0x90a7d192154c6442 0x400f83800018e000 0x2007c1c0000c7000

def z990 : W := mkw 0xc0ebdc2ed3df0dd8 0xe075ee1769ef86ec 0xc00ffc07f01f00f8 0x6007fe03f80f807c

def z991 : W := mkw 0x805a807600a81241 0x402d403b00540920 0x7fff807f03e81f61 0xbfffc03f81f40fb0

def z992 : W := mkw 0x026eefafec000000 0x013777d7f6000000 0xf87fff87fc000000 0x7c3fffc3fe000000

def z993 : W := mkw 0x0020580011460410 0x00102c0008a30208 0xfff0ffe4fffffc9f 0xfff87ff27ffffe4f

def z994 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xff0ff264ff1c9c9f 0xff87f9327f8e4e4f

def z995 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xde0ff267ff1c9cff 0xef07f933ff8e4e7f

def z996 : W := mkw 0x0006222428000000 0x0003111214000000 0xde0f7264ff001c01 0xef07b9327f800e00

def z997 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x127f707f70000000 0x893fb83fb8000000

def z998 : W := mkw 0x0006222428000000 0x0003111214000000 0xc00f7204fc000000 0x6007b9027e000000

def z999 : W := mkw 0x50366efdec01212a 0x281b377ef6009095 0xff7ffffffc1fe3ff 0xffbffffffe0ff1ff

def z1000 : W := mkw 0xf001100013bdbfff 0xf800880009dedfff 0x0580000003ffffff 0x02c0000001ffffff

def z1001 : W := mkw 0x004ea22428000000 0x0027511214000000 0xfa7ff264fc000000 0xfd3ff9327e000000

def z1002 : W := mkw 0xc0b05c5ad1671759 0x60582e2d68b38bac 0xbff07c7bf3e71f79 0xdff83e3df9f38fbc

def z1003 : W := mkw 0x500626adac01212a 0x28031356d6009095 0xfb0ffffffc0b6360 0xfd87fffffe05b1b0

def z1004 : W := mkw 0x0168c90000ca4000 0x00b4648000652000 0x79ff8d8000eb6000 0x3cffc6c00075b000

def z1005 : W := mkw 0x700114899715adbe 0xb8008a44cb8ad6df 0x84000f808f17fc9f 0x420007c0478bfe4f

def z1006 : W := mkw 0x006ceb0000000000 0x0036758000000000 0xfa7fffe0f0000000 0xfd3ffff078000000

def z1007 : W := mkw 0x827eefffec201ac1 0xc13f77fff6100d60 0xff7ffffffc181fe1 0xffbffffffe0c0ff0

def z1008 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xb9fffd8003ef6001 0x5cfffec001f7b000

def z1009 : W := mkw 0x2006222428008004 0x1003111214004002 0xda0f7264fc008006 0xed07b9327e004003

def z1010 : W := mkw 0x214fa3242a98c884 0x90a7d192154c6442 0x400f02040c108086 0x2007810206084043

def z1011 : W := mkw 0x0016227428201201 0x000b113a14100900 0xffff727cffe01f01 0xffffb93e7ff00f80

def z1012 : W := mkw 0x027eefffec201201 0x013f77fff6100900 0xfaffffffffe01c00 0xfd7ffffffff00e00

def z1013 : W := mkw 0x41dda758d2b9d719 0x20eed3ac695ceb8c 0x460f83f8f018ff18 0xa307c1fc780c7f8c

def z1014 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc108086 0xfd3ffffffe084043

def z1015 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x31fffd8003ffe001 0x18fffec001fff000

def z1016 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xfff0fffffff79f9f 0xfff87ffffffbcfcf

def z1017 : W := mkw 0xd21204ffec213beb 0xe909027ff6109df5 0x0600007ffc001ffe 0x8300003ffe000fff

def z1018 : W := mkw 0x016dfb0013dec410 0x00b6fd8009ef6208 0xfbffffe073fffc01 0x7dfffff039fffe00

def z1019 : W := mkw 0x0006222428000000 0x0003111214000000 0xda0f7264fc148001 0xed07b9327e0a4000

def z1020 : W := mkw 0x02266b2468000000 0x0113359234000000 0x120f706070000000 0x0907b83038000000

def z1021 : W := mkw 0x709204fdfc213fbf 0xb849027efe109fdf 0x0600007ffc001ffe 0x8300003ffe000fff

def z1022 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xff7ffffffc1fe09f 0xffbffffffe0ff04f

def z1023 : W := mkw 0x026cef89ec000000 0x013677c4f6000000 0xc00fff80fc000000 0x6007ffc07e000000

def z1024 : W := mkw 0x42feefffec211309 0x217f77fff6108984 0xfa7ffffffc000300 0xfd3ffffffe000180

def z1025 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0xbff07c6073e71f19 0x5ff83e3039f38f8c

def z1026 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0400000003001c9e 0x0200000001800e4f

def z1027 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x127f7060fc000000 0x093fb8307e000000

def z1028 : W := mkw 0x016dfb0003dec880 0x80b6fd8001ef6440 0xfdffff8003fffc81 0x7effffc001fffe40

def z1029 : W := mkw 0xf001148997bdbfff 0xf8008a44cbdedfff 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z1030 : W := mkw 0x42feefffec631309 0x217f77fff6318984 0xffffffffffe31f01 0xfffffffffff18f80

def z1031 : W := mkw 0x0006222428000000 0x0003111214000000 0xde0f7264fc00009e 0xef07b9327e00004f

def z1032 : W := mkw 0x527eeb766801212a 0x293f75bb34009095 0x177f7060701fe3ff 0x0bbfb830380ff1ff

def z1033 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fc7ff3e71f19 0xfff87e3ff9f38f8c

def z1034 : W := mkw 0xf01204ffbc213fff 0xf809027fde109fff 0x0600007ffc001ffe 0x8300003ffe000fff

def z1035 : W := mkw 0x006eeb2428000000 0x0037759214000000 0xfa7fffe070000000 0x7d3ffff038000000

def z1036 : W := mkw 0x216dfb0013dec414 0x10b6fd8009ef620a 0xf9ffff8003ffe01f 0x7cffffc001fff00f

def z1037 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff8403ffe081 0xfeffffc201fff040

def z1038 : W := mkw 0x526cef89ec01212a 0x293677c4f6009095 0xf97fff80fc1fe01f 0x7cbfffc07e0ff00f

def z1039 : W := mkw 0x805b80762ab81ac1 0xc02dc03b155c0d60 0x7fff807ffff81fe1 0xbfffc03ffffc0ff0

def z1040 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbbf07c78f3e31f00 0xddf83e3c79f18f80

def z1041 : W := mkw 0x0006222428000000 0x0003111214000000 0x920f7260fc000000 0x4907b9307e000000

def z1042 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x10ff7d8003e36000 0x087fbec001f1b000

def z1043 : W := mkw 0xd081148997ff3ffb 0xe8408a44cbff9ffd 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z1044 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x12ff007b03e01f60 0x097f803d81f00fb0

def z1045 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x727fffff7c000000 0x393fffffbe000000

def z1046 : W := mkw 0x02266fadec000000 0x011337d6f6000000 0xfa0ffffffc000000 0xfd07fffffe000000

def z1047 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xbff07c60f3e71c19 0xdff83e3079f38e0c

def z1048 : W := mkw 0x10b058d155663633 0x08582c68aab31b19 0x52f0f3e77ff8fce6 0x297879f3bffc7e73

def z1049 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x4c00000403149c9f 0xa6000002018a4e4f

def z1050 : W := mkw 0x2006222428000884 0x9003111214000442 0xda0f7264fc000086 0xed07b9327e000043

def z1051 : W := mkw 0x006eeb2428000000 0x0037759214000000 0xda7f7264fc000000 0xed3fb9327e000000

def z1052 : W := mkw 0x52266fadec01212a 0x291337d6f6009095 0xde0f7fe4fc17e09f 0xef07bff27e0bf04f

def z1053 : W := mkw 0x0006322439040410 0x000319121c820208 0xde0f7264ff149c9f 0xef07b9327f8a4e4f

def z1054 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x9ef07c60f3e71c19 0xcf783e3079f38e0c

def z1055 : W := mkw 0x4081100013771f99 0xa040880009bb8fcc 0x0580000003f71f99 0x02c0000001fb8fcc

def z1056 : W := mkw 0x41fcef58c0eb5309 0x20fe77ac6075a984 0xfbfffff8f0eb6300 0xfdfffffc7875b180

def z1057 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xff7ffffffc1fe3e1 0xffbffffffe0ff1f0

def z1058 : W := mkw 0x8012007600201ac1 0xc009003b00100d60 0xef008fff001fffe1 0xf78047ff800ffff0

def z1059 : W := mkw 0x000626adac000000 0x00031356d6000000 0xda0f727ffc000000 0xed07b93ffe000000

def z1060 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07c78ffe71f1f 0xdff83e3c7ff38f8f

def z1061 : W := mkw 0x500004898401212a 0x28000244c2009095 0xfdf08f9f8fffe3ff 0xfef847cfc7fff1ff

def z1062 : W := mkw 0x2001100013349e95 0x90008800099a4f4a 0x0580000003f49f9f 0x02c0000001fa4fcf

def z1063 : W := mkw 0x007eef7ec0000000 0x003f77bf60000000 0xfa7ffffff0000000 0xfd3ffffff8000000

def z1064 : W := mkw 0x006cef08c0000000 0x0036778460000000 0xf87fff80f0000000 0x7c3fffc078000000

def z1065 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x527ff3fffc000000 0xa93ff9fffe000000

def z1066 : W := mkw 0x815b817602b85ac1 0xc0adc0bb015c2d60 0x7fff81ff03f87fe1 0xbfffc0ff81fc3ff0

def z1067 : W := mkw 0x026eeb2668000000 0x0137759334000000 0x000f700070000000 0x0007b80038000000

def z1068 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xdef07264fff49c9f 0xef7839327ffa4e4f

def z1069 : W := mkw 0x2101100013decc94 0x9080880009ef664a 0x0480000003f49c9f 0x0240000001fa4e4f

def z1070 : W := mkw 0x0006222428000000 0x0003111214000000 0x9a0f7060f0000000 0xcd07b83078000000

def z1071 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff807f03ffffe1 0xbfffc03f81fffff0

def z1072 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xd20f7264ff149c9e 0x6907b9327f8a4e4f

def z1073 : W := mkw 0x200732243b9c8c94 0x900399121dce464a 0xdf8f7264fffc9c9f 0xefc7b9327ffe4e4f

def z1074 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xde0f7fe4ff17fc9f 0xef07bff27f8bfe4f

def z1075 : W := mkw 0x0030585011661611 0x00182c2808b30b08 0xbff07c78f3e71f19 0xdff83e3c79f38f8c

def z1076 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbbf07c7873e71f01 0x5df83e3c39f38f80

def z1077 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff8083ffe019 0xfeffffc041fff00c

def z1078 : W := mkw 0x007ceb5040000000 0x003e75a820000000 0xfa7fffe070000000 0x7d3ffff038000000

def z1079 : W := mkw 0x234fa3a72e98c884 0x91a7d1d3974c6442 0x400f83870c18e086 0x2007c1c3860c7043

def z1080 : W := mkw 0xa059905213bc9ed5 0xd02cc82909de4f6a 0x25f0801b03fc9fff 0x12f8400d81fe4fff

def z1081 : W := mkw 0x007acc7ec0000000 0x003d663f60000000 0xba7f7c78f0000000 0xdd3fbe3c78000000

def z1082 : W := mkw 0x0020580011460410 0x00102c0008a30208 0x12f0706073e01c00 0x0978383039f00e00

def z1083 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0ffffffef7f79 0xfff87ffffff7bfbc

def z1084 : W := mkw 0x6081100013779f9d 0xb040880009bbcfce 0x0580000003e71f19 0x02c0000001f38f8c

def z1085 : W := mkw 0x016dfb0013dec410 0x00b6fd8009ef6208 0xffffffe4fffffc9f 0xfffffff27ffffe4f

def z1086 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xb9ff7f8003e7e001 0x5cffbfc001f3f000

def z1087 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x127f7064fc000000 0x893fb8327e000000

def z1088 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfa7ffffffc00001e 0xfd3ffffffe00000f

def z1089 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xda0f7260ff149c1f 0x6d07b9307f8a4e0f

def z1090 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xde0ff3e4ff1cfc9f 0xef07f9f27f8e7e4f

def z1091 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x65ff801f03f81fe1 0x32ffc00f81fc0ff0

def z1092 : W := mkw 0x527eefffec21332b 0x293f77fff6109995 0xffffffffffffffff 0xffffffffffffffff

def z1093 : W := mkw 0x007ceb5040000000 0x003e75a820000000 0x127f706070000000 0x093fb83038000000

def z1094 : W := mkw 0x216dfb0013decc94 0x90b6fd8009ef664a 0xfdffff848ffffc9f 0xfeffffc247fffe4f

def z1095 : W := mkw 0x024ea3a72c000000 0x012751d396000000 0x520ff3e77c000000 0x2907f9f3be000000

def z1096 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0xfa7ffc7ff0000000 0xfd3ffe3ff8000000

def z1097 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff807f03fc9fff 0xbfffc03f81fe4fff

def z1098 : W := mkw 0x708110001377bfbf 0xb840880009bbdfdf 0x0580000003ffffff 0x02c0000001ffffff

def z1099 : W := mkw 0x4181100013dfc518 0x20c0880009efe28c 0x0180000003ffe019 0x00c0000001fff00c

def z1100 : W := mkw 0x827eefffec0008c0 0xc13f77fff6000460 0xfa7ffffffc0000e0 0xfd3ffffffe000070

def z1101 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x05000000031c9fff 0x02800000018e4fff

def z1102 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0x127f73e07c000000 0x093fb9f03e000000

def z1103 : W := mkw 0x427eefffec211309 0x213f77fff6108984 0xffffffffffe71f19 0xfffffffffff38f8c

def z1104 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0x16f0706073e01f18 0x0b78383039f00f8c

def z1105 : W := mkw 0x210110001356cc94 0x9080880009ab664a 0x040000000317fc9f 0x02000000018bfe4f

def z1106 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfbffffffffe00001 0xfdfffffffff00000

def z1107 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffb70000000 0x7d3ffffdb8000000

def z1108 : W := mkw 0xa14fa3262a98c8c4 0xd0a7d193154c6462 0x400f83870c18e0e6 0x2007c1c3860c7073

def z1109 : W := mkw 0x0003102413140c90 0x80018812098a0648 0xde0f7264ff149c9f 0xef07b9327f8a4e4f

def z1110 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfb7ffffffc0fe37e 0xfdbffffffe07f1bf

def z1111 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x3bf0706073e01c01 0x1df8383039f00e00

def z1112 : W := mkw 0x210732243bdecc94 0x908399121def664a 0xff8fffe4fffffc9f 0xffc7fff27ffffe4f

def z1113 : W := mkw 0x708114899777bfbf 0xb8408a44cbbbdfdf 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z1114 : W := mkw 0x60b15c58d3779f9d 0xb058ae2c69bbcfce 0x25f00c1803f79f9f 0x12f8060c01fbcfcf

def z1115 : W := mkw 0x41b05d58d1675719 0x20d82eac68b3ab8c 0xbff07df8f3e77f19 0xdff83efc79f3bf8c

def z1116 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0000000003149c01 0x00000000018a4e00

def z1117 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0fff8ffffff1f 0xfff87ffc7fffff8f

def z1118 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07c78f3f79f9f 0xdff83e3c79fbcfcf

def z1119 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xbff07c78f3e7ff1f 0xdff83e3c79f3ff8f

def z1120 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xba7f7c6070000000 0x5d3fbe3038000000

def z1121 : W := mkw 0x526cef89ec01212a 0x293677c4f6009095 0xfd7fff9ffc1fe3ff 0xfebfffcffe0ff1ff

def z1122 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0xbff07c78f3e01f01 0xdff83e3c79f00f80

def z1123 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xff7ffffffc000301 0xffbffffffe000180

def z1124 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x7f7ff07f701803e1 0xbfbff83fb80c01f0

def z1125 : W := mkw 0x007ac87640000000 0x003d643b20000000 0x7a7ff07f70000000 0xbd3ff83fb8000000

def z1126 : W := mkw 0x006eefadac000000 0x003777d6d6000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z1127 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff807f83fc1ff9 0xffffc03fc1fe0ffc

def z1128 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xfe7ffffffc1ce0ff 0xff3ffffffe0e707f

def z1129 : W := mkw 0x40b66e7ce8631309 0x205b373e74318984 0xfbff7e7cfce30300 0xfdffbf3e7e718180

def z1130 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0x16f0707fffe01ffe 0x8b78383ffff00fff

def z1131 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xbff07c7873e71f01 0xdff83e3c39f38f80

def z1132 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x160f7064ff149c9f 0x8b07b8327f8a4e4f

def z1133 : W := mkw 0xd27eefffeca9336b 0x693f77fff65499b5 0xfbfffffffceb6360 0xfdfffffffe75b1b0

def z1134 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff808fffe01f 0x7cffffc047fff00f

def z1135 : W := mkw 0x021626ffec000000 0x010b137ff6000000 0x120f707ffc000000 0x8907b83ffe000000

def z1136 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc148001 0xfd3ffffffe0a4000

def z1137 : W := mkw 0xa05b807602b89ac5 0xd02dc03b015c4d62 0x7fff807f03f89fe7 0xbfffc03f81fc4ff3

def z1138 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0x12f07078f3e01c00 0x8978383c79f00e00

def z1139 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc18e000 0xfd3ffffffe0c7000

def z1140 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x9a7f7060f0000000 0xcd3fb83078000000

def z1141 : W := mkw 0x027cefdbc4000000 0x013e77ede2000000 0xfa7ffffbf0000000 0xfd3ffffdf8000000

def z1142 : W := mkw 0x026ceb0068000000 0x0136758034000000 0x107f700070000000 0x083fb80038000000

def z1143 : W := mkw 0x0000000000000000 0x0000000000000000 0xed008f9f8c1fe3ff 0xf68047cfc60ff1ff

def z1144 : W := mkw 0xf04fa6afae99a9ee 0xf827d357d74cd4f7 0xed0f8f9f8c1fe3ff 0xf687c7cfc60ff1ff

def z1145 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc1803ff 0xffbffffffe0c01ff

def z1146 : W := mkw 0x804fa2262a9808c0 0xc027d113154c0460 0x400f82070c1800e0 0x2007c103860c0070

def z1147 : W := mkw 0x0010005000201201 0x0008002800100900 0xbff07078f3e01f01 0xdff8383c79f00f80

def z1148 : W := mkw 0x0016227428000000 0x000b113a14000000 0xfa7f727cfc000000 0xfd3fb93e7e000000

def z1149 : W := mkw 0x827eefffeca81241 0x413f77fff6540920 0xffffffffffe81f61 0xfffffffffff40fb0

def z1150 : W := mkw 0x006eeb2428000000 0x0037759214000000 0x127f706070000000 0x093fb83038000000

def z1151 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xfa7ffffffc00e006 0xfd3ffffffe007003

def z1152 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0x337ffdfb700b6360 0x19bffefdb805b1b0

def z1153 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xe07fff9ffc000000 0x703fffcffe000000

def z1154 : W := mkw 0x40b04c58d0211719 0x2058262c68108b8c 0xbff07c78f3e01f19 0xdff83e3c79f00f8c

def z1155 : W := mkw 0x2001100013148c94 0x90008800098a464a 0xed008f80031ffc9f 0x768047c0018ffe4f

def z1156 : W := mkw 0x0006222428000000 0x0003111214000000 0xda0f7264fc108086 0xed07b9327e084043

def z1157 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xfa7fffff70000000 0xfd3fffffb8000000

def z1158 : W := mkw 0x0169d90003de4000 0x00b4ec8001ef2000 0xf9fffd8003ff6001 0x7cfffec001ffb000

def z1159 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fe7fffff9fff 0xfff87f3fffffcfff

def z1160 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xfdffff9803ffe301 0xfeffffcc01fff180

def z1161 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc07e31f 0xffbffffffe03f18f

def z1162 : W := mkw 0x0016267ce8000000 0x000b133e74000000 0xda0f727cfc000000 0xed07b93e7e000000

def z1163 : W := mkw 0x016deb0002dac000 0x00b6f580016d6000 0xf9ffff8000fbe000 0x7cffffc0007df000

def z1164 : W := mkw 0xa001100013bc9ed5 0xd000880009de4f6a 0x0480000003f49c9f 0x0240000001fa4e4f

def z1165 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x3fff807b03e81f61 0x9fffc03d81f40fb0

def z1166 : W := mkw 0x827eeb7668a81241 0x413f75bb34540920 0x12ff706070e00000 0x097fb83038700000

def z1167 : W := mkw 0x026cef89ec000000 0x013677c4f6000000 0xf87fff9ffc000000 0xfc3fffcffe000000

def z1168 : W := mkw 0x007cefd9c4000000 0x003e77ece2000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z1169 : W := mkw 0x016cfb0001cec000 0x00b67d8000e76000 0xf9ffff8000efe000 0x7cffffc00077f000

def z1170 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xfe0ff27fff149c9f 0xff07f93fff8a4e4f

def z1171 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc04801e 0xfd3ffffffe02400f

def z1172 : W := mkw 0x124ea3a72c002022 0x092751d396001011 0xde0ff3e7fc1ce0ff 0xef07f9f3fe0e707f

def z1173 : W := mkw 0x5181100013fff73b 0x28c0880009fffb9d 0x0580000003ffffff 0x02c0000001ffffff

def z1174 : W := mkw 0x037eeb7668ca4000 0x01bf75bb34652000 0x12ff706070e00000 0x097fb83038700000

def z1175 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07c7ff3e71ff9 0xdff83e3ff9f38ffc

def z1176 : W := mkw 0x52266fadec01212a 0x291337d6f6009095 0xff0ffffffc1fe3ff 0xff87fffffe0ff1ff

def z1177 : W := mkw 0x0006222428000880 0x8003111214000440 0xde0f7264fc001c80 0xef07b9327e000e40

def z1178 : W := mkw 0x006deb0002980000 0x0036f580014c0000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1179 : W := mkw 0x8059805202b81241 0x402cc029015c0920 0x7fff807b03f81f61 0xbfffc03d81fc0fb0

def z1180 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x327ff07b70000000 0x193ff83db8000000

def z1181 : W := mkw 0x529204fffc21373b 0x2949027ffe109b9d 0x0600007ffc001ffe 0x8300003ffe000fff

def z1182 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7fffe0fc000000 0x7d3ffff07e000000

def z1183 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x927f7ffffc000000 0xc93fbffffe000000

def z1184 : W := mkw 0x216dfb002bdec004 0x10b6fd8015ef6002 0xf9ffff800fffe007 0x7cffffc007fff003

def z1185 : W := mkw 0x500004898401212a 0x28000244c2009095 0xc4008f9f8c1fe3fe 0xe20047cfc60ff1ff

def z1186 : W := mkw 0x0006222428000000 0x0003111214000000 0xda0f7264fc04801e 0xed07b9327e02400f

def z1187 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff0fdffffef7fff 0xdff87efffff7bfff

def z1188 : W := mkw 0x8013007602301ac1 0xc009803b01180d60 0x7fff007f03f01fe1 0xbfff803f81f80ff0

def z1189 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x73ff807f03f81fe0 0x39ffc03f81fc0ff0

def z1190 : W := mkw 0x827eefffeca81241 0x413f77fff6540920 0xfafffffffce00000 0xfd7ffffffe700000

def z1191 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xff7ffffffc1f03f9 0xffbffffffe0f81fc

def z1192 : W := mkw 0x037eefffecca4000 0x01bf77fff6652000 0xfafffffffce00000 0xfd7ffffffe700000

def z1193 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x527ff3e070000000 0x293ff9f038000000

def z1194 : W := mkw 0x024ea3a72c000000 0x012751d396000000 0xc00ff387fc000000 0x6007f9c3fe000000

def z1195 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7eff807f03e01fe0 0xbf7fc03f81f00ff0

def z1196 : W := mkw 0xc0f9dc5ad3ff1fd9 0xe07cee2d69ff8fec 0x25f08c1b03ff1ff9 0x12f8460d81ff8ffc

def z1197 : W := mkw 0x0149900003dec000 0x00a4c80001ef6000 0xf9ff8f8003ffe001 0x7cffc7c001fff000

def z1198 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf9ffff840fffe087 0x7cffffc207fff043

def z1199 : W := mkw 0x80314c58c2b81ac1 0xc018a62c615c0d60 0xbff07c78f3f81fe1 0xdff83e3c79fc0ff0

def z1200 : W := mkw 0x016ceb0000ca4000 0x00b6758000652000 0x61ff8f8000eb6000 0x30ffc7c00075b000

def z1201 : W := mkw 0x521626ffec01212a 0x290b137ff6009095 0xff0ffffffc1fe3ff 0xff87fffffe0ff1ff

def z1202 : W := mkw 0x020626adec000000 0x01031356f6000000 0xda0f7264fc000000 0xed07b9327e000000

def z1203 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xdf0f7264ff1ffc9f 0xef87b9327f8ffe4f

def z1204 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xda7f727ffc000000 0xed3fb93ffe000000

def z1205 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0x32f07c7873e01c00 0x19783e3c39f00e00

def z1206 : W := mkw 0x02feeb7668621201 0x017f75bb34310900 0x12ff706070e00000 0x097fb83038700000

def z1207 : W := mkw 0x0010105011241611 0x0008082808920b08 0xfff0f27ffffc9fff 0xfff8793ffffe4fff

def z1208 : W := mkw 0x824fa3262a9808c0 0xc127d193154c0460 0x000f000000000000 0x0007800000000000

def z1209 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0x127ff1e370000000 0x093ff8f1b8000000

def z1210 : W := mkw 0x42feefffec430108 0x217f77fff6218084 0xfa7ffffffc030000 0xfd3ffffffe018000

def z1211 : W := mkw 0x815b807602b8dac1 0xc0adc03b015c6d60 0x7fff807f03f8ffe1 0xbfffc03f81fc7ff0

def z1212 : W := mkw 0x2011105013349e95 0x90088828099a4f4a 0x3ff0007803f49f9f 0x9ff8003c01fa4fcf

def z1213 : W := mkw 0x816dfb0003dec8c0 0xc0b6fd8001ef6460 0xf9ffff8003ffe0e1 0x7cffffc001fff070

def z1214 : W := mkw 0x02366ffdec000000 0x011b37fef6000000 0xfa7f7ffcfc000000 0xfd3fbffe7e000000

def z1215 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff0fffbffefff7f 0xdff87ffdfff7ffbf

def z1216 : W := mkw 0x016eeb2428ca4000 0x00b7759214652000 0xfbffffe4fceb6000 0xfdfffff27e75b000

def z1217 : W := mkw 0x40b04c58c0631309 0x2058262c60318984 0xbff07c78f3e31f01 0xdff83e3c79f18f80

def z1218 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x91ff7f8003ffe001 0x48ffbfc001fff000

def z1219 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x1ef0706073e01c01 0x8f78383039f00e00

def z1220 : W := mkw 0x037eefffec884000 0x01bf77fff6442000 0xfa7ffffffc086000 0xfd3ffffffe043000

def z1221 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xbff07c78f3ef7f79 0xdff83e3c79f7bfbc

def z1222 : W := mkw 0xa04fa2262a9888c4 0xd027d113154c4462 0x400f02040c108086 0x2007810206084043

def z1223 : W := mkw 0x016deb0002dac000 0x00b6f580016d6000 0x21ff8d8000eb6000 0x10ffc6c00075b000

def z1224 : W := mkw 0x007eef7ce8000000 0x003f77be74000000 0xfa7ffffcfc000000 0xfd3ffffe7e000000

def z1225 : W := mkw 0x027eeb7668201201 0x013f75bb34100900 0x12ff706073e01c00 0x097fb83039f00e00

def z1226 : W := mkw 0x02366fffec000000 0x011b37fff6000000 0xda0f7ffffc000000 0xed07bffffe000000

def z1227 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0x13f0706073e31f00 0x09f8383039f18f80

def z1228 : W := mkw 0x6081100013578d9c 0xb040880009abc6ce 0x0400000003179c9f 0x02000000018bce4f

def z1229 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x560f7264ff109c9e 0xab07b9327f884e4f

def z1230 : W := mkw 0x700114899715adbe 0xb8008a44cb8ad6df 0x25008d9b031fffff 0x128046cd818fffff

def z1231 : W := mkw 0x827eefffeca81241 0x413f77fff6540920 0xfffffffffcf803e1 0xfffffffffe7c01f0

def z1232 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xfa7fffe4fc000000 0xfd3ffff27e000000

def z1233 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x6d00801f031c9fff 0xb680400f818e4fff

def z1234 : W := mkw 0x50b058505167373b 0x28582c2828b39b9d 0x17f0706073ffffff 0x0bf8383039ffffff

def z1235 : W := mkw 0x0030485040201201 0x0018242820100900 0x12f0706073e01c00 0x0978383039f00e00

def z1236 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0400000003101c81 0x0200000001880e40

def z1237 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x12f0707873e01f00 0x0978383c39f00f80

def z1238 : W := mkw 0x0006222428000000 0x0003111214000000 0xff0ff27ffc1803e1 0xff87f93ffe0c01f0

def z1239 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x840002008f149c9f 0x42000100478a4e4f

def z1240 : W := mkw 0x027cefd9ec000000 0x013e77ecf6000000 0xfa7ffff8fc000000 0xfd3ffffc7e000000

def z1241 : W := mkw 0x6001100013158d9c 0xb0008800098ac6ce 0x0500000003179f9f 0x02800000018bcfcf

def z1242 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0x927f7c60f0000000 0x493fbe3078000000

def z1243 : W := mkw 0x026ceb0068000000 0x0136758034000000 0xf87fff8070000000 0x7c3fffc038000000

def z1244 : W := mkw 0x026eefafec000000 0x013777d7f6000000 0x800f7f80fc000000 0x4007bfc07e000000

def z1245 : W := mkw 0x0069d80003de0000 0x0034ec0001ef0000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1246 : W := mkw 0xa04fa2262a9888c4 0xd027d113154c4462 0x400f8007001800e0 0x2007c003800c0070

def z1247 : W := mkw 0x0169c90002da4000 0x00b4e480016d2000 0x31ff8d8003eb6000 0x18ffc6c001f5b000

def z1248 : W := mkw 0x52feefffec63332b 0x297f77fff6319995 0xfffffffffcffe3ff 0xfffffffffe7ff1ff

def z1249 : W := mkw 0x40304c58c0211309 0x2018262c60108984 0xbff07c78f3e71f19 0xdff83e3c79f38f8c

def z1250 : W := mkw 0x026eeba72c000000 0x013775d396000000 0xfa7fffe7fc000000 0xfd3ffff3fe000000

def z1251 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x960f7260ff149c9f 0x4b07b9307f8a4e4f

def z1252 : W := mkw 0x0006262ca8000000 0x0003131654000000 0xfa0f7e7cfc000000 0xfd07bf3e7e000000

def z1253 : W := mkw 0x020623a52c000000 0x010311d296000000 0xda0f73e4fc000000 0xed07b9f27e000000

def z1254 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc0f6379 0xffbffffffe07b1bc

def z1255 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff8c7f03ff1fe1 0xffffc63f81ff8ff0

def z1256 : W := mkw 0x216dfb003bdec414 0x10b6fd801def620a 0xfdffff84ffffe09f 0xfeffffc27ffff04f

def z1257 : W := mkw 0x0216227668000000 0x010b113b34000000 0x120f706070000000 0x0907b83038000000

def z1258 : W := mkw 0xe081100013ff9fdd 0xf040880009ffcfee 0x0580000003ff9fff 0x02c0000001ffcfff

def z1259 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07fffffe7ffff 0xdff83ffffff3ffff

def z1260 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x7a7ffdff70000000 0xbd3ffeffb8000000

def z1261 : W := mkw 0x210732243bdecc94 0x908399121def664a 0xde8f7264fff49c9f 0xef47b9327ffa4e4f

def z1262 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x17f07078f3e71f19 0x8bf8383c79f38f8c

def z1263 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xffff7264fff49c9f 0xffffb9327ffa4e4f

def z1264 : W := mkw 0x2006322439048414 0x100319121c82420a 0xde0f7264ff049c1f 0xef07b9327f824e0f

def z1265 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff07ffcfff7ff9f 0xfff83ffe7ffbffcf

def z1266 : W := mkw 0x506eefadac01212a 0x283777d6d6009095 0xff7ffffffc1fe3ff 0xffbffffffe0ff1ff

def z1267 : W := mkw 0x214fa3242a98c884 0x90a7d192154c6442 0xed0f8f848c1fe09f 0xf687c7c2460ff04f

def z1268 : W := mkw 0x507cefd9c401212a 0x283e77ece2009095 0xff7ffffffc1fe3ff 0xffbffffffe0ff1ff

def z1269 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xfa7ffffffc070018 0xfd3ffffffe03800c

def z1270 : W := mkw 0x526eefafec01212a 0x293777d7f6009095 0xed0fff9ffc1fe3ff 0xf687ffcffe0ff1ff

def z1271 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0x9ff07060f3e71f19 0xcff8383079f38f8c

def z1272 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xd8ff7f8003f7e001 0x6c7fbfc001fbf000

def z1273 : W := mkw 0x027eefffec201201 0x013f77fff6100900 0xfe7ffffffc001f00 0xff3ffffffe000f80

def z1274 : W := mkw 0x824fa7afae9808c0 0xc127d3d7d74c0460 0xed0f8f9f8c1803e1 0xf687c7cfc60c01f0

def z1275 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x527f72647c000000 0x293fb9323e000000

def z1276 : W := mkw 0x00324c7cc0000000 0x0019263e60000000 0xfa7f7c7cf0000000 0xfd3fbe3e78000000

def z1277 : W := mkw 0x004b802402980880 0x8025c012014c0440 0x7fff807f03f81fe1 0xbfffc03f81fc0ff0

def z1278 : W := mkw 0x016cfb000146c000 0x00b67d8000a36000 0xf9ffff8003e7e001 0x7cffffc001f3f000

def z1279 : W := mkw 0xa001100013bc9ed5 0xd000880009de4f6a 0x0080000003e01c00 0x0040000001f00e00

def z1280 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x3ff07078f3e01f19 0x9ff8383c79f00f8c

def z1281 : W := mkw 0x51a47f89d547e53a 0x28d23fc4eaa3f29d 0x80007f80fc07e01e 0x40003fc07e03f00f

def z1282 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0xbbf07c78f3e71c01 0xddf83e3c79f38e00

def z1283 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x9ef07078f3e41f19 0xcf78383c79f20f8c

def z1284 : W := mkw 0x021626ffec000000 0x010b137ff6000000 0xfa0ffffffc000000 0xfd07fffffe000000

def z1285 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xc60f7264fc149c9e 0xe307b9327e0a4e4f

def z1286 : W := mkw 0x007ac87640000000 0x003d643b20000000 0x127f706070000000 0x093fb83038000000

def z1287 : W := mkw 0x5181148997fff73b 0x28c08a44cbfffb9d 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z1288 : W := mkw 0x0020580011460410 0x00102c0008a30208 0x9ef07060f3e41c19 0xcf78383079f20e0c

def z1289 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x3a7f707870000000 0x9d3fb83c38000000

def z1290 : W := mkw 0x20011000139c8c94 0x9000880009ce464a 0x0580000003fc9c9f 0x02c0000001fe4e4f

def z1291 : W := mkw 0x8081100013fe1ed1 0xc040880009ff0f68 0x0080000003e01c00 0x0040000001f00e00

def z1292 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfb7ffffffc1be3e6 0xfdbffffffe0df1f3

def z1293 : W := mkw 0x505ea6ffac01212a 0x282f537fd6009095 0xff7ffffffc1fe3ff 0xffbffffffe0ff1ff

def z1294 : W := mkw 0x00346e58c0000000 0x001a372c60000000 0xfa7f7e78f0000000 0xfd3fbf3c78000000

def z1295 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0x167f707ffc0003fe 0x8b3fb83ffe0001ff

def z1296 : W := mkw 0x6001140893158d9c 0xb0008a04498ac6ce 0xad000c1883179f9f 0xd680060c418bcfcf

def z1297 : W := mkw 0x6081140893779f9d 0xb0408a0449bbcfce 0xed800e1c8ff79f9f 0xf6c0070e47fbcfcf

def z1298 : W := mkw 0x02266fadec000000 0x011337d6f6000000 0x920f7fe0fc000000 0x4907bff07e000000

def z1299 : W := mkw 0x0010105011241611 0x0008082808920b08 0x12f0706073e01c00 0x0978383039f00e00

def z1300 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0xbef07c78f3e41c19 0xdf783e3c79f20e0c

def z1301 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x927f7fe070000000 0x493fbff038000000

def z1302 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xff7ffffffc1fe319 0xffbffffffe0ff18c

def z1303 : W := mkw 0x21011000139ccc94 0x9080880009ce664a 0x04000000031cfc9f 0x02000000018e7e4f

def z1304 : W := mkw 0x026cef89ec000000 0x013677c4f6000000 0x907f7f80fc000000 0x483fbfc07e000000

def z1305 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x92f07060f3e41c18 0x4978383079f20e0c

def z1306 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xbff07c7fffe71f19 0xdff83e3ffff38f8c

def z1307 : W := mkw 0x00366e7ce8000000 0x001b373e74000000 0xba7f7c78f0000000 0xdd3fbe3c78000000

def z1308 : W := mkw 0xa001100013bc9ed5 0xd000880009de4f6a 0x0580000003f81fe1 0x02c0000001fc0ff0

def z1309 : W := mkw 0x40205c0891470518 0x20102e0448a3828c 0xbff07c78f3e71f19 0xdff83e3c79f38f8c

def z1310 : W := mkw 0x40da907611671719 0x206d483b08b38b8c 0x7fff807f03e71f19 0xbfffc03f81f38f8c

def z1311 : W := mkw 0x01257b000356c000 0x0092bd8001ab6000 0xf9ff7f8003f7e001 0x7cffbfc001fbf000

def z1312 : W := mkw 0x0181100013fed611 0x00c0880009ff6b08 0x0080000003e01c00 0x0040000001f00e00

def z1313 : W := mkw 0x0020580011460410 0x00102c0008a30208 0xbbf07c6073e71c01 0x5df83e3039f38e00

def z1314 : W := mkw 0x41b05c58d167d719 0x20d82e2c68b3eb8c 0xbff07c78f3e7ff19 0xdff83e3c79f3ff8c

def z1315 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0xda7f726070000000 0x6d3fb93038000000

def z1316 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfe7ffffffc07e3fe 0xff3ffffffe03f1ff

def z1317 : W := mkw 0x50304cd9c421332b 0x2818266ce2109995 0xfff0ffffffffffff 0xfff87fffffffffff

def z1318 : W := mkw 0x407cef58c0010108 0x203e77ac60008084 0xff7ffff8f01fe319 0xffbffffc780ff18c

def z1319 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x17ff007f03f81fe1 0x8bff803f81fc0ff0

def z1320 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfa7ffffffc1800e0 0xfd3ffffffe0c0070

def z1321 : W := mkw 0x037eeb7668ca4000 0x01bf75bb34652000 0x33fffde070eb6000 0x19fffef03875b000

def z1322 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fffff3fffff9 0xfff87ffff9fffffc

def z1323 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0x79fffd8003fb6001 0x3cfffec001fdb000

def z1324 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xfa7ffffffc0000e6 0xfd3ffffffe000073

def z1325 : W := mkw 0x016dfb0013dec410 0x00b6fd8009ef6208 0xf9ffff80f3ffe019 0x7cffffc079fff00c

def z1326 : W := mkw 0x027eefffec420000 0x013f77fff6210000 0xfbfffffffce30000 0xfdfffffffe718000

def z1327 : W := mkw 0x00257a0003568000 0x0012bd0001ab4000 0xf9ffff8003ffe001 0x7cffffc001fff000

def z1328 : W := mkw 0x00305c58c1661201 0x00182e2c60b30900 0xbff07c78f3e71f01 0xdff83e3c79f38f80

def z1329 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff8dff03fb7fe1 0xbfffc6ff81fdbff0

def z1330 : W := mkw 0x200532003b148414 0x100299001d8a420a 0xde0f7260ff149c1f 0xef07b9307f8a4e0f

def z1331 : W := mkw 0x027eeb7668201201 0x013f75bb34100900 0x3fff707873e01f01 0x9fffb83c39f00f80

def z1332 : W := mkw 0xa17ffb763bfeded5 0xd0bffdbb1dff6f6a 0x12ff706073e01c00 0x097fb83039f00e00

def z1333 : W := mkw 0x000622a52c000000 0x0003115296000000 0xda0ff3e7fc000000 0xed07f9f3fe000000

def z1334 : W := mkw 0x025ea6ffec000000 0x012f537ff6000000 0xfa7ff27ffc000000 0xfd3ff93ffe000000

def z1335 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff8fff8fffffff 0xffffc7ffc7ffffff

def z1336 : W := mkw 0x2006222438000c94 0x900311121c00064a 0x160f7064fc001c9e 0x8b07b8327e000e4f

def z1337 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x1e00006003149c9f 0x8f000030018a4e4f

def z1338 : W := mkw 0x016dfb002bdec000 0x00b6fd8015ef6000 0xf9ffff80ffffe001 0x7cffffc07ffff000

def z1339 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xfff0ffffffff1ff9 0xfff87fffffff8ffc

def z1340 : W := mkw 0x0169c90002da4000 0x00b4e480016d2000 0x61ff8d8000fb6000 0x30ffc6c0007db000

def z1341 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0x3ff07c7873e31f01 0x9ff83e3c39f18f80

def z1342 : W := mkw 0x007accffc4000000 0x003d667fe2000000 0xfa7ffffffc000000 0xfd3ffffffe000000

def z1343 : W := mkw 0x004ea22628000000 0x0027511314000000 0xda0ff267fc000000 0xed07f933fe000000

def z1344 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfe7ffffffc100081 0xff3ffffffe080040

def z1345 : W := mkw 0x216dfb0013decc94 0x90b6fd8009ef664a 0xffffffe0f3fffc9f 0xfffffff079fffe4f

def z1346 : W := mkw 0x526eefafec01212a 0x293777d7f6009095 0xc00fff87fc1fe0fe 0x6007ffc3fe0ff07f

def z1347 : W := mkw 0x005ea27628000000 0x002f513b14000000 0x7a7ff07f70000000 0xbd3ff83fb8000000

def z1348 : W := mkw 0x02246f89ec000000 0x011237c4f6000000 0xd80f7f80fc000000 0x6c07bfc07e000000

def z1349 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfb7ffffffc0b6000 0xfdbffffffe05b000

def z1350 : W := mkw 0x200310243b148c94 0x900188121d8a464a 0x040000040f149c9f 0x02000002078a4e4f

def z1351 : W := mkw 0x500622242801212a 0x2803111214009095 0xdf0f7264fc1fe3ff 0xef87b9327e0ff1ff

def z1352 : W := mkw 0x02266b2468000000 0x0113359234000000 0xda0f7264fc000000 0xed07b9327e000000

def z1353 : W := mkw 0x227eefffec000884 0x913f77fff6000442 0xfa7ffffffc000086 0xfd3ffffffe000043

def z1354 : W := mkw 0x500004898401212a 0x28000244c2009095 0xe1008f9f8c1fe3fe 0x708047cfc60ff1ff

def z1355 : W := mkw 0x200310243b140c94 0x900188121d8a064a 0xde0f7064ff141c9f 0xef07b8327f8a0e4f

def z1356 : W := mkw 0x42feefffec631309 0x217f77fff6318984 0xfffffffffce70319 0xfffffffffe73818c

def z1357 : W := mkw 0x827eefffec201ac1 0xc13f77fff6100d60 0xffffffffffe01fe1 0xfffffffffff00ff0

def z1358 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfb7ffffffc1fe01f 0xfdbffffffe0ff00f

def z1359 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfa7ffffffc036000 0xfd3ffffffe01b000

def z1360 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x527ff06770000000 0x293ff833b8000000

def z1361 : W := mkw 0x027eebf76c000000 0x013f75fbb6000000 0x127f70677c000000 0x093fb833be000000

def z1362 : W := mkw 0x507accffc401212a 0x283d667fe2009095 0xff7ffffffc1fe3ff 0xffbffffffe0ff1ff

def z1363 : W := mkw 0x2101100013decc94 0x9080880009ef664a 0x0180000003fffc01 0x00c0000001fffe00

def z1364 : W := mkw 0xa04fa2262a9888c4 0xd027d113154c4462 0x000f000000000000 0x0007800000000000

def z1365 : W := mkw 0xc2feefffeceb1349 0x617f77fff67589a4 0xfbfffffffceb0360 0xfdfffffffe7581b0

def z1366 : W := mkw 0x4181140893ffd719 0x20c08a0449ffeb8c 0xed808f9883ffff19 0xf6c047cc41ffff8c

def z1367 : W := mkw 0x210732243b56cc94 0x908399121dab664a 0xde0f7264ff17fc9f 0xef07b9327f8bfe4f

def z1368 : W := mkw 0x0006222428000000 0x0003111214000000 0x5a0f706470000000 0xad07b83238000000

def z1369 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfe7ffffffc00009e 0xff3ffffffe00004f

def z1370 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0x327f7c7870000000 0x193fbe3c38000000

def z1371 : W := mkw 0x204fa2242a988884 0x9027d112154c4442 0x400f82040c188086 0x2007c102060c4043

def z1372 : W := mkw 0x8081100013fe1ed1 0xc040880009ff0f68 0x0580000003f81fe1 0x02c0000001fc0ff0

def z1373 : W := mkw 0x01edfb0053dec410 0x00f6fd8029ef6208 0xf9ffff8073ffe001 0x7cffffc039fff000

def z1374 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xff7ffffffc18e3e7 0xffbffffffe0c71f3

def z1375 : W := mkw 0x027eefffec201201 0x013f77fff6100900 0xfffffffffff81fe1 0xfffffffffffc0ff0

def z1376 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x9e0f7064ff041c9f 0xcf07b8327f820e4f

def z1377 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xde0f7264ff001c9e 0xef07b9327f800e4f

def z1378 : W := mkw 0x521626ffec01212a 0x290b137ff6009095 0xde0f727ffc1483ff 0xef07b93ffe0a41ff

def z1379 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xfe7ffffffc000318 0xff3ffffffe00018c

def z1380 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x040000048f149c9f 0x82000002478a4e4f

def z1381 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xb1ffff8003efe000 0x58ffffc001f7f000

def z1382 : W := mkw 0x40b0585051671719 0x20582c2828b38b8c 0x3ff0707873e71f19 0x9ff8383c39f38f8c

def z1383 : W := mkw 0xb04fa2a72e98a8e6 0xd827d153974c5473 0x400f83870c18e0e6 0x2007c1c3860c7073

def z1384 : W := mkw 0x0078cc58c0000000 0x003c662c60000000 0xfa7ffc78f0000000 0xfd3ffe3c78000000

def z1385 : W := mkw 0xa101100013feded5 0xd080880009ff6f6a 0x0580000003ffffff 0x02c0000001ffffff

def z1386 : W := mkw 0x025ea3f72c000000 0x012f51fb96000000 0xfa7ff3fffc000000 0xfd3ff9fffe000000

def z1387 : W := mkw 0x43feefffeceb5309 0x21ff77fff675a984 0xfbfffffffceb6300 0xfdfffffffe75b180

def z1388 : W := mkw 0x4181100013ffd719 0x20c0880009ffeb8c 0x0580000003e71f19 0x02c0000001f38f8c

def z1389 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0x92f07fe0ffe7fc1e 0x49783ff07ff3fe0f

def z1390 : W := mkw 0x027eef7ee8000000 0x013f77bf74000000 0x127f7078f0000000 0x893fb83c78000000

def z1391 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xff7ffffffc1c83ff 0xffbffffffe0e41ff

def z1392 : W := mkw 0x4081100013779719 0x2040880009bbcb8c 0x0580000003f79f19 0x02c0000001fbcf8c

def z1393 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0x127f7de070000000 0x093fbef038000000

def z1394 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0ffffffe71fff 0xfff87ffffff38fff

def z1395 : W := mkw 0x0006222428000000 0x0003111214000000 0xfb0fffe4fc1fe001 0xfd87fff27e0ff000

def z1396 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fc78f3ff1f19 0xfff87e3c79ff8f8c

def z1397 : W := mkw 0x027cefdbec000000 0x013e77edf6000000 0xf87fff9bfc000000 0x7c3fffcdfe000000

def z1398 : W := mkw 0x537eefffeccb612a 0x29bf77fff665b095 0xfbfffffffceb6360 0xfdfffffffe75b1b0

def z1399 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfe7ffffffc0003e0 0xff3ffffffe0001f0

def z1400 : W := mkw 0x2081100013769e95 0x9040880009bb4f4a 0x0080000003e01c00 0x0040000001f00e00

def z1401 : W := mkw 0x005ea27628000000 0x002f513b14000000 0xff7ff27ffc1c83ff 0xffbff93ffe0e41ff

def z1402 : W := mkw 0x501014d99525373b 0x28080a6cca929b9d 0xfff0ffffffffffff 0xfff87fffffffffff

def z1403 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x3af0707873e01c00 0x9d78383c39f00e00

def z1404 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x17f0706073e01f01 0x0bf8383039f00f80

def z1405 : W := mkw 0xc181100013ffdfd9 0xe0c0880009ffefec 0x0580000003fffff9 0x02c0000001fffffc

def z1406 : W := mkw 0x005ea27628000000 0x002f513b14000000 0xda7f7264fc000000 0xed3fb9327e000000

def z1407 : W := mkw 0x41f9dd58d3ffd719 0x20fceeac69ffeb8c 0x25f08d9803ffff19 0x12f846cc01ffff8c

def z1408 : W := mkw 0x837eefffecea5241 0x41bf77fff6752920 0xfbfffffffceb6360 0xfdfffffffe75b1b0

def z1409 : W := mkw 0x024ea32628000000 0x0127519314000000 0x120f706070000000 0x0907b83038000000

def z1410 : W := mkw 0x427eefffec010108 0x213f77fff6008084 0xfb7ffffffc030300 0xfdbffffffe018180

def z1411 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0xffff827f03fc9fe1 0xffffc13f81fe4ff0

def z1412 : W := mkw 0x805b807602b81ac1 0xc02dc03b015c0d60 0x7fff807f8ff81fff 0xbfffc03fc7fc0fff

def z1413 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xff7ffffffc1b63e1 0xffbffffffe0db1f0

def z1414 : W := mkw 0x00305c58d1241611 0x00182e2c68920b08 0xbff07c78f3e41f19 0xdff83e3c79f20f8c

def z1415 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xfff0fff8f3e71f19 0xfff87ffc79f38f8c

def z1416 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfa7ffffffc1fe0fe 0xfd3ffffffe0ff07f

def z1417 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff07c78f3ff1ff9 0xdff83e3c79ff8ffc

def z1418 : W := mkw 0xc081100013ff1fd9 0xe040880009ff8fec 0x0580000003e71f19 0x02c0000001f38f8c

def z1419 : W := mkw 0x40901458d1251719 0x20480a2c68928b8c 0xbff07078f3e41f19 0xdff8383c79f20f8c

def z1420 : W := mkw 0x00b05c58d1661611 0x00582e2c68b30b08 0x92f07c60f3e01c00 0x49783e3079f00e00

def z1421 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xb27ffffbfc000000 0x593ffffdfe000000

def z1422 : W := mkw 0xd27eefffec213beb 0xe93f77fff6109df5 0xff7ffffffc1fffff 0xffbffffffe0fffff

def z1423 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x8c00000083149c9f 0xc6000000418a4e4f

def z1424 : W := mkw 0x524ea7afac01212a 0x292753d7d6009095 0xff0ffffffc1fe3ff 0xff87fffffe0ff1ff

def z1425 : W := mkw 0x024ea7afac000000 0x012753d7d6000000 0xfa0ffffffc000000 0xfd07fffffe000000

def z1426 : W := mkw 0xa013107613349ed5 0xd009883b099a4f6a 0x0600007f03149fff 0x8300003f818a4fff

def z1427 : W := mkw 0x016dfb0003dec000 0x00b6fd8001ef6000 0xf8ffff8003e7e000 0x7c7fffc001f3f000

def z1428 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0x92f07c6073e71c00 0x49783e3039f38e00

def z1429 : W := mkw 0xa24fa3a72e9888c4 0xd127d1d3974c4462 0x400f83870c1880e6 0x2007c1c3860c4073

def z1430 : W := mkw 0x216dfb003bdec414 0x10b6fd801def620a 0xf9ffff8073ffe001 0x7cffffc039fff000

def z1431 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfb7ffffffc070001 0xfdbffffffe038000

def z1432 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xba7f7ff8fc000000 0xdd3fbffc7e000000

def z1433 : W := mkw 0x127eefffec002022 0x093f77fff6001011 0xfa7ffffffc086060 0xfd3ffffffe043030

def z1434 : W := mkw 0x50205c899547253a 0x28102e44caa3929d 0xfff0ffffffffffff 0xfff87fffffffffff

def z1435 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfa7ffffffc000360 0xfd3ffffffe0001b0

def z1436 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xb3f07c78f3e71f18 0x59f83e3c79f38f8c

def z1437 : W := mkw 0x825b80766ab81ac1 0xc12dc03b355c0d60 0x7fff807f73f81fe1 0xbfffc03fb9fc0ff0

def z1438 : W := mkw 0xa00732263b148cd4 0xd00399131d8a466a 0xde0f7267ff149cff 0xef07b933ff8a4e7f

def z1439 : W := mkw 0x0169c90002da4000 0x00b4e480016d2000 0xf9ff8f8003ffe001 0x7cffc7c001fff000

def z1440 : W := mkw 0x71247f89bd47e53e 0x38923fc4dea3f29f 0x80007f80fc07e01e 0x40003fc07e03f00f

def z1441 : W := mkw 0x2001148997148c94 0x90008a44cb8a464a 0xec008f9f8f149c9f 0xf60047cfc78a4e4f

def z1442 : W := mkw 0x50b05c58d167373b 0x28582e2c68b39b9d 0xfff07e7cffffffff 0xfff83f3e7fffffff

def z1443 : W := mkw 0x200532003b148c94 0x900299001d8a464a 0x040002000f149c9f 0x02000100078a4e4f

def z1444 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07c7bf3e71f79 0xdff83e3df9f38fbc

def z1445 : W := mkw 0x504984898699212a 0x2824c244c34c9095 0x7dff801f8ff803ff 0xbeffc00fc7fc01ff

def z1446 : W := mkw 0x00304cd9c4201201 0x0018266ce2100900 0xfff0fffffff81fe1 0xfff87ffffffc0ff0

def z1447 : W := mkw 0x026eeba76c000000 0x013775d3b6000000 0x400ff3877c000000 0x2007f9c3be000000

def z1448 : W := mkw 0x40b05cd9d5671719 0x20582e6ceab38b8c 0xfff0ffffffffff19 0xfff87fffffffff8c

def z1449 : W := mkw 0x4081100013ff1719 0x2040880009ff8b8c 0x0580000003ff1f19 0x02c0000001ff8f8c

def z1450 : W := mkw 0x027eeb7668000000 0x013f75bb34000000 0x5a7f706470000000 0xad3fb83238000000

def z1451 : W := mkw 0x2001100013148c94 0x90008800098a464a 0x0400000003041c19 0x0200000001820e0c

def z1452 : W := mkw 0x00266b2428000000 0x0013359214000000 0xda0f7fe4fc000000 0xed07bff27e000000

def z1453 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07ff8ffffffff 0xdff83ffc7fffffff

def z1454 : W := mkw 0x2006322439048c94 0x900319121c82464a 0xde0f7264fc049c9e 0xef07b9327e024e4f

def z1455 : W := mkw 0x40b05c58d1671719 0x20582e2c68b38b8c 0xbff0fdf8f3ef7f19 0xdff87efc79f7bf8c

def z1456 : W := mkw 0x0004220028000000 0x0002110014000000 0xd80f7200fc000000 0x6c07b9007e000000

def z1457 : W := mkw 0x0016227628000000 0x000b113b14000000 0xda0f727ffc000000 0xed07b93ffe000000

def z1458 : W := mkw 0x00b0585051661611 0x00582c2828b30b08 0xfbf0ffe073fffc01 0x7df87ff039fffe00

def z1459 : W := mkw 0x7101148997dfedbe 0xb8808a44cbeff6df 0xed808f9f8fffffff 0xf6c047cfc7ffffff

def z1460 : W := mkw 0x527eefffec01212a 0x293f77fff6009095 0xfe7ffffffc17e09f 0xff3ffffffe0bf04f

def z1461 : W := mkw 0x42b05dd9d5671719 0x21582eeceab38b8c 0xbff07df8f3e71f19 0xdff83efc79f38f8c

def z1462 : W := mkw 0x027accffec000000 0x013d667ff6000000 0xfa7ffc7ffc000000 0xfd3ffe3ffe000000

def z1463 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0xdf0f7264ff1c9fff 0xef87b9327f8e4fff

def z1464 : W := mkw 0x200732243b148c94 0x900399121d8a464a 0x120f7060ff001c1e 0x0907b8307f800e0f

def z1465 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xbff07c7fffffffff 0xdff83e3fffffffff

def z1466 : W := mkw 0x027eefffec000000 0x013f77fff6000000 0xfe7fffffff001c01 0xff3fffffff800e00

def z1467 : W := mkw 0x0010105011241611 0x0008082808920b08 0x9ef07060f3e41c19 0xcf78383079f20e0c

def z1468 : W := mkw 0x2001100013148414 0x10008800098a420a 0x000000000314801f 0x00000000018a400f

def z1469 : W := mkw 0x50b05cd9d567373b 0x28582e6ceab39b9d 0xfff0fdfff3ff7ff9 0xfff87efff9ffbffc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z8,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z10,z6]),(0,[z0,z11,z2,z3,z5,z6,z12])],[(0,[z0,z11,z2,z3,z5,z13,z6]),(0,[z14,z0,z11,z2,z5,z15,z6]),(0,[z9,z7,z0,z2,z3,z5,z6]),(1,[z0,z16,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z18,z6]),(0,[z0,z11,z19,z2,z3,z20,z6])],[(0,[z0,z8,z2,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z21,z6])],[(0,[z9,z0,z11,z22,z3,z5,z6])],[(0,[z23,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z24,z5,z6]),(0,[z25,z0,z11,z2,z5,z15,z6])],[(0,[z0,z11,z2,z3,z5,z26,z6]),(0,[z0,z11,z2,z27,z3,z5,z6]),(1,[z0,z28,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z29,z6]),(0,[z0,z11,z30,z19,z3,z5,z6])],[(0,[z9,z31,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z32,z5,z6]),(0,[z25,z0,z2,z33,z3,z5,z6]),(0,[z0,z11,z34,z2,z3,z5,z6]),(0,[z0,z11,z2,z35,z3,z5,z6])],[],[(0,[z0,z8,z2,z3,z36,z5,z6]),(0,[z0,z37,z11,z2,z3,z5,z6])],[(0,[z38,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z39,z6,z40])],[(0,[z41,z0,z11,z2,z3,z5,z6]),(0,[z42,z0,z2,z3,z5,z17,z6]),(0,[z43,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z5,z6]),(0,[z44,z0,z11,z2,z3,z5,z6]),(0,[z0,z45,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z46,z6]),(0,[z0,z47,z11,z2,z3,z5,z6]),(0,[z48,z0,z11,z2,z3,z20,z6]),(0,[z0,z49,z11,z2,z3,z5,z6])],[(0,[z50,z51,z11,z2,z3,z5,z6]),(0,[z50,z0,z11,z2,z4,z5,z6]),(0,[z52,z0,z2,z3,z5,z17,z6])],[(0,[z0,z11,z2,z3,z5,z6,z53]),(0,[z54,z0,z11,z2,z3,z5,z6]),(0,[z14,z0,z11,z2,z3,z55,z6]),(0,[z0,z8,z2,z33,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z56]),(0,[z0,z11,z2,z3,z5,z6,z40])],[(0,[z0,z11,z2,z3,z5,z6,z57]),(0,[z0,z11,z2,z3,z5,z58,z6])]],
   [[(0,[z0,z11,z2,z3,z5,z10,z6]),(0,[z0,z16,z2,z3,z5,z10,z6]),(0,[z0,z11,z2,z3,z5,z59,z6])],[(0,[z60,z0,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z5,z15,z61,z6])],[(1,[z0,z2,z62,z3,z5,z6]),(0,[z0,z11,z2,z63,z3,z5,z6]),(1,[z47,z11,z2,z3,z5,z6]),(0,[z0,z11,z64,z2,z3,z5,z6])],[(0,[z65,z0,z2,z33,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z66,z6]),(0,[z0,z67,z11,z2,z3,z5,z6]),(0,[z68,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z69,z6]),(1,[z0,z70,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z71,z5,z6]),(1,[z51,z11,z72,z3,z5,z6]),(1,[z0,z11,z2,z73,z5,z6]),(0,[z0,z11,z2,z3,z24,z5,z6]),(1,[z74,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z75,z6])],[(0,[z31,z0,z2,z3,z5,z17,z6])],[(0,[z0,z11,z2,z3,z5,z76,z6]),(0,[z0,z11,z2,z77,z3,z5,z6])],[(0,[z0,z11,z2,z78,z3,z5,z6]),(0,[z0,z11,z2,z3,z79,z5,z6]),(0,[z42,z0,z8,z2,z3,z5,z6]),(0,[z0,z1,z2,z35,z3,z5,z6]),(0,[z48,z0,z11,z2,z3,z5,z76]),(0,[z0,z11,z80,z2,z3,z5,z6])],[(0,[z81,z50,z11,z2,z3,z5,z6]),(1,[z11,z2,z82,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z83,z6])],[(0,[z0,z8,z2,z3,z5,z39,z6])],[(0,[z84,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z85,z5,z6]),(0,[z86,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z87,z3,z5,z6]),(0,[z88,z0,z11,z2,z3,z5,z6]),(0,[z89,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z90,z2,z3,z5,z6]),(0,[z9,z0,z11,z8,z3,z5,z6]),(0,[z0,z45,z11,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z91,z11,z2,z3,z5,z6]),(0,[z0,z11,z3,z5,z39,z6,z92])],[(0,[z0,z93,z11,z2,z3,z5,z6])],[(0,[z94,z0,z11,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z57]),(0,[z95,z0,z11,z2,z96,z5,z6]),(0,[z0,z11,z2,z5,z15,z20,z6]),(0,[z97,z98,z0,z11,z2,z5,z6])]],
   [[(0,[z0,z99,z11,z2,z3,z5,z6]),(1,[z0,z2,z5,z15,z17,z6]),(0,[z0,z11,z2,z3,z100,z5,z6]),(0,[z0,z11,z101,z2,z3,z5,z6])],[(0,[z0,z102,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z103,z3,z5,z6]),(0,[z104,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z105,z6])],[(0,[z106,z0,z11,z30,z3,z5,z6]),(0,[z106,z0,z11,z2,z3,z5,z39])],[(0,[z0,z11,z2,z3,z107,z5,z6])],[(0,[z0,z8,z2,z3,z5,z108,z6])],[(0,[z0,z8,z2,z3,z5,z6,z109]),(0,[z0,z11,z2,z110,z3,z5,z6])],[(0,[z111,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z112,z6])],[(0,[z14,z0,z11,z2,z79,z5,z6]),(0,[z14,z0,z11,z2,z73,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z113]),(0,[z114,z0,z11,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z92]),(0,[z0,z115,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z116])],[(0,[z51,z11,z72,z2,z3,z5,z6]),(0,[z117,z0,z11,z2,z3,z5,z6])],[(0,[z118,z9,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z119,z6])],[(0,[z0,z11,z2,z3,z5,z6,z120])],[(0,[z44,z0,z11,z2,z121,z5,z6]),(0,[z106,z9,z0,z2,z3,z5,z6])],[(0,[z0,z11,z122,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z55,z6]),(0,[z0,z123,z8,z2,z3,z5,z6]),(1,[z0,z11,z2,z35,z5,z108]),(0,[z0,z11,z2,z35,z3,z5,z108])],[(0,[z124,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z72,z2,z3,z5,z6]),(1,[z7,z11,z2,z3,z121,z6]),(0,[z0,z125,z2,z3,z5,z17,z6]),(0,[z0,z126,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z127])],[(0,[z0,z128,z8,z2,z3,z5,z6])],[(0,[z0,z11,z2,z129,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z130,z6])],[(0,[z0,z11,z2,z3,z5,z131,z6]),(0,[z0,z11,z2,z3,z5,z132,z6]),(0,[z60,z0,z11,z2,z3,z5,z10]),(0,[z48,z0,z11,z2,z107,z5,z6]),(0,[z0,z11,z2,z35,z5,z108,z6])],[(0,[z133,z0,z11,z2,z3,z5,z6]),(0,[z134,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z135,z6])],[(0,[z136,z0,z11,z2,z3,z5,z6]),(0,[z137,z98,z0,z11,z2,z5,z6])],[(0,[z81,z0,z8,z2,z3,z5,z6]),(0,[z31,z0,z11,z2,z3,z5,z10]),(0,[z138,z0,z11,z2,z3,z5,z6])],[(1,[z9,z0,z22,z3,z5,z6]),(0,[z0,z11,z2,z3,z139,z5,z6]),(0,[z14,z11,z2,z3,z5,z55,z6])],[(0,[z0,z11,z140,z2,z3,z5,z6]),(0,[z141,z9,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z4,z5,z15,z6]),(0,[z9,z0,z2,z35,z3,z5,z6]),(0,[z0,z11,z2,z3,z142,z5,z6])],[(1,[z0,z2,z3,z143,z5,z6]),(0,[z144,z0,z11,z2,z3,z5,z6])],[(0,[z145,z0,z11,z2,z3,z5,z6]),(0,[z0,z125,z8,z2,z3,z5,z6])],[(1,[z0,z146,z2,z3,z5,z6]),(0,[z0,z147,z1,z2,z3,z5,z6]),(0,[z148,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z149])],[(0,[z50,z0,z2,z3,z5,z17,z6])],[(0,[z124,z0,z11,z2,z3,z5,z6])]],
   [[(0,[z150,z0,z11,z2,z3,z5,z6]),(0,[z0,z8,z19,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z15,z6]),(0,[z0,z11,z2,z3,z151,z5,z6])],[(0,[z152,z0,z11,z2,z3,z5,z6])],[(0,[z153,z11,z154,z2,z3,z5,z6]),(0,[z9,z0,z2,z22,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z155]),(1,[z156,z0,z2,z3,z17,z6])],[(0,[z9,z0,z2,z3,z5,z157,z6]),(1,[z11,z2,z158,z3,z5,z6])],[],[(0,[z0,z28,z11,z2,z3,z5,z6])],[(0,[z159,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z105,z6]),(1,[z0,z11,z2,z5,z29,z6])],[(0,[z0,z11,z2,z3,z160,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z161]),(0,[z0,z11,z2,z3,z5,z6,z162]),(1,[z0,z11,z2,z3,z5,z76]),(0,[z0,z11,z2,z5,z163,z15,z6]),(0,[z0,z11,z2,z35,z3,z5,z164])],[(0,[z0,z11,z2,z3,z5,z6,z165]),(0,[z0,z11,z2,z166,z3,z5,z6]),(0,[z167,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z168,z5,z75,z6])],[(0,[z169,z0,z11,z2,z3,z5,z6]),(0,[z60,z0,z11,z2,z3,z5,z57]),(0,[z0,z11,z2,z170,z3,z5,z6]),(0,[z171,z0,z11,z2,z3,z5,z6])],[(0,[z9,z9,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z172,z6]),(0,[z118,z98,z0,z11,z2,z5,z6])],[(1,[z65,z153,z2,z3,z5,z6]),(0,[z0,z11,z2,z73,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z6,z113]),(0,[z0,z28,z2,z173,z3,z5,z6]),(0,[z98,z0,z11,z174,z2,z5,z6]),(1,[z0,z175,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z176])],[(0,[z0,z11,z177,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z46,z5,z6]),(0,[z118,z0,z11,z178,z3,z5,z6]),(0,[z106,z98,z0,z11,z2,z5,z6]),(0,[z98,z0,z179,z11,z2,z5,z6])],[(0,[z0,z2,z3,z5,z17,z6,z57]),(0,[z180,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z181,z6]),(0,[z148,z0,z11,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z17,z10,z6]),(0,[z182,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z35,z5,z15,z6]),(1,[z183,z0,z11,z2,z5,z6])]],
   [[(0,[z0,z11,z2,z184,z3,z5,z6]),(0,[z9,z0,z30,z2,z3,z5,z6]),(1,[z0,z185,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z186,z6])],[(0,[z0,z11,z187,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z55,z6]),(1,[z9,z0,z8,z3,z5,z6])],[(0,[z0,z11,z2,z22,z3,z5,z6]),(1,[z0,z2,z3,z5,z188,z6]),(0,[z148,z0,z11,z2,z5,z15,z6])],[(0,[z51,z0,z11,z72,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z157,z6])],[(0,[z189,z0,z2,z3,z5,z6,z113]),(0,[z0,z11,z2,z3,z5,z190,z6]),(1,[z0,z11,z2,z5,z75,z6])],[(0,[z0,z11,z2,z82,z3,z5,z6]),(0,[z98,z0,z11,z2,z33,z5,z6]),(0,[z0,z11,z191,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z192,z164])],[(0,[z0,z8,z2,z3,z5,z18,z6])],[(0,[z0,z11,z193,z2,z3,z5,z6]),(0,[z0,z11,z2,z22,z5,z15,z6]),(1,[z0,z11,z2,z79,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z194]),(0,[z195,z0,z8,z2,z3,z5,z6]),(1,[z98,z0,z1,z2,z5,z6])],[(0,[z0,z11,z2,z3,z196,z5,z6]),(0,[z197,z0,z11,z2,z3,z5,z6]),(0,[z98,z0,z11,z19,z2,z5,z6]),(0,[z141,z98,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z198,z3,z5,z6]),(0,[z0,z11,z2,z199,z3,z5,z6])],[(0,[z95,z98,z0,z11,z2,z5,z6])],[(0,[z14,z7,z11,z2,z3,z5,z6]),(0,[z98,z0,z147,z11,z2,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z113])],[],[(0,[z0,z11,z2,z200,z3,z5,z6]),(0,[z0,z2,z3,z96,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z6,z201]),(0,[z202,z0,z11,z2,z3,z5,z6])],[(0,[z9,z0,z125,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z203]),(0,[z0,z19,z2,z3,z5,z17,z6]),(0,[z0,z11,z204,z2,z3,z5,z6]),(0,[z0,z2,z205,z3,z142,z5,z6])],[(0,[z51,z0,z1,z2,z3,z5,z6]),(0,[z0,z206,z11,z2,z3,z5,z6]),(0,[z0,z8,z178,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z207,z6])]],
   [[(0,[z208,z0,z11,z2,z3,z5,z6]),(0,[z50,z0,z11,z2,z209,z5,z6]),(0,[z60,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z210]),(0,[z0,z11,z30,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z55,z6]),(0,[z156,z9,z0,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z211,z5,z6]),(0,[z212,z0,z11,z2,z3,z5,z6])],[(0,[z0,z1,z2,z22,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z213,z6])],[(0,[z0,z11,z2,z214,z3,z5,z6]),(0,[z9,z0,z2,z3,z96,z5,z6]),(0,[z0,z11,z2,z215,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z157,z6]),(0,[z0,z123,z11,z2,z3,z5,z113]),(0,[z0,z11,z216,z2,z3,z5,z6]),(1,[z0,z11,z2,z107,z5,z6]),(1,[z11,z2,z3,z5,z6,z217])],[(0,[z31,z0,z8,z2,z3,z5,z6]),(0,[z0,z218,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z219,z3,z5,z6]),(1,[z220,z0,z11,z2,z5,z6]),(0,[z221,z98,z0,z11,z2,z5,z6])],[(0,[z0,z11,z30,z2,z5,z15,z6]),(1,[z222,z11,z2,z3,z5,z6])],[(0,[z124,z0,z11,z72,z3,z5,z6]),(1,[z0,z11,z2,z219,z5,z6]),(0,[z0,z30,z2,z3,z5,z17,z6]),(0,[z42,z0,z11,z178,z2,z5,z6]),(0,[z223,z98,z0,z11,z2,z5,z6])],[],[(0,[z0,z11,z224,z2,z3,z5,z6]),(0,[z225,z98,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z3,z5,z6,z226]),(0,[z0,z11,z2,z227,z3,z5,z6]),(0,[z9,z98,z0,z11,z2,z5,z6]),(1,[z0,z11,z30,z3,z5,z39])],[(1,[z228,z0,z11,z2,z5,z6]),(0,[z229,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z230])],[],[(0,[z0,z2,z3,z46,z5,z17,z6])],[(0,[z0,z11,z2,z231,z3,z5,z6])],[(0,[z0,z8,z2,z3,z232,z5,z6]),(0,[z0,z2,z3,z5,z233,z20,z6]),(0,[z0,z11,z2,z3,z5,z6,z234])],[(0,[z51,z0,z11,z2,z3,z5,z6]),(0,[z235,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z236])]],
   [[(0,[z65,z0,z11,z237,z3,z5,z6]),(0,[z156,z0,z11,z2,z238,z5,z6]),(0,[z0,z1,z30,z2,z3,z5,z6])],[(0,[z9,z0,z123,z2,z3,z5,z6])],[(0,[z189,z98,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z3,z5,z213,z6]),(1,[z117,z11,z2,z3,z5,z6]),(0,[z98,z98,z0,z11,z2,z5,z6])],[(0,[z239,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z96,z5,z6]),(0,[z0,z11,z2,z3,z5,z240,z6])],[(0,[z65,z0,z11,z87,z3,z5,z6]),(0,[z0,z147,z11,z72,z3,z5,z6]),(0,[z11,z8,z2,z82,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z241,z6]),(0,[z48,z0,z2,z3,z5,z17,z6])],[(0,[z14,z0,z2,z3,z5,z17,z6]),(0,[z0,z2,z3,z5,z6,z242,z92]),(0,[z0,z11,z2,z5,z15,z243,z6])],[(0,[z0,z8,z2,z211,z3,z5,z6]),(0,[z0,z11,z2,z244,z3,z5,z6]),(0,[z0,z11,z2,z5,z245,z15,z6])],[(0,[z0,z11,z2,z3,z246,z5,z6]),(0,[z0,z11,z247,z2,z3,z5,z6]),(0,[z0,z11,z2,z248,z3,z5,z6]),(0,[z0,z11,z178,z2,z5,z157,z6]),(1,[z0,z2,z3,z249,z5,z6]),(0,[z0,z11,z30,z3,z5,z39,z6])],[(0,[z0,z11,z237,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z250,z6]),(0,[z0,z11,z2,z3,z5,z251,z6]),(0,[z25,z0,z2,z3,z5,z17,z6])],[(0,[z252,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z121,z5,z253,z6])],[(0,[z189,z0,z123,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z254]),(0,[z255,z0,z8,z2,z3,z5,z6])],[(0,[z0,z11,z2,z256,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z257])],[(1,[z0,z2,z3,z5,z258,z6])],[(0,[z0,z11,z2,z259,z3,z5,z6]),(0,[z51,z11,z2,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z5,z260,z6]),(0,[z0,z11,z261,z2,z3,z5,z6])],[(0,[z0,z8,z2,z205,z3,z5,z6]),(0,[z262,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z10,z210]),(0,[z0,z8,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z6,z263]),(1,[z0,z2,z3,z5,z6,z192])]],
   [[(0,[z48,z0,z8,z2,z3,z5,z6]),(0,[z95,z0,z11,z2,z33,z5,z6]),(0,[z156,z98,z0,z11,z2,z5,z6]),(1,[z0,z264,z2,z3,z5,z6]),(0,[z0,z11,z2,z158,z3,z5,z6]),(0,[z265,z0,z11,z2,z3,z5,z6])],[(0,[z42,z95,z0,z11,z2,z5,z6])],[(0,[z266,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z267]),(0,[z0,z11,z2,z3,z268,z5,z6]),(0,[z0,z125,z11,z2,z96,z5,z6]),(0,[z0,z1,z2,z3,z5,z213,z6])],[(0,[z0,z8,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z96,z5,z6]),(0,[z0,z11,z2,z5,z6,z269,z92])],[(0,[z65,z0,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z270,z3,z5,z6]),(0,[z0,z11,z2,z271,z3,z5,z6]),(0,[z25,z0,z8,z2,z3,z5,z6]),(0,[z0,z11,z272,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z273]),(0,[z0,z11,z2,z3,z5,z274,z6])],[(0,[z220,z0,z11,z2,z46,z5,z6])],[(0,[z81,z0,z11,z178,z2,z5,z6]),(0,[z118,z0,z11,z2,z173,z5,z6]),(0,[z11,z30,z2,z158,z3,z5,z6])],[(0,[z275,z0,z11,z2,z3,z5,z6]),(0,[z124,z0,z11,z2,z5,z15,z6]),(0,[z276,z0,z2,z3,z5,z17,z6]),(0,[z98,z0,z11,z2,z3,z15,z6])],[(0,[z0,z2,z3,z5,z17,z172,z6]),(0,[z41,z0,z19,z2,z3,z5,z6]),(0,[z277,z0,z11,z2,z3,z5,z6])],[(1,[z98,z0,z2,z5,z17,z6]),(0,[z278,z0,z11,z2,z3,z5,z6]),(0,[z279,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z280,z5,z6]),(0,[z0,z11,z2,z3,z5,z163,z6])],[(0,[z0,z8,z8,z2,z3,z5,z6]),(0,[z0,z1,z2,z256,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z281,z6]),(0,[z0,z11,z2,z282,z3,z5,z6])],[(0,[z0,z1,z2,z283,z3,z5,z6])],[(0,[z50,z0,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z284]),(0,[z0,z11,z2,z3,z5,z285,z6])],[(0,[z9,z50,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z286,z3,z5,z6]),(0,[z0,z11,z287,z2,z3,z5,z6]),(0,[z279,z0,z11,z2,z5,z15,z6]),(0,[z98,z0,z11,z2,z5,z288,z6]),(0,[z0,z289,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z290,z3,z5,z6]),(0,[z14,z0,z11,z2,z3,z5,z291]),(0,[z48,z0,z34,z2,z3,z5,z6])]],
   [[(1,[z0,z11,z237,z3,z5,z6]),(0,[z65,z0,z8,z2,z3,z5,z6]),(0,[z0,z11,z19,z22,z3,z5,z6]),(0,[z31,z0,z11,z2,z3,z5,z57]),(0,[z0,z147,z11,z2,z3,z5,z6]),(0,[z0,z11,z292,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z293,z5,z6]),(0,[z0,z11,z2,z294,z3,z5,z6]),(0,[z0,z11,z2,z3,z168,z5,z210]),(0,[z0,z295,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z296])],[(0,[z156,z0,z11,z2,z3,z17,z6]),(0,[z0,z2,z3,z5,z17,z157,z6])],[(0,[z95,z0,z125,z2,z3,z5,z6])],[(0,[z297,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z22,z3,z5,z20,z6]),(0,[z50,z11,z2,z209,z3,z5,z6]),(0,[z0,z11,z2,z298,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z20,z6]),(0,[z97,z0,z11,z2,z3,z5,z6])],[(1,[z0,z11,z87,z3,z5,z6]),(0,[z299,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z300,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z301,z6]),(0,[z0,z11,z302,z2,z3,z5,z6]),(0,[z0,z11,z2,z303,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z6,z164]),(0,[z304,z98,z0,z11,z2,z5,z6]),(0,[z98,z0,z11,z2,z5,z6,z305])],[(0,[z0,z147,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z3,z5,z61,z6]),(1,[z0,z125,z2,z33,z5,z6])],[(0,[z98,z65,z0,z11,z2,z5,z6]),(0,[z98,z0,z11,z72,z2,z5,z6]),(0,[z95,z0,z2,z3,z5,z213,z6])],[(0,[z0,z11,z2,z3,z306,z5,z6]),(0,[z95,z0,z2,z3,z96,z5,z6])],[(0,[z0,z2,z35,z3,z5,z17,z6]),(0,[z0,z11,z30,z2,z3,z5,z92]),(0,[z42,z98,z0,z11,z2,z5,z6])],[(0,[z0,z2,z3,z5,z17,z6,z113]),(0,[z0,z11,z2,z3,z5,z6,z307]),(0,[z98,z0,z11,z2,z5,z6,z164])],[(0,[z0,z11,z2,z3,z308,z5,z6]),(0,[z0,z1,z11,z2,z3,z17,z6]),(0,[z0,z11,z2,z3,z5,z39,z18])],[(0,[z0,z11,z309,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z310,z6]),(0,[z98,z51,z0,z11,z2,z5,z6]),(0,[z9,z0,z2,z227,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z311,z6]),(0,[z0,z11,z2,z3,z5,z312,z6]),(0,[z313,z0,z11,z2,z3,z5,z6])],[(0,[z51,z11,z2,z3,z5,z10,z6]),(0,[z0,z11,z2,z3,z5,z6,z314])],[(0,[z0,z11,z2,z3,z5,z315,z6])],[(0,[z0,z8,z2,z3,z121,z5,z6]),(0,[z0,z125,z2,z3,z5,z6,z113])]],
   [[(0,[z0,z11,z316,z2,z3,z5,z6]),(1,[z0,z317,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z217])],[(0,[z0,z11,z2,z3,z318,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z57]),(0,[z0,z8,z2,z3,z5,z58,z6])],[(0,[z0,z8,z2,z3,z5,z10,z6]),(0,[z319,z0,z8,z2,z3,z5,z6]),(0,[z320,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z20,z6])],[(1,[z159,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z321,z6]),(0,[z0,z123,z125,z2,z3,z5,z6]),(1,[z0,z2,z3,z5,z17,z6]),(0,[z0,z322,z11,z2,z3,z5,z6])],[(0,[z0,z11,z323,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z324])],[(0,[z98,z0,z11,z325,z2,z5,z6])],[(0,[z0,z11,z2,z326,z3,z5,z6]),(0,[z0,z327,z1,z2,z3,z5,z6]),(0,[z0,z179,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z328,z3,z5,z6])],[(0,[z0,z11,z329,z2,z3,z5,z6]),(0,[z0,z123,z2,z3,z5,z213,z6]),(0,[z330,z0,z11,z2,z3,z5,z6])],[(0,[z0,z123,z2,z3,z96,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z331]),(0,[z0,z11,z2,z3,z332,z5,z6])],[(0,[z137,z0,z11,z2,z3,z5,z6])],[(0,[z51,z11,z2,z3,z5,z55,z6]),(0,[z0,z11,z2,z333,z3,z5,z6]),(0,[z0,z11,z334,z2,z3,z5,z6]),(1,[z8,z2,z82,z3,z5,z6]),(0,[z265,z0,z2,z3,z5,z6,z164])],[],[],[(0,[z118,z0,z1,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z173,z5,z6])],[(0,[z124,z11,z2,z22,z3,z5,z6])]],
   [[(1,[z0,z8,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z213,z6]),(0,[z0,z1,z316,z2,z3,z5,z6]),(0,[z106,z0,z1,z2,z3,z5,z6])],[],[(1,[z0,z11,z2,z335,z5,z6]),(0,[z0,z11,z2,z336,z3,z5,z6])],[(0,[z0,z11,z337,z2,z3,z5,z6]),(0,[z98,z7,z0,z11,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z20,z6]),(0,[z0,z11,z3,z36,z5,z20,z6])],[(0,[z338,z0,z11,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z168,z5,z6]),(0,[z74,z0,z11,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z36,z5,z6]),(1,[z0,z2,z3,z5,z6,z242]),(0,[z339,z0,z11,z2,z3,z5,z6])],[(1,[z0,z8,z2,z5,z15,z6]),(0,[z0,z11,z2,z96,z5,z15,z6]),(0,[z148,z0,z185,z2,z3,z5,z6])],[(0,[z0,z340,z1,z2,z3,z5,z6]),(0,[z118,z341,z11,z2,z3,z5,z6]),(0,[z0,z342,z11,z2,z3,z5,z6])],[(0,[z343,z0,z11,z2,z3,z5,z6]),(0,[z51,z0,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z3,z5,z18,z57]),(0,[z0,z327,z11,z2,z3,z5,z6]),(0,[z0,z11,z3,z5,z20,z6,z92])],[(0,[z81,z98,z0,z11,z2,z5,z6]),(0,[z0,z11,z344,z2,z3,z5,z6]),(0,[z0,z345,z2,z205,z3,z5,z6])],[(0,[z0,z11,z2,z346,z3,z5,z6]),(0,[z0,z11,z2,z347,z3,z5,z6])],[(0,[z348,z0,z11,z2,z3,z5,z6]),(0,[z0,z349,z11,z2,z3,z5,z6])],[(0,[z350,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z351,z6]),(1,[z0,z11,z2,z77,z5,z6])],[(0,[z0,z11,z2,z335,z3,z5,z6]),(0,[z0,z11,z352,z2,z3,z5,z6]),(0,[z11,z2,z209,z3,z4,z5,z6]),(0,[z0,z11,z2,z3,z5,z353,z6]),(0,[z141,z0,z1,z2,z3,z5,z6]),(0,[z0,z264,z11,z2,z3,z5,z6]),(0,[z0,z327,z11,z2,z5,z15,z6])],[(0,[z354,z0,z11,z2,z3,z5,z6]),(0,[z355,z0,z11,z2,z3,z5,z6]),(1,[z0,z2,z3,z5,z233,z6]),(0,[z42,z0,z289,z2,z3,z5,z6])],[(0,[z9,z81,z0,z2,z3,z5,z6]),(1,[z0,z11,z2,z3,z5,z291]),(0,[z356,z0,z11,z2,z3,z5,z6]),(0,[z118,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z357,z2,z3,z5,z6])],[(0,[z0,z11,z2,z283,z3,z5,z6]),(1,[z0,z34,z2,z3,z5,z6]),(0,[z98,z0,z358,z11,z2,z5,z6]),(0,[z0,z126,z174,z2,z3,z5,z6])]],
   [[(0,[z9,z0,z154,z2,z3,z5,z6]),(0,[z0,z359,z11,z2,z3,z5,z6]),(0,[z360,z0,z11,z2,z3,z5,z6]),(0,[z106,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z245,z6])],[(0,[z0,z147,z11,z211,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z361,z6]),(0,[z118,z42,z0,z11,z2,z5,z6])],[(1,[z60,z11,z2,z3,z5,z57])],[(0,[z0,z11,z362,z2,z3,z5,z6])],[(0,[z14,z0,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z46,z5,z15,z6]),(1,[z0,z11,z2,z5,z6,z273]),(0,[z98,z0,z11,z2,z5,z39,z6])],[(0,[z0,z8,z2,z129,z3,z5,z6])],[(0,[z0,z340,z11,z2,z3,z5,z6]),(0,[z68,z0,z11,z2,z5,z6,z113]),(1,[z106,z0,z11,z3,z5,z92]),(1,[z0,z2,z3,z5,z6,z40])],[(0,[z363,z0,z11,z2,z3,z5,z6]),(0,[z364,z0,z11,z2,z3,z5,z6])],[(0,[z221,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z365,z6])],[(0,[z366,z0,z11,z2,z3,z5,z6])],[(0,[z124,z51,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z367,z6])],[(0,[z0,z11,z368,z2,z3,z5,z6]),(0,[z369,z0,z11,z2,z3,z5,z6])],[(0,[z141,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z6,z370]),(1,[z104,z8,z2,z3,z5,z6])],[(0,[z9,z0,z1,z2,z3,z5,z6]),(0,[z48,z0,z371,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z372,z5,z6])],[(0,[z0,z11,z2,z373,z3,z5,z6]),(1,[z124,z11,z22,z3,z5,z6]),(0,[z51,z7,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z15,z6,z92]),(0,[z98,z0,z11,z2,z5,z108,z6])]],
   [[(0,[z0,z11,z154,z2,z3,z5,z6])],[(0,[z0,z11,z72,z3,z5,z20,z6]),(0,[z0,z2,z3,z5,z15,z17,z6]),(1,[z0,z126,z2,z3,z5,z6]),(0,[z374,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z6,z375]),(1,[z98,z0,z11,z2,z15,z6])],[(0,[z0,z11,z376,z2,z3,z5,z6]),(0,[z0,z11,z2,z377,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z61,z6])],[(1,[z0,z90,z2,z3,z5,z6]),(0,[z0,z11,z2,z378,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z6,z92]),(1,[z379,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z3,z5,z6,z380])],[(0,[z0,z11,z2,z381,z3,z5,z6]),(0,[z0,z11,z382,z2,z3,z5,z6]),(0,[z383,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z384]),(0,[z0,z2,z33,z3,z5,z17,z6]),(0,[z98,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z36,z5,z385,z6])],[(0,[z386,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z387])],[(0,[z221,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z388,z2,z3,z5,z6])],[(0,[z223,z0,z11,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z46,z5,z6])],[(0,[z50,z0,z11,z178,z2,z5,z6]),(0,[z7,z11,z2,z3,z121,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z370]),(0,[z0,z11,z2,z389,z3,z5,z6])],[(0,[z9,z0,z11,z2,z3,z5,z6]),(0,[z0,z8,z2,z35,z3,z5,z6]),(0,[z390,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z391]),(0,[z0,z2,z3,z36,z5,z188,z6])],[(0,[z7,z0,z11,z2,z3,z121,z6]),(0,[z0,z11,z392,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z393,z5,z6]),(0,[z0,z11,z394,z2,z3,z5,z6]),(0,[z395,z0,z11,z2,z3,z5,z6]),(0,[z396,z0,z11,z2,z36,z5,z6]),(0,[z0,z11,z2,z3,z397,z5,z6])]],
   [[(0,[z0,z1,z154,z2,z3,z5,z6]),(0,[z398,z9,z0,z2,z3,z5,z6])],[(0,[z60,z98,z0,z11,z2,z5,z6]),(0,[z0,z2,z3,z5,z17,z20,z6]),(1,[z98,z0,z11,z174,z2,z6])],[(0,[z11,z2,z22,z3,z4,z5,z6])],[(0,[z0,z11,z2,z3,z5,z6,z399]),(0,[z0,z125,z11,z2,z33,z5,z6]),(0,[z400,z0,z11,z2,z3,z5,z6]),(0,[z401,z0,z11,z2,z3,z5,z6])],[(1,[z0,z359,z2,z3,z5,z6]),(0,[z156,z0,z1,z2,z3,z5,z6])],[(0,[z0,z8,z2,z22,z3,z5,z6]),(0,[z11,z2,z3,z5,z55,z6,z57]),(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z402,z6]),(0,[z0,z1,z2,z3,z5,z6,z380])],[(0,[z98,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z403,z5,z6]),(0,[z0,z11,z404,z2,z3,z5,z6]),(0,[z0,z11,z2,z405,z3,z5,z6]),(0,[z0,z11,z2,z3,z406,z5,z6]),(0,[z25,z0,z2,z3,z5,z6,z113]),(0,[z407,z0,z11,z2,z3,z5,z6]),(0,[z106,z0,z11,z3,z5,z6,z92]),(0,[z0,z11,z2,z3,z408,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z409])],[(0,[z0,z11,z2,z3,z5,z6,z410]),(0,[z0,z2,z211,z3,z5,z17,z6]),(0,[z0,z8,z2,z82,z3,z5,z6])],[(0,[z0,z11,z2,z3,z411,z5,z6]),(0,[z0,z2,z209,z3,z5,z17,z6]),(1,[z0,z11,z2,z332,z5,z6])],[(0,[z118,z0,z11,z2,z5,z108,z6]),(1,[z48,z0,z11,z3,z20,z6])],[(0,[z412,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z57,z210]),(0,[z413,z0,z1,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z15,z6])],[(0,[z48,z0,z11,z3,z5,z20,z6])],[(0,[z0,z11,z11,z2,z3,z5,z6]),(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z414,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z415])],[(0,[z0,z11,z2,z3,z416,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z113]),(0,[z0,z11,z19,z2,z3,z36,z6])],[(1,[z0,z345,z2,z3,z5,z6]),(0,[z0,z11,z325,z2,z3,z5,z6])]],
   [[(0,[z417,z0,z11,z2,z3,z5,z6])],[(0,[z418,z0,z11,z2,z3,z5,z6]),(1,[z0,z140,z2,z3,z5,z6]),(0,[z11,z2,z3,z121,z5,z10,z6]),(0,[z0,z419,z11,z2,z3,z5,z6]),(0,[z0,z11,z128,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z420,z6])],[(0,[z421,z0,z11,z2,z3,z5,z6]),(1,[z0,z2,z3,z142,z5,z6])],[(0,[z65,z0,z2,z3,z5,z6,z113]),(0,[z0,z11,z2,z209,z3,z5,z6]),(0,[z0,z2,z3,z5,z55,z17,z6]),(0,[z0,z8,z30,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z422,z6]),(0,[z148,z0,z175,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z423,z6]),(0,[z0,z8,z2,z3,z5,z55,z6]),(0,[z0,z11,z2,z3,z5,z424,z6]),(0,[z156,z0,z11,z2,z3,z5,z6])],[(0,[z7,z0,z11,z2,z3,z5,z6]),(0,[z0,z146,z11,z2,z3,z5,z6]),(0,[z425,z98,z0,z11,z2,z5,z6]),(0,[z148,z0,z11,z2,z3,z168,z6])],[(0,[z426,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z427,z5,z6])],[(0,[z0,z11,z2,z3,z428,z5,z6]),(0,[z429,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z430,z6]),(0,[z0,z11,z431,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z243,z6]),(0,[z0,z11,z2,z3,z5,z6,z432]),(0,[z156,z0,z11,z2,z5,z15,z6]),(0,[z48,z0,z11,z2,z3,z36,z6])],[(0,[z95,z0,z11,z2,z5,z108,z6]),(0,[z0,z11,z2,z3,z5,z6,z433])],[(0,[z0,z11,z2,z434,z3,z5,z6]),(0,[z124,z0,z2,z3,z5,z17,z6]),(0,[z435,z0,z11,z2,z3,z5,z6]),(0,[z413,z0,z11,z2,z3,z5,z6]),(1,[z0,z11,z178,z173,z5,z6])],[(0,[z436,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z437,z5,z6]),(0,[z98,z31,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z3,z438,z5,z6]),(0,[z25,z0,z11,z2,z3,z5,z113]),(0,[z0,z11,z2,z3,z5,z385,z6])],[(0,[z0,z1,z11,z2,z3,z5,z6]),(1,[z0,z371,z2,z3,z5,z6])],[(0,[z0,z439,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z121,z5,z17,z6]),(0,[z9,z0,z2,z3,z46,z5,z6])],[(0,[z0,z440,z11,z2,z3,z5,z6]),(0,[z11,z2,z3,z121,z5,z55,z6]),(0,[z0,z441,z11,z2,z3,z5,z6]),(0,[z442,z0,z11,z2,z3,z5,z6]),(0,[z148,z0,z11,z2,z3,z5,z210])]],
   [[(0,[z0,z11,z2,z443,z3,z5,z6]),(0,[z444,z0,z11,z2,z3,z5,z6]),(0,[z445,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z218,z2,z3,z5,z6]),(0,[z95,z0,z1,z2,z3,z5,z6]),(0,[z48,z98,z0,z11,z2,z5,z6]),(0,[z98,z0,z11,z2,z5,z18,z6])],[(0,[z0,z11,z2,z3,z5,z6,z446]),(0,[z11,z2,z22,z3,z5,z10,z6]),(0,[z0,z11,z2,z3,z5,z447,z6]),(0,[z0,z1,z11,z2,z5,z15,z6]),(0,[z0,z264,z2,z3,z36,z5,z6]),(0,[z313,z0,z2,z3,z5,z6,z92]),(0,[z0,z11,z2,z5,z15,z39,z6]),(0,[z0,z358,z11,z2,z3,z5,z6]),(0,[z42,z0,z11,z2,z5,z6,z164])],[(0,[z0,z1,z2,z209,z3,z5,z6]),(0,[z0,z1,z2,z173,z3,z5,z6])],[(0,[z9,z0,z11,z72,z3,z5,z6]),(1,[z0,z11,z122,z3,z5,z6])],[(0,[z14,z0,z140,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z213,z6]),(0,[z448,z0,z11,z2,z3,z5,z6]),(1,[z68,z0,z11,z2,z5,z6]),(0,[z444,z0,z11,z2,z5,z15,z6]),(0,[z98,z0,z11,z2,z35,z5,z6])],[(0,[z0,z11,z2,z3,z449,z5,z6]),(0,[z450,z0,z11,z2,z3,z5,z6]),(0,[z118,z0,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z5,z15,z6,z210])],[(0,[z0,z1,z2,z3,z428,z5,z6]),(0,[z0,z11,z2,z3,z5,z451,z6])],[(0,[z452,z0,z11,z2,z3,z5,z6]),(0,[z106,z0,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z3,z5,z92,z210]),(0,[z304,z0,z11,z2,z3,z5,z6]),(0,[z222,z11,z2,z3,z5,z6,z210])],[(0,[z0,z2,z3,z143,z4,z5,z6]),(0,[z0,z147,z2,z3,z5,z17,z6]),(0,[z148,z0,z2,z3,z5,z17,z6])],[],[(0,[z379,z0,z11,z2,z5,z6,z92]),(0,[z98,z0,z11,z2,z5,z6,z210]),(0,[z0,z11,z2,z3,z453,z5,z6])],[(0,[z189,z0,z154,z2,z3,z5,z6]),(0,[z0,z11,z454,z2,z3,z5,z6])],[(0,[z455,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z108,z6])],[(0,[z456,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z46,z5,z6])],[(0,[z0,z2,z22,z3,z5,z17,z6]),(0,[z0,z2,z3,z96,z5,z6,z113])]],
   [[(0,[z11,z2,z22,z3,z5,z55,z6])],[(0,[z9,z0,z2,z3,z5,z457,z6]),(0,[z95,z0,z11,z2,z3,z5,z6]),(0,[z396,z0,z11,z2,z3,z5,z6])],[(1,[z0,z11,z19,z3,z36,z6])],[(0,[z0,z11,z2,z3,z5,z458,z6]),(0,[z0,z123,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z459,z3,z5,z6]),(0,[z460,z0,z11,z2,z3,z5,z6])],[(0,[z461,z0,z11,z2,z3,z5,z6]),(0,[z141,z0,z11,z2,z5,z15,z6])],[(0,[z65,z153,z11,z2,z3,z5,z6]),(0,[z462,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z463,z6]),(0,[z148,z0,z8,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z464,z5,z6]),(0,[z104,z0,z11,z2,z3,z5,z6]),(0,[z95,z0,z11,z2,z5,z15,z6])],[],[(0,[z0,z11,z154,z2,z5,z15,z6]),(0,[z118,z50,z0,z11,z2,z5,z6]),(0,[z14,z0,z11,z122,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z164])],[(0,[z189,z0,z1,z2,z3,z5,z6]),(0,[z65,z0,z123,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z465,z6]),(0,[z466,z9,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z6,z467])],[(0,[z0,z11,z2,z3,z5,z6,z6]),(0,[z0,z11,z2,z3,z5,z468,z6])],[(0,[z81,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z469,z15,z6])],[(0,[z0,z11,z2,z46,z5,z29,z6]),(0,[z379,z0,z11,z2,z3,z5,z6])],[(0,[z0,z470,z11,z2,z3,z5,z6])],[(0,[z0,z153,z1,z2,z3,z5,z6]),(0,[z220,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z471,z3,z5,z6]),(0,[z472,z0,z11,z2,z3,z5,z6]),(0,[z225,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z473,z6]),(0,[z0,z11,z474,z2,z3,z5,z6])]],
   [[(0,[z0,z11,z2,z3,z5,z475,z6]),(0,[z0,z11,z476,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z477,z6]),(0,[z0,z11,z2,z3,z5,z6,z478]),(1,[z0,z11,z328,z3,z5,z6]),(0,[z148,z0,z11,z2,z77,z5,z6])],[(0,[z0,z11,z2,z3,z479,z5,z6]),(0,[z0,z11,z2,z3,z5,z457,z6]),(0,[z48,z138,z11,z2,z3,z5,z6]),(1,[z445,z11,z2,z3,z5,z6])],[(0,[z7,z11,z2,z3,z5,z6,z57])],[(0,[z0,z480,z11,z2,z3,z5,z6]),(0,[z0,z123,z11,z2,z3,z5,z6]),(0,[z98,z0,z123,z11,z2,z5,z6]),(0,[z0,z11,z2,z3,z5,z481,z6])],[(0,[z0,z11,z2,z3,z5,z253,z6]),(0,[z482,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z10,z18]),(0,[z0,z11,z2,z3,z238,z5,z6]),(1,[z483,z11,z2,z3,z5,z6])],[(0,[z48,z9,z0,z2,z3,z5,z6]),(0,[z9,z0,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z5,z15,z17,z6]),(0,[z0,z11,z484,z2,z3,z5,z6])],[(0,[z9,z0,z2,z209,z3,z5,z6]),(0,[z14,z9,z0,z2,z3,z5,z6]),(0,[z9,z0,z2,z173,z3,z5,z6]),(0,[z0,z11,z485,z2,z3,z5,z6])],[(0,[z0,z486,z11,z2,z3,z5,z6]),(0,[z0,z487,z1,z2,z3,z5,z6])],[(0,[z189,z65,z11,z2,z3,z5,z6]),(0,[z488,z0,z11,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z164])],[(0,[z189,z0,z11,z2,z3,z5,z6]),(0,[z489,z0,z11,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z157,z6]),(0,[z0,z11,z490,z2,z3,z5,z6]),(0,[z0,z11,z173,z3,z5,z157,z6]),(0,[z0,z11,z2,z5,z15,z15,z6]),(0,[z0,z11,z491,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z492,z6]),(0,[z0,z11,z2,z3,z493,z5,z6]),(0,[z98,z0,z11,z2,z5,z17,z6])],[(0,[z51,z0,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z494,z6]),(0,[z0,z11,z2,z3,z5,z495,z6]),(0,[z496,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z497,z3,z5,z6])],[(0,[z81,z0,z11,z2,z3,z5,z6]),(0,[z104,z11,z8,z2,z3,z5,z6]),(0,[z0,z11,z498,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z469,z6])],[(0,[z499,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z500,z5,z6]),(0,[z183,z0,z11,z2,z3,z5,z6])],[(0,[z189,z0,z11,z2,z5,z15,z6]),(0,[z98,z0,z11,z2,z4,z5,z6]),(0,[z0,z371,z11,z2,z3,z5,z6])],[(0,[z0,z153,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z501]),(0,[z0,z11,z2,z3,z5,z6,z502]),(0,[z0,z11,z503,z2,z3,z5,z6]),(0,[z0,z2,z3,z36,z5,z17,z6]),(0,[z98,z0,z11,z504,z2,z5,z6])]],
   [[(0,[z0,z11,z2,z121,z5,z505,z6]),(0,[z0,z2,z3,z5,z10,z6,z502]),(0,[z0,z16,z11,z2,z3,z5,z6])],[(0,[z506,z0,z11,z2,z3,z5,z6]),(1,[z98,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z3,z5,z507,z6]),(0,[z0,z11,z2,z3,z508,z5,z6])],[(0,[z0,z11,z2,z3,z36,z5,z6]),(0,[z0,z11,z2,z3,z5,z509,z6])],[(0,[z0,z153,z11,z2,z5,z15,z6])],[(0,[z0,z11,z2,z3,z5,z6,z510]),(0,[z0,z1,z484,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z511,z6]),(0,[z0,z11,z2,z512,z3,z5,z6]),(0,[z0,z11,z2,z3,z168,z5,z18])],[(0,[z0,z11,z2,z3,z5,z513,z6]),(0,[z0,z11,z2,z3,z5,z514,z6]),(0,[z0,z8,z2,z3,z5,z20,z6]),(0,[z0,z11,z2,z173,z3,z5,z6]),(0,[z0,z11,z515,z2,z3,z5,z6]),(0,[z516,z0,z11,z2,z3,z5,z6])],[(0,[z0,z487,z11,z2,z3,z5,z6])],[(0,[z0,z517,z11,z2,z3,z5,z6])],[(1,[z9,z0,z72,z3,z5,z6]),(0,[z518,z0,z2,z3,z5,z157,z6])],[(0,[z81,z11,z2,z3,z4,z5,z6]),(0,[z519,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z209,z5,z15,z6]),(0,[z520,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z173,z5,z15,z6]),(0,[z106,z0,z11,z2,z3,z5,z92]),(0,[z516,z0,z11,z2,z5,z15,z6])],[(0,[z60,z11,z2,z3,z121,z5,z6]),(0,[z0,z521,z11,z2,z3,z5,z6]),(1,[z95,z0,z2,z96,z5,z6]),(0,[z0,z11,z2,z3,z5,z522,z6]),(1,[z0,z11,z2,z5,z385,z6])],[(0,[z0,z2,z62,z22,z3,z5,z6]),(0,[z523,z0,z11,z2,z3,z5,z6]),(0,[z7,z0,z11,z2,z5,z15,z6])],[(0,[z0,z11,z2,z3,z5,z524,z6]),(0,[z0,z11,z2,z3,z5,z525,z6]),(0,[z526,z9,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z527,z3,z5,z6]),(0,[z0,z392,z19,z2,z3,z5,z6])],[(0,[z42,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z18,z6])]],
   [[(0,[z0,z11,z2,z3,z143,z5,z6]),(0,[z98,z50,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z528,z3,z5,z6])],[(0,[z529,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z153,z2,z3,z5,z6]),(0,[z0,z11,z530,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z6,z531])],[(0,[z0,z11,z2,z3,z532,z5,z6]),(0,[z0,z11,z2,z3,z5,z533,z6])],[(0,[z159,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z6,z92]),(0,[z0,z1,z2,z3,z36,z5,z6]),(1,[z313,z0,z2,z3,z5,z6])],[(0,[z534,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z535,z6])],[(0,[z14,z98,z0,z11,z2,z5,z6]),(0,[z9,z60,z0,z2,z3,z5,z6]),(0,[z60,z0,z1,z2,z3,z5,z6])],[],[(0,[z536,z0,z11,z2,z3,z5,z6])],[(0,[z0,z1,z2,z33,z3,z5,z6]),(0,[z25,z98,z0,z11,z2,z5,z6]),(0,[z0,z11,z504,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z537,z5,z6]),(0,[z31,z0,z1,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z96,z5,z6])],[(0,[z189,z0,z153,z2,z3,z5,z6]),(0,[z124,z0,z8,z2,z3,z5,z6]),(0,[z7,z0,z11,z2,z3,z55,z6]),(0,[z98,z0,z11,z2,z121,z5,z6]),(0,[z98,z0,z11,z2,z5,z5,z6])],[(0,[z9,z0,z2,z3,z5,z6,z164])],[(0,[z0,z538,z11,z2,z3,z5,z6])],[(0,[z98,z0,z11,z2,z5,z6,z57]),(0,[z0,z11,z2,z539,z3,z5,z6])],[(0,[z98,z0,z11,z2,z5,z10,z6]),(0,[z540,z9,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z468,z17,z6]),(0,[z148,z0,z11,z2,z332,z5,z6])],[(0,[z0,z8,z2,z3,z5,z353,z6]),(0,[z0,z11,z2,z541,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z542,z6]),(0,[z42,z0,z11,z2,z3,z5,z6])]],
   [[(0,[z543,z0,z11,z2,z3,z5,z6]),(0,[z544,z0,z11,z2,z3,z5,z6]),(1,[z98,z0,z8,z2,z5,z6]),(0,[z25,z0,z123,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z288,z6])],[(0,[z9,z0,z11,z211,z3,z5,z6]),(0,[z52,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z178,z2,z173,z5,z6]),(1,[z138,z11,z2,z3,z5,z6])],[(0,[z0,z11,z545,z2,z3,z5,z6])],[(0,[z546,z0,z11,z2,z3,z5,z6]),(0,[z98,z0,z125,z11,z2,z5,z6]),(0,[z0,z2,z378,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z39,z6]),(0,[z0,z11,z2,z3,z5,z6,z92])],[(0,[z0,z11,z2,z3,z5,z6,z547]),(0,[z0,z548,z11,z2,z3,z5,z6]),(0,[z42,z0,z11,z2,z5,z15,z6])],[(0,[z60,z0,z11,z2,z3,z5,z6]),(1,[z9,z0,z2,z3,z5,z6]),(0,[z0,z441,z2,z3,z5,z39,z6]),(0,[z0,z11,z2,z5,z285,z15,z6])],[(0,[z189,z11,z2,z22,z3,z5,z6]),(0,[z0,z11,z2,z121,z5,z15,z6]),(0,[z0,z2,z3,z5,z17,z6,z164]),(0,[z0,z11,z2,z3,z5,z6,z305]),(1,[z0,z289,z2,z3,z5,z6])],[(0,[z0,z11,z2,z549,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z188,z6])],[(0,[z0,z11,z2,z3,z5,z550,z6]),(0,[z0,z11,z2,z3,z5,z551,z6]),(0,[z0,z147,z8,z2,z3,z5,z6]),(1,[z0,z316,z2,z3,z5,z6])],[(0,[z31,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z62,z3,z5,z6]),(1,[z9,z0,z2,z5,z15,z6]),(0,[z48,z0,z11,z2,z244,z5,z6])],[(0,[z98,z0,z11,z2,z205,z5,z6]),(0,[z0,z11,z70,z2,z3,z5,z6])],[(0,[z0,z552,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z553]),(0,[z0,z11,z2,z3,z5,z554,z6])],[(0,[z0,z11,z555,z2,z3,z5,z6]),(0,[z0,z125,z11,z2,z5,z108,z6]),(0,[z0,z11,z2,z3,z5,z6,z556])],[(0,[z0,z11,z2,z557,z3,z5,z6]),(0,[z558,z0,z11,z2,z3,z5,z6]),(0,[z48,z0,z11,z19,z3,z5,z6])],[(0,[z9,z0,z2,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z168,z5,z6])]],
   [[(0,[z14,z0,z11,z377,z3,z5,z6]),(0,[z222,z0,z11,z2,z3,z5,z6])],[(0,[z0,z483,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z168,z5,z258,z6])],[],[(0,[z0,z11,z2,z3,z559,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z92]),(1,[z0,z11,z560,z3,z5,z6]),(0,[z183,z0,z11,z2,z168,z5,z6])],[(0,[z0,z125,z1,z2,z3,z5,z6]),(1,[z0,z11,z2,z238,z5,z6])],[(0,[z124,z0,z11,z22,z3,z5,z6]),(0,[z7,z11,z2,z22,z3,z5,z6])],[(0,[z228,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z36,z5,z6]),(0,[z9,z95,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z561,z3,z5,z6])],[(0,[z0,z72,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z562,z6])],[(0,[z0,z11,z2,z3,z5,z6,z563])],[(0,[z0,z11,z2,z564,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z495,z6]),(0,[z0,z11,z2,z3,z565,z5,z6])],[],[(0,[z51,z0,z359,z2,z3,z5,z6]),(0,[z9,z0,z2,z33,z3,z5,z6]),(0,[z320,z0,z8,z2,z3,z5,z6]),(0,[z156,z0,z11,z2,z3,z46,z6]),(0,[z0,z123,z11,z2,z5,z15,z6])],[(0,[z0,z11,z560,z2,z3,z5,z6])],[(0,[z0,z11,z566,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z567,z6]),(0,[z0,z11,z2,z3,z5,z568,z6]),(0,[z569,z0,z11,z2,z3,z5,z6]),(0,[z42,z0,z11,z2,z35,z5,z6])],[(0,[z0,z11,z2,z2,z3,z5,z6]),(1,[z50,z11,z2,z209,z5,z6])]],
   [[(0,[z74,z0,z2,z3,z5,z17,z6]),(1,[z0,z295,z2,z3,z5,z6])],[(0,[z189,z51,z11,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z22,z5,z6]),(0,[z0,z11,z2,z570,z3,z5,z6]),(0,[z0,z11,z2,z571,z3,z5,z6]),(0,[z0,z11,z19,z3,z36,z5,z6])],[(0,[z0,z572,z11,z2,z3,z5,z6]),(0,[z50,z0,z1,z2,z3,z5,z6]),(0,[z156,z0,z11,z2,z219,z5,z6])],[(0,[z398,z0,z11,z2,z3,z5,z6]),(0,[z0,z147,z11,z22,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z573,z6]),(0,[z0,z11,z2,z3,z574,z5,z6])],[(0,[z189,z0,z2,z33,z3,z5,z6]),(0,[z81,z0,z11,z2,z4,z5,z6]),(0,[z81,z0,z11,z2,z5,z15,z6]),(0,[z0,z125,z11,z2,z3,z5,z6]),(0,[z0,z1,z11,z2,z3,z46,z6]),(0,[z0,z11,z2,z5,z15,z575,z6]),(0,[z576,z0,z11,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z17,z6]),(0,[z0,z11,z2,z3,z5,z6,z577])],[(0,[z9,z0,z2,z3,z5,z39,z6]),(0,[z42,z0,z11,z2,z3,z5,z108])],[],[(0,[z41,z9,z0,z2,z3,z5,z6]),(1,[z396,z0,z11,z2,z5,z6])],[(0,[z0,z125,z11,z2,z5,z15,z6]),(0,[z42,z0,z125,z11,z2,z5,z6])],[(0,[z51,z0,z8,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z6,z210]),(0,[z118,z0,z2,z3,z5,z17,z6]),(0,[z0,z1,z19,z2,z3,z5,z6]),(0,[z48,z0,z11,z2,z3,z5,z391]),(0,[z42,z0,z70,z2,z3,z5,z6])],[(0,[z0,z11,z2,z33,z3,z5,z6])],[(0,[z106,z0,z2,z3,z5,z17,z6]),(0,[z0,z11,z174,z2,z3,z5,z6]),(0,[z0,z174,z317,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z578,z5,z6]),(0,[z0,z11,z579,z2,z3,z5,z6]),(0,[z9,z98,z0,z2,z3,z5,z6]),(0,[z0,z392,z2,z3,z5,z17,z6]),(0,[z580,z0,z11,z2,z3,z5,z6])],[],[(1,[z581,z11,z2,z3,z5,z6]),(0,[z0,z11,z30,z2,z3,z5,z39]),(1,[z0,z441,z2,z3,z5,z6]),(0,[z582,z0,z11,z2,z3,z5,z6])]],
   [[(0,[z0,z11,z2,z33,z5,z15,z6]),(0,[z0,z174,z2,z3,z5,z17,z6])],[(0,[z98,z0,z11,z2,z209,z5,z6]),(0,[z14,z0,z11,z2,z3,z5,z399]),(0,[z0,z11,z2,z3,z583,z5,z6]),(0,[z9,z0,z2,z3,z5,z108,z6]),(0,[z0,z2,z3,z5,z17,z39,z6]),(0,[z584,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z258,z6]),(0,[z0,z295,z2,z3,z168,z5,z6])],[(1,[z297,z0,z2,z3,z5,z6]),(0,[z50,z0,z11,z2,z3,z5,z6]),(0,[z60,z11,z2,z3,z5,z6,z57]),(0,[z0,z11,z2,z3,z5,z585,z6]),(0,[z0,z586,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z587,z3,z5,z6]),(1,[z0,z517,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z588,z5,z6]),(0,[z582,z0,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z3,z5,z6,z192])],[(0,[z0,z11,z2,z3,z5,z6,z589])],[(0,[z0,z11,z72,z19,z3,z5,z6]),(0,[z0,z11,z590,z2,z3,z5,z6]),(1,[z591,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z39,z6]),(0,[z148,z445,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z505,z6]),(0,[z31,z11,z2,z3,z5,z10,z6]),(0,[z0,z11,z2,z3,z5,z6,z592]),(0,[z0,z11,z2,z36,z5,z15,z6])],[(0,[z88,z9,z0,z2,z3,z5,z6]),(0,[z141,z0,z2,z3,z5,z17,z6])],[(0,[z593,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z594,z3,z5,z6]),(0,[z0,z392,z8,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z5,z17,z6]),(0,[z0,z2,z3,z168,z5,z17,z6]),(0,[z148,z483,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z335,z22,z5,z6]),(1,[z0,z11,z2,z244,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z210])],[(0,[z0,z11,z2,z3,z5,z595,z6]),(0,[z118,z81,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z5,z15,z6,z57]),(0,[z118,z117,z11,z2,z3,z5,z6]),(0,[z0,z11,z590,z2,z5,z15,z6])],[(0,[z0,z11,z2,z5,z15,z10,z6]),(0,[z0,z147,z11,z8,z3,z5,z6]),(0,[z0,z174,z8,z2,z3,z5,z6]),(0,[z0,z1,z174,z2,z3,z5,z6]),(0,[z596,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z597,z6]),(0,[z0,z11,z2,z205,z3,z15,z6])],[(0,[z9,z0,z72,z2,z3,z5,z6]),(0,[z0,z123,z11,z2,z3,z5,z213]),(0,[z598,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z599,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z600]),(0,[z0,z11,z2,z3,z5,z105,z6])],[(1,[z81,z11,z2,z4,z5,z6]),(1,[z0,z11,z377,z3,z5,z6]),(0,[z195,z0,z11,z2,z3,z5,z6]),(0,[z42,z0,z11,z2,z3,z5,z164])]],
   [[(0,[z601,z0,z11,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z18,z6])],[(0,[z602,z0,z11,z2,z3,z5,z6]),(0,[z603,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z6,z92]),(0,[z0,z11,z2,z3,z604,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z605]),(0,[z0,z11,z19,z3,z5,z6,z92]),(0,[z0,z11,z2,z3,z5,z108,z6])],[(0,[z0,z11,z2,z3,z5,z6,z606]),(0,[z0,z11,z2,z3,z5,z6,z109]),(0,[z169,z98,z0,z11,z2,z5,z6])],[(0,[z0,z11,z178,z173,z3,z5,z6]),(0,[z0,z11,z175,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z607,z5,z6]),(0,[z0,z11,z30,z3,z5,z20,z6])],[(0,[z51,z0,z11,z22,z3,z5,z6]),(0,[z0,z11,z2,z3,z168,z18,z6])],[(1,[z41,z0,z2,z3,z5,z6]),(1,[z0,z392,z2,z3,z5,z6]),(0,[z223,z0,z2,z3,z5,z17,z6]),(0,[z148,z98,z0,z11,z2,z5,z6])],[(0,[z608,z0,z11,z2,z3,z5,z6]),(0,[z14,z0,z517,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z609,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z610]),(0,[z0,z11,z2,z3,z611,z5,z6]),(0,[z0,z11,z2,z3,z5,z612,z6])],[(0,[z319,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z232,z5,z6]),(0,[z613,z0,z11,z2,z3,z5,z6])],[(0,[z9,z0,z2,z3,z5,z17,z6]),(0,[z0,z1,z178,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z6,z113]),(1,[z265,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z614]),(0,[z0,z11,z2,z615,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z210]),(0,[z616,z0,z11,z2,z3,z5,z6])],[],[(0,[z95,z189,z0,z2,z3,z5,z6]),(0,[z11,z72,z2,z22,z3,z5,z6]),(0,[z11,z2,z3,z5,z10,z6,z57])],[(0,[z0,z11,z72,z2,z3,z5,z6]),(0,[z60,z51,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z617,z5,z6]),(0,[z60,z0,z11,z2,z5,z15,z6]),(0,[z9,z0,z19,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z15,z6]),(0,[z0,z11,z2,z5,z6,z273,z113]),(1,[z341,z11,z2,z3,z5,z6]),(0,[z0,z185,z11,z2,z3,z5,z6])],[(0,[z51,z0,z90,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z618]),(0,[z581,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z5,z15,z6])],[(0,[z14,z60,z11,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z55,z6]),(0,[z0,z2,z33,z3,z5,z213,z6]),(0,[z400,z0,z2,z3,z5,z17,z6]),(0,[z48,z47,z11,z2,z3,z5,z6])]],
   [[(0,[z0,z11,z2,z619,z3,z5,z6]),(0,[z0,z154,z2,z3,z5,z17,z6]),(0,[z0,z2,z33,z3,z96,z5,z6]),(0,[z620,z0,z11,z2,z3,z5,z6])],[(0,[z9,z65,z0,z2,z3,z5,z6]),(0,[z31,z0,z11,z2,z5,z15,z6]),(0,[z0,z8,z2,z3,z46,z5,z6]),(0,[z0,z1,z2,z3,z5,z108,z6]),(0,[z0,z2,z3,z5,z213,z6,z113]),(0,[z98,z330,z0,z11,z2,z5,z6])],[(0,[z0,z11,z72,z2,z5,z15,z6]),(0,[z98,z0,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z621,z6]),(0,[z0,z11,z2,z3,z5,z622,z6])],[(0,[z136,z9,z0,z2,z3,z5,z6]),(1,[z0,z123,z2,z3,z5,z213])],[(0,[z0,z623,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z511,z157,z6]),(0,[z0,z11,z174,z2,z205,z3,z6]),(0,[z148,z0,z11,z2,z3,z5,z18]),(1,[z0,z11,z2,z3,z168,z18])],[(0,[z0,z624,z11,z2,z3,z5,z6]),(0,[z0,z625,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z626,z3,z5,z6]),(0,[z591,z0,z2,z3,z5,z20,z6])],[(0,[z0,z11,z2,z3,z609,z5,z6])],[(0,[z0,z11,z2,z3,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z627,z6]),(0,[z95,z25,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z628,z6]),(0,[z48,z0,z1,z2,z3,z5,z6])],[(0,[z14,z0,z1,z2,z3,z5,z6]),(0,[z9,z0,z147,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z629,z3,z5,z6])],[(0,[z0,z11,z2,z3,z630,z5,z6]),(1,[z0,z11,z2,z3,z5,z391])],[(0,[z9,z189,z0,z2,z3,z5,z6]),(0,[z65,z0,z154,z2,z3,z5,z6])],[(0,[z0,z154,z8,z2,z3,z5,z6]),(0,[z124,z9,z0,z2,z3,z5,z6]),(0,[z425,z0,z11,z2,z3,z5,z6]),(0,[z466,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z567,z6]),(0,[z25,z0,z1,z2,z3,z5,z6]),(0,[z118,z0,z11,z2,z5,z157,z6]),(0,[z0,z11,z2,z3,z5,z6,z631])],[(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z150,z9,z0,z2,z3,z5,z6]),(0,[z632,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z19,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z15,z6])],[(0,[z0,z503,z8,z2,z3,z5,z6]),(0,[z98,z0,z8,z2,z3,z5,z6]),(0,[z98,z0,z11,z8,z2,z5,z6]),(0,[z0,z11,z2,z3,z633,z5,z6])],[(0,[z9,z0,z174,z2,z3,z5,z6]),(0,[z0,z11,z634,z2,z3,z5,z6])]],
   [[(1,[z0,z11,z2,z3,z5,z399]),(0,[z0,z1,z2,z211,z3,z5,z6]),(1,[z0,z147,z8,z3,z5,z6]),(0,[z635,z0,z11,z2,z3,z5,z6]),(0,[z156,z0,z2,z3,z5,z17,z6])],[(0,[z636,z0,z11,z2,z3,z5,z6]),(0,[z7,z0,z2,z3,z5,z17,z6])],[(0,[z255,z0,z11,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z621,z6]),(0,[z0,z11,z19,z2,z5,z15,z6])],[(0,[z9,z0,z2,z3,z5,z18,z6])],[(0,[z0,z11,z637,z2,z3,z5,z6]),(0,[z0,z11,z2,z638,z3,z5,z6]),(0,[z639,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z640,z5,z6])],[(0,[z297,z0,z2,z22,z3,z5,z6]),(0,[z0,z11,z178,z2,z5,z108,z6])],[(0,[z0,z11,z641,z2,z3,z5,z6])],[(0,[z0,z11,z642,z2,z3,z5,z6]),(0,[z9,z25,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z643,z3,z5,z6])],[(0,[z65,z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z644,z3,z5,z6]),(0,[z48,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z645])],[(0,[z14,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z121,z5,z6]),(0,[z0,z1,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z6,z646]),(0,[z0,z11,z2,z3,z5,z6,z242])],[(0,[z148,z9,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z647]),(0,[z0,z345,z11,z2,z3,z5,z6])],[(0,[z648,z0,z11,z2,z3,z5,z6]),(0,[z98,z0,z11,z174,z2,z3,z6])],[(0,[z51,z153,z11,z2,z3,z5,z6]),(0,[z9,z0,z178,z2,z3,z5,z6]),(0,[z156,z0,z8,z2,z3,z5,z6]),(0,[z25,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z649,z6]),(0,[z0,z1,z2,z3,z5,z15,z6]),(0,[z48,z0,z11,z2,z5,z15,z6])],[(0,[z0,z11,z2,z3,z5,z6,z269])],[(0,[z0,z125,z2,z33,z3,z5,z6]),(1,[z25,z0,z2,z3,z5,z113]),(0,[z0,z11,z2,z3,z249,z5,z6])]],
   [[(0,[z650,z0,z1,z2,z3,z5,z6]),(0,[z648,z0,z11,z2,z5,z15,z6])],[(0,[z651,z0,z11,z2,z3,z5,z6]),(1,[z104,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z652,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z6,z653]),(0,[z0,z11,z2,z3,z5,z6,z654]),(0,[z655,z0,z11,z2,z3,z5,z6]),(0,[z98,z0,z1,z11,z2,z5,z6]),(0,[z0,z11,z2,z3,z5,z233,z6])],[(0,[z656,z0,z11,z2,z3,z5,z6]),(0,[z657,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z18,z6])],[(0,[z153,z11,z2,z22,z3,z5,z6]),(0,[z0,z11,z2,z658,z3,z5,z6]),(0,[z659,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z174,z2,z5,z15,z6])],[(0,[z60,z11,z2,z22,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z6,z592]),(0,[z0,z11,z2,z3,z5,z6,z531])],[(0,[z0,z2,z3,z5,z83,z17,z6]),(1,[z148,z0,z11,z2,z3,z210])],[(0,[z81,z0,z11,z2,z209,z5,z6]),(0,[z0,z11,z660,z2,z3,z5,z6]),(1,[z0,z11,z2,z5,z505,z6]),(0,[z0,z485,z2,z3,z5,z17,z6])],[(0,[z65,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z661,z6]),(0,[z0,z2,z3,z5,z17,z6,z210]),(0,[z0,z2,z173,z3,z249,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z662]),(0,[z148,z0,z11,z328,z3,z5,z6]),(0,[z148,z0,z11,z560,z3,z5,z6])],[(0,[z0,z8,z2,z209,z3,z5,z6]),(0,[z0,z11,z2,z3,z121,z5,z6]),(1,[z9,z0,z211,z3,z5,z6]),(0,[z118,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z173,z3,z5,z6])],[(0,[z663,z0,z11,z2,z3,z5,z6]),(0,[z50,z0,z11,z2,z5,z15,z6])],[(0,[z276,z0,z11,z2,z3,z5,z6]),(0,[z124,z98,z0,z11,z2,z5,z6]),(0,[z0,z11,z664,z2,z3,z5,z6]),(0,[z106,z0,z8,z2,z3,z5,z6]),(0,[z148,z0,z11,z2,z3,z6,z210])],[(0,[z0,z11,z178,z2,z3,z5,z6])],[(0,[z65,z0,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z3,z5,z6,z665]),(0,[z95,z0,z2,z3,z5,z17,z6]),(0,[z0,z2,z205,z3,z5,z17,z6])],[(0,[z9,z520,z0,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z168,z5,z6]),(0,[z666,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z667,z5,z6]),(0,[z0,z2,z3,z5,z17,z108,z6]),(0,[z0,z11,z2,z5,z15,z157,z6])]],
   [[(0,[z650,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z668,z6]),(0,[z0,z146,z2,z3,z121,z5,z6]),(1,[z9,z98,z0,z2,z5,z6]),(0,[z526,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z178,z2,z5,z15,z6]),(0,[z98,z0,z11,z30,z2,z5,z6])],[(0,[z0,z11,z2,z3,z18,z6,z210])],[(0,[z0,z11,z2,z3,z5,z669,z6]),(0,[z9,z0,z2,z211,z3,z5,z6]),(0,[z518,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z542,z6]),(0,[z0,z670,z11,z2,z3,z5,z6])],[(1,[z189,z154,z2,z3,z5,z6]),(0,[z189,z11,z154,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z157,z6])],[(0,[z95,z65,z0,z2,z3,z5,z6]),(1,[z44,z0,z11,z2,z5,z6]),(0,[z9,z0,z2,z3,z5,z671,z6])],[(0,[z98,z0,z11,z154,z2,z5,z6]),(0,[z11,z2,z3,z5,z6,z217,z210])],[(0,[z141,z0,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z6,z113]),(0,[z0,z11,z2,z3,z5,z6,z672]),(0,[z0,z11,z2,z673,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z674,z6])],[(0,[z31,z11,z2,z3,z5,z55,z6]),(1,[z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z121,z5,z6]),(1,[z0,z2,z3,z5,z457,z6]),(0,[z95,z0,z8,z2,z3,z5,z6]),(0,[z581,z11,z30,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z675,z6]),(0,[z0,z341,z11,z2,z3,z5,z6])],[(0,[z9,z0,z2,z205,z3,z5,z6])],[(1,[z0,z2,z3,z5,z253,z6]),(0,[z676,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z15,z55,z6]),(0,[z0,z1,z2,z3,z5,z10,z6]),(1,[z0,z1,z2,z5,z15,z6]),(0,[z98,z0,z11,z2,z629,z5,z6])],[(0,[z0,z11,z2,z3,z168,z5,z6])],[(0,[z677,z0,z11,z2,z3,z5,z6]),(0,[z0,z123,z2,z3,z5,z17,z6])]],
   [[(0,[z0,z11,z678,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z6])],[(0,[z540,z0,z11,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z20,z6]),(0,[z0,z11,z2,z168,z5,z15,z6]),(0,[z0,z11,z2,z5,z108,z6,z164])],[(0,[z0,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z17,z6]),(0,[z0,z679,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z680,z6])],[(0,[z0,z11,z2,z211,z3,z5,z6]),(0,[z25,z0,z11,z2,z3,z5,z213])],[(0,[z0,z11,z681,z2,z3,z5,z6]),(0,[z682,z0,z11,z2,z3,z5,z6])],[(0,[z189,z0,z2,z3,z5,z17,z6]),(0,[z14,z0,z11,z2,z3,z121,z6]),(0,[z0,z11,z2,z3,z5,z671,z6]),(0,[z118,z0,z11,z3,z5,z157,z6])],[(1,[z14,z11,z2,z3,z55,z6]),(0,[z683,z0,z1,z2,z3,z5,z6])],[(0,[z14,z11,z2,z3,z5,z10,z6]),(1,[z0,z2,z3,z5,z6,z502]),(0,[z0,z2,z3,z5,z17,z17,z6])],[(1,[z0,z11,z2,z3,z5,z6]),(0,[z81,z0,z2,z3,z5,z17,z6]),(0,[z9,z0,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z211,z5,z15,z6]),(0,[z0,z11,z317,z2,z3,z5,z6]),(1,[z42,z0,z11,z2,z5,z164])],[(0,[z65,z0,z153,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z6,z684])],[(0,[z9,z51,z0,z2,z3,z5,z6])],[(0,[z0,z153,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z685,z5,z6]),(0,[z0,z11,z2,z205,z3,z5,z6])],[(0,[z686,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z687,z2,z3,z5,z6])],[(1,[z0,z2,z3,z5,z511,z6]),(1,[z0,z11,z2,z5,z15,z6])],[(0,[z0,z8,z2,z3,z5,z6,z164]),(0,[z0,z1,z2,z3,z168,z5,z6]),(0,[z0,z11,z2,z5,z15,z213,z6]),(1,[z118,z0,z11,z5,z157,z6])],[(0,[z0,z11,z2,z3,z5,z6,z688])]],
   [[(0,[z0,z11,z2,z3,z4,z5,z6]),(0,[z591,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z205,z5,z15,z6])],[(0,[z189,z0,z8,z2,z3,z5,z6]),(0,[z228,z0,z11,z2,z22,z5,z6]),(0,[z689,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z447,z17,z6])],[(0,[z50,z11,z2,z22,z3,z5,z6]),(0,[z690,z0,z11,z2,z3,z5,z6])],[(0,[z98,z0,z153,z11,z2,z5,z6]),(0,[z98,z0,z11,z2,z5,z213,z6]),(0,[z0,z11,z691,z2,z3,z5,z6])],[(0,[z9,z42,z0,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z96,z5,z6]),(0,[z0,z178,z2,z3,z5,z17,z6]),(0,[z0,z11,z692,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z693,z6]),(0,[z694,z0,z11,z2,z3,z5,z6]),(0,[z0,z2,z173,z3,z5,z17,z6]),(0,[z0,z11,z2,z3,z5,z39,z210]),(0,[z0,z11,z2,z695,z3,z5,z6])],[(0,[z683,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z696,z5,z6])],[(0,[z0,z153,z8,z2,z3,z5,z6])],[(0,[z0,z11,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z575,z6]),(0,[z697,z0,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z291,z6])],[(0,[z698,z0,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z699,z3,z5,z6])],[(0,[z700,z0,z11,z2,z3,z5,z6]),(0,[z31,z7,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z701,z3,z5,z6]),(0,[z9,z0,z419,z2,z3,z5,z6]),(0,[z41,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z205,z3,z5,z6]),(0,[z0,z11,z702,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z703,z5,z6]),(0,[z0,z11,z2,z3,z5,z18,z92])],[],[(0,[z60,z31,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z704,z3,z5,z6]),(0,[z0,z11,z8,z2,z5,z15,z6]),(1,[z518,z0,z2,z3,z5,z6]),(0,[z98,z0,z11,z178,z2,z5,z6])],[(1,[z0,z11,z2,z5,z6,z269]),(1,[z0,z11,z2,z205,z15,z6])],[(0,[z705,z0,z11,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z6,z57]),(0,[z0,z11,z2,z3,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z11,z707,z3,z5,z6]),(0,[z0,z90,z2,z5,z15,z6]),(0,[z0,z11,z2,z708,z5,z6]),(0,[z0,z2,z3,z5,z6,z709]),(0,[z48,z0,z11,z15,z20,z6])],[(0,[z9,z0,z2,z3,z5,z399]),(0,[z710,z11,z2,z3,z5,z6]),(0,[z148,z0,z11,z2,z3,z711])],[(0,[z50,z2,z209,z5,z17,z6]),(0,[z712,z11,z2,z3,z5,z6])],[(0,[z0,z2,z62,z335,z5,z6]),(0,[z51,z8,z72,z3,z5,z6]),(0,[z0,z8,z2,z73,z5,z6]),(0,[z0,z2,z5,z75,z17,z6]),(0,[z0,z2,z142,z5,z15,z6]),(0,[z11,z2,z713,z3,z5,z6])],[(0,[z189,z90,z2,z3,z5,z6]),(0,[z81,z358,z11,z2,z5,z6]),(0,[z9,z44,z0,z2,z5,z6]),(0,[z0,z2,z3,z430,z17,z6]),(0,[z0,z11,z2,z714,z5,z6])],[(0,[z0,z715,z2,z3,z5,z6]),(0,[z398,z9,z22,z3,z5,z6]),(0,[z445,z11,z2,z3,z5,z6]),(0,[z222,z2,z3,z5,z17,z6]),(0,[z0,z11,z716,z3,z5,z6]),(0,[z0,z11,z3,z5,z20,z391])],[(0,[z0,z11,z2,z3,z5,z717]),(0,[z98,z0,z2,z62,z5,z6])],[(0,[z0,z11,z2,z15,z551,z6]),(0,[z718,z11,z2,z3,z5,z6])],[(0,[z719,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z693,z15,z6]),(0,[z0,z720,z2,z3,z5,z6]),(0,[z98,z0,z11,z174,z2,z6])],[(0,[z124,z228,z11,z22,z5,z6]),(0,[z721,z0,z2,z3,z5,z6]),(0,[z722,z11,z2,z3,z5,z6])],[(0,[z9,z98,z0,z72,z5,z6]),(0,[z0,z11,z2,z723,z5,z6]),(0,[z68,z0,z2,z5,z213,z6])],[(0,[z68,z0,z2,z96,z5,z6]),(0,[z106,z74,z0,z3,z5,z6]),(0,[z0,z724,z2,z3,z5,z6]),(0,[z725,z0,z2,z3,z5,z6]),(0,[z726,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z465,z6]),(0,[z0,z727,z2,z3,z5,z6]),(0,[z9,z0,z2,z457,z15,z6]),(0,[z466,z0,z2,z3,z5,z671])],[(0,[z0,z11,z2,z5,z6,z728]),(0,[z0,z729,z377,z3,z5,z6]),(0,[z104,z2,z82,z3,z5,z6]),(0,[z0,z11,z2,z5,z730,z6])],[(0,[z0,z731,z2,z3,z5,z6]),(0,[z0,z517,z377,z3,z5,z6]),(0,[z732,z0,z11,z2,z3,z5]),(0,[z0,z11,z2,z733,z5,z6])],[(0,[z0,z2,z3,z5,z6,z734]),(0,[z0,z11,z2,z735,z5,z6]),(0,[z98,z0,z441,z2,z5,z6])]],
   [[(0,[z0,z359,z2,z5,z15,z6]),(0,[z0,z11,z2,z5,z736,z6]),(0,[z0,z2,z5,z505,z253,z6]),(0,[z0,z2,z3,z737,z5,z6]),(0,[z0,z1,z2,z5,z385,z6]),(0,[z47,z34,z2,z3,z5,z6])],[(0,[z0,z11,z738,z3,z5,z6]),(0,[z0,z11,z2,z79,z5,z291]),(0,[z0,z739,z2,z3,z5,z6]),(0,[z44,z0,z2,z5,z17,z6]),(0,[z0,z11,z740,z3,z5,z6]),(0,[z48,z0,z11,z3,z20,z6])],[(0,[z0,z2,z3,z5,z741,z6]),(0,[z117,z2,z3,z5,z17,z6]),(0,[z0,z1,z178,z173,z5,z6]),(0,[z0,z11,z3,z5,z6,z742])],[(0,[z0,z11,z2,z743,z5,z6]),(0,[z0,z2,z3,z5,z744,z6]),(0,[z0,z2,z3,z5,z745,z6]),(0,[z104,z2,z3,z5,z6,z113]),(0,[z746,z0,z328,z3,z5,z6]),(0,[z0,z2,z3,z5,z747,z6])],[(0,[z0,z748,z211,z3,z5,z6]),(0,[z0,z125,z2,z5,z469,z6])],[(0,[z0,z2,z3,z5,z749,z6])],[(0,[z14,z140,z2,z3,z55,z6]),(0,[z11,z750,z2,z3,z5,z6]),(0,[z48,z0,z11,z3,z20,z391])],[(0,[z751,z0,z2,z3,z5,z6])],[(0,[z752,z0,z2,z3,z5,z6]),(0,[z9,z0,z2,z5,z505,z6]),(0,[z753,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z163,z108])],[(0,[z0,z11,z2,z3,z754,z6]),(0,[z0,z2,z3,z142,z5,z6]),(0,[z0,z2,z755,z3,z5,z6])],[(0,[z0,z11,z2,z5,z756,z6]),(0,[z9,z68,z0,z2,z5,z6]),(0,[z138,z11,z2,z244,z5,z6]),(0,[z98,z0,z11,z2,z5,z391])],[(0,[z0,z1,z122,z3,z5,z6]),(0,[z0,z757,z2,z3,z5,z6])],[(0,[z9,z0,z2,z609,z15,z6]),(0,[z9,z222,z2,z3,z5,z6]),(0,[z0,z128,z2,z129,z5,z6]),(0,[z278,z0,z2,z3,z17,z6]),(0,[z0,z1,z2,z46,z29,z6])],[(0,[z0,z11,z758,z3,z5,z6]),(0,[z153,z759,z2,z3,z5,z6]),(0,[z9,z0,z72,z3,z5,z6]),(0,[z760,z0,z2,z3,z5,z6]),(0,[z0,z140,z2,z5,z15,z6]),(0,[z147,z11,z82,z3,z5,z6]),(0,[z320,z0,z2,z3,z105,z6]),(0,[z0,z8,z2,z35,z5,z108]),(0,[z8,z2,z3,z5,z6,z217])],[(0,[z74,z0,z22,z3,z5,z6]),(0,[z51,z11,z761,z3,z5,z6]),(0,[z9,z0,z2,z244,z5,z6])],[(0,[z523,z11,z22,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z762]),(0,[z7,z8,z2,z3,z121,z6]),(0,[z763,z0,z2,z3,z5,z6]),(1,[z0,z11,z3,z764,z6]),(0,[z152,z0,z11,z2,z3,z210]),(0,[z183,z0,z295,z2,z5,z6]),(0,[z0,z11,z2,z5,z6,z765])]],
   [[(0,[z9,z0,z218,z3,z5,z6]),(0,[z766,z0,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z399]),(0,[z95,z0,z2,z96,z5,z6]),(0,[z0,z11,z2,z5,z385,z6])],[(0,[z0,z8,z3,z5,z6,z646]),(0,[z0,z11,z3,z764,z20,z6])],[(0,[z0,z767,z2,z3,z5,z6]),(0,[z0,z11,z178,z173,z5,z6]),(0,[z98,z0,z11,z328,z5,z6])],[(0,[z768,z0,z11,z2,z5,z6]),(0,[z98,z0,z11,z431,z2,z6])],[(0,[z9,z0,z62,z3,z5,z6]),(0,[z769,z0,z2,z3,z5,z6]),(0,[z770,z0,z11,z2,z5,z6]),(0,[z771,z11,z2,z3,z5,z6]),(0,[z0,z371,z2,z3,z5,z6]),(0,[z42,z0,z2,z5,z17,z164]),(0,[z0,z11,z19,z36,z15,z6]),(0,[z772,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z773,z5,z6]),(0,[z9,z0,z2,z3,z5,z774]),(0,[z0,z316,z19,z3,z5,z6])],[(0,[z1,z750,z2,z3,z5,z6]),(0,[z0,z11,z2,z199,z15,z6])],[(0,[z0,z123,z2,z3,z5,z550]),(0,[z775,z0,z11,z2,z5,z6]),(0,[z51,z90,z72,z3,z5,z6]),(0,[z222,z11,z2,z3,z5,z10]),(0,[z9,z0,z2,z776,z5,z6]),(0,[z0,z2,z3,z5,z6,z777]),(0,[z0,z327,z2,z283,z5,z6]),(0,[z42,z0,z70,z2,z5,z164])],[],[(0,[z14,z11,z122,z3,z55,z6]),(0,[z0,z371,z2,z5,z15,z6])],[(0,[z50,z11,z2,z571,z5,z6]),(0,[z0,z778,z2,z3,z5,z6]),(0,[z9,z42,z0,z2,z5,z164]),(0,[z47,z11,z3,z5,z20,z6]),(0,[z148,z98,z0,z11,z2,z210])],[(0,[z0,z11,z122,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z779]),(0,[z0,z2,z73,z5,z17,z6])],[(0,[z124,z9,z22,z3,z5,z6]),(0,[z0,z2,z3,z46,z105,z6]),(0,[z0,z345,z2,z205,z15,z6])],[(0,[z9,z0,z702,z3,z5,z6]),(0,[z780,z11,z2,z3,z5,z6]),(0,[z98,z0,z317,z2,z5,z6])],[(0,[z0,z2,z3,z5,z781,z6]),(0,[z782,z8,z2,z3,z5,z6]),(0,[z148,z0,z2,z3,z17,z210]),(0,[z98,z0,z11,z2,z680,z6]),(0,[z0,z2,z3,z5,z6,z783])],[(0,[z0,z517,z2,z3,z5,z399]),(0,[z9,z784,z2,z3,z5,z6]),(0,[z0,z785,z2,z3,z5,z6]),(0,[z48,z0,z3,z17,z20,z6]),(0,[z0,z2,z5,z17,z6,z269]),(0,[z98,z0,z126,z174,z2,z6])]],
   [[(0,[z0,z786,z2,z3,z5,z6]),(0,[z0,z11,z122,z5,z15,z6]),(0,[z0,z2,z3,z5,z787,z6])],[(0,[z0,z788,z2,z3,z5,z6]),(0,[z0,z2,z5,z15,z6,z789])],[(0,[z790,z0,z11,z2,z5,z6]),(0,[z0,z2,z791,z3,z5,z6]),(0,[z0,z11,z2,z792,z5,z6]),(0,[z9,z0,z2,z3,z5,z793]),(0,[z0,z794,z2,z3,z5,z6])],[(0,[z65,z2,z82,z3,z5,z6]),(0,[z0,z2,z795,z3,z5,z6]),(0,[z98,z0,z11,z2,z280,z6])],[(0,[z0,z11,z2,z3,z5,z796]),(0,[z98,z0,z8,z2,z5,z6]),(0,[z797,z8,z2,z3,z5,z6]),(0,[z0,z344,z2,z3,z17,z6]),(0,[z118,z518,z0,z5,z157,z6])],[(0,[z0,z2,z3,z5,z798,z6]),(0,[z0,z2,z3,z5,z799,z6]),(0,[z0,z8,z2,z5,z29,z6]),(0,[z0,z1,z2,z3,z533,z6]),(0,[z800,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z801,z5,z6]),(0,[z0,z11,z2,z802,z5,z6]),(0,[z0,z8,z2,z3,z5,z76]),(0,[z0,z2,z3,z5,z6,z803])],[(0,[z51,z359,z72,z3,z5,z6]),(0,[z0,z8,z3,z667,z5,z6]),(0,[z0,z1,z328,z3,z5,z6]),(0,[z0,z2,z5,z385,z188,z6]),(0,[z98,z0,z11,z560,z5,z6]),(0,[z0,z804,z2,z3,z5,z6])],[(0,[z9,z0,z2,z3,z168,z18]),(0,[z0,z11,z2,z805,z5,z6]),(0,[z0,z1,z2,z238,z5,z6]),(0,[z11,z2,z806,z3,z5,z6])],[(0,[z9,z0,z2,z3,z5,z6]),(0,[z11,z2,z3,z121,z6,z606]),(0,[z104,z123,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z807]),(0,[z0,z289,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z108,z201]),(0,[z808,z0,z3,z5,z17,z6]),(0,[z138,z11,z2,z3,z5,z391]),(0,[z2,z809,z158,z3,z5,z6])],[(0,[z9,z0,z570,z3,z5,z6]),(0,[z0,z11,z377,z3,z5,z399]),(0,[z0,z2,z3,z5,z810,z6]),(0,[z483,z1,z2,z3,z5,z6])],[(0,[z0,z8,z237,z3,z5,z6]),(0,[z9,z0,z376,z3,z5,z6]),(0,[z811,z0,z2,z3,z5,z6]),(0,[z812,z0,z2,z3,z5,z6])],[(0,[z189,z2,z82,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z813]),(0,[z0,z814,z2,z3,z5,z6]),(0,[z11,z2,z3,z5,z6,z815])],[(0,[z816,z0,z11,z2,z5,z6]),(0,[z0,z2,z3,z5,z6,z817]),(0,[z9,z0,z2,z3,z5,z391]),(0,[z0,z125,z2,z5,z6,z614])],[(0,[z0,z392,z2,z3,z105,z6]),(0,[z818,z316,z2,z3,z5,z6]),(0,[z0,z28,z178,z173,z5,z6])]],
   [[(0,[z0,z11,z2,z5,z819,z6]),(0,[z0,z11,z2,z5,z820,z6]),(0,[z0,z11,z2,z821,z5,z6])],[(0,[z51,z72,z3,z5,z17,z6]),(0,[z14,z98,z11,z2,z55,z6]),(0,[z0,z822,z2,z3,z5,z6]),(0,[z0,z2,z3,z823,z5,z6])],[(0,[z824,z0,z11,z2,z5,z6]),(0,[z95,z0,z2,z5,z61,z6]),(0,[z825,z0,z2,z3,z5,z6])],[(0,[z153,z2,z62,z3,z5,z6]),(0,[z50,z1,z2,z209,z5,z6]),(0,[z0,z8,z2,z5,z75,z6]),(0,[z0,z826,z2,z3,z5,z6]),(0,[z148,z0,z11,z2,z332,z210])],[(0,[z0,z140,z2,z79,z5,z6]),(0,[z0,z140,z2,z73,z5,z6]),(0,[z8,z2,z827,z3,z5,z6]),(0,[z0,z2,z219,z5,z17,z6])],[(0,[z0,z11,z2,z828,z5,z6]),(0,[z0,z34,z2,z3,z5,z76]),(0,[z0,z175,z2,z77,z5,z6])],[(0,[z0,z8,z2,z79,z5,z6])],[(0,[z159,z98,z0,z2,z5,z6]),(0,[z0,z2,z5,z17,z6,z829]),(0,[z0,z11,z328,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z830]),(0,[z0,z11,z2,z238,z5,z6]),(0,[z831,z0,z11,z2,z5,z6])],[(0,[z197,z11,z2,z3,z55,z6]),(0,[z0,z147,z316,z3,z5,z6]),(0,[z0,z11,z2,z3,z18,z711])],[(0,[z0,z185,z2,z77,z5,z6])],[(0,[z483,z11,z2,z3,z5,z6]),(0,[z0,z2,z33,z5,z6,z307]),(1,[z0,z2,z3,z5,z832]),(0,[z0,z11,z2,z5,z833,z6])],[(0,[z0,z11,z834,z3,z5,z6]),(0,[z0,z11,z3,z5,z6,z835]),(0,[z836,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z837,z5,z6]),(0,[z0,z11,z328,z5,z15,z6])],[(0,[z98,z0,z146,z2,z5,z6]),(0,[z445,z11,z2,z5,z15,z6])],[(0,[z0,z2,z3,z5,z838,z6]),(0,[z47,z371,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z839]),(0,[z9,z0,z2,z5,z6,z269]),(0,[z98,z0,z175,z2,z5,z6]),(0,[z98,z0,z185,z2,z5,z6])]],
   [[(0,[z189,z98,z154,z2,z5,z6]),(0,[z0,z2,z3,z5,z6,z840]),(0,[z41,z0,z2,z3,z609,z6]),(0,[z841,z341,z2,z3,z5,z6]),(0,[z483,z11,z2,z5,z15,z6])],[(0,[z118,z9,z0,z5,z157,z6]),(0,[z0,z125,z70,z2,z5,z6]),(0,[z0,z2,z35,z5,z17,z108]),(0,[z0,z2,z3,z5,z832,z113]),(0,[z842,z0,z2,z3,z5,z6])],[(0,[z0,z8,z2,z107,z5,z6])],[(0,[z11,z22,z3,z5,z513,z6]),(0,[z50,z11,z2,z209,z5,z6]),(0,[z0,z295,z2,z3,z168,z18])],[(0,[z9,z0,z335,z22,z5,z6]),(1,[z0,z748,z3,z5,z6]),(0,[z222,z8,z2,z3,z5,z6]),(0,[z0,z295,z2,z3,z5,z6]),(0,[z843,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z844,z6]),(0,[z620,z0,z8,z3,z5,z6]),(0,[z0,z8,z2,z219,z5,z6]),(0,[z0,z11,z2,z845,z5,z6]),(0,[z0,z11,z2,z5,z846,z6]),(0,[z847,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z848,z5,z6]),(0,[z0,z2,z3,z5,z849,z6]),(0,[z0,z2,z3,z5,z850,z6]),(0,[z0,z2,z244,z5,z17,z6]),(0,[z851,z11,z2,z3,z5,z6])],[(0,[z0,z11,z122,z73,z5,z6]),(0,[z0,z2,z852,z3,z5,z6])],[(0,[z98,z0,z11,z2,z5,z6]),(0,[z0,z853,z2,z3,z5,z6]),(0,[z0,z8,z30,z3,z5,z39]),(0,[z0,z854,z2,z3,z5,z6])],[(0,[z60,z11,z377,z3,z5,z6]),(0,[z9,z341,z2,z3,z5,z6]),(0,[z183,z0,z1,z2,z5,z6]),(0,[z0,z2,z3,z5,z855,z6]),(0,[z0,z295,z2,z5,z15,z6])],[(0,[z0,z856,z2,z3,z5,z6]),(0,[z9,z0,z539,z3,z5,z6]),(0,[z255,z0,z2,z5,z58,z6]),(0,[z0,z11,z2,z5,z6,z857])],[(0,[z11,z287,z22,z3,z5,z6]),(0,[z858,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z35,z5,z288])],[(0,[z0,z2,z3,z5,z6,z859]),(0,[z48,z0,z371,z3,z20,z6])],[(0,[z9,z860,z2,z3,z5,z6]),(0,[z0,z2,z861,z3,z5,z6]),(0,[z0,z11,z5,z862,z157,z6])],[(0,[z0,z2,z3,z5,z17,z291]),(0,[z0,z19,z2,z3,z457,z6]),(0,[z95,z104,z2,z3,z5,z6])],[(0,[z0,z863,z2,z3,z5,z6])]],
   [[(0,[z0,z864,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z865])],[(0,[z98,z0,z11,z122,z5,z6]),(0,[z0,z8,z224,z3,z5,z6]),(0,[z824,z0,z8,z2,z5,z6]),(0,[z117,z8,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z832]),(0,[z0,z34,z2,z107,z5,z6]),(0,[z98,z0,z174,z317,z2,z6])],[(0,[z60,z2,z3,z5,z17,z57]),(0,[z0,z1,z2,z3,z5,z866])],[(0,[z0,z237,z33,z3,z5,z6]),(0,[z0,z1,z377,z3,z5,z6]),(0,[z0,z441,z2,z3,z5,z6]),(0,[z319,z2,z82,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z867]),(0,[z0,z1,z2,z3,z500,z6]),(0,[z868,z11,z2,z3,z5,z6]),(0,[z0,z869,z2,z3,z5,z6]),(0,[z183,z0,z2,z5,z258,z6])],[(0,[z0,z870,z2,z3,z5,z6]),(0,[z9,z0,z549,z3,z5,z6])],[(0,[z0,z11,z2,z871,z5,z6]),(0,[z9,z0,z72,z5,z15,z6]),(0,[z9,z0,z2,z73,z5,z6]),(0,[z9,z98,z0,z174,z2,z6])],[(0,[z297,z0,z2,z3,z5,z6]),(1,[z759,z2,z3,z5,z6]),(0,[z0,z11,z872,z3,z5,z6]),(0,[z0,z873,z2,z3,z5,z6]),(0,[z339,z9,z0,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z874]),(0,[z0,z11,z2,z5,z875,z6]),(0,[z0,z11,z2,z3,z5,z742]),(0,[z876,z0,z2,z3,z5,z6])],[(0,[z0,z517,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z139,z6]),(0,[z0,z11,z2,z5,z877,z6])],[(0,[z0,z2,z3,z5,z6,z878]),(0,[z0,z11,z2,z3,z5,z879]),(0,[z0,z880,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z881,z6]),(0,[z0,z11,z882,z3,z5,z6]),(0,[z9,z50,z2,z209,z5,z6]),(0,[z138,z1,z2,z3,z5,z6]),(0,[z0,z883,z2,z3,z5,z6])],[(0,[z884,z0,z11,z2,z3,z5]),(0,[z0,z2,z3,z17,z6,z120]),(0,[z0,z2,z885,z3,z5,z6])],[(0,[z0,z11,z2,z886,z5,z6]),(0,[z0,z887,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z291]),(0,[z0,z11,z888,z3,z5,z6]),(0,[z313,z0,z2,z3,z5,z6]),(0,[z0,z11,z889,z3,z5,z6])],[(0,[z159,z2,z22,z3,z5,z6]),(0,[z228,z11,z2,z4,z5,z6]),(0,[z9,z0,z557,z3,z5,z6]),(0,[z369,z0,z2,z3,z17,z6]),(0,[z0,z392,z2,z3,z232,z6]),(0,[z0,z11,z2,z5,z15,z874])],[(0,[z148,z9,z0,z2,z3,z210]),(0,[z0,z11,z3,z5,z6,z890]),(0,[z0,z891,z2,z3,z5,z6])],[(0,[z540,z0,z2,z3,z457,z6]),(0,[z0,z11,z2,z892,z5,z6]),(0,[z445,z185,z2,z3,z5,z6])],[(0,[z893,z0,z11,z2,z5,z6]),(0,[z60,z8,z2,z3,z5,z57]),(0,[z0,z2,z3,z5,z6,z894]),(0,[z98,z0,z174,z2,z17,z6]),(0,[z220,z0,z1,z2,z5,z6]),(0,[z0,z11,z5,z15,z6,z895])],[(0,[z0,z11,z2,z896,z5,z6]),(0,[z74,z0,z3,z5,z20,z6]),(0,[z313,z0,z2,z5,z15,z6])]],
   [[(0,[z0,z174,z2,z3,z457,z6]),(0,[z0,z2,z3,z5,z6,z897]),(0,[z11,z2,z3,z5,z6,z898]),(0,[z48,z0,z11,z3,z20,z76]),(0,[z899,z0,z11,z2,z5,z15])],[(0,[z341,z1,z2,z3,z5,z6])],[(0,[z0,z11,z2,z900,z5,z6]),(0,[z0,z11,z2,z3,z5,z866]),(0,[z50,z11,z2,z270,z5,z6]),(0,[z11,z2,z3,z901,z55,z6]),(0,[z860,z11,z2,z3,z5,z6]),(0,[z902,z0,z11,z2,z5,z6]),(0,[z903,z11,z2,z3,z5,z6])],[(0,[z0,z11,z377,z3,z5,z6]),(0,[z0,z11,z2,z244,z5,z391]),(0,[z0,z904,z2,z3,z5,z6]),(0,[z98,z905,z11,z2,z5,z6]),(0,[z0,z175,z2,z332,z5,z6])],[(0,[z228,z0,z1,z2,z5,z6]),(0,[z9,z0,z302,z3,z5,z6]),(1,[z0,z2,z457,z15,z6]),(0,[z9,z396,z0,z2,z5,z6]),(0,[z906,z0,z2,z3,z5,z6]),(0,[z0,z485,z2,z33,z5,z6]),(0,[z0,z11,z2,z3,z907,z6]),(0,[z0,z11,z3,z5,z312,z92])],[(0,[z0,z11,z908,z3,z5,z6]),(0,[z780,z11,z2,z5,z15,z6]),(0,[z0,z11,z2,z5,z163,z575]),(0,[z0,z909,z2,z3,z5,z6])],[(0,[z9,z0,z564,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z56]),(0,[z0,z11,z2,z3,z5,z832])],[(0,[z0,z910,z2,z3,z5,z6]),(0,[z0,z11,z19,z3,z5,z391]),(0,[z98,z0,z911,z2,z5,z6])],[(0,[z138,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z912,z6]),(0,[z11,z2,z913,z3,z5,z6]),(0,[z98,z341,z11,z2,z5,z6]),(0,[z0,z185,z2,z332,z5,z6])],[(0,[z7,z11,z2,z3,z406,z6])],[(0,[z0,z914,z2,z3,z5,z6]),(0,[z60,z11,z2,z3,z5,z399]),(0,[z41,z0,z2,z3,z5,z6]),(0,[z74,z0,z8,z3,z5,z6]),(0,[z0,z1,z560,z3,z5,z6]),(0,[z0,z2,z5,z15,z915,z6])],[(0,[z396,z0,z8,z2,z5,z6]),(0,[z916,z0,z11,z2,z5,z6])],[],[(0,[z98,z8,z2,z82,z5,z6]),(0,[z118,z0,z5,z17,z157,z6]),(0,[z118,z74,z0,z3,z5,z6]),(0,[z138,z11,z2,z5,z15,z6]),(0,[z0,z11,z3,z5,z39,z742]),(0,[z42,z0,z2,z5,z192,z164])],[(0,[z0,z503,z2,z3,z5,z353]),(0,[z0,z917,z2,z3,z5,z6]),(0,[z0,z2,z918,z3,z5,z6]),(0,[z0,z11,z919,z3,z5,z6])],[(0,[z11,z2,z3,z5,z10,z399]),(0,[z0,z2,z5,z15,z253,z6]),(0,[z0,z316,z2,z3,z5,z6]),(0,[z0,z11,z748,z3,z5,z6]),(0,[z0,z920,z2,z3,z5,z6]),(0,[z98,z0,z126,z2,z5,z6])]],
   [[(0,[z222,z11,z2,z3,z5,z57]),(0,[z0,z8,z3,z5,z83,z6]),(0,[z0,z1,z2,z5,z6,z921]),(0,[z313,z0,z2,z5,z6,z269]),(0,[z922,z11,z2,z3,z5,z6])],[(0,[z341,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z923]),(0,[z9,z0,z2,z5,z15,z6])],[(0,[z0,z1,z2,z3,z537,z6]),(0,[z924,z0,z2,z3,z5,z6]),(0,[z0,z11,z925,z3,z5,z6]),(0,[z9,z0,z644,z3,z5,z6]),(0,[z52,z0,z2,z3,z5,z592]),(0,[z0,z289,z2,z5,z15,z6])],[(0,[z0,z8,z87,z3,z5,z6]),(0,[z0,z371,z2,z3,z5,z76]),(0,[z0,z11,z5,z15,z926,z6]),(0,[z0,z927,z560,z3,z5,z6])],[(0,[z928,z0,z11,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z399]),(0,[z60,z11,z2,z3,z5,z929]),(0,[z9,z0,z272,z3,z5,z6]),(0,[z0,z316,z2,z5,z15,z6]),(0,[z811,z0,z2,z5,z15,z6])],[],[(0,[z0,z930,z2,z3,z5,z6]),(0,[z931,z11,z2,z3,z5,z6]),(0,[z42,z0,z289,z2,z5,z164])],[(0,[z0,z11,z932,z3,z5,z6]),(0,[z0,z125,z2,z933,z5,z6]),(0,[z0,z3,z5,z17,z934,z6]),(0,[z0,z123,z2,z3,z5,z213]),(0,[z11,z2,z3,z5,z6,z935]),(0,[z725,z98,z0,z2,z5,z6])],[(0,[z0,z11,z2,z3,z5,z936]),(0,[z0,z2,z3,z5,z937,z6]),(0,[z425,z330,z11,z2,z5,z6])],[(0,[z0,z2,z5,z385,z17,z6]),(0,[z928,z0,z11,z5,z15,z6]),(0,[z582,z0,z11,z5,z542,z6]),(0,[z148,z0,z11,z560,z3,z210]),(0,[z0,z2,z3,z168,z258,z18])],[(0,[z0,z122,z3,z5,z17,z6]),(0,[z0,z2,z5,z15,z6,z502]),(0,[z42,z0,z11,z2,z5,z384]),(0,[z0,z11,z560,z3,z5,z6])],[(0,[z0,z11,z938,z3,z5,z6]),(0,[z51,z11,z530,z3,z5,z6]),(0,[z9,z0,z2,z3,z939,z6]),(0,[z0,z940,z2,z3,z5,z6]),(0,[z0,z1,z2,z15,z17,z6]),(0,[z183,z0,z2,z5,z17,z6]),(0,[z0,z11,z2,z5,z6,z941]),(0,[z42,z0,z11,z2,z5,z387]),(0,[z0,z2,z3,z5,z6,z942]),(0,[z0,z943,z2,z3,z5,z6])],[(0,[z9,z0,z2,z944,z5,z6]),(0,[z0,z11,z2,z945,z5,z6]),(0,[z0,z123,z2,z5,z15,z213]),(0,[z48,z0,z11,z107,z20,z6])],[(0,[z98,z0,z11,z2,z633,z6]),(0,[z0,z11,z19,z3,z764,z6]),(0,[z0,z11,z590,z5,z245,z6]),(0,[z148,z222,z11,z2,z3,z210])],[(0,[z9,z51,z72,z3,z5,z6]),(0,[z356,z0,z2,z3,z5,z113]),(0,[z0,z2,z15,z17,z20,z6])],[(0,[z0,z11,z560,z5,z15,z6])]],
   [[(0,[z946,z0,z11,z2,z5,z6]),(0,[z0,z947,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z6,z921]),(0,[z0,z2,z5,z15,z511,z6])],[(0,[z591,z0,z72,z3,z5,z6]),(0,[z948,z11,z2,z3,z5,z6]),(0,[z949,z11,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z5,z950]),(0,[z0,z2,z3,z5,z6,z951]),(0,[z9,z0,z2,z205,z15,z6]),(0,[z0,z1,z2,z3,z609,z6]),(0,[z952,z0,z11,z2,z5,z6])],[(0,[z51,z11,z187,z3,z5,z6]),(0,[z953,z0,z2,z3,z5,z6]),(0,[z0,z517,z2,z73,z5,z6]),(0,[z954,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z213,z556])],[(0,[z0,z11,z2,z3,z5,z399]),(0,[z0,z147,z8,z3,z5,z6]),(0,[z955,z11,z2,z3,z5,z6])],[(0,[z44,z0,z8,z2,z5,z6]),(0,[z0,z2,z5,z505,z17,z6]),(0,[z0,z11,z2,z956,z5,z6])],[(0,[z104,z392,z2,z3,z5,z6]),(0,[z581,z1,z2,z3,z5,z6]),(0,[z118,z0,z11,z5,z862,z6])],[(0,[z957,z0,z2,z3,z5,z6]),(0,[z0,z2,z958,z3,z5,z6])],[(0,[z0,z959,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z76])],[(0,[z9,z98,z0,z2,z15,z6]),(0,[z0,z147,z8,z5,z15,z6]),(0,[z0,z11,z2,z604,z15,z6]),(0,[z98,z0,z11,z2,z397,z6])],[(0,[z0,z11,z122,z79,z5,z6]),(0,[z0,z340,z2,z3,z5,z621])],[(0,[z0,z11,z2,z5,z960,z6]),(0,[z81,z2,z143,z4,z5,z6]),(0,[z0,z1,z2,z5,z505,z6]),(0,[z9,z961,z2,z3,z5,z6])],[(0,[z962,z0,z11,z2,z5,z6]),(0,[z963,z0,z11,z2,z5,z6]),(0,[z0,z1,z2,z3,z17,z6]),(0,[z0,z11,z2,z5,z964,z6]),(0,[z47,z11,z19,z3,z5,z6]),(0,[z11,z158,z3,z5,z20,z6]),(0,[z965,z0,z11,z2,z5,z6]),(0,[z98,z966,z11,z2,z5,z6]),(0,[z137,z0,z11,z2,z5,z288])],[(0,[z0,z967,z2,z3,z5,z6]),(0,[z9,z11,z82,z3,z5,z6]),(0,[z968,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z969,z5,z6])],[(0,[z9,z0,z970,z3,z5,z6]),(0,[z0,z971,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z929]),(0,[z0,z394,z2,z3,z17,z6])],[(0,[z0,z11,z377,z73,z5,z6]),(0,[z0,z11,z2,z457,z15,z6]),(0,[z396,z0,z11,z2,z5,z6]),(0,[z118,z0,z11,z282,z5,z6]),(0,[z0,z371,z2,z107,z5,z6])]],
   [[(0,[z11,z376,z22,z3,z5,z6]),(0,[z0,z11,z972,z3,z5,z6]),(1,[z11,z2,z3,z901,z6]),(0,[z0,z11,z2,z973,z5,z6]),(0,[z68,z25,z0,z2,z5,z6])],[(0,[z0,z8,z2,z335,z5,z6]),(0,[z41,z0,z72,z3,z5,z6]),(0,[z0,z974,z2,z3,z5,z6]),(0,[z14,z11,z2,z3,z693,z6]),(0,[z0,z11,z2,z658,z15,z6]),(0,[z0,z1,z2,z244,z5,z6]),(0,[z43,z0,z11,z3,z5,z92]),(0,[z279,z0,z11,z2,z5,z531]),(0,[z148,z0,z175,z2,z3,z210])],[(0,[z0,z11,z2,z975,z5,z6]),(0,[z0,z976,z2,z3,z5,z6]),(0,[z9,z0,z2,z3,z5,z977]),(0,[z978,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z979]),(0,[z98,z0,z980,z2,z5,z6])],[(0,[z981,z0,z2,z3,z5,z6]),(0,[z0,z2,z982,z3,z5,z6]),(0,[z25,z0,z2,z3,z5,z113]),(0,[z0,z983,z2,z3,z5,z6]),(0,[z98,z0,z371,z2,z5,z6]),(0,[z0,z984,z2,z3,z5,z6])],[(0,[z400,z154,z2,z3,z5,z6]),(0,[z0,z985,z2,z3,z5,z6]),(0,[z98,z0,z11,z377,z5,z6]),(0,[z0,z11,z2,z986,z5,z6]),(0,[z95,z0,z2,z428,z5,z6]),(0,[z0,z11,z2,z168,z75,z18])],[(0,[z0,z11,z2,z617,z15,z6]),(0,[z0,z987,z2,z3,z5,z6]),(0,[z0,z327,z2,z33,z5,z6]),(0,[z988,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z989,z5,z6])],[(0,[z581,z11,z2,z3,z5,z6]),(0,[z228,z0,z2,z5,z17,z6]),(0,[z81,z1,z2,z4,z5,z6]),(0,[z0,z2,z33,z5,z424,z6]),(0,[z0,z11,z2,z5,z6,z990])],[(0,[z9,z98,z0,z211,z5,z6]),(0,[z0,z8,z2,z3,z5,z991])],[(0,[z9,z0,z687,z3,z5,z6]),(0,[z0,z992,z2,z3,z5,z6]),(0,[z14,z517,z2,z3,z55,z6]),(0,[z9,z0,z2,z79,z5,z6])],[(0,[z993,z0,z11,z2,z5,z6]),(0,[z0,z729,z2,z3,z5,z6]),(0,[z0,z11,z994,z3,z5,z6]),(0,[z0,z11,z995,z3,z5,z6]),(0,[z996,z0,z2,z3,z5,z6]),(0,[z265,z0,z2,z5,z108,z6])],[(0,[z9,z22,z3,z4,z5,z6]),(0,[z0,z997,z2,z3,z5,z6]),(0,[z998,z0,z2,z3,z5,z6]),(0,[z0,z8,z2,z77,z5,z6]),(0,[z0,z175,z328,z3,z5,z6]),(0,[z148,z0,z11,z2,z3,z210])],[(0,[z0,z11,z2,z5,z505,z6]),(0,[z0,z140,z2,z3,z5,z291]),(0,[z0,z2,z3,z5,z999,z6]),(0,[z0,z2,z3,z5,z6,z1000]),(0,[z581,z11,z2,z5,z15,z6]),(0,[z0,z441,z2,z5,z15,z6]),(0,[z445,z175,z2,z3,z5,z6])],[(0,[z1001,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z6,z1002]),(0,[z9,z0,z211,z3,z5,z6]),(0,[z591,z0,z2,z3,z5,z6])],[(0,[z297,z0,z2,z5,z15,z6]),(0,[z0,z2,z3,z5,z1003,z6]),(0,[z1004,z11,z2,z3,z5,z6]),(0,[z483,z175,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z669,z113]),(0,[z0,z517,z2,z5,z15,z6]),(0,[z0,z11,z2,z609,z15,z6]),(0,[z0,z2,z3,z5,z1005,z6]),(0,[z1006,z0,z2,z3,z5,z6]),(0,[z0,z185,z328,z3,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z1007]),(0,[z104,z147,z8,z3,z5,z6]),(0,[z0,z2,z107,z5,z17,z6]),(0,[z1008,z11,z2,z3,z5,z6]),(0,[z0,z1009,z2,z3,z5,z6])],[(0,[z0,z11,z2,z1010,z5,z6]),(0,[z1011,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z168,z17,z18]),(0,[z0,z11,z2,z244,z5,z6]),(0,[z98,z0,z1012,z2,z5,z6])],[(0,[z11,z2,z1013,z4,z5,z6]),(0,[z0,z1014,z2,z3,z5,z6]),(0,[z591,z0,z2,z5,z15,z6]),(0,[z0,z2,z5,z15,z188,z6])],[(0,[z9,z0,z626,z3,z5,z6]),(0,[z1015,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z1016,z5,z6]),(0,[z0,z8,z2,z5,z6,z273]),(0,[z11,z2,z3,z5,z6,z1017]),(0,[z483,z185,z2,z3,z5,z6])],[(0,[z14,z11,z377,z3,z55,z6]),(0,[z9,z7,z2,z3,z121,z6]),(0,[z9,z0,z2,z107,z5,z6]),(0,[z98,z581,z11,z2,z5,z6])],[(0,[z0,z179,z2,z33,z5,z6]),(0,[z1018,z11,z2,z3,z5,z6])],[(0,[z81,z11,z2,z4,z5,z6]),(0,[z0,z2,z79,z5,z17,z6]),(1,[z0,z11,z5,z862,z6]),(0,[z48,z0,z34,z3,z20,z6]),(0,[z0,z11,z328,z3,z5,z210])],[(0,[z0,z87,z3,z5,z17,z6]),(0,[z1019,z0,z2,z3,z5,z6]),(0,[z9,z0,z2,z219,z5,z6]),(0,[z0,z1020,z2,z3,z5,z6]),(0,[z98,z0,z11,z2,z5,z76]),(0,[z11,z2,z5,z15,z1021,z6]),(0,[z148,z0,z11,z328,z3,z210])],[(0,[z0,z1022,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z774])],[(0,[z9,z419,z72,z3,z5,z6]),(0,[z44,z0,z11,z2,z5,z6]),(0,[z0,z11,z5,z15,z934,z6])],[(0,[z0,z1023,z2,z3,z5,z6]),(0,[z9,z0,z30,z3,z5,z39]),(0,[z0,z11,z2,z776,z5,z6]),(0,[z732,z0,z2,z3,z5,z17]),(0,[z98,z0,z34,z2,z5,z6]),(0,[z483,z11,z2,z3,z5,z210])],[(0,[z9,z228,z0,z22,z5,z6]),(0,[z0,z2,z3,z1024,z5,z6]),(0,[z0,z11,z377,z5,z15,z6]),(0,[z0,z1,z2,z3,z168,z18])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z11,z2,z1025,z5,z6]),(0,[z0,z1026,z122,z3,z5,z6]),(0,[z0,z1027,z2,z3,z5,z6]),(0,[z1028,z8,z2,z3,z5,z6]),(0,[z0,z2,z3,z17,z6,z263]),(0,[z0,z2,z3,z5,z6,z1029]),(0,[z0,z2,z3,z1030,z5,z6]),(0,[z516,z11,z2,z5,z243,z6])],[(0,[z124,z8,z22,z3,z5,z6]),(0,[z1031,z0,z2,z3,z5,z6]),(0,[z0,z392,z2,z3,z5,z6]),(0,[z2,z827,z3,z5,z17,z6]),(0,[z0,z909,z2,z5,z15,z6])],[(0,[z0,z11,z122,z3,z5,z291]),(0,[z0,z2,z748,z3,z5,z6]),(0,[z0,z2,z3,z46,z1032,z6])],[(0,[z0,z11,z2,z1033,z5,z6]),(0,[z818,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z11,z2,z73,z5,z399]),(0,[z265,z0,z2,z3,z5,z6]),(0,[z11,z2,z3,z5,z6,z1034]),(0,[z1035,z0,z2,z3,z5,z6]),(0,[z222,z98,z11,z2,z5,z6]),(0,[z0,z295,z2,z5,z75,z6])],[(0,[z8,z2,z1036,z3,z5,z6]),(0,[z445,z2,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z391]),(0,[z1037,z11,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z1038,z6]),(0,[z9,z0,z2,z3,z5,z1039]),(0,[z41,z0,z2,z5,z15,z6]),(0,[z9,z0,z2,z35,z5,z108]),(0,[z0,z392,z2,z5,z15,z6])],[(0,[z0,z11,z2,z1040,z5,z6]),(0,[z98,z1018,z11,z2,z5,z6]),(0,[z1041,z0,z560,z3,z5,z6])],[(0,[z9,z104,z8,z3,z5,z6]),(0,[z483,z2,z3,z5,z17,z6])],[(0,[z153,z11,z87,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z793]),(0,[z1042,z11,z2,z3,z5,z6]),(0,[z265,z0,z2,z5,z15,z6])],[(0,[z0,z2,z3,z5,z6,z1043])],[(0,[z0,z11,z2,z3,z5,z1044]),(0,[z0,z1045,z2,z3,z5,z6]),(0,[z0,z1046,z2,z3,z5,z6])],[(0,[z1047,z0,z11,z2,z5,z6]),(0,[z0,z2,z3,z5,z213,z109]),(1,[z0,z11,z1048,z2,z6]),(0,[z0,z1049,z2,z3,z5,z6])],[(0,[z0,z1050,z2,z3,z5,z6]),(0,[z0,z125,z2,z227,z5,z6]),(0,[z148,z0,z8,z2,z3,z210]),(0,[z341,z11,z2,z5,z15,z6]),(0,[z98,z0,z11,z2,z260,z6])],[(0,[z65,z2,z3,z5,z6,z331]),(0,[z9,z22,z3,z5,z10,z6]),(0,[z1051,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1052,z6])],[(0,[z104,z154,z2,z3,z5,z6]),(0,[z0,z19,z2,z3,z105,z6]),(0,[z1053,z0,z11,z3,z5,z6]),(0,[z0,z11,z2,z1054,z5,z6]),(0,[z0,z11,z2,z3,z168,z18])],[(0,[z0,z11,z2,z3,z5,z6]),(0,[z51,z11,z476,z3,z5,z6]),(0,[z0,z2,z1055,z3,z5,z6]),(0,[z42,z0,z11,z2,z5,z164])],[(0,[z0,z2,z3,z1056,z5,z6]),(0,[z0,z1057,z2,z3,z5,z6]),(0,[z445,z8,z2,z3,z5,z6])],[(0,[z11,z2,z3,z5,z1058,z6]),(0,[z1059,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z1060,z6]),(0,[z0,z11,z2,z541,z15,z6])],[(0,[z818,z11,z2,z3,z5,z6])]],
   [[(0,[z0,z759,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z1061,z6]),(0,[z11,z2,z3,z5,z55,z399]),(0,[z392,z2,z82,z3,z5,z6]),(0,[z106,z0,z1,z3,z5,z92]),(0,[z0,z1,z2,z3,z1032,z6]),(0,[z0,z2,z5,z6,z242,z269]),(0,[z1053,z0,z11,z5,z15,z6]),(0,[z0,z1062,z2,z3,z5,z6])],[(0,[z1063,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z391]),(0,[z0,z264,z19,z3,z36,z6]),(0,[z1064,z0,z2,z3,z5,z6])],[(0,[z7,z11,z377,z3,z5,z6]),(0,[z95,z0,z325,z2,z5,z6]),(0,[z0,z1,z2,z5,z6,z269]),(0,[z118,z0,z11,z5,z157,z6])],[(0,[z98,z7,z11,z2,z121,z6])],[(0,[z0,z237,z3,z5,z17,z6]),(0,[z0,z1065,z2,z3,z5,z6])],[(0,[z14,z11,z2,z3,z55,z399]),(0,[z961,z11,z2,z3,z5,z6]),(0,[z0,z8,z2,z5,z730,z6]),(0,[z98,z117,z11,z2,z5,z6]),(0,[z48,z47,z11,z3,z20,z6]),(0,[z0,z11,z2,z3,z5,z711])],[(0,[z0,z11,z2,z3,z5,z1066]),(0,[z0,z517,z2,z79,z5,z6]),(0,[z88,z0,z2,z24,z5,z6]),(0,[z0,z1067,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z391]),(0,[z1068,z0,z11,z2,z5,z6]),(0,[z98,z0,z2,z885,z5,z6])],[(0,[z0,z2,z1069,z3,z5,z6]),(0,[z1070,z0,z2,z3,z5,z6]),(0,[z138,z11,z2,z3,z5,z76]),(0,[z97,z0,z11,z629,z5,z6])],[(0,[z0,z11,z2,z3,z5,z1071]),(0,[z0,z11,z19,z3,z493,z6]),(0,[z0,z623,z11,z2,z15,z6]),(0,[z9,z581,z2,z3,z5,z6]),(0,[z0,z8,z2,z332,z5,z6]),(0,[z104,z1,z2,z3,z5,z6]),(0,[z0,z11,z1072,z3,z5,z6])],[(0,[z0,z11,z1073,z3,z5,z6]),(0,[z0,z11,z1074,z3,z5,z6]),(0,[z98,z47,z11,z2,z5,z6])],[(0,[z60,z98,z11,z2,z5,z57]),(0,[z9,z0,z2,z5,z29,z6]),(0,[z0,z1,z2,z3,z280,z6])],[(0,[z1075,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z1076,z5,z6]),(0,[z1077,z11,z2,z3,z5,z6]),(0,[z47,z11,z2,z244,z5,z6]),(0,[z148,z0,z11,z2,z15,z210]),(0,[z746,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z15,z399]),(0,[z9,z2,z82,z3,z5,z6]),(0,[z0,z2,z129,z96,z5,z6]),(0,[z0,z8,z3,z5,z241,z6]),(0,[z98,z0,z1,z2,z15,z6]),(0,[z0,z11,z3,z5,z742,z92]),(0,[z0,z2,z5,z15,z258,z6]),(0,[z1078,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z1079,z5,z6]),(0,[z0,z2,z3,z5,z6,z1080]),(0,[z444,z0,z2,z96,z5,z6]),(0,[z1081,z0,z2,z3,z5,z6])],[(0,[z1082,z0,z11,z2,z5,z6]),(0,[z50,z11,z2,z1013,z5,z6]),(0,[z9,z379,z0,z2,z5,z6]),(0,[z379,z0,z1,z2,z5,z6]),(0,[z0,z19,z3,z36,z188,z6])],[(0,[z0,z2,z335,z5,z17,z6]),(0,[z239,z11,z2,z3,z5,z57]),(0,[z0,z11,z2,z5,z1083,z6]),(0,[z0,z2,z3,z5,z1084,z6]),(0,[z1085,z11,z2,z3,z5,z6]),(0,[z0,z2,z5,z15,z6,z192]),(0,[z1086,z11,z2,z3,z5,z6])]],
   [[(0,[z0,z1087,z2,z3,z5,z6]),(0,[z50,z11,z2,z5,z285,z6]),(0,[z0,z2,z3,z5,z1088,z6]),(0,[z0,z11,z2,z3,z1032,z6]),(0,[z0,z11,z2,z5,z990,z164])],[(0,[z9,z0,z237,z3,z5,z6]),(0,[z0,z11,z1089,z3,z5,z6]),(0,[z156,z0,z2,z3,z457,z6]),(0,[z74,z0,z19,z3,z5,z6]),(0,[z0,z11,z2,z15,z130,z6])],[(0,[z228,z50,z11,z2,z5,z6]),(0,[z0,z11,z1090,z3,z5,z6]),(0,[z0,z11,z377,z79,z5,z6]),(0,[z636,z11,z2,z3,z5,z57]),(0,[z0,z11,z2,z5,z6,z269]),(0,[z0,z11,z178,z5,z6,z127])],[(0,[z9,z0,z2,z3,z5,z1091]),(0,[z0,z2,z3,z5,z1092,z6]),(0,[z220,z0,z2,z5,z17,z6])],[(0,[z1093,z0,z2,z3,z5,z6]),(0,[z11,z2,z1094,z3,z5,z6]),(0,[z0,z1095,z2,z3,z5,z6]),(0,[z0,z441,z30,z3,z5,z39]),(0,[z1085,z11,z2,z5,z15,z6]),(0,[z0,z1096,z2,z3,z5,z6]),(0,[z148,z0,z185,z2,z3,z210])],[(0,[z98,z0,z2,z5,z457,z6]),(0,[z0,z11,z2,z3,z5,z1097]),(0,[z156,z0,z2,z238,z17,z6]),(0,[z220,z0,z1,z2,z46,z6]),(0,[z0,z2,z5,z15,z1098,z6]),(0,[z0,z2,z3,z1099,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1100]),(0,[z47,z1,z2,z3,z5,z6]),(0,[z313,z98,z0,z2,z5,z6]),(0,[z223,z0,z179,z2,z5,z6]),(0,[z0,z980,z2,z3,z5,z6]),(0,[z0,z1101,z328,z3,z5,z6])],[(0,[z104,z503,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z764,z6]),(0,[z596,z0,z11,z3,z5,z92]),(0,[z0,z1102,z2,z3,z5,z6]),(0,[z0,z2,z3,z1103,z5,z6])],[(0,[z104,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z1104,z5,z6]),(0,[z0,z1,z2,z73,z5,z6]),(0,[z98,z0,z2,z5,z253,z6]),(0,[z9,z0,z2,z5,z75,z6])],[(0,[z9,z60,z22,z3,z5,z6]),(0,[z0,z2,z1105,z3,z5,z6]),(0,[z9,z0,z664,z3,z5,z6]),(0,[z0,z28,z2,z3,z5,z6]),(0,[z0,z2,z5,z15,z105,z6]),(0,[z780,z2,z3,z5,z17,z6]),(0,[z98,z0,z943,z2,z5,z6])],[(0,[z124,z11,z335,z22,z5,z6]),(0,[z0,z1106,z2,z3,z5,z6]),(0,[z0,z8,z178,z173,z5,z6])],[(0,[z0,z1107,z2,z3,z5,z6]),(0,[z42,z0,z8,z2,z5,z164]),(0,[z25,z0,z2,z5,z15,z113]),(0,[z148,z0,z11,z2,z77,z210])],[(0,[z0,z11,z2,z5,z6,z1108])],[(0,[z0,z970,z22,z3,z5,z6]),(0,[z195,z0,z2,z3,z5,z109]),(0,[z104,z11,z2,z5,z15,z6]),(0,[z221,z0,z2,z96,z5,z6]),(0,[z0,z2,z36,z15,z17,z6]),(0,[z1109,z0,z11,z3,z5,z6]),(0,[z0,z175,z560,z3,z5,z6])],[(0,[z0,z359,z22,z3,z5,z6]),(0,[z0,z11,z30,z3,z5,z281]),(0,[z0,z11,z3,z36,z764,z6]),(0,[z0,z2,z3,z5,z1110,z6])],[(0,[z1111,z0,z11,z2,z5,z6])]],
   [[(0,[z0,z22,z3,z5,z457,z6]),(0,[z98,z0,z11,z2,z321,z6]),(0,[z0,z1,z1112,z3,z5,z6]),(0,[z98,z0,z264,z2,z5,z6])],[(0,[z11,z2,z3,z121,z901,z6]),(0,[z44,z0,z146,z2,z5,z6]),(0,[z118,z0,z8,z5,z157,z6]),(0,[z2,z3,z5,z17,z6,z1017])],[(0,[z118,z341,z11,z5,z157,z6]),(0,[z0,z2,z3,z5,z1113,z6]),(0,[z1109,z0,z11,z5,z15,z6]),(0,[z0,z11,z3,z5,z6,z895]),(0,[z98,z0,z11,z64,z2,z6]),(0,[z0,z185,z560,z3,z5,z6])],[(0,[z9,z50,z22,z3,z5,z6]),(0,[z7,z11,z2,z3,z5,z399]),(0,[z0,z8,z122,z3,z5,z6]),(0,[z98,z0,z2,z5,z6,z502]),(0,[z0,z2,z3,z5,z1114,z6]),(0,[z138,z11,z2,z107,z5,z6]),(0,[z0,z11,z2,z685,z15,z6]),(0,[z42,z0,z11,z2,z5,z990])],[(0,[z0,z11,z2,z1115,z5,z6]),(0,[z0,z1116,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z1117,z6]),(0,[z0,z11,z2,z1118,z5,z6]),(0,[z1,z2,z1094,z3,z5,z6])],[(0,[z9,z0,z211,z5,z15,z6]),(0,[z0,z2,z5,z17,z6,z273]),(0,[z0,z11,z2,z5,z1119,z6])],[(0,[z0,z2,z62,z3,z5,z6]),(0,[z47,z11,z2,z3,z5,z6]),(0,[z14,z11,z2,z3,z901,z6])],[(0,[z0,z1120,z2,z3,z5,z6]),(0,[z330,z11,z2,z209,z5,z6]),(0,[z74,z0,z3,z5,z495,z6])],[(0,[z0,z11,z2,z73,z5,z6]),(0,[z0,z2,z3,z5,z1121,z6]),(0,[z9,z98,z0,z2,z5,z6]),(1,[z0,z2,z3,z1032,z6]),(0,[z98,z0,z2,z15,z17,z6]),(0,[z48,z591,z0,z3,z20,z6]),(0,[z0,z2,z3,z5,z6,z789])],[(0,[z0,z2,z143,z5,z15,z6]),(0,[z9,z117,z2,z3,z5,z6]),(0,[z1122,z0,z11,z2,z5,z6]),(0,[z98,z0,z2,z5,z511,z6]),(0,[z0,z1123,z2,z3,z5,z6])],[(0,[z9,z60,z2,z3,z5,z57]),(0,[z9,z0,z3,z5,z6,z127]),(0,[z0,z1124,z2,z3,z5,z6]),(0,[z1125,z0,z2,z3,z5,z6])],[(0,[z189,z154,z2,z3,z5,z6]),(0,[z1126,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z1127]),(0,[z0,z1128,z2,z3,z5,z6]),(0,[z47,z11,z2,z5,z15,z6]),(0,[z47,z11,z2,z3,z5,z391]),(0,[z0,z264,z2,z5,z385,z6]),(0,[z98,z483,z11,z2,z5,z6])],[(0,[z11,z2,z82,z3,z5,z6]),(0,[z14,z11,z2,z15,z55,z6]),(0,[z0,z2,z3,z1129,z5,z6]),(0,[z104,z218,z2,z3,z5,z6])],[(0,[z14,z1,z2,z3,z55,z6]),(0,[z0,z11,z2,z5,z1130,z6]),(0,[z1131,z0,z11,z2,z5,z6]),(0,[z9,z902,z0,z2,z5,z6]),(0,[z9,z47,z2,z3,z5,z6]),(0,[z0,z327,z2,z5,z469,z6])],[(0,[z9,z153,z22,z3,z5,z6]),(0,[z0,z2,z3,z5,z915,z6])],[(0,[z0,z11,z1132,z3,z5,z6]),(0,[z584,z11,z22,z3,z5,z6]),(0,[z400,z2,z3,z5,z567,z6]),(0,[z444,z0,z2,z5,z61,z6])]],
   [[(0,[z189,z154,z2,z5,z15,z6]),(0,[z0,z146,z2,z5,z505,z6]),(0,[z0,z2,z3,z5,z457,z6]),(0,[z0,z11,z1112,z3,z5,z6]),(0,[z98,z445,z11,z2,z5,z6]),(0,[z0,z2,z3,z5,z6,z1133])],[(0,[z9,z0,z309,z3,z5,z6]),(0,[z0,z8,z19,z3,z36,z6]),(0,[z98,z0,z11,z2,z430,z6]),(0,[z68,z0,z70,z2,z5,z6]),(0,[z1134,z11,z2,z3,z5,z6]),(0,[z0,z1135,z2,z3,z5,z6])],[(0,[z74,z0,z173,z3,z5,z6])],[(0,[z0,z2,z3,z5,z253,z6]),(0,[z0,z1136,z2,z3,z5,z6]),(0,[z11,z2,z209,z1013,z5,z6]),(0,[z0,z11,z2,z79,z5,z399]),(0,[z0,z11,z2,z3,z5,z1137]),(0,[z0,z2,z3,z5,z468,z172]),(0,[z98,z0,z11,z19,z36,z6])],[(0,[z1138,z0,z11,z2,z5,z6]),(0,[z98,z0,z90,z2,z5,z6]),(0,[z0,z1139,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z15,z6]),(0,[z0,z2,z5,z15,z17,z6]),(0,[z0,z1140,z2,z3,z5,z6])],[(0,[z124,z98,z11,z22,z5,z6]),(0,[z0,z1141,z2,z3,z5,z6])],[(0,[z0,z1142,z2,z3,z5,z6]),(0,[z0,z11,z2,z933,z5,z6]),(0,[z11,z2,z5,z15,z6,z217]),(0,[z445,z11,z2,z332,z5,z6]),(1,[z0,z11,z2,z3,z711])],[(0,[z1143,z0,z11,z2,z3,z6]),(0,[z0,z11,z3,z5,z926,z6]),(0,[z106,z0,z3,z5,z17,z92]),(0,[z0,z11,z2,z5,z6,z1144])],[(0,[z0,z123,z237,z3,z5,z6]),(0,[z0,z2,z3,z5,z1145,z6]),(0,[z9,z98,z0,z8,z5,z6]),(0,[z0,z2,z5,z457,z15,z6]),(0,[z9,z0,z2,z5,z1146,z6]),(0,[z0,z147,z748,z3,z5,z6]),(0,[z0,z927,z2,z3,z5,z6])],[(0,[z104,z153,z2,z3,z5,z6]),(0,[z9,z1147,z0,z2,z5,z6]),(0,[z582,z0,z11,z5,z157,z6]),(0,[z1148,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z901,z6]),(0,[z7,z11,z2,z121,z505,z6]),(0,[z0,z2,z3,z5,z6,z1149]),(0,[z0,z11,z2,z312,z15,z6]),(0,[z42,z0,z11,z2,z5,z305]),(0,[z905,z11,z2,z3,z5,z6])],[(0,[z1150,z0,z2,z3,z5,z6]),(0,[z0,z938,z3,z5,z17,z6]),(0,[z152,z0,z11,z3,z20,z6]),(0,[z0,z1151,z2,z3,z5,z6])],[(0,[z11,z2,z3,z5,z929,z57]),(0,[z1,z2,z82,z3,z5,z6]),(0,[z0,z2,z3,z5,z1152,z6]),(0,[z0,z1153,z2,z3,z5,z6]),(0,[z0,z11,z178,z5,z862,z6]),(0,[z106,z0,z11,z3,z5,z742])],[(0,[z14,z11,z2,z3,z55,z6]),(0,[z98,z0,z11,z2,z361,z6]),(0,[z25,z0,z2,z3,z5,z832])],[(0,[z0,z2,z3,z5,z6,z502]),(0,[z0,z11,z2,z1154,z5,z6]),(0,[z0,z1155,z2,z3,z5,z6]),(0,[z9,z771,z2,z3,z5,z6]),(0,[z1156,z0,z2,z3,z5,z6])],[(0,[z9,z0,z2,z3,z5,z291]),(0,[z0,z1157,z2,z3,z5,z6]),(0,[z0,z8,z328,z3,z5,z6]),(0,[z68,z0,z1,z2,z5,z6]),(0,[z1158,z11,z2,z3,z5,z6])]],
   [[(0,[z0,z11,z394,z2,z15,z6]),(0,[z379,z0,z2,z5,z17,z6]),(0,[z0,z11,z2,z244,z5,z76]),(0,[z0,z11,z2,z1159,z5,z6]),(0,[z1160,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1161,z6])],[(0,[z0,z11,z504,z173,z5,z6])],[(0,[z418,z0,z2,z3,z17,z6]),(0,[z65,z759,z2,z3,z5,z6]),(0,[z1162,z0,z2,z3,z5,z6]),(0,[z1163,z11,z2,z3,z5,z6]),(0,[z0,z123,z2,z3,z5,z621]),(0,[z1006,z341,z2,z3,z5,z6])],[(0,[z483,z8,z2,z3,z5,z6]),(0,[z48,z138,z11,z3,z20,z6])],[(0,[z0,z11,z2,z5,z15,z6]),(0,[z189,z498,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z511,z6]),(0,[z782,z392,z2,z3,z5,z6]),(0,[z95,z0,z2,z5,z562,z6]),(0,[z0,z2,z5,z15,z6,z242]),(0,[z98,z0,z345,z2,z5,z6]),(0,[z0,z2,z3,z5,z6,z1164])],[(0,[z0,z1,z2,z3,z293,z6]),(0,[z0,z1,z2,z205,z15,z6]),(0,[z899,z0,z11,z2,z3,z5]),(0,[z0,z11,z2,z3,z5,z1165]),(0,[z0,z2,z3,z5,z6,z1166])],[(0,[z98,z0,z11,z87,z5,z6]),(0,[z0,z1167,z2,z3,z5,z6])],[(0,[z1168,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z457,z15,z6]),(0,[z1169,z11,z2,z3,z5,z6]),(0,[z0,z11,z1170,z3,z5,z6]),(0,[z98,z138,z11,z2,z5,z6]),(0,[z0,z1171,z2,z3,z5,z6])],[(0,[z0,z1172,z2,z3,z5,z6]),(0,[z2,z158,z3,z5,z17,z6]),(0,[z0,z2,z5,z15,z1173,z6])],[(0,[z0,z1174,z2,z3,z5,z6]),(0,[z0,z11,z2,z15,z6,z230])],[(0,[z0,z11,z2,z1175,z5,z6]),(0,[z0,z11,z328,z77,z5,z6])],[(0,[z9,z22,z3,z5,z55,z6]),(0,[z343,z0,z11,z3,z20,z6]),(0,[z98,z0,z1,z2,z17,z6]),(0,[z0,z1,z2,z3,z5,z76]),(0,[z98,z0,z2,z5,z188,z6]),(0,[z445,z11,z2,z77,z5,z6])],[(0,[z189,z759,z2,z3,z5,z6]),(0,[z1168,z0,z2,z5,z15,z6]),(0,[z0,z11,z2,z5,z108,z990])],[(0,[z0,z2,z5,z15,z233,z6]),(0,[z0,z2,z3,z5,z1176,z6])],[(0,[z1177,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z939,z6]),(1,[z0,z2,z933,z5,z6]),(0,[z1178,z11,z2,z3,z5,z6]),(0,[z118,z0,z11,z629,z5,z6]),(0,[z0,z2,z249,z5,z15,z6]),(0,[z483,z11,z2,z77,z5,z6])],[(0,[z0,z2,z3,z143,z5,z6]),(0,[z520,z11,z72,z3,z5,z6]),(0,[z74,z0,z72,z3,z5,z6]),(0,[z7,z2,z3,z121,z253,z6]),(0,[z9,z0,z82,z3,z5,z6]),(0,[z9,z483,z2,z3,z5,z6]),(0,[z0,z11,z2,z944,z5,z6])]],
   [[(0,[z11,z2,z761,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z1179]),(0,[z808,z0,z11,z3,z5,z6]),(0,[z379,z0,z2,z5,z6,z242]),(0,[z0,z1180,z2,z3,z5,z6]),(0,[z11,z2,z5,z15,z1181,z6])],[(0,[z0,z146,z2,z3,z5,z6]),(0,[z14,z2,z3,z55,z17,z6]),(0,[z0,z1182,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z468,z213])],[(0,[z0,z1183,z2,z3,z5,z6]),(0,[z11,z2,z1184,z3,z5,z6])],[(0,[z65,z2,z3,z5,z447,z6]),(0,[z0,z11,z2,z3,z1185,z6]),(0,[z782,z11,z2,z3,z5,z6]),(0,[z95,z356,z0,z2,z5,z6]),(0,[z0,z1,z2,z3,z240,z6]),(0,[z1186,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z1187,z6]),(0,[z9,z445,z2,z3,z5,z6]),(0,[z518,z0,z2,z3,z5,z6]),(0,[z0,z45,z316,z3,z5,z6])],[(0,[z297,z98,z0,z2,z5,z6]),(0,[z0,z11,z2,z3,z5,z1188]),(0,[z0,z11,z2,z3,z5,z1189]),(0,[z0,z11,z2,z205,z15,z6])],[(0,[z0,z2,z3,z5,z6,z1190]),(0,[z0,z2,z5,z15,z6,z40])],[(0,[z413,z153,z2,z3,z5,z6]),(0,[z11,z2,z158,z3,z5,z6]),(0,[z11,z377,z3,z5,z10,z6]),(0,[z98,z0,z28,z2,z5,z6]),(0,[z581,z11,z30,z3,z5,z39]),(0,[z0,z2,z3,z1191,z5,z6])],[(0,[z0,z16,z2,z3,z5,z6]),(0,[z9,z0,z87,z3,z5,z6]),(0,[z147,z8,z82,z3,z5,z6])],[(0,[z552,z11,z22,z3,z5,z6]),(0,[z0,z1192,z2,z3,z5,z6]),(0,[z0,z1193,z2,z3,z5,z6]),(0,[z518,z0,z2,z5,z15,z6]),(0,[z591,z98,z0,z2,z5,z6]),(0,[z0,z1194,z2,z3,z5,z6]),(0,[z0,z11,z174,z1048,z2,z6])],[(0,[z0,z11,z2,z3,z5,z1195]),(0,[z0,z2,z3,z5,z6,z1196]),(0,[z1197,z1,z2,z3,z5,z6]),(0,[z1198,z11,z2,z3,z5,z6])],[(0,[z51,z1,z72,z3,z5,z6]),(0,[z0,z1,z2,z79,z5,z6]),(0,[z0,z8,z2,z5,z385,z6]),(0,[z0,z2,z3,z5,z1199,z6]),(0,[z0,z2,z3,z1032,z17,z6]),(0,[z0,z11,z2,z3,z5,z76])],[(0,[z1200,z11,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z1201,z6]),(0,[z9,z0,z214,z3,z5,z6]),(0,[z0,z1202,z2,z3,z5,z6]),(0,[z0,z16,z2,z5,z15,z6]),(0,[z9,z0,z316,z3,z5,z6]),(0,[z0,z2,z933,z96,z5,z6])],[(0,[z0,z11,z1203,z3,z5,z6]),(0,[z0,z1204,z2,z3,z5,z6]),(0,[z0,z72,z3,z5,z457,z6]),(0,[z98,z0,z11,z2,z5,z291]),(0,[z1205,z0,z11,z2,z5,z6]),(0,[z0,z1206,z2,z3,z5,z6])],[(0,[z65,z153,z2,z3,z5,z6]),(0,[z1207,z0,z11,z2,z5,z6])]],
   [[(0,[z124,z297,z22,z3,z5,z6]),(0,[z7,z11,z2,z121,z15,z6]),(0,[z0,z19,z3,z36,z17,z6]),(0,[z0,z11,z2,z5,z6,z1208]),(0,[z0,z1209,z2,z3,z5,z6]),(0,[z0,z2,z3,z1210,z5,z6]),(0,[z0,z11,z19,z36,z385,z6])],[(0,[z95,z0,z2,z588,z5,z6]),(0,[z0,z11,z2,z3,z5,z1211]),(0,[z0,z2,z1212,z3,z5,z6]),(0,[z11,z2,z3,z5,z6,z1213]),(0,[z0,z28,z2,z5,z15,z6])],[(0,[z0,z8,z191,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z813]),(0,[z183,z0,z11,z2,z168,z18])],[(0,[z0,z642,z2,z3,z17,z6]),(0,[z104,z2,z33,z3,z5,z6]),(0,[z0,z1,z2,z3,z46,z6]),(0,[z183,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z3,z5,z990])],[(0,[z65,z153,z2,z5,z15,z6]),(0,[z0,z140,z122,z3,z5,z6]),(0,[z11,z2,z3,z5,z901,z6]),(0,[z44,z7,z11,z2,z121,z6]),(0,[z138,z2,z3,z5,z17,z6]),(0,[z25,z0,z2,z5,z273,z113])],[(0,[z0,z11,z2,z3,z5,z977]),(0,[z0,z1214,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z1215,z6]),(0,[z772,z2,z158,z3,z5,z6])],[(0,[z0,z1216,z2,z3,z5,z6]),(0,[z150,z0,z2,z3,z5,z370]),(0,[z0,z2,z3,z5,z188,z6]),(0,[z0,z11,z2,z1217,z5,z6]),(0,[z1218,z11,z2,z3,z5,z6]),(0,[z1219,z0,z11,z2,z5,z6])],[(0,[z343,z11,z2,z3,z55,z6]),(0,[z0,z1220,z2,z3,z5,z6]),(0,[z0,z1,z2,z107,z5,z6]),(0,[z48,z0,z1,z3,z20,z6]),(0,[z1,z2,z158,z3,z5,z6]),(0,[z396,z0,z264,z2,z5,z6])],[(0,[z0,z11,z2,z5,z1221,z6])],[(0,[z118,z0,z11,z184,z5,z6]),(0,[z14,z11,z2,z73,z55,z6]),(0,[z41,z98,z0,z2,z5,z6]),(0,[z0,z11,z2,z5,z6,z1222])],[(0,[z9,z0,z2,z332,z5,z6]),(0,[z0,z70,z2,z3,z5,z6]),(0,[z0,z1,z2,z219,z5,z6]),(0,[z1197,z11,z2,z3,z5,z6]),(0,[z1223,z11,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z168,z711])],[(0,[z51,z11,z72,z3,z5,z6]),(0,[z0,z11,z2,z79,z5,z6]),(0,[z0,z8,z377,z3,z5,z6]),(0,[z74,z0,z2,z3,z5,z6]),(0,[z9,z138,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z5,z6]),(0,[z11,z2,z3,z5,z1021,z6])],[(0,[z766,z0,z122,z3,z5,z6]),(0,[z265,z98,z0,z2,z5,z6])],[(0,[z0,z517,z2,z3,z5,z291]),(0,[z9,z0,z292,z3,z5,z6]),(0,[z0,z11,z3,z5,z934,z6]),(0,[z341,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z5,z6,z829]),(0,[z0,z1,z30,z3,z5,z39])],[(0,[z0,z2,z62,z5,z15,z6]),(0,[z0,z125,z2,z283,z5,z6]),(0,[z0,z911,z2,z3,z5,z6]),(0,[z0,z11,z19,z3,z611,z6]),(0,[z106,z379,z0,z11,z5,z92])],[(0,[z0,z2,z3,z668,z17,z6]),(0,[z228,z0,z2,z62,z5,z6]),(0,[z1224,z0,z2,z3,z5,z6]),(0,[z255,z104,z2,z3,z5,z6]),(0,[z0,z70,z2,z5,z15,z6])]],
   [[(0,[z0,z147,z62,z3,z5,z6]),(0,[z51,z11,z72,z5,z15,z6]),(0,[z9,z0,z5,z245,z15,z6]),(0,[z138,z8,z2,z3,z5,z6]),(0,[z0,z2,z658,z3,z17,z6]),(0,[z74,z0,z2,z5,z15,z6]),(0,[z0,z1225,z2,z3,z5,z6])],[(0,[z0,z1226,z2,z3,z5,z6]),(0,[z0,z11,z2,z1227,z5,z6]),(0,[z68,z0,z2,z5,z17,z6])],[(0,[z189,z2,z62,z3,z5,z6]),(0,[z9,z520,z72,z3,z5,z6]),(0,[z2,z82,z3,z5,z105,z6]),(0,[z392,z2,z827,z3,z5,z6]),(0,[z0,z2,z3,z5,z1228,z6])],[(0,[z0,z237,z3,z5,z6,z113]),(0,[z0,z11,z1229,z3,z5,z6]),(0,[z0,z2,z3,z5,z1230,z6])],[(0,[z14,z9,z2,z3,z55,z6]),(0,[z11,z2,z82,z5,z15,z6]),(0,[z0,z2,z3,z5,z6,z1231]),(0,[z98,z0,z295,z2,z5,z6])],[(0,[z0,z1232,z2,z3,z5,z6]),(1,[z11,z2,z1013,z5,z6]),(0,[z0,z1,z2,z35,z5,z108]),(0,[z0,z11,z173,z5,z862,z6]),(0,[z106,z0,z3,z5,z242,z92])],[(0,[z9,z0,z2,z335,z5,z6]),(0,[z50,z341,z11,z2,z5,z6]),(0,[z98,z0,z517,z2,z5,z6]),(0,[z104,z2,z3,z5,z105,z6]),(0,[z0,z1233,z2,z3,z5,z6]),(0,[z117,z1,z2,z3,z5,z6])],[(0,[z98,z0,z2,z143,z5,z6]),(0,[z7,z1,z2,z3,z121,z6]),(0,[z0,z8,z748,z3,z5,z6]),(0,[z0,z11,z2,z107,z5,z6])],[(0,[z153,z90,z2,z3,z5,z6]),(0,[z1041,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z1234,z6]),(0,[z1235,z0,z11,z2,z5,z6]),(0,[z98,z0,z2,z5,z6,z192]),(0,[z0,z11,z328,z332,z5,z6])],[(0,[z0,z11,z377,z3,z5,z291]),(0,[z44,z0,z2,z5,z253,z6]),(0,[z0,z1236,z2,z3,z5,z6]),(0,[z768,z0,z1,z2,z5,z6]),(0,[z0,z30,z3,z5,z39,z40])],[(0,[z0,z11,z2,z1237,z5,z6]),(0,[z9,z2,z158,z3,z5,z6]),(0,[z104,z2,z3,z5,z6,z109]),(0,[z0,z11,z2,z219,z5,z6]),(0,[z396,z0,z11,z19,z36,z6])],[(0,[z1238,z0,z2,z3,z5,z6]),(0,[z9,z183,z0,z2,z5,z6]),(0,[z0,z1239,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z310,z6]),(0,[z0,z1240,z2,z3,z5,z6]),(0,[z0,z11,z2,z107,z5,z391]),(0,[z0,z2,z3,z5,z1241,z6]),(0,[z0,z1242,z2,z3,z5,z6]),(0,[z483,z11,z2,z332,z5,z6]),(0,[z1243,z2,z3,z5,z6,z217])],[(0,[z0,z11,z30,z3,z5,z39])],[(0,[z228,z0,z11,z2,z5,z6]),(0,[z8,z2,z913,z3,z5,z6]),(0,[z0,z1244,z2,z3,z5,z6]),(0,[z1245,z11,z2,z3,z5,z6])],[(0,[z9,z0,z2,z77,z5,z6]),(0,[z138,z34,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z6,z1246]),(0,[z1247,z11,z2,z3,z5,z6])]],
   [[(0,[z189,z484,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z399]),(0,[z753,z11,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1248,z6]),(0,[z0,z2,z1249,z5,z17,z6]),(0,[z0,z1012,z2,z3,z5,z6]),(0,[z98,z0,z11,z1048,z2,z6])],[(0,[z0,z1250,z2,z3,z5,z6]),(0,[z81,z11,z2,z1013,z5,z6]),(0,[z0,z11,z1251,z3,z5,z6])],[(0,[z98,z0,z2,z5,z105,z6]),(0,[z0,z8,z560,z3,z5,z6]),(0,[z183,z0,z8,z2,z5,z6]),(0,[z74,z0,z3,z5,z39,z6]),(0,[z1252,z0,z2,z3,z5,z6]),(0,[z0,z1253,z2,z3,z5,z6]),(0,[z0,z11,z2,z35,z5,z990])],[(0,[z784,z11,z2,z3,z5,z6]),(0,[z0,z8,z2,z238,z5,z6]),(0,[z0,z2,z3,z5,z1254,z6]),(0,[z1245,z11,z2,z5,z15,z6])],[(0,[z0,z11,z2,z3,z5,z1255]),(0,[z222,z11,z2,z3,z5,z399])],[(0,[z0,z11,z2,z3,z5,z1039]),(0,[z9,z0,z166,z3,z5,z6]),(0,[z0,z11,z2,z293,z15,z6]),(0,[z47,z11,z2,z3,z5,z76]),(0,[z0,z11,z2,z35,z5,z108]),(0,[z11,z2,z1256,z3,z5,z6])],[(0,[z117,z11,z2,z3,z5,z6]),(0,[z0,z1257,z2,z3,z5,z6]),(0,[z0,z2,z205,z15,z17,z6]),(0,[z52,z0,z2,z3,z5,z113])],[(0,[z0,z154,z237,z3,z5,z6]),(0,[z7,z11,z2,z3,z121,z6]),(0,[z0,z2,z3,z232,z17,z6]),(0,[z1,z2,z3,z5,z6,z217]),(0,[z0,z2,z3,z5,z6,z1258]),(0,[z225,z0,z11,z504,z5,z6])],[(0,[z0,z11,z2,z5,z1259,z6]),(0,[z9,z0,z2,z5,z6,z273]),(0,[z156,z0,z2,z15,z17,z6]),(0,[z683,z484,z2,z3,z5,z6]),(0,[z0,z1260,z2,z3,z5,z6]),(0,[z106,z98,z0,z11,z5,z92]),(0,[z1078,z98,z0,z2,z5,z6])],[(0,[z9,z0,z290,z3,z5,z6]),(0,[z0,z11,z1261,z3,z5,z6]),(0,[z948,z8,z2,z3,z5,z6]),(0,[z95,z0,z70,z2,z5,z6])],[(0,[z0,z11,z2,z1262,z5,z6]),(0,[z0,z11,z1263,z3,z5,z6]),(0,[z0,z11,z1264,z3,z5,z6]),(0,[z0,z11,z2,z5,z1265,z6])],[(0,[z0,z2,z3,z5,z1266,z6]),(0,[z0,z11,z2,z1267,z5,z6]),(0,[z0,z2,z3,z5,z1268,z6]),(0,[z0,z2,z3,z1269,z5,z6]),(0,[z0,z2,z3,z5,z1270,z6]),(0,[z0,z11,z328,z3,z5,z18])],[(0,[z520,z153,z2,z3,z5,z6]),(0,[z0,z11,z2,z1271,z5,z6]),(0,[z1272,z11,z2,z3,z5,z6])],[(0,[z9,z0,z184,z3,z5,z6]),(0,[z0,z1026,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z574,z6]),(0,[z2,z82,z3,z5,z17,z6]),(0,[z0,z1,z2,z5,z29,z6]),(0,[z0,z11,z560,z77,z5,z6])],[(0,[z299,z11,z22,z3,z5,z6]),(0,[z50,z8,z2,z209,z5,z6]),(0,[z0,z11,z1048,z2,z3,z6])],[(0,[z9,z0,z22,z3,z5,z6]),(0,[z0,z1273,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z6,z1274]),(0,[z0,z1275,z2,z3,z5,z6]),(0,[z1276,z0,z2,z3,z5,z6]),(0,[z483,z11,z2,z3,z5,z18])]],
   [[(0,[z1277,z0,z11,z2,z3,z5]),(0,[z0,z2,z3,z5,z258,z6]),(0,[z25,z0,z2,z3,z5,z380]),(0,[z98,z0,z11,z30,z5,z39]),(0,[z169,z358,z11,z2,z5,z6])],[(0,[z98,z0,z11,z2,z463,z6]),(0,[z98,z104,z11,z2,z5,z6]),(0,[z25,z0,z2,z3,z5,z384]),(0,[z1278,z11,z2,z3,z5,z6]),(0,[z0,z2,z238,z5,z17,z6]),(0,[z0,z2,z3,z5,z6,z1279]),(0,[z0,z11,z2,z1249,z5,z6])],[(0,[z81,z159,z2,z4,z5,z6]),(0,[z581,z2,z3,z5,z17,z6]),(0,[z25,z98,z0,z2,z5,z113]),(0,[z339,z0,z11,z3,z5,z92])],[(0,[z0,z11,z2,z1280,z5,z6]),(0,[z9,z0,z19,z3,z36,z6]),(0,[z0,z2,z3,z5,z6,z192])],[(0,[z0,z1,z237,z3,z5,z6]),(0,[z9,z0,z22,z5,z15,z6]),(0,[z0,z11,z2,z3,z5,z1281])],[(0,[z1282,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z1283,z5,z6]),(0,[z11,z19,z158,z3,z5,z6])],[(0,[z0,z1284,z2,z3,z5,z6]),(0,[z0,z11,z1285,z3,z5,z6]),(0,[z0,z392,z3,z5,z83,z6])],[(0,[z25,z0,z2,z3,z5,z370]),(0,[z220,z0,z8,z2,z5,z6]),(0,[z1286,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z1287,z6]),(0,[z1288,z0,z11,z2,z5,z6]),(0,[z0,z1289,z2,z3,z5,z6])],[(0,[z7,z11,z2,z3,z901,z6]),(0,[z7,z146,z2,z3,z121,z6]),(0,[z0,z146,z2,z5,z15,z6]),(0,[z156,z0,z2,z3,z17,z6]),(0,[z0,z2,z3,z5,z1098,z6]),(0,[z0,z11,z2,z5,z15,z1281]),(0,[z732,z0,z11,z2,z5,z15])],[(0,[z0,z1290,z2,z3,z5,z6]),(0,[z9,z2,z3,z5,z6,z217]),(0,[z9,z0,z200,z3,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1291]),(0,[z0,z1,z2,z5,z75,z6]),(0,[z0,z2,z3,z5,z1292,z6]),(0,[z0,z2,z3,z5,z1293,z6]),(0,[z0,z1243,z2,z3,z5,z6])],[(1,[z11,z761,z3,z5,z6]),(0,[z106,z9,z0,z3,z5,z92]),(0,[z797,z11,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z599,z6]),(0,[z1294,z0,z2,z3,z5,z6]),(0,[z228,z0,z8,z2,z5,z6]),(0,[z9,z0,z530,z3,z5,z6]),(0,[z0,z2,z3,z5,z105,z6]),(0,[z0,z11,z2,z5,z29,z6]),(0,[z0,z2,z3,z633,z17,z6]),(0,[z98,z0,z2,z5,z17,z6])],[(0,[z228,z341,z11,z2,z5,z6]),(0,[z9,z81,z2,z4,z5,z6]),(0,[z41,z0,z316,z3,z5,z6]),(0,[z581,z8,z2,z3,z5,z6])],[(0,[z0,z62,z87,z3,z5,z6]),(0,[z48,z0,z2,z3,z457,z6]),(0,[z11,z2,z158,z5,z15,z6])]],
   [[(0,[z0,z2,z970,z3,z5,z6]),(0,[z51,z16,z2,z3,z5,z6]),(0,[z98,z0,z70,z2,z5,z6])],[(0,[z0,z2,z3,z5,z1295,z6]),(0,[z0,z2,z3,z5,z1296,z6]),(0,[z221,z0,z2,z428,z5,z6]),(0,[z47,z11,z2,z107,z5,z6])],[(0,[z9,z1015,z2,z3,z5,z6]),(0,[z0,z175,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1297,z6]),(0,[z0,z11,z178,z5,z245,z6]),(0,[z0,z1298,z2,z3,z5,z6])],[(0,[z297,z0,z2,z335,z5,z6]),(0,[z0,z178,z173,z5,z17,z6]),(0,[z0,z3,z5,z17,z6,z890]),(0,[z0,z11,z2,z5,z15,z76]),(0,[z42,z265,z0,z2,z5,z6])],[(0,[z0,z11,z237,z3,z5,z6]),(0,[z81,z2,z4,z5,z17,z6]),(0,[z0,z11,z2,z5,z108,z610]),(0,[z1299,z0,z11,z2,z5,z6])],[(0,[z11,z2,z3,z1013,z5,z6]),(0,[z1300,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z3,z5,z1091]),(0,[z1125,z98,z0,z2,z5,z6])],[(0,[z0,z1301,z2,z3,z5,z6]),(0,[z0,z185,z2,z3,z5,z6]),(0,[z0,z175,z2,z5,z15,z6])],[(0,[z11,z377,z3,z5,z55,z6]),(0,[z9,z0,z8,z3,z5,z6])],[(0,[z0,z11,z237,z5,z15,z6]),(0,[z0,z8,z2,z244,z5,z6]),(0,[z316,z2,z1094,z3,z5,z6])],[(0,[z276,z2,z3,z5,z447,z6]),(0,[z11,z30,z158,z3,z5,z39])],[(0,[z0,z11,z2,z5,z75,z6])],[(0,[z9,z189,z22,z3,z5,z6]),(0,[z0,z2,z3,z1302,z5,z6]),(0,[z0,z140,z377,z3,z5,z6]),(0,[z14,z11,z2,z79,z55,z6]),(0,[z9,z0,z336,z3,z5,z6]),(0,[z413,z487,z2,z3,z5,z6]),(0,[z222,z1,z2,z3,z5,z6]),(0,[z48,z98,z0,z11,z20,z6]),(0,[z0,z185,z2,z5,z15,z6])],[(0,[z9,z0,z8,z5,z15,z6]),(0,[z98,z0,z2,z5,z6,z242])],[(0,[z98,z65,z153,z2,z5,z6]),(0,[z81,z8,z2,z4,z5,z6]),(0,[z0,z2,z1303,z3,z5,z6]),(0,[z0,z1304,z2,z3,z5,z6]),(0,[z0,z2,z33,z5,z58,z6]),(0,[z0,z11,z2,z5,z862,z6]),(0,[z1305,z0,z11,z2,z5,z6])],[(0,[z0,z11,z2,z1306,z5,z6]),(0,[z16,z2,z22,z3,z5,z6]),(1,[z9,z82,z3,z5,z6]),(0,[z1307,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1308])]],
   [[(0,[z0,z11,z2,z1309,z5,z6]),(0,[z98,z104,z8,z2,z5,z6]),(0,[z0,z2,z3,z1310,z5,z6]),(0,[z445,z11,z328,z3,z5,z6]),(0,[z445,z11,z560,z3,z5,z6])],[(0,[z98,z0,z123,z2,z5,z213]),(0,[z1311,z11,z2,z3,z5,z6])],[(0,[z0,z1312,z2,z3,z5,z6]),(0,[z396,z0,z1,z2,z5,z6]),(0,[z1313,z0,z11,z2,z5,z6]),(0,[z1223,z11,z2,z5,z15,z6])],[(0,[z0,z11,z2,z1314,z5,z6]),(0,[z0,z1315,z2,z3,z5,z6]),(0,[z136,z9,z22,z3,z5,z6]),(0,[z0,z2,z3,z5,z1316,z6]),(0,[z0,z11,z2,z5,z1317,z6]),(0,[z98,z0,z2,z249,z5,z6]),(0,[z483,z11,z328,z3,z5,z6])],[(0,[z0,z2,z1318,z3,z5,z6]),(0,[z197,z0,z11,z2,z3,z210]),(0,[z9,z0,z490,z3,z5,z6]),(0,[z0,z317,z2,z3,z5,z6]),(0,[z0,z11,z3,z5,z764,z6])],[(0,[z9,z104,z2,z3,z5,z6])],[(0,[z9,z0,z2,z3,z754,z6]),(0,[z98,z0,z2,z5,z233,z6])],[(0,[z0,z11,z2,z3,z5,z1319]),(0,[z0,z1,z2,z3,z301,z6]),(0,[z98,z11,z2,z158,z5,z6])],[(0,[z0,z2,z3,z5,z17,z6]),(0,[z159,z0,z2,z3,z5,z6]),(0,[z0,z218,z237,z3,z5,z6]),(0,[z9,z0,z256,z3,z5,z6]),(0,[z0,z2,z5,z29,z17,z6]),(0,[z98,z0,z11,z2,z522,z6]),(0,[z0,z34,z2,z244,z5,z6]),(0,[z98,z0,z2,z5,z258,z6]),(0,[z0,z1320,z2,z3,z5,z6]),(0,[z148,z11,z2,z3,z217,z210])],[(0,[z0,z1321,z2,z3,z5,z6]),(0,[z0,z11,z2,z1322,z5,z6]),(0,[z0,z178,z173,z249,z5,z6])],[(0,[z11,z2,z3,z5,z6,z217]),(0,[z98,z0,z11,z344,z2,z6])],[(0,[z0,z8,z2,z1040,z5,z6]),(0,[z220,z0,z11,z2,z5,z6]),(0,[z0,z11,z560,z332,z5,z6])],[(0,[z222,z11,z2,z3,z5,z6]),(0,[z341,z8,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z630,z6]),(0,[z1323,z11,z2,z3,z5,z6])],[(0,[z9,z72,z22,z3,z5,z6]),(0,[z9,z0,z2,z5,z385,z6]),(0,[z0,z2,z3,z5,z17,z391]),(0,[z138,z371,z2,z3,z5,z6])],[(0,[z98,z0,z140,z2,z5,z6])],[(0,[z202,z11,z72,z3,z5,z6]),(0,[z0,z1324,z2,z3,z5,z6]),(0,[z41,z0,z2,z3,z457,z6]),(0,[z9,z0,z178,z173,z5,z6]),(0,[z98,z0,z392,z2,z5,z6]),(0,[z95,z0,z2,z933,z5,z6]),(0,[z1325,z11,z2,z3,z5,z6]),(0,[z0,z11,z1048,z2,z15,z6])]],
   [[(0,[z591,z0,z22,z3,z5,z6]),(0,[z0,z1326,z2,z3,z5,z6]),(0,[z48,z9,z0,z3,z20,z6]),(0,[z118,z0,z5,z511,z157,z6]),(0,[z148,z483,z11,z2,z3,z210])],[(0,[z11,z72,z761,z3,z5,z6]),(0,[z1327,z11,z2,z3,z5,z6]),(0,[z222,z11,z2,z5,z15,z6])],[(0,[z1328,z0,z11,z2,z5,z6]),(0,[z65,z2,z3,z640,z5,z6]),(0,[z0,z11,z2,z3,z5,z1329]),(0,[z0,z1,z2,z3,z5,z291]),(0,[z118,z117,z11,z5,z157,z6])],[(0,[z0,z11,z1330,z3,z5,z6]),(0,[z0,z8,z2,z3,z168,z18]),(0,[z0,z1331,z2,z3,z5,z6])],[(0,[z0,z11,z2,z3,z6,z1332]),(0,[z0,z11,z2,z381,z15,z6]),(0,[z11,z2,z3,z5,z6,z929]),(0,[z0,z2,z33,z933,z5,z6]),(0,[z1333,z0,z2,z3,z5,z6])],[(0,[z0,z153,z237,z3,z5,z6]),(0,[z48,z0,z11,z3,z764,z6]),(0,[z0,z11,z30,z5,z15,z39]),(0,[z148,z445,z11,z2,z3,z210])],[(0,[z0,z1334,z2,z3,z5,z6]),(0,[z60,z1,z2,z3,z5,z57]),(0,[z1327,z11,z2,z5,z15,z6]),(0,[z0,z1244,z2,z5,z15,z6])],[(0,[z0,z11,z2,z3,z5,z1335]),(0,[z0,z1,z1336,z3,z5,z6]),(0,[z0,z1337,z2,z3,z5,z6])],[(0,[z9,z0,z122,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z242])],[(0,[z98,z0,z11,z368,z2,z6]),(0,[z1338,z11,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z391]),(0,[z0,z11,z2,z1339,z5,z6]),(0,[z1340,z11,z2,z3,z5,z6])],[(0,[z98,z0,z11,z237,z5,z6]),(0,[z0,z11,z2,z1341,z5,z6]),(0,[z1342,z0,z2,z3,z5,z6]),(0,[z1343,z0,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z1146,z6]),(0,[z0,z1344,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z1173,z6]),(0,[z11,z2,z1345,z3,z5,z6]),(0,[z0,z2,z3,z5,z1346,z6]),(0,[z1347,z0,z2,z3,z5,z6])],[(0,[z0,z1348,z2,z3,z5,z6]),(0,[z11,z761,z22,z3,z5,z6]),(0,[z0,z140,z2,z3,z5,z399]),(0,[z0,z125,z2,z5,z430,z6])],[(0,[z0,z1349,z2,z3,z5,z6]),(0,[z0,z1350,z2,z3,z5,z6]),(0,[z0,z2,z3,z249,z5,z6]),(0,[z117,z11,z2,z5,z15,z6]),(1,[z0,z11,z3,z5,z742])],[(0,[z686,z0,z8,z3,z5,z6]),(0,[z0,z11,z178,z570,z5,z6]),(0,[z0,z8,z2,z3,z5,z399]),(0,[z1342,z0,z2,z5,z15,z6]),(0,[z221,z0,z325,z2,z5,z6]),(0,[z0,z11,z2,z3,z711,z210])]],
   [[(0,[z41,z0,z22,z3,z5,z6]),(0,[z0,z2,z378,z5,z61,z6]),(0,[z518,z98,z0,z2,z5,z6]),(0,[z0,z11,z2,z459,z15,z6]),(0,[z648,z11,z2,z5,z285,z6])],[(0,[z11,z2,z3,z5,z10,z654]),(0,[z9,z0,z303,z3,z5,z6]),(0,[z0,z2,z3,z5,z1351,z6]),(0,[z0,z2,z3,z5,z233,z6]),(0,[z0,z11,z2,z3,z6,z711])],[(0,[z0,z11,z2,z3,z5,z291]),(0,[z223,z0,z125,z2,z5,z6]),(0,[z0,z1352,z2,z3,z5,z6])],[(0,[z0,z2,z1353,z3,z5,z6]),(0,[z0,z11,z2,z15,z424,z6])],[(0,[z104,z2,z3,z5,z17,z6]),(0,[z11,z2,z3,z5,z1181,z6]),(0,[z0,z1,z2,z3,z424,z6])],[(0,[z0,z2,z3,z260,z17,z6]),(0,[z396,z0,z2,z5,z188,z6])],[(0,[z60,z11,z2,z3,z5,z57]),(0,[z0,z11,z2,z3,z1354,z6]),(0,[z0,z11,z2,z107,z5,z76])],[(0,[z189,z67,z2,z3,z5,z6]),(0,[z60,z11,z2,z3,z5,z665]),(0,[z0,z11,z1355,z3,z5,z6]),(0,[z0,z11,z2,z5,z15,z291]),(0,[z0,z264,z2,z3,z5,z6]),(0,[z98,z0,z147,z8,z5,z6]),(0,[z0,z8,z2,z5,z1083,z6]),(0,[z0,z11,z2,z3,z5,z867]),(0,[z0,z11,z1336,z3,z5,z6]),(0,[z0,z2,z3,z1356,z5,z6])],[(0,[z0,z2,z3,z5,z6,z1357]),(0,[z0,z2,z3,z5,z1358,z6]),(0,[z9,z8,z82,z3,z5,z6]),(0,[z968,z8,z2,z3,z5,z6]),(0,[z0,z2,z96,z5,z361,z6]),(0,[z0,z34,z2,z3,z5,z391]),(0,[z0,z2,z3,z5,z1359,z6]),(0,[z0,z1360,z2,z3,z5,z6])],[(0,[z0,z1361,z2,z3,z5,z6]),(0,[z0,z11,z2,z15,z6,z433]),(0,[z0,z2,z3,z5,z1362,z6])],[(0,[z252,z11,z22,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z40])],[(0,[z0,z1,z87,z3,z5,z6]),(0,[z60,z11,z2,z5,z15,z57]),(0,[z0,z8,z216,z3,z5,z6]),(0,[z0,z2,z1363,z3,z5,z6])],[(0,[z0,z8,z3,z5,z535,z6]),(0,[z0,z264,z2,z5,z15,z6]),(0,[z0,z11,z2,z5,z6,z1364]),(0,[z0,z2,z3,z5,z6,z1365])],[(0,[z0,z2,z3,z1366,z5,z6]),(0,[z978,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z1097])],[(0,[z0,z11,z1367,z3,z5,z6]),(0,[z9,z0,z476,z3,z5,z6]),(0,[z1368,z0,z2,z3,z5,z6]),(0,[z0,z1101,z2,z3,z5,z6])],[(0,[z0,z1369,z2,z3,z5,z6]),(0,[z74,z0,z211,z3,z5,z6])]],
   [[(0,[z759,z154,z2,z3,z5,z6]),(0,[z104,z8,z2,z3,z5,z6]),(0,[z0,z1370,z2,z3,z5,z6])],[(0,[z0,z11,z2,z1371,z5,z6]),(0,[z11,z2,z827,z3,z5,z6]),(0,[z98,z0,z2,z5,z6,z1372]),(0,[z1373,z11,z2,z3,z5,z6]),(0,[z0,z1374,z2,z3,z5,z6])],[(0,[z47,z2,z3,z5,z17,z6])],[(0,[z516,z11,z2,z4,z5,z6]),(0,[z0,z11,z2,z416,z15,z6]),(0,[z0,z316,z3,z5,z20,z6]),(0,[z0,z1375,z2,z3,z5,z6]),(0,[z42,z265,z0,z2,z5,z164])],[(0,[z0,z11,z1376,z3,z5,z6]),(0,[z9,z0,z328,z3,z5,z6]),(0,[z0,z1,z2,z3,z361,z6])],[(0,[z0,z11,z1377,z3,z5,z6]),(0,[z0,z2,z3,z5,z1378,z6]),(0,[z9,z0,z2,z3,z5,z830]),(0,[z9,z0,z2,z238,z5,z6]),(0,[z104,z8,z2,z5,z15,z6]),(0,[z98,z11,z2,z82,z5,z6]),(0,[z0,z126,z2,z3,z5,z6])],[(0,[z0,z8,z2,z5,z505,z6]),(0,[z2,z3,z5,z6,z217,z783])],[(0,[z9,z98,z0,z22,z5,z6]),(0,[z0,z2,z3,z1379,z5,z6]),(0,[z74,z98,z0,z2,z5,z6]),(0,[z0,z11,z3,z5,z862,z6])],[(0,[z9,z0,z187,z3,z5,z6]),(0,[z9,z0,z333,z3,z5,z6]),(0,[z0,z1380,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z213,z832]),(0,[z1381,z11,z2,z3,z5,z6]),(0,[z0,z1375,z2,z5,z15,z6])],[(0,[z81,z341,z11,z2,z5,z6]),(0,[z0,z11,z2,z1382,z5,z6]),(0,[z0,z11,z2,z5,z6,z1383]),(0,[z11,z2,z5,z15,z6,z815])],[(0,[z1384,z0,z2,z3,z5,z6]),(0,[z223,z0,z485,z2,z5,z6])],[(0,[z0,z11,z87,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1385]),(0,[z0,z1386,z2,z3,z5,z6])],[(0,[z0,z2,z3,z1387,z5,z6]),(0,[z0,z2,z3,z1388,z5,z6]),(0,[z0,z125,z2,z33,z5,z6]),(0,[z68,z0,z125,z2,z5,z6]),(0,[z0,z2,z3,z151,z17,z6]),(0,[z48,z0,z3,z233,z20,z6]),(0,[z0,z11,z2,z5,z1389,z6])],[(0,[z0,z1390,z2,z3,z5,z6]),(0,[z0,z1,z2,z332,z5,z6]),(0,[z0,z1391,z2,z3,z5,z6]),(0,[z0,z11,z1048,z2,z205,z6])],[(0,[z124,z22,z3,z5,z17,z6]),(0,[z47,z8,z2,z3,z5,z6])],[(0,[z752,z0,z377,z3,z5,z6])]],
   [[(0,[z0,z11,z87,z5,z15,z6]),(0,[z0,z2,z1392,z3,z5,z6]),(0,[z0,z1393,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z1394,z6]),(0,[z1395,z0,z2,z3,z5,z6]),(0,[z95,z0,z2,z24,z5,z6]),(0,[z0,z2,z3,z933,z5,z6]),(0,[z0,z2,z378,z96,z5,z6])],[(0,[z0,z11,z2,z1396,z5,z6]),(0,[z9,z0,z2,z5,z844,z6])],[(0,[z0,z323,z8,z3,z5,z6]),(0,[z0,z2,z3,z160,z17,z6]),(0,[z0,z1397,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1398,z6]),(0,[z0,z328,z3,z5,z17,z6]),(0,[z0,z1,z2,z46,z15,z6])],[(0,[z189,z11,z87,z3,z5,z6]),(0,[z0,z1399,z2,z3,z5,z6]),(0,[z0,z2,z1400,z3,z5,z6]),(0,[z1401,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z1402,z6]),(0,[z884,z0,z11,z2,z5,z15])],[(0,[z235,z11,z22,z3,z5,z6]),(0,[z68,z0,z8,z2,z5,z6]),(0,[z1403,z0,z11,z2,z5,z6])],[(0,[z0,z2,z33,z71,z5,z6]),(0,[z0,z517,z122,z3,z5,z6]),(0,[z398,z419,z2,z3,z5,z6]),(0,[z1404,z0,z11,z2,z5,z6]),(0,[z0,z371,z2,z244,z5,z6]),(0,[z483,z11,z560,z3,z5,z6])],[(0,[z0,z123,z2,z3,z5,z832])],[(0,[z0,z359,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1405]),(0,[z0,z560,z3,z5,z17,z6]),(0,[z2,z3,z5,z17,z6,z217]),(0,[z0,z11,z30,z3,z5,z742]),(0,[z1406,z0,z2,z3,z5,z6])],[(0,[z0,z1,z2,z335,z5,z6]),(0,[z106,z0,z8,z3,z5,z92]),(0,[z41,z0,z256,z3,z5,z6])],[(0,[z0,z2,z3,z1407,z5,z6])],[(0,[z0,z8,z2,z3,z5,z1137]),(0,[z0,z2,z3,z17,z105,z6])],[(0,[z9,z1338,z2,z3,z5,z6]),(0,[z0,z123,z2,z3,z5,z671]),(0,[z0,z317,z2,z5,z15,z6]),(0,[z0,z2,z3,z5,z6,z1372])],[(0,[z0,z2,z3,z5,z6,z1408]),(0,[z136,z520,z2,z3,z5,z6]),(0,[z9,z0,z3,z5,z245,z6]),(0,[z95,z0,z2,z100,z5,z6]),(0,[z650,z0,z2,z3,z5,z380]),(0,[z0,z1409,z2,z3,z5,z6]),(0,[z0,z2,z3,z1410,z5,z6]),(0,[z0,z11,z2,z332,z5,z6])],[(0,[z398,z11,z22,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z1411]),(0,[z0,z11,z2,z73,z5,z291]),(0,[z1147,z0,z11,z2,z5,z6]),(0,[z0,z125,z2,z652,z5,z6])],[(0,[z0,z11,z2,z3,z5,z1412]),(0,[z98,z0,z289,z2,z5,z6])]],
   [[(0,[z68,z189,z0,z2,z5,z6]),(0,[z159,z0,z2,z5,z15,z6]),(0,[z148,z0,z1,z2,z3,z210]),(0,[z0,z2,z3,z5,z1413,z6]),(0,[z0,z11,z2,z3,z706,z18]),(0,[z0,z11,z2,z453,z15,z6])],[(0,[z228,z297,z0,z2,z5,z6]),(0,[z0,z1,z2,z3,z457,z6]),(0,[z966,z11,z2,z3,z5,z6])],[(0,[z8,z2,z82,z3,z5,z6]),(0,[z656,z0,z8,z3,z5,z6]),(0,[z0,z1,z2,z77,z5,z6]),(0,[z98,z0,z2,z5,z6,z40]),(0,[z0,z11,z101,z3,z5,z39])],[(0,[z11,z2,z3,z5,z693,z57]),(0,[z1414,z0,z11,z2,z5,z6]),(0,[z0,z345,z2,z3,z5,z6])],[(0,[z68,z65,z0,z2,z5,z6]),(0,[z104,z90,z2,z3,z5,z6]),(0,[z98,z1373,z11,z2,z5,z6])],[(0,[z0,z140,z2,z3,z5,z6]),(0,[z14,z8,z2,z3,z55,z6]),(0,[z74,z0,z392,z3,z5,z6]),(0,[z98,z0,z8,z2,z15,z6]),(0,[z106,z313,z0,z3,z5,z92])],[(0,[z0,z11,z761,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6]),(0,[z65,z153,z237,z3,z5,z6]),(0,[z8,z2,z82,z5,z15,z6]),(0,[z379,z0,z8,z2,z5,z6])],[(0,[z0,z11,z2,z1415,z5,z6]),(0,[z0,z345,z2,z5,z15,z6]),(0,[z0,z2,z3,z5,z1416,z6])],[(0,[z124,z11,z761,z3,z5,z6]),(0,[z0,z11,z2,z335,z5,z6])],[(0,[z1163,z8,z2,z3,z5,z6]),(0,[z1178,z2,z3,z5,z17,z6]),(0,[z0,z11,z2,z1417,z5,z6]),(0,[z0,z2,z3,z5,z6,z1418])],[(0,[z11,z759,z2,z3,z5,z6]),(0,[z65,z153,z87,z3,z5,z6]),(0,[z0,z11,z2,z1419,z5,z6]),(0,[z98,z51,z11,z72,z5,z6]),(0,[z0,z2,z3,z5,z353,z113]),(0,[z0,z30,z3,z5,z17,z39]),(0,[z0,z1,z2,z5,z6,z273]),(0,[z1420,z0,z11,z2,z5,z6]),(0,[z0,z1421,z2,z3,z5,z6]),(0,[z0,z2,z5,z75,z258,z6])],[(0,[z51,z11,z309,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1422]),(0,[z0,z8,z2,z5,z15,z6]),(0,[z48,z0,z2,z3,z105,z6]),(0,[z0,z1423,z2,z3,z5,z6])],[(0,[z582,z9,z0,z3,z5,z6]),(0,[z9,z0,z545,z3,z5,z6]),(0,[z0,z2,z3,z5,z1424,z6]),(0,[z0,z1425,z2,z3,z5,z6])],[(0,[z98,z0,z359,z2,z5,z6]),(0,[z0,z2,z3,z5,z6,z1426]),(0,[z1427,z11,z2,z3,z5,z6])],[(0,[z44,z0,z1,z2,z5,z6]),(0,[z1428,z0,z11,z2,z5,z6]),(0,[z0,z11,z2,z5,z6,z1429]),(0,[z1169,z8,z2,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z991]),(0,[z782,z2,z3,z5,z17,z6]),(0,[z11,z2,z1430,z3,z5,z6])]],
   [[(0,[z0,z1431,z2,z3,z5,z6]),(0,[z9,z0,z377,z3,z5,z6]),(0,[z0,z2,z103,z3,z17,z6]),(0,[z156,z0,z2,z3,z1032,z6]),(0,[z68,z25,z0,z2,z5,z113]),(0,[z98,z0,z11,z2,z674,z6]),(0,[z0,z1432,z2,z3,z5,z6])],[(0,[z0,z123,z2,z3,z5,z420]),(0,[z0,z1433,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z1434,z6]),(0,[z582,z9,z0,z5,z15,z6]),(0,[z2,z3,z5,z17,z1181,z6]),(0,[z0,z11,z2,z77,z5,z6]),(0,[z98,z11,z2,z5,z6,z217])],[(0,[z0,z2,z3,z5,z1435,z6]),(0,[z14,z11,z2,z3,z55,z291]),(0,[z0,z11,z2,z1436,z5,z6]),(0,[z379,z313,z0,z2,z5,z6])],[(0,[z526,z0,z2,z227,z5,z6])],[(0,[z124,z1,z22,z3,z5,z6]),(0,[z156,z98,z0,z2,z17,z6]),(0,[z0,z1261,z3,z5,z17,z6]),(0,[z1053,z0,z3,z5,z17,z6]),(0,[z0,z1,z2,z3,z5,z1437]),(0,[z0,z2,z809,z3,z5,z6])],[(0,[z0,z11,z3,z5,z6,z1438]),(0,[z0,z34,z2,z3,z5,z6]),(0,[z0,z1,z19,z3,z36,z6]),(0,[z0,z371,z2,z3,z5,z391]),(0,[z1439,z11,z2,z3,z5,z6]),(0,[z106,z0,z11,z5,z269,z92])],[(0,[z2,z62,z82,z3,z5,z6]),(0,[z0,z11,z2,z3,z5,z1440]),(0,[z7,z2,z3,z121,z17,z6]),(0,[z0,z1441,z2,z3,z5,z6]),(0,[z156,z0,z2,z219,z17,z6]),(0,[z0,z2,z3,z5,z17,z76]),(0,[z41,z0,z19,z3,z36,z6]),(0,[z0,z392,z19,z3,z36,z6])],[],[(0,[z0,z11,z2,z5,z1442,z6]),(0,[z68,z0,z11,z2,z5,z6]),(0,[z98,z0,z316,z2,z5,z6]),(0,[z0,z1443,z2,z3,z5,z6])],[(0,[z0,z11,z2,z5,z1444,z6]),(0,[z11,z2,z3,z5,z1445,z6]),(0,[z104,z2,z129,z3,z5,z6])],[(0,[z11,z2,z1036,z3,z5,z6]),(0,[z0,z11,z2,z5,z6,z273]),(0,[z1446,z0,z11,z2,z5,z6]),(0,[z0,z34,z2,z5,z15,z6])],[(0,[z124,z62,z22,z3,z5,z6]),(0,[z9,z0,z748,z3,z5,z6]),(0,[z304,z0,z11,z2,z5,z305])],[(0,[z0,z11,z2,z3,z438,z18]),(0,[z48,z0,z8,z3,z20,z6]),(0,[z0,z8,z2,z5,z6,z269]),(0,[z0,z8,z2,z205,z15,z6]),(0,[z841,z0,z2,z3,z5,z6]),(0,[z106,z0,z11,z3,z5,z92]),(0,[z0,z1447,z2,z3,z5,z6])],[(0,[z0,z11,z2,z1448,z5,z6]),(0,[z0,z11,z1048,z2,z5,z6])],[(0,[z0,z359,z72,z3,z5,z6]),(0,[z0,z2,z1449,z3,z5,z6]),(0,[z98,z0,z174,z8,z2,z6]),(0,[z0,z11,z2,z5,z15,z867])]],
   [[(0,[z0,z1450,z2,z3,z5,z6])],[(0,[z9,z7,z22,z3,z5,z6]),(0,[z9,z220,z0,z2,z5,z6]),(0,[z0,z1451,z2,z3,z5,z6])],[(0,[z0,z11,z2,z1013,z5,z6]),(0,[z98,z0,z16,z2,z5,z6]),(0,[z42,z0,z1,z2,z5,z164]),(0,[z106,z0,z11,z5,z15,z92])],[(0,[z189,z419,z2,z3,z5,z6]),(0,[z0,z11,z122,z3,z5,z399]),(0,[z1452,z0,z2,z3,z5,z6]),(0,[z0,z11,z2,z5,z1453,z6])],[(0,[z0,z11,z1454,z3,z5,z6]),(0,[z0,z11,z2,z1455,z5,z6]),(0,[z9,z0,z3,z5,z6,z409]),(0,[z1028,z11,z2,z3,z5,z6]),(0,[z279,z0,z11,z2,z5,z164]),(1,[z0,z11,z2,z5,z990])],[(0,[z0,z11,z2,z3,z5,z1437]),(0,[z124,z11,z22,z3,z5,z6]),(0,[z445,z1,z2,z3,z5,z6])],[(0,[z7,z11,z2,z3,z578,z6]),(0,[z0,z2,z332,z5,z17,z6]),(0,[z0,z2,z77,z5,z17,z6]),(0,[z0,z11,z19,z3,z36,z6]),(0,[z48,z0,z11,z244,z20,z6])],[(0,[z1456,z0,z2,z3,z5,z6]),(0,[z1457,z0,z2,z3,z5,z6]),(0,[z9,z0,z560,z3,z5,z6]),(0,[z396,z0,z2,z5,z17,z6])],[(0,[z0,z377,z3,z5,z17,z6]),(0,[z95,z0,z394,z2,z5,z6]),(0,[z118,z0,z1,z5,z157,z6])],[(0,[z159,z51,z2,z3,z5,z6]),(0,[z1458,z0,z11,z2,z5,z6]),(0,[z98,z0,z11,z2,z15,z6])],[(0,[z124,z11,z22,z5,z15,z6]),(0,[z0,z2,z3,z5,z1459,z6]),(0,[z0,z2,z3,z5,z1460,z6]),(0,[z0,z11,z2,z168,z15,z18]),(0,[z98,z0,z1425,z2,z5,z6])],[(0,[z0,z90,z2,z3,z5,z6]),(0,[z0,z11,z2,z1461,z5,z6]),(0,[z379,z0,z11,z2,z5,z6])],[(0,[z9,z228,z0,z2,z5,z6]),(0,[z0,z1462,z2,z3,z5,z6]),(0,[z0,z11,z1463,z3,z5,z6])],[(0,[z95,z0,z237,z3,z5,z6]),(0,[z0,z11,z1464,z3,z5,z6]),(0,[z8,z2,z158,z3,z5,z6]),(0,[z0,z2,z205,z142,z15,z6]),(0,[z0,z126,z2,z5,z15,z6])],[(0,[z0,z11,z2,z5,z1465,z6]),(0,[z0,z8,z2,z1217,z5,z6]),(0,[z0,z1466,z2,z3,z5,z6]),(0,[z98,z0,z2,z142,z5,z6]),(0,[z1467,z0,z11,z2,z5,z6])],[(0,[z0,z1468,z2,z3,z5,z6]),(0,[z0,z8,z2,z1118,z5,z6]),(0,[z0,z2,z3,z5,z1032,z6]),(0,[z0,z11,z2,z5,z1469,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 492) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 492).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 982).take 484) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1466).take 105) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1571)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [492, 490, 484, 105] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 136).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 136).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 250).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 368).take 132).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 500).take 12).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [136, 114, 118, 132, 12] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_38681

theorem PEqualNP.Outside.L_meta_38681 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4205505160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4205505160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38681.solve