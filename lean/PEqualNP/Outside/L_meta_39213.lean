import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39213

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4205504640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4000011880950db0#64 ++ 0x44000011880950db#64 ++ 0xb012533983ff1fff#64 ++ 0xfb012533983ff1ff#64 : BitVec 256),
   (0x8024844a624c62d2#64 ++ 0xa8024844a624c62d#64 ++ 0x7c6dacce624ce3f7#64 ++ 0xf7c6dacce624ce3f#64 : BitVec 256),
   (0x058e30f02c70b464#64 ++ 0x3058e30f02c70b46#64 ++ 0xf78e30f07c70fc7e#64 ++ 0xaf78e30f07c70fc7#64 : BitVec 256),
   (0x0af03f005780db08#64 ++ 0xc0af03f005780db0#64 ++ 0xfbf03f007f80ff8d#64 ++ 0x9fbf03f007f80ff8#64 : BitVec 256),
   (0x037fc0007b6a000f#64 ++ 0x0037fc0007b6a000#64 ++ 0xe3ffc0007fff000c#64 ++ 0x7e3ffc0007fff000#64 : BitVec 256),
   (0x03db7aa500000000#64 ++ 0x003db7aa50000000#64 ++ 0xefffffff80000003#64 ++ 0xfefffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffc0007fff000c 0x7e3ffc0007fff000

def z1 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff80000003 0xfefffffff8000000

def z2 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e30f07c70fc7e 0xaf78e30f07c70fc7

def z3 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f007f80ff8d 0x9fbf03f007f80ff8

def z4 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb012533983ff1fff 0xfb012533983ff1ff

def z5 : W := mkw 0x42514b0d80850990 0x442514b0d8085099 0x0871cf0f838f0381 0x50871cf0f838f038

def z6 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacce624ce3f7 0xf7c6dacce624ce3f

def z7 : W := mkw 0x010b40a500000000 0x0010b40a50000000 0xa41fd3ff80000003 0xfa41fd3ff8000000

def z8 : W := mkw 0x837fc04a7b6e20df 0x2837fc04a7b6e20d 0xe7ffc0ce7fff007e 0x7e7ffc0ce7fff007

def z9 : W := mkw 0x43fffbbdfbff0dbf 0x443fffbbdfbff0db 0xffffffffffff1fff 0xfffffffffffff1ff

def z10 : W := mkw 0x0271c000530a000b 0x00271c000530a000 0x0071c000038f0000 0x50071c000038f000

def z11 : W := mkw 0x048030f00410b460 0x3048030f00410b46 0x140030f00000fc72 0x8140030f00000fc7

def z12 : W := mkw 0x010b40a500000000 0x0010b40a50000000 0x040fc0ff80000002 0x6040fc0ff8000000

def z13 : W := mkw 0x048430502c70b464 0x3048430502c70b46 0xf38030007c70fc7c 0x8f38030007c70fc7

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c6dacce00000003 0xf6c6dacce0000000

def z15 : W := mkw 0x4000011880950db0 0x44000011880950db 0xfc7fffff83ff1fff 0xffc7fffff83ff1ff

def z16 : W := mkw 0x4080311884959db0 0x44080311884959db 0xf3927339ffffffff 0xff3927339fffffff

def z17 : W := mkw 0x0080310004809900 0x4008031000480990 0xf39033007f80ff8d 0x9f39033007f80ff8

def z18 : W := mkw 0x850e80fa287c24f6 0x3850e80fa287c24f 0x040f80fe007c0072 0x6040f80fe007c007

def z19 : W := mkw 0x4ad03b1095919d28 0x44ad03b1095919d2 0x839253319db31c08 0x0839253319db31c0

def z20 : W := mkw 0x42700118d3950db8 0x442700118d3950db 0xf3f25339ffff1fff 0xff3f25339ffff1ff

def z21 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43ed80007fff000c 0x043ed80007fff000

def z22 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x578c20c07c70fc7c 0x0578c20c07c70fc7

def z23 : W := mkw 0x03db7aa504009000 0x003db7aa50400900 0xfffffffffc00fc0f 0xffffffffffc00fc0

def z24 : W := mkw 0x010a000008200004 0x0010a00000820000 0x838200001c300008 0x0838200001c30000

def z25 : W := mkw 0x0ef43f507ff0ff6c 0xf0ef43f507ff0ff6 0xfbf03f007ff0fffd 0x9fbf03f007ff0fff

def z26 : W := mkw 0x458a31b88cb59db4 0x5458a31b88cb59db 0xb39253399fff1fff 0xfb39253399fff1ff

def z27 : W := mkw 0x02d03a0004009000 0x002d03a000400900 0xfbf03f007c00fc0d 0x9fbf03f007c00fc0

def z28 : W := mkw 0x8024844262486242 0xa802484426248624 0x000000006000e000 0x0000000006000e00

def z29 : W := mkw 0x00248008624c0092 0x000248008624c009 0x706d8008624c03f7 0xf706d8008624c03f

def z30 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffecc600000000 0x7efffecc60000000

def z31 : W := mkw 0x07db7ab50c309424 0x107db7ab50c30942 0x839253319c301c08 0x0839253319c301c0

def z32 : W := mkw 0x82f4be4a624c62d2 0xa82f4be4a624c62d 0xfffdbfce624ce3f7 0xffffdbfce624ce3f

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x8012533180000000 0x0801253318000000

def z34 : W := mkw 0xc024855ae2dd6ff2 0xec024855ae2dd6ff 0x1000000063fffffc 0x01000000063fffff

def z35 : W := mkw 0x0a7005005780db08 0xc0a7005005780db0 0xf3f000007f80ff8c 0x1f3f000007f80ff8

def z36 : W := mkw 0x0080300004009000 0x0008030000400900 0x100030000000fc00 0x8100030000000fc0

def z37 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x578c30f07c00fc72 0x8578c30f07c00fc7

def z38 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x8392533180000000 0x0839253318000000

def z39 : W := mkw 0x837fc44a7b6e62df 0xa837fc44a7b6e62d 0xffffecce7fffe3ff 0xfffffecce7fffe3f

def z40 : W := mkw 0x837fc4427b6a624f 0xa837fc4427b6a624 0x4fedacc67c00e000 0x04fedacc67c00e00

def z41 : W := mkw 0x0a714f0553804b08 0xc0a714f0553804b0 0x0871cf0f83800381 0x50871cf0f8380038

def z42 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x938210307c70fc7c 0x0938210307c70fc7

def z43 : W := mkw 0x4000011080910d20 0x44000011080910d2 0xb012533181f31c7e 0xab012533181f31c7

def z44 : W := mkw 0x010e000028600004 0x0010e00002860000 0xe38e00007c70000c 0x2e38e00007c70000

def z45 : W := mkw 0x040400502c70b464 0x3040400502c70b46 0x100000007c70fc7c 0x0100000007c70fc7

def z46 : W := mkw 0x03fbfaa5530a000b 0x003fbfaa5530a000 0xefffffff838f0003 0xfefffffff838f000

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0xa01000000380000c 0x1a01000000380000

def z48 : W := mkw 0x4bffff18ffffdfbf 0xc4bffff18ffffdfb 0xfbffff39ffffffff 0xffbffff39fffffff

def z49 : W := mkw 0x8bffffef77ccfbda 0xe8bffffef77ccfbd 0xffffffffffccffff 0xfffffffffffccfff

def z50 : W := mkw 0x43db7bb580910d20 0x443db7bb580910d2 0x8392533181b31c08 0x08392533181b31c0

def z51 : W := mkw 0x07df7af52c70b464 0x307df7af52c70b46 0xf79e73f1fc70fc7e 0xaf79e73f1fc70fc7

def z52 : W := mkw 0x058a30b00c309424 0x1058a30b00c30942 0x838210301c301c08 0x0838210301c301c0

def z53 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1000000000001ff0 0x01000000000001ff

def z54 : W := mkw 0x0bffff007feadb0f 0xc0bffff007feadb0 0xfbffff007fffff8d 0xffbffff007fffff8

def z55 : W := mkw 0x4af03f18d795dfb8 0xc4af03f18d795dfb 0xfbf27f39ffffffff 0xffbf27f39fffffff

def z56 : W := mkw 0x0004800020480002 0x0000480002048000 0x000d8000004c0000 0x6000d8000004c000

def z57 : W := mkw 0x0000001000100420 0x0000000100010042 0xb012533980701c7f 0xfb012533980701c7

def z58 : W := mkw 0x43db7bbd80950db0 0x443db7bbd80950db 0xffffffff83ff1fff 0xfffffffff83ff1ff

def z59 : W := mkw 0xc024855ae2dd6ff2 0xec024855ae2dd6ff 0xfc7fffffe3ffffff 0xffc7fffffe3fffff

def z60 : W := mkw 0x027480007b6a000f 0x0027480007b6a000 0xe3f000007fff000c 0x1e3f000007fff000

def z61 : W := mkw 0x010b40a500000000 0x0010b40a50000000 0x040d80c600000000 0x0040d80c60000000

def z62 : W := mkw 0x4000011080910d20 0x44000011080910d2 0x0000000001b31c08 0x00000000001b31c0

def z63 : W := mkw 0x037fc00062480002 0x0037fc0006248000 0xe3ffc000624c0004 0x7e3ffc000624c000

def z64 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xcbf03f007d80fc08 0x0cbf03f007d80fc0

def z65 : W := mkw 0x07fff0f07f7ab46f 0x307fff0f07f7ab46 0xf7fff0f07ffffc7e 0xff7fff0f07ffffc7

def z66 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43ed80007c000000 0x043ed80007c00000

def z67 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf27f007fffff8d 0xffbf27f007fffff8

def z68 : W := mkw 0x03fffaa562480002 0x003fffaa56248000 0xefffffffe24c0007 0xfefffffffe24c000

def z69 : W := mkw 0x0bfb7fa55780db08 0xc0bfb7fa55780db0 0xfffdbfc67f80ff8d 0x9fffdbfc67f80ff8

def z70 : W := mkw 0x0000001000100420 0x0000000100010042 0xb002103000701c7e 0xab002103000701c7

def z71 : W := mkw 0x058e30e02c60b044 0x3058e30e02c60b04 0x478c20c07c00e000 0x0478c20c07c00e00

def z72 : W := mkw 0x0020040042004200 0x8002004004200420 0x78602c006200e385 0x978602c006200e38

def z73 : W := mkw 0x8af4bf4a77ccfbda 0xe8af4bf4a77ccfbd 0xfffdbfce7fccffff 0xffffdbfce7fccfff

def z74 : W := mkw 0x058a30b00c309424 0x1058a30b00c30942 0xb38210301c701c7e 0xab38210301c701c7

def z75 : W := mkw 0x0080300004009000 0x0008030000400900 0xf38030007c00fc0c 0x8f38030007c00fc0

def z76 : W := mkw 0x08803f000480db00 0xc08803f000480db0 0x18003f000000ff81 0x818003f000000ff8

def z77 : W := mkw 0x4000011880950db0 0x44000011880950db 0x30001339824c1ff7 0xf30001339824c1ff

def z78 : W := mkw 0x0020040042004200 0x8002004004200420 0x7c6dacce6200e387 0xf7c6dacce6200e38

def z79 : W := mkw 0x0a700f0053804b08 0xc0a700f0053804b0 0x08700f0003800381 0x108700f000380038

def z80 : W := mkw 0x0ffe3ff07ff0ff6c 0xf0ffe3ff07ff0ff6 0xfffe3ff07ff0ffff 0xbfffe3ff07ff0fff

def z81 : W := mkw 0x0080301004109420 0x0008030100410942 0xf38230307c70fc7e 0xaf38230307c70fc7

def z82 : W := mkw 0x0af1ff00578adb0b 0xc0af1ff00578adb0 0xfbf1ff007f8fff8d 0xdfbf1ff007f8fff8

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0xa012400003ff000c 0x7a012400003ff000

def z84 : W := mkw 0x0270000053000008 0x0027000005300000 0xe3f000007f80000c 0x1e3f000007f80000

def z85 : W := mkw 0x437fc118fbff0dbf 0x4437fc118fbff0db 0xf3ffd339ffff1fff 0xff3ffd339ffff1ff

def z86 : W := mkw 0x03db7aa51922000d 0x003db7aa51922000 0xefffffff9db3000b 0xfefffffff9db3000

def z87 : W := mkw 0x8af03f4a5784fbd8 0xe8af03f4a5784fbd 0xfff03fce7f80ffff 0x9fff03fce7f80fff

def z88 : W := mkw 0x448031f88495bdf0 0x7448031f88495bdf 0x140033f98000fff3 0x8140033f98000fff

def z89 : W := mkw 0x8020044a420462d0 0xa8020044a420462d 0x7c602cce6200e3f7 0x97c602cce6200e3f

def z90 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x839240007fff000c 0x0839240007fff000

def z91 : W := mkw 0x037fc1007bea090f 0x4037fc1007bea090 0xf3ffd3007fff1f8d 0xff3ffd3007fff1f8

def z92 : W := mkw 0x8024844a7b6e62df 0xa8024844a7b6e62d 0x100000007fffe3fc 0x0100000007fffe3f

def z93 : W := mkw 0x8024844262486242 0xa802484426248624 0x6c6dacce6000e003 0xf6c6dacce6000e00

def z94 : W := mkw 0x02514a0500000000 0x002514a050000000 0x0871cf0f80000001 0x50871cf0f8000000

def z95 : W := mkw 0x02d03a0000000000 0x002d03a000000000 0x8390130000000000 0x0839013000000000

def z96 : W := mkw 0x8020840a420c4292 0x88020840a420c429 0x08618c0e020c0381 0x508618c0e020c038

def z97 : W := mkw 0x458e31f8acf5bdf4 0x7458e31f8acf5bdf 0xf79e73f9ffffffff 0xff79e73f9fffffff

def z98 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacce6000e3f3 0x85c6dacce6000e3f

def z99 : W := mkw 0x0ad03b0015809908 0x40ad03b001580990 0xebf03f001d801c09 0x9ebf03f001d801c0

def z100 : W := mkw 0x02d03a0000000000 0x002d03a000000000 0xebf03f0000000001 0x9ebf03f000000000

def z101 : W := mkw 0x082005005780db08 0xc082005005780db0 0x100000007f80ff8c 0x0100000007f80ff8

def z102 : W := mkw 0x00040048204420d0 0x200040048204420d 0x740c20c8624ce3f7 0xf740c20c8624ce3f

def z103 : W := mkw 0x4000011080910d20 0x44000011080910d2 0x8012533181b31c08 0x08012533181b31c0

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0xa012533983ff000f 0xfa012533983ff000

def z105 : W := mkw 0x8020844a420c62d2 0xa8020844a420c62d 0x1c61acce020ce3f3 0xd1c61acce020ce3f

def z106 : W := mkw 0x0251400011020009 0x0025140001102000 0x0010400001830000 0x0001040000183000

def z107 : W := mkw 0x035b40001922000d 0x0035b40001922000 0x839240001db30008 0x0839240001db3000

def z108 : W := mkw 0x8000044a000462d0 0xa8000044a000462d 0x1c002cce0000e3f3 0x81c002cce0000e3f

def z109 : W := mkw 0x0af03b0057809908 0x40af03b005780990 0xe3f013007f801c0c 0x1e3f013007f801c0

def z110 : W := mkw 0x8424845a6e7cf6f6 0xb8424845a6e7cf6f 0x7c6dacce7e7cffff 0xf7c6dacce7e7cfff

def z111 : W := mkw 0x0fde3bf03df0bd6c 0x70fde3bf03df0bd6 0xf79e33f07df0fc7e 0xaf79e33f07df0fc7

def z112 : W := mkw 0x058a30f00410b460 0x3058a30f00410b46 0xf78e30f00000fc72 0xaf78e30f00000fc7

def z113 : W := mkw 0x4000010880850990 0x4400001088085099 0x00104309838f0381 0x500104309838f038

def z114 : W := mkw 0x8020840242084202 0x8802084024208420 0x08618c0600000000 0x008618c060000000

def z115 : W := mkw 0x010a00a000000000 0x0010a00a00000000 0x040e00f000000002 0x2040e00f00000000

def z116 : W := mkw 0x48200518d795dfb8 0xc48200518d795dfb 0xb0125339ffffffff 0xfb0125339fffffff

def z117 : W := mkw 0x010e000028600004 0x0010e00002860000 0xe39e40007fff000c 0x7e39e40007fff000

def z118 : W := mkw 0x0024800062480002 0x0002480006248000 0x6c6dacce624c0007 0xf6c6dacce624c000

def z119 : W := mkw 0x08a035005780db08 0xc08a035005780db0 0xf38030007f80ff8c 0x8f38030007f80ff8

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000133980000003 0x8000013398000000

def z121 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010130000000001 0x9a01013000000000

def z122 : W := mkw 0x02d17a0500000000 0x002d17a050000000 0xebf1ff0f80000001 0xdebf1ff0f8000000

def z123 : W := mkw 0x0004004020402040 0x2000400402040204 0x7c6dacce6040e077 0xf7c6dacce6040e07

def z124 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x5be02c007f80ff8c 0x05be02c007f80ff8

def z125 : W := mkw 0x80803eef000462d0 0xa80803eef000462d 0x1c003fff8000e3f3 0x81c003fff8000e3f

def z126 : W := mkw 0x8000044a000462d0 0xa8000044a000462d 0x7c6dacce0000e3f3 0xf7c6dacce0000e3f

def z127 : W := mkw 0x0bdb7b001da2990d 0x40bdb7b001da2990 0x839253001db31c08 0x0839253001db31c0

def z128 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffc0007c000000 0x7e3ffc0007c00000

def z129 : W := mkw 0x8a748f4a73cc6bda 0xe8a748f4a73cc6bd 0x7c7dafce63cce3f7 0xf7c7dafce63cce3f

def z130 : W := mkw 0x0af03e005700d208 0x80af03e005700d20 0x7be02c007e00e385 0x97be02c007e00e38

def z131 : W := mkw 0x435b411880950db0 0x4435b411880950db 0xf3ffd33983ff1fff 0xff3ffd33983ff1ff

def z132 : W := mkw 0x037fc0a57b6a000f 0x0037fc0a57b6a000 0xe7ffc0ffffff000e 0x7e7ffc0ffffff000

def z133 : W := mkw 0x83fffeef624c62d2 0xa83fffeef624c62d 0xffffffffe24ce3f7 0xfffffffffe24ce3f

def z134 : W := mkw 0x43db7bad80850990 0x443db7bad8085099 0xefffffff838f0383 0xfefffffff838f038

def z135 : W := mkw 0x0004000028600004 0x0000400002860000 0x000000007c70000c 0x0000000007c70000

def z136 : W := mkw 0x4000010880850990 0x4400001088085099 0x0000030980000381 0x0000003098000038

def z137 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e70f07ffffc7e 0xff79e70f07ffffc7

def z138 : W := mkw 0xc000055a80956ff0 0xec000055a80956ff 0xbc127fff83ffffff 0xfbc127fff83fffff

def z139 : W := mkw 0xc024855ae2dd6ff2 0xec024855ae2dd6ff 0x7c6dacce63ffffff 0xf7c6dacce63fffff

def z140 : W := mkw 0x050a00b008300424 0x1050a00b00830042 0x0002003000300000 0x0000200300030000

def z141 : W := mkw 0x018e30a028600004 0x0018e30a02860000 0xe78e30f07c70000e 0xae78e30f07c70000

def z142 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x8bf3df3f80000001 0x58bf3df3f8000000

def z143 : W := mkw 0x8024844262486242 0xa802484426248624 0x4c6dacc66000e000 0x04c6dacc66000e00

def z144 : W := mkw 0x43db7bbd80950db0 0x443db7bbd80950db 0xffffffff80001ff3 0xfffffffff80001ff

def z145 : W := mkw 0x0af03e005700d208 0x80af03e005700d20 0x4be02c007c00e000 0x04be02c007c00e00

def z146 : W := mkw 0x0bfb7fa55780db08 0xc0bfb7fa55780db0 0xffffffffff80ff8f 0xfffffffffff80ff8

def z147 : W := mkw 0x0000000000000000 0x0000000000000000 0xa012533980000003 0xfa01253398000000

def z148 : W := mkw 0x810fc0ef204c20d2 0x2810fc0ef204c20d 0x040fc0ff804c0072 0x6040fc0ff804c007

def z149 : W := mkw 0x8af0bf0a578cdb9a 0xc8af0bf0a578cdb9 0xfbf1bf0e7f8cff8d 0xdfbf1bf0e7f8cff8

def z150 : W := mkw 0x010b40a500000000 0x0010b40a50000000 0x6c6fecff80000003 0xf6c6fecff8000000

def z151 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xc78e30f07c30fc08 0x0c78e30f07c30fc0

def z152 : W := mkw 0x03fffaa57b6a000f 0x003fffaa57b6a000 0xefffffffffff000f 0xfefffffffffff000

def z153 : W := mkw 0x050e00f028702464 0x3050e00f02870246 0x040e00f000700072 0x2040e00f00070007

def z154 : W := mkw 0x002480007b6a000f 0x0002480007b6a000 0x000000007fff000c 0x0000000007fff000

def z155 : W := mkw 0x00803aa500000000 0x000803aa50000000 0x0c003fff80000003 0x80c003fff8000000

def z156 : W := mkw 0x05aeb0f06e78b466 0x305aeb0f06e78b46 0xf7efb0f07e7cfc7e 0xff7efb0f07e7cfc7

def z157 : W := mkw 0x07df7af52c70b464 0x307df7af52c70b46 0xfffffffffc70fc7f 0xffffffffffc70fc7

def z158 : W := mkw 0x0000000004009000 0x0000000000400900 0x100000007c00fc0c 0x0100000007c00fc0

def z159 : W := mkw 0x0000000800040090 0x0000000080004009 0xb0125339824c03f7 0xfb0125339824c03f

def z160 : W := mkw 0x812fc4ef624c62d2 0xa812fc4ef624c62d 0x7c6fecffe24ce3f7 0xf7c6fecffe24ce3f

def z161 : W := mkw 0x8004804a204c20d2 0x28004804a204c20d 0x040d80ce004c0072 0x6040d80ce004c007

def z162 : W := mkw 0x4af03f10d791df28 0xc4af03f10d791df2 0xfbf27f31ffb3ff8d 0x9fbf27f31ffb3ff8

def z163 : W := mkw 0x03db70a000000000 0x003db70a00000000 0xe7fff0f000000002 0xfe7fff0f00000000

def z164 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x10000000624ce3f4 0x010000000624ce3f

def z165 : W := mkw 0x0000010000800900 0x4000001000080090 0x8010130001801c08 0x08010130001801c0

def z166 : W := mkw 0x8824854a77ccfbda 0xe8824854a77ccfbd 0x100000007fccfffc 0x0100000007fccfff

def z167 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x0380000000000000 0x0038000000000000

def z168 : W := mkw 0x80a4b44a664cf2d2 0xa80a4b44a664cf2d 0xffedbcce7e4cffff 0xfffedbcce7e4cfff

def z169 : W := mkw 0x450e00f8a87524f4 0x3450e00f8a87524f 0x040e40f9807f0072 0x6040e40f9807f007

def z170 : W := mkw 0x050e00f028702464 0x3050e00f02870246 0xb40e10f000701c7e 0xab40e10f000701c7

def z171 : W := mkw 0x035b400000000000 0x0035b40000000000 0xe3ffc00000000000 0x7e3ffc0000000000

def z172 : W := mkw 0x012e80006a680006 0x0012e80006a68000 0xe3ef80007e7c000c 0x7e3ef80007e7c000

def z173 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xe79e73f180000002 0xae79e73f18000000

def z174 : W := mkw 0x8024844a7b6e62df 0xa8024844a7b6e62d 0x7c6dacce7fffe3ff 0xf7c6dacce7fffe3f

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0xe38000007c00000c 0x0e38000007c00000

def z176 : W := mkw 0x8275c44a734e62db 0xa8275c44a734e62d 0x7c7decce63cfe3f7 0xf7c7decce63cfe3f

def z177 : W := mkw 0x050f40f528702464 0x3050f40f52870246 0x040fc0ff80700072 0x6040fc0ff8070007

def z178 : W := mkw 0x4000011880950db0 0x44000011880950db 0x9012533981b31ffb 0x89012533981b31ff

def z179 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4fedacc600000000 0x04fedacc60000000

def z180 : W := mkw 0x8000800a000c0092 0x08000800a000c009 0x0001800e000c0000 0x40001800e000c000

def z181 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1000000003ff1ffc 0x01000000003ff1ff

def z182 : W := mkw 0x4af03f18d795dfb8 0xc4af03f18d795dfb 0xfbf03f007ffffffd 0x9fbf03f007ffffff

def z183 : W := mkw 0x0af03e005700d208 0x80af03e005700d20 0xebf02c007f80e00c 0x1ebf02c007f80e00

def z184 : W := mkw 0x410b41bd80950db0 0x4410b41bd80950db 0xb41fd3ff83ff1fff 0xfb41fd3ff83ff1ff

def z185 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb010130003ff1ffd 0x9b010130003ff1ff

def z186 : W := mkw 0x037fca057b6a000f 0x0037fca057b6a000 0xebffcf0fffff000d 0x7ebffcf0fffff000

def z187 : W := mkw 0x0bfb7fa553804b08 0xc0bfb7fa553804b0 0xefffffff83800383 0xfefffffff8380038

def z188 : W := mkw 0xc024854ae2cd6bd2 0xec024854ae2cd6bd 0x7c7defcfe3cfe3f7 0xf7c7defcfe3cfe3f

def z189 : W := mkw 0x0024800062480002 0x0002480006248000 0x606d8000624c0004 0x7606d8000624c000

def z190 : W := mkw 0x07de3af02c70b464 0x307de3af02c70b46 0xfffe3ff07c70fc7f 0xbfffe3ff07c70fc7

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000000400076 0xa300000000040007

def z192 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff83ff000f 0xfefffffff83ff000

def z193 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x939013007f80ff8c 0x0939013007f80ff8

def z194 : W := mkw 0x48803f188495dfb0 0xc48803f188495dfb 0x18003f398000fff3 0x818003f398000fff

def z195 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1000133980001ff3 0x81000133980001ff

def z196 : W := mkw 0x018b7aa500000000 0x0018b7aa50000000 0x0c0fffff80000003 0xe0c0fffff8000000

def z197 : W := mkw 0x0af17f055780db08 0xc0af17f055780db0 0xfbf1ff0fff80ff8d 0xdfbf1ff0fff80ff8

def z198 : W := mkw 0x0020040042004200 0x8002004004200420 0x08600c0002000381 0x108600c000200038

def z199 : W := mkw 0x000000001922000d 0x0000000001922000 0x000000001db30008 0x0000000001db3000

def z200 : W := mkw 0x8024840a624c4292 0x88024840a624c429 0x686d8c0e624c0385 0x7686d8c0e624c038

def z201 : W := mkw 0x010fc000286a0007 0x0010fc000286a000 0x000fc000007f0000 0x6000fc000007f000

def z202 : W := mkw 0x0bdb7ba515809908 0x40bdb7ba51580990 0x839253319d801c08 0x0839253319d801c0

def z203 : W := mkw 0x08803f000480db00 0xc08803f000480db0 0xfb803f007c00ff8d 0x8fb803f007c00ff8

def z204 : W := mkw 0x018e30002c609004 0x0018e30002c60900 0xf38e30007c70fc0c 0xaf38e30007c70fc0

def z205 : W := mkw 0x4271c108d38f099b 0x44271c108d38f099 0x0071c309838f0381 0x50071c309838f038

def z206 : W := mkw 0x02d03a0000000000 0x002d03a000000000 0x4be02c0000000000 0x04be02c000000000

def z207 : W := mkw 0x458e30f8ac75b4f4 0x3458e30f8ac75b4f 0xf78e70f9fc7ffc7e 0xef78e70f9fc7ffc7

def z208 : W := mkw 0x037b40005b22000d 0x0037b40005b22000 0xe3f240007fb3000c 0x1e3f240007fb3000

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z210 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4fedbfff80000003 0x84fedbfff8000000

def z211 : W := mkw 0x0004004020402040 0x2000400402040204 0x740c20c06040e076 0xa740c20c06040e07

def z212 : W := mkw 0x85aeb4fa6e7cf6f6 0xb85aeb4fa6e7cf6f 0xffefbcfe7e7cffff 0xfffefbcfe7e7cfff

def z213 : W := mkw 0xc024845ae25d66f2 0xac024845ae25d66f 0x7c6fecffe27fe3f7 0xf7c6fecffe27fe3f

def z214 : W := mkw 0x018a30a000000000 0x0018a30a00000000 0xe78e30f000000002 0xae78e30f00000000

def z215 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4ffdefcf80000001 0x54ffdefcf8000000

def z216 : W := mkw 0x852e84fa6a7c66f6 0xb852e84fa6a7c66f 0x7c6facfe627ce3f7 0xf7c6facfe627ce3f

def z217 : W := mkw 0x058e30e02c60b044 0x3058e30e02c60b04 0xf78c30c07c00fc0c 0x8f78c30c07c00fc0

def z218 : W := mkw 0x0001400500000000 0x0000140050000000 0x0001c00f80000000 0x40001c00f8000000

def z219 : W := mkw 0x0275c000734a000b 0x00275c000734a000 0x607dc00063cf0004 0x7607dc00063cf000

def z220 : W := mkw 0x08000f0000804b00 0xc08000f0000804b0 0x08000f0000000381 0x008000f000000038

def z221 : W := mkw 0x448031f88495bdf0 0x7448031f88495bdf 0xb41273f983ffffff 0xfb41273f983fffff

def z222 : W := mkw 0x018b70a500000000 0x0018b70a50000000 0xe78ff0ff80000002 0xee78ff0ff8000000

def z223 : W := mkw 0x0020040042004200 0x8002004004200420 0x48602c006000e000 0x048602c006000e00

def z224 : W := mkw 0x0bfffe007f6ad20f 0x80bfffe007f6ad20 0x4bedac007c00e000 0x04bedac007c00e00

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x68602c0000000001 0x968602c000000000

def z226 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf27f39ff80ff8f 0xffbf27f39ff80ff8

def z227 : W := mkw 0x40000018801504b0 0x040000018801504b 0x00024039807f0072 0x600024039807f007

def z228 : W := mkw 0x0a700e0053004208 0x80a700e005300420 0x08600c0000000000 0x008600c000000000

def z229 : W := mkw 0x458e31f8acf5bdf4 0x7458e31f8acf5bdf 0xf78e30f07ffffffe 0xaf78e30f07ffffff

def z230 : W := mkw 0x8824854a77ccfbda 0xe8824854a77ccfbd 0x7c6dacce7fccffff 0xf7c6dacce7fccfff

def z231 : W := mkw 0x0004004020402040 0x2000400402040204 0x440c20c06000e000 0x0440c20c06000e00

def z232 : W := mkw 0x037bc0005b2a000f 0x0037bc0005b2a000 0x83f3c0001fbf0008 0x583f3c0001fbf000

def z233 : W := mkw 0x8000040a00044290 0x88000040a0004429 0x08000c0e00000381 0x008000c0e0000038

def z234 : W := mkw 0x035b4a0500000000 0x0035b4a050000000 0xebffcf0f80000001 0x7ebffcf0f8000000

def z235 : W := mkw 0x4000011880950db0 0x44000011880950db 0x3000000803ff1fff 0xf3000000803ff1ff

def z236 : W := mkw 0x02500a0000000000 0x002500a000000000 0x08700f0000000001 0x108700f000000000

def z237 : W := mkw 0x837fc44a624c62d2 0xa837fc44a624c62d 0xffffecce624ce3f7 0xfffffecce624ce3f

def z238 : W := mkw 0x035f40003962000d 0x0035f40003962000 0xe39e40007df3000c 0x2e39e40007df3000

def z239 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x140d80ce624ce3f6 0x6140d80ce624ce3f

def z240 : W := mkw 0x8004804a204c20d2 0x28004804a204c20d 0x740da0ce604ce076 0xe740da0ce604ce07

def z241 : W := mkw 0x050e00502c70b464 0x3050e00502c70b46 0xf38e00007c70fc7c 0x2f38e00007c70fc7

def z242 : W := mkw 0x0000010800840990 0x4000001080084099 0xb010130803cc1fff 0xfb010130803cc1ff

def z243 : W := mkw 0x07fff0e07f6ab04f 0x307fff0e07f6ab04 0x47eda0c07c00e000 0x047eda0c07c00e00

def z244 : W := mkw 0x42d03b1880950db0 0x442d03b1880950db 0xfbf27f3983ff1fff 0xffbf27f3983ff1ff

def z245 : W := mkw 0x0bfffe007f6ad20f 0x80bfffe007f6ad20 0xebffec007fffe00c 0x7ebffec007fffe00

def z246 : W := mkw 0x0c2405507ff0ff6c 0xf0c2405507ff0ff6 0x100000007ff0fffc 0x0100000007ff0fff

def z247 : W := mkw 0x4ffe3ff8fff5fffc 0xf4ffe3ff8fff5fff 0xfffe7ff9ffffffff 0xffffe7ff9fffffff

def z248 : W := mkw 0x0af03f085784db98 0xc0af03f085784db9 0xfbf03f087fccffff 0xffbf03f087fccfff

def z249 : W := mkw 0x0004005020502460 0x2000400502050246 0xf40e30f06070fc7e 0xaf40e30f06070fc7

def z250 : W := mkw 0x048030f00410b460 0x3048030f00410b46 0xf78030f07c00fc7e 0x8f78030f07c00fc7

def z251 : W := mkw 0x035b400000000000 0x0035b40000000000 0xe3ffc00003ff000c 0x7e3ffc00003ff000

def z252 : W := mkw 0x0000001000100420 0x0000000100010042 0x0002003000700072 0x2000200300070007

def z253 : W := mkw 0x05ae34f06e70f664 0xb05ae34f06e70f66 0xffee3cf07e70ffff 0xbffee3cf07e70fff

def z254 : W := mkw 0xc004815aa0dd2df2 0x6c004815aa0dd2df 0xb41fd3ff83ff1fff 0xfb41fd3ff83ff1ff

def z255 : W := mkw 0x0250000000000000 0x0025000000000000 0xe3f0000000000000 0x1e3f000000000000

def z256 : W := mkw 0x0271c000530a000b 0x00271c000530a000 0xa073c00003ff000c 0x7a073c00003ff000

def z257 : W := mkw 0x83fffeef624c62d2 0xa83fffeef624c62d 0x7fedacce624ce3f7 0xf7fedacce624ce3f

def z258 : W := mkw 0x8271ce0f420c4292 0x88271ce0f420c429 0x0871cf0f820c0381 0x50871cf0f820c038

def z259 : W := mkw 0x8004804a204c20d2 0x28004804a204c20d 0x340d80ce024c03f7 0xf340d80ce024c03f

def z260 : W := mkw 0x037fc4007b6a420f 0x8037fc4007b6a420 0xfbffec007fffe38d 0xffbffec007fffe38

def z261 : W := mkw 0x00803a0000000000 0x000803a000000000 0x08003f0000000001 0x808003f000000000

def z262 : W := mkw 0x00803aa500000000 0x000803aa50000000 0x6c6dbfff80000003 0xf6c6dbfff8000000

def z263 : W := mkw 0x00a034004600d200 0x800a034004600d20 0xfbe03c007e00ff8d 0x9fbe03c007e00ff8

def z264 : W := mkw 0x035b400000000000 0x0035b40000000000 0x43ed800000000000 0x043ed80000000000

def z265 : W := mkw 0x44040158acf5bdf4 0x744040158acf5bdf 0xb0125339ffffffff 0xfb0125339fffffff

def z266 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffd339ffff000f 0xfe3ffd339ffff000

def z267 : W := mkw 0x8020840a420c4292 0x88020840a420c429 0x7861ac0e620ce385 0xd7861ac0e620ce38

def z268 : W := mkw 0x07df7ae52c60b044 0x307df7ae52c60b04 0xeffffffffc00e003 0xfeffffffffc00e00

def z269 : W := mkw 0x0271c000530a000b 0x00271c000530a000 0x0061800000000000 0x0006180000000000

def z270 : W := mkw 0x8000044a000462d0 0xa8000044a000462d 0x3c002cce024ce3f7 0xf3c002cce024ce3f

def z271 : W := mkw 0x035b4aa500000000 0x0035b4aa50000000 0x0c7fcfff80000003 0x70c7fcfff8000000

def z272 : W := mkw 0x8024844262486242 0xa802484426248624 0x6c6dacc6624ce004 0x76c6dacc6624ce00

def z273 : W := mkw 0x0000010000800900 0x4000001000080090 0x0010030003800381 0x1001003000380038

def z274 : W := mkw 0x0bdb7fa50480db00 0xc0bdb7fa50480db0 0xffffffff8000ff83 0xfffffffff8000ff8

def z275 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfffdbfce7f80ff8f 0xffffdbfce7f80ff8

def z276 : W := mkw 0x008430402440b040 0x2008430402440b04 0xf78c30c07c40fc7e 0xaf78c30c07c40fc7

def z277 : W := mkw 0x435b411899b70dbd 0x4435b411899b70db 0xb39253399fff1fff 0xfb39253399fff1ff

def z278 : W := mkw 0x0af43f4077c0fb48 0xe0af43f4077c0fb4 0xfffc3fc07fc0ffff 0xbfffc3fc07fc0fff

def z279 : W := mkw 0x0000040000004200 0x8000004000000420 0x18002c000000e381 0x818002c000000e38

def z280 : W := mkw 0x058e30f82c74b4f4 0x3058e30f82c74b4f 0xf78e30f87e7cffff 0xff78e30f87e7cfff

def z281 : W := mkw 0x437fc110fbfb0d2f 0x4437fc110fbfb0d2 0xe3ffd331ffff1c0c 0x7e3ffd331ffff1c0

def z282 : W := mkw 0x40803bbd80950db0 0x440803bbd80950db 0xbc127fff83ff1fff 0xfbc127fff83ff1ff

def z283 : W := mkw 0x048030f00410b460 0x3048030f00410b46 0xb40230f00070fc7e 0xab40230f00070fc7

def z284 : W := mkw 0x0af03f105790df28 0xc0af03f105790df2 0xfbf23f307ff0ffff 0xbfbf23f307ff0fff

def z285 : W := mkw 0x0bfb7ea55700d208 0x80bfb7ea55700d20 0xeffffffffc00e003 0xfeffffffffc00e00

def z286 : W := mkw 0x0000000800040090 0x0000000080004009 0x30000008024c03f7 0xf30000008024c03f

def z287 : W := mkw 0x0080300000000000 0x0008030000000000 0xe380300000000000 0x8e38030000000000

def z288 : W := mkw 0x035b40001922000d 0x0035b40001922000 0xa39240001fff000c 0x7a39240001fff000

def z289 : W := mkw 0x040000500410b460 0x3040000500410b46 0x100000000000fc70 0x0100000000000fc7

def z290 : W := mkw 0x8004044a204462d0 0xa8004044a204462d 0x7c0c2cce6040e3f7 0xa7c0c2cce6040e3f

def z291 : W := mkw 0x002480007b6a000f 0x0002480007b6a000 0x606d80007fff000c 0x7606d80007fff000

def z292 : W := mkw 0x037fc0407b6a204f 0x2037fc0407b6a204 0xf7ffe0c07fffe07e 0xff7ffe0c07fffe07

def z293 : W := mkw 0x458a31b08cb19d24 0x5458a31b08cb19d2 0x839253319db31c08 0x0839253319db31c0

def z294 : W := mkw 0x0020040842044290 0x8002004084204429 0x78602c08624ce3f7 0xf78602c08624ce3f

def z295 : W := mkw 0x8004804220482042 0x2800480422048204 0x040d80c600000000 0x0040d80c60000000

def z296 : W := mkw 0x03df7aa528600004 0x003df7aa52860000 0xeffffffffc70000f 0xfeffffffffc70000

def z297 : W := mkw 0x035b40001922000d 0x0035b40001922000 0x038000001c000000 0x0038000001c00000

def z298 : W := mkw 0x0ffe3fe07fe0fb4c 0xf0ffe3fe07fe0fb4 0xfffc3fc07f80ff8d 0x9fffc3fc07f80ff8

def z299 : W := mkw 0x8004844a204c62d2 0xa8004844a204c62d 0x1c0dacce004ce3f3 0xe1c0dacce004ce3f

def z300 : W := mkw 0x48803f188495dfb0 0xc48803f188495dfb 0xb8127f3983ffffff 0xfb8127f3983fffff

def z301 : W := mkw 0x03fffa007b6a000f 0x003fffa007b6a000 0xebffff007fff000d 0xfebffff007fff000

def z302 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacc6624ce3f4 0x05c6dacc6624ce3f

def z303 : W := mkw 0x0000000800040090 0x0000000080004009 0x00000008020c0381 0x500000008020c038

def z304 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb010133983801fff 0x9b010133983801ff

def z305 : W := mkw 0x4000011880950db0 0x44000011880950db 0x9012533183ff1ffc 0x09012533183ff1ff

def z306 : W := mkw 0x4a700f18d3954fb8 0xc4a700f18d3954fb 0xb8725f3983ff1fff 0xfb8725f3983ff1ff

def z307 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xc3ffc0007db30008 0x0c3ffc0007db3000

def z308 : W := mkw 0x4000010080810900 0x4400001008081090 0x0010430181830000 0x0001043018183000

def z309 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xeffdbfc600000001 0x9effdbfc60000000

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x00024000007f0000 0x600024000007f000

def z311 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xefffecce7fff000f 0xfefffecce7fff000

def z312 : W := mkw 0x0250000011000008 0x0025000001100000 0x839000001d800008 0x0839000001d80000

def z313 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43fdc0007f8f0000 0x543fdc0007f8f000

def z314 : W := mkw 0x837fc40a7b6e429f 0x8837fc40a7b6e429 0xebffcc0e7fff038d 0x7ebffcc0e7fff038

def z315 : W := mkw 0x40000018801504b0 0x040000018801504b 0xb0025039807f1c7e 0xeb0025039807f1c7

def z316 : W := mkw 0xcaf4bf5af7ddfffa 0xecaf4bf5af7ddfff 0xffffffffffffffff 0xffffffffffffffff

def z317 : W := mkw 0x0251400000000000 0x0025140000000000 0x0071c00000000000 0x50071c0000000000

def z318 : W := mkw 0x0001c000000a0003 0x00001c000000a000 0x0001c000000f0000 0x40001c000000f000

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x08618c0e00000001 0x508618c0e0000000

def z320 : W := mkw 0x437fc118fbff0dbf 0x4437fc118fbff0db 0xf3ffc0007fff1ffc 0x7f3ffc0007fff1ff

def z321 : W := mkw 0x8ffebffa7ffcfffe 0xf8ffebffa7ffcfff 0xffffbffe7ffcffff 0xfffffbffe7ffcfff

def z322 : W := mkw 0x0a500b0011800908 0x40a500b001180090 0x0010030001800000 0x0001003000180000

def z323 : W := mkw 0x018a30a000000000 0x0018a30a00000000 0xefefbcfe00000003 0xfefefbcfe0000000

def z324 : W := mkw 0x84a4b4fa665cf6f2 0xb84a4b4fa665cf6f 0x7c6dbcfe624cfff7 0xf7c6dbcfe624cfff

def z325 : W := mkw 0x035b400000000000 0x0035b40000000000 0xefffecce00000003 0xfefffecce0000000

def z326 : W := mkw 0x858e34fa2c74f6f4 0xb858e34fa2c74f6f 0xff8e3cfe7c70ffff 0xaff8e3cfe7c70fff

def z327 : W := mkw 0x40248118e2dd0db2 0x440248118e2dd0db 0xf07fd339e3ff1fff 0xff07fd339e3ff1ff

def z328 : W := mkw 0x03fffaa57b6a000f 0x003fffaa57b6a000 0xe3ffd331ffff000c 0x7e3ffd331ffff000

def z329 : W := mkw 0x44040158acf5bdf4 0x744040158acf5bdf 0x100000007ffffffc 0x0100000007ffffff

def z330 : W := mkw 0x035fc000286a0007 0x0035fc000286a000 0xe3ffc000007f0000 0x7e3ffc000007f000

def z331 : W := mkw 0x03fff0007f6a900f 0x003fff0007f6a900 0xf3fff0007ffffc0c 0xff3fff0007ffffc0

def z332 : W := mkw 0x03fb7ea542004200 0x803fb7ea54200420 0xffffffffe200e387 0xfffffffffe200e38

def z333 : W := mkw 0x4000010880850990 0x4400001088085099 0xa0125339838f0383 0xfa0125339838f038

def z334 : W := mkw 0x058e3af52c70b464 0x3058e3af52c70b46 0xff8e3ffffc70fc7f 0xaff8e3ffffc70fc7

def z335 : W := mkw 0x07df7af52c70b464 0x307df7af52c70b46 0xffefbcf67c70fc7e 0xaffefbcf67c70fc7

def z336 : W := mkw 0x0000010000800900 0x4000001000080090 0xb010130003801f8d 0x9b010130003801f8

def z337 : W := mkw 0x40200518c2954fb0 0xc40200518c2954fb 0xf8727f39e3ffffff 0xff8727f39e3fffff

def z338 : W := mkw 0x0ad03f001580db08 0xc0ad03f001580db0 0x9b903f001d80ff89 0x89b903f001d80ff8

def z339 : W := mkw 0x058ff0f02c7ab467 0x3058ff0f02c7ab46 0xf78ff0f07c7ffc7e 0xef78ff0f07c7ffc7

def z340 : W := mkw 0x010fc000286a0007 0x0010fc000286a000 0xa01fc00003ff000c 0x7a01fc00003ff000

def z341 : W := mkw 0x010e000028600004 0x0010e00002860000 0x000e000000700000 0x2000e00000070000

def z342 : W := mkw 0x4000011880950db0 0x44000011880950db 0x10105339838f1ff3 0xd10105339838f1ff

def z343 : W := mkw 0x058e30f028702464 0x3058e30f02870246 0xe78e30f000700072 0xae78e30f00070007

def z344 : W := mkw 0x410b40bd801504b0 0x0410b40bd801504b 0x040fc0ff807f0072 0x6040fc0ff807f007

def z345 : W := mkw 0x07df7af528702464 0x307df7af52870246 0xefffffff80700073 0xfefffffff8070007

def z346 : W := mkw 0x40803bbd80950db0 0x440803bbd80950db 0x1c003fff80001ff3 0x81c003fff80001ff

def z347 : W := mkw 0x02d03a0000000000 0x002d03a000000000 0xebf27f3980000003 0xfebf27f398000000

def z348 : W := mkw 0x458e31f0acf1bd64 0x7458e31f0acf1bd6 0xf79e73f1fdf3fc7e 0xaf79e73f1fdf3fc7

def z349 : W := mkw 0x87fff4fa7f7ef6ff 0xb87fff4fa7f7ef6f 0xfffffcfe7fffffff 0xffffffcfe7ffffff

def z350 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1002403983ff1ffe 0x61002403983ff1ff

def z351 : W := mkw 0x058e31f02cf0bd64 0x7058e31f02cf0bd6 0xf79e33f07ff0ffff 0xbf79e33f07ff0fff

def z352 : W := mkw 0x07fe30f07f70b46c 0x307fe30f07f70b46 0xf7fe30f07ff0fc7e 0xbf7fe30f07ff0fc7

def z353 : W := mkw 0x83fffee762486242 0xa83fffee76248624 0x4fedacc66000e000 0x04fedacc66000e00

def z354 : W := mkw 0x0a700f0053804b08 0xc0a700f0053804b0 0x78702f006380e385 0x978702f006380e38

def z355 : W := mkw 0x010fc000286a0007 0x0010fc000286a000 0x000d800000000000 0x0000d80000000000

def z356 : W := mkw 0x03fb7aa553000008 0x003fb7aa55300000 0xefffffffff80000f 0xfefffffffff80000

def z357 : W := mkw 0x012e80007b6a000f 0x0012e80007b6a000 0xe38e00007fff000c 0x2e38e00007fff000

def z358 : W := mkw 0x40000018801504b0 0x040000018801504b 0xa0125339807f0073 0xfa0125339807f007

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0xb000100000001c0c 0x8b000100000001c0

def z360 : W := mkw 0xc5aeb5faeefdfff6 0xfc5aeb5faeefdfff 0xffffffffffffffff 0xffffffffffffffff

def z361 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xebf27f3180000001 0x9ebf27f318000000

def z362 : W := mkw 0x0ad03b0015809908 0x40ad03b001580990 0xb39013001f801f8d 0x9b39013001f801f8

def z363 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb012533980001ff3 0xfb012533980001ff

def z364 : W := mkw 0x0024840062484202 0x8002484006248420 0x786dac00624ce385 0xf786dac00624ce38

def z365 : W := mkw 0x04803af50410b460 0x304803af50410b46 0x1c003fff8000fc73 0x81c003fff8000fc7

def z366 : W := mkw 0x082004005700d208 0x8082004005700d20 0x000000007c00e000 0x0000000007c00e00

def z367 : W := mkw 0x058e30e02c60b044 0x3058e30e02c60b04 0xe78e30f07c00e002 0xae78e30f07c00e00

def z368 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x6fedacce00000003 0xf6fedacce0000000

def z369 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x140e30f00070fc72 0xa140e30f00070fc7

def z370 : W := mkw 0x4000011080910d20 0x44000011080910d2 0xa012533981b31c0b 0xfa012533981b31c0

def z371 : W := mkw 0x010a000000000000 0x0010a00000000000 0xe38e000000000000 0x2e38e00000000000

def z372 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e73f9fc70fc7f 0xff79e73f9fc70fc7

def z373 : W := mkw 0x0af03e005700d208 0x80af03e005700d20 0xebf03f007c00e001 0x9ebf03f007c00e00

def z374 : W := mkw 0x050e00f028702464 0x3050e00f02870246 0xe78e00f07c70007e 0x2e78e00f07c70007

def z375 : W := mkw 0x0ad03b0015809908 0x40ad03b001580990 0x839013001d801c08 0x0839013001d801c0

def z376 : W := mkw 0x03fffaa57b6a000f 0x003fffaa57b6a000 0xefffecc67fff000c 0x7efffecc67fff000

def z377 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ef80007c70000c 0x2e3ef80007c70000

def z378 : W := mkw 0xc004805aa05d24f2 0x2c004805aa05d24f 0x040fc0ff807f0072 0x6040fc0ff807f007

def z379 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x18618c0e624ce3f5 0x518618c0e624ce3f

def z380 : W := mkw 0x8024844262486242 0xa802484426248624 0x7c6dacc66200e385 0x97c6dacc66200e38

def z381 : W := mkw 0x0820050053804b08 0xc0820050053804b0 0x0000000003800380 0x0000000000380038

def z382 : W := mkw 0x0d8e3ff02cf0ff64 0xf0d8e3ff02cf0ff6 0xff8e3ff07c70ffff 0xaff8e3ff07c70fff

def z383 : W := mkw 0x035fc000396a000f 0x0035fc000396a000 0x839fc0001dff0008 0x6839fc0001dff000

def z384 : W := mkw 0x0bfffb007fea990f 0x40bfffb007fea990 0xe3ffd3007fff1c0c 0x7e3ffd3007fff1c0

def z385 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x63ed80007e4c0004 0x763ed80007e4c000

def z386 : W := mkw 0x02f03a0053000008 0x002f03a005300000 0xebf03f007f80000d 0x9ebf03f007f80000

def z387 : W := mkw 0x0af03f0053804b08 0xc0af03f0053804b0 0xebf03f0003800381 0x9ebf03f000380038

def z388 : W := mkw 0x02f03e0042004200 0x802f03e004200420 0xfbf03f006200e385 0x9fbf03f006200e38

def z389 : W := mkw 0x837fc4427b6a624f 0xa837fc4427b6a624 0xefffecc67fffe00c 0x7efffecc67fffe00

def z390 : W := mkw 0x03fffaa57b6a000f 0x003fffaa57b6a000 0x4fedacc67c000000 0x04fedacc67c00000

def z391 : W := mkw 0x85aeb4fa6e7cf6f6 0xb85aeb4fa6e7cf6f 0xf78e30f07e7cfffe 0xaf78e30f07e7cfff

def z392 : W := mkw 0x058a30a00c209004 0x1058a30a00c20900 0x038000001c000000 0x0038000001c00000

def z393 : W := mkw 0x88a4bf4a66ccfbd2 0xe88a4bf4a66ccfbd 0x7c6dbfce624cfff7 0xf7c6dbfce624cfff

def z394 : W := mkw 0x02f0300057009008 0x002f030005700900 0xf3f030007f80fc0c 0x9f3f030007f80fc0

def z395 : W := mkw 0x03db7a0000000000 0x003db7a000000000 0xebffff0000000001 0xfebffff000000000

def z396 : W := mkw 0x03da3aa000000000 0x003da3aa00000000 0xeffe3ff000000003 0xbeffe3ff00000000

def z397 : W := mkw 0x0af03e005700d208 0x80af03e005700d20 0xfbe03c007c00fc0c 0x8fbe03c007c00fc0

def z398 : W := mkw 0x0270000053000008 0x0027000005300000 0xe3f240007fff000c 0x7e3f240007fff000

def z399 : W := mkw 0x0271ca05530a000b 0x00271ca05530a000 0x0871cf0f838f0001 0x50871cf0f838f000

def z400 : W := mkw 0x0af03fa55780db08 0xc0af03fa55780db0 0xfff03fffff80ff8f 0x9fff03fffff80ff8

def z401 : W := mkw 0xc024855ae2dd6ff2 0xec024855ae2dd6ff 0x7c6dbfffe24cfff7 0xf7c6dbfffe24cfff

def z402 : W := mkw 0x050e00f02c70b464 0x3050e00f02c70b46 0x140e00f07c70fc7e 0x2140e00f07c70fc7

def z403 : W := mkw 0x4000011880950db0 0x44000011880950db 0x0012433983ff03f3 0x70012433983ff03f

def z404 : W := mkw 0xc020851ac29d4fb2 0xcc020851ac29d4fb 0xb873df3f83ff1fff 0xfb873df3f83ff1ff

def z405 : W := mkw 0x8a708f0a538c4b9a 0xc8a708f0a538c4b9 0x08718f0e038c0381 0x508718f0e038c038

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0xec7fffff80000003 0xfec7fffff8000000

def z407 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x18703f000380ff81 0x918703f000380ff8

def z408 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x4c6dacce620ce381 0x54c6dacce620ce38

def z409 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x478e20f07c70e072 0x2478e20f07c70e07

def z410 : W := mkw 0x027480007348000a 0x0027480007348000 0xe3fd80007fcc000c 0x7e3fd80007fcc000

def z411 : W := mkw 0x058a30b00c309424 0x1058a30b00c30942 0xf38230307c30fc0c 0x8f38230307c30fc0

def z412 : W := mkw 0x07fffaf57f7ab46f 0x307fffaf57f7ab46 0xfffffffffffffc7f 0xffffffffffffffc7

def z413 : W := mkw 0x0020000042000000 0x0002000004200000 0x6060000062000004 0x1606000006200000

def z414 : W := mkw 0x0270040053004208 0x8027004005300420 0xfbf02c007f80e38d 0x9fbf02c007f80e38

def z415 : W := mkw 0x058a30f00c30b464 0x3058a30f00c30b46 0x978230f01c30fc7a 0x8978230f01c30fc7

def z416 : W := mkw 0x03db7aad00040090 0x003db7aad0004009 0xffffffff824c03f7 0xfffffffff824c03f

def z417 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc7fecce63ffe3ff 0xffc7fecce63ffe3f

def z418 : W := mkw 0x035b400000000000 0x0035b40000000000 0xe3ffd33980000003 0xfe3ffd3398000000

def z419 : W := mkw 0x0af4bf0077c8db0a 0xc0af4bf0077c8db0 0xfbfdbf007fccff8d 0xffbfdbf007fccff8

def z420 : W := mkw 0x02d03b0000800900 0x402d03b000080090 0xfbf03f0003801f8d 0x9fbf03f0003801f8

def z421 : W := mkw 0x0004004020402040 0x2000400402040204 0x040c00c000400072 0x2040c00c00040007

def z422 : W := mkw 0x040000f000102460 0x3040000f00010246 0x040000f000000072 0x0040000f00000007

def z423 : W := mkw 0x8bffff4a7feefbdf 0xe8bffff4a7feefbd 0xffffffce7fffffff 0xfffffffce7ffffff

def z424 : W := mkw 0x08803b0004809900 0x408803b000480990 0x0000130000001c00 0x00000130000001c0

def z425 : W := mkw 0x018a30a000000000 0x0018a30a00000000 0x478c20c000000000 0x0478c20c00000000

def z426 : W := mkw 0x0000000000000000 0x0000000000000000 0xa012400000000000 0x7a01240000000000

def z427 : W := mkw 0x035f400028600004 0x0035f40002860000 0xe3ffc0007c70000c 0x7e3ffc0007c70000

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002403980000002 0x6000240398000000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c6dacc600000000 0x04c6dacc60000000

def z430 : W := mkw 0x010fc000286a0007 0x0010fc000286a000 0xe38fc0007c7f000c 0x6e38fc0007c7f000

def z431 : W := mkw 0x0000001000100420 0x0000000100010042 0x8002103000301c08 0x08002103000301c0

def z432 : W := mkw 0xc37fc55afbff6fff 0xec37fc55afbff6ff 0xffffffffffffffff 0xffffffffffffffff

def z433 : W := mkw 0x4bfb7fbdd795dfb8 0xc4bfb7fbdd795dfb 0xffffffffffffffff 0xffffffffffffffff

def z434 : W := mkw 0x81aeb4ea624c62d2 0xa81aeb4ea624c62d 0xffefbcfe624ce3f7 0xfffefbcfe624ce3f

def z435 : W := mkw 0xc024855ae2dd6ff2 0xec024855ae2dd6ff 0xb0125339e3ffffff 0xfb0125339e3fffff

def z436 : W := mkw 0x8024854a62cc6bd2 0xe8024854a62cc6bd 0xfc7dbfce63ccffff 0xffc7dbfce63ccfff

def z437 : W := mkw 0x4000010880850990 0x4400001088085099 0x3010430983cf03f7 0xf3010430983cf03f

def z438 : W := mkw 0x4a700f08d3854b98 0xc4a700f08d3854b9 0x08704f09838f0381 0x508704f09838f038

def z439 : W := mkw 0x0020050042804b00 0xc0020050042804b0 0xf8703f006380ff8d 0x9f8703f006380ff8

def z440 : W := mkw 0x0bffffa57feadb0f 0xc0bffffa57feadb0 0xffffffffffffff8f 0xfffffffffffffff8

def z441 : W := mkw 0x0004000020400000 0x0000400002040000 0x600c000060400004 0x2600c00006040000

def z442 : W := mkw 0x02514a0500000000 0x002514a050000000 0x6c7defcf80000003 0xf6c7defcf8000000

def z443 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x5be03f007c00ff81 0x85be03f007c00ff8

def z444 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x1c002cce624ce3f7 0x81c002cce624ce3f

def z445 : W := mkw 0x0270000053000008 0x0027000005300000 0x43e000007c000000 0x043e000007c00000

def z446 : W := mkw 0x0080300004009000 0x0008030000400900 0x838010001c001c08 0x0838010001c001c0

def z447 : W := mkw 0x0fda3bb01db09d2c 0x50fda3bb01db09d2 0x839213301db01c08 0x0839213301db01c0

def z448 : W := mkw 0x40248118fbff0dbf 0x440248118fbff0db 0xb0125339ffff1fff 0xfb0125339ffff1ff

def z449 : W := mkw 0x08a03f004680db00 0xc08a03f004680db0 0x78603f006200ff85 0x978603f006200ff8

def z450 : W := mkw 0x050e00e028602044 0x3050e00e02860204 0x040c00c000000000 0x0040c00c00000000

def z451 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x8f927fff80000003 0x88f927fff8000000

def z452 : W := mkw 0x058e30e02c60b044 0x3058e30e02c60b04 0x778c20c07c40e076 0xa778c20c07c40e07

def z453 : W := mkw 0x0020000053000008 0x0002000005300000 0x000000007f80000c 0x0000000007f80000

def z454 : W := mkw 0x03fff0a07b6a000f 0x003fff0a07b6a000 0xe7fff0f07fff000e 0xfe7fff0f07fff000

def z455 : W := mkw 0x077fc0507f7ab46f 0x3077fc0507f7ab46 0xf3ffc0007ffffc7c 0x7f3ffc0007ffffc7

def z456 : W := mkw 0x0020040042004200 0x8002004004200420 0x100000006200e384 0x0100000006200e38

def z457 : W := mkw 0x4af03f08d785db98 0xc4af03f08d785db9 0xfbf07f09ff8fff8d 0xdfbf07f09ff8fff8

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000002000385 0x9300000000200038

def z459 : W := mkw 0x0000004000002040 0x2000000400000204 0x140020c00000e072 0x8140020c00000e07

def z460 : W := mkw 0x0000011000900d20 0x40000011000900d2 0xb012133003f01fff 0xbb012133003f01ff

def z461 : W := mkw 0x0bdb7ba515809908 0x40bdb7ba51580990 0xefffffff9d801c0b 0xfefffffff9d801c0

def z462 : W := mkw 0x0bfb7f005780db08 0xc0bfb7f005780db0 0xfbffff007f80ff8d 0xffbffff007f80ff8

def z463 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xffefbcfe7c70fc7f 0xfffefbcfe7c70fc7

def z464 : W := mkw 0x035b40001922000d 0x0035b40001922000 0xe3ffc0001db30008 0x7e3ffc0001db3000

def z465 : W := mkw 0x85aeb4f26e78f666 0xb85aeb4f26e78f66 0xffefbcf67c70fc7e 0xaffefbcf67c70fc7

def z466 : W := mkw 0x037e00007b60000c 0x0037e00007b60000 0xe3fe00007ff0000c 0x3e3fe00007ff0000

def z467 : W := mkw 0x0a700f0053804b08 0xc0a700f0053804b0 0xb8701f0003801f8d 0x9b8701f0003801f8

def z468 : W := mkw 0x8000044200006240 0xa800004420000624 0x0c002cc60000e000 0x00c002cc60000e00

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000800000003 0xf200000080000000

def z470 : W := mkw 0x0ffa3fb05fb0df2c 0xd0ffa3fb05fb0df2 0xfbf23f307fb0ff8d 0x9fbf23f307fb0ff8

def z471 : W := mkw 0x07db7af50410b460 0x307db7af50410b46 0xffffffff8000fc73 0xfffffffff8000fc7

def z472 : W := mkw 0x08803e000400d200 0x808803e000400d20 0x08002c000000e000 0x008002c000000e00

def z473 : W := mkw 0x837fc44a7b6e62df 0xa837fc44a7b6e62d 0xf3ffc0007fffe3fc 0x7f3ffc0007fffe3f

def z474 : W := mkw 0x07fff0b07f7a942f 0x107fff0b07f7a942 0xe3ffd0307fff1c0c 0x7e3ffd0307fff1c0

def z475 : W := mkw 0x435b411099b30d2d 0x4435b411099b30d2 0x839253319db31c08 0x0839253319db31c0

def z476 : W := mkw 0x03db7ba500800900 0x403db7ba50080090 0xffffffff83801f8f 0xfffffffff83801f8

def z477 : W := mkw 0x0bffff007feadb0f 0xc0bffff007feadb0 0xfbfdbf007f80ff8d 0x9fbfdbf007f80ff8

def z478 : W := mkw 0x418a31b880950db0 0x4418a31b880950db 0xf79e73f983ff1fff 0xff79e73f983ff1ff

def z479 : W := mkw 0x0b7fc5007feadb0f 0xc0b7fc5007feadb0 0xf3ffc0007fffff8c 0x7f3ffc0007fffff8

def z480 : W := mkw 0x0ffe3ef07f70f66c 0xb0ffe3ef07f70f66 0xffee3cf07c70fc7e 0xaffee3cf07c70fc7

def z481 : W := mkw 0x812fc44a6a6e62d7 0xa812fc44a6a6e62d 0x7c6fecce627fe3f7 0xf7c6fecce627fe3f

def z482 : W := mkw 0x8024804a624c20d2 0x28024804a624c20d 0x646d80ce624c0076 0x7646d80ce624c007

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000024c0004 0x720000000024c000

def z484 : W := mkw 0x8275ce4f624c62d2 0xa8275ce4f624c62d 0x7c7defcfe24ce3f7 0xf7c7defcfe24ce3f

def z485 : W := mkw 0x0000010000800900 0x4000001000080090 0x1000000003801f8c 0x01000000003801f8

def z486 : W := mkw 0x0024800062480002 0x0002480006248000 0x00000000624c0004 0x000000000624c000

def z487 : W := mkw 0x0bfa3fa05780db08 0xc0bfa3fa05780db0 0xfffe3ff07f80ff8f 0xbfffe3ff07f80ff8

def z488 : W := mkw 0x058f70f52c70b464 0x3058f70f52c70b46 0xf78ff0fffc70fc7e 0xef78ff0fffc70fc7

def z489 : W := mkw 0x0ad03b0015809908 0x40ad03b001580990 0xf39033007d80fc0c 0x8f39033007d80fc0

def z490 : W := mkw 0x4000011080910d20 0x44000011080910d2 0xa012533183ff1c0c 0x7a012533183ff1c0

def z491 : W := mkw 0x0000000800040090 0x0000000080004009 0x7c6dacce024c03f7 0xf7c6dacce024c03f

def z492 : W := mkw 0x00000018001404b0 0x000000018001404b 0xb0021038027c1fff 0xfb0021038027c1ff

def z493 : W := mkw 0x0404005028702464 0x3040400502870246 0x0000000000700070 0x0000000000070007

def z494 : W := mkw 0x0004004020402040 0x2000400402040204 0x100000006040e074 0x0100000006040e07

def z495 : W := mkw 0x018e30e020402040 0x2018e30e02040204 0xf78e30f06040e076 0xaf78e30f06040e07

def z496 : W := mkw 0x437fc018fb7f04bf 0x0437fc018fb7f04b 0xe3ffc039ffff007e 0x7e3ffc039ffff007

def z497 : W := mkw 0x02d03aa500000000 0x002d03aa50000000 0xeff03fff80000003 0x9eff03fff8000000

def z498 : W := mkw 0x43db7abd801504b0 0x043db7abd801504b 0xefffffff807f0073 0xfefffffff807f007

def z499 : W := mkw 0x40000018801504b0 0x040000018801504b 0x30024039827f03f7 0xf30024039827f03f

def z500 : W := mkw 0x40248118fbff0dbf 0x440248118fbff0db 0x100000007fff1ffc 0x0100000007fff1ff

def z501 : W := mkw 0x010b40a500000000 0x0010b40a50000000 0x0002403180000000 0x0000240318000000

def z502 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4fefecff80000002 0x64fefecff8000000

def z503 : W := mkw 0x07fff0e07f6ab04f 0x307fff0e07f6ab04 0xe7ffe0c07fffe00c 0x7e7ffe0c07fffe00

def z504 : W := mkw 0x058e30b02c709424 0x1058e30b02c70942 0xe38e10307c701c0c 0x2e38e10307c701c0

def z505 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb002103003ff1ffe 0xab002103003ff1ff

def z506 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x4bf02f007f80e381 0x14bf02f007f80e38

def z507 : W := mkw 0x8000004a000420d0 0x28000004a000420d 0x040000ce00000072 0x0040000ce0000007

def z508 : W := mkw 0x410fc118a8ff0db7 0x4410fc118a8ff0db 0xb01fd33983ff1fff 0xfb01fd33983ff1ff

def z509 : W := mkw 0x058e30e02c60b044 0x3058e30e02c60b04 0xe78e20c07c70e00c 0x2e78e20c07c70e00

def z510 : W := mkw 0x040400402c60b044 0x3040400402c60b04 0x000000007c00e000 0x0000000007c00e00

def z511 : W := mkw 0x8004804a204c20d2 0x28004804a204c20d 0x00000000004c0070 0x000000000004c007

def z512 : W := mkw 0x02514a0500000000 0x002514a050000000 0xa873df3f80000003 0xfa873df3f8000000

def z513 : W := mkw 0x0000010000800900 0x4000001000080090 0xb012530003ff1f8d 0xfb012530003ff1f8

def z514 : W := mkw 0x03dffaa5286a0007 0x003dffaa5286a000 0xefffffff807f0003 0xfefffffff807f000

def z515 : W := mkw 0x83dffaef204c20d2 0x283dffaef204c20d 0xefffffff804c0073 0xfefffffff804c007

def z516 : W := mkw 0xc000055a80956ff0 0xec000055a80956ff 0x1c003fff8000fff3 0x81c003fff8000fff

def z517 : W := mkw 0x03db7aa51922000d 0x003db7aa51922000 0x839253319db30008 0x0839253319db3000

def z518 : W := mkw 0x002480007b6a000f 0x0002480007b6a000 0xa01240007fff000c 0x7a01240007fff000

def z519 : W := mkw 0x4000000880050090 0x0400000088005009 0x00004009800f0000 0x400004009800f000

def z520 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x878e10f01c701c7a 0x2878e10f01c701c7

def z521 : W := mkw 0x8af4bf4277c8fb4a 0xe8af4bf4277c8fb4 0xfffdbfc67f80ff8d 0x9fffdbfc67f80ff8

def z522 : W := mkw 0x07db70b01d32942d 0x107db70b01d32942 0x839250301db31c08 0x0839250301db31c0

def z523 : W := mkw 0x410e0118a8f50db4 0x4410e0118a8f50db 0xf39e5339ffff1fff 0xff39e5339ffff1ff

def z524 : W := mkw 0x8af4bf4a77ccfbda 0xe8af4bf4a77ccfbd 0xfbf03f007fccfffd 0x9fbf03f007fccfff

def z525 : W := mkw 0x010e000028600004 0x0010e00002860000 0x438c00007c000000 0x0438c00007c00000

def z526 : W := mkw 0x0000010000800900 0x4000001000080090 0x1000130000001f81 0x81000130000001f8

def z527 : W := mkw 0x07df70f03d72b46d 0x307df70f03d72b46 0xf79e70f07df3fc7e 0xaf79e70f07df3fc7

def z528 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xe3ffd33180000000 0x7e3ffd3318000000

def z529 : W := mkw 0x002480007b6a000f 0x0002480007b6a000 0x000000007c000000 0x0000000007c00000

def z530 : W := mkw 0x00208000530a000b 0x000208000530a000 0x00000000038f0000 0x000000000038f000

def z531 : W := mkw 0x0270000053000008 0x0027000005300000 0x0070000003800000 0x1007000000380000

def z532 : W := mkw 0x077fc0f07b7a246f 0x3077fc0f07b7a246 0xe7ffc0f07fff007e 0x7e7ffc0f07fff007

def z533 : W := mkw 0x058a30b00c309424 0x1058a30b00c30942 0xe78e30f01c301c0a 0xae78e30f01c301c0

def z534 : W := mkw 0x0b7fcf007bea4b0f 0xc0b7fcf007bea4b0 0xebffcf007fff038d 0x7ebffcf007fff038

def z535 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xa392533980000003 0xfa39253398000000

def z536 : W := mkw 0x07fff0f07f7ab46f 0x307fff0f07f7ab46 0xf7efb0f07c70fc7e 0xaf7efb0f07c70fc7

def z537 : W := mkw 0x02514a0500000000 0x002514a050000000 0x08618c0600000000 0x008618c060000000

def z538 : W := mkw 0x03df7ae520402040 0x203df7ae52040204 0xffffffffe040e077 0xfffffffffe040e07

def z539 : W := mkw 0x8004804a204c20d2 0x28004804a204c20d 0x6c6dacce004c0073 0xf6c6dacce004c007

def z540 : W := mkw 0x8af4be4a774cf2da 0xa8af4be4a774cf2d 0x7fedacce7e4ce3f7 0xf7fedacce7e4ce3f

def z541 : W := mkw 0x40000018801504b0 0x040000018801504b 0xa012403983ff007e 0x7a012403983ff007

def z542 : W := mkw 0x43db7bbd80950db0 0x443db7bbd80950db 0xb392533983ff1fff 0xfb392533983ff1ff

def z543 : W := mkw 0x0024804062482042 0x2002480406248204 0x746da0c0624ce076 0xf746da0c0624ce07

def z544 : W := mkw 0x47df7bfdacf5bdf4 0x747df7bfdacf5bdf 0xffffffffffffffff 0xffffffffffffffff

def z545 : W := mkw 0x4000001080110420 0x0400000108011042 0x0002403180330000 0x0000240318033000

def z546 : W := mkw 0x4271c118d39f0dbb 0x44271c118d39f0db 0xb073d33983ff1fff 0xfb073d33983ff1ff

def z547 : W := mkw 0x010b400008220005 0x0010b40000822000 0x0002400000330000 0x0000240000033000

def z548 : W := mkw 0x048030e00400b040 0x3048030e00400b04 0x040020c00000e000 0x0040020c00000e00

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010430980000001 0x5001043098000000

def z550 : W := mkw 0x02d17aa500000000 0x002d17aa50000000 0x0c71ffff80000003 0xd0c71ffff8000000

def z551 : W := mkw 0x018a30a000000000 0x0018a30a00000000 0xe79e73f980000003 0xfe79e73f98000000

def z552 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x706d8000624ce3f4 0x7706d8000624ce3f

def z553 : W := mkw 0x458e31f8acf5bdf4 0x7458e31f8acf5bdf 0xf78e33f9fc70ffff 0xaf78e33f9fc70fff

def z554 : W := mkw 0x0ef03ff05790ff68 0xf0ef03ff05790ff6 0xfff03ff07f80ffff 0x9fff03ff07f80fff

def z555 : W := mkw 0x010e004028602044 0x2010e00402860204 0xf78e20c07c70e07e 0xaf78e20c07c70e07

def z556 : W := mkw 0x0fff7ff57ff0ff6c 0xf0fff7ff57ff0ff6 0xfffffffffff0ffff 0xffffffffffff0fff

def z557 : W := mkw 0x0080300004009000 0x0008030000400900 0x438020007c00e000 0x0438020007c00e00

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x8012400001b30008 0x08012400001b3000

def z559 : W := mkw 0x83fbfeaf420c4292 0x883fbfeaf420c429 0xefffffff820c0383 0xfefffffff820c038

def z560 : W := mkw 0x000000a500000000 0x0000000a50000000 0x040000ff80000002 0x0040000ff8000000

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x640c20c000000002 0xa640c20c00000000

def z562 : W := mkw 0x8020840a420c4292 0x88020840a420c429 0x00000000020c0380 0x000000000020c038

def z563 : W := mkw 0x4000011880950db0 0x44000011880950db 0x8012533983bf1f89 0x58012533983bf1f8

def z564 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1000133983ff1fff 0x81000133983ff1ff

def z565 : W := mkw 0x40000018801504b0 0x040000018801504b 0x00000000007f0070 0x000000000007f007

def z566 : W := mkw 0x8274844a734c62da 0xa8274844a734c62d 0xfffdacce7fcce3ff 0xffffdacce7fcce3f

def z567 : W := mkw 0x0a71cf00538a4b0b 0xc0a71cf00538a4b0 0x0871cf00038f0381 0x50871cf00038f038

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x00104000038f0000 0x500104000038f000

def z569 : W := mkw 0x0a700f0053804b08 0xc0a700f0053804b0 0xebf00f007f80038d 0x1ebf00f007f80038

def z570 : W := mkw 0x040400502c70b464 0x3040400502c70b46 0x740c20c07c70fc7e 0xa740c20c07c70fc7

def z571 : W := mkw 0x8020840a420c4292 0x88020840a420c429 0x38618c0e024c03f7 0xf38618c0e024c03f

def z572 : W := mkw 0x0275c0007b6a000f 0x00275c0007b6a000 0x0071c0007fff000c 0x50071c0007fff000

def z573 : W := mkw 0x85aeb4ea6e6cf2d6 0xb85aeb4ea6e6cf2d 0x7fedacce7e4ce3f7 0xf7fedacce7e4ce3f

def z574 : W := mkw 0x8000044a000462d0 0xa8000044a000462d 0x100000000000e3f0 0x0100000000000e3f

def z575 : W := mkw 0x0a700f005780db08 0xc0a700f005780db0 0x18700f007f80ff8d 0x118700f007f80ff8

def z576 : W := mkw 0x0ad03a0015009008 0x00ad03a001500900 0x038000001c000000 0x0038000001c00000

def z577 : W := mkw 0x02d03a0000000000 0x002d03a000000000 0xeffdbfce00000003 0xfeffdbfce0000000

def z578 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb002133980701fff 0xab002133980701ff

def z579 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x78602c00624ce3f5 0x978602c00624ce3f

def z580 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefefbcf600000002 0xaefefbcf60000000

def z581 : W := mkw 0x037fc0087b6e009f 0x0037fc0087b6e009 0xf3ffc0087fff03ff 0xff3ffc0087fff03f

def z582 : W := mkw 0x010b400000000000 0x0010b40000000000 0x000fc00000000000 0x6000fc0000000000

def z583 : W := mkw 0x42514b1d80950db0 0x442514b1d80950db 0xb873df3f83ff1fff 0xfb873df3f83ff1ff

def z584 : W := mkw 0x0800010015809908 0x4080001001580990 0x000000001d801c08 0x0000000001d801c0

def z585 : W := mkw 0x0af4bf007feadb0f 0xc0af4bf007feadb0 0xfbf03f007fffff8d 0x9fbf03f007fffff8

def z586 : W := mkw 0x8271c40a530e429b 0x88271c40a530e429 0x0871cc0e038f0381 0x50871cc0e038f038

def z587 : W := mkw 0x0000001000100420 0x0000000100010042 0xb012503003ff1c7e 0xfb012503003ff1c7

def z588 : W := mkw 0x8020840a420c4292 0x88020840a420c429 0x6c6dacce020c0383 0xf6c6dacce020c038

def z589 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x007fc00003ff0000 0x7007fc00003ff000

def z590 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb012400003ff1ffc 0x7b012400003ff1ff

def z591 : W := mkw 0x0000001000100420 0x0000000100010042 0x1000000000701c7c 0x01000000000701c7

def z592 : W := mkw 0x4000010880850990 0x4400001088085099 0xb0105309838f1f8d 0xdb0105309838f1f8

def z593 : W := mkw 0x00803aa500000000 0x000803aa50000000 0x0000133180000000 0x0000013318000000

def z594 : W := mkw 0x018a30b000100420 0x0018a30b00010042 0xf78e30f000701c7e 0xaf78e30f000701c7

def z595 : W := mkw 0x082005005780db08 0xc082005005780db0 0xb01013007f80ff8d 0x9b01013007f80ff8

def z596 : W := mkw 0x0c803ff00490ff60 0xf0c803ff00490ff6 0x1c003ff00000fff3 0x81c003ff00000fff

def z597 : W := mkw 0x0271c000530a000b 0x00271c000530a000 0xe3f1c0007f8f000c 0x5e3f1c0007f8f000

def z598 : W := mkw 0x037fc0107b7a042f 0x0037fc0107b7a042 0xf3ffd0307fff1c7e 0xff3ffd0307fff1c7

def z599 : W := mkw 0x43db7bb580910d20 0x443db7bb580910d2 0xefffffff81b31c0b 0xfefffffff81b31c0

def z600 : W := mkw 0x00000a0500000000 0x000000a050000000 0x08000f0f80000001 0x008000f0f8000000

def z601 : W := mkw 0x03fffaa57b6a000f 0x003fffaa57b6a000 0xeffffffffc000003 0xfeffffffffc00000

def z602 : W := mkw 0x02514a0500000000 0x002514a050000000 0x0010430180000000 0x0001043018000000

def z603 : W := mkw 0x848034fa0414f6f0 0xb848034fa0414f6f 0x1c003cfe0000fff3 0x81c003cfe0000fff

def z604 : W := mkw 0x858eb0fa2c7cb4f6 0x3858eb0fa2c7cb4f 0xf78fb0fe7c7cfc7e 0xef78fb0fe7c7cfc7

def z605 : W := mkw 0xc020850ac28d4b92 0xcc020850ac28d4b9 0x0871cf0f838f0381 0x50871cf0f838f038

def z606 : W := mkw 0x018a3aa500000000 0x0018a3aa50000000 0xef8e3fff80000003 0xaef8e3fff8000000

def z607 : W := mkw 0x8024845a625c66f2 0xa8024845a625c66f 0xfc6fbcfe627cffff 0xffc6fbcfe627cfff

def z608 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xcffffff780000000 0x0cffffff78000000

def z609 : W := mkw 0x0000001000100420 0x0000000100010042 0x1000103000001c72 0x81000103000001c7

def z610 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x879fd3ff80000002 0x6879fd3ff8000000

def z611 : W := mkw 0x048430f02450b460 0x3048430f02450b46 0x740c30f06040fc76 0xa740c30f06040fc7

def z612 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x8bf01f001f801f89 0x18bf01f001f801f8

def z613 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x740c20c0624ce3f6 0xa740c20c0624ce3f

def z614 : W := mkw 0x037bc000530a000b 0x0037bc000530a000 0xe3ffc000038f0000 0x7e3ffc000038f000

def z615 : W := mkw 0x0000010000800900 0x4000001000080090 0xb012533983801f8f 0xfb012533983801f8

def z616 : W := mkw 0x042480507f7ab46f 0x3042480507f7ab46 0x100000007ffffc7c 0x0100000007ffffc7

def z617 : W := mkw 0x082005005780db08 0xc082005005780db0 0x78602c007f80ff8d 0x978602c007f80ff8

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000003ff000c 0x00000000003ff000

def z619 : W := mkw 0x4000011080910d20 0x44000011080910d2 0x0000133180001c00 0x00000133180001c0

def z620 : W := mkw 0x8af4be427748f24a 0xa8af4be427748f24 0x4fedacc67c00e000 0x04fedacc67c00e00

def z621 : W := mkw 0x4000011080910d20 0x44000011080910d2 0xb012533183b31f8d 0x9b012533183b31f8

def z622 : W := mkw 0x4000011880950db0 0x44000011880950db 0x10025339807f1ff3 0xe10025339807f1ff

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00200000070000c 0x2a00200000070000

def z624 : W := mkw 0x0000000800040090 0x0000000080004009 0xb012400803ff03ff 0xfb012400803ff03f

def z625 : W := mkw 0x012fc0006a6a0007 0x0012fc0006a6a000 0x606fc000627f0004 0x7606fc000627f000

def z626 : W := mkw 0x010fc0a5286a0007 0x0010fc0a5286a000 0x040fc0ff807f0002 0x6040fc0ff807f000

def z627 : W := mkw 0x082485007feadb0f 0xc082485007feadb0 0x100000007fffff8c 0x0100000007fffff8

def z628 : W := mkw 0x810fc04a286e20d7 0x2810fc04a286e20d 0x040fc0ce007f0072 0x6040fc0ce007f007

def z629 : W := mkw 0x018a30a004009000 0x0018a30a00400900 0xf78e30f07c00fc0e 0xaf78e30f07c00fc0

def z630 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3fd80007f80000c 0x1e3fd80007f80000

def z631 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc7fffffe24ce3f7 0xffc7fffffe24ce3f

def z632 : W := mkw 0x437fc108fbef099f 0x4437fc108fbef099 0xe3ffc309ffff038d 0x7e3ffc309ffff038

def z633 : W := mkw 0x0270010053800908 0x4027001005380090 0xf3f013007f801f8d 0x9f3f013007f801f8

def z634 : W := mkw 0x837fc44a7b6e62df 0xa837fc44a7b6e62d 0x7fedacce7e4ce3f7 0xf7fedacce7e4ce3f

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xa002103000000002 0xaa00210300000000

def z636 : W := mkw 0x87fffeff6e7cf6f6 0xb87fffeff6e7cf6f 0xfffffffffe7cffff 0xffffffffffe7cfff

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0x700020006000e004 0x8700020006000e00

def z638 : W := mkw 0x0ffffff07ffaff6f 0xf0ffffff07ffaff6 0xfffffff07fffffff 0xffffffff07ffffff

def z639 : W := mkw 0x0000000800040090 0x0000000080004009 0x10000008000003f3 0x810000008000003f

def z640 : W := mkw 0x0bfb7f005fa2db0d 0xc0bfb7f005fa2db0 0xfbf27f007fb3ff8d 0x9fbf27f007fb3ff8

def z641 : W := mkw 0x07df70f02c70b464 0x307df70f02c70b46 0xf7fff0f07c70fc7e 0xff7fff0f07c70fc7

def z642 : W := mkw 0x0bfe3f007fe0db0c 0xc0bfe3f007fe0db0 0xfbfe3f007ff0ff8d 0xbfbfe3f007ff0ff8

def z643 : W := mkw 0x4000010880850990 0x4400001088085099 0xa012430983ff038d 0x7a012430983ff038

def z644 : W := mkw 0x40040158a0d52df0 0x640040158a0d52df 0xf41e73f9e3ffffff 0xff41e73f9e3fffff

def z645 : W := mkw 0x0024800062480002 0x0002480006248000 0xe07fc00063ff000c 0x7e07fc00063ff000

def z646 : W := mkw 0x08803fa50480db00 0xc08803fa50480db0 0x1c003fff8000ff83 0x81c003fff8000ff8

def z647 : W := mkw 0x450e01f8a8f52df4 0x7450e01f8a8f52df 0xb41e53f983ff1fff 0xfb41e53f983ff1ff

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x606d800000000000 0x7606d80000000000

def z649 : W := mkw 0x00803aa500000000 0x000803aa50000000 0xac127fff80000003 0xfac127fff8000000

def z650 : W := mkw 0x018a30a000000000 0x0018a30a00000000 0x8382103000000000 0x0838210300000000

def z651 : W := mkw 0x035b400000000000 0x0035b40000000000 0x8392400000000000 0x0839240000000000

def z652 : W := mkw 0x83db7eef000462d0 0xa83db7eef000462d 0xffffffff8000e3f3 0xfffffffff8000e3f

def z653 : W := mkw 0x0bfb7ea55700d208 0x80bfb7ea55700d20 0x4fedacc67c00e000 0x04fedacc67c00e00

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x040d80ce00000002 0x6040d80ce0000000

def z655 : W := mkw 0x0000000800040090 0x0000000080004009 0x10000000024c03f4 0x010000000024c03f

def z656 : W := mkw 0x47fff1f8ffffbdff 0x747fff1f8ffffbdf 0xf7fff3f9ffffffff 0xff7fff3f9fffffff

def z657 : W := mkw 0x035b40a500000000 0x0035b40a50000000 0xe7ffc0ff80000002 0x7e7ffc0ff8000000

def z658 : W := mkw 0x410fc018a87f04b7 0x0410fc018a87f04b 0x000fc039807f0072 0x6000fc039807f007

def z659 : W := mkw 0x0024800062480002 0x0002480006248000 0x406d800060000000 0x0406d80006000000

def z660 : W := mkw 0x4af03f18d795dfb8 0xc4af03f18d795dfb 0xfbf03f39ff80ffff 0x9fbf03f39ff80fff

def z661 : W := mkw 0x8024844262486242 0xa802484426248624 0x7c6dacc66040e076 0xa7c6dacc66040e07

def z662 : W := mkw 0x80a4beef624c62d2 0xa80a4beef624c62d 0x7c6dbfffe24ce3f7 0xf7c6dbfffe24ce3f

def z663 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1010430983ff1ffd 0x51010430983ff1ff

def z664 : W := mkw 0xc3ffffffe2dd6ff2 0xec3ffffffe2dd6ff 0xffffffffe3ffffff 0xfffffffffe3fffff

def z665 : W := mkw 0x0024044062406240 0xa002404406240624 0x7c6c2cc06240e3f7 0xb7c6c2cc06240e3f

def z666 : W := mkw 0x48200518d795dfb8 0xc48200518d795dfb 0x100000007ffffffc 0x0100000007ffffff

def z667 : W := mkw 0x0000000800040090 0x0000000080004009 0x00000008004c0072 0x600000008004c007

def z668 : W := mkw 0x88803f4a0484fbd0 0xe88803f4a0484fbd 0x1c003fce0000fff3 0x81c003fce0000fff

def z669 : W := mkw 0x83fffee762486242 0xa83fffee76248624 0xefffffffe000e003 0xfefffffffe000e00

def z670 : W := mkw 0x05aeb0f07f7ab46f 0x305aeb0f07f7ab46 0xf78e30f07ffffc7e 0xaf78e30f07ffffc7

def z671 : W := mkw 0x85aeb4e26e68f246 0xb85aeb4e26e68f24 0x4fedacc67c00e000 0x04fedacc67c00e00

def z672 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43efc0007c7f0000 0x643efc0007c7f000

def z673 : W := mkw 0x4000011880950db0 0x44000011880950db 0x8012533981ff1c7a 0x68012533981ff1c7

def z674 : W := mkw 0x07df7ae52c60b044 0x307df7ae52c60b04 0x4fedacc67c00e000 0x04fedacc67c00e00

def z675 : W := mkw 0x040000100c309424 0x1040000100c30942 0x000000001c301c08 0x0000000001c301c0

def z676 : W := mkw 0x0ffe3ee07f60f24c 0xb0ffe3ee07f60f24 0x4fec2cc07c00e000 0x04fec2cc07c00e00

def z677 : W := mkw 0x00803aa500000000 0x000803aa50000000 0x0c002cc600000000 0x00c002cc60000000

def z678 : W := mkw 0x40000018801504b0 0x040000018801504b 0x0000003980000072 0x0000000398000007

def z679 : W := mkw 0x050fc0f0287a2467 0x3050fc0f0287a246 0x040fc0f0007f0072 0x6040fc0f0007f007

def z680 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x4c6dacce604ce072 0x64c6dacce604ce07

def z681 : W := mkw 0x012fc0007b6a000f 0x0012fc0007b6a000 0x000fc0007fff000c 0x6000fc0007fff000

def z682 : W := mkw 0x050e00f028702464 0x3050e00f02870246 0x740e20f06070e076 0xa740e20f06070e07

def z683 : W := mkw 0x4ad03b1895959db8 0x44ad03b1895959db 0xb39253399fff1fff 0xfb39253399fff1ff

def z684 : W := mkw 0x83fffeef7b6e62df 0xa83fffeef7b6e62d 0xffffffffffffe3ff 0xfffffffffffffe3f

def z685 : W := mkw 0x008030a000000000 0x0008030a00000000 0x040030f000000002 0x8040030f00000000

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c002cce00000003 0x80c002cce0000000

def z687 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x30000008624ce3f7 0xf30000008624ce3f

def z688 : W := mkw 0x0bfb7fa55780db08 0xc0bfb7fa55780db0 0xfbf27f31ff80ff8d 0x9fbf27f31ff80ff8

def z689 : W := mkw 0x00048000286a0007 0x000048000286a000 0x00000000007f0000 0x000000000007f000

def z690 : W := mkw 0x07db7ab50c309424 0x107db7ab50c30942 0xefffffff9c301c0b 0xfefffffff9c301c0

def z691 : W := mkw 0x08a03f005780db08 0xc08a03f005780db0 0x18003f007f80ff8d 0x818003f007f80ff8

def z692 : W := mkw 0x812e844a6a6c62d6 0xa812e844a6a6c62d 0xffefacce7e7ce3ff 0xfffefacce7e7ce3f

def z693 : W := mkw 0x040400502c70b464 0x3040400502c70b46 0xb00210307c70fc7e 0xab00210307c70fc7

def z694 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x0c6d8cce024c03f3 0x70c6d8cce024c03f

def z695 : W := mkw 0x03db7ab500100420 0x003db7ab50010042 0xffffffff80701c7f 0xfffffffff80701c7

def z696 : W := mkw 0x080005000480db00 0xc080005000480db0 0x100000000000ff80 0x0100000000000ff8

def z697 : W := mkw 0x4000010880850990 0x4400001088085099 0x00000000038f0380 0x000000000038f038

def z698 : W := mkw 0x0020800042080002 0x0002080004208000 0x00618000020c0000 0x500618000020c000

def z699 : W := mkw 0x08803f000480db00 0xc08803f000480db0 0xb8103f000380ff8d 0x9b8103f000380ff8

def z700 : W := mkw 0x048430f02c70b464 0x3048430f02c70b46 0x140030f07c70fc7e 0x8140030f07c70fc7

def z701 : W := mkw 0x0ad03f000480db00 0xc0ad03f000480db0 0xfbf03f000000ff81 0x9fbf03f000000ff8

def z702 : W := mkw 0x010e001028700424 0x0010e00102870042 0xf38e10307c701c7e 0xaf38e10307c701c7

def z703 : W := mkw 0x0dae35f07ff0ff6c 0xf0dae35f07ff0ff6 0xf78e30f07ff0fffe 0xaf78e30f07ff0fff

def z704 : W := mkw 0x8424845a6e7cf6f6 0xb8424845a6e7cf6f 0x100000007e7cfffc 0x0100000007e7cfff

def z705 : W := mkw 0x037b400053000008 0x0037b40005300000 0xe3ffc0007f80000c 0x7e3ffc0007f80000

def z706 : W := mkw 0x048030b004109420 0x1048030b00410942 0x0000103000001c00 0x00000103000001c0

def z707 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x578c30f07c70fc7e 0x8578c30f07c70fc7

def z708 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e30f07ffffc7e 0xaf78e30f07ffffc7

def z709 : W := mkw 0x048430f02450b460 0x3048430f02450b46 0xf78c30f07c40fc7e 0xaf78c30f07c40fc7

def z710 : W := mkw 0x0080301004109420 0x0008030100410942 0xf38030007c70fc7c 0x8f38030007c70fc7

def z711 : W := mkw 0x437fc118fbff0dbf 0x4437fc118fbff0db 0x53ed9339fc001ff3 0x853ed9339fc001ff

def z712 : W := mkw 0x4a700f08d3854b98 0xc4a700f08d3854b9 0x08700f00038f0381 0x108700f00038f038

def z713 : W := mkw 0x03db7aa504009000 0x003db7aa50400900 0xefffffff9c001c0b 0xfefffffff9c001c0

def z714 : W := mkw 0xc824855af7ddfffa 0xec824855af7ddfff 0x100000007ffffffc 0x0100000007ffffff

def z715 : W := mkw 0x02f03e004600d200 0x802f03e004600d20 0xfbf03f007e00ff8d 0x9fbf03f007e00ff8

def z716 : W := mkw 0x450fc0f8a87f24f7 0x3450fc0f8a87f24f 0x040fc0f9807f0072 0x6040fc0f9807f007

def z717 : W := mkw 0x098fff002ceadb07 0xc098fff002ceadb0 0x180fff00007fff81 0xe180fff00007fff8

def z718 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xb39013007f80ff8d 0x9b39013007f80ff8

def z719 : W := mkw 0x035b4aa500000000 0x0035b4aa50000000 0xefffcfff80000003 0x7efffcfff8000000

def z720 : W := mkw 0x4a700f08d3854b98 0xc4a700f08d3854b9 0x08700f0983800381 0x108700f098380038

def z721 : W := mkw 0x835b444a192662dd 0xa835b444a192662d 0x9f926cce1db3e3fb 0x89f926cce1db3e3f

def z722 : W := mkw 0x012e80007b6a000f 0x0012e80007b6a000 0xe39e40007fff000c 0x7e39e40007fff000

def z723 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffc0087fff000f 0xfe3ffc0087fff000

def z724 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf27f007f80ff8d 0xffbf27f007f80ff8

def z725 : W := mkw 0x8000044a000462d0 0xa8000044a000462d 0x7c6dacce024ce3f7 0xf7c6dacce024ce3f

def z726 : W := mkw 0x0af03fa55780db08 0xc0af03fa55780db0 0xfbf03f31ff80ff8d 0x9fbf03f31ff80ff8

def z727 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x5bf03f007f80ff81 0x95bf03f007f80ff8

def z728 : W := mkw 0x092b45a55780db08 0xc092b45a55780db0 0x140fc0ffff80ff8e 0x6140fc0ffff80ff8

def z729 : W := mkw 0xc024855afbff6fff 0xec024855afbff6ff 0x100000007ffffffc 0x0100000007ffffff

def z730 : W := mkw 0x00a4baa57b6a000f 0x000a4baa57b6a000 0x0c003fffffff000f 0x80c003fffffff000

def z731 : W := mkw 0x4a71cf08d38f4b9b 0xc4a71cf08d38f4b9 0x0871cf09838f0381 0x50871cf09838f038

def z732 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f007fccff8d 0xffbf03f007fccff8

def z733 : W := mkw 0x850e00fa287424f4 0x3850e00fa287424f 0x040e00fe00700072 0x2040e00fe0070007

def z734 : W := mkw 0x0af03f055780db08 0xc0af03f055780db0 0xfbf03f0fff80ff8d 0x9fbf03f0fff80ff8

def z735 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xf3f013007f80ff8c 0x1f3f013007f80ff8

def z736 : W := mkw 0x00040048204420d0 0x200040048204420d 0x7c6dacce624ce3f7 0xf7c6dacce624ce3f

def z737 : W := mkw 0x058f70f52c70b464 0x3058f70f52c70b46 0xffeffcfffc70fc7f 0xfffeffcfffc70fc7

def z738 : W := mkw 0x058f70f52c70b464 0x3058f70f52c70b46 0xf78fb0f67c70fc7e 0xaf78fb0f67c70fc7

def z739 : W := mkw 0x8020844a420c62d2 0xa8020844a420c62d 0x7c6dacce020ce3f3 0xf7c6dacce020ce3f

def z740 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xff8e3cfe7c70fc7f 0xaff8e3cfe7c70fc7

def z741 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xc3ffc0007fbf0008 0x5c3ffc0007fbf000

def z742 : W := mkw 0xca708f0ad38d4b9a 0xcca708f0ad38d4b9 0x0871cf0f838f0381 0x50871cf0f838f038

def z743 : W := mkw 0x4000011880950db0 0x44000011880950db 0x1012533983ff1ff3 0xf1012533983ff1ff

def z744 : W := mkw 0x018a30b004109420 0x0018a30b00410942 0xf78e30f07c70fc7e 0xaf78e30f07c70fc7

def z745 : W := mkw 0x4000011880950db0 0x44000011880950db 0x9012533983ff1ffe 0x69012533983ff1ff

def z746 : W := mkw 0x037fc4007b6a420f 0x8037fc4007b6a420 0xebffcc007fff038d 0x7ebffcc007fff038

def z747 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf27f31ff80ff8d 0x9fbf27f31ff80ff8

def z748 : W := mkw 0x8024844a734c62da 0xa8024844a734c62d 0x7c6dacce7fcce3ff 0xf7c6dacce7fcce3f

def z749 : W := mkw 0x06554a552c70b464 0x306554a552c70b46 0x1871cf0ffc70fc7d 0x51871cf0ffc70fc7

def z750 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xf3ffd0007fff1c0c 0xff3ffd0007fff1c0

def z751 : W := mkw 0x058e3af52c70b464 0x3058e3af52c70b46 0xffefbffffc70fc7f 0xfffefbffffc70fc7

def z752 : W := mkw 0x010fc000286a0007 0x0010fc000286a000 0xe39fc0007fff000c 0x7e39fc0007fff000

def z753 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x038000007fff000c 0x0038000007fff000

def z754 : W := mkw 0x048430502c70b464 0x3048430502c70b46 0xf78c30c07c70fc7e 0xaf78c30c07c70fc7

def z755 : W := mkw 0xc8803f5a8495fff0 0xec8803f5a8495fff 0x1c003fff8000fff3 0x81c003fff8000fff

def z756 : W := mkw 0x0a7005005780db08 0xc0a7005005780db0 0x939000007f80ff8c 0x0939000007f80ff8

def z757 : W := mkw 0x037b40005b22000d 0x0037b40005b22000 0xe3f240007fff000c 0x7e3f240007fff000

def z758 : W := mkw 0x00803aa500000000 0x000803aa50000000 0x4c6dbfff80000003 0x84c6dbfff8000000

def z759 : W := mkw 0x0af035005780db08 0xc0af035005780db0 0xf3f030007f80ff8c 0x9f3f030007f80ff8

def z760 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4ffdffff80000003 0xd4ffdffff8000000

def z761 : W := mkw 0x037e00007b60000c 0x0037e00007b60000 0xe3fe40007fff000c 0x7e3fe40007fff000

def z762 : W := mkw 0x0a7005005780db08 0xc0a7005005780db0 0xf3f013007f80ff8d 0x9f3f013007f80ff8

def z763 : W := mkw 0x43db7bbd80950db0 0x443db7bbd80950db 0x5fedacc603ff1ffc 0x05fedacc603ff1ff

def z764 : W := mkw 0x85aab4ba4e3cd6b6 0x985aab4ba4e3cd6b 0x8be39c3e1e3c1f89 0x58be39c3e1e3c1f8

def z765 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf27f39ffffff8f 0xffbf27f39ffffff8

def z766 : W := mkw 0xc271c50ad38f4b9b 0xcc271c50ad38f4b9 0x0871cf0f838f0381 0x50871cf0f838f038

def z767 : W := mkw 0x037fc0407b6a204f 0x2037fc0407b6a204 0xe7ffc0c07fff007e 0x7e7ffc0c07fff007

def z768 : W := mkw 0x4af03f00d781db08 0xc4af03f00d781db0 0xfbf07f01ff83ff8d 0x9fbf07f01ff83ff8

def z769 : W := mkw 0x050e00502c70b464 0x3050e00502c70b46 0xf78e20c07c70fc7e 0xaf78e20c07c70fc7

def z770 : W := mkw 0x08803f000480db00 0xc08803f000480db0 0xfb903f007f80ff8d 0x9fb903f007f80ff8

def z771 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xffffffffe000e007 0xfffffffffe000e00

def z772 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xf3ffc0007fff038d 0xff3ffc0007fff038

def z773 : W := mkw 0x0af17fa55780db08 0xc0af17fa55780db0 0xfff1ffffff80ff8f 0xdfff1ffffff80ff8

def z774 : W := mkw 0x0f7e0ff07bf06f6c 0xf0f7e0ff07bf06f6 0x0c7e0ff003f003f3 0x30c7e0ff003f003f

def z775 : W := mkw 0xc50e80faa87d24f6 0x3c50e80faa87d24f 0x040fc0ff807f0072 0x6040fc0ff807f007

def z776 : W := mkw 0x037fc0a57b6a000f 0x0037fc0a57b6a000 0xefffecffffff000f 0xfefffecffffff000

def z777 : W := mkw 0x037fca007b6a000f 0x0037fca007b6a000 0xebffcf007fff000d 0x7ebffcf007fff000

def z778 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e70f9fc70fc7e 0xef78e70f9fc70fc7

def z779 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xeffffffffc00000f 0xfeffffffffc00000

def z780 : W := mkw 0x06f1f0f0571ab46b 0x306f1f0f0571ab46 0x1471f0f0038ffc72 0xd1471f0f0038ffc7

def z781 : W := mkw 0x08a03f004680db00 0xc08a03f004680db0 0xfbe03f007e00ff8d 0x9fbe03f007e00ff8

def z782 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfffdbfc67f80ff8d 0x9fffdbfc67f80ff8

def z783 : W := mkw 0x058eb0f02c7ab467 0x3058eb0f02c7ab46 0xf78e30f07c7ffc7e 0xaf78e30f07c7ffc7

def z784 : W := mkw 0x0a7005005780db08 0xc0a7005005780db0 0x53e000007f80ff8c 0x053e000007f80ff8

def z785 : W := mkw 0x035f400028600004 0x0035f40002860000 0xe3ffc0007fff000c 0x7e3ffc0007fff000

def z786 : W := mkw 0x035fc000396a000f 0x0035fc000396a000 0x839240001dff0008 0x0839240001dff000

def z787 : W := mkw 0x47db7bb58cb19d24 0x547db7bb58cb19d2 0x839253319db31c08 0x0839253319db31c0

def z788 : W := mkw 0x0af17f005782db09 0xc0af17f005782db0 0xfbf07f007f83ff8d 0x9fbf07f007f83ff8

def z789 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x978e10f07c70fc7e 0x2978e10f07c70fc7

def z790 : W := mkw 0x037fca057b6a000f 0x0037fca057b6a000 0xe3ffc301ffff000c 0x7e3ffc301ffff000

def z791 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x778c20c07c70fc7e 0xa778c20c07c70fc7

def z792 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x5be03f007f80ff8d 0x85be03f007f80ff8

def z793 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf38e10307c70fc7c 0x2f38e10307c70fc7

def z794 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x9bf01f007f80ff8d 0x19bf01f007f80ff8

def z795 : W := mkw 0x037fca057b6a000f 0x0037fca057b6a000 0xebffcc067fff000c 0x7ebffcc067fff000

def z796 : W := mkw 0x010b40a500000000 0x0010b40a50000000 0xec7fffff80000003 0xfec7fffff8000000

def z797 : W := mkw 0x058e3af52c70b464 0x3058e3af52c70b46 0xff9e7ffffc70fc7f 0xfff9e7ffffc70fc7

def z798 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xb38210307c70fc7e 0xab38210307c70fc7

def z799 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff838f0003 0xfefffffff838f000

def z800 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xd78e30f07c70fc7c 0x0d78e30f07c70fc7

def z801 : W := mkw 0x02d03aa500000000 0x002d03aa50000000 0xeffdbfff80000003 0xfeffdbfff8000000

def z802 : W := mkw 0x035b4aa500000000 0x0035b4aa50000000 0xac7fdfff80000003 0xfac7fdfff8000000

def z803 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff8070000f 0xfefffffff8070000

def z804 : W := mkw 0x0af03fa55780db08 0xc0af03fa55780db0 0xfffdbfffff80ff8f 0xffffdbfffff80ff8

def z805 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacc6624ce3f6 0xa7c6dacc6624ce3f

def z806 : W := mkw 0x0270000053000008 0x0027000005300000 0xe3f000007fff000c 0x1e3f000007fff000

def z807 : W := mkw 0xc0248552e2d96f62 0xec0248552e2d96f6 0xcc7ffff7e1b3fc08 0x0cc7ffff7e1b3fc0

def z808 : W := mkw 0x0b7fce007b6a420f 0x80b7fce007b6a420 0xebffcc007fff000c 0x7ebffcc007fff000

def z809 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf38230307c70fc7c 0x8f38230307c70fc7

def z810 : W := mkw 0x0af03fa55780db08 0xc0af03fa55780db0 0xfff03fc67f80ff8d 0x9fff03fc67f80ff8

def z811 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43fdc0007fff000c 0x543fdc0007fff000

def z812 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xefffecc67fff000c 0x7efffecc67fff000

def z813 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f007fc0ffff 0xbfbf03f007fc0fff

def z814 : W := mkw 0x002480007b6a000f 0x0002480007b6a000 0xe38000007fff000c 0x0e38000007fff000

def z815 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e30f07c00fc72 0xaf78e30f07c00fc7

def z816 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xf3ffc0007fff007e 0xff3ffc0007fff007

def z817 : W := mkw 0xc48035fa8495fff0 0xfc48035fa8495fff 0x1c003fff8000fff3 0x81c003fff8000fff

def z818 : W := mkw 0x048030f00410b460 0x3048030f00410b46 0x578030f07c00fc72 0x8578030f07c00fc7

def z819 : W := mkw 0x0af0bf005788db0a 0xc0af0bf005788db0 0xfbf1bf007f8cff8d 0xdfbf1bf007f8cff8

def z820 : W := mkw 0x0af17f055780db08 0xc0af17f055780db0 0xfbf3ff3fff80ff8f 0xffbf3ff3fff80ff8

def z821 : W := mkw 0x8ad4bb4a35ccb9da 0x68ad4bb4a35ccb9d 0x879d93ce1dcc1c7a 0x6879d93ce1dcc1c7

def z822 : W := mkw 0x00803aa500000000 0x000803aa50000000 0xec7fffff80000003 0xfec7fffff8000000

def z823 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff824c0007 0xfefffffff824c000

def z824 : W := mkw 0x0af03fa05780db08 0xc0af03fa05780db0 0xfff03ff07f80ff8f 0x9fff03ff07f80ff8

def z825 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xffffffff82000387 0xfffffffff8200038

def z826 : W := mkw 0x0ad03b0015809908 0x40ad03b001580990 0xf39033007f80ff8d 0x9f39033007f80ff8

def z827 : W := mkw 0x035bc000192a000f 0x0035bc000192a000 0x8393c0001dbf0008 0x48393c0001dbf000

def z828 : W := mkw 0x058e30e02c60b044 0x3058e30e02c60b04 0xf78c30c07c40fc7e 0xaf78c30c07c40fc7

def z829 : W := mkw 0x037b400053000008 0x0037b40005300000 0xe3ffc0007fff000c 0x7e3ffc0007fff000

def z830 : W := mkw 0x027480007b6a000f 0x0027480007b6a000 0x43e000007fff000c 0x043e000007fff000

def z831 : W := mkw 0x4af03e18d715d6b8 0x84af03e18d715d6b 0x4be26c39fc7fe072 0x64be26c39fc7fe07

def z832 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xefffffffffff000f 0xfefffffffffff000

def z833 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf7efb0f07c70fc7e 0xff7efb0f07c70fc7

def z834 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfff03fce7f80ff8f 0x9fff03fce7f80ff8

def z835 : W := mkw 0x02f0310057809908 0x402f031005780990 0xf3f033007f80ff8d 0x9f3f033007f80ff8

def z836 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf02c007f80ff8c 0x1fbf02c007f80ff8

def z837 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x6fedbfff80000003 0xf6fedbfff8000000

def z838 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xffefbcf67c70fc7e 0xaffefbcf67c70fc7

def z839 : W := mkw 0x0a700f005780db08 0xc0a700f005780db0 0xfbf00f007f80ff8d 0x1fbf00f007f80ff8

def z840 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x578e30f07c70fc72 0xa578e30f07c70fc7

def z841 : W := mkw 0x83fffeef624c62d2 0xa83fffeef624c62d 0x93925331e24ce3f4 0x093925331e24ce3f

def z842 : W := mkw 0x4c803ff88495fff0 0xf4c803ff88495fff 0x1c003ff98000fff3 0x81c003ff98000fff

def z843 : W := mkw 0x077fc0e07b6a204f 0x3077fc0e07b6a204 0xe7ffc0c07fff000c 0x7e7ffc0c07fff000

def z844 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e70f07df3fc7e 0xaf79e70f07df3fc7

def z845 : W := mkw 0x012fc0007b6a000f 0x0012fc0007b6a000 0xe38fc0007fff000c 0x6e38fc0007fff000

def z846 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xcfffffff80000001 0x5cfffffff8000000

def z847 : W := mkw 0x8024844a7b6e62df 0xa8024844a7b6e62d 0x7c6dacce7e4ce3f7 0xf7c6dacce7e4ce3f

def z848 : W := mkw 0xc10fc05aa87f24f7 0x2c10fc05aa87f24f 0x040fc0ff807f0072 0x6040fc0ff807f007

def z849 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffd0307fff000e 0xfe3ffd0307fff000

def z850 : W := mkw 0x837fc0427b6a204f 0x2837fc0427b6a204 0xe7ffc0c67fff000c 0x7e7ffc0c67fff000

def z851 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacce624ce3f6 0x65c6dacce624ce3f

def z852 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xffffffff80400077 0xfffffffff8040007

def z853 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xc3ffc0007fff000c 0x0c3ffc0007fff000

def z854 : W := mkw 0x0af17f055780db08 0xc0af17f055780db0 0xfffdffcfff80ff8f 0xffffdffcfff80ff8

def z855 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e73f9fffffc7f 0xff79e73f9fffffc7

def z856 : W := mkw 0x0ad03f000480db00 0xc0ad03f000480db0 0xfbf03f007c00ff8d 0x9fbf03f007c00ff8

def z857 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e70f07c7ffc7e 0xef78e70f07c7ffc7

def z858 : W := mkw 0x8a708f0a538c4b9a 0xc8a708f0a538c4b9 0x08700f00038c0381 0x108700f00038c038

def z859 : W := mkw 0x8af0bf025788db0a 0xc8af0bf025788db0 0xfbf1bf067f80ff8d 0x9fbf1bf067f80ff8

def z860 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dbfffe24ce3f7 0xf7c6dbfffe24ce3f

def z861 : W := mkw 0x0fdb7bb51db09d2c 0x50fdb7bb51db09d2 0x839253319db01c08 0x0839253319db01c0

def z862 : W := mkw 0x02d03b0004809900 0x402d03b000480990 0xfbf03f007f80ff8d 0x9fbf03f007f80ff8

def z863 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb012533183ff1ffe 0xab012533183ff1ff

def z864 : W := mkw 0x037fc4007b6a420f 0x8037fc4007b6a420 0xf3ffc0007fffe38c 0x7f3ffc0007fffe38

def z865 : W := mkw 0x0bdb7aa515009008 0x00bdb7aa51500900 0xefffffff9c000003 0xfefffffff9c00000

def z866 : W := mkw 0x058f7af52c70b464 0x3058f7af52c70b46 0xff8ffffffc70fc7f 0xeff8ffffffc70fc7

def z867 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e30f07ff0fc7e 0xbf79e30f07ff0fc7

def z868 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x7be03f007e00ff85 0x97be03f007e00ff8

def z869 : W := mkw 0x450f40fda87524f4 0x3450f40fda87524f 0x040fc0ff807f0072 0x6040fc0ff807f007

def z870 : W := mkw 0x4000011880950db0 0x44000011880950db 0x8012533983ff1ffb 0x78012533983ff1ff

def z871 : W := mkw 0x0a7005005780db08 0xc0a7005005780db0 0xfbf02c007f80ff8d 0x9fbf02c007f80ff8

def z872 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43efc0007fff000c 0x643efc0007fff000

def z873 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xebffec007fff000d 0xfebffec007fff000

def z874 : W := mkw 0x4000011880950db0 0x44000011880950db 0x9012533983ff1fff 0x89012533983ff1ff

def z875 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e33f9fc70fc7f 0xaf78e33f9fc70fc7

def z876 : W := mkw 0x018a3aa500000000 0x0018a3aa50000000 0xefefbfff80000003 0xfefefbfff8000000

def z877 : W := mkw 0x8a71cf0f538c4b9a 0xc8a71cf0f538c4b9 0x0871cf0f838c0381 0x50871cf0f838c038

def z878 : W := mkw 0x050e00f8287424f4 0x3050e00f8287424f 0x040e00f8007c0072 0x6040e00f8007c007

def z879 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xfffffffffc70fc7f 0xffffffffffc70fc7

def z880 : W := mkw 0x008430402440b040 0x2008430402440b04 0xf38030007c40fc7c 0x8f38030007c40fc7

def z881 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x4c6dacce624ce3f3 0x74c6dacce624ce3f

def z882 : W := mkw 0x008430502450b460 0x2008430502450b46 0xf78e30f07c70fc7e 0xaf78e30f07c70fc7

def z883 : W := mkw 0x037fc0407b6a204f 0x2037fc0407b6a204 0xf3ffc0007fffe07c 0x7f3ffc0007fffe07

def z884 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c7decce63cfe3f7 0xf7c7decce63cfe3f

def z885 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e30f07e7cfc7e 0xff78e30f07e7cfc7

def z886 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xf39033007f80ff8c 0x8f39033007f80ff8

def z887 : W := mkw 0x07db7aa50c209004 0x107db7aa50c20900 0xefffffff9c000003 0xfefffffff9c00000

def z888 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe7ffe0c07fff000e 0xfe7ffe0c07fff000

def z889 : W := mkw 0x4a714f0dd3854b98 0xc4a714f0dd3854b9 0x0871cf0f838f0381 0x50871cf0f838f038

def z890 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xffffffffff80ff8f 0xfffffffffff80ff8

def z891 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e20c07c70fc7c 0x2f78e20c07c70fc7

def z892 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb012533183ff1ffc 0x7b012533183ff1ff

def z893 : W := mkw 0x08803f000480db00 0xc08803f000480db0 0x5b803f007c00ff81 0x85b803f007c00ff8

def z894 : W := mkw 0x837fc4427b6a624f 0xa837fc4427b6a624 0xffffecc67fffe07e 0xfffffecc67fffe07

def z895 : W := mkw 0x44803bfd8495bdf0 0x744803bfd8495bdf 0x1c003fff8000fff3 0x81c003fff8000fff

def z896 : W := mkw 0x037fc4407b6a624f 0xa037fc4407b6a624 0xffffecc07fffe3ff 0xfffffecc07fffe3f

def z897 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6fecce627fe3f7 0xf7c6fecce627fe3f

def z898 : W := mkw 0x058f70f52c70b464 0x3058f70f52c70b46 0xf79ff3fffc70fc7f 0xff79ff3fffc70fc7

def z899 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x778c30f07c40fc76 0xa778c30f07c40fc7

def z900 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf23f307f80ff8f 0xbfbf23f307f80ff8

def z901 : W := mkw 0x4000011880950db0 0x44000011880950db 0x9012533983ff1ffd 0x59012533983ff1ff

def z902 : W := mkw 0x837fc4427b6a624f 0xa837fc4427b6a624 0xefffecce7fffe00f 0xfefffecce7fffe00

def z903 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e70f07c70fc7e 0xff79e70f07c70fc7

def z904 : W := mkw 0x8004844a204c62d2 0xa8004844a204c62d 0x7c6dacce004ce3f3 0xf7c6dacce004ce3f

def z905 : W := mkw 0x058f70f52c70b464 0x3058f70f52c70b46 0xf78e70f1fc70fc7e 0xaf78e70f1fc70fc7

def z906 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xa39240007fff000c 0x7a39240007fff000

def z907 : W := mkw 0x850e80fa287c24f6 0x3850e80fa287c24f 0x040e00f0007c0072 0x2040e00f0007c007

def z908 : W := mkw 0x0250000011000008 0x0025000001100000 0xa39240001fff000c 0x7a39240001fff000

def z909 : W := mkw 0x4000011880950db0 0x44000011880950db 0xf0127339e3ffffff 0xff0127339e3fffff

def z910 : W := mkw 0x8004044a204462d0 0xa8004044a204462d 0x7c6dacce6040e3f7 0xf7c6dacce6040e3f

def z911 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xcfffffff80000003 0x8cfffffff8000000

def z912 : W := mkw 0x850fc0ff287c24f6 0x3850fc0ff287c24f 0x040fc0ff807c0072 0x6040fc0ff807c007

def z913 : W := mkw 0x018e30e02440b040 0x2018e30e02440b04 0xf78e30f07c40fc7e 0xaf78e30f07c40fc7

def z914 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6fecffe24ce3f7 0xf7c6fecffe24ce3f

def z915 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff81b3000b 0xfefffffff81b3000

def z916 : W := mkw 0x058e30f52c70b464 0x3058e30f52c70b46 0xf78e30fffc70fc7e 0xaf78e30fffc70fc7

def z917 : W := mkw 0x058e3af52c70b464 0x3058e3af52c70b46 0xf78e33f1fc70fc7e 0xaf78e33f1fc70fc7

def z918 : W := mkw 0x010a000008200004 0x0010a00000820000 0xa39240001fff000c 0x7a39240001fff000

def z919 : W := mkw 0x458e31e8ace5b9d4 0x7458e31e8ace5b9d 0x479c63c9ff8fe381 0x5479c63c9ff8fe38

def z920 : W := mkw 0x035f40003962000d 0x0035f40003962000 0xe39e40007fff000c 0x7e39e40007fff000

def z921 : W := mkw 0x048430502c70b464 0x3048430502c70b46 0x538020007c70fc7c 0x0538020007c70fc7

def z922 : W := mkw 0x088035000480db00 0xc088035000480db0 0xf38030007c00ff8c 0x8f38030007c00ff8

def z923 : W := mkw 0x08a035005780db08 0xc08a035005780db0 0xfbe03c007f80ff8d 0x9fbe03c007f80ff8

def z924 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacc6624ce3f5 0x97c6dacc6624ce3f

def z925 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacce6000e3f3 0xf7c6dacce6000e3f

def z926 : W := mkw 0x8024844a6a6e62d7 0xa8024844a6a6e62d 0x7c6dacce627fe3f7 0xf7c6dacce627fe3f

def z927 : W := mkw 0x00a034004600d200 0x800a034004600d20 0xf38030007e00ff8c 0x8f38030007e00ff8

def z928 : W := mkw 0xc024844ae24d62d2 0xac024844ae24d62d 0x7c6deccfe24fe3f7 0xf7c6deccfe24fe3f

def z929 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfffc3fc07f80ff8f 0xbfffc3fc07f80ff8

def z930 : W := mkw 0x037fca057b6a000f 0x0037fca057b6a000 0xebffdf3fffff000f 0xfebffdf3fffff000

def z931 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x0c7fffff80000003 0xf0c7fffff8000000

def z932 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x83f3c0007fff000c 0x583f3c0007fff000

def z933 : W := mkw 0x448031f88495bdf0 0x7448031f88495bdf 0x140030f00000fff2 0x8140030f00000fff

def z934 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e30f07e70ffff 0xbf78e30f07e70fff

def z935 : W := mkw 0x050e00502c70b464 0x3050e00502c70b46 0x938200007c70fc7c 0x0938200007c70fc7

def z936 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x9b903f007f80ff8d 0x89b903f007f80ff8

def z937 : W := mkw 0x040400502c70b464 0x3040400502c70b46 0xf38000007c70fc7c 0x0f38000007c70fc7

def z938 : W := mkw 0x027480007348000a 0x0027480007348000 0xe3ffc0007fff000c 0x7e3ffc0007fff000

def z939 : W := mkw 0x0af17f005780db08 0xc0af17f005780db0 0xfbf1ff007f80ff8d 0xdfbf1ff007f80ff8

def z940 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xffedacce7e4ce3ff 0xfffedacce7e4ce3f

def z941 : W := mkw 0x0080310004809900 0x4008031000480990 0xf38030007f80ff8c 0x8f38030007f80ff8

def z942 : W := mkw 0x0080300004009000 0x0008030000400900 0xf38030007e00ff8d 0x9f38030007e00ff8

def z943 : W := mkw 0x0a700f0853844b98 0xc0a700f0853844b9 0x08700f08038c0381 0x508700f08038c038

def z944 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf07f09ff80ff8d 0xdfbf07f09ff80ff8

def z945 : W := mkw 0x010e005028702464 0x2010e00502870246 0xf78e30f07c70fc7e 0xaf78e30f07c70fc7

def z946 : W := mkw 0x037fc0a57b6a000f 0x0037fc0a57b6a000 0xe7ffc0c67fff000c 0x7e7ffc0c67fff000

def z947 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc7dacce63cce3ff 0xffc7dacce63cce3f

def z948 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x43ffc0007fff0000 0x743ffc0007fff000

def z949 : W := mkw 0x0080310004809900 0x4008031000480990 0xf38033007c00ff8d 0x8f38033007c00ff8

def z950 : W := mkw 0x037bc0005b2a000f 0x0037bc0005b2a000 0xe3ffc0001fbf0008 0x7e3ffc0001fbf000

def z951 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe39e40007fff000c 0x2e39e40007fff000

def z952 : W := mkw 0x03db7aa508200004 0x003db7aa50820000 0xefffffff9c30000b 0xfefffffff9c30000

def z953 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xdbf03f007f80ff8c 0x0dbf03f007f80ff8

def z954 : W := mkw 0xc424855aeefdfff6 0xfc424855aeefdfff 0x100000007ffffffc 0x0100000007ffffff

def z955 : W := mkw 0x058f70f02c70b464 0x3058f70f02c70b46 0xf78ff0f07c70fc7e 0xef78ff0f07c70fc7

def z956 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc6facce627ce3ff 0xffc6facce627ce3f

def z957 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc6fbcfe624ce3f7 0xffc6fbcfe624ce3f

def z958 : W := mkw 0x0000000000000000 0x0000000000000000 0xe39240007fff000c 0x7e39240007fff000

def z959 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x5be02c007c00ff80 0x05be02c007c00ff8

def z960 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacce624ce3f5 0x55c6dacce624ce3f

def z961 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xffee3cf07c70fc7f 0xbffee3cf07c70fc7

def z962 : W := mkw 0x027480007b6a000f 0x0027480007b6a000 0xe3fd80007fff000c 0x7e3fd80007fff000

def z963 : W := mkw 0x058a30b00c309424 0x1058a30b00c30942 0xf38230307c70fc7e 0xaf38230307c70fc7

def z964 : W := mkw 0x037fc4007b6a420f 0x8037fc4007b6a420 0xebffec007fffe00c 0x7ebffec007fffe00

def z965 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xffffffff80001c0f 0xfffffffff80001c0

def z966 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c6dbfff80000003 0xf6c6dbfff8000000

def z967 : W := mkw 0x037fc0a57b6a000f 0x0037fc0a57b6a000 0xe3ffc031ffff000c 0x7e3ffc031ffff000

def z968 : W := mkw 0x08a035005780db08 0xc08a035005780db0 0x938010007f80ff8c 0x0938010007f80ff8

def z969 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x138000007f80ff8c 0x0138000007f80ff8

def z970 : W := mkw 0x03db7aa508220005 0x003db7aa50822000 0xefffffff80330003 0xfefffffff8033000

def z971 : W := mkw 0x027480007b6a000f 0x0027480007b6a000 0xe3f240007fff000c 0x7e3f240007fff000

def z972 : W := mkw 0x035b400000000000 0x0035b40000000000 0xefffffff80000003 0xfefffffff8000000

def z973 : W := mkw 0x050e00f02c70b464 0x3050e00f02c70b46 0xf78e00f07c70fc7e 0x2f78e00f07c70fc7

def z974 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xdbf03f007d80ff89 0x8dbf03f007d80ff8

def z975 : W := mkw 0x048430f02c70b464 0x3048430f02c70b46 0xf78030f07c70fc7e 0x8f78030f07c70fc7

def z976 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefefbfff80000003 0xaefefbfff8000000

def z977 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4fefffff80000003 0xe4fefffff8000000

def z978 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78c30c07c70fc7c 0x8f78c30c07c70fc7

def z979 : W := mkw 0x058ff0f02c7ab467 0x3058ff0f02c7ab46 0xf79ff0f07ffffc7e 0xff79ff0f07ffffc7

def z980 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xd78e30f07c30fc7a 0x8d78e30f07c30fc7

def z981 : W := mkw 0x03db7aa511000008 0x003db7aa51100000 0xefffffff9d80000b 0xfefffffff9d80000

def z982 : W := mkw 0x458e30f0ac71b464 0x3458e30f0ac71b46 0xf78e70f1fc73fc7e 0xaf78e70f1fc73fc7

def z983 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacce604ce3f3 0xe5c6dacce604ce3f

def z984 : W := mkw 0x037e80007b6a000f 0x0037e80007b6a000 0xe3fe00007fff000c 0x3e3fe00007fff000

def z985 : W := mkw 0x058ff0f02c7ab467 0x3058ff0f02c7ab46 0xf78fb0f07c70fc7e 0xaf78fb0f07c70fc7

def z986 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x1c6dacce024ce3f3 0xf1c6dacce024ce3f

def z987 : W := mkw 0x058a30f00c30b464 0x3058a30f00c30b46 0xf78230f07c30fc7e 0x8f78230f07c30fc7

def z988 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffc309ffff000d 0x7e3ffc309ffff000

def z989 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb012533183ff1ffd 0x9b012533183ff1ff

def z990 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xcbf03f007f80ff89 0x1cbf03f007f80ff8

def z991 : W := mkw 0x837fc4027b6a420f 0x8837fc4027b6a420 0xebffcc067fff000c 0x7ebffcc067fff000

def z992 : W := mkw 0x050e00502c70b464 0x3050e00502c70b46 0x538c00007c70fc7c 0x0538c00007c70fc7

def z993 : W := mkw 0x0024044062406240 0xa002404406240624 0x7c6dacce6240e3f7 0xf7c6dacce6240e3f

def z994 : W := mkw 0x837fc4427b6a624f 0xa837fc4427b6a624 0xe3ffc0007fffe00c 0x7e3ffc0007fffe00

def z995 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x138000007c70fc7c 0x0138000007c70fc7

def z996 : W := mkw 0x02d17aa500000000 0x002d17aa50000000 0x6c7dffff80000003 0xf6c7dffff8000000

def z997 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf27f007fb3ff8d 0x9fbf27f007fb3ff8

def z998 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xebffcc0e7fff000d 0x7ebffcc0e7fff000

def z999 : W := mkw 0x02d03a0000000000 0x002d03a000000000 0xefffffff80000003 0xfefffffff8000000

def z1000 : W := mkw 0x858eb0f22c78b466 0x3858eb0f22c78b46 0xf78fb0f67c70fc7e 0xaf78fb0f67c70fc7

def z1001 : W := mkw 0x837fc4427b6a624f 0xa837fc4427b6a624 0xffffecc67fffe38d 0xfffffecc67fffe38

def z1002 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc7fecce624ce3f7 0xffc7fecce624ce3f

def z1003 : W := mkw 0x082005005780db08 0xc082005005780db0 0xf38000007f80ff8c 0x0f38000007f80ff8

def z1004 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacce6040e3f7 0xa7c6dacce6040e3f

def z1005 : W := mkw 0x03db7aa511020009 0x003db7aa51102000 0xefffffff81830003 0xfefffffff8183000

def z1006 : W := mkw 0x012e80007b6a000f 0x0012e80007b6a000 0xe3ef80007fff000c 0x7e3ef80007fff000

def z1007 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe7ffc0ce7fff000e 0x7e7ffc0ce7fff000

def z1008 : W := mkw 0x010e000028600004 0x0010e00002860000 0xe38e00007fff000c 0x2e38e00007fff000

def z1009 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x8fffdfff80000003 0x78fffdfff8000000

def z1010 : W := mkw 0x048030f00410b460 0x3048030f00410b46 0xf78230f07c70fc7e 0xaf78230f07c70fc7

def z1011 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x5bf02f007f80ff8d 0x15bf02f007f80ff8

def z1012 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff807f0003 0xfefffffff807f000

def z1013 : W := mkw 0x08a03f005780db08 0xc08a03f005780db0 0xfb803f007f80ff8d 0x8fb803f007f80ff8

def z1014 : W := mkw 0x8024844a734e62db 0xa8024844a734e62d 0x7c6dacce63cfe3f7 0xf7c6dacce63cfe3f

def z1015 : W := mkw 0x037fc0057b6a000f 0x0037fc0057b6a000 0xe3ffc00fffff000c 0x7e3ffc00fffff000

def z1016 : W := mkw 0x03db7aa51922000d 0x003db7aa51922000 0xefffffff9fff000f 0xfefffffff9fff000

def z1017 : W := mkw 0x048030500410b460 0x3048030500410b46 0xf38030007c00fc7c 0x8f38030007c00fc7

def z1018 : W := mkw 0x0af03fa55780db08 0xc0af03fa55780db0 0xfff27fffff80ff8f 0xffff27fffff80ff8

def z1019 : W := mkw 0x058ff0f52c7ab467 0x3058ff0f52c7ab46 0xf78ff0fffc7ffc7e 0xef78ff0fffc7ffc7

def z1020 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0x7be02c007f80ff8d 0x97be02c007f80ff8

def z1021 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf07f007f8fff8d 0xdfbf07f007f8fff8

def z1022 : W := mkw 0x48803f188495dfb0 0xc48803f188495dfb 0x18003f000000fff1 0x818003f000000fff

def z1023 : W := mkw 0x012e80007b6a000f 0x0012e80007b6a000 0x838200007fff000c 0x0838200007fff000

def z1024 : W := mkw 0x48803b1884959db0 0x448803b1884959db 0x1000133980001ff3 0x81000133980001ff

def z1025 : W := mkw 0x035b40001922000d 0x0035b40001922000 0x839240001dff0008 0x6839240001dff000

def z1026 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffc039ffff000e 0x7e3ffc039ffff000

def z1027 : W := mkw 0x035b40001922000d 0x0035b40001922000 0x839240001fbf0008 0x5839240001fbf000

def z1028 : W := mkw 0x8a700f0a53844b98 0xc8a700f0a53844b9 0x08700f0e03800381 0x108700f0e0380038

def z1029 : W := mkw 0x0af1ff00578adb0b 0xc0af1ff00578adb0 0xfbf1bf007f80ff8d 0x9fbf1bf007f80ff8

def z1030 : W := mkw 0x058e30502c70b464 0x3058e30502c70b46 0xf38e30007c70fc7c 0xaf38e30007c70fc7

def z1031 : W := mkw 0x02f034005700d208 0x802f034005700d20 0xfbf03c007f80ff8d 0x9fbf03c007f80ff8

def z1032 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c7defcfe24ce3f7 0xf7c7defcfe24ce3f

def z1033 : W := mkw 0x048430502c70b464 0x3048430502c70b46 0xf38230307c70fc7e 0xaf38230307c70fc7

def z1034 : W := mkw 0x012e80007b6a000f 0x0012e80007b6a000 0x438c00007fff000c 0x0438c00007fff000

def z1035 : W := mkw 0x037fc0407b6a204f 0x2037fc0407b6a204 0xe7ffe0c07fffe00c 0x7e7ffe0c07fffe00

def z1036 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f007c00ff81 0x9fbf03f007c00ff8

def z1037 : W := mkw 0x0275c0007b6a000f 0x00275c0007b6a000 0xe3f1c0007fff000c 0x5e3f1c0007fff000

def z1038 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacc6624ce3f4 0x77c6dacc6624ce3f

def z1039 : W := mkw 0x037fcaa57b6a000f 0x0037fcaa57b6a000 0xefffcfffffff000f 0x7efffcfffffff000

def z1040 : W := mkw 0x0271c000530a000b 0x00271c000530a000 0xe3f3c0007fff000c 0x7e3f3c0007fff000

def z1041 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xc78e30f07c70fc7a 0x2c78e30f07c70fc7

def z1042 : W := mkw 0x8a71cf0a538e4b9b 0xc8a71cf0a538e4b9 0x0871cf0e038f0381 0x50871cf0e038f038

def z1043 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacc66000e3f0 0x05c6dacc66000e3f

def z1044 : W := mkw 0x058f70f02c72b465 0x3058f70f02c72b46 0xf78e70f07c73fc7e 0xaf78e70f07c73fc7

def z1045 : W := mkw 0x037fc0a57b6a000f 0x0037fc0a57b6a000 0xe7ffd3ffffff000f 0xfe7ffd3ffffff000

def z1046 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf1bf0e7f80ff8d 0xdfbf1bf0e7f80ff8

def z1047 : W := mkw 0x037fca057b6a000f 0x0037fca057b6a000 0xefffefcfffff000f 0xfefffefcfffff000

def z1048 : W := mkw 0x8024844a7b6e62df 0xa8024844a7b6e62d 0xfc7fecce7fffe3ff 0xffc7fecce7fffe3f

def z1049 : W := mkw 0x012e80006a680006 0x0012e80006a68000 0xe3ffc0007fff000c 0x7e3ffc0007fff000

def z1050 : W := mkw 0x03db7aa51922000d 0x003db7aa51922000 0xefffffff9c000003 0xfefffffff9c00000

def z1051 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacce620ce3f3 0xd5c6dacce620ce3f

def z1052 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3fd80007fff000c 0x1e3fd80007fff000

def z1053 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x83ffc0001fff0008 0x783ffc0001fff000

def z1054 : W := mkw 0x058a30f00410b460 0x3058a30f00410b46 0xf78e30f07c00fc7e 0xaf78e30f07c00fc7

def z1055 : W := mkw 0x018b7aa500000000 0x0018b7aa50000000 0x6c6fffff80000003 0xf6c6fffff8000000

def z1056 : W := mkw 0x008030400400b040 0x2008030400400b04 0xf78030c07c00fc7e 0x8f78030c07c00fc7

def z1057 : W := mkw 0x0af17f055780db08 0xc0af17f055780db0 0xfbf07f01ff80ff8d 0x9fbf07f01ff80ff8

def z1058 : W := mkw 0x08a035005780db08 0xc08a035005780db0 0x538020007f80ff8c 0x0538020007f80ff8

def z1059 : W := mkw 0x0080301004109420 0x0008030100410942 0xf38030307c00fc7e 0x8f38030307c00fc7

def z1060 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb873df3f83ff1fff 0xfb873df3f83ff1ff

def z1061 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x578e20f07c70fc7e 0x2578e20f07c70fc7

def z1062 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc7fffffe3ffe3ff 0xffc7fffffe3ffe3f

def z1063 : W := mkw 0x0af17f055780db08 0xc0af17f055780db0 0xfbf1bf067f80ff8d 0x9fbf1bf067f80ff8

def z1064 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f087f80ff8f 0xffbf03f087f80ff8

def z1065 : W := mkw 0x037fc0a07b6a000f 0x0037fc0a07b6a000 0xe7ffc0f07fff000e 0x7e7ffc0f07fff000

def z1066 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbe03c007f80ff8c 0x8fbe03c007f80ff8

def z1067 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78e30f87c70fc7f 0xff78e30f87c70fc7

def z1068 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x63ed80007fff000c 0x763ed80007fff000

def z1069 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xc3ffc0007dff0008 0x6c3ffc0007dff000

def z1070 : W := mkw 0x037bc0005b2a000f 0x0037bc0005b2a000 0x839240001fbf0008 0x0839240001fbf000

def z1071 : W := mkw 0x8000044a000462d0 0xa8000044a000462d 0x5c6dacce0000e3f3 0x85c6dacce0000e3f

def z1072 : W := mkw 0x0af03e005700d208 0x80af03e005700d20 0xfbe03c007e00ff8d 0x9fbe03c007e00ff8

def z1073 : W := mkw 0x0af1ff05578adb0b 0xc0af1ff05578adb0 0xfbf1ff0fff8fff8d 0xdfbf1ff0fff8fff8

def z1074 : W := mkw 0x058e3af02c70b464 0x3058e3af02c70b46 0xff8e3ff07c70fc7f 0xaff8e3ff07c70fc7

def z1075 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc6dbcce624cffff 0xffc6dbcce624cfff

def z1076 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78fb0fe7c70fc7e 0xef78fb0fe7c70fc7

def z1077 : W := mkw 0x048430502c70b464 0x3048430502c70b46 0x938010007c70fc7c 0x0938010007c70fc7

def z1078 : W := mkw 0x8020044a420462d0 0xa8020044a420462d 0x7c6dacce6200e3f7 0xf7c6dacce6200e3f

def z1079 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacce6200e3f7 0x97c6dacce6200e3f

def z1080 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3f240007fff000c 0x1e3f240007fff000

def z1081 : W := mkw 0x027480007b6a000f 0x0027480007b6a000 0x839000007fff000c 0x0839000007fff000

def z1082 : W := mkw 0x4000011880950db0 0x44000011880950db 0xf07fd33983ff1fff 0xff07fd33983ff1ff

def z1083 : W := mkw 0x850fc0fa287e24f7 0x3850fc0fa287e24f 0x040fc0fe007f0072 0x6040fc0fe007f007

def z1084 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f39ff80ff8f 0x9fbf03f39ff80ff8

def z1085 : W := mkw 0x4080311884959db0 0x44080311884959db 0x100033398000fff3 0x8100033398000fff

def z1086 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0xfc7dbfce624ce3f7 0xffc7dbfce624ce3f

def z1087 : W := mkw 0x8024844a6a6c62d6 0xa8024844a6a6c62d 0x7c6dacce7e7ce3ff 0xf7c6dacce7e7ce3f

def z1088 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xeffdbfff80000003 0x9effdbfff8000000

def z1089 : W := mkw 0x0ad03f001580db08 0xc0ad03f001580db0 0xfb903f007d80ff8d 0x8fb903f007d80ff8

def z1090 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e33f07c70fc7f 0xbf79e33f07c70fc7

def z1091 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xf3ffe0007fffe00c 0xff3ffe0007fffe00

def z1092 : W := mkw 0x0080300004009000 0x0008030000400900 0xf38030007c40fc7e 0xaf38030007c40fc7

def z1093 : W := mkw 0x00a035004680db00 0xc00a035004680db0 0xfbf03f007f80ff8d 0x9fbf03f007f80ff8

def z1094 : W := mkw 0x018e30402c60b044 0x2018e30402c60b04 0xf78e30c07c70fc7e 0xaf78e30c07c70fc7

def z1095 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xcfffffff80000002 0x6cfffffff8000000

def z1096 : W := mkw 0x018e30102c709424 0x0018e30102c70942 0xf38e30307c70fc7e 0xaf38e30307c70fc7

def z1097 : W := mkw 0x03db7aa504009000 0x003db7aa50400900 0xeffffffffc00e003 0xfeffffffffc00e00

def z1098 : W := mkw 0x02514a0500000000 0x002514a050000000 0xec7fffff80000003 0xfec7fffff8000000

def z1099 : W := mkw 0x035fc000396a000f 0x0035fc000396a000 0xe3ffc0001dff0008 0x7e3ffc0001dff000

def z1100 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbe03f007c00ff8d 0x8fbe03f007c00ff8

def z1101 : W := mkw 0x4000011880950db0 0x44000011880950db 0xf8727f3983ff1fff 0xff8727f3983ff1ff

def z1102 : W := mkw 0x4000011880950db0 0x44000011880950db 0xb41fd3ff83ff1fff 0xfb41fd3ff83ff1ff

def z1103 : W := mkw 0x058e3af52c70b464 0x3058e3af52c70b46 0xff8e3cf67c70fc7e 0xaff8e3cf67c70fc7

def z1104 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ef80007fff000c 0x2e3ef80007fff000

def z1105 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0x839fc0007fff000c 0x6839fc0007fff000

def z1106 : W := mkw 0x48803fbd8495dfb0 0xc48803fbd8495dfb 0x1c003fff8000fff3 0x81c003fff8000fff

def z1107 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0x4fffefff80000003 0x74fffefff8000000

def z1108 : W := mkw 0x037bc0005b2a000f 0x0037bc0005b2a000 0xa3f3c0001fff000c 0x7a3f3c0001fff000

def z1109 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffd331ffff000c 0x7e3ffd331ffff000

def z1110 : W := mkw 0x448031b884959db0 0x5448031b884959db 0x1000133980001ff3 0x81000133980001ff

def z1111 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf03f007fffff8d 0x9fbf03f007fffff8

def z1112 : W := mkw 0x037fc4007b6a420f 0x8037fc4007b6a420 0xffffecce7fffe38f 0xfffffecce7fffe38

def z1113 : W := mkw 0x058eb0f02c78b466 0x3058eb0f02c78b46 0xf78fb0f07c7cfc7e 0xef78fb0f07c7cfc7

def z1114 : W := mkw 0x4000011880950db0 0x44000011880950db 0xbc127fff83ff1fff 0xfbc127fff83ff1ff

def z1115 : W := mkw 0x4000011880950db0 0x44000011880950db 0xf3925339ffff1fff 0xff3925339ffff1ff

def z1116 : W := mkw 0x4bdb7bb595919d28 0x44bdb7bb595919d2 0x839253319db31c08 0x0839253319db31c0

def z1117 : W := mkw 0x037bc0005b2a000f 0x0037bc0005b2a000 0xe3f3c0007fbf000c 0x5e3f3c0007fbf000

def z1118 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbfdbf007f80ff8d 0xffbfdbf007f80ff8

def z1119 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf79e73f1fc70fc7e 0xaf79e73f1fc70fc7

def z1120 : W := mkw 0x0af0bf00578adb0b 0xc0af0bf00578adb0 0xfbf03f007f8fff8d 0x9fbf03f007f8fff8

def z1121 : W := mkw 0x035b40001922000d 0x0035b40001922000 0xe3ffc0001fff000c 0x7e3ffc0001fff000

def z1122 : W := mkw 0xc024855ae2dd6ff2 0xec024855ae2dd6ff 0x10000000624cfff4 0x010000000624cfff

def z1123 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x578c20c07c00fc70 0x0578c20c07c00fc7

def z1124 : W := mkw 0x050e00502c70b464 0x3050e00502c70b46 0xf38e10307c70fc7e 0xaf38e10307c70fc7

def z1125 : W := mkw 0x037fc0407b6a204f 0x2037fc0407b6a204 0xffffecce7fffe07f 0xfffffecce7fffe07

def z1126 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0x978230f07c70fc7e 0x8978230f07c70fc7

def z1127 : W := mkw 0x008034000400d200 0x8008034000400d20 0xfb803c007c00ff8d 0x8fb803c007c00ff8

def z1128 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x7c6dacce63ffe3ff 0xf7c6dacce63ffe3f

def z1129 : W := mkw 0x058e30f02c70b464 0x3058e30f02c70b46 0xf78c30f07c00fc7e 0x8f78c30f07c00fc7

def z1130 : W := mkw 0x037fc0007b6a000f 0x0037fc0007b6a000 0xe3ffd3007fff000d 0xfe3ffd3007fff000

def z1131 : W := mkw 0x035fc000396a000f 0x0035fc000396a000 0xa39fc0001fff000c 0x7a39fc0001fff000

def z1132 : W := mkw 0x035b40001922000d 0x0035b40001922000 0x839240001fff000c 0x0839240001fff000

def z1133 : W := mkw 0x035b4aa500000000 0x0035b4aa50000000 0x6c7fefff80000003 0xf6c7fefff8000000

def z1134 : W := mkw 0x8024844262486242 0xa802484426248624 0x7c6dacc66240e3f7 0xb7c6dacc66240e3f

def z1135 : W := mkw 0x4000011880950db0 0x44000011880950db 0xf41e73f983ff1fff 0xff41e73f983ff1ff

def z1136 : W := mkw 0x018a30a000000000 0x0018a30a00000000 0xefffffff80000003 0xfefffffff8000000

def z1137 : W := mkw 0x035fc000396a000f 0x0035fc000396a000 0xe39fc0007dff000c 0x6e39fc0007dff000

def z1138 : W := mkw 0x0270050053804b08 0xc0270050053804b0 0xfbf03f007f80ff8d 0x9fbf03f007f80ff8

def z1139 : W := mkw 0x0020040842044290 0x8002004084204429 0x7c6dacce624ce3f7 0xf7c6dacce624ce3f

def z1140 : W := mkw 0x08a035005780db08 0xc08a035005780db0 0xf39033007f80ff8d 0x9f39033007f80ff8

def z1141 : W := mkw 0x450e00f8a87524f4 0x3450e00f8a87524f 0x040e00f0007f0072 0x2040e00f0007f007

def z1142 : W := mkw 0x03db7aa504009000 0x003db7aa50400900 0xffffffff8000fc03 0xfffffffff8000fc0

def z1143 : W := mkw 0x0af03f005780db08 0xc0af03f005780db0 0xfbf23f007ff0ff8d 0xbfbf23f007ff0ff8

def z1144 : W := mkw 0x03db7aa500000000 0x003db7aa50000000 0xefffffff8380000f 0xfefffffff8380000

def z1145 : W := mkw 0x450e00f8a87524f4 0x3450e00f8a87524f 0x040e00f980700072 0x2040e00f98070007

def z1146 : W := mkw 0x8024844a624c62d2 0xa8024844a624c62d 0x5c6dacce624ce3f7 0x85c6dacce624ce3f

def z1147 : W := mkw 0x0af1ff00578adb0b 0xc0af1ff00578adb0 0xfbf3ff007fffff8d 0xffbf3ff007fffff8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z8])],[(0,[z0,z1,z2,z3,z4,z9,z6]),(1,[z10,z1,z11,z3,z4,z6]),(0,[z12,z0,z1,z13,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z4,z16,z6]),(1,[z17,z0,z1,z2,z4,z6]),(1,[z0,z1,z2,z4,z6,z18]),(0,[z0,z1,z2,z3,z4,z19,z6])],[(0,[z0,z1,z2,z3,z4,z20,z6]),(1,[z21,z1,z2,z3,z4,z6]),(1,[z0,z1,z22,z3,z4,z6]),(0,[z0,z1,z23,z2,z3,z4,z6])],[(0,[z24,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z25,z4,z6]),(0,[z0,z1,z13,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z26,z6])],[(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z28,z6])],[(0,[z29,z0,z1,z2,z3,z4,z6]),(0,[z0,z30,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z31,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z32]),(0,[z33,z0,z1,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z34])],[(1,[z0,z1,z2,z35,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z2,z3,z4,z6]),(0,[z0,z38,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z3,z4,z6,z40]),(0,[z0,z1,z2,z41,z3,z4,z6]),(1,[z0,z1,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z6])]],
   [[(0,[z44,z0,z1,z45,z3,z4,z6]),(0,[z0,z1,z46,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z48,z6]),(0,[z0,z1,z2,z3,z4,z6,z49]),(0,[z0,z1,z2,z3,z4,z50,z6]),(0,[z0,z1,z2,z51,z3,z4,z6]),(0,[z0,z1,z52,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z53,z4,z6]),(0,[z0,z1,z2,z54,z4,z55,z6]),(0,[z56,z0,z1,z2,z3,z4,z6]),(0,[z57,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z58,z6,z59]),(1,[z0,z23,z2,z3,z4,z6])],[(0,[z12,z60,z1,z2,z3,z4,z6]),(0,[z61,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z62,z4,z6]),(0,[z63,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z64,z3,z4,z6])],[(0,[z44,z0,z1,z11,z3,z4,z6]),(1,[z44,z1,z65,z3,z4,z6]),(0,[z10,z1,z11,z2,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z67,z4,z6]),(0,[z0,z1,z68,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z69,z4,z6]),(0,[z70,z0,z1,z71,z3,z4,z6]),(0,[z72,z0,z1,z2,z4,z6,z73]),(0,[z0,z1,z74,z2,z3,z4,z6])],[(0,[z75,z0,z1,z2,z76,z4,z6]),(0,[z0,z1,z2,z3,z77,z4,z6]),(0,[z78,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z79,z3,z80,z4,z6]),(0,[z81,z0,z1,z2,z3,z4,z6])],[],[(1,[z0,z1,z2,z82,z4,z6]),(0,[z83,z84,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z85,z6]),(0,[z0,z1,z86,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z87]),(0,[z0,z1,z2,z3,z4,z88,z6])],[(1,[z84,z1,z2,z54,z4,z6]),(0,[z0,z1,z2,z3,z4,z89,z6]),(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z90,z0,z1,z2,z3,z4,z6]),(0,[z0,z91,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z92]),(0,[z0,z1,z2,z3,z4,z93,z6])],[(0,[z94,z0,z45,z2,z3,z4,z6]),(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z75,z0,z1,z3,z4,z96,z6]),(1,[z70,z0,z1,z3,z97,z6])],[(1,[z0,z1,z2,z3,z4,z98]),(0,[z0,z1,z2,z99,z3,z4,z6])],[(0,[z100,z0,z1,z2,z101,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z4,z59])],[(0,[z104,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z105,z6]),(0,[z106,z0,z1,z2,z3,z4,z6]),(0,[z107,z0,z1,z2,z3,z4,z108]),(0,[z0,z1,z2,z109,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z110])],[(0,[z0,z1,z2,z3,z111,z4,z6])],[(0,[z0,z1,z112,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z39]),(0,[z100,z0,z1,z2,z3,z4,z6]),(1,[z75,z0,z1,z80,z4,z6]),(0,[z0,z1,z3,z113,z4,z97,z6]),(0,[z0,z1,z2,z3,z4,z114,z6])],[(0,[z1,z2,z3,z4,z108,z6,z39]),(0,[z115,z0,z1,z2,z3,z4,z6]),(0,[z12,z0,z1,z2,z101,z4,z6]),(0,[z0,z1,z2,z3,z4,z116,z6]),(1,[z117,z1,z2,z3,z4,z6])]],
   [[(0,[z118,z0,z1,z2,z3,z4,z6]),(0,[z94,z0,z1,z2,z119,z4,z6])],[(0,[z120,z0,z1,z2,z3,z4,z6]),(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z75,z0,z1,z2,z80,z4,z6]),(0,[z122,z0,z1,z2,z3,z4,z6])],[(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z12,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z124,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z125])],[(1,[z0,z1,z2,z3,z4,z126]),(0,[z0,z1,z2,z3,z127,z4,z6]),(0,[z0,z1,z2,z3,z4,z98,z6]),(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z129]),(0,[z0,z1,z2,z130,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z131,z6]),(1,[z132,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z133]),(0,[z0,z1,z2,z3,z4,z134,z6])],[(0,[z135,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z136,z4,z6]),(0,[z0,z1,z2,z137,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z108]),(0,[z0,z1,z2,z3,z4,z6,z138]),(0,[z0,z1,z2,z3,z4,z6,z139]),(0,[z0,z1,z140,z2,z3,z4,z6])],[(0,[z141,z0,z1,z2,z3,z4,z6]),(0,[z75,z0,z1,z2,z54,z4,z6]),(0,[z0,z142,z1,z2,z3,z4,z6]),(0,[z0,z1,z52,z3,z4,z96,z6]),(0,[z0,z1,z2,z3,z143,z6,z59])],[(0,[z0,z1,z2,z3,z4,z144,z6]),(0,[z0,z1,z2,z145,z146,z4,z6]),(0,[z147,z21,z1,z2,z3,z4,z6]),(0,[z147,z0,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z148]),(0,[z0,z1,z2,z3,z4,z6,z149]),(0,[z150,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z151,z2,z3,z4,z6])]],
   [[(0,[z0,z152,z2,z3,z4,z58,z6]),(0,[z0,z1,z153,z79,z3,z4,z6])],[(0,[z154,z155,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z156,z3,z4,z6]),(0,[z0,z1,z71,z157,z3,z4,z6]),(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z159,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z160]),(0,[z75,z0,z1,z2,z4,z161,z6]),(0,[z0,z1,z2,z3,z4,z162,z6])],[(0,[z0,z163,z1,z2,z3,z4,z6]),(0,[z147,z0,z2,z3,z4,z164,z6]),(0,[z165,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z166])],[(0,[z0,z167,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z4,z169,z6]),(0,[z0,z1,z170,z2,z3,z4,z6])],[(0,[z171,z0,z152,z2,z3,z4,z6]),(0,[z172,z0,z1,z2,z3,z4,z6])],[(0,[z154,z0,z152,z2,z3,z4,z6]),(0,[z0,z2,z157,z3,z146,z4,z6]),(0,[z0,z173,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z174]),(0,[z175,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z176]),(0,[z0,z1,z177,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z3,z4,z174]),(0,[z0,z1,z2,z3,z178,z4,z6]),(0,[z0,z179,z1,z2,z3,z58,z6]),(0,[z70,z75,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z180,z6])],[(0,[z83,z0,z1,z137,z3,z4,z6]),(0,[z0,z2,z3,z181,z4,z164,z6]),(0,[z0,z1,z2,z3,z4,z182,z6]),(0,[z0,z1,z2,z3,z4,z143,z133])],[(0,[z0,z1,z2,z76,z4,z55,z6]),(0,[z0,z1,z2,z183,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z184,z6]),(0,[z0,z1,z2,z3,z185,z4,z6]),(0,[z0,z1,z2,z3,z103,z143,z6])],[(0,[z0,z186,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z187,z4,z6]),(0,[z0,z1,z2,z4,z169,z97,z6]),(0,[z0,z1,z2,z3,z4,z6,z188])],[(1,[z189,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z190,z3,z4,z6]),(0,[z191,z0,z1,z2,z3,z4,z6])],[(0,[z83,z0,z192,z2,z3,z4,z6]),(1,[z0,z1,z2,z193,z4,z6]),(0,[z0,z1,z2,z3,z4,z194,z6])],[(0,[z44,z1,z2,z3,z195,z4,z6]),(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z83,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z197,z4,z6]),(0,[z198,z0,z1,z2,z3,z4,z6])],[(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z200,z6]),(0,[z201,z84,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z202,z4,z6])]],
   [[(0,[z10,z0,z1,z2,z203,z4,z6]),(0,[z10,z1,z2,z3,z4,z6,z39]),(0,[z204,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z205,z6]),(0,[z206,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z208,z0,z1,z2,z3,z4,z6])],[(0,[z117,z1,z2,z3,z4,z97,z6])],[],[(0,[z209,z0,z1,z2,z3,z4,z6]),(0,[z83,z0,z210,z2,z3,z4,z6]),(0,[z211,z0,z1,z2,z3,z4,z212]),(0,[z0,z1,z2,z3,z4,z6,z213])],[(0,[z0,z1,z11,z2,z3,z4,z6]),(0,[z0,z1,z2,z76,z3,z4,z6]),(0,[z83,z0,z1,z2,z3,z4,z98]),(0,[z214,z0,z1,z2,z3,z4,z6]),(0,[z94,z0,z2,z3,z146,z4,z6]),(0,[z0,z215,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z194,z55,z6]),(0,[z0,z1,z2,z3,z4,z6,z73])],[(0,[z0,z1,z2,z3,z4,z6,z216]),(0,[z0,z1,z217,z2,z3,z4,z6])],[(0,[z218,z0,z1,z2,z3,z4,z6]),(0,[z219,z0,z1,z2,z3,z4,z6])],[(0,[z1,z2,z65,z3,z4,z6,z39]),(0,[z0,z1,z2,z220,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z221,z6]),(0,[z147,z0,z1,z2,z124,z4,z6]),(0,[z222,z0,z1,z2,z3,z4,z6]),(0,[z223,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z224,z4,z6]),(0,[z107,z1,z2,z3,z4,z108,z6]),(0,[z225,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z226,z4,z6]),(0,[z0,z1,z153,z2,z227,z4,z6]),(0,[z0,z1,z2,z228,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z96,z6])],[(0,[z0,z1,z2,z3,z4,z229,z6]),(0,[z0,z1,z2,z3,z227,z4,z6])],[(0,[z154,z84,z1,z2,z3,z4,z6]),(1,[z94,z0,z45,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z230]),(0,[z231,z0,z1,z2,z3,z4,z6]),(0,[z211,z232,z1,z2,z3,z4,z6])],[(0,[z155,z0,z179,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z233,z6]),(0,[z234,z0,z1,z2,z3,z4,z6]),(1,[z66,z1,z2,z3,z195,z6]),(0,[z0,z1,z2,z3,z235,z4,z6])],[(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z161,z6,z73])],[(0,[z0,z1,z2,z3,z4,z6,z237]),(0,[z238,z0,z1,z2,z3,z4,z6]),(1,[z81,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z239,z6]),(0,[z0,z1,z2,z3,z4,z240,z6])],[(0,[z0,z1,z241,z2,z3,z4,z6]),(0,[z1,z2,z76,z3,z195,z4,z6]),(0,[z242,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z147,z0,z1,z2,z3,z181,z6]),(0,[z0,z1,z2,z3,z4,z133,z59])],[(0,[z0,z179,z152,z2,z3,z4,z6]),(0,[z0,z1,z2,z243,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z244,z6])],[(0,[z0,z1,z2,z145,z54,z4,z6]),(0,[z0,z1,z22,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z181,z6]),(0,[z0,z1,z2,z3,z245,z4,z6])],[(0,[z83,z66,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z246,z4,z6]),(0,[z0,z1,z2,z3,z4,z247,z6]),(0,[z0,z1,z2,z3,z248,z4,z6]),(0,[z249,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z250,z3,z4,z6]),(0,[z251,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z143,z164]),(0,[z252,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z253,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z254])],[(0,[z255,z0,z1,z2,z3,z4,z6]),(0,[z256,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z257]),(0,[z0,z1,z2,z3,z4,z6,z258]),(0,[z0,z1,z2,z3,z4,z259,z6]),(0,[z0,z260,z1,z2,z3,z4,z6])],[(0,[z261,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z192,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z83,z0,z1,z2,z3,z195,z6]),(0,[z262,z0,z1,z2,z3,z4,z6]),(1,[z263,z0,z1,z2,z4,z6])],[(0,[z154,z171,z1,z2,z3,z4,z6]),(0,[z264,z0,z1,z2,z3,z4,z6]),(0,[z44,z1,z2,z65,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z265,z6]),(0,[z0,z266,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z6,z59]),(0,[z0,z1,z2,z3,z4,z267,z6]),(0,[z0,z1,z2,z268,z3,z4,z6])],[(0,[z269,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z137,z3,z4,z6]),(0,[z83,z107,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z270,z6]),(0,[z75,z271,z0,z2,z3,z4,z6])],[(0,[z155,z0,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z3,z4,z272,z6]),(0,[z273,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z52,z2,z3,z4,z212]),(0,[z0,z2,z3,z4,z6,z34,z59])],[(0,[z0,z1,z2,z3,z274,z4,z6]),(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z276,z0,z1,z2,z3,z4,z6])],[(0,[z1,z2,z76,z3,z54,z4,z6]),(0,[z0,z1,z2,z3,z4,z277,z6]),(0,[z0,z1,z2,z3,z278,z4,z6])],[(0,[z279,z0,z1,z2,z3,z4,z6]),(1,[z0,z192,z2,z3,z4,z6]),(0,[z100,z0,z2,z3,z146,z4,z6]),(0,[z0,z1,z153,z2,z79,z4,z6]),(0,[z211,z0,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z212]),(0,[z0,z1,z2,z280,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z281,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z282,z6]),(0,[z201,z0,z1,z2,z146,z4,z6]),(0,[z0,z1,z283,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z284,z4,z6]),(0,[z0,z1,z2,z3,z285,z4,z6]),(0,[z286,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z287,z0,z1,z2,z3,z4,z6]),(0,[z288,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z289,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z290,z6]),(0,[z291,z0,z1,z2,z3,z4,z6])],[(0,[z0,z292,z1,z2,z3,z4,z6])],[(0,[z0,z152,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z3,z4,z293,z6]),(0,[z294,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z295,z6])],[(0,[z0,z1,z296,z2,z3,z4,z6]),(1,[z0,z210,z2,z3,z4,z6]),(1,[z0,z1,z2,z67,z4,z6])],[(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z189,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z298,z4,z6])],[(0,[z0,z1,z2,z3,z4,z299,z6]),(0,[z0,z1,z2,z3,z4,z300,z6]),(0,[z0,z1,z301,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z302,z6]),(0,[z303,z0,z1,z2,z3,z4,z6])],[(0,[z1,z11,z2,z3,z195,z4,z6]),(0,[z0,z1,z2,z3,z304,z4,z6]),(1,[z0,z1,z2,z3,z305,z6]),(0,[z0,z1,z2,z3,z4,z306,z6]),(1,[z1,z2,z3,z4,z88,z6]),(0,[z307,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z308,z4,z6]),(0,[z0,z309,z1,z2,z3,z4,z6])],[(0,[z1,z152,z2,z3,z4,z85,z6]),(0,[z310,z0,z1,z2,z3,z4,z6]),(0,[z12,z94,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z305,z4,z6])],[(0,[z0,z1,z2,z3,z4,z108,z6]),(0,[z0,z1,z45,z52,z3,z4,z6]),(0,[z0,z311,z1,z2,z3,z4,z6])],[(0,[z155,z0,z2,z3,z4,z58,z6]),(0,[z312,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z101,z145,z4,z6]),(1,[z271,z0,z2,z3,z4,z6]),(0,[z313,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z314]),(0,[z0,z1,z2,z3,z4,z143,z6])],[(0,[z44,z0,z1,z2,z3,z4,z6]),(0,[z83,z44,z1,z2,z3,z4,z6]),(0,[z83,z1,z2,z76,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z3,z315,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z316])],[(0,[z317,z0,z1,z2,z3,z4,z6]),(0,[z318,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z45,z2,z3,z4,z6]),(0,[z319,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z320,z6]),(0,[z0,z1,z2,z3,z4,z6,z321]),(0,[z0,z1,z2,z322,z3,z4,z6]),(0,[z0,z1,z71,z3,z113,z4,z6]),(0,[z323,z0,z1,z2,z3,z4,z6]),(0,[z276,z0,z1,z3,z4,z6,z73])],[(0,[z44,z10,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z324]),(0,[z325,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z326]),(0,[z211,z0,z1,z3,z4,z6,z212])]],
   [[(0,[z0,z1,z2,z3,z4,z327,z6]),(0,[z189,z0,z1,z2,z3,z4,z39]),(1,[z0,z1,z2,z3,z4,z302]),(0,[z0,z1,z328,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z329,z6])],[(0,[z1,z152,z2,z3,z4,z6,z39]),(0,[z0,z1,z71,z65,z3,z4,z6]),(0,[z330,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z331,z2,z3,z4,z6]),(0,[z0,z1,z332,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z333,z4,z6]),(0,[z0,z1,z2,z145,z3,z4,z6])],[(0,[z155,z0,z1,z334,z3,z4,z6]),(0,[z0,z1,z2,z335,z3,z4,z6]),(1,[z0,z1,z2,z3,z15,z6]),(0,[z0,z1,z79,z3,z4,z96,z6]),(0,[z336,z0,z1,z2,z145,z4,z6])],[(0,[z84,z0,z1,z2,z146,z4,z6]),(0,[z94,z186,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z337,z6])],[(0,[z0,z1,z2,z338,z3,z4,z6]),(0,[z0,z179,z2,z3,z181,z4,z6])],[(0,[z0,z1,z2,z3,z4,z143,z39]),(0,[z0,z1,z3,z4,z96,z6,z212])],[(0,[z0,z1,z2,z339,z3,z4,z6]),(0,[z107,z0,z86,z2,z3,z4,z6]),(0,[z0,z1,z2,z193,z3,z4,z6]),(0,[z340,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z341,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z342,z4,z6]),(0,[z0,z1,z343,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z344,z6]),(0,[z0,z1,z2,z345,z3,z4,z6])],[(0,[z154,z0,z1,z2,z3,z4,z126]),(0,[z0,z1,z157,z3,z4,z97,z6]),(0,[z0,z1,z2,z3,z4,z346,z6]),(0,[z347,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z348,z6])],[(0,[z44,z1,z152,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z349]),(0,[z0,z1,z2,z3,z350,z4,z6]),(0,[z232,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z351,z3,z4,z6]),(1,[z0,z1,z2,z145,z227,z6])],[(0,[z10,z0,z1,z65,z3,z4,z6]),(0,[z0,z1,z2,z352,z3,z4,z6]),(1,[z0,z1,z2,z119,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z353]),(0,[z70,z0,z1,z2,z3,z97,z6]),(0,[z0,z1,z2,z354,z3,z4,z6])],[(0,[z355,z0,z1,z2,z3,z4,z6]),(0,[z60,z0,z1,z2,z3,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z356,z2,z3,z4,z6])],[(0,[z10,z0,z1,z157,z3,z4,z6]),(1,[z201,z1,z2,z76,z4,z6]),(0,[z357,z94,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z358,z4,z6]),(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z360]),(0,[z0,z1,z2,z3,z103,z4,z6])],[(0,[z0,z38,z1,z2,z3,z4,z108]),(0,[z0,z1,z157,z3,z4,z6,z212]),(0,[z0,z361,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z362,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z363,z4,z6]),(0,[z364,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z365,z2,z3,z4,z6]),(0,[z0,z1,z2,z366,z3,z4,z6]),(0,[z0,z1,z367,z2,z3,z4,z6]),(0,[z0,z368,z1,z2,z3,z4,z6])],[(0,[z0,z1,z369,z2,z3,z4,z6]),(0,[z189,z107,z1,z2,z3,z4,z6]),(0,[z0,z2,z101,z3,z146,z4,z6]),(0,[z0,z1,z2,z3,z370,z4,z6]),(0,[z75,z0,z1,z2,z227,z4,z6])],[(0,[z371,z0,z1,z2,z3,z4,z6]),(0,[z84,z1,z152,z2,z3,z4,z6]),(0,[z1,z11,z2,z65,z3,z4,z6]),(0,[z201,z0,z1,z2,z54,z4,z6]),(0,[z0,z1,z2,z372,z3,z4,z6]),(0,[z0,z1,z2,z373,z3,z4,z6])],[(0,[z0,z1,z374,z2,z3,z4,z6]),(0,[z107,z1,z2,z3,z195,z4,z6]),(0,[z214,z94,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z375,z146,z4,z6]),(0,[z0,z1,z376,z2,z3,z4,z6]),(0,[z377,z0,z1,z2,z3,z4,z6]),(1,[z286,z0,z1,z2,z3,z59]),(0,[z0,z1,z2,z3,z4,z6,z378])],[(0,[z0,z1,z2,z3,z4,z379,z6]),(1,[z186,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z380,z6]),(0,[z286,z0,z1,z2,z3,z4,z143])],[(0,[z84,z0,z1,z2,z76,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z18])],[(0,[z14,z0,z152,z2,z3,z4,z6]),(0,[z154,z0,z1,z2,z3,z4,z174]),(0,[z83,z0,z1,z2,z67,z4,z6]),(0,[z0,z1,z2,z381,z3,z4,z6]),(0,[z0,z1,z42,z2,z3,z4,z6]),(0,[z14,z0,z1,z2,z275,z4,z6]),(1,[z1,z2,z3,z4,z194,z6])],[(0,[z0,z1,z2,z3,z382,z4,z6]),(0,[z383,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z384,z4,z6]),(0,[z385,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z387,z3,z4,z6]),(0,[z388,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z389])],[(0,[z0,z1,z390,z2,z3,z4,z6]),(0,[z155,z0,z1,z241,z3,z4,z6]),(0,[z84,z1,z2,z3,z195,z4,z6]),(0,[z83,z1,z2,z3,z4,z85,z6]),(0,[z0,z1,z2,z3,z4,z6,z391]),(0,[z0,z1,z392,z2,z3,z4,z6])],[(0,[z0,z1,z2,z203,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z393]),(0,[z66,z0,z1,z2,z3,z85,z6])],[(0,[z394,z0,z1,z2,z3,z4,z6]),(0,[z0,z395,z1,z2,z3,z4,z6]),(0,[z0,z396,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z397,z3,z4,z6]),(1,[z398,z1,z2,z3,z4,z6])],[(0,[z399,z0,z1,z2,z3,z4,z6]),(0,[z155,z0,z1,z2,z400,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z401]),(0,[z0,z1,z402,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z403,z4,z6]),(0,[z0,z1,z71,z2,z3,z97,z6]),(0,[z0,z1,z2,z3,z4,z6,z404]),(0,[z336,z0,z1,z2,z4,z55,z6]),(0,[z0,z1,z2,z145,z3,z55,z6]),(0,[z0,z1,z3,z4,z6,z405,z73]),(0,[z406,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z407,z3,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z302]),(0,[z0,z1,z2,z3,z4,z408,z6]),(0,[z0,z1,z409,z2,z3,z4,z6]),(0,[z410,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z411,z2,z3,z4,z6])],[(0,[z14,z0,z2,z3,z4,z6,z133])],[(0,[z1,z152,z11,z2,z3,z4,z6]),(0,[z1,z152,z2,z76,z3,z4,z6]),(0,[z0,z1,z2,z412,z3,z4,z6]),(0,[z413,z0,z1,z2,z3,z4,z6]),(0,[z414,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z108,z143]),(0,[z0,z1,z153,z2,z146,z4,z6]),(0,[z70,z0,z1,z2,z3,z4,z6]),(0,[z211,z292,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z415,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z146,z4,z6]),(0,[z0,z1,z2,z79,z3,z4,z6]),(0,[z398,z1,z2,z3,z4,z55,z6]),(0,[z72,z0,z1,z2,z3,z4,z73])],[(0,[z107,z1,z2,z3,z54,z4,z6]),(0,[z83,z1,z2,z3,z4,z6,z39]),(1,[z12,z0,z2,z101,z4,z6]),(1,[z0,z1,z2,z226,z4,z6]),(0,[z263,z0,z1,z2,z4,z6,z212]),(0,[z0,z1,z416,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z82,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z417]),(0,[z418,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z417]),(0,[z0,z1,z2,z3,z419,z4,z6]),(0,[z0,z1,z45,z3,z4,z97,z6]),(0,[z420,z0,z1,z2,z3,z4,z6])],[(1,[z171,z152,z2,z3,z4,z6]),(0,[z14,z311,z1,z2,z3,z4,z6]),(0,[z421,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z375,z4,z161])],[(0,[z0,z1,z422,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z423]),(0,[z0,z1,z2,z424,z3,z4,z6]),(0,[z425,z0,z1,z2,z3,z4,z6]),(0,[z12,z0,z2,z157,z3,z4,z6])],[(0,[z426,z0,z1,z2,z3,z4,z6]),(0,[z427,z0,z1,z2,z3,z4,z6]),(0,[z428,z0,z1,z2,z3,z4,z6]),(0,[z429,z0,z1,z2,z3,z4,z6]),(0,[z430,z0,z1,z2,z3,z4,z6]),(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z336,z0,z1,z2,z3,z4,z6])],[(0,[z84,z0,z1,z2,z54,z4,z6]),(0,[z84,z1,z2,z3,z54,z4,z6]),(0,[z201,z0,z1,z250,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z432]),(0,[z0,z1,z2,z3,z4,z433,z6]),(0,[z75,z0,z1,z2,z79,z4,z6])]],
   [[(0,[z154,z44,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z434]),(0,[z0,z45,z2,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z435]),(0,[z0,z1,z2,z3,z4,z6,z436])],[(0,[z10,z0,z1,z45,z3,z4,z6]),(0,[z0,z1,z45,z3,z4,z6,z212]),(0,[z0,z1,z2,z3,z437,z4,z6]),(1,[z336,z0,z1,z2,z55,z6])],[(0,[z0,z1,z2,z35,z3,z4,z6]),(0,[z398,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z438,z6]),(0,[z439,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z440,z4,z6]),(0,[z154,z155,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z97,z6])],[(0,[z441,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z11,z3,z4,z6]),(0,[z75,z0,z1,z157,z3,z4,z6]),(0,[z14,z0,z38,z2,z3,z4,z6]),(0,[z442,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z443,z4,z6]),(0,[z94,z0,z1,z157,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z444,z6]),(0,[z107,z1,z2,z65,z3,z4,z6])],[(0,[z155,z0,z1,z2,z35,z4,z6]),(0,[z445,z0,z1,z2,z3,z4,z6]),(0,[z201,z0,z1,z2,z101,z4,z6]),(0,[z446,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z447,z4,z6]),(1,[z260,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z153,z2,z76,z4,z6]),(0,[z0,z132,z1,z2,z3,z4,z6]),(0,[z0,z1,z71,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z448,z6]),(1,[z211,z0,z1,z3,z4,z212])],[(0,[z0,z1,z11,z79,z3,z4,z6]),(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z449,z3,z4,z6]),(1,[z266,z1,z2,z3,z4,z6]),(0,[z0,z1,z450,z2,z3,z4,z6])],[(0,[z0,z451,z1,z2,z3,z4,z6]),(0,[z12,z0,z2,z101,z3,z4,z6]),(0,[z0,z1,z452,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z4,z143])],[(0,[z155,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z339,z3,z4,z6]),(0,[z0,z2,z3,z4,z164,z6,z133])],[(0,[z453,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z195,z4,z6]),(0,[z0,z1,z454,z2,z3,z4,z6]),(0,[z0,z1,z2,z455,z3,z4,z6]),(0,[z456,z0,z1,z2,z3,z4,z6]),(1,[z72,z0,z1,z2,z4,z73])],[(0,[z0,z1,z2,z3,z4,z457,z6]),(0,[z458,z0,z1,z2,z3,z4,z6])],[(0,[z459,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z39,z59]),(0,[z460,z0,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z2,z3,z4,z96]),(0,[z0,z1,z2,z3,z461,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z462,z4,z6]),(0,[z14,z0,z1,z463,z3,z4,z6]),(0,[z464,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z153,z79,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z465])],[(0,[z0,z1,z52,z157,z3,z4,z6]),(0,[z357,z0,z1,z2,z3,z4,z6]),(0,[z211,z75,z0,z1,z3,z4,z6]),(0,[z466,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z467,z3,z4,z6]),(1,[z232,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z468,z6]),(0,[z66,z1,z2,z3,z195,z4,z6]),(0,[z469,z0,z1,z2,z3,z4,z6]),(0,[z14,z0,z2,z3,z181,z4,z6]),(1,[z90,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z470,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z471,z3,z4,z6]),(0,[z0,z1,z2,z472,z3,z4,z6]),(1,[z107,z1,z2,z3,z4,z108]),(0,[z0,z1,z2,z3,z4,z6,z473]),(1,[z292,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z474,z3,z4,z6])],[(0,[z171,z0,z1,z2,z3,z4,z6]),(0,[z10,z0,z1,z2,z82,z4,z6]),(0,[z0,z1,z2,z146,z4,z55,z6]),(0,[z0,z1,z2,z375,z3,z4,z73])],[(0,[z154,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z11,z3,z4,z97,z6]),(0,[z0,z1,z2,z3,z4,z475,z6]),(0,[z0,z1,z476,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z477,z4,z6]),(0,[z0,z1,z2,z3,z4,z478,z6]),(0,[z0,z1,z2,z3,z479,z4,z6]),(0,[z147,z0,z1,z2,z226,z4,z6]),(0,[z0,z1,z2,z3,z480,z4,z6])],[(0,[z83,z1,z11,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z481]),(0,[z0,z1,z2,z3,z4,z482,z6]),(0,[z483,z0,z1,z2,z3,z4,z6]),(0,[z214,z0,z2,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z484]),(1,[z0,z1,z372,z3,z4,z6]),(0,[z286,z0,z1,z2,z3,z103,z6])]],
   [[(0,[z485,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z145,z3,z227,z6])],[(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z487,z4,z6]),(0,[z0,z1,z157,z79,z3,z4,z6]),(0,[z12,z0,z1,z488,z3,z4,z6]),(0,[z0,z1,z2,z489,z3,z4,z6])],[(0,[z155,z1,z152,z2,z3,z4,z6]),(1,[z0,z1,z2,z203,z4,z6]),(0,[z0,z1,z153,z2,z54,z4,z6]),(0,[z0,z1,z2,z3,z490,z4,z6]),(0,[z0,z1,z2,z3,z197,z4,z6]),(0,[z491,z0,z1,z2,z3,z4,z6]),(0,[z492,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z54,z4,z6]),(0,[z201,z0,z1,z2,z76,z4,z6]),(0,[z0,z1,z493,z2,z3,z4,z6]),(0,[z494,z0,z1,z2,z3,z4,z6]),(0,[z81,z0,z1,z3,z4,z55,z6]),(0,[z286,z0,z1,z2,z3,z6,z59])],[(0,[z84,z0,z1,z2,z101,z4,z6]),(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z164,z59]),(0,[z1,z2,z3,z4,z143,z6,z389])],[(0,[z83,z0,z1,z2,z3,z4,z417]),(0,[z14,z0,z1,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z496,z6]),(0,[z288,z1,z2,z3,z4,z143,z6])],[(0,[z497,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z498,z6])],[(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z195,z4,z85,z6]),(1,[z147,z0,z2,z3,z58,z6]),(1,[z383,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z499,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z500,z6]),(0,[z189,z1,z2,z3,z4,z6,z39]),(0,[z501,z0,z1,z2,z3,z4,z6]),(0,[z0,z502,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z488,z3,z4,z6]),(0,[z0,z1,z2,z503,z3,z4,z6])],[(0,[z171,z1,z152,z2,z3,z4,z6]),(0,[z0,z1,z65,z3,z4,z97,z6]),(0,[z0,z1,z504,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z505,z4,z6]),(0,[z336,z75,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z506,z3,z4,z6])],[(0,[z0,z1,z2,z3,z400,z4,z6]),(0,[z0,z1,z2,z3,z4,z507,z6]),(0,[z0,z1,z2,z3,z4,z508,z6]),(0,[z0,z1,z509,z2,z3,z4,z6]),(0,[z0,z1,z510,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z511,z6]),(0,[z512,z0,z1,z2,z3,z4,z6])],[(0,[z513,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z514,z2,z3,z4,z6]),(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z438,z55,z6]),(1,[z0,z1,z3,z4,z6,z405]),(0,[z0,z1,z2,z3,z4,z6,z515]),(0,[z0,z1,z2,z3,z4,z6,z516])],[(0,[z0,z1,z517,z2,z3,z4,z6]),(0,[z518,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z0,z1,z2,z3,z113,z4,z6]),(0,[z0,z1,z520,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z521])],[(0,[z0,z1,z2,z522,z3,z4,z6]),(0,[z201,z107,z1,z2,z3,z4,z6])],[(0,[z107,z1,z152,z2,z3,z4,z6]),(0,[z83,z0,z1,z2,z443,z4,z6]),(0,[z1,z2,z3,z195,z4,z6,z39]),(0,[z147,z266,z1,z2,z3,z4,z6]),(0,[z0,z1,z52,z2,z3,z4,z96])]],
   [[(0,[z0,z1,z2,z3,z4,z523,z6]),(0,[z0,z1,z2,z65,z3,z4,z6]),(0,[z1,z2,z3,z54,z4,z6,z39]),(0,[z0,z1,z2,z3,z4,z6,z524]),(1,[z0,z1,z2,z4,z169,z6]),(0,[z0,z1,z2,z3,z4,z6,z59])],[(0,[z525,z0,z1,z2,z3,z4,z6]),(0,[z526,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z527,z3,z4,z6]),(0,[z0,z528,z1,z2,z3,z4,z6])],[(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z154,z66,z1,z2,z3,z4,z6]),(0,[z70,z0,z1,z2,z3,z113,z6])],[(0,[z530,z0,z1,z2,z3,z4,z6]),(0,[z531,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z157,z3,z4,z6]),(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z124,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z15,z6]),(0,[z0,z38,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z532,z3,z4,z6]),(0,[z1,z2,z3,z4,z88,z97,z6]),(0,[z0,z1,z2,z375,z3,z4,z161])],[(0,[z0,z1,z533,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z534,z4,z6]),(0,[z0,z535,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z536,z3,z4,z6]),(0,[z537,z0,z1,z2,z3,z4,z6]),(0,[z75,z0,z23,z2,z3,z4,z6])],[(0,[z0,z1,z2,z101,z375,z4,z6]),(0,[z0,z1,z538,z2,z3,z4,z6]),(0,[z0,z1,z2,z375,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z539,z6]),(0,[z0,z1,z2,z101,z4,z55,z6]),(1,[z0,z1,z3,z4,z438,z6]),(0,[z0,z1,z2,z3,z4,z6,z540])]],
   [[(0,[z0,z1,z2,z3,z541,z4,z6]),(0,[z0,z1,z2,z443,z3,z4,z6]),(0,[z75,z0,z1,z2,z146,z4,z6]),(0,[z0,z179,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z542,z6]),(0,[z75,z0,z1,z153,z3,z4,z6])],[(0,[z154,z107,z1,z2,z3,z4,z6]),(0,[z543,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z544,z6]),(0,[z0,z1,z2,z119,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z55,z6]),(0,[z0,z1,z2,z3,z545,z4,z6])],[(0,[z0,z1,z2,z3,z4,z546,z6])],[(0,[z0,z1,z45,z79,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z133])],[(0,[z547,z0,z1,z2,z3,z4,z6]),(0,[z147,z0,z1,z372,z3,z4,z6])],[(0,[z0,z1,z548,z2,z3,z4,z6]),(0,[z549,z0,z1,z2,z3,z4,z6])],[(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z72,z75,z0,z1,z2,z4,z6]),(0,[z336,z0,z1,z153,z2,z4,z6]),(0,[z551,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z552,z6]),(0,[z0,z1,z2,z3,z4,z553,z6]),(0,[z0,z1,z153,z2,z101,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z554,z4,z6]),(0,[z0,z1,z11,z71,z3,z4,z6]),(0,[z201,z1,z2,z76,z3,z4,z6]),(0,[z555,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z556,z4,z6]),(0,[z557,z0,z1,z2,z3,z4,z6])],[(0,[z83,z0,z1,z37,z3,z4,z6]),(0,[z0,z1,z2,z101,z3,z4,z6]),(1,[z14,z0,z2,z3,z4,z133]),(1,[z1,z2,z3,z4,z6,z389])],[(0,[z558,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z559]),(0,[z0,z1,z2,z3,z4,z6,z405])],[(0,[z560,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z562,z6]),(0,[z0,z1,z71,z2,z3,z113,z6]),(0,[z0,z1,z2,z3,z563,z4,z6])],[(0,[z0,z1,z2,z3,z564,z4,z6]),(0,[z0,z1,z2,z3,z565,z4,z6]),(0,[z336,z0,z1,z2,z3,z227,z6]),(1,[z0,z1,z2,z3,z103,z143])],[(0,[z0,z1,z2,z3,z4,z6,z566]),(0,[z0,z1,z2,z567,z3,z4,z6]),(0,[z214,z0,z1,z157,z3,z4,z6])],[(0,[z568,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z569,z3,z4,z6]),(0,[z0,z1,z570,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z571,z6])],[(0,[z572,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z189,z0,z1,z2,z3,z4,z108])],[(0,[z75,z0,z1,z3,z113,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z573])],[(1,[z154,z155,z2,z3,z4,z6]),(1,[z0,z179,z2,z3,z181,z6]),(0,[z0,z38,z1,z2,z3,z4,z133]),(1,[z0,z2,z3,z4,z6,z34])],[(0,[z0,z1,z2,z3,z4,z574,z6]),(0,[z154,z1,z11,z2,z3,z4,z6]),(0,[z154,z1,z2,z76,z3,z4,z6]),(0,[z0,z1,z2,z575,z3,z4,z6]),(0,[z14,z0,z1,z2,z193,z4,z6]),(0,[z0,z1,z2,z576,z3,z4,z6]),(0,[z577,z0,z1,z2,z3,z4,z6]),(1,[z406,z0,z2,z3,z4,z6])],[(0,[z75,z0,z1,z65,z3,z4,z6]),(0,[z0,z1,z2,z3,z578,z4,z6]),(0,[z0,z1,z2,z3,z4,z579,z6]),(0,[z0,z580,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z4,z55,z6]),(0,[z0,z581,z1,z2,z3,z4,z6])],[(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z583,z6]),(0,[z0,z1,z2,z584,z3,z4,z6]),(0,[z0,z1,z2,z463,z3,z4,z6])],[(0,[z0,z1,z2,z3,z585,z4,z6]),(0,[z0,z1,z2,z76,z145,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z586]),(0,[z262,z107,z0,z2,z3,z4,z6])],[(0,[z587,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z588,z6]),(0,[z0,z179,z1,z2,z3,z181,z6]),(0,[z589,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z590,z4,z6]),(1,[z357,z1,z2,z3,z4,z6]),(0,[z591,z0,z1,z2,z3,z4,z6]),(0,[z147,z0,z179,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z592,z4,z6])],[(0,[z0,z1,z152,z2,z3,z4,z6]),(0,[z593,z0,z1,z2,z3,z4,z6]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z595,z3,z4,z6]),(0,[z0,z1,z2,z3,z596,z4,z6]),(0,[z597,z0,z1,z2,z3,z4,z6]),(0,[z0,z598,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z599,z6])],[(0,[z600,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z601,z2,z3,z4,z6]),(1,[z0,z86,z2,z3,z4,z6]),(0,[z602,z0,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z153,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z603]),(0,[z72,z0,z1,z2,z375,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z604]),(0,[z0,z1,z2,z3,z4,z6,z605])],[(0,[z606,z0,z1,z2,z3,z4,z6]),(0,[z100,z0,z1,z2,z146,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z607]),(0,[z0,z608,z1,z2,z3,z4,z6])],[(0,[z609,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z146,z4,z6,z73])],[(0,[z14,z147,z0,z2,z3,z4,z6]),(0,[z0,z610,z1,z2,z3,z4,z6])],[(0,[z66,z1,z152,z2,z3,z4,z6]),(0,[z0,z1,z611,z2,z3,z4,z6]),(1,[z0,z1,z488,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z164])],[(0,[z0,z1,z2,z3,z4,z126,z6]),(0,[z201,z0,z1,z339,z3,z4,z6]),(0,[z12,z0,z1,z2,z146,z4,z6])]],
   [[(1,[z0,z1,z2,z275,z4,z6]),(0,[z0,z1,z79,z3,z113,z4,z6]),(0,[z0,z1,z2,z612,z3,z4,z6]),(0,[z0,z1,z2,z145,z227,z4,z6])],[(0,[z0,z1,z2,z3,z4,z613,z6]),(0,[z614,z0,z1,z2,z3,z4,z6]),(0,[z615,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z616,z2,z3,z4,z6]),(1,[z83,z1,z2,z3,z85,z6]),(0,[z0,z1,z2,z617,z3,z4,z6]),(0,[z72,z260,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z161])],[(0,[z618,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z334,z3,z4,z6]),(0,[z14,z155,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z619,z4,z6]),(0,[z94,z0,z1,z2,z197,z4,z6]),(1,[z100,z0,z2,z146,z4,z6]),(0,[z17,z0,z1,z2,z4,z97,z6])],[(0,[z147,z0,z1,z2,z3,z58,z6]),(0,[z0,z1,z2,z3,z4,z6,z620]),(0,[z0,z1,z2,z3,z621,z4,z6])],[(0,[z10,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z622,z4,z6]),(0,[z70,z0,z1,z79,z3,z4,z6]),(0,[z0,z1,z2,z375,z4,z161,z6])],[(0,[z623,z0,z1,z2,z3,z4,z6]),(0,[z624,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z58,z6]),(0,[z625,z0,z1,z2,z3,z4,z6])],[(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z627,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z628]),(0,[z629,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z83,z0,z1,z2,z3,z85,z6]),(0,[z214,z0,z1,z45,z3,z4,z6]),(0,[z271,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z153,z2,z80,z4,z6]),(0,[z630,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z631]),(0,[z0,z1,z2,z3,z80,z4,z6]),(0,[z0,z1,z2,z3,z4,z632,z6])],[(0,[z0,z1,z65,z79,z3,z4,z6]),(1,[z0,z1,z37,z3,z4,z6]),(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z634]),(0,[z66,z0,z1,z2,z3,z195,z6]),(0,[z635,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z636]),(1,[z0,z1,z2,z3,z4,z631]),(0,[z637,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z638,z4,z6]),(0,[z639,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z640,z4,z6]),(0,[z336,z0,z1,z2,z3,z55,z6])],[(0,[z0,z1,z2,z641,z3,z4,z6]),(0,[z0,z1,z2,z3,z642,z4,z6]),(0,[z0,z1,z2,z3,z643,z4,z6]),(0,[z0,z1,z2,z3,z4,z644,z6]),(0,[z645,z0,z1,z2,z3,z4,z6]),(0,[z406,z0,z2,z3,z4,z6,z59])],[(0,[z0,z1,z250,z2,z3,z4,z6]),(0,[z201,z1,z2,z3,z4,z6,z39]),(0,[z0,z1,z2,z646,z3,z4,z6]),(0,[z0,z38,z1,z2,z3,z4,z164])],[(1,[z311,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z647,z6])],[(0,[z648,z0,z1,z2,z3,z4,z6]),(0,[z649,z0,z1,z2,z3,z4,z6]),(0,[z650,z0,z1,z2,z3,z4,z6]),(0,[z12,z132,z1,z2,z3,z4,z6]),(1,[z276,z0,z1,z3,z4,z6])]],
   [[(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z154,z1,z2,z3,z4,z85,z6]),(0,[z0,z1,z2,z3,z4,z6,z652]),(1,[z214,z0,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z653,z4,z6]),(0,[z654,z0,z1,z2,z3,z4,z6]),(0,[z655,z0,z1,z2,z3,z4,z6]),(0,[z70,z0,z1,z3,z4,z97,z6]),(0,[z0,z1,z2,z4,z6,z18,z212])],[(0,[z0,z1,z2,z3,z4,z656,z6]),(0,[z657,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z658,z6]),(0,[z659,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z660,z6]),(0,[z0,z1,z45,z71,z3,z4,z6]),(0,[z12,z100,z0,z2,z3,z4,z6]),(0,[z0,z1,z153,z2,z4,z161,z6]),(0,[z0,z1,z2,z3,z4,z661,z6])],[(0,[z0,z1,z2,z3,z4,z6,z662]),(0,[z44,z0,z1,z65,z3,z4,z6]),(0,[z0,z1,z2,z3,z663,z4,z6]),(0,[z75,z0,z1,z45,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z161,z6])],[(0,[z94,z0,z1,z45,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z664]),(0,[z665,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z666,z6])],[(0,[z667,z0,z1,z2,z3,z4,z6])],[(0,[z155,z171,z0,z2,z3,z4,z6]),(0,[z44,z0,z1,z157,z3,z4,z6]),(0,[z75,z0,z1,z11,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z52,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z668]),(0,[z0,z1,z2,z3,z4,z6,z669])],[(0,[z0,z1,z2,z670,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z671]),(0,[z672,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z673,z4,z6])],[(0,[z107,z0,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z674,z3,z4,z6]),(0,[z0,z1,z675,z2,z3,z4,z6]),(0,[z0,z1,z2,z101,z4,z6,z73]),(0,[z0,z1,z2,z3,z676,z4,z6])]],
   [[(0,[z154,z1,z2,z3,z4,z6,z39]),(0,[z147,z0,z2,z3,z4,z58,z6]),(0,[z211,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z334,z3,z4,z6]),(1,[z0,z1,z241,z3,z4,z6]),(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z678,z4,z6])],[(0,[z0,z1,z679,z2,z3,z4,z6]),(1,[z262,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z680,z6]),(0,[z72,z383,z1,z2,z3,z4,z6])],[(1,[z0,z1,z13,z3,z4,z6]),(1,[z0,z1,z52,z3,z4,z96])],[(1,[z0,z1,z2,z400,z4,z6]),(0,[z681,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z682,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z683,z6]),(0,[z286,z0,z1,z2,z3,z4,z59])],[(0,[z0,z1,z2,z3,z4,z6,z684]),(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z6]),(0,[z14,z90,z1,z2,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z305,z6]),(1,[z288,z1,z2,z3,z4,z6])],[(0,[z686,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z181,z4,z58,z6]),(0,[z263,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z687,z6]),(0,[z0,z1,z2,z3,z688,z4,z6])]],
   [[(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z14,z0,z1,z2,z3,z4,z39]),(0,[z75,z0,z1,z2,z101,z4,z6]),(0,[z0,z1,z2,z690,z3,z4,z6])],[(0,[z10,z107,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z691,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z692]),(0,[z0,z1,z693,z2,z3,z4,z6]),(1,[z0,z1,z463,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z694,z6]),(0,[z0,z1,z695,z2,z3,z4,z6])],[(0,[z0,z1,z2,z696,z3,z4,z6]),(0,[z0,z210,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z697,z4,z6]),(0,[z75,z0,z1,z2,z3,z4,z6])],[(0,[z698,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z699,z3,z4,z6]),(0,[z94,z0,z1,z2,z3,z4,z6]),(1,[z60,z1,z2,z3,z4,z6]),(0,[z0,z38,z1,z2,z3,z4,z6])],[(0,[z0,z1,z700,z2,z3,z4,z6]),(0,[z0,z1,z2,z701,z3,z4,z6]),(0,[z702,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z703,z4,z6]),(0,[z75,z0,z1,z3,z80,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z704])],[(0,[z705,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z706,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z108,z59]),(0,[z147,z0,z1,z2,z3,z4,z631]),(0,[z0,z1,z2,z3,z4,z164,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z4,z6]),(0,[z132,z1,z2,z3,z4,z6]),(0,[z0,z1,z708,z3,z4,z6]),(0,[z0,z1,z709,z3,z4,z6]),(0,[z147,z0,z2,z226,z58,z6]),(0,[z710,z0,z1,z3,z4,z6])],[(0,[z83,z1,z2,z3,z85,z6])],[(0,[z0,z1,z334,z3,z4,z6]),(0,[z1,z2,z3,z711,z85,z6]),(0,[z0,z1,z3,z4,z712,z6]),(0,[z0,z713,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z714])],[(0,[z0,z1,z177,z79,z4,z6]),(0,[z715,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z716,z6]),(0,[z84,z1,z2,z717,z4,z6]),(0,[z0,z1,z2,z718,z4,z6])],[(0,[z719,z0,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z720,z6]),(0,[z1,z2,z3,z4,z108,z721])],[(0,[z83,z210,z2,z3,z85,z6]),(0,[z83,z1,z2,z67,z85,z6]),(0,[z722,z1,z2,z3,z4,z6]),(0,[z406,z0,z2,z3,z15,z6])],[(0,[z90,z152,z2,z3,z4,z6]),(0,[z723,z1,z2,z3,z4,z6]),(0,[z90,z1,z2,z275,z4,z6]),(0,[z0,z1,z2,z275,z305,z6]),(0,[z1,z2,z3,z103,z143,z389])]],
   [[(0,[z0,z1,z2,z724,z4,z6]),(0,[z0,z1,z2,z3,z4,z725]),(0,[z0,z1,z2,z726,z4,z6])],[(0,[z0,z1,z2,z727,z4,z6]),(0,[z0,z2,z728,z146,z4,z6]),(0,[z0,z1,z2,z3,z4,z631])],[(0,[z0,z2,z3,z4,z6,z729]),(0,[z398,z1,z3,z4,z438,z6])],[(0,[z730,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z731,z6]),(0,[z0,z1,z2,z732,z4,z6]),(0,[z0,z1,z2,z4,z6,z733]),(0,[z276,z0,z1,z101,z4,z6])],[(0,[z0,z1,z42,z193,z4,z6])],[(0,[z0,z1,z2,z734,z4,z6]),(0,[z0,z1,z2,z735,z4,z6]),(0,[z736,z0,z1,z2,z3,z4]),(0,[z0,z1,z737,z3,z4,z6])],[(0,[z0,z210,z37,z3,z4,z6]),(0,[z0,z1,z37,z67,z4,z6]),(0,[z0,z1,z738,z3,z4,z6]),(0,[z276,z0,z1,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z739]),(0,[z0,z1,z740,z3,z4,z6]),(0,[z741,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z742])]],
   [[(0,[z0,z1,z2,z3,z743,z6]),(0,[z744,z0,z1,z3,z4,z6]),(0,[z70,z1,z3,z88,z97,z6])],[(0,[z0,z1,z2,z3,z745,z6]),(0,[z75,z292,z1,z3,z4,z6]),(0,[z746,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z197,z4,z6]),(0,[z0,z1,z2,z747,z4,z6])],[(0,[z0,z152,z2,z3,z15,z6]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z241,z35,z4,z6]),(1,[z0,z749,z3,z4,z6]),(0,[z271,z0,z157,z3,z4,z6]),(0,[z0,z1,z2,z275,z15,z6]),(0,[z750,z1,z2,z3,z4,z6])],[(0,[z66,z1,z2,z3,z711,z6]),(0,[z0,z1,z751,z3,z4,z6])],[(0,[z311,z1,z2,z3,z305,z6]),(0,[z752,z1,z2,z3,z4,z6]),(0,[z753,z1,z2,z3,z4,z6])],[(0,[z94,z0,z13,z3,z4,z6]),(0,[z0,z1,z754,z3,z4,z6]),(0,[z75,z0,z1,z703,z4,z6]),(0,[z14,z311,z2,z3,z4,z133]),(0,[z0,z1,z3,z4,z96,z129]),(0,[z406,z753,z2,z3,z4,z6])],[(0,[z154,z1,z241,z3,z4,z6]),(0,[z0,z1,z13,z101,z4,z6]),(0,[z1,z2,z3,z4,z6,z755])]],
   [[(0,[z0,z1,z241,z3,z4,z6]),(0,[z84,z1,z2,z67,z4,z6]),(0,[z262,z0,z2,z756,z4,z6]),(0,[z757,z1,z2,z3,z4,z6]),(0,[z758,z288,z2,z3,z4,z6])],[(0,[z0,z1,z2,z759,z4,z6]),(0,[z0,z760,z2,z3,z4,z6]),(0,[z44,z1,z137,z3,z4,z6]),(0,[z0,z1,z52,z3,z4,z588]),(0,[z761,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z762,z4,z6]),(0,[z0,z1,z13,z3,z4,z6]),(1,[z0,z2,z3,z763,z6]),(0,[z0,z1,z52,z3,z4,z764])],[(0,[z0,z1,z2,z400,z4,z6]),(0,[z0,z1,z2,z765,z4,z6]),(0,[z107,z1,z2,z3,z4,z126]),(0,[z84,z1,z2,z627,z4,z6]),(0,[z150,z0,z2,z101,z4,z6])],[(0,[z192,z2,z3,z4,z85,z6]),(0,[z288,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z766]),(0,[z75,z0,z1,z25,z4,z6])],[(0,[z266,z179,z2,z3,z4,z6]),(0,[z767,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z768,z6]),(0,[z0,z1,z2,z3,z4,z764])],[(0,[z84,z1,z2,z585,z4,z6]),(0,[z0,z1,z769,z3,z4,z6]),(0,[z0,z1,z2,z770,z4,z6]),(0,[z94,z0,z45,z3,z4,z6]),(0,[z0,z771,z2,z3,z4,z6])],[(0,[z772,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z773,z4,z6]),(0,[z60,z1,z2,z101,z4,z6]),(0,[z0,z1,z2,z774,z4,z6]),(0,[z292,z1,z79,z3,z4,z6])],[(0,[z311,z1,z2,z3,z15,z6]),(0,[z81,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z775]),(0,[z776,z1,z2,z3,z4,z6])],[(0,[z406,z0,z2,z3,z4,z108]),(0,[z777,z1,z2,z3,z4,z6]),(0,[z0,z1,z778,z3,z4,z6]),(1,[z0,z1,z3,z4,z764])],[(0,[z60,z1,z2,z3,z4,z6]),(0,[z0,z1,z157,z119,z4,z6]),(0,[z12,z132,z2,z101,z4,z6]),(0,[z75,z0,z1,z253,z4,z6])],[(0,[z0,z779,z2,z3,z4,z6]),(0,[z1,z11,z780,z3,z4,z6]),(0,[z0,z1,z2,z717,z4,z6]),(0,[z192,z2,z3,z4,z6,z39])],[(0,[z0,z1,z2,z781,z4,z6]),(1,[z0,z1,z774,z4,z6])],[(0,[z271,z0,z13,z3,z4,z6]),(0,[z0,z1,z2,z782,z4,z6]),(0,[z263,z0,z1,z4,z96,z6])],[(0,[z0,z1,z783,z3,z4,z6]),(0,[z288,z1,z2,z3,z4,z39]),(0,[z75,z271,z0,z80,z4,z6]),(0,[z211,z263,z0,z1,z4,z6])]],
   [[(0,[z0,z1,z250,z3,z4,z6]),(0,[z0,z1,z2,z784,z4,z6]),(0,[z785,z1,z2,z3,z4,z6]),(0,[z786,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z181,z164,z59]),(0,[z17,z0,z1,z2,z4,z6])],[(0,[z104,z0,z2,z3,z58,z6]),(0,[z107,z1,z2,z3,z4,z89]),(0,[z262,z90,z2,z3,z4,z6]),(0,[z0,z1,z22,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z787]),(0,[z90,z1,z463,z3,z4,z6]),(0,[z0,z1,z463,z3,z305,z6]),(0,[z70,z17,z0,z1,z97,z6])],[(0,[z0,z1,z2,z788,z4,z6]),(0,[z0,z1,z789,z3,z4,z6])],[(0,[z790,z1,z2,z3,z4,z6]),(0,[z17,z0,z1,z45,z4,z6]),(0,[z0,z1,z791,z3,z4,z6])],[(0,[z147,z266,z2,z3,z58,z6]),(0,[z263,z0,z1,z2,z4,z6]),(0,[z17,z1,z2,z4,z88,z6])],[(0,[z0,z1,z2,z792,z4,z6]),(0,[z44,z1,z670,z3,z4,z6]),(0,[z154,z1,z2,z35,z4,z6]),(0,[z0,z1,z793,z3,z4,z6]),(0,[z0,z192,z137,z3,z4,z6]),(0,[z266,z2,z3,z4,z164,z6])],[(0,[z0,z1,z2,z35,z4,z6]),(1,[z730,z2,z3,z4,z6]),(0,[z0,z1,z137,z3,z4,z6]),(0,[z0,z1,z2,z794,z4,z6]),(0,[z795,z1,z2,z3,z4,z6]),(0,[z271,z0,z45,z3,z4,z6]),(0,[z491,z0,z1,z2,z3,z59]),(0,[z796,z0,z2,z3,z4,z6])],[(0,[z263,z0,z1,z45,z4,z6]),(0,[z12,z0,z488,z101,z4,z6]),(0,[z0,z1,z3,z4,z764,z212])]],
   [[(0,[z0,z1,z797,z3,z4,z6]),(0,[z0,z1,z798,z3,z4,z6])],[(0,[z155,z90,z2,z3,z4,z6]),(0,[z0,z799,z2,z3,z4,z6]),(0,[z201,z1,z2,z449,z4,z6]),(0,[z0,z1,z800,z3,z4,z6])],[(0,[z730,z0,z2,z3,z4,z6]),(0,[z0,z192,z2,z3,z4,z6]),(0,[z801,z0,z2,z3,z4,z6]),(0,[z81,z0,z1,z76,z4,z6]),(0,[z0,z1,z2,z756,z4,z6]),(0,[z512,z0,z45,z3,z4,z6]),(0,[z802,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z414,z1,z2,z54,z4,z6]),(0,[z0,z210,z137,z3,z4,z6]),(0,[z0,z1,z2,z227,z647,z6]),(0,[z0,z1,z3,z4,z96,z764])],[(0,[z0,z803,z2,z3,z4,z6]),(0,[z606,z0,z157,z3,z4,z6]),(0,[z0,z1,z137,z3,z4,z98]),(0,[z262,z0,z2,z804,z4,z6]),(0,[z0,z1,z2,z3,z4,z805]),(0,[z806,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z807])],[(0,[z0,z1,z2,z82,z4,z6]),(0,[z83,z1,z2,z3,z85,z417]),(0,[z291,z1,z2,z3,z4,z39]),(0,[z0,z1,z463,z3,z15,z6]),(0,[z276,z0,z1,z4,z161,z6])],[(0,[z256,z1,z11,z3,z4,z6]),(0,[z21,z1,z372,z3,z4,z6]),(0,[z90,z1,z42,z3,z4,z6]),(0,[z0,z1,z42,z3,z305,z6]),(0,[z1,z2,z3,z808,z4,z6])],[(0,[z154,z730,z2,z3,z4,z6]),(0,[z0,z1,z809,z3,z4,z6]),(0,[z0,z2,z3,z181,z15,z6])]],
   [[(0,[z0,z210,z2,z3,z4,z6]),(0,[z0,z1,z2,z810,z4,z6]),(0,[z0,z192,z2,z3,z4,z98]),(0,[z811,z1,z2,z3,z4,z6]),(0,[z70,z0,z1,z3,z97,z6])],[(0,[z0,z1,z250,z76,z4,z6]),(0,[z0,z1,z2,z3,z4,z98]),(0,[z812,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z813,z4,z6])],[(0,[z201,z1,z2,z646,z4,z6]),(0,[z94,z0,z45,z119,z4,z6]),(0,[z21,z1,z2,z3,z4,z302]),(0,[z0,z1,z22,z3,z4,z302]),(0,[z0,z368,z2,z3,z181,z6])],[(0,[z0,z1,z2,z226,z4,z631]),(0,[z814,z1,z2,z3,z4,z6])],[(0,[z0,z1,z815,z3,z4,z6]),(0,[z589,z1,z11,z3,z4,z6]),(0,[z816,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z817])],[(0,[z0,z1,z37,z3,z4,z417]),(0,[z266,z2,z3,z4,z58,z6]),(0,[z70,z17,z0,z1,z4,z6]),(0,[z0,z1,z818,z3,z4,z6])],[(0,[z430,z1,z65,z3,z4,z6]),(0,[z0,z1,z2,z819,z4,z6]),(0,[z0,z210,z2,z3,z4,z98]),(0,[z0,z1,z2,z67,z4,z98]),(0,[z0,z1,z45,z119,z4,z6]),(0,[z0,z1,z2,z375,z4,z539]),(0,[z0,z1,z2,z820,z4,z6]),(0,[z0,z1,z2,z4,z821,z73])],[(0,[z83,z1,z2,z443,z85,z6]),(0,[z822,z0,z2,z3,z4,z6]),(0,[z271,z0,z2,z146,z4,z6])]],
   [[(0,[z0,z823,z2,z3,z4,z6]),(0,[z70,z0,z1,z169,z97,z6])],[(0,[z0,z1,z2,z824,z4,z6]),(0,[z1,z11,z3,z4,z553,z6]),(0,[z75,z0,z1,z4,z180,z6]),(0,[z0,z825,z2,z3,z4,z6])],[(0,[z325,z152,z2,z3,z4,z6]),(0,[z192,z11,z2,z3,z4,z6]),(0,[z597,z1,z2,z54,z4,z6]),(0,[z192,z2,z76,z3,z4,z6]),(0,[z0,z1,z42,z3,z15,z6]),(0,[z0,z1,z2,z826,z4,z6])],[(0,[z827,z1,z2,z3,z4,z6]),(0,[z0,z1,z828,z3,z4,z6])],[(0,[z104,z1,z2,z3,z85,z6]),(0,[z14,z152,z2,z3,z4,z39]),(0,[z81,z0,z1,z54,z4,z6]),(0,[z829,z1,z2,z3,z4,z6]),(0,[z830,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z831,z6]),(0,[z406,z832,z2,z3,z4,z6])],[(0,[z0,z1,z833,z3,z4,z6]),(0,[z357,z1,z157,z3,z4,z6]),(0,[z75,z0,z23,z80,z4,z6])],[(0,[z0,z1,z2,z834,z4,z6]),(0,[z835,z0,z1,z2,z4,z6]),(0,[z81,z398,z1,z3,z4,z6])],[(0,[z0,z1,z2,z836,z4,z6]),(0,[z66,z192,z2,z3,z4,z6]),(0,[z0,z1,z37,z443,z4,z6]),(0,[z0,z837,z2,z3,z4,z6]),(0,[z0,z1,z838,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z839,z4,z6]),(0,[z0,z1,z840,z3,z4,z6]),(0,[z551,z0,z157,z3,z4,z6]),(0,[z442,z0,z45,z3,z4,z6]),(0,[z7,z0,z2,z101,z4,z6]),(0,[z0,z2,z3,z4,z841,z133]),(0,[z1,z2,z3,z4,z842,z6])],[(0,[z251,z152,z2,z3,z4,z6]),(0,[z262,z0,z2,z3,z4,z108]),(0,[z0,z1,z3,z4,z6,z764])],[(0,[z90,z1,z2,z3,z4,z126]),(0,[z107,z1,z137,z3,z4,z6]),(0,[z0,z2,z749,z3,z4,z6]),(0,[z1,z2,z843,z3,z4,z6])],[(0,[z0,z1,z250,z54,z4,z6]),(0,[z0,z1,z844,z3,z4,z6]),(0,[z845,z1,z2,z3,z4,z6]),(0,[z0,z846,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z1,z2,z4,z6,z848]),(0,[z288,z1,z2,z3,z4,z108]),(0,[z849,z1,z2,z3,z4,z6]),(0,[z0,z2,z728,z3,z4,z6]),(0,[z266,z1,z2,z3,z4,z631]),(0,[z1,z2,z3,z4,z6,z850])],[(0,[z399,z1,z11,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z807])],[(0,[z107,z192,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z851]),(0,[z0,z852,z2,z3,z4,z6]),(0,[z0,z1,z2,z145,z227,z6]),(1,[z0,z1,z2,z831,z6]),(0,[z72,z383,z1,z2,z4,z73])],[(0,[z0,z1,z2,z3,z4,z174]),(0,[z0,z1,z71,z3,z643,z6]),(0,[z0,z1,z2,z119,z4,z6]),(0,[z853,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z854,z4,z6])]],
   [[(0,[z0,z1,z855,z3,z4,z6]),(0,[z0,z1,z2,z856,z4,z6]),(0,[z154,z550,z2,z3,z4,z6])],[(0,[z107,z1,z2,z82,z4,z6]),(0,[z0,z1,z857,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z858]),(0,[z0,z1,z2,z4,z6,z859])],[(0,[z1,z2,z3,z4,z126,z39]),(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z1,z2,z3,z861,z4]),(0,[z862,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z863,z6]),(0,[z78,z0,z1,z2,z4,z73]),(0,[z864,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z124,z4,z302]),(0,[z0,z2,z3,z865,z4,z6])],[(0,[z0,z1,z866,z3,z4,z6]),(0,[z0,z1,z867,z3,z4,z6]),(0,[z0,z1,z2,z868,z4,z6]),(0,[z189,z1,z2,z3,z4,z39]),(0,[z0,z1,z2,z4,z869,z6]),(0,[z311,z1,z2,z275,z4,z6]),(0,[z0,z1,z2,z3,z870,z6])],[(0,[z0,z1,z2,z871,z4,z6]),(0,[z872,z1,z2,z3,z4,z6]),(0,[z873,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z193,z4,z6]),(0,[z0,z1,z2,z3,z103,z93])],[(0,[z0,z1,z2,z3,z874,z6]),(0,[z0,z1,z875,z3,z4,z6]),(0,[z876,z0,z2,z3,z4,z6]),(0,[z107,z1,z2,z3,z4,z98]),(0,[z0,z1,z3,z4,z6,z877]),(0,[z0,z1,z878,z2,z4,z6])],[(0,[z406,z0,z879,z3,z4,z6])],[(0,[z0,z1,z65,z203,z4,z6]),(0,[z880,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z881]),(0,[z882,z0,z1,z3,z4,z6]),(0,[z286,z0,z1,z2,z3,z59])]],
   [[(0,[z66,z1,z2,z3,z363,z6]),(0,[z883,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z15,z133])],[(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z1,z885,z3,z4,z6]),(0,[z0,z1,z2,z886,z4,z6]),(0,[z0,z1,z372,z3,z4,z631]),(0,[z0,z2,z887,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z821])],[(0,[z0,z1,z157,z203,z4,z6]),(0,[z888,z1,z2,z3,z4,z6]),(0,[z94,z186,z45,z3,z4,z6]),(0,[z0,z1,z3,z4,z889,z6]),(0,[z406,z0,z2,z890,z4,z6])],[(0,[z589,z1,z2,z76,z4,z6]),(0,[z0,z1,z153,z41,z4,z6]),(0,[z21,z1,z2,z226,z4,z6]),(0,[z0,z1,z22,z226,z4,z6])],[(0,[z0,z1,z891,z3,z4,z6]),(0,[z0,z1,z2,z3,z892,z6]),(0,[z12,z60,z2,z101,z4,z6]),(0,[z75,z0,z1,z246,z4,z6]),(0,[z117,z1,z2,z4,z169,z6]),(0,[z0,z1,z2,z893,z4,z6]),(0,[z1,z2,z3,z4,z6,z894])],[(1,[z1,z2,z717,z4,z6]),(0,[z1,z2,z3,z4,z895,z6]),(0,[z615,z0,z1,z2,z55,z6]),(0,[z0,z1,z2,z3,z370,z143]),(0,[z75,z260,z1,z2,z4,z6]),(0,[z896,z1,z2,z3,z4,z6])],[(0,[z264,z152,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z897]),(0,[z0,z1,z898,z3,z4,z6])],[(0,[z0,z1,z899,z3,z4,z6]),(0,[z0,z1,z2,z900,z4,z6]),(0,[z0,z1,z2,z3,z901,z6]),(0,[z398,z1,z2,z146,z4,z6]),(0,[z211,z0,z1,z3,z4,z764])]],
   [[(0,[z44,z192,z2,z3,z4,z6]),(0,[z107,z1,z2,z3,z4,z290]),(0,[z357,z1,z45,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z902]),(0,[z81,z1,z3,z4,z194,z6])],[(0,[z0,z1,z903,z3,z4,z6]),(0,[z0,z2,z119,z146,z4,z6]),(0,[z81,z0,z1,z101,z4,z6]),(0,[z147,z0,z2,z3,z58,z631]),(0,[z0,z179,z2,z3,z763,z6])],[(0,[z626,z1,z2,z76,z4,z6]),(0,[z0,z1,z2,z3,z4,z904]),(0,[z66,z1,z2,z3,z195,z6]),(0,[z0,z1,z905,z3,z4,z6]),(0,[z406,z0,z2,z3,z58,z6]),(0,[z906,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z6,z907]),(0,[z908,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z145,z541,z6]),(0,[z0,z1,z2,z3,z909,z6]),(0,[z0,z1,z79,z4,z457,z6])],[(0,[z1,z137,z3,z4,z6,z39]),(0,[z12,z0,z2,z728,z4,z6])],[(0,[z0,z1,z2,z3,z4,z910]),(0,[z0,z2,z101,z728,z4,z6]),(0,[z0,z2,z3,z763,z58,z6]),(0,[z75,z0,z1,z278,z4,z6])],[(0,[z0,z911,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z912]),(0,[z913,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z914]),(0,[z0,z2,z3,z181,z763,z6]),(0,[z0,z1,z463,z275,z4,z6])]],
   [[(0,[z0,z1,z250,z101,z4,z6]),(0,[z0,z915,z2,z3,z4,z6]),(0,[z0,z1,z2,z193,z15,z6]),(0,[z75,z0,z1,z284,z4,z6])],[(0,[z0,z1,z916,z3,z4,z6]),(0,[z0,z1,z917,z3,z4,z6]),(0,[z918,z1,z2,z3,z4,z6])],[(0,[z211,z263,z0,z1,z4,z212])],[(0,[z70,z0,z1,z3,z919,z6]),(0,[z920,z1,z2,z3,z4,z6]),(0,[z0,z1,z921,z3,z4,z6])],[(0,[z0,z1,z2,z922,z4,z6]),(0,[z0,z1,z2,z923,z4,z6]),(0,[z0,z1,z2,z3,z4,z924]),(0,[z266,z1,z22,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z925]),(0,[z336,z0,z1,z2,z55,z6])],[],[(0,[z0,z1,z2,z3,z4,z926]),(0,[z927,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z928])]],
   [[(0,[z398,z1,z2,z76,z4,z6]),(0,[z0,z1,z2,z929,z4,z6]),(0,[z72,z276,z0,z1,z4,z6])],[(0,[z196,z0,z2,z101,z4,z6]),(0,[z645,z1,z2,z3,z4,z39]),(0,[z14,z0,z2,z275,z4,z133]),(0,[z930,z1,z2,z3,z4,z6])],[(0,[z147,z0,z2,z3,z15,z6]),(0,[z159,z0,z1,z2,z3,z59])],[(0,[z0,z931,z2,z3,z4,z6]),(0,[z260,z1,z2,z3,z4,z6]),(0,[z932,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z15,z164])],[(0,[z0,z1,z42,z275,z4,z6])],[(0,[z0,z1,z45,z203,z4,z6]),(0,[z201,z1,z2,z717,z4,z6]),(0,[z1,z2,z3,z4,z933,z6]),(0,[z311,z1,z463,z3,z4,z6]),(0,[z0,z1,z934,z3,z4,z6])],[(0,[z266,z1,z2,z3,z4,z6]),(0,[z0,z1,z137,z67,z4,z6]),(0,[z72,z0,z1,z4,z405,z73])],[(0,[z0,z1,z2,z443,z4,z98])]],
   [[(0,[z657,z152,z2,z3,z4,z6]),(0,[z155,z0,z2,z3,z15,z6]),(0,[z0,z1,z339,z3,z4,z6]),(0,[z0,z1,z11,z203,z4,z6]),(0,[z14,z266,z2,z3,z4,z6]),(0,[z336,z81,z0,z1,z4,z6])],[(0,[z262,z0,z935,z3,z4,z6]),(0,[z0,z1,z2,z3,z58,z631]),(0,[z72,z0,z1,z2,z4,z73])],[(0,[z0,z1,z2,z936,z4,z6]),(0,[z154,z155,z2,z3,z4,z126]),(0,[z0,z1,z937,z3,z4,z6]),(0,[z0,z192,z2,z67,z4,z6]),(0,[z186,z1,z2,z197,z4,z6]),(0,[z938,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z939,z4,z6]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z10,z1,z11,z203,z4,z6]),(0,[z0,z1,z2,z67,z4,z6]),(0,[z941,z0,z1,z2,z4,z6]),(0,[z942,z0,z1,z2,z4,z6]),(0,[z0,z1,z943,z3,z4,z6])],[(0,[z0,z1,z2,z944,z4,z6]),(0,[z0,z1,z153,z79,z4,z6]),(0,[z336,z1,z2,z194,z55,z6]),(0,[z832,z1,z2,z3,z4,z6])],[(0,[z154,z155,z334,z3,z4,z6]),(0,[z232,z1,z2,z3,z4,z6])],[(0,[z90,z1,z2,z3,z4,z6]),(0,[z555,z1,z65,z3,z4,z6]),(0,[z1,z2,z3,z4,z88,z6]),(0,[z0,z1,z153,z567,z4,z6]),(0,[z945,z0,z1,z3,z4,z6]),(0,[z946,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z305,z6]),(0,[z0,z1,z79,z774,z4,z6])],[(0,[z0,z1,z2,z3,z4,z947]),(0,[z0,z13,z157,z3,z4,z6]),(0,[z271,z0,z2,z101,z4,z6]),(0,[z948,z1,z2,z3,z4,z6]),(0,[z336,z0,z1,z438,z55,z6])]],
   [[(0,[z0,z210,z2,z67,z4,z6]),(0,[z949,z0,z1,z2,z4,z6]),(0,[z950,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z161,z821])],[(0,[z951,z1,z2,z3,z4,z6]),(0,[z147,z0,z22,z3,z58,z6])],[(0,[z17,z0,z1,z11,z4,z6]),(0,[z398,z1,z2,z54,z4,z6]),(0,[z271,z0,z2,z3,z4,z6]),(0,[z311,z1,z42,z3,z4,z6])],[(0,[z0,z952,z2,z3,z4,z6]),(0,[z189,z1,z2,z3,z4,z721]),(0,[z0,z1,z372,z3,z4,z6]),(0,[z0,z1,z2,z953,z4,z6]),(0,[z0,z2,z3,z4,z6,z954])],[(0,[z0,z1,z955,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z0,z1,z2,z3,z4,z957]),(0,[z266,z1,z2,z124,z4,z6]),(0,[z958,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z959,z4,z6]),(0,[z75,z0,z157,z146,z4,z6]),(0,[z0,z45,z749,z3,z4,z6]),(0,[z406,z0,z2,z3,z4,z631])],[(0,[z0,z1,z2,z3,z4,z960]),(0,[z0,z1,z961,z3,z4,z6]),(0,[z962,z1,z2,z3,z4,z6]),(0,[z75,z0,z1,z774,z4,z6]),(0,[z0,z1,z963,z3,z4,z6])],[(0,[z154,z155,z2,z3,z4,z174]),(0,[z132,z1,z488,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z302]),(0,[z964,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z152,z2,z3,z4,z126]),(0,[z107,z86,z2,z3,z4,z108]),(0,[z0,z965,z2,z3,z4,z6])],[(0,[z966,z0,z2,z3,z4,z6]),(0,[z90,z1,z2,z3,z4,z39])],[(0,[z201,z1,z250,z76,z4,z6]),(0,[z967,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z15,z6])],[(0,[z383,z1,z2,z3,z4,z6]),(0,[z147,z0,z2,z3,z58,z6])],[(0,[z497,z0,z2,z146,z4,z6]),(0,[z117,z1,z157,z3,z4,z6])],[(0,[z464,z152,z2,z3,z4,z6]),(0,[z0,z1,z2,z968,z4,z6])],[(0,[z1,z2,z3,z195,z711,z6]),(0,[z211,z0,z1,z3,z4,z168]),(0,[z406,z0,z2,z969,z4,z6])],[(0,[z550,z0,z45,z3,z4,z6]),(0,[z12,z0,z13,z101,z4,z6]),(0,[z0,z1,z2,z3,z807,z59])]],
   [[(0,[z75,z0,z1,z382,z4,z6]),(1,[z0,z2,z728,z4,z6])],[(0,[z0,z970,z2,z3,z4,z6]),(0,[z0,z1,z2,z804,z4,z6]),(0,[z971,z1,z2,z3,z4,z6]),(0,[z0,z1,z372,z124,z4,z6]),(0,[z0,z1,z2,z375,z4,z821]),(0,[z288,z1,z2,z3,z103,z143])],[(0,[z972,z0,z2,z3,z4,z6]),(0,[z336,z398,z1,z2,z55,z6])],[(0,[z154,z155,z241,z3,z4,z6]),(0,[z0,z1,z973,z3,z4,z6]),(0,[z364,z1,z2,z3,z4,z39]),(0,[z357,z1,z2,z197,z4,z6]),(0,[z14,z0,z463,z3,z4,z133])],[(0,[z730,z152,z2,z3,z4,z6]),(0,[z1,z780,z65,z3,z4,z6]),(0,[z17,z0,z1,z65,z4,z6]),(0,[z107,z1,z339,z3,z4,z6]),(0,[z83,z1,z37,z3,z85,z6]),(0,[z0,z1,z2,z974,z4,z6])],[(0,[z0,z1,z975,z3,z4,z6]),(0,[z0,z976,z2,z3,z4,z6]),(0,[z201,z1,z2,z76,z4,z6]),(0,[z0,z977,z2,z3,z4,z6]),(0,[z1,z2,z76,z717,z4,z6]),(0,[z0,z1,z2,z3,z15,z39]),(0,[z0,z1,z978,z3,z4,z6]),(0,[z814,z271,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z919,z6])],[(0,[z154,z155,z2,z400,z4,z6]),(0,[z1,z2,z3,z4,z98,z39]),(0,[z262,z107,z2,z3,z4,z108])],[(0,[z107,z1,z2,z67,z4,z6]),(0,[z17,z0,z1,z113,z4,z6]),(0,[z0,z1,z879,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z711,z6]),(0,[z0,z1,z2,z3,z490,z143]),(0,[z577,z0,z2,z146,z4,z6]),(0,[z0,z1,z979,z3,z4,z6])],[(0,[z147,z0,z2,z124,z58,z6]),(0,[z72,z276,z0,z1,z4,z73])],[(0,[z0,z1,z980,z3,z4,z6]),(0,[z75,z0,z1,z351,z4,z6]),(0,[z406,z286,z0,z2,z3,z59])],[(0,[z186,z1,z2,z3,z4,z6]),(0,[z0,z981,z2,z3,z4,z6]),(0,[z357,z94,z45,z3,z4,z6]),(0,[z0,z1,z3,z4,z438,z6]),(0,[z0,z1,z3,z4,z982,z6]),(0,[z0,z1,z2,z890,z4,z6])],[(0,[z0,z1,z2,z3,z4,z983]),(0,[z984,z1,z2,z3,z4,z6])],[(0,[z152,z2,z3,z4,z131,z6]),(0,[z1,z2,z3,z195,z221,z6]),(0,[z1,z2,z3,z4,z194,z6]),(0,[z0,z1,z985,z3,z4,z6])],[(0,[z154,z262,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z44,z1,z780,z3,z4,z6]),(0,[z0,z1,z987,z3,z4,z6]),(0,[z271,z0,z2,z119,z4,z6]),(0,[z0,z1,z416,z2,z3,z59])],[(0,[z543,z1,z2,z3,z4,z39]),(0,[z1,z11,z137,z3,z4,z6]),(0,[z398,z1,z2,z101,z4,z6]),(0,[z90,z1,z2,z193,z4,z6]),(0,[z0,z1,z2,z193,z305,z6])]],
   [[(0,[z988,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z989,z6]),(0,[z14,z0,z42,z3,z4,z133]),(0,[z0,z1,z153,z4,z207,z6]),(0,[z0,z1,z2,z990,z4,z6])],[(0,[z1,z2,z3,z4,z6,z991]),(0,[z0,z1,z2,z4,z6,z821])],[(0,[z398,z1,z2,z3,z4,z6]),(0,[z0,z1,z992,z3,z4,z6]),(0,[z993,z0,z1,z2,z3,z4]),(0,[z147,z0,z2,z3,z763,z6]),(0,[z1,z2,z3,z4,z6,z994]),(0,[z406,z0,z995,z3,z4,z6])],[(0,[z83,z1,z2,z3,z523,z6]),(0,[z996,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z997,z4,z6]),(0,[z998,z1,z2,z3,z4,z6]),(0,[z999,z0,z2,z3,z4,z6])],[],[(0,[z0,z1,z137,z3,z4,z417]),(0,[z17,z117,z1,z2,z4,z6]),(0,[z0,z1,z3,z4,z6,z1000]),(0,[z1,z2,z3,z4,z6,z1001])],[],[(0,[z0,z1,z2,z3,z4,z1002]),(0,[z0,z1,z2,z1003,z4,z6]),(0,[z0,z1,z2,z3,z4,z1004]),(0,[z398,z1,z2,z67,z4,z6]),(0,[z117,z1,z45,z3,z4,z6]),(0,[z0,z1,z2,z145,z358,z6])]],
   [[(0,[z12,z0,z2,z101,z4,z6]),(0,[z0,z1,z2,z226,z4,z6]),(0,[z0,z1,z2,z3,z103,z143])],[(0,[z730,z171,z2,z3,z4,z6]),(0,[z154,z155,z2,z35,z4,z6]),(0,[z154,z649,z2,z3,z4,z6]),(0,[z0,z1005,z2,z3,z4,z6]),(0,[z1,z2,z76,z67,z4,z6]),(0,[z0,z192,z2,z3,z4,z417]),(0,[z1006,z1,z2,z3,z4,z6]),(0,[z1007,z1,z2,z3,z4,z6]),(0,[z1008,z1,z2,z3,z4,z6]),(0,[z0,z1009,z2,z3,z4,z6])],[(0,[z117,z1,z11,z3,z4,z6]),(0,[z0,z1,z1010,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z417]),(0,[z0,z1,z2,z1011,z4,z6]),(0,[z60,z1,z488,z3,z4,z6]),(0,[z0,z1,z2,z4,z831,z6])],[(0,[z171,z152,z2,z3,z4,z6]),(0,[z0,z1012,z2,z3,z4,z6]),(0,[z260,z1,z153,z2,z4,z6]),(0,[z336,z0,z1,z2,z831,z6]),(0,[z0,z1,z2,z145,z831,z6]),(0,[z0,z1,z2,z375,z4,z161])],[(0,[z0,z1,z2,z1013,z4,z6]),(0,[z0,z1,z2,z3,z4,z1014]),(0,[z1015,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z4,z168]),(0,[z0,z1,z2,z3,z6,z807]),(0,[z288,z1016,z2,z3,z4,z6])],[(0,[z0,z1,z1017,z3,z4,z6]),(0,[z0,z1,z2,z1018,z4,z6]),(0,[z14,z0,z2,z3,z4,z631])],[(0,[z154,z155,z2,z3,z4,z6]),(0,[z0,z1,z1019,z3,z4,z6]),(0,[z0,z1,z2,z1020,z4,z6]),(0,[z70,z0,z1,z3,z16,z6])],[(0,[z0,z210,z2,z3,z4,z417]),(0,[z0,z1,z137,z443,z4,z6]),(0,[z0,z1,z2,z67,z4,z417]),(0,[z94,z0,z749,z3,z4,z6]),(0,[z347,z0,z2,z146,z4,z6])]],
   [[(0,[z1,z2,z3,z195,z6,z40])],[(0,[z0,z1,z2,z1021,z4,z6]),(0,[z1,z2,z717,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z721]),(0,[z21,z1,z2,z124,z4,z6]),(0,[z1,z2,z3,z4,z1022,z6]),(0,[z1023,z1,z2,z3,z4,z6])],[(0,[z83,z1,z2,z3,z20,z6]),(0,[z1,z2,z3,z4,z1024,z6])],[(0,[z0,z1,z780,z3,z4,z6]),(0,[z0,z192,z2,z443,z4,z6]),(0,[z0,z1,z749,z3,z4,z6]),(0,[z1025,z1,z2,z3,z4,z6])],[(0,[z357,z1,z2,z3,z4,z6]),(0,[z10,z1,z365,z3,z4,z6]),(0,[z0,z1,z2,z443,z4,z6]),(0,[z14,z0,z2,z3,z4,z652]),(0,[z57,z0,z1,z3,z97,z6])],[(0,[z1026,z1,z2,z3,z4,z6]),(0,[z336,z0,z1,z2,z16,z6]),(0,[z70,z117,z1,z3,z97,z6]),(0,[z1,z2,z4,z88,z169,z6]),(0,[z1027,z1,z2,z3,z4,z6])],[(0,[z14,z0,z2,z3,z4,z662]),(0,[z10,z1,z780,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1028]),(0,[z1,z3,z4,z194,z438,z6])],[(0,[z0,z1,z2,z1029,z4,z6]),(0,[z262,z0,z751,z3,z4,z6]),(0,[z186,z1,z2,z119,z4,z6])]],
   [[(0,[z0,z1,z1030,z3,z4,z6]),(0,[z1031,z0,z1,z2,z4,z6]),(0,[z624,z0,z1,z2,z3,z59]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z0,z1,z1033,z3,z4,z6]),(0,[z211,z0,z1,z3,z4,z212])],[(0,[z0,z210,z2,z443,z4,z6]),(0,[z83,z1,z137,z3,z85,z6]),(0,[z0,z1,z2,z226,z4,z302]),(0,[z1034,z1,z2,z3,z4,z6]),(0,[z1035,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z4,z821])],[(0,[z0,z1,z2,z1036,z4,z6]),(0,[z0,z1,z2,z3,z15,z108]),(0,[z1037,z1,z2,z3,z4,z6]),(0,[z0,z1,z488,z3,z4,z6]),(0,[z0,z1,z2,z3,z763,z6])],[(0,[z0,z1,z2,z3,z4,z1038]),(0,[z214,z0,z749,z3,z4,z6]),(0,[z271,z1039,z2,z3,z4,z6])],[(0,[z155,z730,z2,z3,z4,z6]),(0,[z1,z2,z3,z195,z300,z6]),(0,[z1,z2,z3,z4,z721,z39]),(0,[z100,z0,z2,z728,z4,z6]),(0,[z0,z1,z2,z275,z4,z6]),(0,[z21,z1,z2,z3,z4,z631]),(0,[z0,z1,z22,z3,z4,z631]),(0,[z1040,z1,z2,z3,z4,z6]),(0,[z0,z1,z1041,z3,z4,z6])],[(0,[z0,z1,z241,z400,z4,z6]),(0,[z83,z192,z2,z3,z85,z6])],[(0,[z44,z1,z412,z3,z4,z6])],[(0,[z100,z0,z2,z146,z4,z6]),(0,[z286,z0,z1,z2,z3,z807])]],
   [[(0,[z0,z1,z3,z4,z6,z1042]),(0,[z0,z2,z3,z4,z164,z631]),(0,[z406,z0,z2,z3,z4,z133])],[(0,[z14,z0,z2,z3,z4,z684]),(0,[z0,z1,z2,z3,z4,z1043]),(0,[z0,z1,z679,z79,z4,z6]),(0,[z0,z1,z1044,z3,z4,z6]),(0,[z0,z1,z3,z774,z4,z6]),(0,[z1045,z1,z2,z3,z4,z6])],[(0,[z292,z1,z2,z3,z4,z6]),(0,[z107,z1,z2,z3,z4,z108]),(0,[z0,z1,z2,z1046,z4,z6]),(0,[z1047,z1,z2,z3,z4,z6]),(0,[z72,z260,z1,z2,z4,z73])],[(0,[z0,z1,z2,z3,z4,z1048]),(0,[z1049,z1,z2,z3,z4,z6]),(0,[z0,z1016,z2,z3,z4,z6])],[(0,[z83,z1,z2,z3,z85,z98]),(0,[z0,z1050,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1051]),(0,[z0,z192,z37,z3,z4,z6]),(0,[z1052,z1,z2,z3,z4,z6]),(0,[z1053,z1,z2,z3,z4,z6])],[(0,[z0,z1,z1054,z3,z4,z6]),(0,[z0,z1,z37,z3,z4,z6]),(0,[z1055,z0,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z272,z39]),(0,[z1056,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z1057,z4,z6]),(0,[z266,z1,z372,z3,z4,z6]),(0,[z406,z0,z2,z3,z181,z6]),(0,[z14,z0,z2,z193,z4,z133]),(0,[z75,z0,z1,z519,z4,z6]),(0,[z0,z1,z2,z1058,z4,z6])],[(0,[z1059,z0,z1,z3,z4,z6]),(0,[z12,z0,z2,z119,z4,z6]),(0,[z0,z1,z2,z3,z1060,z6]),(0,[z0,z1,z1061,z3,z4,z6]),(0,[z60,z1,z13,z3,z4,z6]),(0,[z0,z1,z2,z4,z161,z216])]],
   [[],[(0,[z0,z1,z2,z3,z4,z1062]),(0,[z0,z1,z2,z203,z4,z6]),(0,[z0,z1,z2,z1063,z4,z6]),(0,[z0,z1,z2,z1064,z4,z6]),(0,[z0,z2,z3,z181,z6,z435]),(0,[z90,z1,z2,z3,z305,z6])],[(0,[z311,z1,z2,z3,z4,z6]),(0,[z1,z2,z76,z4,z660,z6]),(0,[z1065,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1066,z4,z6]),(0,[z266,z1,z2,z3,z4,z302]),(0,[z0,z1,z1067,z3,z4,z6]),(0,[z1068,z1,z2,z3,z4,z6]),(0,[z211,z0,z1,z4,z18,z212]),(0,[z1069,z1,z2,z3,z4,z6])],[(0,[z1,z2,z82,z4,z6,z39]),(0,[z27,z0,z2,z146,z4,z6]),(0,[z1070,z1,z2,z3,z4,z6]),(0,[z276,z0,z1,z146,z4,z6]),(0,[z0,z1,z2,z3,z4,z1071]),(0,[z0,z1,z2,z1072,z4,z6])],[(0,[z0,z1,z2,z1073,z4,z6]),(0,[z0,z1,z1074,z3,z4,z6]),(0,[z117,z1,z65,z3,z4,z6]),(0,[z0,z1,z37,z3,z4,z98]),(0,[z214,z0,z157,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1075])],[(0,[z107,z1,z2,z3,z4,z721])],[(0,[z0,z1,z1076,z3,z4,z6]),(0,[z0,z2,z3,z4,z763,z6]),(0,[z0,z1,z2,z3,z831,z6]),(0,[z0,z1,z1077,z3,z4,z6])],[(0,[z1,z2,z780,z3,z4,z6]),(0,[z84,z192,z2,z3,z4,z6]),(0,[z122,z0,z2,z146,z4,z6]),(0,[z0,z1,z3,z4,z919,z6]),(0,[z0,z1,z2,z969,z4,z6])]],
   [[(0,[z234,z152,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1078]),(0,[z0,z1,z2,z3,z4,z1079]),(0,[z357,z1,z2,z119,z4,z6]),(0,[z1080,z1,z2,z3,z4,z6]),(0,[z460,z75,z0,z1,z4,z6]),(0,[z0,z1,z3,z919,z97,z6])],[(0,[z14,z0,z2,z3,z4,z841]),(0,[z1081,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1082,z6]),(0,[z587,z0,z1,z3,z97,z6]),(0,[z0,z1,z2,z4,z6,z1083])],[(0,[z0,z1,z2,z1084,z4,z6]),(0,[z10,z1,z611,z3,z4,z6]),(0,[z147,z21,z2,z3,z58,z6]),(0,[z1,z2,z3,z4,z1085,z6]),(0,[z0,z1,z3,z4,z6,z405]),(0,[z211,z232,z1,z3,z4,z212])],[(0,[z44,z1,z455,z3,z4,z6]),(0,[z1,z2,z717,z54,z4,z6]),(0,[z0,z1,z2,z124,z4,z631])],[(0,[z0,z1,z2,z3,z4,z1086]),(0,[z90,z1,z2,z3,z15,z6]),(0,[z336,z81,z0,z1,z55,z6])],[(0,[z262,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1087]),(0,[z0,z1088,z2,z3,z4,z6]),(0,[z0,z1,z935,z3,z4,z6])],[(0,[z0,z1,z2,z1089,z4,z6]),(0,[z0,z1,z1090,z3,z4,z6]),(0,[z0,z1,z13,z146,z4,z6]),(0,[z0,z1,z372,z3,z4,z302]),(0,[z0,z1,z2,z4,z169,z6]),(0,[z0,z1,z52,z3,z4,z96])]],
   [[(0,[z83,z1,z2,z3,z711,z6]),(0,[z629,z0,z157,z3,z4,z6]),(0,[z1091,z1,z2,z3,z4,z6]),(0,[z1092,z0,z1,z3,z4,z6])],[(0,[z44,z1,z616,z3,z4,z6]),(0,[z75,z0,z1,z554,z4,z6]),(0,[z75,z0,z1,z556,z4,z6]),(0,[z1093,z0,z1,z2,z4,z6]),(1,[z0,z1,z2,z4,z821])],[(0,[z1094,z0,z1,z3,z4,z6]),(0,[z201,z1,z339,z76,z4,z6]),(0,[z123,z0,z1,z3,z4,z212]),(0,[z0,z1095,z2,z3,z4,z6]),(0,[z81,z0,z1,z227,z4,z6])],[(0,[z84,z1,z2,z440,z4,z6]),(0,[z1096,z0,z1,z3,z4,z6]),(0,[z147,z0,z372,z3,z58,z6]),(0,[z406,z0,z2,z3,z4,z164]),(0,[z0,z1097,z2,z3,z4,z6]),(0,[z1098,z0,z2,z3,z4,z6])],[(0,[z222,z0,z157,z3,z4,z6]),(0,[z21,z1,z22,z3,z4,z6])],[(0,[z1099,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z631]),(0,[z0,z1,z153,z774,z4,z6])],[(0,[z0,z1,z2,z1100,z4,z6]),(0,[z0,z1,z463,z3,z4,z6]),(0,[z0,z1,z2,z3,z1101,z6]),(0,[z81,z0,z1,z146,z4,z6])],[(0,[z288,z1,z2,z3,z4,z98]),(0,[z0,z1,z2,z3,z1102,z6]),(0,[z147,z0,z2,z3,z58,z302])]],
   [[(0,[z0,z1,z1103,z3,z4,z6]),(0,[z60,z1,z2,z146,z4,z6])],[(0,[z262,z0,z2,z3,z4,z39]),(0,[z1104,z1,z2,z3,z4,z6]),(0,[z1105,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1106,z6]),(0,[z655,z0,z1,z2,z3,z59])],[(0,[z1,z152,z241,z3,z4,z6]),(0,[z1,z2,z67,z4,z6,z39]),(0,[z0,z1107,z2,z3,z4,z6]),(0,[z0,z1,z995,z3,z4,z6])],[(0,[z1108,z1,z2,z3,z4,z6])],[(0,[z10,z1,z11,z3,z4,z6]),(0,[z0,z1,z250,z146,z4,z6]),(0,[z1109,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z18]),(0,[z1,z2,z3,z4,z1110,z6])],[(0,[z21,z1,z2,z3,z4,z6]),(0,[z14,z0,z2,z3,z4,z125])],[(0,[z0,z179,z2,z3,z590,z6]),(0,[z10,z1,z11,z82,z4,z6]),(0,[z132,z1,z13,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z443,z4,z417]),(0,[z1,z2,z3,z4,z6,z389]),(0,[z14,z0,z2,z3,z4,z133])],[(0,[z0,z1,z2,z1111,z4,z6]),(0,[z1112,z1,z2,z3,z4,z6])],[(0,[z118,z1,z2,z3,z4,z39]),(0,[z0,z1,z334,z400,z4,z6]),(0,[z0,z1,z1113,z3,z4,z6]),(1,[z1,z2,z3,z4,z721]),(0,[z0,z1,z2,z3,z4,z841]),(0,[z75,z0,z1,z596,z4,z6]),(0,[z286,z0,z2,z3,z34,z59])],[(0,[z0,z1,z2,z3,z1114,z6]),(0,[z0,z1,z2,z3,z1115,z6]),(0,[z0,z1,z42,z3,z4,z6]),(0,[z17,z0,z1,z157,z4,z6]),(0,[z0,z1,z2,z3,z4,z1116]),(0,[z266,z1,z2,z226,z4,z6]),(0,[z311,z1,z2,z193,z4,z6]),(0,[z1117,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1118,z4,z6]),(1,[z1,z780,z3,z4,z6]),(0,[z0,z1,z1119,z3,z4,z6])],[(0,[z0,z1,z2,z1120,z4,z6]),(0,[z155,z0,z2,z3,z4,z126]),(0,[z0,z23,z2,z3,z4,z6]),(0,[z0,z1,z2,z728,z4,z6]),(0,[z1121,z1,z2,z3,z4,z6]),(0,[z0,z1,z79,z4,z6,z149]),(0,[z211,z292,z1,z3,z4,z212])],[(0,[z418,z152,z2,z3,z4,z6]),(0,[z84,z1,z2,z479,z4,z6]),(0,[z0,z2,z3,z4,z6,z1122]),(0,[z323,z0,z157,z3,z4,z6])],[(0,[z0,z1,z1123,z3,z4,z6]),(0,[z0,z1,z1124,z3,z4,z6]),(0,[z44,z1,z65,z3,z4,z6]),(0,[z263,z0,z1,z157,z4,z6]),(0,[z1125,z1,z2,z3,z4,z6]),(0,[z1039,z1,z2,z3,z4,z6]),(0,[z0,z1,z774,z80,z4,z6])]],
   [[(0,[z14,z0,z2,z3,z305,z133]),(0,[z0,z2,z3,z4,z6,z841])],[(0,[z0,z1,z1126,z3,z4,z6]),(0,[z340,z1,z2,z76,z4,z6]),(0,[z90,z1,z2,z3,z4,z108]),(0,[z0,z179,z2,z3,z181,z6]),(0,[z0,z2,z3,z4,z6,z34])],[(0,[z1127,z0,z1,z2,z4,z6]),(0,[z406,z0,z2,z3,z4,z6]),(0,[z758,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1128]),(0,[z84,z1,z2,z54,z4,z6])],[(0,[z0,z1,z1129,z3,z4,z6]),(0,[z1130,z1,z2,z3,z4,z6]),(0,[z0,z1,z22,z124,z4,z6]),(0,[z1131,z1,z2,z3,z4,z6])],[(0,[z262,z152,z2,z3,z4,z6]),(1,[z1,z2,z3,z711,z6]),(0,[z1132,z1,z2,z3,z4,z6]),(0,[z1133,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1134])],[(0,[z117,z1,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z1135,z6]),(0,[z1136,z0,z2,z3,z4,z6])],[]],
   [[(0,[z0,z1,z372,z226,z4,z6]),(0,[z14,z90,z2,z3,z4,z133])],[(0,[z1,z152,z2,z35,z4,z6]),(0,[z0,z86,z2,z3,z4,z6]),(0,[z1,z339,z3,z4,z6,z39]),(0,[z1,z2,z3,z4,z6,z721]),(0,[z1137,z1,z2,z3,z4,z6])],[(0,[z154,z196,z2,z3,z4,z6]),(0,[z1138,z0,z1,z2,z4,z6]),(0,[z0,z749,z157,z3,z4,z6]),(0,[z1139,z0,z1,z2,z3,z4]),(0,[z75,z0,z1,z80,z4,z6]),(0,[z0,z1,z2,z831,z55,z6])],[(0,[z518,z155,z2,z3,z4,z6]),(0,[z117,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z1140,z4,z6]),(0,[z0,z1,z2,z4,z1141,z6])],[(0,[z75,z0,z1,z638,z4,z6]),(0,[z0,z1142,z2,z3,z4,z6]),(0,[z513,z0,z1,z2,z55,z6]),(0,[z0,z2,z3,z4,z164,z139]),(0,[z14,z0,z2,z3,z15,z133]),(0,[z0,z1,z2,z3,z143,z807])],[(0,[z0,z1,z334,z35,z4,z6]),(0,[z0,z1,z2,z1143,z4,z6]),(0,[z0,z1144,z2,z3,z4,z6]),(0,[z83,z1,z2,z3,z277,z6]),(0,[z406,z0,z2,z3,z4,z39]),(0,[z94,z0,z45,z197,z4,z6]),(0,[z665,z75,z0,z1,z4,z6]),(0,[z0,z1,z2,z3,z4,z807])],[(0,[z0,z1,z2,z4,z1145,z6]),(0,[z0,z1,z2,z124,z4,z6])],[(0,[z0,z1,z2,z3,z4,z126]),(0,[z0,z1,z2,z3,z4,z1146]),(0,[z0,z1,z2,z3,z711,z6]),(0,[z0,z1,z463,z193,z4,z6]),(0,[z0,z1,z153,z4,z6,z604]),(0,[z0,z1,z2,z1147,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 538) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1082).take 38) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1120)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 538, 38] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 145).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 145).take 111).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [145, 111] = true :=
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

end PEqualNP.Outside.L_meta_39213

theorem PEqualNP.Outside.L_meta_39213 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4205504640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4205504640) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39213.solve